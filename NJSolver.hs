module NJSolver where

import Parser
import Control.Applicative
import Data.List
import qualified Data.Set as S
import Data.Tree
import Data.Maybe
import Debug.Trace

data Rule = ID | EFQ | ImplE | AndE | OrE | ImplI | AndI | OrI
    deriving (Ord, Eq)

instance Show Rule where
    show ID = "(ID)"
    show EFQ = "(EFQ)"
    show ImplE = "(\\to E)"
    show AndE = "(\\land E)"
    show OrE = "(\\lor E)"
    show ImplI = "(\\to I)"
    show AndI = "(\\land I)"
    show OrI = "(\\lor I)"

type Diagram = Tree (Rule, Sequent)

drawDiag :: [(Expr, Int)] -> Int -> Diagram -> (Int, String)
drawDiag g n (Node (ID, Seq c x) [])
    | isJust $ lookup x g
        = (n, "\\infer[(" ++ (show $ fromJust $ lookup x g) ++ ")]{"
            ++ (showE x) ++ "}{}")
    | otherwise = (n, showE x)
drawDiag g n (Node (ImplI, Seq c a@(Expr _ (Impl x y))) (z:_))
    = (m, "\\infer[(\\to I," ++ (show n) ++ ")]{" ++ (showE a) ++ "}{"
        ++ ys ++ "}")
  where
    (m, ys) = drawDiag ((x, n):g) (n + 1) z
drawDiag g n (Node (OrE, Seq c x) xs@(a:_))
    = (m, "\\infer[(\\lor E," ++ (show n) ++ ")]{" ++ (showE x) ++ "}{"
        ++ (intercalate "&" ys) ++ "}")
  where
    Node (_, Seq _ (Expr _ (Or y z))) _ = a
    (m, ys) = mapAccumL (drawDiag ((y, n):(z, n):g)) (n + 1) xs
drawDiag g n (Node (r, Seq c x) xs)
    = (m, "\\infer[" ++ (show r) ++ "]{" ++ (showE x) ++ "}{"
        ++ (intercalate "&" $ ys) ++ "}")
  where
    (m, ys) = mapAccumL (drawDiag g) n xs

contra a@(Node (ID, _) []) = a
contra (Node (ImplE, Seq c x) xs) = Node (ImplE, Seq (S.union d g) x) ys
  where
    ys@((Node (_, Seq d _) _):(Node (_, Seq g _) _):_) = map contra xs
contra (Node (r, Seq c x) xs)
    | r `elem` [ImplE, AndE, OrE, EFQ] = Node (r, Seq d x) ys
    | otherwise = Node (r, Seq c x) ys
  where
    ys@((Node (_, Seq d _) _):_) = map contra xs

{-
remove (Node (ID, (Seq c x)) []) = (Node (ID, (Seq [x] x)) [], delete x c)
remove (Node (r, (Seq c x)) xs) = (Node (r, Seq (c \\ d) x) ys, intersect d c)
  where
    (ys, ds) = unzip $ map remove xs
    d = foldl1' intersect $ map (nubBy (~=)) ds
-}

shorten a@(Node (ID, _) _) = a
shorten a@(Node (_, x) xs) = Node (t, y) (map shorten ys)
  where
    (Node (t, y) ys) = fromMaybe a (fld x xs)
    fld x xs = foldr (<|>) empty (map (go x) xs)
    go _ (Node (ID, _) _) = Nothing
    go a@(Seq c y) (Node (r, Seq d x) ys)
        | x == y && S.isSubsetOf d c = Just (Node (r, a) ys)
        | otherwise = fld a ys

prove :: Sequent -> Maybe Diagram
prove s@(Seq c x)
    | S.member x c = Just (Node (ID, s) [])
    | otherwise = intro s <|> topDown s

intro :: Sequent -> Maybe Diagram
intro s@(Seq c (Expr Norm (Or x y))) = do
    p <- prove (Seq c x) <|> prove (Seq c y)
    return $ Node (OrI, s) [p]
intro s@(Seq c (Expr Norm (And x y))) = do
    p <- prove (Seq c x)
    q <- prove (Seq c y)
    return $ Node (AndI, s) [p, q]
intro s@(Seq c (Expr Norm (Impl x y))) = do
    p <- prove (Seq (S.insert x c) y)
    return $ Node (ImplI, s) [p]
intro _ = Nothing

topDown :: Sequent -> Maybe Diagram
topDown s@(Seq c y)
    | S.null c = Nothing
    | otherwise = foldr (<|>) empty $ map helper (S.toList c)
  where
    helper x = meet y (Node (ID, Seq c x) [])

goDown :: Expr -> Diagram -> Maybe Diagram
goDown g a@(Node (_, Seq c p@(Expr Weak (And y z))) _)
    = meet g (Node (AndE, Seq (S.delete p c) y) [a])
        <|> meet g (Node (AndE, Seq (S.delete p c) z) [a])
goDown g a@(Node (_, Seq c p@(Expr Norm (And y z))) _)
    | S.member p c =
        meet g (Node (AndE, Seq (S.insert (weaken p) (S.delete p c)) y) [a])
        <|> meet g (Node (AndE, Seq (S.insert (weaken p) (S.delete p c)) z) [a])
    | otherwise = meet g (Node (AndE, Seq c y) [a])
        <|> meet g (Node (AndE, Seq c z) [a])
goDown g y@(Node (_, s) _) = do
    (tag, p, q) <- elim g s
    r <- mapM prove p
    meet g (Node (tag, q) (y:r))

meet g y@(Node (_, Seq c p) _)
    | p == g = Just y
    | otherwise = goDown g y

elim g (Seq c p@(Expr Weak (Impl y z))) =
    Just (ImplE, [Seq (S.delete p c) y], Seq (S.delete p c) z)
elim g (Seq c p@(Expr Norm (Impl y z)))
    | S.member p c = Just (ImplE, [Seq (S.insert (weaken p) (S.delete p c)) y],
        Seq (S.insert (weaken p) (S.delete p c)) z)
    | otherwise = Just (ImplE, [Seq c y], Seq c z)
elim g (Seq c p@(Expr _ (Or y z))) =
    Just (OrE, [Seq (S.insert y (S.delete p c)) g,
        Seq (S.insert z (S.delete p c)) g], Seq c g)
elim g (Seq c (Expr _ Fal)) = Just (EFQ, [], Seq c g)
elim _ _ = Nothing

test s = case start s of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> case prove t of
        Just d -> putStrLn $ snd $ drawDiag [] 1 $ shorten $ contra d
        Nothing -> putStrLn "Unprovable"

