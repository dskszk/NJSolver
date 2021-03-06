module NJSolver where

import Parser
import Control.Applicative
import Data.List
import qualified Data.Set as S
import Data.Tree
import Data.Maybe

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
drawDiag g n (Node (ID, Seq c x) []) = case lookup x g of
    Just m -> (n, "\\infer[(" ++ (show m) ++ ")]{"
        ++ (showE x) ++ "}{}")
    Nothing -> (n, showE x)
drawDiag g n (Node (ImplI, Seq c a@(Expr _ (Impl x y))) (z:_))
    = (m, "\\infer[(\\to I," ++ (show n) ++ ")]{" ++ (showE a) ++ "}{"
        ++ ys ++ "}")
  where
    (m, ys) = drawDiag ((f x) ++ g) (n + 1) z
    f (Expr _ (And x y)) = (f x) ++ (f y)
    f x = [(x, n)]
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

shorten a@(Node (ID, _) _) = a
shorten a@(Node (_, x) xs) = Node (t, y) $ map shorten ys
  where
    (Node (t, y) ys) = fromMaybe a $ fld x xs
    fld x xs = foldr (<|>) empty (map (go x) xs)
    go _ (Node (ID, _) _) = Nothing
    go a@(Seq c y) (Node (r, Seq d x) ys)
        | x == y && S.isSubsetOf d c = Just $ Node (r, a) ys
        | otherwise = fld a ys

prove :: Sequent -> Maybe Diagram
prove s@(Seq c x)
    | S.member x c = Just $ Node (ID, s) []
    | otherwise = intro s <|> topDown s

intro :: Sequent -> Maybe Diagram
intro s@(Seq c (Expr Norm e)) = formOf e
  where
    formOf (Or x y) = do
        p <- prove (Seq c x) <|> prove (Seq c y)
        return $ Node (OrI, s) [p]
    formOf (And x y) = do
        p <- prove $ Seq c x
        q <- prove $ Seq c y
        return $ Node (AndI, s) [p, q]
    formOf (Impl x y) = do
        p <- prove $ insert' x y c
        return $ Node (ImplI, s) [p]
    formOf _ = Nothing
    insert' (Expr _ (And x y)) z c = Seq (S.insert x c) (Expr Norm (Impl y z))
    insert' x y c = Seq (S.insert x c) y
intro _ = Nothing

topDown :: Sequent -> Maybe Diagram
topDown s@(Seq c y)
    | S.null c = Nothing
    | otherwise = foldr (<|>) empty $ map helper $ S.toList c
  where
    helper x = meet y $ Node (ID, Seq (weaken' x) x) []
    weaken' x = S.insert (weaken x) $ S.delete x c

goDown :: Expr -> Diagram -> Maybe Diagram
goDown g a@(Node (_, Seq c e) _) = formOf e
  where
    formOf (Expr _ (And y z))
        = meet g (Node (AndE, Seq c y) [a])
            <|> meet g (Node (AndE, Seq c z) [a])
    formOf _ = do
        (tag, p, q) <- elim g $ Seq c e
        r <- mapM prove p
        meet g $ Node (tag, q) (a:r)
    addc x y = S.insert y $ S.insert x $ S.delete e c

meet g y@(Node (_, Seq c p) _)
    | p == g = Just y
    | otherwise = goDown g y

elim g (Seq c e) = formOf e
  where
    {-
    formOf (Expr Weak (Impl y z)) = Just (ImplE, [Seq wc y], Seq c z)
    formOf (Expr Norm (Impl y z))
        | S.member e c = Just (ImplE, [Seq wc' y], Seq c' z)
        | otherwise = Just (ImplE, [Seq wc y], Seq c z)
    -}
    formOf (Expr Weak (Impl y z)) = Just (ImplE, [Seq wc y], Seq wc z)
    formOf (Expr Norm (Impl y z)) = Just (ImplE, [Seq c y], Seq c z)
    formOf (Expr _ (Or y z))
        = Just (OrE, [Seq (addc y) g, Seq (addc z) g], Seq c g)
    formOf (Expr _ Fal) = Just (EFQ, [], Seq c g)
    formOf _ = Nothing
    wc = S.filter isNorm c
    isNorm (Expr Norm _) = True
    isNorm (Expr Weak _) = False
    addc x = S.insert x (S.delete e wc)

test s = case start s of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> case prove t of
        Just d -> putStrLn $ snd $ drawDiag [] 1 $ shorten $ contra d
        Nothing -> putStrLn "Unprovable"

