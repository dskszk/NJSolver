module NJSolver where

import Parser
import Control.Applicative
import Data.List
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

drawDiag (Node (r, s) []) = "\\infer[" ++ show r ++ "]{" ++ show s ++ "}{}"
drawDiag (Node (r, s) xs) = "\\infer[" ++ show r ++ "]{" ++ show s ++ "}{"
    ++ (intercalate "&" $ map drawDiag xs) ++ "}"

contra a@(Node (ID, _) []) = a
contra (Node (ImplE, Seq c x) xs) = Node (ImplE, Seq (unionBy (~=) d g) x) ys
  where
    ys@((Node (_, Seq d _) _):(Node (_, Seq g _) _):_) = map contra xs
contra (Node (r, Seq c x) xs)
    | r `elem` [ImplE, AndE, OrE, EFQ] = Node (r, Seq d x) ys
    | otherwise = Node (r, Seq c x) ys
  where
    ys@((Node (_, Seq d _) _):_) = map contra xs

weaken (Node (ID, (Seq c x)) []) = (Node (ID, (Seq [x] x)) [], deleteBy (~=) x c)
weaken (Node (r, (Seq c x)) xs) = (Node (r, Seq (deleteFirstsBy (~=) c d) x) ys, intersectBy (~=) d c)
  where
    (ys, ds) = unzip $ map weaken xs
    d = foldl1' (intersectBy (~=)) ds

shorten a@(Node (ID, _) _) = a
shorten a@(Node (_, x) xs) = Node (t, y) (map shorten ys)
  where
    (Node (t, y) ys) = fromMaybe a (fld x xs)
    fld x xs = foldr (<|>) empty (map (go x) xs)
    go _ (Node (ID, _) _) = Nothing
    go a@(Seq c y) (Node (r, Seq d x) ys)
        | x ~= y && null (deleteFirstsBy (~=) d c) = Just (Node (r, a) ys)
        | otherwise = fld a ys

prove :: Sequent -> Maybe Diagram
prove s@(Seq c x)
    | any (x ~=) c = Just (Node (ID, s) [])
    | otherwise = intro s <|> topDown s

intro :: Sequent -> Maybe Diagram
intro s@(Seq c (Or x y)) = do
    p <- prove (Seq c x) <|> prove (Seq c y)
    return $ Node (OrI, s) [p]
intro s@(Seq c (And x y)) = do
    p <- prove (Seq c x)
    q <- prove (Seq c y)
    return $ Node (AndI, s) [p, q]
intro s@(Seq c (Impl x y)) = do
    p <- prove (Seq (x:c) y)
    return $ Node (ImplI, s) [p]
intro _ = Nothing

topDown :: Sequent -> Maybe Diagram
topDown (Seq [] _) = Nothing
topDown s@(Seq c y) = foldr (<|>) empty $ map helper c
  where
    helper x = meet y (Node (ID, Seq c x) [])

goDown :: Expr -> Diagram -> Maybe Diagram
goDown g a@(Node (_, Seq c p@(Weak (And y z))) _)
    = meet g (Node (AndE, Seq (p `delete` c) y) [a])
        <|> meet g (Node (AndE, Seq (p `delete` c) z) [a])
goDown g a@(Node (_, Seq c p@(And y z)) _)
    | p `elem` c = meet g (Node (AndE, Seq ((Weak p):(p `delete` c)) y) [a])
        <|> meet g (Node (AndE, Seq ((Weak p):(p `delete` c)) z) [a])
    | otherwise = meet g (Node (AndE, Seq c y) [a])
        <|> meet g (Node (AndE, Seq c z) [a])
goDown g y@(Node (_, s) _) = do
    (tag, p, q) <- elim g s
    r <- mapM prove p
    meet g (Node (tag, q) (y:r))

meet g y@(Node (_, Seq c p) _)
    | p ~= g = Just y
    | otherwise = goDown g y

elim g (Seq c p@(Weak (Impl y z))) = Just (ImplE, [Seq (p `delete` c) y], Seq (p `delete` c) z)
elim g (Seq c p@(Impl y z))
    | p `elem` c = Just (ImplE, [Seq ((Weak p):(p `delete` c)) y], Seq ((Weak p):(p `delete` c)) z)
    | otherwise = Just (ImplE, [Seq c y], Seq c z)
elim g (Seq c p@(Or y z)) =
    Just (OrE, [Seq (y:(p `delete` c)) g, Seq (z:(p `delete` c)) g], Seq c g)
elim g (Seq c Fal) = Just (EFQ, [], Seq c g)
elim _ _ = Nothing

test s = case start s of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> case prove t of
        Just d -> putStrLn $ drawDiag $ fst $ weaken $ shorten $ contra d
        Nothing -> putStrLn "Unprovable"

