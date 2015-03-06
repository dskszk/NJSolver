module Parser where

import Text.Parsec
import Text.Parsec.String
import Control.Applicative (pure, (<$>), (<*>), (*>), (<*))
import Data.List
import qualified Data.Set as S

data Sequent = Seq (S.Set Expr) Expr

data Mark = Weak | Norm

mark :: Body -> Expr
mark e = Expr Norm e

weaken :: Expr -> Expr
weaken (Expr _ e) = Expr Weak e

data Expr = Expr Mark Body

data Body = Sym String
    | Impl Expr Expr
    | And Expr Expr
    | Or Expr Expr
    | Fal deriving (Eq, Ord)

instance Eq Expr where
    (Expr _ e1) == (Expr _ e2) = e1 == e2

instance Ord Expr where
    (Expr _ e1) <= (Expr _ e2) = e1 <= e2

instance Show Expr where
    show (Expr _ e) = show e

showE :: Expr -> String
showE e = rmPar $ show e
  where
    rmPar ('(':s) = init s
    rmPar s = s

instance Show Sequent where
    show (Seq ant dec) = intercalate ", " (map (rmPar . show) $ S.toList ant) ++ "\\Rightarrow " ++ (rmPar $ show dec)
      where
        rmPar ('(':s) = init s
        rmPar s = s

instance Show Body where
    show (Sym s) = s
    show (Impl (Expr _ Fal) (Expr _ Fal)) = "\\top"
    show (Impl e (Expr _ Fal)) = "\\lnot " ++ show e
    show (Impl e1 e2) = concat ["(", show e1, "\\to ", show e2, ")"]
    show (And e1 e2) = concat ["(", show e1, "\\land ", show e2, ")"]
    show (Or e1 e2) = concat ["(", show e1, "\\lor ", show e2, ")"]
    show Fal = "\\bot"

lexeme p = p <* spaces
ident = lexeme $ try $ ((:) <$> letter <*> many alphaNum)
resOp s = lexeme $ try $ string s
res s = lexeme $ try $ (string s *> notFollowedBy alphaNum)
match s = lexeme $ string s
parens p = between (match "(") (match ")") p
commaSep p = sepBy p (match ",")

sequent :: Parser Sequent
sequent = Seq <$> (S.fromList <$> commaSep expr) <*> (resOp "=>" *> expr)
expr = try (mark <$> (Impl <$> disj <*> (resOp "->" *> expr))) <|> disj
disj = try (mark <$> (Or <$> conj <*> (resOp "|" *> disj))) <|> conj
conj = try (mark <$> (And <$> sym <*> (resOp "&" *> conj))) <|> sym
sym = try truth <|> mark <$> Sym <$> ident <|> non <|> parens expr
truth = pure (mark Fal) <* res "F"
    <|> (pure $ mark $ Impl (mark Fal) (mark Fal)) <* res "T"
non = resOp "~" *> (mark <$> (Impl <$> sym <*> (pure $ mark Fal)))

start :: String -> Either String Sequent
start str = case parse sequent "" str of
    Left err -> Left $ show err
    Right s -> Right s

