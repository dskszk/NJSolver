module Parser where

import Text.Parsec
import Text.Parsec.String
import Control.Applicative (pure, (<$>), (<*>), (*>), (<*))
import Data.List


data Sequent = Seq [Expr] Expr

data Expr = Sym String
    | Impl Expr Expr
    | And Expr Expr
    | Or Expr Expr
    | Weak Expr 
    | Fal deriving (Ord, Eq)

instance Show Sequent where
    show (Seq ant dec) = intercalate ", " (map (rmPar . show) ant) ++ "\\Rightarrow " ++ (rmPar $ show dec)
      where
        rmPar ('(':s) = init s
        rmPar s = s

instance Show Expr where
    show (Sym s) = s
    show (Impl Fal Fal) = "\\top"
    show (Impl e Fal) = "\\lnot " ++ show e
    show (Impl e1 e2) = concat ["(", show e1, "\\to ", show e2, ")"]
    show (And e1 e2) = concat ["(", show e1, "\\land ", show e2, ")"]
    show (Or e1 e2) = concat ["(", show e1, "\\lor ", show e2, ")"]
    show (Weak e) = show e
    show Fal = "\\bot"

lexeme p = p <* spaces
ident = lexeme $ try $ ((:) <$> letter <*> many alphaNum)
resOp s = lexeme $ try $ string s
res s = lexeme $ try $ (string s *> notFollowedBy alphaNum)
match s = lexeme $ string s
parens p = between (match "(") (match ")") p
commaSep p = sepBy p (match ",")

sequent :: Parser Sequent
sequent = Seq <$> commaSep expr <*> (resOp "=>" *> expr)
expr = try (Impl <$> disj <*> (resOp "->" *> expr)) <|> disj
disj = try (Or <$> conj <*> (resOp "|" *> disj)) <|> conj
conj = try (And <$> sym <*> (resOp "&" *> conj)) <|> sym
sym = try truth <|> Sym <$> ident <|> non <|> parens expr
truth = pure Fal <* res "F" <|> pure (Impl Fal Fal) <* res "T"
non = resOp "~" *> (Impl <$> sym <*> pure Fal)

start :: String -> Either String Sequent
start str = case parse sequent "" str of
    Left err -> Left $ show err
    Right s -> Right s

