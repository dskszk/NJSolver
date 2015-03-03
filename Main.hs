module Main(main) where

import NJSolver

main :: IO ()
main = do
    s <- getLine
    putStrLn "\\documentclass[a4paper]{article}"
    putStrLn "\\usepackage{proof}"
    putStrLn "\\usepackage[landscape]{geometry}"
    putStrLn "\\begin{document}"
    putStrLn "$$"
    test s
    putStrLn "$$"
    putStrLn "\\end{document}"

