module Main where

import TypeInference

main :: IO ()
main = do
    putStrLn "Enter expression"
    s <- getLine
    putStrLn $ getType s
    main
