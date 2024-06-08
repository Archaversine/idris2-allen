module Main

import Allen

import System
import System.File.ReadWrite

handleInput : HasIO io => String -> io ()
handleInput input = case parseNetwork input of 
    Left x  => putStrLn $ "ERR " ++ show x
    Right n => case runAllen (loadNetwork n) of 
        (graph, Left e)  => putStrLn $ "ERR " ++ show e
        (graph, Right a) => putStrLn $ "OK " ++ encode (graphToNetwork graph)

handleFile : HasIO io => String -> String -> io ()
handleFile input output = readFile input >>= \case 
    Left e  => putStrLn $ "ERR " ++ show e
    Right s => case parseNetwork s of 
        Left x  => putStrLn $ "ERR " ++ show x
        Right n => case runAllen (loadNetwork n) of 
            (graph, Left e)  => putStrLn $ "ERR " ++ show e
            (graph, Right a) => writeFile output (encode (graphToNetwork graph)) >>= \case
                Left e  => putStrLn $ "ERR " ++ show e
                Right _ => putStrLn "OK"

main : IO ()
main = getArgs >>= \case 
    [_, "input", input]        => handleInput input
    [_, "file", input, output] => handleFile input output
    xs => putStrLn "Usage: allen input <json> | allen file <input json> <output json>" >> printLn xs