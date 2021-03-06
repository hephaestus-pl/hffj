-- automatically generated by BNF Converter
module Main where


import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )

import FJ.Syntax.Lexfj_syntax
import FJ.Syntax.Parfj_syntax
import FJ.Syntax.Skelfj_syntax
import FJ.Syntax.Printfj_syntax
import FJ.Syntax.Absfj_syntax
import FJ.Dynamics.Computation
import FJ.Syntax.LookupFunctions
import FJ.TypeSystem.TypeChecker
import qualified FJ.Core.CommonTypes as Common




import FJ.Syntax.ErrM

type ParseFun = [Token] -> Err Program

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: Verbosity -> ParseFun -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: Verbosity -> ParseFun -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn s
           Ok  tree -> do putStrLn "\nParse Successful!"
                          showTree v tree
                          typeCheck tree




showTree :: Int -> Program -> IO ()
showTree v tree = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

typeCheck :: Program -> IO ()
typeCheck tree = 
    let ct = programCT tree in
    let exp = programExp tree in 
    case mapM (\cdecl -> classOk cdecl ct) ct of
        Common.Ex s -> do putStrLn $ "\nProgram ill Typed\n" ++ show s
        Common.Ok _ -> compute tree
 
compute:: Program -> IO ()
compute tree = 
    let ct = programCT tree in
    let exp = programExp tree in 
   putStrLn $ "\n[Computation Result]\n\n" ++ show (computation exp ct)
   
main :: IO ()
main = do args <- getArgs
          case args of
            [] -> hGetContents stdin >>= run 2 pProgram
            "-s":fs -> mapM_ (runFile 0 pProgram) fs
            fs -> mapM_ (runFile 2 pProgram) fs





