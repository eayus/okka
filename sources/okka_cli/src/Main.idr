module Main

import Sap

import Okka.Syntax.Terms
import Okka.Syntax.Terms.Util
import Okka.Syntax.Parse
import Okka.Syntax.Check
import Okka.Core.Terms

import System
import System.File.ReadWrite
import Data.Vect


die : Show a => a -> IO ()
die x = do
    print x
    exitFailure


compile : (filepath : String) -> IO ()
compile filepath = do
    Right contents <- readFile filepath
        | Left err => die err

    let Right prog = lexParseProgram contents
        | Left err => die err

    let Right coreProg = checkProgram [] prog
        | Left err => putStrLn err >> exitFailure --die err

    putStrLn "Compilation succesful."


cmd : Command (IO ())
cmd = Cmd {
    name = "okka",
    desc = "Okka language compiler",
    rhs = Basic ["filepath" # String] [] (\[filepath], [] => compile filepath)
}


partial
main : IO ()
main = runCommand cmd
