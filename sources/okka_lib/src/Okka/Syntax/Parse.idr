module Okka.Syntax.Parse

import Okka.Syntax.Terms
import Okka.Syntax.Lex
import Okka.Syntax.Util
import Text.Parser
import Data.List1

%default total

{-
def hello : Int -> Int =
    fksdafjdafds;
-}

-- Raw tokens

thinArrow : Grammar state Token True ()
thinArrow = terminal "Expected '->'" (\case { TThinArrow => Just (); _ => Nothing })

thickArrow : Grammar state Token True ()
thickArrow = terminal "Expected '=>'" (\case { TThickArrow => Just (); _ => Nothing })

colon : Grammar state Token True ()
colon = terminal "Expected ':'" (\case { TColon => Just (); _ => Nothing })

semiColon : Grammar state Token True ()
semiColon = terminal "Expected ';'" (\case { TSemiColon => Just (); _ => Nothing })

lparen : Grammar state Token True ()
lparen = terminal "Expected '('" (\case { TLParen => Just (); _ => Nothing })

rparen : Grammar state Token True ()
rparen = terminal "Expected ')'" (\case { TRParen => Just (); _ => Nothing })

equals : Grammar state Token True ()
equals = terminal "Expected '='" (\case { TEquals => Just (); _ => Nothing })

def : Grammar state Token True ()
def = terminal "Expected 'def'" (\case { TDef => Just (); _ => Nothing })

fn : Grammar state Token True ()
fn = terminal "Expected 'fn'" (\case { TFn => Just (); _ => Nothing })

ident : Grammar state Token True Ident
ident = terminal "Expected 'identifier'" (\case { TIdent s => Just (MkIdent s); _ => Nothing })


-- Expressions


mutual
    lam : Grammar state Token True SExpr
    lam = do
        fn
        param <- ident
        thickArrow
        body <- expr
        pure $ SLam param body

    pi : Grammar state Token True SExpr
    pi = do
        lparen
        param <- ident
        colon
        paramTy <- expr
        rparen
        thinArrow
        retTy <- expr
        pure $ SPi param paramTy retTy

    subexpr : Grammar state Token True SExpr
    subexpr = do
        lparen
        res <- expr
        rparen
        pure res

    atom : Grammar state Token True SExpr
    atom = (SVar <$> ident) <|> lam <|> pi <|> subexpr

    chunk : Grammar state Token True SExpr
    chunk = foldl1 SApp <$> some atom 

    export
    expr : Grammar state Token True SExpr
    expr = foldr1 (SPi (MkIdent "_")) <$> sepBy1 thinArrow chunk


-- Functions and programs

function : Grammar state Token True SFunction
function = do
    def
    name <- ident
    colon
    type <- expr
    equals
    body <- expr
    semiColon
    pure $ MkSFunction { name = name, type = type, body = body }


program : Grammar state Token True SProgram
program = do
    x <- function
    xs <- program <|> pure []
    pure $ x :: xs


parser : Grammar state Token True SProgram
parser = do
    prog <- program
    eof
    pure prog


showError : ParsingError Token -> String
showError (Error err Nothing) = "Parse error. \{err}"
showError (Error err (Just (MkBounds startLine startCol endLine endCol)))
    = "Parse error from lines \{show startLine}-\{show endLine} and cols \{show startCol}-\{show endCol}.\n\{err}\n\n"


export
lexParseProgram : String -> Either String SProgram
lexParseProgram input with (lex input)
  _ | (Left loc) = Left $ "Lex error. Invalid token on line \{show loc.line}, col \{show loc.col}"
  _ | (Right toks) with (parse parser toks)
    _ | (Left (err ::: parseErrors)) = Left $ showError err
    _ | (Right (prog, _)) = Right prog
