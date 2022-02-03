module Okka.Syntax.Lex

import Okka.Syntax.Terms
import Okka.Syntax.Util
import Text.Lexer
import Data.List


-- TODO: fix bug when lexing a string like "fnx"
-- TODO: can identifiers be empty?


public export
data Token : Type where
    TIdent : String -> Token
    TLit : Int -> Token
    TThinArrow : Token
    TThickArrow : Token
    TColon : Token
    TSemiColon : Token
    TLParen : Token
    TRParen : Token
    TEquals : Token
    TDef : Token
    TPostulate : Token
    TFn : Token


tokens : TokenMap (Maybe Token)
tokens =
    [
        (reject (exact "def" <|> exact "fn" <|> exact "postulate") <+> (alpha <+> many alphaNum), Just . TIdent),
        (digits, Just . TLit . cast),
        (exact "->", Just . const TThinArrow),
        (exact "=>", Just . const TThickArrow),
        (exact ":", Just . const TColon),
        (exact ";", Just . const TSemiColon),
        (exact "(", Just . const TLParen),
        (exact ")", Just . const TRParen),
        (exact "=", Just . const TEquals),
        (exact "def", Just . const TDef),
        (exact "postulate", Just . const TPostulate),
        (exact "fn", Just . const TFn),
        (spaces, const Nothing)
    ]


-- Return the location of the invalid token on fail.
export
lex : String -> Either Loc (List (WithBounds Token))
lex input with (Text.Lexer.Core.lex tokens input)
  _ | (toks, (line, col, "")) = Right $ catMaybes $ map (\x => (\y => MkBounded y x.isIrrelevant x.bounds) <$> x.val) toks
  _ | (toks, (line, col, _)) = Left $ MkLoc { line = line, col = col }


export
lex' : String -> Either String (List Token)
lex' input = bimap (\loc => "Error on line \{show loc.line}, col \{show loc.col}") (map (.val)) $ lex input


public export
Show Token where
    show (TIdent x) = "Ident \{show x}"
    show TThinArrow = "ThinArrow"
    show TThickArrow = "ThickArrow"
    show TColon = "Colon"
    show TSemiColon = "SemiColon"
    show TLParen = "LParen"
    show TRParen = "RParen"
    show TEquals = "Equals"
    show TDef = "Def"
    show TPostulate = "Postulate"
    show TFn = "Fn"
    show (TLit n) = "Lit \{show n}"
