module Okka.Core.ToScheme

import Okka.Core.Terms
import Data.Vect


-- We have to be careful not to generate any variable names which
-- would clash with scheme keywords


freshName : Vect scope String -> String
freshName xs = "x\{show $ length xs}"


toScheme : Vect scope String -> CExpr scope -> String
toScheme names (CVar x) = index x names

toScheme names (CApp _ _ x y) =
    let lhs = toScheme names x
        rhs = toScheme names y
    in "(\{lhs} \{rhs})"

toScheme names (CLam x) =
    let name = freshName names
        body = toScheme (name :: names) x
    in "(lambda \{name} \{body})"

toScheme names (CPi x y) = show "UNIT"
toScheme names CUni = show "UNIT"
toScheme names CI32 = show "UNIT"
toScheme names (CLit n) = show n


export
progToScheme : Vect scope String -> CProgram scope -> String
progToScheme names [] = ""
progToScheme names (x :: xs) =
    let name = freshName names
        body = toScheme names x
        func = "(define \{name} \{body})"
        rest = progToScheme (name :: names) xs
    in "\{func}\n\n\{rest}"
