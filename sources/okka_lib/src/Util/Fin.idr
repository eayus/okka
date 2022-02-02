module Util.Fin

import Data.Fin


-- TODO: next version, remove this in favour of Data.Fin.complement in base
public export
complement : {n : Nat} -> Fin n -> Fin n
complement {n = S _} FZ = last
complement {n = S _} (FS x) = weaken $ complement x
