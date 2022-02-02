module Util.Error

import System


public export
error : Show err => err -> a
error x = unsafePerformIO $ do
    print x
    exitFailure

