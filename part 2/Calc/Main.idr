module Main

import Effects
import Effect.StdIO
import Rpn

main : IO ()
main = do
  s <- getLine
  print $ calcRpn s

-- Local Variables:
-- idris-load-packages: effects
-- End:
