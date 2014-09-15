import System.Environment
import System.Process (system)

main = do [x] <- getArgs
          system $ "sed -i 's/" ++ x ++ "_/" ++ x ++ "/g' *.hs"
          return ()
