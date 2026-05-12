open import cqts
open import cqts-ext
open import scratch

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

main : IO ⊤
main = putStrLn "No standard library!"


-- module main where
-- 
-- open import IO
-- 
-- main : Main
-- main = run (putStrLn "Hmm")
