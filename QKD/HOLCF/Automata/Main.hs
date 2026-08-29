module Main where

import Automata
import qualified Prelude

main :: Prelude.IO ()
main = do
    Prelude.print (test_automaton 0)