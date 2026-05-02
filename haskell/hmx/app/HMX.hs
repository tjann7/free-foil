module Main where

import qualified Language.HMX.Impl.Interpret as Interpret
import System.Exit
 
main :: IO ()
main = do Interpret.defaultMain
