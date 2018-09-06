module Algebra.Main where
import Algebra.AlgebraicClosure
import Algebra.NewtonTheorem

main :: IO ()
main = putStr $ show $ apply (run $ newton test7) []