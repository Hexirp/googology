module Bashicu where
 import Prelude

 expand :: ([[Int]], Int) -> Int
 expand ([], n) = n
 expand (s,  n) = let x = length s in case is_empty_column (s !! (x - 1)) of
  True -> expand (append_from_to 0 (x - 2) (\n -> [s !! n]), act n)
  False -> expand (good_part s ++ append_from_to 0 (act n) (\n -> bad_part s n), act n)

 is_empty_column :: [Int] -> Bool
 is_empty_column = undefined

 append_from_to :: Int -> Int -> (Int -> [a]) -> [a]
 append_from_to = undefined

 act :: Int -> Int
 act = undefined

 good_part :: [[Int]] -> [[Int]]
 good_part = undefined

 bad_part :: [[Int]] -> Int -> [[Int]]
 bad_part = undefined
