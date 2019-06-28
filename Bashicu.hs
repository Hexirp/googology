module Bashicu where
 import Prelude

 k :: Int
 k = iter bm 10 9

 bm :: Int -> Int
 bm = expand ([replicate (n + 1) 0, replicate (n + 1) 1], n)

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

 type Matrix = [[Int]]

 data Signature = Zero | Succ | Limit

 sig :: Matrix -> Signature
 sig [] = Zero
 sig (x:xs) = if all (0 ==) x then Succ else Limit
