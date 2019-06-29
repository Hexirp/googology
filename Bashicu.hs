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

 type Matrix = [Sequence]

 type Sequence = [Int]

 data Signature = Zero | Succ Matrix | Limit Sequence Matrix

 sig :: Matrix -> Signature
 sig [] = Zero
 sig (x : xs) = if all (0 ==) x then Succ xs else Limit x xs

 -- エラーの可能性あり
 parent :: Matrix -> Int -> Int -> Int
 parent s 0 x = go (x + 1) where
  go :: Int -> Int
  go n = if s ! n ! 0 < s ! x ! 0 then n else go (n + 1)
 parent s y x = go x where
  go :: Int -> Int
  go n = if n `elem` ancestor s (y - 1) x
   then if s ! n ! y < s ! x ! y then n else go (n + 1)
   else go (n + 1)

 -- エラーの可能性あり
 ancestor :: Matrix -> Int -> Int -> [Int]
 ancestor s y x = go x where
  go n = n : if n == length s - 1 then [] else go (parent s y n)

 -- エラーの可能性あり
 t :: Sequence -> Int
 t x = fromMaybe undefined $ go x where
  go :: [Int] -> Maybe Int
  go [] = Nothing
  go (x : xs) = let nu = go xs in
   if x == 0
    then nu
    else case nu of
     Nothing -> Just 0
     Just n -> Just (n + 1)

 -- エラーの可能性あり
 bad_root :: Sequence -> Matrix -> Int
 bad_root e s = parent (e : s) (t e) (length s - 1)

 -- エラーの可能性あり
 split :: Sequence -> Matrix -> (Matrix, Matrix)
 split e s = splitAt (bad_root e s + 1) s
