module Bashicu where
 import Prelude

 type Matrix = [Sequence]

 type Sequence = [Integer]

 data PIndex = IsRoot | HasParent Integer

 parent :: Matrix -> Integer -> Integer -> PIndex
 parent s 0 x = go (x + 1) where
  go p = if s ! p ! 0 < s ! x ! 0 then HasParent p else if p == length s - 1 then IsRoot else go (p + 1)
 parent s y x = go (x + 1) where
  go p = if p `elem` ancestor s y x && s ! p ! y < s ! x ! y then HasParent p else if p == length s - 1 then IsRoot else go (p + 1)

 (!) :: [a] -> Integer -> a
 [] ! _ = undefined
 (x : xs) ! 0 = x
 (x : xs) ! n = xs ! (n - 1)

 infixl 9 !

 mlength :: Matrix -> Integer
 mlength [] = 0
 mlength (_ : xs) = mlength xs + 1

 slength :: Matrix -> Integer
 slength [] = undefined
 slength (x : _) = go x where
  go [] = 0
  go (_ : xs) = go xs + 1
