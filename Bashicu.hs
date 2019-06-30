module Bashicu where
 import Prelude

 type Matrix = [Sequence]

 type Sequence = [Integer]

 data PIndex = IsRoot | HasParent Integer

 parent :: Matrix -> Integer -> Integer -> PIndex
 parent s 0 x = go (x + 1) where
  go p = if s ! p ! 0 < s ! x ! 0 then HasParent p else if p == length s

 (!) :: [a] -> Integer -> a
 [] ! n = undefined
 (x : xs) ! 0 = x
 (x : xs) ! n = xs ! (n - 1)

 infixl 9 !

 mlength :: Matrix -> Integer
 mlength [] = 0
 mlength (x : xs) = mlength xs + 1

 slength :: Matrix -> Integer
 slength [] = undefined
 slength (x : xs) = go x where
  go [] = 0
  go (x : xs) = go xs + 1
