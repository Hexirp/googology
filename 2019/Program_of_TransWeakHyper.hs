﻿import Prelude hiding (succ)
import System.IO

data Formula = One | Omega | Node Formula Formula Formula deriving (Eq, Ord, Show)

s :: Formula -> Formula
s One = One
s Omega = Omega
s (Node a One (Node b One c)) = s (Node (Node a One b) One c)
s (Node a One b) = Node (s a) One (s b)
s (Node a b One) = s a
s (Node a (Node b One One) (Node c One One)) = s (Node (Node a (Node b One One) c) b a)
s (Node a b c) = Node (s a) (s b) (s c)

one :: Formula -> Bool
one One = True
one _ = False

succ :: Formula -> Bool
succ (Node a One One) = True
succ _ = False

limit :: Formula -> Bool
limit a = not (one a || succ a)

p :: Formula -> Formula
p (Node a One One) = a
p a = a

t :: Formula -> Integer -> Formula
t Omega 1 = One
t Omega n = Node (t Omega (n - 1)) One One
t (Node a b c) n = if limit b
 then Node a (t b n) c
 else if limit c
  then Node a b (t c n)
  else Node a b c
t a n = a

iter :: (a -> a) -> Integer -> a -> a
iter f 0 a = a
iter f n a = f (iter f (n - 1) a)

f :: Formula -> Integer -> Integer
f a n = let a' = s a in
 if one a'
  then 2 * n
  else if succ a'
   then iter (f (p a')) n n
   else if limit a'
    then f (t a' n) n
    else 1

o :: Integer -> Formula
o 1 = Omega
o n = Node Omega (o (n - 1)) Omega

twh :: Integer -> Integer
twh n = f (o n) n

ntwh :: Integer
ntwh = twh 10000


-- ここからは計算過程を見やすくするためのプログラム

sf :: Formula -> String -> String
sf One = (:) '1'
sf Omega = (:) 'ω'
sf (Node a b c) = (:) '(' . sf a . (:) ')' . (:) '[' . sf b . (:) ']' . (:) '(' . sf c . (:) ')'

fe :: Integer -> Formula -> IO ()
fe n a = let a' = s a in
 if one a'
  then putStrLn (sf a' []) >> return ()
  else if succ a'
   then putStrLn (sf a' []) >> fe n (p a')
   else if limit a'
    then putStrLn (sf a' []) >> fe n (t a' n)
    else putStrLn (sf a' []) >> putStrLn "error" >> return ()

main :: IO ()
main = hSetBuffering stdout NoBuffering >> fe 3 (Node Omega (Node One One One) Omega)

{-

> fe 3 (Node Omega Omega Omega)
(ω)[ω](ω)
(ω)[((1)[1](1))[1](1)](ω)
((ω)[(1)[1](1)](ω))[(1)[1](1)](ω)
(((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1]((ω)[(1)[1](1)](ω))
(((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](((ω)[1](ω))[1](ω))
(((((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω))[1](ω))[1](1))[1](1))[1](1)
((((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω))[1](ω))[1](1))[1](1)
(((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω))[1](ω))[1](1)
((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω))[1](ω)
((((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω))[1](1))[1](1))[1](1)
(((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω))[1](1))[1](1)
((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω))[1](1)
(((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](ω)
(((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](1))[1](1))[1](1)
((((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](1))[1](1)
(((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω)))[1](1)
((ω)[(1)[1](1)](ω))[1]((ω)[(1)[1](1)](ω))
((ω)[(1)[1](1)](ω))[1](((ω)[1](ω))[1](ω))
((((((ω)[(1)[1](1)](ω))[1](ω))[1](ω))[1](1))[1](1))[1](1)
(((((ω)[(1)[1](1)](ω))[1](ω))[1](ω))[1](1))[1](1)
((((ω)[(1)[1](1)](ω))[1](ω))[1](ω))[1](1)
(((ω)[(1)[1](1)](ω))[1](ω))[1](ω)
(((((ω)[(1)[1](1)](ω))[1](ω))[1](1))[1](1))[1](1)
((((ω)[(1)[1](1)](ω))[1](ω))[1](1))[1](1)
(((ω)[(1)[1](1)](ω))[1](ω))[1](1)
((ω)[(1)[1](1)](ω))[1](ω)
((((ω)[(1)[1](1)](ω))[1](1))[1](1))[1](1)
(((ω)[(1)[1](1)](ω))[1](1))[1](1)
((ω)[(1)[1](1)](ω))[1](1)
(ω)[(1)[1](1)](ω)
((ω)[1](ω))[1](ω)
((((ω)[1](ω))[1](1))[1](1))[1](1)
(((ω)[1](ω))[1](1))[1](1)
((ω)[1](ω))[1](1)
(ω)[1](ω)
(((ω)[1](1))[1](1))[1](1)
((ω)[1](1))[1](1)
(ω)[1](1)
ω
((1)[1](1))[1](1)
(1)[1](1)
1

-}
