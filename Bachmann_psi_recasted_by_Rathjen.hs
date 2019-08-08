module Oridnal where

  import Prelude

  data Sequence = Sequence [Unary]

  data Unary = Omega Sequence | Psi Sequence | Cardinal

  comp_seq :: Sequence -> Sequence -> Ordering
  comp_seq (Sequence a) (Sequence b) = go a b
   where
    go :: [Unary] -> [Unary] -> Ordering
    go []       []       = EQ
    go []       (b : bs) = LT
    go (a : as) []       = GT
    go (a : as) (b : bs) = case comp_u a b of
      LT -> LT
      EQ -> go as bs
      GT -> GT

  comp_u :: Unary -> Unary -> Ordering
  comp_u (Omega a) (Omega b) = comp_seq a b
  comp_u (Omega a) (Psi b)   = comp_seq a (Sequence [Psi b])
  comp_u (Omega a) Cardinal  = LT
  comp_u (Psi a)   (Omega b) = comp_seq (Sequence [Psi a]) b
  comp_u (Psi a)   (Psi b)   = comp_seq a b
  comp_u (Psi a)   Cardinal  = LT
  comp_u Cardinal  (Omega b) = GT
  comp_u Cardinal  (Psi b)   = GT
  comp_u Cardinal  Cardinal  = EQ

  st_seq :: Sequence -> Bool
  st_seq (Sequence x) = go x
   where
    go :: [Unary] -> Bool
    go []       = True
    go (x : xs) = st_u x && dec x xs && go xs

  dec :: Unary -> [Unary] -> Bool
  dec x []       = True
  dex x (y : ys) = comp_u x y == LT && dec x ys

  st_u :: Unary -> Bool
  st_u (Omega x) = o_u x && st_seq x
  st_u (Psi x) = g_u x && st_seq x
  st_u Cardinal = True

  o_u :: Sequence -> Bool
  o_u (Sequence x) = case x of
    []       -> True
    x' : []  -> case x' of
      Omega x'' -> True
      Psi x''   -> False
      Cardinal  -> False
    x' : xs' -> True

  g_u :: Sequence -> Bool
  g_u x = go_seq x x
   where
    --
    go_seq :: Sequence -> Sequence -> Bool
    go_seq x (Sequence y) = go_us x y
    --
    go_us :: Sequence -> [Unary] -> Bool
    go_us x []       = True
    go_us x (y : ys) = go_u x y && go_us x ys
    --
    go_u :: Sequence -> Unary -> Bool
    go_u x (Omega y) = comp_seq x (Sequence [Omega y])  == GT && go_seq x y -- r
    go_u x (Psi y)   = comp_seq x (Sequence [Psi y])    == GT && go_seq x y
    go_u x Cardinal  = comp_seq x (Sequence [Cardinal]) == GT


  main :: IO ()
  main = return ()
