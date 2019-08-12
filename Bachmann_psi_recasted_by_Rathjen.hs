module Oridnal where

  import Prelude
  import System.IO

  data Sequence = Sequence [Unary] deriving Show

  data Unary = Omega Sequence | Psi Sequence | Cardinal deriving Show

  comp_seq :: Sequence -> Sequence -> Ordering
  comp_seq (Sequence a) (Sequence b) = go a b
   where
    go :: [Unary] -> [Unary] -> Ordering
    go []       []       = EQ
    go []       (_ : _)  = LT
    go (_ : _)  []       = GT
    go (a : as) (b : bs) = comp_u a b <> comp_seq

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
  dec x (y : ys) = comp_u x y /= LT && dec x ys

  st_u :: Unary -> Bool
  st_u (Omega x) = st_o x && st_seq x
  st_u (Psi x)   = st_p x && st_seq x
  st_u Cardinal  = True

  st_o :: Sequence -> Bool
  st_o (Sequence x) = case x of
    []       -> True
    x' : []  -> case x' of
      Omega x'' -> True
      Psi x''   -> False
      Cardinal  -> False
    x' : xs' -> True

  st_p :: Sequence -> Bool
  st_p x = all (\x' -> comp_seq x' x == LT) (g_1 x)
   where
    --
    g_1 :: Sequence -> [Sequence]
    g_1 x (Sequence y) = case y of
      []      -> []
      u : []  -> g_1_u u
      _       -> g_1_s y
    --
    g_1_u :: Unary -> [Sequence]
    g_1_u (Omega x) = g x
    g_1_u (Psi x)   = g x
    g_1_u Cardinal  = []
    --
    g_1_s :: [Sequence] -> [Sequence]
    g_1_s []       = []
    g_1_s (x : xs) = g x ++ g_1_s xs
    --
    g :: Sequence -> [Sequence]
    g (Sequence x) = go_seq x
     where
      --
      go_s :: [Unary] -> [Sequence]
      go_s [] = []
      go_s (x : xs) = go_u x ++ go_s xs
      --
      go_u :: Unary -> [Sequence]
      go_u (Omega x) = Omega x : g x
      go_u (Psi x)   = Psi x : g x
      go_u Cardinal  = Cardinal : []


  main :: IO ()
  main = do
    put $ comp_seq (Sequence []) (Sequence []) == EQ
    put $ comp_seq (Sequence [Psi (Sequence [])]) (Sequence [Psi (Sequence [Cardinal])]) == LT
    put $ st_seq (Sequence []) == True
    put $ st_seq (Sequence [Psi (Sequence [])]) == True
    put $ st_seq (Sequence [Psi (Sequence [Cardinal])]) == True
    put $ st_seq (Sequence [Omega (Sequence [])]) == True
    put $ st_seq (Sequence [Omega (Sequence []), Omega (Sequence [])]) == True
    put $ st_seq (Sequence [Psi (Sequence []), Psi (Sequence [])]) == True
    put $ st_seq (Sequence [Omega (Sequence [Psi (Sequence [])])]) == False
    put $ st_seq (Sequence [Omega (Sequence [Psi (Sequence []), Omega (Sequence [])])]) == True -- n
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Omega (Sequence [])])]) == True -- n
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Psi (Sequence [Cardinal])])]) == True -- n
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Cardinal])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Omega (Sequence [Psi (Sequence [Cardinal]), Omega (Sequence [])])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Omega (Sequence [Cardinal, Omega (Sequence [])])])]) == True -- n
    put $ st_seq (Sequence [Psi (Sequence [Omega (Sequence [Omega (Sequence [Cardinal, Cardinal])])])]) == True -- n
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Cardinal, Psi (Sequence [Cardinal])])]) == True -- n
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Cardinal]), Omega (Sequence [])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Cardinal, Psi (Sequence [Cardinal, Cardinal, Cardinal])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Psi (Sequence [Cardinal])]), Psi (Sequence [])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Cardinal, Cardinal])])]) == True -- n
   where
    put :: Show a => a -> IO ()
    put a = print a >> putStrLn "" >> hFlush stdout
