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
    go []       _        = LT
    go _        []       = GT
    go (a : as) (b : bs) = comp_u a b <> go as bs

  comp_u :: Unary -> Unary -> Ordering
  comp_u (Omega a) (Omega b) = comp_seq a b
  comp_u (Omega a) (Psi b)   = comp_seq a (Sequence [Psi b])
  comp_u (Omega a) Cardinal  = comp_seq a (Sequence [Cardinal])
  comp_u (Psi a)   (Omega b) = comp_seq (Sequence [Psi a]) b
  comp_u (Psi a)   (Psi b)   = comp_seq a b
  comp_u (Psi _)   Cardinal  = LT
  comp_u Cardinal  (Omega b) = comp_seq (Seqeunce [Cardinal]) b
  comp_u Cardinal  (Psi _)   = GT
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
      Omega _  -> True
      Psi _    -> False
      Cardinal -> False
    _        -> True

  st_p :: Sequence -> Bool
  st_p x = all (\x' -> comp_seq x' x == LT) (g1 x)

  g1 :: Sequence -> [Sequence]
  g1 (Sequence y) = case y of
    []      -> []
    u : []  -> g1_u u
    _       -> g1_s y

  g1_u :: Unary -> [Sequence]
  g1_u (Omega x) = g x
  g1_u (Psi x)   = g x
  g1_u Cardinal  = []

  g1_s :: [Unary] -> [Sequence]
  g1_s []       = []
  g1_s (x : xs) = g (Sequence [x]) ++ g1_s xs

  g :: Sequence -> [Sequence]
  g (Sequence x) = Sequence x : go_s x
   where
    --
    go_s :: [Unary] -> [Sequence]
    go_s [] = []
    go_s (x : xs) = go_u x ++ go_s xs
    --
    go_u :: Unary -> [Sequence]
    go_u (Omega x) = Sequence [Omega x] : g x
    go_u (Psi x)   = Sequence [Psi x] : g x
    go_u Cardinal  = Sequence [Cardinal] : []


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
    put $ st_seq (Sequence [Omega (Sequence [Psi (Sequence []), Omega (Sequence [])])]) == True
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Omega (Sequence [])])]) == True
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Psi (Sequence [Cardinal])])]) == True
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Cardinal])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Omega (Sequence [Psi (Sequence [Cardinal]), Omega (Sequence [])])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Omega (Sequence [Cardinal, Omega (Sequence [])])])]) == True -- n
    put $ g1 (Sequence [Omega (Sequence [Cardinal, Omega (Sequence [])])])
    put $ st_seq (Sequence [Psi (Sequence [Omega (Sequence [Omega (Sequence [Cardinal, Cardinal])])])]) == True -- n
    put $ g1 (Sequence [Omega (Sequence [Omega (Sequence [Cardinal, Cardinal])])])
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Cardinal, Psi (Sequence [Cardinal])])]) == True
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Cardinal]), Omega (Sequence [])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Cardinal, Cardinal, Psi (Sequence [Cardinal, Cardinal, Cardinal])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Psi (Sequence [Cardinal])]), Psi (Sequence [])])]) == False
    put $ st_seq (Sequence [Psi (Sequence [Psi (Sequence [Cardinal, Cardinal])])]) == True -- n
    put $ g1 (Sequence [Psi (Sequence [Cardinal, Cardinal])])
   where
    put :: Show a => a -> IO ()
    put a = print a >> putStrLn "" >> hFlush stdout
