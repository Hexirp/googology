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
  comp_u Cardinal  (Omega b) = comp_seq (Sequence [Cardinal]) b
  comp_u Cardinal  (Psi _)   = GT
  comp_u Cardinal  Cardinal  = EQ

  st_s :: Sequence -> Bool
  st_s (Sequence x) = go x
   where
    go :: [Unary] -> Bool
    go []       = True
    go (x : xs) = st_u x && dec x xs && go xs

  dec :: Unary -> [Unary] -> Bool
  dec x []       = True
  dec x (y : ys) = comp_u x y /= LT && dec x ys

  st_u :: Unary -> Bool
  st_u (Omega x) = st_o x && st_s x
  st_u (Psi x)   = st_p x && st_s x
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

  data Fundamental = Zero | Succ Sequence | Limit (Integer -> Sequence)

  fs :: Sequence -> Fundamental
  fs (Sequence x) = go x
   where
    go x = case mleft x of
      Nothing -> Zero
      Just x' -> if isSucc x'
        then Succ (fpred (Sequence x))
        else Limit (fseq (Sequence x))

  mleft :: [a] -> Maybe a
  mleft []       = Nothing
  mleft (x : []) = Just x
  mleft (_ : xs) = mleft xs

  isSucc :: Unary -> Bool
  isSucc (Omega (Sequence [])) = True
  isSucc _                     = False

  fpred :: Sequence -> Sequence
  fpred (Sequence x) = Sequence (go x)
   where
    go :: [Unary] -> [Unary]
    go []       = []
    go (x : []) = []
    go (x : xs) = x : go xs

  fseq :: Sequence -> Integer -> Sequence
  fseq (Sequence x) n = Sequence (go x n)
   where
    go :: [Unary] -> Integer -> [Unary]
    go []       _ = []
    go (x : []) n = fseq1 x n : []
    go (x : xs) n = x : (go xs n)

  fseq1 :: Unary -> Integer -> Unary
  fseq1 = undefined


  main :: IO ()
  main = do
    put $ comp_seq (Sequence []) (Sequence []) == EQ
    put $ comp_seq (Sequence [Psi (Sequence [])]) (Sequence [Psi (Sequence [Cardinal])]) == LT
    put $ st_s (Sequence []) == True
    put $ st_s (Sequence [Psi (Sequence [])]) == True
    put $ st_s (Sequence [Psi (Sequence [Cardinal])]) == True
    put $ st_s (Sequence [Omega (Sequence [])]) == True
    put $ st_s (Sequence [Omega (Sequence []), Omega (Sequence [])]) == True
    put $ st_s (Sequence [Psi (Sequence []), Psi (Sequence [])]) == True
    put $ st_s (Sequence [Omega (Sequence [Psi (Sequence [])])]) == False
    put $ st_s (Sequence [Omega (Sequence [Psi (Sequence []), Omega (Sequence [])])]) == True
    put $ st_s (Sequence [Psi (Sequence [Cardinal, Omega (Sequence [])])]) == True
    put $ st_s (Sequence [Psi (Sequence [Cardinal, Psi (Sequence [Cardinal])])]) == True
    put $ st_s (Sequence [Psi (Sequence [Psi (Sequence [Cardinal])])]) == False
    put $ st_s (Sequence [Psi (Sequence [Omega (Sequence [Psi (Sequence [Cardinal]), Omega (Sequence [])])])]) == False
    put $ st_s (Sequence [Psi (Sequence [Omega (Sequence [Cardinal, Omega (Sequence [])])])]) == True
    put $ g1 (Sequence [Omega (Sequence [Cardinal, Omega (Sequence [])])])
    put $ st_s (Sequence [Psi (Sequence [Omega (Sequence [Omega (Sequence [Cardinal, Cardinal])])])]) == True
    put $ g1 (Sequence [Omega (Sequence [Omega (Sequence [Cardinal, Cardinal])])])
    put $ st_s (Sequence [Psi (Sequence [Cardinal, Cardinal, Psi (Sequence [Cardinal])])]) == True
    put $ st_s (Sequence [Psi (Sequence [Psi (Sequence [Cardinal]), Omega (Sequence [])])]) == False
    put $ st_s (Sequence [Psi (Sequence [Cardinal, Cardinal, Psi (Sequence [Cardinal, Cardinal, Cardinal])])]) == False
    put $ st_s (Sequence [Psi (Sequence [Psi (Sequence [Psi (Sequence [Cardinal])]), Psi (Sequence [])])]) == False
    put $ st_s (Sequence [Psi (Sequence [Psi (Sequence [Cardinal, Cardinal])])]) == False
    put $ g1 (Sequence [Psi (Sequence [Cardinal, Cardinal])])
    put $ st_s (Sequence [Omega (Sequence []), Omega (Sequence [Omega (Sequence [])])]) == False
   where
    put :: Show a => a -> IO ()
    put a = print a >> hFlush stdout
