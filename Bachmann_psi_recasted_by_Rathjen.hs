module Oridnal where

  import Prelude
  import System.IO

  data Seq = Seq [Unary] deriving Show

  data Unary = Omega Seq | Psi Seq | Card deriving Show

  comp_s :: Seq -> Seq -> Ordering
  comp_s (Seq a) (Seq b) = go a b
   where
    go :: [Unary] -> [Unary] -> Ordering
    go []       []       = EQ
    go []       _        = LT
    go _        []       = GT
    go (a : as) (b : bs) = comp_u a b <> go as bs

  comp_u :: Unary -> Unary -> Ordering
  comp_u (Omega a) (Omega b) = comp_s a b
  comp_u (Omega a) (Psi b)   = comp_s a (Seq [Psi b])
  comp_u (Omega a) Card      = comp_s a (Seq [Card])
  comp_u (Psi a)   (Omega b) = comp_s (Seq [Psi a]) b
  comp_u (Psi a)   (Psi b)   = comp_s a b
  comp_u (Psi _)   Card      = LT
  comp_u Card      (Omega b) = comp_s (Seq [Card]) b
  comp_u Card      (Psi _)   = GT
  comp_u Card      Card      = EQ

  st_s :: Seq -> Bool
  st_s (Seq x) = go x
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
  st_u Card      = True

  st_o :: Seq -> Bool
  st_o (Seq x) = case x of
    []       -> True
    x' : []  -> case x' of
      Omega _  -> True
      Psi _    -> False
      Card     -> False
    _        -> True

  st_p :: Seq -> Bool
  st_p x = all (\x' -> comp_s x' x == LT) (g1 x)

  g1 :: Seq -> [Seq]
  g1 (Seq y) = case y of
    []      -> []
    u : []  -> g1_u u
    _       -> g1_s y

  g1_u :: Unary -> [Seq]
  g1_u (Omega x) = g x
  g1_u (Psi x)   = g x
  g1_u Card      = []

  g1_s :: [Unary] -> [Seq]
  g1_s []       = []
  g1_s (x : xs) = g (Seq [x]) ++ g1_s xs

  g :: Seq -> [Seq]
  g (Seq x) = Seq x : go_s x
   where
    --
    go_s :: [Unary] -> [Seq]
    go_s [] = []
    go_s (x : xs) = go_u x ++ go_s xs
    --
    go_u :: Unary -> [Seq]
    go_u (Omega x) = Seq [Omega x] : g x
    go_u (Psi x)   = Seq [Psi x] : g x
    go_u Card      = Seq [Card] : []

  data Fundamental = Zero | Succ Seq | Limit (Integer -> Seq)

  fs :: Seq -> Fundamental
  fs (Seq x) = go x
   where
    go x = case mleft x of
      Nothing -> Zero
      Just x' -> if isSucc x'
        then Succ (fpred (Seq x))
        else Limit (fseq (Seq x))

  mleft :: [a] -> Maybe a
  mleft []       = Nothing
  mleft (x : []) = Just x
  mleft (_ : xs) = mleft xs

  isSucc :: Unary -> Bool
  isSucc (Omega (Seq [])) = True
  isSucc _                     = False

  fpred :: Seq -> Seq
  fpred (Seq x) = Seq (go x)
   where
    go :: [Unary] -> [Unary]
    go []       = []
    go (x : []) = []
    go (x : xs) = x : go xs

  fseq :: Seq -> Integer -> Seq
  fseq (Seq x) n = Seq (go x n)
   where
    go :: [Unary] -> Integer -> [Unary]
    go []       _ = []
    go (x : []) n = fseq1 x n : []
    go (x : xs) n = x : (go xs n)

  fseq1 :: Unary -> Integer -> Unary
  fseq1 x = case lef x of
    Omega (Seq []) -> undefined
    Psi (Seq []) -> undefined
    Card -> undefined

  lef :: Unary -> Unary
  lef = undefined


  main :: IO ()
  main = do
    put $ comp_s (Seq []) (Seq []) == EQ
    put $ comp_s (Seq [Psi (Seq [])]) (Seq [Psi (Seq [Card])]) == LT
    put $ st_s (Seq []) == True
    put $ st_s (Seq [Psi (Seq [])]) == True
    put $ st_s (Seq [Psi (Seq [Card])]) == True
    put $ st_s (Seq [Omega (Seq [])]) == True
    put $ st_s (Seq [Omega (Seq []), Omega (Seq [])]) == True
    put $ st_s (Seq [Psi (Seq []), Psi (Seq [])]) == True
    put $ st_s (Seq [Omega (Seq [Psi (Seq [])])]) == False
    put $ st_s (Seq [Omega (Seq [Psi (Seq []), Omega (Seq [])])]) == True
    put $ st_s (Seq [Psi (Seq [Card, Omega (Seq [])])]) == True
    put $ st_s (Seq [Psi (Seq [Card, Psi (Seq [Card])])]) == True
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card])])]) == False
    put $ st_s (Seq [Psi (Seq [Omega (Seq [Psi (Seq [Card]), Omega (Seq [])])])]) == False
    put $ st_s (Seq [Psi (Seq [Omega (Seq [Card, Omega (Seq [])])])]) == True
    put $ g1 (Seq [Omega (Seq [Card, Omega (Seq [])])])
    put $ st_s (Seq [Psi (Seq [Omega (Seq [Omega (Seq [Card, Card])])])]) == True
    put $ g1 (Seq [Omega (Seq [Omega (Seq [Card, Card])])])
    put $ st_s (Seq [Psi (Seq [Card, Card, Psi (Seq [Card])])]) == True
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card]), Omega (Seq [])])]) == False
    put $ st_s (Seq [Psi (Seq [Card, Card, Psi (Seq [Card, Card, Card])])]) == False
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Psi (Seq [Card])]), Psi (Seq [])])]) == False
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card, Card])])]) == False
    put $ g1 (Seq [Psi (Seq [Card, Card])])
    put $ st_s (Seq [Omega (Seq []), Omega (Seq [Omega (Seq [])])]) == False
   where
    put :: Show a => a -> IO ()
    put a = print a >> hFlush stdout
