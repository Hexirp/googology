hyp :: (Integer -> Integer) -> Integer -> Integer -> Integer
hyp f 0 x = x
hyp f n x = f (hyp f (n - 1) x)

er :: Integer -> Integer -> Integer
er a 0 = a
er a 1 = 0
er a n = 1

hyper :: Integer -> Integer -> Integer -> Integer
hyper a 0 b = b + 1
hyper a n b = hyp (\x -> hyper a (n - 1)) b (er a (n - 1))

{-
 -
 - hyp :: (Integer -> Integer) -> Integer -> Integer -> Integer
 - hyp f 0 x = x
 - hyp f n x | succ n  = f (hyp f (n - 1) x)
 -           | limit n = sup { hyp f i x | i < n }
 -
 - er :: Integer -> Integer -> Integer
 - er a 0 = a
 - er a 1 = 0
 - er a n = 1
 -
 - hyper :: Integer -> Integer -> Integer -> Integer
 - hyper a 0 b = b + 1
 - hyper a n b | succ n  = hyp (\x -> hyper a (n - 1)) b (er a (n - 1))
 -             | limit n = sup { hyper a i b | i < n }
 -
 -}


whyp :: (Integer -> Integer) -> Integer -> Integer -> Integer
whyp f 0 x = undefined
whyp f 1 x = x
whyp f n x = f (whyp f (n - 1) x)

whyper :: Integer -> Integer -> Integer -> Integer]
whyper a 0 b = undefined
whyper a 1 b = a + b
whyper a n b = whyp (\x -> hyper x (n - 1) a) b a

{-
 -
 - whyp :: (Integer -> Integer) -> Integer -> Integer -> Integer
 - whyp f 0 x = undefined
 - whyp f 1 x = x
 - whyp f n x | succ n  = f (whyp f (n - 1) x)
 -            | limit n = sup { whyp f i x | i < n /\ n <> 0 }
 -
 - whyper :: Integer -> Integer -> Integer -> Integer
 - whyper a 0 b = undefined
 - whyper a 1 b = a + b
 - whyper a n b | succ n  = whyp (\x -> hyper x (n - 1) a) b a
 -              | limit n = sup { whyper a i b | i < n /\ n <> 0 }
 -
 -}
