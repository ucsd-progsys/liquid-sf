{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--no-totality"                         @-}

{-@ infix : @-}

module ADT where
import Prelude hiding(abs,repeat)
import Language.Haskell.Liquid.ProofCombinators 
import qualified Language.Haskell.Liquid.Bag	as B
import Permutations


{-@ reflect fibonacci @-}
{-@ fibonacci :: Nat -> Nat @-}
fibonacci :: Int -> Int
fibonacci 0 = 1
fibonacci 1 = 1
fibonacci n = fibonacci (n-1) + fibonacci (n-2)


{-@ reflect repeat @-}
{-@ repeat :: (a -> a) -> a -> Nat -> a @-}
repeat :: (a -> a) -> a -> Int -> a
repeat f x 0 = x
repeat f x n = f (repeat f x (n-1))


{-@reflect step@-}
{-@ step :: xs:[Nat] -> ys:[Nat]@-}
step :: [Int] -> [Int]
step []       = []
step [x]      = [x,x]
step (x:y:xs) = (x+y):(x:y:xs)


{-@reflect nth1@-}
{-@nth1 :: Nat  -> [a] -> a -> a@-}
nth1 :: Int -> [a] -> a -> a
nth1 0 []     d = d
nth1 0 (x:xs) d = x
nth1 n (x:xs) d = nth1 (n-1) xs d

{-@reflect firstn@-}
{-@firstn :: Nat  -> [a] -> [a] @-}
firstn :: Int -> [a] -> [a]
firstn 0 l      = []
firstn n []     = []
firstn n (x:xs) = x:firstn (n-1) xs


{-@ reflect lHd @-}
{-@ lHd :: (Ord a) => [a]  -> a @-}
lHd :: (Ord a) => [a] -> a
lHd (x:_) = x


{-@reflect fib@-}
{-@ fib :: Nat -> Int @-}
fib :: Int -> Int
fib n = lHd ( repeat step (1:(0:(0:([])))) n)

-----------------------------------------------------------
data Listish = L Int Int Int

{-@reflect create@-}
create :: Int -> Int -> Int -> Listish
create x y z = L x y z


{-@reflect cons@-}
cons :: Int ->  Listish -> Listish
cons i (L x y z) = (L i x y)


{-@ reflect lHd2 @-}
{-@ lHd2 :: Listish  -> Int @-}
lHd2 :: Listish -> Int
lHd2 (L x y z) = x

{-@ reflect stepish@-}
stepish :: Listish -> Listish
stepish (L x y z) = cons (x+y) (L x y z)


{-@ reflect fibish @-}
{-@ fibish :: Nat -> Int @-}
fibish :: Int -> Int
fibish n = lHd2 ( repeat stepish (create 1 0 0) n)


{-@ lemma_nth_firstn :: al:[a] -> d:a -> i: Nat -> j: {Nat| i<j} -> {  nth1 i (firstn j al) d = nth1 i al d  } @-}
lemma_nth_firstn :: [a] -> a -> Int -> Int -> Proof
lemma_nth_firstn [] d i j     = trivial
lemma_nth_firstn (x:xs) d i j 
        | i == 0  =   nth1 0 (  firstn j (x:xs)) d
                   ==. nth1 0 (  firstn j (x:xs)) d
                   ==. nth1 0 (x:firstn (j-1) xs) d
                   ==. x
                   ==. nth1 0 (x:xs) d
                   *** QED

        | otherwise =   nth1 i (firstn j (x:xs) ) d
                    ==. nth1 i (x:firstn (j-1) (xs) ) d
                    ==. nth1 (i-1) (firstn (j-1) (xs) ) d
                    ==. nth1 (i-1) xs d  ? lemma_nth_firstn xs d (i-1) (j-1)
                    ==. nth1 i (x:xs) d
                    *** QED



{-@ reflect l_Abs @-}
l_Abs :: [Int] -> Listish -> Bool
l_Abs [] (L x y z)            = False
l_Abs [x1] (L x y z)          = False
l_Abs [x1,x2] (L x y z)       = False
l_Abs (x1:x2:x3:xs) (L x y z) = if(x==x1 && y==x2 && z==x3) then True else False


{-@lemma_step_relate:: al:[Int] -> bl: {Listish | l_Abs al bl} -> {l_Abs  (step al) (stepish bl)} @-}
lemma_step_relate:: [Int] -> Listish -> Proof
lemma_step_relate al bl = trivial

{-@lemma_repeat_step_relate:: n:Nat -> al:[Nat] -> bl: {Listish | l_Abs al bl} -> {l_Abs (repeat step al n) (repeat stepish bl n)} @-}
lemma_repeat_step_relate:: Int -> [Int] -> Listish -> Proof
lemma_repeat_step_relate 0 al bl = trivial
lemma_repeat_step_relate n al bl = l_Abs (repeat step al n) (repeat stepish bl n)
                                 ==. l_Abs (step (repeat step al (n-1))) (stepish (repeat stepish bl (n-1)))
                                 ==. True ? (lemma_repeat_step_relate (n-1) al bl) &&& lemma_step_relate (repeat step al (n-1)) (repeat stepish bl (n-1))
                                 *** QED



{-@ fibish_correct :: n:Nat -> {fibish n = fib n} @-}
fibish_correct :: Int -> Proof
fibish_correct n = (lemma_repeat_step_relate n (1:(0:(0:([])))) (create 1 0 0)) *** QED
