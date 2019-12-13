{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}


module Lists where 
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, (++), reverse, pred, (^))


{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a] 
[] ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ ys)

{-@ lemma_app_Nil2 :: xs:_ -> { xs ++ [] = xs } @-}
lemma_app_Nil2 :: [a] -> Proof 
lemma_app_Nil2 []     = ()
lemma_app_Nil2 (x:xs) = lemma_app_Nil2 xs 


{-@ appendAssoc :: xs:_ -> ys:_ -> zs:_ -> { xs ++ (ys ++ zs) = (xs ++ ys) ++ zs } @-}
appendAssoc :: [a] -> [a] -> [a] -> Proof                
appendAssoc [] _ _       = trivial
appendAssoc (_:xs) ys zs = appendAssoc xs ys zs


{-@ app_assoc4 ::  xs:_ -> ys:_ -> zs:_ -> ws:_ ->{ xs ++ (ys ++ (zs ++ ws)) = ((xs ++ ys) ++ zs) ++ ws } @-}
app_assoc4 :: [a] -> [a] -> [a] -> [a] -> Proof
app_assoc4 [] ys zs ws     = appendAssoc ys zs ws
app_assoc4 (x:xs) ys zs ws = app_assoc4 xs ys zs ws


{-@ measure length @-}
{-@ length :: [a] -> Nat @-}
length :: [a] -> Int 
length [] = 0 
length (x:xs) = 1 + length xs


{-@ app_length ::  xs:_ -> ys:_ -> { length (xs ++ ys) == length xs + length ys } @-}
app_length :: [a] -> [a] -> Proof
app_length [] ys     = trivial
app_length (x:xs) ys = app_length xs ys


{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]
reverse (x:xs) = reverse xs ++ [x]


{-@ lemma_rev_app ::  xs:_ -> ys:_ -> {reverse (xs ++ ys) = reverse (ys) ++ reverse (xs)} @-}
lemma_rev_app :: [a] -> [a] -> Proof
lemma_rev_app [] ys = lemma_app_Nil2 (reverse ys)
lemma_rev_app (x:xs) ys=[ lemma_rev_app xs ys, appendAssoc (reverse ys) (reverse xs) [x] ] *** QED


{-@ theorem_rev_rev ::  xs:_ -> { reverse (reverse xs) =  xs } @-}
theorem_rev_rev :: [a] ->  Proof
theorem_rev_rev [] = trivial
theorem_rev_rev (x:xs)=[lemma_rev_app (reverse xs) ([x]), theorem_rev_rev xs] *** QED


{-@ rev_length :: xs:_ ->{ length (reverse xs) == length xs } @-}
rev_length :: [a] -> Proof
rev_length [] = trivial
rev_length (x:xs)=[ app_length (reverse xs) [x], rev_length xs, app_length [x] xs ] *** QED


{-@ reflect nonzeros @-}
nonzeros ::  [Int] -> [Int]
nonzeros [] = []
nonzeros (x:xs) = if (x==0) then nonzeros xs else x:(nonzeros xs)


{-@  nonzeros_app ::  xs:_ -> ys:_ -> { nonzeros (xs ++ ys) = (nonzeros xs) ++ (nonzeros ys) } @-}
nonzeros_app :: [Int] -> [Int] -> Proof
nonzeros_app [] ys = trivial
nonzeros_app (0:xs) ys = nonzeros_app xs ys  
nonzeros_app (x:xs) ys = nonzeros_app xs ys


{-@ reflect pred @-}
pred :: Int -> Int
pred n 
  | n == 0 = 0
  | otherwise = n-1


{-@ lHd :: (Ord a) => {v: [a] | len v > 0} -> a @-}
lHd :: (Ord a) => [a] -> a
lHd (x:_) =x


{-@ reflect lTl @-}
lTl :: (Ord a) =>  [a] -> [a]
lTl [] = []
lTl (_:xs) = xs


{-@ tl_length_pred ::  xs:_ -> { pred (length xs) == length (lTl xs) } @-}
tl_length_pred :: [a] -> Proof
tl_length_pred []     = trivial
tl_length_pred (x:xs) = tl_length_pred xs


{-@ reflect beq_list @-}
beq_list :: [Int] -> [Int] -> Bool
beq_list [] []         = True
beq_list [] _          = False
beq_list _ []          = False
beq_list (x:xs) (y:ys) = if (x==y) then (beq_list xs ys) else False


{-@ beq_natlist_refl ::  xs: [Nat] -> { beq_list xs xs } @-}
beq_natlist_refl :: [Int]  -> Proof
beq_natlist_refl []     = trivial
beq_natlist_refl (x:xs) = beq_natlist_refl xs
