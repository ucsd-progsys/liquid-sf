# liquid-sf

Port "Software Foundations" to LiquidHaskell

## Issues 

`Sort.hs`

- Wierd LH sort-error crash
    
  https://github.com/ucsd-progsys/liquidhaskell/issues/1004

## Inductive Predicates 

```
{-@ measure permutation :: List a -> List a -> Bool @-}

data Permutation a where

  PermNil  :: { permutation Nil Nil }

  PermSkip :: x:a -> l:List a -> l':List a -> { permutation l l' } ->
              { permutation (Cons x l) (Cons x l') }

  PermSwap :: x:a -> y:a -> l:List A ->
              { permutation (Cons x (Cons y l)) (Cons x (Cons y l)) }

  PermTrans :: l1:List a -> l2: List a -> l3:List a ->
              { permutation l1 l2 } -> {permutation l2 l3} ->
              { permutation l1 l3 }

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    perm_nil : Permutation
  | perm_skip : forall (x : A) (l l' : list A),
                Permutation l l' ->
                Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.
```
