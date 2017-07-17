# liquid-sf

Port "Software Foundations" to LiquidHaskell

* VFA -> Perm ->  Sort -> *Selection* -> SearchTree -> Redblack
             `-> Trie `-> Multiset                 `-> ADT -> Priqueue -> Binom

- [*] VFA
- [*] Perm
- [*] Sort
- [ ] Selection
- [ ] SearchTree
- [ ] Redblack
- [ ] Trie
- [ ] Multiset
- [ ] ADT
- [ ] Priqueue
- [ ] Binom



  type State = St { ptr :: STRef Int }

  type ST a = State -> (a, State)




## Issues

`Sort.hs`

- {-@ TODO:LH #1004 thmInsertSorted :: x:a -> ys:{List a | sorted ys} -> { sorted (insert x ys) } @-}
- {-@ TODO:LH #1004 thmSortSorted :: xs:List a -> { sorted (sort xs) } @-}
- https://github.com/ucsd-progsys/liquidhaskell/issues/1004

## Reasoning about Stores

Maybe the below is crap; just prove the law* for each map implementation.

### Stores via abstract refinements

```haskell
data Map k v <r :: k -> v -> bool>

init  :: val:v -> Map <{\ _ v -> v = val}> k v
empty :: Map k v <{\key val -> False}>
get   :: key:k -> Map<r> k v -> v<r key>
put   :: key:k -> val:v -> Map<r> k v ->
```

### Laws for an abstract `Store`

You get to _assume_ these.

```
lawStoreEmp :: key:k
            -> { sel key emp = None }
lawStoreEq  :: key:k -> val:v -> s:Store k v
            -> { sel key (sto key val s) = s }
lawStoreNe  :: key':k -> key:{k | key /= key'} -> val:v -> s:Store k v
            -> { sel key' (sto key val s) = sel key' s }
```

### Equivalence

A "proof" of equivalence is a function of the below type,
that says that a dictionary `m` is equivalent to the store `s`

```
type Eq m s = key:k -> { get key m = sel m s }
```

### Correctness

Suppose you have an implementation of a `Map` with the following API:

```haskell
empty :: Map k v
get   :: k -> Map k v -> Option v
put   :: k -> v -> Map k v -> Map k v
```

To prove a given implementation of a `Map` is correct, show that:

```
thmEmp :: Eq empty emp
thmPut :: m:Map k v -> s:{Store k v | Eq m s}  -> key:k -> val:v
       -> { Eq (put key val m) (sto key val s) }
```

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
