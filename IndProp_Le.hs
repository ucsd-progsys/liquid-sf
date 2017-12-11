{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module IndProp_Le where

import Peano
import Language.Haskell.Liquid.NewProofCombinators

data LeProp where
  Le :: Peano -> Peano -> LeProp

data Le where
  Le_n :: Peano -> Le
  Le_S :: Peano -> Peano -> Le -> Le

{-@ data Le [leNat] where
      Le_n :: n:Peano -> Prop (Le n n)
    | Le_S :: n:Peano -> m:Peano -> Prop (Le n m) -> Prop (Le n (S m))
  @-}


--------------------------------------------------------------------------------
-- | Some simple tests
--------------------------------------------------------------------------------
{-@ test_le_1 :: () -> Prop (Le three three) @-}
test_le_1 () = Le_n three

{-@ test_le_2 :: () -> Prop (Le one four) @-}
test_le_2 () = le_1_4
  where
    le_1_1   = Le_n one
    le_1_2   = Le_S one one   le_1_1
    le_1_3   = Le_S one two   le_1_2
    le_1_4   = Le_S one three le_1_3


{-@ test_le_3 :: Prop (Le two one) -> { false } @-}
test_le_3 :: Le -> ()
test_le_3 (Le_S _ Z (Le_n _)) = ()

--------------------------------------------------------------------------------
-- | Le exercises
--------------------------------------------------------------------------------
{-@ le_trans :: m:Peano -> n:Peano -> o:Peano
             -> Prop (Le m n) -> zz:Prop (Le n o) -> Prop (Le m o) / [leNat zz]
  @-}
le_trans :: Peano -> Peano -> Peano -> Le -> Le -> Le
le_trans _ _ _ mn (Le_n _)      = mn
le_trans m n _ mn (Le_S _ o no) = Le_S m o (le_trans m n o mn no)

{-@ zero_le_n :: n:Peano -> Prop (Le Z n) @-}
zero_le_n :: Peano -> Le
zero_le_n Z     = Le_n Z
zero_le_n (S n) = Le_S Z n (zero_le_n n)

{-@ n_le_m__Sn_le_Sm :: n:Peano -> m:Peano -> pf:Prop (Le n m) -> Prop (Le (S n) (S m)) / [leNat pf] @-}
n_le_m__Sn_le_Sm :: Peano -> Peano -> Le -> Le
n_le_m__Sn_le_Sm n m (Le_n _)      = Le_n (S n)
n_le_m__Sn_le_Sm n _ (Le_S _ m nm) = Le_S (S n) ((S m)) (n_le_m__Sn_le_Sm n m nm)

{-@ sn_le_Sm__n_le_m :: n:Peano -> m:Peano -> pf:Prop (Le (S n) (S m)) -> Prop (Le n m) / [leNat pf] @-}
sn_le_Sm__n_le_m :: Peano -> Peano -> Le -> Le
sn_le_Sm__n_le_m n m (Le_n sn)       = Le_n n
sn_le_Sm__n_le_m n m (Le_S sn _ snm) = sn_le_m__n_le_m n m snm

{-@ sn_le_m__n_le_m :: n:Peano -> m:Peano -> pf:Prop (Le (S n) m) -> Prop (Le n m) @-}
sn_le_m__n_le_m :: Peano -> Peano -> Le -> Le
sn_le_m__n_le_m n m pf = le_trans n (S n) m (le_n_sn n) pf

{-@ le_n_sn :: n:Peano -> Prop (Le n (S n)) @-}
le_n_sn :: Peano -> Le
le_n_sn n = Le_S n n (Le_n n)

{-@ le_plus_l :: a:Peano -> b:Peano -> Prop {Le a (plus a b)} @-}
le_plus_l :: Peano -> Peano -> Le
le_plus_l Z     b = zero_le_n b
le_plus_l (S a) b = n_le_m__Sn_le_Sm a (plus a b) (le_plus_l a b)

--------------------------------------------------------------------------------
-- Less-than
--------------------------------------------------------------------------------
{-@ type Lt N M = Prop (Le (S N) M) @-}

{-@ test_lt_1 :: () -> (Lt Z one) @-}
test_lt_1 () = Le_n one

{-@ plus_lt :: n1:Peano -> n2:Peano -> m:Peano -> (Lt {plus n1 n2} m) -> (Lt n1 m) @-}
plus_lt :: Peano -> Peano -> Peano -> Le -> Le
plus_lt n1 n2 m pf = lt_trans_l n1 (plus n1 n2) m (le_plus_l n1 n2) pf


{-@ lt_trans_l :: m:Peano -> n:Peano -> o:Peano
             -> Prop (Le m n) -> (Lt n o) -> (Lt m o)
  @-}
lt_trans_l :: Peano -> Peano -> Peano -> Le -> Le -> Le
lt_trans_l m n o m_n sn_o = le_trans (S m) (S n) o sm_sn sn_o
  where
    sm_sn = n_le_m__Sn_le_Sm m n m_n

{-@ lt_trans_r :: m:Peano -> n:Peano -> o:Peano
               -> (Lt m n) -> Prop (Le n o) -> (Lt m o)
  @-}
lt_trans_r :: Peano -> Peano -> Peano -> Le -> Le -> Le
lt_trans_r m n o sm_n n_o = le_trans (S m) n o sm_n n_o

{-@ lt_S :: n:Peano -> m:Peano -> (Lt n m) -> (Lt n (S m)) @-}
lt_S :: Peano -> Peano -> Le -> Le
lt_S n m n_m = lt_trans_r n m (S m) n_m (le_n_sn m)

{-@ leb_complete :: n:Peano -> m:{Peano | isLe n m} -> Prop (Le n m) / [toNat m] @-}
leb_complete :: Peano -> Peano -> Le
leb_complete Z     Z     = Le_n Z
leb_complete Z     (S m) = Le_S Z m (leb_complete Z m)
leb_complete (S n) (S m) = n_le_m__Sn_le_Sm n m (leb_complete n m)

{-@ leb_correct :: n:Peano -> m:Peano -> pf:Prop (Le n m) -> {isLe n m} / [toNat m] @-}
leb_correct :: Peano -> Peano -> Le -> ()
leb_correct Z     _     _               = ()
leb_correct _     _     (Le_n n)        = isLe_n n
leb_correct (S n) (S m) (Le_S _ _ sn_m) = leb_correct n m n_m
  where
    n_m                                 = sn_le_m__n_le_m n m sn_m

{-@ isLe_n :: n:Peano -> { isLe n n } @-}
isLe_n Z     = ()
isLe_n (S n) = isLe_n n

{-@ isLe_trans :: n:Peano -> m:{Peano | isLe n m} -> o:{Peano | isLe m o} -> {isLe n o} @-}
isLe_trans :: Peano -> Peano -> Peano -> ()
isLe_trans n m o = leb_correct n o (le_n_o)
  where
    le_n_m       = leb_complete n m
    le_m_o       = leb_complete m o
    le_n_o       = le_trans   n m o le_n_m le_m_o

--------------------------------------------------------------------------------
-- | Syntactic sugar for prelude -----------------------------------------------
--------------------------------------------------------------------------------
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible _ = undefined

{-@ withPf :: x:a -> b -> {v:a | v = x} @-}
withPf :: a -> b -> a
withPf x y = x


--------------------------------------------------------------------------------
-- | Crufty termination stuff [How to auto-generate?] --------------------------
--------------------------------------------------------------------------------

{-@ measure leNat      @-}
{-@ leNat :: Le -> Nat @-}
leNat :: Le -> Int
leNat (Le_n _)     = 0
leNat (Le_S _ _ p) = 1 + leNat p
