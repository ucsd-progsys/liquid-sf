{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module Ev where

import Peano
import Language.Haskell.Liquid.NewProofCombinators

data EvProp where
  Ev :: Peano -> EvProp

data Ev where
  EZ  :: Ev
  ESS :: Peano -> Ev -> Ev

{-@ data Ev [evNat] where
      EZ  :: Prop (Ev Z)
    | ESS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))
  @-}

{-@ test :: n:Peano -> Prop (Ev (S (S n))) -> Prop (Ev n) @-}
test :: Peano -> Ev -> Ev
test n (ESS m q) = q

{-@ reflect isEven @-}
isEven :: Peano -> Bool
isEven Z         = True
isEven (S Z)     = False
isEven (S (S n)) = isEven n

{-@ thm1 :: n:Peano -> {v:_ | isEven n} -> Prop (Ev n) @-}
thm1 :: Peano -> () -> Ev
thm1 Z _          = EZ
thm1 (S (S n)) pf = ESS n (thm1 n ())

{-@ thm2 :: n:Peano -> pf:(Prop (Ev n)) -> {isEven n} / [evNat pf] @-}
thm2 :: Peano -> Ev -> ()
thm2 n EZ         = ()
thm2 n (ESS m pf) = thm2 m pf

{-@ ev4 :: Prop (Ev (S (S (S (S Z))))) @-}
ev4 :: Ev
ev4 = ESS (S (S Z)) (ESS Z EZ)

{-@ reflect plus4 @-}
plus4 :: Peano -> Peano
plus4 n = S (S (S (S n)))

{-@ ev_plus4 :: n:Peano -> Prop (Ev n) -> Prop (Ev (plus4 n)) @-}
ev_plus4 :: Peano -> Ev -> Ev
ev_plus4 n pf = ESS (S (S n)) (ESS n pf)

{-@ succ_double :: n:Peano -> { double (S n) = S (S (double n)) } @-}
succ_double :: Peano -> ()
succ_double n = plus_succ_r n n

{-@ isEven_double :: n:Peano -> { isEven (double n) } @-}
isEven_double :: Peano -> ()
isEven_double Z     = ()
isEven_double (S n) = succ_double n &&& isEven_double n

{-@ ev_double :: n:Peano -> Prop (Ev (double n)) @-}
ev_double :: Peano -> Ev
ev_double n = thm1 (double n) (isEven_double n)

{-@ reflect minus2 @-}
minus2 n = prev (prev n)

{-@ ev_minus2 :: n:Peano -> Prop (Ev n) -> Prop (Ev (minus2 n)) @-}
ev_minus2 :: Peano -> Ev -> Ev
ev_minus2 Z         _          = EZ
ev_minus2 (S Z)     _          = EZ
ev_minus2 (S (S n)) (ESS _ pf) = pf

{-@ evSS_ev :: n:Peano -> Prop (Ev (S (S n))) -> Prop (Ev n) @-}
evSS_ev :: Peano -> Ev -> Ev
evSS_ev n (ESS _ pf) = pf

{-@ one_not_even :: Prop (Ev (S Z)) -> { false } @-}
one_not_even :: Ev -> ()
one_not_even EZ        = ()
one_not_even (ESS _ _) = ()

{-@ one_not_even' :: { v: a | isEven (S Z) } -> { false } @-}
one_not_even' :: a -> ()
one_not_even' _ = ()

{-@ sSSSev__even :: n: Peano -> Prop (Ev (S (S (S (S n))))) -> Prop (Ev n) @-}
sSSSev__even :: Peano -> Ev -> Ev
sSSSev__even n (ESS _ (ESS _ pf)) = pf

{-@ reflect dubble @-}
dubble :: Peano -> Peano
dubble Z     = Z
dubble (S n) = S (S (dubble n))

{-@ ev_even' :: n:Peano -> Prop (Ev n) -> (k :: Peano, { n = dubble k} ) @-}
ev_even' :: Peano -> Ev -> (Peano, ())
ev_even' Z         EZ          = (Z  , Z === dubble Z *** QED )
ev_even' (S Z)     pf          = impossible (one_not_even pf)     -- Coq does auto case analysis here.
ev_even' (S (S n)) (ESS _ pf)  = (S k, S (S n) === dubble (S k) *** QED )
  where
    (k, _)                    = ev_even' n pf

{-@ ev_even :: n:Peano -> Prop (Ev n) -> (k :: Peano, { n = double k} ) @-}
ev_even :: Peano -> Ev -> (Peano, ())
ev_even Z         EZ          = (Z  , Z === double Z *** QED )
ev_even (S Z)     pf          = impossible (one_not_even pf)     -- Coq does auto case analysis here.
ev_even (S (S n)) (ESS _ pf)  = (S k, succ_double k *** QED )
  where
    (k, _)                    = ev_even n pf

{-@ ev_sum :: n:Peano -> m:Peano -> Prop (Ev n) -> Prop (Ev m) -> Prop {Ev (plus n m)} @-}
ev_sum :: Peano -> Peano -> Ev -> Ev -> Ev
ev_sum Z         m _          pm = pm
ev_sum (S Z)     _ pn         _  = impossible (one_not_even pn)
ev_sum (S (S n)) m (ESS _ pn) pm = ESS (plus n m) (ev_sum n m pn pm)

{-@ ev_sum' :: n:{Peano | isEven n} -> m:{Peano | isEven m} -> { isEven (plus n m)}  @-}
ev_sum' :: Peano -> Peano -> ()
ev_sum' Z         m = ()
ev_sum' (S (S n)) m = ev_sum' n m

{-@ ev_ev__ev :: n:Peano -> m:Peano -> Prop {Ev (plus n m)} -> Prop (Ev n) -> Prop (Ev m) @-}
ev_ev__ev :: Peano -> Peano -> Ev -> Ev -> Ev
ev_ev__ev Z         _ pf         _          = pf
ev_ev__ev (S Z)     _ _          pn         = impossible (one_not_even pn)
ev_ev__ev (S (S n)) m (ESS _ pf) (ESS _ pn) = ev_ev__ev n m pf pn

{-@ ev_plus_plus :: n:Peano -> m:Peano -> p:Peano
                 -> Prop {Ev (plus n m)} -> Prop {Ev (plus n p)}
                 -> Prop {Ev (plus m p)}
  @-}
ev_plus_plus :: Peano -> Peano -> Peano -> Ev -> Ev -> Ev
ev_plus_plus n m p n_m n_p = ev_ev__ev (double n) (plus m p) n2_m_p n2
  where
    n_m_n_p = ev_sum (plus n m) (plus n p) n_m n_p -- Ev (plus (plus n m) (plus n p))
    n2_m_p  = n_m_n_p `withPf` shuffle n m p       -- Ev (plus (double n) (plus m p))
    n2      = ev_double n                          -- Ev (double n)

{-@ shuffle :: n:Peano -> m:Peano -> p:Peano -> { plus (plus n m) (plus n p) = plus (double n) (plus m p)} @-}
shuffle :: Peano -> Peano -> Peano -> ()
shuffle n m p
  =   plus (plus n m) (plus n p)
  ==? plus n (plus m (plus n p)) ? plus_assoc n m (plus n p)
  ==? plus n (plus (plus m n) p) ? plus_assoc m n p
  ==? plus n (plus (plus n m) p) ? plus_comm  m n
  ==? plus n (plus n (plus m p)) ? plus_assoc n m p
  ==? plus (plus n n) (plus m p) ? plus_assoc n n  (plus m p)
  === plus (double n) (plus m p)
  *** QED

{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible _ = undefined

{-@ withPf :: x:a -> b -> {v:a | v = x} @-}
withPf :: a -> b -> a
withPf x y = x

--------------------------------------------------------------------------------
-- | Syntactic sugar for prelude -----------------------------------------------
--------------------------------------------------------------------------------
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

--------------------------------------------------------------------------------
-- | Crufty termination stuff [How to auto-generate?] --------------------------
--------------------------------------------------------------------------------

{-@ measure evNat      @-}
{-@ evNat :: Ev -> Nat @-}
evNat :: Ev -> Int
evNat EZ        = 0
evNat (ESS _ p) = 1 + evNat p
