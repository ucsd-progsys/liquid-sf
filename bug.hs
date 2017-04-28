
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--exact-data-con"                      @-}

module Sort where

-- | Lists ---------------------------------------------------------------------

{-@ data List = Nil | Cons {lHd :: Int, lTl :: List} @-}
data List = Nil | Cons Int List

-- | Insertion Sort ------------------------------------------------------------

{-@ reflect sort @-}
sort Nil        = Nil
sort (Cons h t) = Cons h t

{-@ reflect insert @-}
insert x ys = Cons x ys

{-@ reflect sorted @-}
sorted :: List -> Bool
sorted (Cons x1 (Cons x2 t))        -- disabling this pattern removes the bug
  = if x1 <= x2
      then True -- sorted (Cons x2 t)
      else False
sorted _
  = True

{-@ thmInsertSorted :: x:Int -> ys:{List | sorted ys} -> { sorted (insert x ys) } @-}
thmInsertSorted :: Int -> List -> ()
thmInsertSorted = undefined






----
