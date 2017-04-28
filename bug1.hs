{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--exact-data-con"                      @-}

module Sort where

{-@ data List = Nil | Cons {lHd :: Int, lTl :: List} @-}
data List = Nil | Cons Int List

{-@ reflect sort @-}
sort :: List -> List
sort xs = xs

{-@ reflect insert @-}
insert x ys = Cons x ys

{-@ reflect sorted1 @-}
sorted1 :: List -> Int -> Bool
sorted1  Nil         x1 = True
sorted1  (Cons x2 t) x1 = True

{-@ reflect sorted @-}
sorted :: List -> Bool
sorted Nil         = True
sorted (Cons x1 t) = True

{-@ thmInsertSorted :: x:Int -> ys:{v:List | sorted v} -> { sorted (insert x ys) } @-}
thmInsertSorted :: Int -> List -> ()
thmInsertSorted = undefined         -- CRASH
-- thmInsertSorted x l = undefined  -- OK
