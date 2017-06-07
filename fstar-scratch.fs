
(* 
val zink : v:int{v = 8} (* OK *)

let zink = 
  let foo = fun a -> let t = fib a in 
                     let _ = assert (t = 8) in (* FAILS *)
                     t 
  in
  foo 5
  
let rec sum xs = match xs with
    | [] -> 0
    | h::t -> h + sum t
*)

(* 
(* FAILS 
let _ = (fun x -> assert (sum [x;x;x] = 6)) 2
*) 
    
(* OK *)

let _ = assert (((fun x -> sum [x;x;x]) 2) = 6)

let rec incr n x = if n = 0 then x + 1 else incr (n-1) x

(* let _ = fun y -> assert (incr 8 y = y + 1) *)


val propIncr   : y:int -> v:int{v = y + 1}
let propIncr y = incr 8 y 

*)

  
(*

assume val dec : x:int -> Pure int 
   (requires True) 
   (ensures (fun y -> y = x - 1))

assume val inc : x:int -> Pure int 
   (requires True) 
   (ensures (fun y -> y = x + 1))
*)

(* assume val last : list 'a -> 'a *)

(*
let rec last xs = match xs with 
    | [x] -> x 
    | x::rest -> last rest

assume val zink : list 'a -> 'a 
*)
(* 
let zink xs = match xs with 
    | h::_ -> h 
 *)
 
 (*
let ex2 (x:nat) : nat = 
  let ys = 
    let n = dec x in
    let p = inc x in 
    let xs = [n] in 
    p::xs 
  in
  let y = zink ys in
  inc y
  
*)

(* Alternatively, F* will also just reason about definitions:  *)
(*
assume val dec : x:int -> Pure int 
   (requires True) (ensures (fun y -> y = x - 1))

assume val inc : x:int -> Pure int 
   (requires True) (ensures (fun y -> y = x + 1))

let compose (f:'b -> 'c) (g:'a -> 'b) (x:'a) = f (g x)
*)




  (* 
  

assume val dec : x:int -> Pure int 
   (requires True) 
   (ensures (fun y -> y = x - 1))

assume val inc : x:int -> Pure int 
   (requires True) 
   (ensures (fun y -> y = x + 1))
  



let ex3 : i:int -> Pure int
  (requires (0 <= i))
  (ensures (fun j -> 0 <= j))
  = compose inc dec


let ex1 (x:nat) : nat = 
  let y = 
    let t = x in 
    (fun z -> z - 1) t 
  in 
  (fun p -> p + 1) y

let ex2 (x:nat) : nat = 
  let ys = 
    let n = dec x in
    let p = inc x in 
    let xs = [p] in 
    n::xs in
  let y = Cons?.hd ys in
  inc y
*)  
