exception NotImplemented
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lrevrev : 'a list list -> 'a list list =
  let rec lrev l =
      match l with
      | [] -> []
      | hd::tl -> lrev (tl) @ hd::[]
  in
  fun l ->
    match l with
    | [] -> []
    | hd::tl -> lrevrev(tl) @ lrev(hd)::[]

let rec lfoldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b =
  fun f e l ->
    match l with
    | [] -> e
    | hd::tl -> lfoldl (f) (f(hd,e)) (tl)

(** Tail recursive functions  **)

let fact : int -> int =
  let rec fact' n acc =
    if n==0 then acc
    else fact' (n-1) (acc*n)
  in
  fun n -> fact' n 1

let fib : int -> int =
  let rec fib' n acc1 acc2 =
    if n==0 then acc1
    else fib' (n-1) (acc1+acc2) (acc1)
  in
  fun n -> fib' n 0 1

let alterSum : int list -> int =
  let rec alterSum' l acc opr =
    match l with
    | [] -> acc
    | hd:: tl -> alterSum' (tl) (acc+opr*hd) (-1*opr) 
  in
  fun l -> alterSum' l 0 1

let ltabulate : int -> (int -> 'a) -> 'a list =
  let rec ltabulate' f n accl =
    if n==0 then f(n)::accl
    else ltabulate' (f) (n-1) (f(n)::accl)
  in
  fun n f -> ltabulate' f n []

let lfilter : ('a -> bool) -> 'a list -> 'a list =
  let rec lfilter' p l accl =
    match l with
    | [] -> accl
    | hd::tl -> if p(hd) then lfilter' (p) (tl) (accl@(hd::[])) else lfilter' (p) (tl) (accl)
  in
  fun p l -> lfilter' p l []

let rec union : 'a list -> 'a list -> 'a list =
  fun s t ->
    match s, t with
    | _, [] -> s
    | _, hd::tl -> union(hd::(lfilter (fun x -> x!=hd) s)) (tl)

let inorder : 'a tree -> 'a list = 
  let rec inorder' t ret =
    match t with
    | Leaf value -> ret value
    | Node (left, value, right) -> inorder' left (fun l -> l::[] @ value::[] @ inorder' right ret)
  in
  fun t -> inorder' t (fun x -> x::[])
	
let postorder : 'a tree -> 'a list =
  let rec postorder' t ret =
    match t with
    | Leaf value -> ret value
    | Node (left, value, right) -> postorder' left (fun l -> l::[] @ postorder' right (fun r -> r::[]) @ ret value)
  in
  fun t -> postorder' t (fun x -> x::[])

let preorder : 'a tree -> 'a list =
  let rec preorder' t ret =
    match t with
    | Leaf value -> ret value
    | Node (left, value, right) -> preorder' right (fun r -> ret value @ preorder' left (fun l -> l::[]) @ r::[])
  in
  fun t -> preorder' t (fun x -> x::[])
		       
(** Sorting in the ascending order **)

let rec quicksort : 'a list -> 'a list =
  fun l ->
    match l with
    | [] -> []
    | hd::tl -> quicksort(lfilter (fun x->x<=hd) tl) @ (hd::[]) @ quicksort(lfilter (fun x->x>hd) tl)

let rec mergesort : 'a list -> 'a list =
  let rec merge al bl =
    match al, bl with
    | [], bl -> bl
    | al, [] -> al
    | alh::alt, blh::blt -> if alh<blh then alh:: merge alt bl else blh:: merge al blt
  in
  let rec split l =
    match l with
    | [] -> [], []
    | hd::[] -> hd::[], []
    | hd::md::tl -> let hd', md' = split tl in hd::hd', md::md'
  in
  fun l -> 
    match l with
    | [] -> l
    | hd::[] -> l
    | _ -> let left, right = split l in merge (mergesort left) (mergesort right)

(** Structures **)

module type HEAP = 
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a 
    val update : 'a heap -> loc -> 'a -> 'a heap
  end
    
module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict 
  end

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = int
    type 'a heap = 'a list

    let empty _ = []

    let allocate h v = 
      let rec allocate' : loc -> 'a heap -> loc =
        fun n h ->
          match h with
          | [] -> n
          | hd::tl -> allocate' (n+1) (tl)
        in
      (h@(v::[]), allocate' (0) (h))
    
    let rec dereference h l =
      match h with
      | [] -> raise InvalidLocation
      | hd::tl -> if l = 0 then hd else dereference (tl) (l-1)
    
    let update h l v =
      let rec update' : 'a heap -> loc -> 'a -> 'a heap -> 'a heap =
        fun h l v front ->
          match h with
          | [] -> raise InvalidLocation
          | hd::tl -> if l = 0 then front@v::[]@tl else update' (tl) (l-1) (v) (front@hd::[])
        in
      update' h l v []
 
   end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty _ = []

    let rec lookup d k =
      match d with
      | [] -> None
      | (k', v)::rest -> if k'=k then Some v else lookup (rest) (k)
    
    let delete d k =
      let rec delete' d k r =
        match d with
        | [] -> r
        | (k', v)::rest -> if k'=k then r@rest else delete' (rest) (k) (r@(k',v)::[])
      in
      delete' d k []
    
    let insert d set =
      let rec insert' d set r =
        match d, set with
        | [], _ -> set::r
        | (dk, dv)::rest, (k, v) -> if dk = k then r@(k, v)::rest else insert' (rest) (set) (r@(dk, dv)::[])
      in
    insert' d set []

  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty _ = fun _ -> None
    
    let lookup d k = d k

    let delete d k = fun k' -> if k = k' then None else d k'

    let insert d set = 
      match set with
      | (k, v) -> fun k' -> if k = k' then Some v else d k'
  end
