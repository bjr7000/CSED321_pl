exception Not_implemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum : int -> int =
  fun n ->
    if n == 1 then 1
    else n + sum(n-1)

let rec power : int -> int -> int = 
  fun x n ->
    if n == 0 then 1
    else x * power x (n-1)

let rec gcd : int -> int -> int =
  fun n m ->
    if n<m then gcd m (n)
    else 
      if n mod m == 0 then m
      else gcd m (n mod m)

let rec combi : int -> int -> int =
  fun n k ->
    if n * k * (n-k) == 0 then 1
    else combi (n-1)(k) + combi (n-1)(k-1)

    
let rec sum_tree : int tree -> int =
  fun t ->
  match t with
  | Leaf value -> value
  | Node (left, mid, right) -> sum_tree(left) + mid + sum_tree(right)

let rec depth : 'a tree -> int =
  fun t ->
  match t with
  | Leaf _ -> 0
  | Node (left, _, right) ->
      if depth(left)>depth(right) then depth(left)+1
      else depth(right)+1

let rec bin_search :  int tree -> int -> bool =
  fun t x->
  match t with
  | Leaf value -> value == x
  | Node (left, mid, right) ->
      if mid==x then true
      else
        if mid>x then bin_search (left) x
        else bin_search (right) x

let rec postorder : 'a tree -> 'a list =
  fun t ->
  match t with
  | Leaf value -> value::[]
  | Node (left, mid, right) -> postorder(left) @ postorder(right) @ ((mid) :: [])


let rec max : int list -> int =
  fun l ->
  match l with
  | [] -> 0
  | hd::tl ->
    if tl == [] then hd
    else
      if hd > max(tl) then hd
      else max(tl)

let rec list_add : int list -> int list -> int list =
  fun al bl ->
    match al, bl with
    | _, [] -> al
    | [], _ -> bl
    | ahd::atl, bhd::btl -> (ahd+bhd)::[] @ list_add (atl) (btl)

let rec insert :  int -> int list -> int list =
  fun m l ->
  match l with
  | [] -> m::[]
  | hd::tl ->
    if hd > m then m::[] @ hd::[] @ tl
    else hd::[] @ insert m(tl)

let rec insort : int list -> int list =
  fun l ->
  match l with
  | [] -> []
  | hd::tl -> insert (hd)(insort(tl))


let rec compose :  ('a -> 'b) -> ('b -> 'c) -> ('a -> 'c) =
  fun f g x -> g(f x)

let rec curry : ('a * 'b -> 'c) -> ('a -> 'b -> 'c) =
  fun f x y -> f (x,y)

let rec uncurry : ('a -> 'b -> 'c) -> ('a * 'b -> 'c) =
  fun f (x, y) -> f x y

let rec multifun : ('a -> 'a) -> int -> ('a -> 'a) =
  fun f n x ->
    if n == 1 then f x
    else (multifun f (n-1)) (f x)


let rec ltake : 'a list -> int -> 'a list =
  fun l n ->
  match l with
  | [] -> []
  | hd::tl -> 
    if n==0 then []
    else hd::[] @ ltake (tl) (n-1)

let rec lall : ('a -> bool) -> 'a list -> bool =
  fun f l ->
  match l with
  | [] -> true
  | hd::tl ->
    if f hd then lall f (tl)
    else false

let rec lmap : ('a -> 'b) -> 'a list -> 'b list =
  fun f l ->
    match l with
    | [] -> []
    | hd::tl -> (f hd)::[] @ lmap f (tl)

let rec lrev : 'a list -> 'a list =
  fun l ->
    match l with
    | [] -> []
    | hd::tl -> lrev (tl) @ hd::[]

let rec lflat : 'a list list -> 'a list =
  fun l ->
    match l with
    | [] -> []
    | hd::tl -> hd @ lflat (tl)

let rec lzip : 'a list -> 'b list -> ('a * 'b) list =
  fun al bl ->
    match al, bl with
    | _, [] -> []
    | [], _ -> []
    | ahd::atl, bhd::btl -> (ahd,bhd)::[] @ lzip (atl) (btl)

let mergePair : ('b list * 'b list) -> ('b list * 'b list) -> ('b list * 'b list) =
  fun ap bp ->
    match ap, bp with
    | (ap1,ap2), (bp1,bp2) -> (ap1@bp1, ap2@bp2)
let rec split : 'a list -> 'a list * 'a list =
  fun l ->
    match l with
    | [] -> ([],[])
    | hd::[] -> (hd::[],[])
    | hd::mid::tl -> mergePair (hd::[],mid::[]) (split(tl))

let rec cartprod : 'a list -> 'b list -> ('a * 'b) list =
  fun al bl ->
    match al, bl with
    | _, [] -> []
    | [], _ -> []
    | ahd::atl, bhd::btl -> (ahd,bhd)::[] @ cartprod (ahd::[])(btl) @ cartprod (atl)(bhd::btl)

let rec powerset : 'a list -> 'a list list =
  fun l ->
    match l with
    | [] -> [[]]
    | hd::tl -> powerset(tl)@ lmap (fun l -> hd::l) (powerset(tl))
