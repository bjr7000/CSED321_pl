open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y = x||y
  let ( ** ) x y = x&&y
  let (==) x y = x=y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create l = 
    match l with
    | [] -> raise VectorIllegal
    | _ -> l

  let to_list l = l

  let dim l =
    let rec dim' l' acc =
      match l' with
      | [] -> acc
      | hd::tl -> dim' tl acc+1
    in
    dim' l 0

  let rec nth l n =
    match l with
    | [] -> raise VectorIllegal
    | hd::tl -> if n = 0 then hd else nth (tl) (n-1)
  
  let rec (++) x y =
    match x, y with
    | [], [] -> []
    | xhd::xtl, [] -> raise VectorIllegal
    | [], yhd::ytl -> raise VectorIllegal
    | xhd::xtl, yhd::ytl -> (Scal.(++) xhd yhd)::((++) xtl ytl)
    
  let rec (==) x y =
    match x, y with
    | [], [] -> true
    | xhd::xtl, [] -> raise VectorIllegal
    | [], yhd::ytl -> raise VectorIllegal
    | xhd::xtl, yhd::ytl -> (Scal.(==) xhd yhd)&&((==) xtl ytl)

  let rec innerp x y =
    match x, y with
    | [], [] -> Scal.zero
    | xhd::xtl, [] -> raise VectorIllegal
    | [], yhd::ytl -> raise VectorIllegal
    | xhd::xtl, yhd::ytl -> Scal.(++) (Scal.( ** ) xhd yhd) (innerp xtl ytl)
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list list

  exception MatrixIllegal

  let create ll =
    let rec len l n =
      match l with
      | [] -> n
      | hd::tl -> len tl n+1
    in
    let rec create' ll' n = 
      match ll' with
      | [] -> []
      | hd::tl -> if len hd 0 = n then hd::(create' tl n) else raise MatrixIllegal
    in
    match ll with
    | [] -> raise MatrixIllegal
    | hd::_ -> create' (ll) (len hd 0)

  let identity n = 
    let rec identity' i j n acc1 acc2 = 
      if j = n then acc2
      else if i = n && j != n then identity' (0) (j+1) (n) ([]) (acc2@acc1::[])
      else if i != n && j != n && i = j then identity' (i+1) (j) (n) (acc1@Scal.one::[]) (acc2)
      else if i != n && j != n && i != j then identity' (i+1) (j) (n) (acc1@Scal.zero::[]) (acc2)
      else []
    in
    if n <= 0 then raise MatrixIllegal
    else identity' 0 0 n [] []

  let dim m =
    let rec dim' m' acc =
      match m' with
      | [] -> acc
      | hd::tl -> dim' tl acc+1
    in
    dim' m 0

  let rec to_list ll = ll

  let rec get m r c =
    let rec get' l c =
      match l with
      | [] -> raise MatrixIllegal
      | hd::tl -> if c = 0 then hd else get' (tl) (c-1)
    in
    match m with
    | [] -> raise MatrixIllegal
    | hd::tl -> if r = 0 then get' (hd) (c) else get (tl) (r-1) (c)

  let transpose m =
    let rec transpose' i j n acc1 acc2 = 
      if j = n then acc2
      else if i = n && j != n then transpose' (0) (j+1) (n) ([]) (acc2@acc1::[])
      else if i != n && j != n then transpose' (i+1) (j) (n) (acc1@(get m i j)::[]) (acc2)
      else []
    in
    transpose' 0 0 (dim m) [] []

  let rec (++) x y = 
    let rec plusVec x' y' =
      match x', y' with
      | [], [] -> []
      | xhd::xtl, [] -> raise MatrixIllegal
      | [], yhd::ytl -> raise MatrixIllegal
      | xhd::xtl, yhd::ytl -> (Scal.(++) xhd yhd)::(plusVec xtl ytl)
    in
    match x, y with
    | [], [] -> []
    | xhd::xtl, [] -> raise MatrixIllegal
    | [], yhd::ytl -> raise MatrixIllegal
    | xhd::xtl, yhd::ytl -> (plusVec xhd yhd)::((++) xtl ytl)
  
  let ( ** ) x y =
    let rec mult x' y' i j n acc=
      if n < dim x' then mult x' y' i j (n+1) (Scal.(++) acc (Scal.( ** ) (get x' n i) (get y' j n)))
      else acc
    in
    let rec mult' i j n acc1 acc2 = 
      if j = n then acc2
      else if i = n && j != n then mult' (0) (j+1) (n) ([]) (acc2@acc1::[])
      else if i != n && j != n then mult' (i+1) (j) (n) (acc1@(mult x y i j 0 Scal.zero)::[]) (acc2)
      else []
    in
    if (dim x) != (dim y) then raise MatrixIllegal
    else mult' 0 0 (dim x) [] []

  let rec (==) x y =
    let rec equalVec x' y' =
      match x', y' with
      | [], [] -> true
      | xhd::xtl, [] -> raise MatrixIllegal
      | [], yhd::ytl -> raise MatrixIllegal
      | xhd::xtl, yhd::ytl -> (Scal.(==) xhd yhd)&&(equalVec xtl ytl)
    in
    match x, y with
    | [], [] -> true
    | xhd::xtl, [] -> raise MatrixIllegal
    | [], yhd::ytl -> raise MatrixIllegal
    | xhd::xtl, yhd::ytl -> (equalVec xhd yhd)&&((==) xtl ytl)

end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure m =
    let rec closure' m' n acc1 acc2 =
      if n = (Mat.dim m) then Mat.(++) acc1 acc2
      else closure' m' (n+1) (Mat.( ** ) m acc1) (Mat.(++) acc1 acc2)
    in
    closure' m 1 m (Mat.identity (Mat.dim m))
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach m = BoolMat.to_list (BoolMatClosure.closure (BoolMat.create m))

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = -1
  let one = 0

  let (++) x y = 
    match x, y with
    | -1, -1 -> -1
    | -1, _ -> y
    | _, -1 -> x
    | _, _ -> if x > y then y else x
  let ( ** ) x y =
    if x = -1 || y = -1 then -1 else x+y
  let (==) x y = x = y 
end

module DistanceMat = MatrixFn (Distance)
module DistanceMatClosure = ClosureFn (DistanceMat)

let distance m = DistanceMat.to_list (DistanceMatClosure.closure (DistanceMat.create m))

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = -1

  let (++) x y = 
    if x = -1 || y = -1 then -1
    else if x > y then x else y
  let ( ** ) x y =
    match x, y with
    | -1, -1 -> -1
    | -1, _ -> y
    | _, -1 -> x
    | 0, _ -> 0
    | _, 0 -> 0
    | _, _ -> if x < y then x else y
  let (==) x y = x = y 
end

module WeightMat = MatrixFn (Weight)
module WeightMatClosure = ClosureFn (WeightMat)

let weight m = WeightMat.to_list (WeightMatClosure.closure (WeightMat.create m))

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let _ =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 

