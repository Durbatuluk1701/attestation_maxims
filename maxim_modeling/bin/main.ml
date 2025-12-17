open Set
open Printf

module PairOrd (Ord : OrderedType) = struct
  type t = Ord.t * Ord.t

  let fst = fst
  let snd = snd

  let compare (x1, y1) (x2, y2) =
    let c = Ord.compare x1 x2 in
    if c <> 0 then c else Ord.compare y1 y2
  ;;
end

module type ClosureS = sig
  type t

  val one_step_paths : t -> (t * t) list -> t list
  val multi_step_paths : t -> (t * t) list -> [> `Dead of t list | `Good of t list ] list
end

module Closure (Ord : OrderedType) : ClosureS with type t = Ord.t = struct
  type t = Ord.t

  module CSet = Set.Make (Ord)

  let one_step_paths_set a rel =
    List.fold_left
      (fun acc (x, y) -> if x = a then CSet.add y acc else acc)
      CSet.empty
      rel
  ;;

  let one_step_paths a rela = one_step_paths_set a rela |> CSet.to_list
  let extend_paths v ps = List.map (fun tl -> v :: tl) ps

  let multi_step_paths a rela =
    let extend_one_step paths =
      List.fold_left
        (fun (dead, good) (`Good path) ->
           let hd = List.hd path in
           let one_step = one_step_paths hd rela in
           List.fold_left
             (fun (dead, good) next ->
                if List.mem next path
                then `Dead (next :: path) :: dead, good
                else dead, `Good (next :: path) :: good)
             (dead, good)
             one_step)
        ([], [])
        paths
    in
    let rec multi_step_paths_set paths =
      if paths = []
      then []
      else (
        let dead_paths, good_paths = extend_one_step paths in
        multi_step_paths_set good_paths @ dead_paths @ good_paths)
    in
    multi_step_paths_set [ `Good [ a ] ]
  ;;
end

module IntClosure : ClosureS with type t = int = Closure (Int)

let () =
  let test_rel = [ 1, 2; 1, 6; 2, 3; 3, 4; 4, 5; 5, 6; 6, 4; 4, 1 ] in
  let one_step = IntClosure.one_step_paths 1 test_rel in
  printf "%s\n" (String.concat ", " (List.map string_of_int one_step));
  let multi_step = IntClosure.multi_step_paths 1 test_rel in
  printf "Length: %i\n" (List.length multi_step);
  printf
    "%s\n"
    (String.concat
       ", "
       (List.map
          (fun path ->
             match path with
             | `Dead p -> "Dead: " ^ String.concat "<-" (List.map string_of_int p) ^ "\n"
             | `Good p -> "Good: " ^ String.concat "<-" (List.map string_of_int p) ^ "\n")
          multi_step))
;;
