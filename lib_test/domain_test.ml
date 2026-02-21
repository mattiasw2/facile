(* Domain Operations test
   Direct tests for Domain module functions: create, add, remove,
   remove_min, remove_max, intersection, union, difference,
   smallest_geq, greatest_leq, largest_hole_around, choose.

   Demonstrates: Domain.create, Domain.add, Domain.remove,
   Domain.remove_min, Domain.remove_max, Domain.intersection,
   Domain.union, Domain.difference, Domain.smallest_geq,
   Domain.greatest_leq, Domain.largest_hole_around, Domain.choose,
   Domain.values, Domain.iter, Domain.plus, Domain.times *)

open Facile

let errors = ref 0

let check name cond =
  if not cond then begin
    Printf.eprintf "FAILED: %s\n" name;
    incr errors
  end

let () =
  (* === Domain.create from list === *)
  let d = Domain.create [5; 3; 1; 3; 7; 1] in (* duplicates and unsorted *)
  check "create: values" (Domain.values d = [1; 3; 5; 7]);
  check "create: size" (Domain.size d = 4);
  check "create: min" (Domain.min d = 1);
  check "create: max" (Domain.max d = 7);

  (* empty list *)
  let d_empty = Domain.create [] in
  check "create empty" (Domain.is_empty d_empty);

  (* === Domain.add === *)
  let d2 = Domain.add 4 d in
  check "add: contains 4" (Domain.member 4 d2);
  check "add: size" (Domain.size d2 = 5);
  check "add: values" (Domain.values d2 = [1; 3; 4; 5; 7]);

  (* add existing element *)
  let d2b = Domain.add 3 d in
  check "add existing: size unchanged" (Domain.size d2b = 4);

  (* === Domain.remove === *)
  let d3 = Domain.remove 3 d in
  check "remove: not contains 3" (not (Domain.member 3 d3));
  check "remove: size" (Domain.size d3 = 3);
  check "remove: values" (Domain.values d3 = [1; 5; 7]);

  (* remove non-existent *)
  let d3b = Domain.remove 99 d in
  check "remove non-existent: unchanged" (Domain.values d3b = Domain.values d);

  (* === Domain.remove_min / remove_max === *)
  let d4 = Domain.remove_min d in
  check "remove_min: values" (Domain.values d4 = [3; 5; 7]);

  let d5 = Domain.remove (Domain.max d) d in
  check "remove_max: values" (Domain.values d5 = [1; 3; 5]);

  (* === Domain.intersection === *)
  let da = Domain.create [1; 2; 3; 4; 5] in
  let db = Domain.create [3; 4; 5; 6; 7] in
  let di = Domain.intersection da db in
  check "intersection: values" (Domain.values di = [3; 4; 5]);

  (* disjoint intersection *)
  let dc = Domain.create [10; 11] in
  let di2 = Domain.intersection da dc in
  check "intersection disjoint: empty" (Domain.is_empty di2);

  (* === Domain.union === *)
  let du = Domain.union da db in
  check "union: values" (Domain.values du = [1; 2; 3; 4; 5; 6; 7]);

  (* === Domain.difference === *)
  (* difference requires small ⊆ big *)
  let big = Domain.create [1; 2; 3; 4; 5] in
  let small = Domain.create [2; 4] in
  let dd = Domain.difference big small in
  check "difference: values" (Domain.values dd = [1; 3; 5]);

  (* === Domain.diff (general, no inclusion required) === *)
  let dd2 = Domain.diff da db in
  check "diff: values" (Domain.values dd2 = [1; 2]);

  (* === Domain.smallest_geq === *)
  let d_holes = Domain.create [1; 3; 5; 8; 10] in
  check "smallest_geq 1" (Domain.smallest_geq d_holes 1 = 1);
  check "smallest_geq 2" (Domain.smallest_geq d_holes 2 = 3);
  check "smallest_geq 4" (Domain.smallest_geq d_holes 4 = 5);
  check "smallest_geq 6" (Domain.smallest_geq d_holes 6 = 8);
  check "smallest_geq 10" (Domain.smallest_geq d_holes 10 = 10);
  (try
    ignore (Domain.smallest_geq d_holes 11);
    check "smallest_geq 11: should raise" false
  with Not_found -> ());

  (* === Domain.greatest_leq === *)
  check "greatest_leq 10" (Domain.greatest_leq d_holes 10 = 10);
  check "greatest_leq 9" (Domain.greatest_leq d_holes 9 = 8);
  check "greatest_leq 7" (Domain.greatest_leq d_holes 7 = 5);
  check "greatest_leq 2" (Domain.greatest_leq d_holes 2 = 1);
  check "greatest_leq 1" (Domain.greatest_leq d_holes 1 = 1);
  (try
    ignore (Domain.greatest_leq d_holes 0);
    check "greatest_leq 0: should raise" false
  with Not_found -> ());

  (* === Domain.largest_hole_around === *)
  (* d_holes = {1, 3, 5, 8, 10} *)
  (* Around 3 (in domain): no hole, returns (3,3) *)
  let (lo, hi) = Domain.largest_hole_around d_holes 3 in
  check "largest_hole_around 3" (lo = 3 && hi = 3);

  (* Around 6 (in a hole between 5 and 8): returns (5,8) *)
  let (lo2, hi2) = Domain.largest_hole_around d_holes 6 in
  check "largest_hole_around 6" (lo2 = 5 && hi2 = 8);

  (* Around 2 (in a hole between 1 and 3): returns (1,3) *)
  let (lo3, hi3) = Domain.largest_hole_around d_holes 2 in
  check "largest_hole_around 2" (lo3 = 1 && hi3 = 3);

  (* === Domain.choose === *)
  let chosen = Domain.choose (fun a b -> a > b) d_holes in
  check "choose max" (chosen = 10);

  let chosen_min = Domain.choose (fun a b -> a < b) d_holes in
  check "choose min" (chosen_min = 1);

  (* === Domain.plus === *)
  let dp = Domain.plus (Domain.create [1; 3; 5]) 10 in
  check "plus: values" (Domain.values dp = [11; 13; 15]);

  (* === Domain.times === *)
  let dt = Domain.times (Domain.create [1; 3; 5]) 2 in
  check "times: values" (Domain.values dt = [2; 6; 10]);

  (* === Domain.minus === *)
  let dm = Domain.minus (Domain.create [1; 3; 5]) in
  check "minus: values" (Domain.values dm = [-5; -3; -1]);

  (* === Domain.disjoint === *)
  check "disjoint: yes" (Domain.disjoint (Domain.create [1; 2]) (Domain.create [3; 4]));
  check "disjoint: no" (not (Domain.disjoint (Domain.create [1; 2; 3]) (Domain.create [3; 4])));

  (* === Domain.included === *)
  check "included: yes" (Domain.included (Domain.create [2; 3]) (Domain.create [1; 2; 3; 4]));
  check "included: no" (not (Domain.included (Domain.create [2; 5]) (Domain.create [1; 2; 3; 4])));

  (* === Domain.remove_closed_inter === *)
  let d_rci = Domain.remove_closed_inter 3 5 (Domain.create [1; 2; 3; 4; 5; 6; 7]) in
  check "remove_closed_inter: values" (Domain.values d_rci = [1; 2; 6; 7]);

  (* === Domain.iter === *)
  let acc = ref [] in
  Domain.iter (fun x -> acc := x :: !acc) d_holes;
  check "iter: collects all" (List.rev !acc = [1; 3; 5; 8; 10]);

  (* === Domain.interval_iter === *)
  let intervals = ref [] in
  Domain.interval_iter (fun lo hi -> intervals := (lo, hi) :: !intervals) d_holes;
  let ivs = List.rev !intervals in
  check "interval_iter" (ivs = [(1, 1); (3, 3); (5, 5); (8, 8); (10, 10)]);

  (* intervals on a contiguous domain *)
  let intervals2 = ref [] in
  Domain.interval_iter (fun lo hi -> intervals2 := (lo, hi) :: !intervals2)
    (Domain.create [3; 4; 5; 8; 9; 12]);
  let ivs2 = List.rev !intervals2 in
  check "interval_iter contiguous" (ivs2 = [(3, 5); (8, 9); (12, 12)]);

  (* === Domain.compare === *)
  let cmp = Domain.compare (Domain.create [1; 2]) (Domain.create [1; 2; 3]) in
  check "compare: smaller size first" (cmp < 0);
  let cmp2 = Domain.compare (Domain.create [1; 3]) (Domain.create [2; 3]) in
  check "compare: same size, lex order" (cmp2 < 0); (* {1,3} < {2,3} *)

  (* === Domain.sprint === *)
  let s = Domain.sprint (Domain.create [1; 2; 3; 5]) in
  check "sprint: not empty" (String.length s > 0);

  (* Summary *)
  if !errors = 0 then
    Printf.printf "Domain test: PASSED\n"
  else begin
    Printf.eprintf "Domain test: %d FAILURES\n" !errors;
    exit 1
  end
