(* Sorting Constraint demo
   Given an array of variables, constrain a second array to be
   the sorted version, and find the permutation that sorts it.

   Demonstrates: Sorting.sort, Sorting.sortp *)

open Facile
open Easy

let () =
  (* 6 variables with bounded domains *)
  let n = 6 in
  let x = [|
    Fd.interval 3 8;
    Fd.interval 1 5;
    Fd.interval 6 9;
    Fd.interval 2 7;
    Fd.interval 4 8;
    Fd.interval 1 6;
  |] in

  (* Additional constraints to make the problem interesting *)
  Cstr.post (Alldiff.cstr x);

  (* Create sorted version and permutation using sortp *)
  let (sorted, perm) = Sorting.sortp x in

  (* Constrain the sum to a specific value *)
  Cstr.post (Arith.sum_fd x =~ i2e 27);

  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  (* Label x, then sorted and perm (propagation may not fully bind them) *)
  let goal =
    Goals.Array.forall ~select:min_size Goals.indomain x
    &&~ Goals.Array.forall ~select:min_size Goals.indomain sorted
    &&~ Goals.Array.forall ~select:min_size Goals.indomain perm in

  if Goals.solve goal then begin
    let xv = Array.map Fd.int_value x in
    let sv = Array.map Fd.int_value sorted in
    let pv = Array.map Fd.int_value perm in
    Printf.printf "Original:    ";
    Array.iter (fun v -> Printf.printf "%d " v) xv;
    Printf.printf "\nSorted:      ";
    Array.iter (fun v -> Printf.printf "%d " v) sv;
    Printf.printf "\nPermutation: ";
    Array.iter (fun v -> Printf.printf "%d " v) pv;
    Printf.printf "\n";
    (* Verify: sorted is actually sorted *)
    for i = 0 to n - 2 do
      assert (sv.(i) <= sv.(i + 1)
              || (Printf.eprintf "FAILED: sorted[%d]=%d > sorted[%d]=%d\n"
                    i sv.(i) (i+1) sv.(i+1); false))
    done;
    (* Verify: sorted is a permutation of original *)
    let xs = Array.copy xv and ss = Array.copy sv in
    Array.sort compare xs; Array.sort compare ss;
    assert (xs = ss);
    (* Verify: permutation relationship: x.(i) = sorted.(perm.(i)) *)
    Array.iteri (fun i xi ->
      assert (xi = sv.(pv.(i))
              || (Printf.eprintf "FAILED: x[%d]=%d != sorted[perm[%d]]=%d\n"
                    i xi i sv.(pv.(i)); false))) xv;
    (* Verify: all different *)
    for i = 0 to n - 1 do
      for j = i + 1 to n - 1 do assert (xv.(i) <> xv.(j)) done
    done;
    (* Verify: sum = 27 *)
    assert (Array.fold_left ( + ) 0 xv = 27);
    Printf.printf "Sorting test: PASSED\n"
  end else begin
    prerr_endline "No solution"; exit 1
  end
