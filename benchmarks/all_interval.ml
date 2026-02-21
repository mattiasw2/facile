(* All-Interval Series (CSPLib #7)
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/all_interval.py
 *
 * Find a permutation of 0..n-1 such that the absolute differences between
 * consecutive elements form a permutation of 1..n-1.
 * Key constraints: AllDifferent on series and diffs, abs linking, symmetry breaking. *)

open Facile
open Easy

let all_distinct arr =
  let a = Array.copy arr in
  Array.sort compare a;
  try
    for i = 1 to Array.length a - 1 do
      if a.(i) = a.(i-1) then raise Exit
    done;
    true
  with Exit -> false

let solve n =
  Printf.printf "All-Interval n=%d\n" n;

  (* Series: n variables in 0..n-1 *)
  let x = Fd.array n 0 (n - 1) in
  (* Diffs: n-1 variables in 1..n-1 *)
  let diffs = Fd.array (n - 1) 1 (n - 1) in

  (* All values in x are different *)
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) x);
  (* All diffs are different *)
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) diffs);

  (* diffs[k] = |x[k+1] - x[k]| *)
  for k = 0 to n - 2 do
    Cstr.post (fd2e diffs.(k) =~ Arith.abs (fd2e x.(k + 1) -~ fd2e x.(k)))
  done;

  (* Symmetry breaking *)
  Cstr.post (fd2e x.(0) <~ fd2e x.(n - 1));
  Cstr.post (fd2e diffs.(0) <~ fd2e diffs.(1));

  (* First-fail heuristic *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 ->
      (Var.Attr.size a1, Var.Attr.min a1) < (Var.Attr.size a2, Var.Attr.min a2))
  in

  let all = Array.append x diffs in
  let labeling = Goals.Array.forall ~select:min_size Goals.indomain all in

  let bt = ref 0 in
  if Goals.solve ~control:(fun b -> bt := b) labeling then begin
    let xv = Array.map Fd.int_value x in
    let dv = Array.map Fd.int_value diffs in
    Printf.printf "  x: ";
    Array.iter (fun v -> Printf.printf "%d " v) xv;
    Printf.printf " diffs: ";
    Array.iter (fun v -> Printf.printf "%d " v) dv;
    Printf.printf "\n";
    Printf.printf "  %d backtracks\n" !bt;

    (* Verify *)
    for k = 0 to n - 2 do
      assert (dv.(k) = abs (xv.(k + 1) - xv.(k)))
    done;
    assert (all_distinct xv);
    assert (Array.length xv = n);
    assert (all_distinct dv);
    assert (Array.length dv = n - 1);
    Printf.printf "  All-Interval n=%d: PASSED\n" n
  end else
    Printf.printf "  No solution for n=%d\n" n

let run () =
  solve 12;
  solve 20;
  solve 50
