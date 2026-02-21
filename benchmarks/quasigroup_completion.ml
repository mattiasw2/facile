(* Quasigroup Completion (Latin Square Completion)
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/quasigroup_completion.py
 *
 * Given a partially filled n x n grid, complete it so that each row and column
 * is a permutation of 1..n (a Latin square).
 * Key constraints: AllDifferent per row and column, fixed cell pre-assignments. *)

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

let solve puzzle name =
  let n = Array.length puzzle in
  Printf.printf "Quasigroup Completion: %s (%d x %d)\n" name n n;

  (* Create grid of variables *)
  let grid = Array.init n (fun i ->
    Array.init n (fun j ->
      if puzzle.(i).(j) > 0 then
        Fd.int puzzle.(i).(j)    (* fixed cell *)
      else
        Fd.interval 1 n))       (* unknown cell *)
  in

  (* Row constraints: all different in each row *)
  for i = 0 to n - 1 do
    Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) grid.(i))
  done;

  (* Column constraints: all different in each column *)
  for j = 0 to n - 1 do
    let col = Array.init n (fun i -> grid.(i).(j)) in
    Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) col)
  done;

  (* Flatten for labeling *)
  let flat = Array.concat (Array.to_list grid) in

  (* First-fail heuristic *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2)
  in
  let labeling = Goals.Array.forall ~select:min_size Goals.indomain flat in

  let bt = ref 0 in
  if Goals.solve ~control:(fun b -> bt := b) labeling then begin
    let sol = Array.init n (fun i -> Array.map Fd.int_value grid.(i)) in
    Printf.printf "Solution (%d backtracks):\n" !bt;
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        Printf.printf "%2d " sol.(i).(j)
      done;
      Printf.printf "\n"
    done;

    (* Verify: each row and column contains 1..n *)
    for i = 0 to n - 1 do
      assert (all_distinct sol.(i));
      assert (all_distinct (Array.init n (fun j -> sol.(j).(i))));
      for j = 0 to n - 1 do
        assert (sol.(i).(j) >= 1 && sol.(i).(j) <= n)
      done
    done;
    (* Verify: fixed cells preserved *)
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        if puzzle.(i).(j) > 0 then
          assert (sol.(i).(j) = puzzle.(i).(j))
      done
    done;
    Printf.printf "Quasigroup %s: PASSED\n" name
  end else
    Printf.printf "Quasigroup %s: no solution\n" name

let problem1 () =
  let puzzle = [|
    [| 1; 0; 0; 0; 4 |];
    [| 0; 5; 0; 0; 0 |];
    [| 4; 0; 0; 2; 0 |];
    [| 0; 4; 0; 0; 0 |];
    [| 0; 0; 5; 0; 1 |];
  |] in
  solve puzzle "5x5"

let problem2 () =
  let puzzle = [|
    [| 0; 0; 1; 0; 0; 5; 0 |];
    [| 0; 0; 0; 4; 0; 0; 0 |];
    [| 3; 0; 0; 0; 0; 0; 6 |];
    [| 0; 6; 0; 0; 0; 0; 0 |];
    [| 0; 0; 0; 0; 0; 3; 0 |];
    [| 0; 0; 7; 0; 0; 0; 0 |];
    [| 0; 0; 0; 0; 4; 0; 0 |];
  |] in
  solve puzzle "7x7"

let problem3 () =
  let puzzle = [|
    [| 0; 0; 0; 0; 6; 0; 0; 0; 9 |];
    [| 0; 0; 0; 0; 0; 3; 0; 5; 0 |];
    [| 0; 4; 0; 0; 0; 0; 0; 0; 7 |];
    [| 0; 0; 7; 0; 0; 0; 0; 0; 0 |];
    [| 6; 0; 0; 0; 0; 0; 0; 0; 4 |];
    [| 0; 0; 0; 0; 0; 0; 5; 0; 0 |];
    [| 3; 0; 0; 0; 0; 0; 0; 8; 0 |];
    [| 0; 9; 0; 1; 0; 0; 0; 0; 0 |];
    [| 1; 0; 0; 0; 2; 0; 0; 0; 0 |];
  |] in
  solve puzzle "9x9"

let problem4 () =
  let n = 10 in
  let puzzle = Array.init n (fun _ -> Array.make n 0) in
  solve puzzle "10x10-empty"

let problem5 () =
  let n = 20 in
  let puzzle = Array.init n (fun _ -> Array.make n 0) in
  solve puzzle "20x20-empty"

let run () =
  problem1 ();
  problem2 ();
  problem3 ();
  problem4 ();
  problem5 ()
