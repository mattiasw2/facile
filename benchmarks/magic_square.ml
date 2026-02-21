(* Magic Squares
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/magic_square.py
 *
 * Fill an n x n grid with distinct integers 1..n^2 such that every row,
 * column, and both main diagonals sum to the magic constant n*(n^2+1)/2.
 * Key constraints: AllDifferent, row/column/diagonal sum constraints. *)

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

let array_sum arr = Array.fold_left ( + ) 0 arr

let solve n =
  let m = n * n in
  let total = n * (m + 1) / 2 in
  Printf.printf "Magic Square n=%d, magic constant=%d\n" n total;

  (* n x n grid of variables in 1..n^2 *)
  let grid = Array.init n (fun _ -> Fd.array n 1 m) in
  let flat = Array.concat (Array.to_list grid) in

  (* All values are different *)
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) flat);

  (* Row sums *)
  for i = 0 to n - 1 do
    Cstr.post (Arith.sum_fd grid.(i) =~ i2e total)
  done;

  (* Column sums *)
  for j = 0 to n - 1 do
    let col = Array.init n (fun i -> grid.(i).(j)) in
    Cstr.post (Arith.sum_fd col =~ i2e total)
  done;

  (* Main diagonal *)
  let diag1 = Array.init n (fun i -> grid.(i).(i)) in
  Cstr.post (Arith.sum_fd diag1 =~ i2e total);

  (* Anti-diagonal *)
  let diag2 = Array.init n (fun i -> grid.(i).(n - 1 - i)) in
  Cstr.post (Arith.sum_fd diag2 =~ i2e total);

  (* Symmetry breaking *)
  Cstr.post (fd2e grid.(0).(0) <~ fd2e grid.(0).(n - 1));
  Cstr.post (fd2e grid.(0).(0) <~ fd2e grid.(n - 1).(0));
  Cstr.post (fd2e grid.(0).(0) <~ fd2e grid.(n - 1).(n - 1));

  (* First-fail heuristic *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 ->
      (Var.Attr.size a1, Var.Attr.min a1) < (Var.Attr.size a2, Var.Attr.min a2))
  in
  let labeling = Goals.Array.forall ~select:min_size Goals.indomain flat in

  let bt = ref 0 in
  if Goals.solve ~control:(fun b -> bt := b) labeling then begin
    let sol = Array.init n (fun i -> Array.map Fd.int_value grid.(i)) in
    Printf.printf "Solution (%d backtracks):\n" !bt;
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        Printf.printf "%3d " sol.(i).(j)
      done;
      Printf.printf "\n"
    done;

    (* Verify *)
    let all_vals = Array.concat (Array.to_list sol) in
    assert (all_distinct all_vals);
    assert (Array.length all_vals = m);
    Array.iter (fun v -> assert (v >= 1 && v <= m)) all_vals;

    for i = 0 to n - 1 do
      assert (array_sum sol.(i) = total);
      assert (array_sum (Array.init n (fun j -> sol.(j).(i))) = total)
    done;
    assert (array_sum (Array.init n (fun i -> sol.(i).(i))) = total);
    assert (array_sum (Array.init n (fun i -> sol.(i).(n - 1 - i))) = total);
    Printf.printf "Magic Square n=%d: PASSED\n" n
  end else
    Printf.printf "No solution for n=%d\n" n

let run () =
  solve 3;
  solve 4;
  solve 5;
  solve 6
