(* N-Queens (Scaling Benchmark)
 * Place N queens on an NxN board so no two attack each other.
 *
 * Tests solver scaling on large search trees with 3x AllDifferent.
 * At large N, Gecode's space copying dominates Facile's trailing. *)

open Facile
open Easy

let solve n =
  Printf.printf "N-Queens n=%d\n" n;

  (* n decision variables in 0..n-1 *)
  let queens = Fd.array n 0 (n - 1) in

  (* Auxiliary variables for diagonals *)
  let shift op =
    Array.mapi (fun i qi -> Arith.e2fd (op (fd2e qi) (i2e i))) queens in
  let diag1 = shift ( +~ ) and diag2 = shift ( -~ ) in

  (* Global constraints *)
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) queens);
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) diag1);
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) diag2);

  (* Heuristic: min domain size, then min value *)
  let h a = (Var.Attr.size a, Var.Attr.min a) in
  let min_min = Goals.Array.choose_index (fun a1 a2 -> h a1 < h a2) in
  let labeling = Goals.Array.forall ~select:min_min Goals.indomain queens in

  let bt = ref 0 in
  if Goals.solve ~control:(fun b -> bt := b) labeling then begin
    Printf.printf "  %d backtracks\n" !bt;
    (* Verify: no two queens attack each other *)
    let cols = Array.map Fd.int_value queens in
    for i = 0 to n - 1 do
      for j = i + 1 to n - 1 do
        assert (cols.(i) <> cols.(j));
        assert (abs (cols.(i) - cols.(j)) <> j - i)
      done
    done;
    Printf.printf "  N-Queens n=%d: PASSED\n" n
  end else begin
    Printf.printf "  No solution for n=%d\n" n;
    assert false
  end

let run () =
  solve 50;
  solve 100;
  solve 200;
  solve 500;
  solve 1000
