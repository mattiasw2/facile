(* Magic Sequence
   A magic sequence of length N is (x0, x1, ..., xN-1) such that
   value i appears exactly x_i times in the sequence.
   E.g. for N=4: (1, 2, 1, 0) — 0 appears once, 1 twice, 2 once, 3 zero times.

   Uses the Global Cardinality Constraint (GCC). *)

open Facile
open Easy

let magic n =
  (* N variables, each in domain 0..N-1 *)
  let x = Fd.array n 0 (n - 1) in

  (* GCC: x[i] counts how many times value i appears in x *)
  let card_vals = Array.mapi (fun i xi -> (xi, i)) x in
  Cstr.post (Gcc.cstr ~level:Gcc.Medium x card_vals);

  (* Redundant constraint: sum(i * x[i]) = N *)
  let coeffs = Array.init n (fun i -> i) in
  Cstr.post (Arith.scalprod_fd coeffs x =~ i2e n);

  (* First-fail heuristic *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let goal = Goals.Array.forall ~select:min_size Goals.indomain x in

  if Goals.solve goal then begin
    let vals = Array.map Fd.int_value x in
    Printf.printf "Magic sequence (N=%d): " n;
    Array.iteri (fun i v ->
      if i > 0 then Printf.printf ", ";
      Printf.printf "%d" v) vals;
    Printf.printf "\n";
    (* Verify: value i appears exactly vals[i] times *)
    for i = 0 to n - 1 do
      let count = Array.fold_left (fun acc v -> if v = i then acc + 1 else acc) 0 vals in
      assert (count = vals.(i)
              || (Printf.eprintf "FAILED: %d appears %d times, expected %d\n" i count vals.(i); false))
    done;
    Printf.printf "Magic sequence: PASSED\n"
  end else begin
    Printf.printf "No magic sequence of size %d\n" n; exit 1
  end

let () =
  let n =
    if Array.length Sys.argv >= 2 then int_of_string Sys.argv.(1)
    else 7
  in
  magic n
