(* Combined test — runs LDS search then Queens in the same process.
   Exposes the Stak.reset() bug: reset() doesn't undo trail entries,
   so event registrations (like lds_check on on_choice_point) leak
   into the next solve call.

   In OCaml's normal test setup each test runs as a separate process,
   hiding the bug. This combined test reproduces it. *)

open Facile
open Easy

(* --- Copied from search_test.ml: LDS portion --- *)

let post_queens_constraints n queens =
  Cstr.post (Alldiff.cstr queens);
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      let diff = j - i in
      Cstr.post (fd2e queens.(i) -~ fd2e queens.(j) <>~ i2e diff);
      Cstr.post (fd2e queens.(i) -~ fd2e queens.(j) <>~ i2e (-diff));
    done
  done

let verify_queens v n =
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      assert (v.(i) <> v.(j));
      assert (abs (v.(i) - v.(j)) <> j - i)
    done
  done

let () =
  let n = 5 in
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in

  (* --- Part 1: LDS search (registers lds_check on on_choice_point) --- *)
  Printf.printf "=== Part 1: LDS search ===\n%!";
  let q_lds = Fd.array n 0 (n - 1) in
  post_queens_constraints n q_lds;

  let lds_base = Goals.Array.forall ~select:min_size Goals.indomain q_lds in
  let lds_goal = Goals.lds ~step:1 lds_base in

  if Goals.solve lds_goal then begin
    let sol = Array.map Fd.int_value q_lds in
    Printf.printf "LDS solution: [";
    Array.iteri (fun i x -> if i > 0 then Printf.printf ", "; Printf.printf "%d" x) sol;
    Printf.printf "]\n%!";
    verify_queens sol n;
    Printf.printf "LDS: PASSED\n%!"
  end else begin
    prerr_endline "FAILED: LDS found no solution"; exit 1
  end;

  (* --- Part 2: Normal queens in the SAME process --- *)
  (* Without fix: lds_check is still registered on on_choice_point,
     causing spurious failures in this second solve. *)
  Printf.printf "=== Part 2: Normal queens after LDS ===\n%!";
  let q2 = Fd.array n 0 (n - 1) in
  post_queens_constraints n q2;

  let goal2 = Goals.Array.forall ~select:min_size Goals.indomain q2 in
  if Goals.solve goal2 then begin
    let sol2 = Array.map Fd.int_value q2 in
    Printf.printf "Queens solution: [";
    Array.iteri (fun i x -> if i > 0 then Printf.printf ", "; Printf.printf "%d" x) sol2;
    Printf.printf "]\n%!";
    verify_queens sol2 n;
    Printf.printf "Queens after LDS: PASSED\n%!"
  end else begin
    prerr_endline "FAILED: Queens after LDS found no solution"; exit 1
  end;

  Printf.printf "Combined test: PASSED\n%!"
