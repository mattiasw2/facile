(* Golomb Rulers (Optimal, Branch-and-Bound)
 *
 * A Golomb ruler with k marks is a set 0 = a(1) < a(2) < ... < a(k)
 * such that all pairwise differences a(j) - a(i) (j > i) are distinct.
 * Find the shortest such ruler (minimize a(k)).
 *
 * Key constraints: AllDifferent on distances, ordering, minimize.
 * First benchmark to use branch-and-bound optimization.
 * Gecode excels here: space-based B&B with good bounding. *)

open Facile
open Easy

(* Known optimal Golomb ruler lengths (OEIS A003418) *)
let known_optimal =
  [| 0; 0; 1; 3; 6; 11; 17; 25; 34; 44; 55; 72; 85; 106 |]

let solve n =
  Printf.printf "Golomb ruler marks=%d\n" n;

  (* Upper bound for ruler length *)
  let ub = if n < Array.length known_optimal then known_optimal.(n) * 2
           else truncate (2. ** float n) in
  let ticks = Fd.array n 0 ub in
  let ndists = n * (n - 1) / 2 in
  let dists = Array.make ndists (Fd.int 0) in

  (* First tick at 0 *)
  Fd.unify ticks.(0) 0;

  (* Compute all pairwise distances *)
  let cpt = ref 0 in
  for i = 0 to n - 1 do
    (* Ticks are strictly increasing *)
    if i < n - 1 then
      Cstr.post (fd2e ticks.(i + 1) >~ fd2e ticks.(i));
    for j = i + 1 to n - 1 do
      dists.(!cpt) <- Arith.e2fd (fd2e ticks.(j) -~ fd2e ticks.(i));
      Cstr.post (fd2e dists.(!cpt) >~ i2e 0);
      incr cpt
    done
  done;

  (* All distances are distinct *)
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) dists);

  (* Symmetry breaking: first distance < last distance *)
  Cstr.post (fd2e dists.(!cpt - 1) >~ fd2e dists.(0));

  (* Search goal: label ticks *)
  let goal = Goals.Array.labeling ticks in

  (* Minimize the last tick *)
  let bt = ref 0 in
  let best_ticks = ref [||] in
  ignore
    (Goals.solve ~control:(fun b -> bt := b)
       (Goals.minimize goal ticks.(n - 1)
          (fun _cost ->
            best_ticks := Array.map Fd.int_value ticks;
            Printf.printf "  Found: ";
            Array.iter (fun t -> Printf.printf "%d " t) !best_ticks;
            Printf.printf "(length %d)\n%!" (Fd.int_value ticks.(n - 1)))));

  Printf.printf "  Golomb ruler marks=%d: %d backtracks\n" n !bt;

  (* Verify *)
  let t = !best_ticks in
  assert (Array.length t = n);
  assert (t.(0) = 0);
  (* Marks strictly increasing *)
  for i = 0 to n - 2 do assert (t.(i) < t.(i + 1)) done;
  (* All pairwise distances distinct *)
  let all_dists = ref [] in
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      let d = t.(j) - t.(i) in
      assert (not (List.mem d !all_dists));
      all_dists := d :: !all_dists
    done
  done;
  (* Check against known optimal *)
  if n < Array.length known_optimal then begin
    assert (t.(n - 1) = known_optimal.(n));
    Printf.printf "  Golomb ruler marks=%d: PASSED (optimal length %d)\n" n t.(n - 1)
  end else
    Printf.printf "  Golomb ruler marks=%d: PASSED (length %d, optimal unknown)\n" n t.(n - 1)

let run () =
  solve 7;
  solve 8;
  solve 9;
  solve 10
