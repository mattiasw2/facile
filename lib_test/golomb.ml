(* Golomb Ruler
   A Golomb ruler is a set of marks a(1) < ... < a(k) on a ruler
   such that all pairwise distances are distinct.
   Find the shortest ruler with k marks (optimal Golomb ruler).

   Uses Alldiff on distances and branch-and-bound optimization. *)

open Facile
open Easy

let golomb n =
  (* Upper bound: 2^n *)
  let n2 = truncate (2. ** float n) in
  let dummy = Fd.int 0 in
  let ticks = Fd.array n 0 n2 in
  let dists = Array.make ((n * (n - 1)) / 2) dummy in

  (* First tick at 0 *)
  Fd.unify ticks.(0) 0;

  (* Compute all pairwise distances *)
  let cpt = ref 0 in
  for i = 0 to n - 1 do
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

  (* Search goal *)
  let goal = Goals.Array.labeling ticks in

  (* Minimize the last tick (ruler length) *)
  let bt = ref 0 in
  let best_ticks = ref [||] in
  ignore
    (Goals.solve ~control:(fun b -> bt := b)
       (Goals.minimize goal ticks.(n - 1)
          (fun _cost ->
            best_ticks := Array.map Fd.int_value ticks;
            Printf.printf "  Found: ";
            Array.iter (fun t -> Printf.printf "%d " t) !best_ticks;
            Printf.printf "(length %d)\n" (Fd.int_value ticks.(n - 1)))));
  Printf.printf "Golomb ruler with %d marks, %d backtracks\n" n !bt;
  (* Verify *)
  let t = !best_ticks in
  assert (Array.length t = n);
  assert (t.(0) = 0);
  (* Verify marks are strictly increasing *)
  for i = 0 to n - 2 do assert (t.(i) < t.(i + 1)) done;
  (* Verify all pairwise distances are distinct *)
  let all_dists = ref [] in
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      let d = t.(j) - t.(i) in
      assert (not (List.mem d !all_dists)
              || (Printf.eprintf "FAILED: duplicate distance %d\n" d; false));
      all_dists := d :: !all_dists
    done
  done;
  (* Known optimal lengths for small Golomb rulers *)
  let known_optimal = [| 0; 0; 1; 3; 6; 11; 17; 25; 34; 44; 55 |] in
  if n < Array.length known_optimal then begin
    assert (t.(n - 1) = known_optimal.(n)
            || (Printf.eprintf "FAILED: length %d, expected %d\n" t.(n-1) known_optimal.(n); false));
  end;
  Printf.printf "Golomb ruler: PASSED\n"

let () =
  let n =
    if Array.length Sys.argv >= 2 then int_of_string Sys.argv.(1)
    else 7
  in
  golomb n
