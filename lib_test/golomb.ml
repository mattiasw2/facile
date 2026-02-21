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
  ignore
    (Goals.solve ~control:(fun b -> bt := b)
       (Goals.minimize goal ticks.(n - 1)
          (fun _cost ->
            Printf.printf "  Found: ";
            Array.iter (fun t -> Printf.printf "%d " (Fd.int_value t)) ticks;
            Printf.printf "(length %d)\n" (Fd.int_value ticks.(n - 1)))));
  Printf.printf "Golomb ruler with %d marks, %d backtracks\n" n !bt

let () =
  let n =
    if Array.length Sys.argv >= 2 then int_of_string Sys.argv.(1)
    else 7
  in
  golomb n
