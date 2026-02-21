(* Discrete Tomography
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/discrete_tomography.py
 *
 * Reconstruct a binary (0/1) matrix given the row and column sums.
 * Key constraints: Binary decision variables, row-sum and column-sum constraints. *)

open Facile
open Easy

let solve row_sums col_sums name =
  let r = Array.length row_sums in
  let c = Array.length col_sums in
  Printf.printf "Discrete Tomography: %s (%d x %d)\n" name r c;

  (* Binary matrix *)
  let grid = Array.init r (fun _ ->
    Array.init c (fun _ -> Fd.create Domain.boolean))
  in

  (* Row sum constraints *)
  for i = 0 to r - 1 do
    Cstr.post (Arith.sum_fd grid.(i) =~ i2e row_sums.(i))
  done;

  (* Column sum constraints *)
  for j = 0 to c - 1 do
    let col = Array.init r (fun i -> grid.(i).(j)) in
    Cstr.post (Arith.sum_fd col =~ i2e col_sums.(j))
  done;

  (* Flatten for labeling *)
  let flat = Array.concat (Array.to_list grid) in
  let labeling = Goals.Array.labeling flat in

  (* Count all solutions *)
  let nsol = ref 0 in
  let first_sol = ref None in
  let count_goal =
    Goals.atomic ~name:"count_solution"
      (fun () ->
        incr nsol;
        if !nsol = 1 then
          first_sol := Some (Array.init r (fun i ->
            Array.map Fd.int_value grid.(i)));
        Stak.fail "next_solution")
  in

  let goal = labeling &&~ count_goal in

  let bt = ref 0 in
  ignore (Goals.solve ~control:(fun b -> bt := b) goal);

  (* Print first solution *)
  (match !first_sol with
  | Some sol ->
    Printf.printf "     ";
    Array.iter (fun cs -> Printf.printf "%d " cs) col_sums;
    Printf.printf "\n";
    for i = 0 to r - 1 do
      Printf.printf "%2d   " row_sums.(i);
      for j = 0 to c - 1 do
        Printf.printf "%s " (if sol.(i).(j) = 1 then "#" else ".")
      done;
      Printf.printf "\n"
    done;

    (* Verify first solution *)
    for i = 0 to r - 1 do
      assert (Array.fold_left ( + ) 0 sol.(i) = row_sums.(i))
    done;
    for j = 0 to c - 1 do
      let cs = Array.fold_left (fun acc row -> acc + row.(j)) 0 sol in
      assert (cs = col_sums.(j))
    done
  | None -> ());

  Printf.printf "  Discrete Tomography %s: %d solutions, %d backtracks\n" name !nsol !bt

let problem1 () =
  let row_sums = [| 0; 0; 8; 2; 6; 4; 5; 3; 7; 0; 0 |] in
  let col_sums = [| 0; 0; 7; 1; 6; 3; 4; 5; 2; 7; 0; 0 |] in
  solve row_sums col_sums "SciAm"

let problem2 () =
  let row_sums = [| 0; 4; 6; 6; 6; 6; 4; 0 |] in
  let col_sums = [| 0; 4; 6; 6; 6; 6; 4; 0 |] in
  solve row_sums col_sums "Diamond"

let run () =
  problem1 ();
  problem2 ()
