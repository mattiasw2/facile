(* Sudoku solver
   Classic 9x9 Sudoku: fill in digits 1-9 so that each row,
   column, and 3x3 box contains all digits exactly once. *)

open Facile
open Easy

(* A well-known puzzle (0 = unknown) *)
let puzzle = [|
  [| 5; 3; 0; 0; 7; 0; 0; 0; 0 |];
  [| 6; 0; 0; 1; 9; 5; 0; 0; 0 |];
  [| 0; 9; 8; 0; 0; 0; 0; 6; 0 |];
  [| 8; 0; 0; 0; 6; 0; 0; 0; 3 |];
  [| 4; 0; 0; 8; 0; 3; 0; 0; 1 |];
  [| 7; 0; 0; 0; 2; 0; 0; 0; 6 |];
  [| 0; 6; 0; 0; 0; 0; 2; 8; 0 |];
  [| 0; 0; 0; 4; 1; 9; 0; 0; 5 |];
  [| 0; 0; 0; 0; 8; 0; 0; 7; 9 |];
|]

let () =
  (* Create 9x9 grid of variables *)
  let grid = Array.init 9 (fun i ->
    Array.init 9 (fun j ->
      if puzzle.(i).(j) > 0 then
        Fd.int puzzle.(i).(j)  (* fixed cell *)
      else
        Fd.interval 1 9))     (* unknown cell *)
  in

  (* Row constraints: all different in each row *)
  for i = 0 to 8 do
    Cstr.post (Alldiff.cstr grid.(i))
  done;

  (* Column constraints: all different in each column *)
  for j = 0 to 8 do
    let col = Array.init 9 (fun i -> grid.(i).(j)) in
    Cstr.post (Alldiff.cstr col)
  done;

  (* Box constraints: all different in each 3x3 box *)
  for bi = 0 to 2 do
    for bj = 0 to 2 do
      let box = Array.init 9 (fun k ->
        grid.(bi * 3 + k / 3).(bj * 3 + k mod 3)) in
      Cstr.post (Alldiff.cstr box)
    done
  done;

  (* Flatten grid for labeling *)
  let all = Array.concat (Array.to_list grid) in

  (* First-fail heuristic: choose variable with smallest domain *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let goal = Goals.Array.forall ~select:min_size Goals.indomain all in

  let bt = ref 0 in
  if Goals.solve ~control:(fun b -> bt := b) goal then begin
    Printf.printf "Sudoku solved (%d backtracks):\n" !bt;
    for i = 0 to 8 do
      if i > 0 && i mod 3 = 0 then
        Printf.printf "------+-------+------\n";
      for j = 0 to 8 do
        if j > 0 && j mod 3 = 0 then Printf.printf "| ";
        Printf.printf "%d " (Fd.int_value grid.(i).(j))
      done;
      Printf.printf "\n"
    done
  end else
    prerr_endline "No solution"
