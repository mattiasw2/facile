(* Nonogram (Picture Logic Puzzles)
 *
 * Given row and column clues (run lengths of filled cells),
 * reconstruct a binary grid.
 *
 * Key constraints: Binary variables, start-position model with reification.
 * First benchmark to use Reify.boolean and Boolean constraint combinators.
 * Tests decomposed pattern constraints where Gecode's native table/regular
 * propagator would give a dramatic advantage. *)

open Facile
open Easy

(* Extract run-length clues from a binary row *)
let clues_of_line line =
  let runs = ref [] in
  let current = ref 0 in
  Array.iter (fun v ->
    if v = 1 then incr current
    else begin
      if !current > 0 then runs := !current :: !runs;
      current := 0
    end) line;
  if !current > 0 then runs := !current :: !runs;
  Array.of_list (List.rev !runs)

(* Post constraints for one line (row or column) *)
let post_line_constraint cells clue =
  let len = Array.length cells in
  let k = Array.length clue in
  if k = 0 then
    (* Empty clue: all cells must be 0 *)
    Array.iter (fun c -> Fd.unify c 0) cells
  else begin
    (* Tight bounds for start positions *)
    let min_starts = Array.make k 0 in
    let max_starts = Array.make k 0 in
    let sum_before = ref 0 in
    for j = 0 to k - 1 do
      min_starts.(j) <- !sum_before + j; (* blocks + gaps *)
      sum_before := !sum_before + clue.(j)
    done;
    let sum_after = ref 0 in
    for j = k - 1 downto 0 do
      max_starts.(j) <- len - !sum_after - (k - 1 - j); (* blocks + gaps *)
      max_starts.(j) <- max_starts.(j) - clue.(j);
      sum_after := !sum_after + clue.(j)
    done;

    let starts = Array.init k (fun j ->
      Fd.create (Domain.interval min_starts.(j) max_starts.(j))) in

    (* Ordering: s[j+1] >= s[j] + c[j] + 1 *)
    for j = 0 to k - 2 do
      Cstr.post (fd2e starts.(j + 1) >=~
                 fd2e starts.(j) +~ i2e (clue.(j) + 1))
    done;

    (* Link cells to start positions via reification *)
    for p = 0 to len - 1 do
      (* For each block j, create a boolean: is cell p in block j? *)
      let in_block = Array.init k (fun j ->
        if p < min_starts.(j) || p > max_starts.(j) + clue.(j) - 1 then
          (* Cell p can never be in block j *)
          Fd.int 0
        else
          (* b = 1 iff starts[j] <= p < starts[j] + clue[j]
             i.e. starts[j] <= p AND starts[j] >= p - clue[j] + 1 *)
          Reify.boolean
            ((fd2e starts.(j) <=~ i2e p)
             &&~~ (fd2e starts.(j) >=~ i2e (p - clue.(j) + 1))))
      in
      (* cell[p] = sum of in_block (0 or 1 since blocks don't overlap) *)
      Cstr.post (Boolean.cstr in_block cells.(p))
    done
  end

(* Verify that a solved row matches the expected clue *)
let verify_line solved_line expected_clue =
  let actual = clues_of_line solved_line in
  if actual <> expected_clue then begin
    Printf.eprintf "  FAILED: expected clue [%s] got [%s]\n"
      (String.concat "," (List.map string_of_int (Array.to_list expected_clue)))
      (String.concat "," (List.map string_of_int (Array.to_list actual)));
    false
  end else true

let solve name solution =
  let rows = Array.length solution in
  let cols = Array.length solution.(0) in
  Printf.printf "Nonogram %s (%dx%d)\n" name rows cols;

  (* Compute clues from solution *)
  let row_clues = Array.map clues_of_line solution in
  let col_clues = Array.init cols (fun j ->
    let col = Array.init rows (fun i -> solution.(i).(j)) in
    clues_of_line col) in

  (* Print clue summary *)
  let total_filled = Array.fold_left (fun acc row ->
    acc + Array.fold_left ( + ) 0 row) 0 solution in
  Printf.printf "  %d filled cells (%.0f%%)\n" total_filled
    (100. *. float total_filled /. float (rows * cols));

  (* Binary grid variables *)
  let grid = Array.init rows (fun _ ->
    Array.init cols (fun _ -> Fd.create Domain.boolean)) in

  (* Post constraints for all rows *)
  for i = 0 to rows - 1 do
    post_line_constraint grid.(i) row_clues.(i)
  done;

  (* Post constraints for all columns *)
  for j = 0 to cols - 1 do
    let col = Array.init rows (fun i -> grid.(i).(j)) in
    post_line_constraint col col_clues.(j)
  done;

  (* Flatten and label *)
  let flat = Array.concat (Array.to_list grid) in
  let labeling = Goals.Array.labeling flat in

  let bt = ref 0 in
  if Goals.solve ~control:(fun b -> bt := b) labeling then begin
    Printf.printf "  %d backtracks\n" !bt;

    (* Extract solution *)
    let sol = Array.init rows (fun i ->
      Array.map Fd.int_value grid.(i)) in

    (* Print if small enough *)
    if rows <= 25 && cols <= 25 then begin
      Printf.printf "  ";
      for i = 0 to rows - 1 do
        for j = 0 to cols - 1 do
          Printf.printf "%c" (if sol.(i).(j) = 1 then '#' else '.')
        done;
        if i < rows - 1 then Printf.printf "\n  "
      done;
      Printf.printf "\n"
    end;

    (* Verify all row clues *)
    let ok = ref true in
    for i = 0 to rows - 1 do
      if not (verify_line sol.(i) row_clues.(i)) then ok := false
    done;
    (* Verify all column clues *)
    for j = 0 to cols - 1 do
      let col = Array.init rows (fun i -> sol.(i).(j)) in
      if not (verify_line col col_clues.(j)) then ok := false
    done;
    assert !ok;
    Printf.printf "  Nonogram %s: PASSED\n" name
  end else begin
    Printf.printf "  No solution for %s\n" name;
    assert false
  end

(* ---- Instances ---- *)

(* Heart (9x9) — easy validation *)
let heart = [|
  [|0;0;0;0;0;0;0;0;0|];
  [|0;1;1;0;0;0;1;1;0|];
  [|1;1;1;1;0;1;1;1;1|];
  [|1;1;1;1;1;1;1;1;1|];
  [|0;1;1;1;1;1;1;1;0|];
  [|0;0;1;1;1;1;1;0;0|];
  [|0;0;0;1;1;1;0;0;0|];
  [|0;0;0;0;1;0;0;0;0|];
  [|0;0;0;0;0;0;0;0;0|];
|]

(* Nested rectangles (10x10) — denser, fewer blocks per line *)
let nested_rect = [|
  [|0;0;0;0;0;0;0;0;0;0|];
  [|0;1;1;1;1;1;1;1;1;0|];
  [|0;1;0;0;0;0;0;0;1;0|];
  [|0;1;0;1;1;1;1;0;1;0|];
  [|0;1;0;1;0;0;1;0;1;0|];
  [|0;1;0;1;0;0;1;0;1;0|];
  [|0;1;0;1;1;1;1;0;1;0|];
  [|0;1;0;0;0;0;0;0;1;0|];
  [|0;1;1;1;1;1;1;1;1;0|];
  [|0;0;0;0;0;0;0;0;0;0|];
|]

(* Solid diamond (15x15) — long contiguous blocks *)
let diamond_15 =
  let n = 15 in
  Array.init n (fun i ->
    Array.init n (fun j ->
      let di = abs (i - n/2) in
      let dj = abs (j - n/2) in
      if di + dj <= n/2 then 1 else 0))

(* Two hearts (15x15) — more blocks, some search needed *)
let two_hearts = [|
  [|0;0;0;0;0;0;0;0;0;0;0;0;0;0;0|];
  [|0;1;1;0;1;1;0;0;0;1;1;0;1;1;0|];
  [|1;1;1;1;1;1;1;0;1;1;1;1;1;1;1|];
  [|1;1;1;1;1;1;1;0;1;1;1;1;1;1;1|];
  [|0;1;1;1;1;1;0;0;0;1;1;1;1;1;0|];
  [|0;0;1;1;1;0;0;0;0;0;1;1;1;0;0|];
  [|0;0;0;1;0;0;0;0;0;0;0;1;0;0;0|];
  [|0;0;0;0;0;0;0;0;0;0;0;0;0;0;0|];
  [|0;0;0;0;0;0;0;0;0;0;0;0;0;0;0|];
  [|0;0;0;0;0;0;0;1;0;0;0;0;0;0;0|];
  [|0;0;0;0;0;0;1;1;1;0;0;0;0;0;0|];
  [|0;0;0;0;0;1;1;1;1;1;0;0;0;0;0|];
  [|0;0;0;0;1;1;1;1;1;1;1;0;0;0;0|];
  [|0;0;0;1;1;1;1;1;1;1;1;1;0;0;0|];
  [|0;0;1;1;1;1;1;1;1;1;1;1;1;0;0|];
|]

(* Solid diamond (25x25) — larger, more propagation work *)
let diamond_25 =
  let n = 25 in
  Array.init n (fun i ->
    Array.init n (fun j ->
      let di = abs (i - n/2) in
      let dj = abs (j - n/2) in
      if di + dj <= n/2 then 1 else 0))

(* Nested diamonds (25x25) — multiple blocks per line *)
let nested_diamonds_25 =
  let n = 25 in
  Array.init n (fun i ->
    Array.init n (fun j ->
      let di = abs (i - n/2) in
      let dj = abs (j - n/2) in
      let d = di + dj in
      (* Three concentric diamond rings *)
      if d <= 3 then 1
      else if d >= 5 && d <= 7 then 1
      else if d >= 9 && d <= 11 then 1
      else 0))

(* Concentric squares (20x20) — 2-3 blocks per line, moderate ambiguity *)
let concentric_20 =
  let n = 20 in
  Array.init n (fun i ->
    Array.init n (fun j ->
      let di = min i (n - 1 - i) in
      let dj = min j (n - 1 - j) in
      let d = min di dj in
      (* Alternating filled/empty rings *)
      if d mod 2 = 0 && d < n/2 then 1
      else 0))

(* Concentric squares (40x40) — larger, more reification overhead *)
let concentric_40 =
  let n = 40 in
  Array.init n (fun i ->
    Array.init n (fun j ->
      let di = min i (n - 1 - i) in
      let dj = min j (n - 1 - j) in
      let d = min di dj in
      if d mod 2 = 0 && d < n/2 then 1
      else 0))

(* Concentric squares (80x80) *)
let concentric_80 =
  let n = 80 in
  Array.init n (fun i ->
    Array.init n (fun j ->
      let di = min i (n - 1 - i) in
      let dj = min j (n - 1 - j) in
      let d = min di dj in
      if d mod 2 = 0 && d < n/2 then 1
      else 0))

(* Concentric squares (120x120) *)
let concentric_120 =
  let n = 120 in
  Array.init n (fun i ->
    Array.init n (fun j ->
      let di = min i (n - 1 - i) in
      let dj = min j (n - 1 - j) in
      let d = min di dj in
      if d mod 2 = 0 && d < n/2 then 1
      else 0))

let run () =
  solve "Heart" heart;
  solve "Two-Hearts" two_hearts;
  solve "Concentric-20" concentric_20;
  solve "Concentric-40" concentric_40;
  solve "Concentric-80" concentric_80;
  solve "Concentric-120" concentric_120
