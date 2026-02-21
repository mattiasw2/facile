(* Costas Arrays
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/costas_array.py
 *
 * An order-n Costas array is a permutation of {1,...,n} such that
 * the distances in each row of the triangular difference table are distinct.
 * Key constraints: AllDifferent on permutation and difference table rows. *)

open Facile
open Easy

let solve n =
  Printf.printf "Costas Array n=%d\n" n;

  (* The permutation: costas[i] in 1..n *)
  let costas = Fd.array n 1 n in

  (* Difference table: differences[i][j] for j > i *)
  let sentinel = -n + 1 in
  let differences = Array.init n (fun i ->
    Array.init n (fun j ->
      if j > i then
        Fd.interval (-(n - 1)) (n - 1)
      else
        Fd.int sentinel))
  in

  (* AllDifferent on the permutation *)
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) costas);

  (* Relate positions to the difference triangle *)
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if i < j then
        Cstr.post (fd2e differences.(i).(j) =~ fd2e costas.(j) -~ fd2e costas.(j - i - 1))
    done
  done;

  (* All entries in each row of the difference triangle must be distinct *)
  for i = 0 to n - 3 do
    let row = Array.init (n - i - 1) (fun k -> differences.(i).(i + k + 1)) in
    Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) row)
  done;

  (* Redundant: no zero in the difference table *)
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if i < j then
        Cstr.post (fd2e differences.(i).(j) <>~ i2e 0)
    done
  done;

  (* Redundant constraint from Barry O'Sullivan's model *)
  for k = 2 to n - 1 do
    for l = 2 to n - 1 do
      if k < l then
        Cstr.post (
          fd2e differences.(k - 2).(l - 1) +~ fd2e differences.(k).(l)
          =~ fd2e differences.(k - 1).(l - 1) +~ fd2e differences.(k - 1).(l))
    done
  done;

  (* First-fail heuristic *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2)
  in

  (* Count all solutions by failing after each one *)
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count_solution"
      (fun () ->
        incr nsol;
        let cv = Array.map Fd.int_value costas in
        if n <= 6 then begin
          Printf.printf "  costas: ";
          Array.iter (fun v -> Printf.printf "%d " v) cv;
          Printf.printf "\n"
        end;
        Stak.fail "next_solution")
  in

  let labeling = Goals.Array.forall ~select:min_size Goals.indomain costas in
  let goal = labeling &&~ count_goal in

  let bt = ref 0 in
  ignore (Goals.solve ~control:(fun b -> bt := b) goal);

  Printf.printf "  Costas Array n=%d: %d solutions, %d backtracks\n" n !nsol !bt;

  (* Verify known solution counts *)
  let known = [| 0; 1; 2; 4; 12; 40; 116; 200; 444 |] in
  if n < Array.length known then begin
    if !nsol <> known.(n) then begin
      Printf.eprintf "  FAILED: expected %d solutions, got %d\n" known.(n) !nsol;
      assert false
    end else
      Printf.printf "  Costas Array n=%d: PASSED (matches known count %d)\n" n known.(n)
  end

let run () =
  for n = 4 to 8 do
    solve n;
    ()
  done
