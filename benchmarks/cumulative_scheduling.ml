(* Cumulative Scheduling (SICStus Prolog CLP(FD) Example)
 * https://sicstus.sics.se/sicstus/docs/4.3.5/html/sicstus/Cumulative-Scheduling.html
 *
 * Seven tasks with fixed durations and resource requirements must be
 * scheduled on a resource with capacity 13 to minimize the makespan.
 *
 * Key constraints: reification for time-indexed cumulative decomposition,
 * scalar product for resource usage, FdArray.max for makespan.
 * Uses branch-and-bound optimization. *)

open Facile
open Easy

let solve () =
  let durations = [| 16; 6; 13; 7; 5; 18; 4 |] in
  let resources = [| 2; 9; 3; 7; 10; 1; 11 |] in
  let capacity = 13 in
  let n = Array.length durations in
  let horizon = 30 in

  Printf.printf "Cumulative Scheduling: %d tasks, capacity %d\n" n capacity;

  (* Start time variables: start_i in [0, horizon - duration_i] *)
  let starts = Array.init n (fun i ->
    Fd.interval 0 (horizon - durations.(i))) in

  (* End time variables: end_i = start_i + duration_i *)
  let ends = Array.init n (fun i ->
    Arith.e2fd (fd2e starts.(i) +~ i2e durations.(i))) in

  (* Makespan = max of all end times *)
  let makespan = FdArray.max ends in

  (* Cumulative constraint (time-indexed decomposition):
     For each time point t, sum of resource usage of active tasks <= capacity.
     Task i is active at t iff start_i <= t < start_i + duration_i,
     i.e., t - duration_i + 1 <= start_i <= t *)
  for t = 0 to horizon - 1 do
    let active = Array.init n (fun i ->
      Reify.boolean
        ((fd2e starts.(i) <=~ i2e t)
         &&~~ (fd2e starts.(i) >=~ i2e (t - durations.(i) + 1)))) in
    Cstr.post (Arith.scalprod_fd resources active <=~ i2e capacity)
  done;

  (* Search: first-fail variable ordering, minimize makespan *)
  let select = Goals.Array.choose_index
    (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let goal = Goals.Array.forall ~select Goals.indomain starts in

  let bt = ref 0 in
  let best_starts = ref [||] in
  let best_end = ref 0 in
  ignore (Goals.solve ~control:(fun b -> bt := b)
    (Goals.minimize goal makespan
      (fun cost ->
        best_starts := Array.map Fd.int_value starts;
        best_end := cost;
        Printf.printf "  Found makespan %d\n" cost;
        flush stdout)));

  Printf.printf "  Cumulative Scheduling: %d backtracks\n" !bt;

  (* Verify solution *)
  let ss = !best_starts in
  assert (Array.length ss = n);

  (* Verify: no time point exceeds capacity *)
  for t = 0 to !best_end - 1 do
    let usage = ref 0 in
    for i = 0 to n - 1 do
      if ss.(i) <= t && t < ss.(i) + durations.(i) then
        usage := !usage + resources.(i)
    done;
    assert (!usage <= capacity)
  done;

  assert (!best_end = 22);
  Printf.printf "  Cumulative Scheduling: PASSED (optimal makespan %d)\n" !best_end

let run () =
  solve ()
