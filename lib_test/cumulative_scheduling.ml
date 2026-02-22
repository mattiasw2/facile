(* Cumulative Scheduling
   From SICStus Prolog documentation, section "Cumulative Scheduling".

   Seven tasks with fixed durations and resource requirements must be
   scheduled on a resource with capacity 13 to minimize the makespan.

   Task  Duration  Resource
    t1      16        2
    t2       6        9
    t3      13        3
    t4       7        7
    t5       5       10
    t6      18        1
    t7       4       11

   Uses reification to decompose the cumulative constraint:
   for each time point, the sum of resource usage of active tasks
   must not exceed the capacity.

   Optimal makespan: 22 *)

open Facile
open Easy

let () =
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

  let best_starts = ref [||] in
  let best_end = ref 0 in
  ignore (Goals.solve
    (Goals.minimize goal makespan
      (fun cost ->
        best_starts := Array.map Fd.int_value starts;
        best_end := cost;
        Printf.printf "  Found makespan %d\n" cost;
        flush stdout)));

  match !best_starts with
  | [||] -> prerr_endline "No solution"; exit 1
  | ss ->
    Printf.printf "\nOptimal makespan: %d\n" !best_end;
    Printf.printf "Task  Duration  Resource  Start  End\n";
    for i = 0 to n - 1 do
      Printf.printf "  t%d      %2d        %2d      %2d    %2d\n"
        (i + 1) durations.(i) resources.(i) ss.(i) (ss.(i) + durations.(i))
    done;
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
    Printf.printf "Cumulative Scheduling: PASSED\n"
