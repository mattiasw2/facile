(* Assignment Problem - FdArray demo
   Assign N workers to N jobs minimizing total cost.
   Uses FdArray.get to look up cost[worker][assigned_job],
   and FdArray.min to constrain the minimum cost.

   Demonstrates: FdArray.get, FdArray.min, FdArray.max *)

open Facile
open Easy

let () =
  (* Cost matrix: cost.(i).(j) = cost of worker i doing job j *)
  let cost = [|
    [| 9; 2; 7; 8 |];
    [| 6; 4; 3; 7 |];
    [| 5; 8; 1; 8 |];
    [| 7; 6; 9; 4 |];
  |] in
  let n = Array.length cost in

  (* Decision: assign.(i) = job assigned to worker i *)
  let assign = Fd.array n 0 (n - 1) in

  (* All workers get different jobs *)
  Cstr.post (Alldiff.cstr assign);

  (* Cost for each worker: use FdArray.get to index into cost arrays *)
  let worker_costs = Array.init n (fun i ->
    let cost_row = Array.map Fd.int cost.(i) in
    FdArray.get cost_row assign.(i)) in

  (* Total cost *)
  let total_cost = Arith.e2fd (Arith.sum_fd worker_costs) in

  (* Also demonstrate FdArray.min and FdArray.max *)
  let min_cost = FdArray.min worker_costs in
  let max_cost = FdArray.max worker_costs in

  (* Search with optimization *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let labeling = Goals.Array.forall ~select:min_size Goals.indomain assign in

  let best_assign = ref [||] in
  let best_min = ref 0 and best_max = ref 0 in
  ignore
    (Goals.solve
       (Goals.minimize labeling total_cost
          (fun c ->
            Printf.printf "  Found assignment with cost %d\n" c;
            best_assign := Array.map Fd.int_value assign;
            best_min := Fd.int_value min_cost;
            best_max := Fd.int_value max_cost)));

  match !best_assign with
  | [||] -> prerr_endline "No solution"; exit 1
  | sol ->
    Printf.printf "\nOptimal assignment:\n";
    let total = ref 0 in
    Array.iteri (fun i j ->
      Printf.printf "  Worker %d -> Job %d (cost %d)\n" i j cost.(i).(j);
      total := !total + cost.(i).(j)) sol;
    Printf.printf "Total cost: %d\n" !total;
    Printf.printf "Min worker cost: %d, Max worker cost: %d\n" !best_min !best_max;
    (* Verify: all different assignments *)
    let seen = Array.make n false in
    Array.iter (fun j -> assert (not seen.(j)); seen.(j) <- true) sol;
    (* Verify: total cost is correct *)
    let computed = Array.mapi (fun i j -> cost.(i).(j)) sol in
    let computed_total = Array.fold_left ( + ) 0 computed in
    assert (!total = computed_total);
    (* Verify: this is optimal (known answer for this instance: 13) *)
    assert (computed_total = 13);
    (* Verify: min and max worker costs *)
    let min_c = Array.fold_left min max_int computed in
    let max_c = Array.fold_left max min_int computed in
    assert (!best_min = min_c);
    assert (!best_max = max_c);
    Printf.printf "Assignment: PASSED\n"
