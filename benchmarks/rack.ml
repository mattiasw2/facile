(* Rack Configuration (SICStus Prolog CLP(FD) Example)
 * https://sicstus.sics.se/sicstus/docs/latest/html/sicstus/Rack-Configuration.html
 *
 * Place circuit boards into equipment racks to satisfy power and connector
 * limits while minimizing total rack cost. Each rack has a type that determines
 * its power capacity, number of slots, and cost. Each card type has a power
 * draw and a required quantity.
 *
 * Key constraints: element (FdArray.get), scalar product for power, sum for
 * slots, symmetry breaking (decreasing rack types), minimize total cost.
 * Uses branch-and-bound optimization. *)

open Facile
open Easy

(* Rack type properties: power (x2 to avoid floats), slots, cost *)
let rack_power = [| 0; 300; 400 |]
let rack_slots = [| 0; 8; 16 |]
let rack_cost  = [| 0; 150; 200 |]

(* Card type properties: power draw (x2), demand *)
let card_power  = [| 39; 79; 99; 149 |]
let card_demand = [| 10; 4; 2; 1 |]

let solve nb_racks =
  let nb_rack_types = Array.length rack_cost in
  let nb_card_types = Array.length card_demand in

  Printf.printf "Rack Configuration: %d racks, %d rack types, %d card types\n"
    nb_racks nb_rack_types nb_card_types;

  (* Decision variables: rack type for each rack *)
  let rtype = Fd.array nb_racks 0 (nb_rack_types - 1) in

  (* Cards placed: cards.(r).(c) = number of cards of type c in rack r *)
  let cards = Array.init nb_racks (fun _ ->
    Array.init nb_card_types (fun c -> Fd.interval 0 card_demand.(c))) in

  (* Per-rack constraints *)
  let rack_power_arr = Array.map Fd.int rack_power in
  let rack_slots_arr = Array.map Fd.int rack_slots in
  let rack_cost_arr  = Array.map Fd.int rack_cost in

  let cost_vars = Array.init nb_racks (fun r ->
    let rp = FdArray.get rack_power_arr rtype.(r) in
    let rs = FdArray.get rack_slots_arr rtype.(r) in
    let rc = FdArray.get rack_cost_arr  rtype.(r) in

    (* Total cards in rack <= available slots *)
    Cstr.post (Arith.sum_fd cards.(r) <=~ fd2e rs);

    (* Total power draw (x2) <= rack power capacity (x2) *)
    Cstr.post (Arith.scalprod_fd card_power cards.(r) <=~ fd2e rp);

    rc) in

  (* Demand constraints: all cards of each type must be placed *)
  for c = 0 to nb_card_types - 1 do
    let col = Array.init nb_racks (fun r -> cards.(r).(c)) in
    Cstr.post (Arith.sum_fd col =~ i2e card_demand.(c))
  done;

  (* Symmetry breaking: decreasing rack types *)
  for r = 0 to nb_racks - 2 do
    Cstr.post (fd2e rtype.(r) >=~ fd2e rtype.(r + 1))
  done;

  (* Objective: minimize total cost *)
  let total_cost = Arith.e2fd (Arith.sum_fd cost_vars) in

  (* Search: first-fail on rack types then cards *)
  let all_cards = Array.concat (Array.to_list cards) in
  let all_vars = Array.append rtype all_cards in
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let labeling = Goals.Array.forall ~select:min_size Goals.indomain all_vars in

  let bt = ref 0 in
  let best_types = ref [||] in
  let best_cards = ref [||] in
  let best_cost = ref max_int in
  ignore
    (Goals.solve ~control:(fun b -> bt := b)
       (Goals.minimize labeling total_cost
          (fun cost ->
            best_cost := cost;
            best_types := Array.map Fd.int_value rtype;
            best_cards := Array.init nb_racks (fun r ->
              Array.map Fd.int_value cards.(r));
            Printf.printf "  cost=%d, racks=[" cost;
            Array.iter (fun t -> Printf.printf "%d " t) !best_types;
            Printf.printf "]\n%!")));

  Printf.printf "  Rack Configuration: %d backtracks\n" !bt;

  (* Verify solution *)
  let rt = !best_types in
  let ca = !best_cards in
  assert (Array.length rt = nb_racks);
  assert (Array.length ca = nb_racks);

  (* Verify demand satisfaction *)
  for c = 0 to nb_card_types - 1 do
    let total = Array.fold_left (fun acc r -> acc + ca.(r).(c)) 0
      (Array.init nb_racks (fun i -> i)) in
    assert (total = card_demand.(c))
  done;

  (* Verify per-rack constraints *)
  let computed_cost = ref 0 in
  for r = 0 to nb_racks - 1 do
    let t = rt.(r) in
    assert (t >= 0 && t < nb_rack_types);
    let nslots = Array.fold_left ( + ) 0 ca.(r) in
    assert (nslots <= rack_slots.(t));
    let pwr = ref 0 in
    for c = 0 to nb_card_types - 1 do
      pwr := !pwr + card_power.(c) * ca.(r).(c)
    done;
    assert (!pwr <= rack_power.(t));
    computed_cost := !computed_cost + rack_cost.(t)
  done;
  assert (!computed_cost = !best_cost);

  (* Verify symmetry breaking *)
  for r = 0 to nb_racks - 2 do
    assert (rt.(r) >= rt.(r + 1))
  done;

  assert (!best_cost = 550);
  Printf.printf "  Rack Configuration: PASSED (optimal cost %d)\n" !best_cost

let run () =
  solve 5
