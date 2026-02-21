(* 0-1 Knapsack Problem
   Select items to maximize total value without exceeding capacity.
   Each item is either taken (1) or not (0).

   Uses boolean variables, scalar product constraints, and
   branch-and-bound optimization (minimize cost = max_value - value). *)

open Facile
open Easy

let () =
  let weights  = [| 10; 20; 30; 40; 50 |] in
  let values   = [| 60; 100; 120; 160; 200 |] in
  let capacity = 80 in
  let n = Array.length weights in

  Printf.printf "Knapsack: %d items, capacity %d\n" n capacity;
  Printf.printf "Items: ";
  Array.iteri (fun i _ ->
    Printf.printf "[w=%d,v=%d] " weights.(i) values.(i)) weights;
  Printf.printf "\n";

  (* Binary decision variables *)
  let items = Array.init n (fun _ -> Fd.create Domain.boolean) in

  (* Weight constraint: sum(w_i * x_i) <= capacity *)
  Cstr.post (Arith.scalprod_fd weights items <=~ i2e capacity);

  (* To maximize value, minimize (max_possible - value) *)
  let max_value = Array.fold_left ( + ) 0 values in
  let profit = Arith.e2fd (Arith.scalprod_fd values items) in
  let cost = Arith.e2fd (i2e max_value -~ fd2e profit) in

  let labeling = Goals.Array.labeling items in

  let best = ref [||] in
  ignore
    (Goals.solve
       (Goals.minimize labeling cost
          (fun c ->
            let p = max_value - c in
            Printf.printf "  Found solution with value %d\n" p;
            best := Array.map Fd.int_value items)));

  match !best with
  | [||] -> prerr_endline "No solution"
  | sol ->
    Printf.printf "\nOptimal selection:\n";
    let total_w = ref 0 and total_v = ref 0 in
    Array.iteri (fun i x ->
      if x = 1 then begin
        Printf.printf "  Item %d: weight=%d value=%d\n" (i + 1) weights.(i) values.(i);
        total_w := !total_w + weights.(i);
        total_v := !total_v + values.(i)
      end) sol;
    Printf.printf "Total: weight=%d/%d, value=%d\n" !total_w capacity !total_v
