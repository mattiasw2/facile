(* Subset Sum
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/subset_sum.py
 *
 * Given a set of integers and a target sum, find how many of each item
 * are needed to reach exactly the target.
 * Key constraints: scalar product == target, all solutions enumeration. *)

open Facile
open Easy

let solve values target name =
  let n = Array.length values in
  Printf.printf "Subset Sum: %s, target=%d, values=[|" name target;
  Array.iteri (fun i v ->
    if i > 0 then Printf.printf "; ";
    Printf.printf "%d" v) values;
  Printf.printf "|]\n";

  (* x[i] = number of items of type i taken (0..max possible) *)
  let max_per_item = Array.map (fun v -> if v > 0 then target / v else 0) values in
  let x = Array.init n (fun i -> Fd.interval 0 max_per_item.(i)) in

  (* Constraint: sum(x[i] * values[i]) = target *)
  Cstr.post (Arith.scalprod_fd values x =~ i2e target);

  let labeling = Goals.Array.labeling x in

  (* Count all solutions using fail-after-record *)
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count_solution"
      (fun () ->
        incr nsol;
        let xv = Array.map Fd.int_value x in
        if !nsol <= 20 then begin
          Printf.printf "  Solution %d: " !nsol;
          Array.iteri (fun i v ->
            if v > 0 then Printf.printf "%dx%d " v values.(i)) xv;
          Printf.printf "\n"
        end;

        (* Verify *)
        let computed = ref 0 in
        for i = 0 to n - 1 do
          computed := !computed + xv.(i) * values.(i)
        done;
        assert (!computed = target);
        Stak.fail "next_solution")
  in

  let goal = labeling &&~ count_goal in

  let bt = ref 0 in
  ignore (Goals.solve ~control:(fun b -> bt := b) goal);
  Printf.printf "  Subset Sum %s: %d solutions, %d backtracks\n" name !nsol !bt

let problem1 () =
  solve [| 16; 17; 23; 24; 39; 40 |] 100 "BankRobbery"

let problem2 () =
  solve [| 7; 11; 13; 17; 19; 23; 29; 31 |] 200 "Primes200"

let run () =
  problem1 ();
  problem2 ()
