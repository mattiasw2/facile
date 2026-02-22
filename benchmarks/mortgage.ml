(* Mortgage Calculator (Finite Domain)
 * Adapted from SICStus CLP(R) example:
 * https://sicstus.sics.se/sicstus/docs/latest/html/sicstus/Mortgage-Calculator.html
 *
 * Demonstrates bidirectional arithmetic constraints:
 * the same model can solve for any unknown (balance, principal, payment,
 * or interest rate).
 *
 * The SICStus original uses CLP(R) over reals; this version uses integer
 * finite domains with amounts in cents and interest as integer percentage.
 *
 * Relation for each period:
 *   (balance_next + payment) * 100 = balance_current * (100 + rate)
 *
 * Key constraints: linear arithmetic, bidirectional propagation. *)

open Facile
open Easy

(* Post mortgage constraints for a fixed interest rate.
   balance.(0) = principal, balance.(periods) = final_balance.
   Intermediate balances are fresh FD variables. *)
let mortgage ~periods ~rate ~principal ~final_balance ~payment =
  let max_bal = 100_000_000 in
  let balance = Array.init (periods + 1) (fun i ->
    if i = 0 then principal
    else if i = periods then final_balance
    else Fd.interval 0 max_bal) in
  let m = 100 + rate in
  for i = 0 to periods - 1 do
    Cstr.post (
      i2e 100 *~ fd2e balance.(i + 1) +~ i2e 100 *~ fd2e payment
      =~
      i2e m *~ fd2e balance.(i))
  done;
  balance

(* Post mortgage constraints with variable interest rate (non-linear). *)
let mortgage_var_rate ~periods ~rate ~principal ~final_balance ~payment =
  let max_bal = 100_000_000 in
  let balance = Array.init (periods + 1) (fun i ->
    if i = 0 then principal
    else if i = periods then final_balance
    else Fd.interval 0 max_bal) in
  for i = 0 to periods - 1 do
    Cstr.post (
      i2e 100 *~ fd2e balance.(i + 1) +~ i2e 100 *~ fd2e payment
      =~
      i2e 100 *~ fd2e balance.(i) +~ fd2e rate *~ fd2e balance.(i))
  done;
  balance

(* Example 1: solve for final balance
   "Deposit $1000 at 10%, withdraw $250/year for 4 years -> balance?"
   Answer: $303.85 *)
let solve_for_balance () =
  Printf.printf "Mortgage: solve for final balance\n";
  Printf.printf "  P=$1000, rate=10%%, T=4, MP=$250\n";
  let principal = Fd.int 100_000 in
  let payment = Fd.int 25_000 in
  let final_balance = Fd.interval 0 1_000_000 in
  ignore (mortgage ~periods:4 ~rate:10 ~principal ~final_balance ~payment);
  let goal = Goals.Array.labeling [| final_balance |] in
  let bt = ref 0 in
  assert (Goals.solve ~control:(fun b -> bt := b) goal);
  let b = Fd.int_value final_balance in
  Printf.printf "  Final balance: %d cents ($%.2f)\n" b (float b /. 100.0);
  Printf.printf "  %d backtracks\n" !bt;
  assert (b = 30_385);
  Printf.printf "  solve-for-balance: PASSED\n"

(* Example 2: solve for principal
   "What initial deposit at 10% with $250/year withdrawals gives
    $303.85 after 4 years?" Answer: $1000 *)
let solve_for_principal () =
  Printf.printf "Mortgage: solve for principal\n";
  Printf.printf "  B=$303.85, rate=10%%, T=4, MP=$250\n";
  let principal = Fd.interval 0 1_000_000 in
  let payment = Fd.int 25_000 in
  let final_balance = Fd.int 30_385 in
  ignore (mortgage ~periods:4 ~rate:10 ~principal ~final_balance ~payment);
  let goal = Goals.Array.labeling [| principal |] in
  let bt = ref 0 in
  assert (Goals.solve ~control:(fun b -> bt := b) goal);
  let p = Fd.int_value principal in
  Printf.printf "  Principal: %d cents ($%.2f)\n" p (float p /. 100.0);
  Printf.printf "  %d backtracks\n" !bt;
  assert (p = 100_000);
  Printf.printf "  solve-for-principal: PASSED\n"

(* Example 3: solve for payment
   "What yearly payment reduces $1000 at 10% to $303.85 in 4 years?"
   Answer: $250 *)
let solve_for_payment () =
  Printf.printf "Mortgage: solve for payment\n";
  Printf.printf "  P=$1000, rate=10%%, T=4, B=$303.85\n";
  let principal = Fd.int 100_000 in
  let payment = Fd.interval 0 200_000 in
  let final_balance = Fd.int 30_385 in
  ignore (mortgage ~periods:4 ~rate:10 ~principal ~final_balance ~payment);
  let goal = Goals.dichotomic payment in
  let bt = ref 0 in
  assert (Goals.solve ~control:(fun b -> bt := b) goal);
  let mp = Fd.int_value payment in
  Printf.printf "  Payment: %d cents ($%.2f)\n" mp (float mp /. 100.0);
  Printf.printf "  %d backtracks\n" !bt;
  assert (mp = 25_000);
  Printf.printf "  solve-for-payment: PASSED\n"

(* Example 4: solve for interest rate (non-linear)
   "What rate makes $1000 with $250/year reach $303.85 in 4 years?"
   Answer: 10% *)
let solve_for_rate () =
  Printf.printf "Mortgage: solve for interest rate\n";
  Printf.printf "  P=$1000, T=4, MP=$250, B=$303.85\n";
  let principal = Fd.int 100_000 in
  let payment = Fd.int 25_000 in
  let final_balance = Fd.int 30_385 in
  let rate = Fd.interval 1 50 in
  ignore (mortgage_var_rate ~periods:4 ~rate ~principal ~final_balance ~payment);
  let goal = Goals.Array.labeling [| rate |] in
  let bt = ref 0 in
  assert (Goals.solve ~control:(fun b -> bt := b) goal);
  let r = Fd.int_value rate in
  Printf.printf "  Interest rate: %d%%\n" r;
  Printf.printf "  %d backtracks\n" !bt;
  assert (r = 10);
  Printf.printf "  solve-for-rate: PASSED\n"

(* Example 5: second scenario
   P=$2000, rate=5%, T=3, MP=$500 -> B=$739.00 *)
let solve_scenario2 () =
  Printf.printf "Mortgage: second scenario\n";
  Printf.printf "  P=$2000, rate=5%%, T=3, MP=$500\n";
  let principal = Fd.int 200_000 in
  let payment = Fd.int 50_000 in
  let final_balance = Fd.interval 0 1_000_000 in
  ignore (mortgage ~periods:3 ~rate:5 ~principal ~final_balance ~payment);
  let goal = Goals.Array.labeling [| final_balance |] in
  let bt = ref 0 in
  assert (Goals.solve ~control:(fun b -> bt := b) goal);
  let b = Fd.int_value final_balance in
  Printf.printf "  Final balance: %d cents ($%.2f)\n" b (float b /. 100.0);
  Printf.printf "  %d backtracks\n" !bt;
  assert (b = 73_900);
  Printf.printf "  scenario2: PASSED\n"

let run () =
  solve_for_balance ();
  solve_for_principal ();
  solve_for_payment ();
  solve_for_rate ();
  solve_scenario2 ()
