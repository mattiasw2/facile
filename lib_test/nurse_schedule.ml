(* Nurse Scheduling - Boolean sum demo
   Schedule nurses to shifts so that each shift has enough coverage.

   Demonstrates: Boolean.sum, Boolean.cstr, Domain.boolean *)

open Facile
open Easy

let () =
  let n_nurses = 5 in
  let n_shifts = 4 in
  Printf.printf "Nurse scheduling: %d nurses, %d shifts\n" n_nurses n_shifts;

  (* schedule.(nurse).(shift) = 1 if nurse works that shift, 0 otherwise *)
  let schedule = Array.init n_nurses (fun _ ->
    Array.init n_shifts (fun _ -> Fd.create Domain.boolean)) in

  (* Each shift needs at least 2 nurses (use Boolean.sum) *)
  for s = 0 to n_shifts - 1 do
    let nurses_on_shift = Array.init n_nurses (fun n -> schedule.(n).(s)) in
    let count = Boolean.sum nurses_on_shift in
    Cstr.post (fd2e count >=~ i2e 2)
  done;

  (* Each nurse works at most 3 shifts (use Boolean.cstr) *)
  for n = 0 to n_nurses - 1 do
    let shifts_count = Fd.interval 0 n_shifts in
    Cstr.post (Boolean.cstr schedule.(n) shifts_count);
    Cstr.post (fd2e shifts_count <=~ i2e 3)
  done;

  (* Nurse 0 and Nurse 1 cannot work the same shift (incompatibility) *)
  for s = 0 to n_shifts - 1 do
    Cstr.post (fd2e schedule.(0).(s) +~ fd2e schedule.(1).(s) <=~ i2e 1)
  done;

  (* Minimize total assignments *)
  let all_vars = Array.concat (Array.to_list schedule) in
  let total = Boolean.sum all_vars in

  let labeling = Goals.Array.labeling all_vars in

  let best = ref [||] in
  ignore
    (Goals.solve
       (Goals.minimize labeling total
          (fun c ->
            Printf.printf "  Found schedule with %d total assignments\n" c;
            best := Array.map Fd.int_value all_vars)));

  match !best with
  | [||] -> prerr_endline "No solution"; exit 1
  | sol ->
    Printf.printf "\nOptimal schedule:\n";
    Printf.printf "        ";
    for s = 0 to n_shifts - 1 do Printf.printf "S%d " s done;
    Printf.printf "\n";
    for n = 0 to n_nurses - 1 do
      Printf.printf "  N%d:   " n;
      for s = 0 to n_shifts - 1 do
        Printf.printf "%s  " (if sol.(n * n_shifts + s) = 1 then "X" else ".")
      done;
      Printf.printf "\n"
    done;
    let total_v = Array.fold_left ( + ) 0 sol in
    Printf.printf "Total assignments: %d\n" total_v;
    (* Verify: each shift has at least 2 nurses *)
    for s = 0 to n_shifts - 1 do
      let count = ref 0 in
      for n = 0 to n_nurses - 1 do
        count := !count + sol.(n * n_shifts + s)
      done;
      assert (!count >= 2
              || (Printf.eprintf "FAILED: shift %d has only %d nurses\n" s !count; false))
    done;
    (* Verify: each nurse works at most 3 shifts *)
    for n = 0 to n_nurses - 1 do
      let count = ref 0 in
      for s = 0 to n_shifts - 1 do
        count := !count + sol.(n * n_shifts + s)
      done;
      assert (!count <= 3
              || (Printf.eprintf "FAILED: nurse %d works %d shifts\n" n !count; false))
    done;
    (* Verify: nurse 0 and nurse 1 never share a shift *)
    for s = 0 to n_shifts - 1 do
      assert (sol.(0 * n_shifts + s) + sol.(1 * n_shifts + s) <= 1
              || (Printf.eprintf "FAILED: nurses 0,1 share shift %d\n" s; false))
    done;
    Printf.printf "Nurse schedule: PASSED\n"
