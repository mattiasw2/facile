(* Interval Membership - Interval module demo
   Schedule tasks into time slots with time window constraints.
   Use Interval.is_member to check if a task falls within allowed windows,
   and use the boolean results to count satisfied preferences.

   Demonstrates: Interval.is_member, Interval.cstr *)

open Facile
open Easy

let () =
  (* 5 tasks, each assigned to a time slot 0..9 *)
  let n = 5 in
  let tasks = Fd.array n 0 9 in

  (* All tasks at different times *)
  Cstr.post (Alldiff.cstr tasks);

  (* Time windows: each task has a preferred interval *)
  let windows = [| (0, 3); (2, 5); (4, 7); (6, 9); (1, 4) |] in

  (* Use Interval.is_member to create boolean variables for membership *)
  let in_window = Array.init n (fun i ->
    let (lo, hi) = windows.(i) in
    Interval.is_member tasks.(i) lo hi) in

  (* Require at least 4 of 5 tasks within their preferred window *)
  let satisfied = Arith.e2fd (Arith.sum_fd in_window) in
  Cstr.post (fd2e satisfied >=~ i2e 4);

  (* Also demonstrate Interval.cstr directly *)
  (* Task 0 MUST be in [0,3] — post it as a hard constraint *)
  let b0 = Fd.create Domain.boolean in
  Cstr.post (Interval.cstr tasks.(0) 0 3 b0);
  Cstr.post (fd2e b0 =~ i2e 1);

  (* Task ordering: task 0 before task 1 *)
  Cstr.post (fd2e tasks.(0) <~ fd2e tasks.(1));

  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let goal = Goals.Array.forall ~select:min_size Goals.indomain tasks in

  if Goals.solve goal then begin
    Printf.printf "Task scheduling solution:\n";
    let vals = Array.map Fd.int_value tasks in
    let bools = Array.map Fd.int_value in_window in
    Array.iteri (fun i t ->
      let (lo, hi) = windows.(i) in
      Printf.printf "  Task %d: time=%d  window=[%d,%d]  %s\n"
        i t lo hi (if bools.(i) = 1 then "in-window" else "OUTSIDE")) vals;
    let n_satisfied = Array.fold_left ( + ) 0 bools in
    Printf.printf "Tasks in preferred window: %d/%d\n" n_satisfied n;
    (* Verify: all different *)
    let sorted = Array.copy vals in
    Array.sort compare sorted;
    for i = 0 to n - 2 do assert (sorted.(i) <> sorted.(i + 1)) done;
    (* Verify: at least 4 in window *)
    assert (n_satisfied >= 4);
    (* Verify: is_member correctness *)
    Array.iteri (fun i t ->
      let (lo, hi) = windows.(i) in
      let expected = if t >= lo && t <= hi then 1 else 0 in
      assert (bools.(i) = expected
              || (Printf.eprintf "FAILED: task %d at %d, window [%d,%d], got %d expected %d\n"
                    i t lo hi bools.(i) expected; false))) vals;
    (* Verify: task 0 in [0,3] *)
    assert (vals.(0) >= 0 && vals.(0) <= 3);
    (* Verify: task 0 before task 1 *)
    assert (vals.(0) < vals.(1));
    Printf.printf "Interval test: PASSED\n"
  end else begin
    prerr_endline "No solution"; exit 1
  end
