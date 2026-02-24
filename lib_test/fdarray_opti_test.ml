(* FdArray and Opti module tests
   Tests for array min/max constraints, element access (get),
   and the alternative optimization module (Opti).

   Demonstrates: FdArray.min, FdArray.max, FdArray.get,
   Opti.minimize with Restart and Continue modes. *)

open Facile
open Easy

let errors = ref 0
let check name cond =
  if not cond then begin
    Printf.eprintf "FAILED: %s\n%!" name;
    incr errors
  end

(* === FdArray.min === *)

(* 1a: min of array with known values *)
let test_min_enumerate () =
  let xs = [| Fd.interval 3 8; Fd.interval 1 5; Fd.interval 4 9 |] in
  let m = FdArray.min xs in
  let goal = Goals.Array.labeling (Array.append xs [|m|]) in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let vs = Array.map Fd.int_value xs in
      let mv = Fd.int_value m in
      let expected = Array.fold_left min max_int vs in
      check (Printf.sprintf "min: min(%d,%d,%d)=%d" vs.(0) vs.(1) vs.(2) mv)
        (mv = expected);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "min: found solutions" (!nsol > 0);
  Printf.printf "  min of 3 vars: %d solutions\n%!" !nsol

(* 1b: constrain the minimum *)
let test_min_constrained () =
  let xs2 = [| Fd.interval 1 5; Fd.interval 1 5; Fd.interval 1 5 |] in
  let m2 = FdArray.min xs2 in
  Cstr.post (fd2e m2 =~ i2e 3);
  check "min: min=3 solvable" (Goals.solve (Goals.Array.labeling xs2));
  let vs2 = Array.map Fd.int_value xs2 in
  check "min: all >= 3" (Array.for_all (fun v -> v >= 3) vs2);
  check "min: some = 3" (Array.exists (fun v -> v = 3) vs2);
  Printf.printf "  min=3: [%d,%d,%d]\n%!" vs2.(0) vs2.(1) vs2.(2)

(* === FdArray.max === *)

(* 2a: max of array *)
let test_max_constrained () =
  let xs = [| Fd.interval 1 4; Fd.interval 2 6; Fd.interval 0 3 |] in
  let m = FdArray.max xs in
  Cstr.post (fd2e m =~ i2e 4);
  check "max: max=4 solvable" (Goals.solve (Goals.Array.labeling xs));
  let vs = Array.map Fd.int_value xs in
  check "max: all <= 4" (Array.for_all (fun v -> v <= 4) vs);
  check "max: some = 4" (Array.exists (fun v -> v = 4) vs);
  Printf.printf "  max=4: [%d,%d,%d]\n%!" vs.(0) vs.(1) vs.(2)

(* 2b: max with enumeration *)
let test_max_enumerate () =
  let xs2 = [| Fd.interval 0 3; Fd.interval 0 3 |] in
  let m2 = FdArray.max xs2 in
  Cstr.post (fd2e m2 <=~ i2e 2);
  let nsol = ref 0 in
  let goal = Goals.Array.labeling (Array.append xs2 [|m2|]) in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let v0 = Fd.int_value xs2.(0) and v1 = Fd.int_value xs2.(1) in
      let mv = Fd.int_value m2 in
      check (Printf.sprintf "max: max(%d,%d)=%d<=2" v0 v1 mv) (mv = max v0 v1 && mv <= 2);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "max: max<=2, 2 vars [0,3] has 9 solutions" (!nsol = 9);
  Printf.printf "  max<=2: %d solutions\n%!" !nsol

(* === FdArray.get (element constraint) === *)

(* 3a: basic element access *)
let test_get_basic () =
  let data = [| Fd.int 10; Fd.int 20; Fd.int 30; Fd.int 40 |] in
  let idx = Fd.interval 0 3 in
  let value = FdArray.get data idx in
  Cstr.post (fd2e value =~ i2e 30);
  check "get: data[idx]=30 solvable" (Goals.solve (Goals.Array.labeling [|idx|]));
  check "get: idx=2" (Fd.int_value idx = 2);
  Printf.printf "  data[idx]=30: idx=%d\n%!" (Fd.int_value idx)

(* 3b: variable array and variable index *)
let test_get_alldiff () =
  let arr = [| Fd.interval 1 5; Fd.interval 1 5; Fd.interval 1 5 |] in
  let idx2 = Fd.interval 0 2 in
  let val2 = FdArray.get arr idx2 in
  Cstr.post (Alldiff.cstr arr);
  Cstr.post (fd2e val2 =~ i2e 3);
  let nsol = ref 0 in
  let goal = Goals.Array.labeling (Array.append arr [|idx2; val2|]) in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let avs = Array.map Fd.int_value arr in
      let iv = Fd.int_value idx2 and vv = Fd.int_value val2 in
      check (Printf.sprintf "get: arr[%d]=%d=3" iv vv) (avs.(iv) = 3 && vv = 3);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "get: arr[idx]=3, alldiff has solutions" (!nsol > 0);
  Printf.printf "  arr[idx]=3, alldiff: %d solutions\n%!" !nsol

(* 3c: channeling via get — find index of maximum *)
let test_get_channel () =
  let costs = [| Fd.int 5; Fd.int 2; Fd.int 8; Fd.int 1; Fd.int 6 |] in
  let idx3 = Fd.interval 0 4 in
  let val3 = FdArray.get costs idx3 in
  Cstr.post (fd2e val3 =~ i2e 8);
  check "get: find index of 8" (Goals.solve (Goals.Array.labeling [|idx3|]));
  check "get: idx=2" (Fd.int_value idx3 = 2);
  Printf.printf "  find 8: idx=%d\n%!" (Fd.int_value idx3)

(* === Opti.minimize === *)

(* 4a: Minimize with Restart mode *)
let test_opti_restart () =
  let x = Fd.interval 1 10 in
  let y = Fd.interval 1 10 in
  let cost = Arith.e2fd (fd2e x +~ fd2e y) in
  Cstr.post (fd2e x *~ fd2e y >=~ i2e 12);
  let labeling = Goals.Array.labeling [|x; y|] in
  let best = ref None in
  let result = Opti.minimize labeling cost ~step:1 ~mode:Opti.Restart
    (fun c -> best := Some (Fd.int_value x, Fd.int_value y, c)) in
  (match result with
  | Some _ ->
    (match !best with
    | Some (xv, yv, cv) ->
      check (Printf.sprintf "opti restart: %d+%d=%d, %d*%d=%d>=12" xv yv cv xv yv (xv*yv))
        (xv + yv = cv && xv * yv >= 12);
      check "opti restart: optimal" (cv = 7);
      Printf.printf "  Restart: x=%d, y=%d, cost=%d\n%!" xv yv cv
    | None -> check "opti restart: best recorded" false)
  | None -> check "opti restart: found solution" false)

(* 4b: Minimize with Continue mode *)
let test_opti_continue () =
  let a = Fd.interval 1 10 in
  let b = Fd.interval 1 10 in
  let cost2 = Arith.e2fd (fd2e a +~ fd2e b) in
  Cstr.post (fd2e a *~ fd2e b >=~ i2e 12);
  let labeling2 = Goals.Array.labeling [|a; b|] in
  let best2 = ref None in
  let result2 = Opti.minimize labeling2 cost2 ~step:1 ~mode:Opti.Continue
    (fun c -> best2 := Some (Fd.int_value a, Fd.int_value b, c)) in
  (match result2 with
  | Some _ ->
    (match !best2 with
    | Some (av, bv, cv) ->
      check (Printf.sprintf "opti continue: %d+%d=%d" av bv cv) (av + bv = cv);
      check "opti continue: optimal" (cv = 7);
      Printf.printf "  Continue: a=%d, b=%d, cost=%d\n%!" av bv cv
    | None -> check "opti continue: best recorded" false)
  | None -> check "opti continue: found solution" false)

(* 4c: Minimize with step > 1 *)
let test_opti_step () =
  let v = Fd.interval 0 100 in
  let cost3 = Arith.e2fd (fd2e v) in
  Cstr.post (fd2e v %~ i2e 7 =~ i2e 0);
  Cstr.post (fd2e v >=~ i2e 1);
  let labeling3 = Goals.Array.labeling [|v|] in
  let best3 = ref 0 in
  let result3 = Opti.minimize labeling3 cost3 ~step:5 ~mode:Opti.Restart
    (fun c -> best3 := c) in
  (match result3 with
  | Some _ ->
    check "opti step=5: optimal=7" (!best3 = 7);
    Printf.printf "  Step=5: cost=%d\n%!" !best3
  | None -> check "opti step=5: found solution" false)

let run_test name f =
  Stak.reset ();
  f ();
  Printf.printf "  %s: OK\n%!" name

let () =
  Printf.printf "FdArray.min tests:\n%!";
  run_test "min enumerate" test_min_enumerate;
  run_test "min constrained" test_min_constrained;
  Printf.printf "FdArray.max tests:\n%!";
  run_test "max constrained" test_max_constrained;
  run_test "max enumerate" test_max_enumerate;
  Printf.printf "FdArray.get tests:\n%!";
  run_test "get basic" test_get_basic;
  run_test "get alldiff" test_get_alldiff;
  run_test "get channel" test_get_channel;
  Printf.printf "Opti.minimize tests:\n%!";
  run_test "opti restart" test_opti_restart;
  run_test "opti continue" test_opti_continue;
  run_test "opti step" test_opti_step;
  if !errors = 0 then
    Printf.printf "FdArray/Opti test: PASSED\n%!"
  else begin
    Printf.eprintf "FdArray/Opti test: %d FAILURES\n%!" !errors;
    exit 1
  end
