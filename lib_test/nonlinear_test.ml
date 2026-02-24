(* Nonlinear Arithmetic Tests
   Direct tests for division, modulo, absolute value, exponentiation,
   and multiplication constraints with propagation verification.

   Demonstrates: /~, %~, abs, **~, *~ with signed domains,
   bidirectional propagation, and all-solutions enumeration. *)

open Facile
open Easy

let errors = ref 0
let check name cond =
  if not cond then begin
    Printf.eprintf "FAILED: %s\n%!" name;
    incr errors
  end

(* === Division /~ === *)

(* 1a: x / y = z where x in [6,12], y in [2,4] *)
let test_div_enumerate () =
  let x = Fd.interval 6 12 in
  let y = Fd.interval 2 4 in
  let z = Arith.e2fd (fd2e x /~ fd2e y) in
  let goal = Goals.Array.labeling [|x; y; z|] in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x and yv = Fd.int_value y and zv = Fd.int_value z in
      check (Printf.sprintf "div: %d / %d = %d" xv yv zv) (xv / yv = zv);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "div: found solutions" (!nsol > 0);
  Printf.printf "  x/y: %d solutions\n%!" !nsol

(* 1b: 15 / y = 5 => y = 3 *)
let test_div_propagate () =
  let y2 = Fd.interval 1 10 in
  let z2 = Arith.e2fd (i2e 15 /~ fd2e y2) in
  Cstr.post (fd2e z2 =~ i2e 5);
  check "div: 15/y=5 propagates" (Goals.solve (Goals.Array.labeling [|y2|]));
  check "div: 15/y=5 => y=3" (Fd.int_value y2 = 3)

(* 1c: x / y = 2 enumeration *)
let test_div_constrained () =
  let x3 = Fd.interval 1 10 in
  let y3 = Fd.interval 1 5 in
  let z3 = Arith.e2fd (fd2e x3 /~ fd2e y3) in
  Cstr.post (fd2e z3 =~ i2e 2);
  let nsol3 = ref 0 in
  let goal3 = Goals.Array.labeling [|x3; y3|] in
  let count3 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x3 and yv = Fd.int_value y3 in
      check (Printf.sprintf "div: %d/%d=2" xv yv) (xv / yv = 2);
      incr nsol3; Stak.fail "next") in
  ignore (Goals.solve (goal3 &&~ count3));
  check "div: x/y=2 has solutions" (!nsol3 > 0);
  Printf.printf "  x/y=2: %d solutions\n%!" !nsol3

(* === Modulo %~ === *)

(* 2a: x % 3 = 1, x in [0,15] *)
let test_mod_fixed_divisor () =
  let x = Fd.interval 0 15 in
  Cstr.post (fd2e x %~ i2e 3 =~ i2e 1);
  let nsol = ref 0 in
  let goal = Goals.Array.labeling [|x|] in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x in
      check (Printf.sprintf "mod: %d %% 3 = %d" xv (xv mod 3)) (xv mod 3 = 1);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "mod: x%%3=1 count" (!nsol = 5);
  Printf.printf "  x%%3=1: %d solutions\n%!" !nsol

(* 2b: x % y = 0 (divisibility), x in [1,12], y in [2,4] *)
let test_mod_divisibility () =
  let x2 = Fd.interval 1 12 in
  let y2 = Fd.interval 2 4 in
  Cstr.post (fd2e x2 %~ fd2e y2 =~ i2e 0);
  let nsol2 = ref 0 in
  let goal2 = Goals.Array.labeling [|x2; y2|] in
  let count2 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x2 and yv = Fd.int_value y2 in
      check (Printf.sprintf "mod: %d %% %d = 0" xv yv) (xv mod yv = 0);
      incr nsol2; Stak.fail "next") in
  ignore (Goals.solve (goal2 &&~ count2));
  check "mod: x%%y=0 has solutions" (!nsol2 > 0);
  Printf.printf "  x%%y=0: %d solutions\n%!" !nsol2

(* 2c: x % y = r with all three variable *)
let test_mod_three_vars () =
  let x3 = Fd.interval 10 15 in
  let y3 = Fd.interval 3 5 in
  let r3 = Arith.e2fd (fd2e x3 %~ fd2e y3) in
  let nsol3 = ref 0 in
  let goal3 = Goals.Array.labeling [|x3; y3; r3|] in
  let count3 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x3 and yv = Fd.int_value y3 and rv = Fd.int_value r3 in
      check (Printf.sprintf "mod: %d %% %d = %d" xv yv rv) (xv mod yv = rv);
      incr nsol3; Stak.fail "next") in
  ignore (Goals.solve (goal3 &&~ count3));
  check "mod: x%%y=r has solutions" (!nsol3 > 0);
  Printf.printf "  x%%y=r: %d solutions\n%!" !nsol3

(* === Absolute value |x| === *)

(* 3a: |x| = 5, x in [-10,10] => x = -5 or x = 5 *)
let test_abs_fixed () =
  let x = Fd.interval (-10) 10 in
  Cstr.post (Arith.abs (fd2e x) =~ i2e 5);
  let nsol = ref 0 in
  let goal = Goals.Array.labeling [|x|] in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x in
      check (Printf.sprintf "abs: |%d| = 5" xv) (abs xv = 5);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "abs: |x|=5 has 2 solutions" (!nsol = 2);
  Printf.printf "  |x|=5: %d solutions\n%!" !nsol

(* 3b: |x - y| >= 3, x,y in [0,5] *)
let test_abs_diff () =
  let x2 = Fd.interval 0 5 in
  let y2 = Fd.interval 0 5 in
  Cstr.post (Arith.abs (fd2e x2 -~ fd2e y2) >=~ i2e 3);
  let nsol2 = ref 0 in
  let goal2 = Goals.Array.labeling [|x2; y2|] in
  let count2 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x2 and yv = Fd.int_value y2 in
      check (Printf.sprintf "abs: |%d-%d| >= 3" xv yv) (abs (xv - yv) >= 3);
      incr nsol2; Stak.fail "next") in
  ignore (Goals.solve (goal2 &&~ count2));
  check "abs: |x-y|>=3 has solutions" (!nsol2 > 0);
  Printf.printf "  |x-y|>=3: %d solutions\n%!" !nsol2

(* 3c: |x| = y, x in [-3,3], y in [0,5] — bidirectional *)
let test_abs_bidirectional () =
  let x3 = Fd.interval (-3) 3 in
  let y3 = Fd.interval 0 5 in
  Cstr.post (Arith.abs (fd2e x3) =~ fd2e y3);
  let nsol3 = ref 0 in
  let goal3 = Goals.Array.labeling [|x3; y3|] in
  let count3 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x3 and yv = Fd.int_value y3 in
      check (Printf.sprintf "abs: |%d| = %d" xv yv) (abs xv = yv);
      incr nsol3; Stak.fail "next") in
  ignore (Goals.solve (goal3 &&~ count3));
  check "abs: |x|=y has 7 solutions" (!nsol3 = 7);
  Printf.printf "  |x|=y: %d solutions\n%!" !nsol3

(* === Exponentiation **~ === *)

(* 4a: x^2 = 16, x in [-10, 10] => x = -4 or x = 4 *)
let test_expn_square () =
  let x = Fd.interval (-10) 10 in
  Cstr.post (fd2e x **~ 2 =~ i2e 16);
  let nsol = ref 0 in
  let goal = Goals.Array.labeling [|x|] in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x in
      check (Printf.sprintf "expn: %d^2 = 16" xv) (xv * xv = 16);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "expn: x^2=16 has 2 solutions" (!nsol = 2);
  Printf.printf "  x^2=16: %d solutions\n%!" !nsol

(* 4b: x^3 = 27, x in [-5, 5] => x = 3 *)
let test_expn_cube () =
  let x2 = Fd.interval (-5) 5 in
  Cstr.post (fd2e x2 **~ 3 =~ i2e 27);
  check "expn: x^3=27 propagates" (Goals.solve (Goals.Array.labeling [|x2|]));
  check "expn: x^3=27 => x=3" (Fd.int_value x2 = 3)

(* 4c: x^2 + y^2 = z^2 (Pythagorean), x,y,z in [1,20], x<=y *)
let test_expn_pythagorean () =
  let x3 = Fd.interval 1 20 in
  let y3 = Fd.interval 1 20 in
  let z3 = Fd.interval 1 20 in
  Cstr.post (fd2e x3 **~ 2 +~ fd2e y3 **~ 2 =~ fd2e z3 **~ 2);
  Cstr.post (fd2e x3 <=~ fd2e y3);
  let nsol3 = ref 0 in
  let goal3 = Goals.Array.labeling [|x3; y3; z3|] in
  let count3 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x3 and yv = Fd.int_value y3 and zv = Fd.int_value z3 in
      check (Printf.sprintf "expn: %d^2+%d^2=%d^2" xv yv zv)
        (xv*xv + yv*yv = zv*zv);
      incr nsol3; Stak.fail "next") in
  ignore (Goals.solve (goal3 &&~ count3));
  (* 3,4,5 / 5,12,13 / 6,8,10 / 8,15,17 / 9,12,15 / 12,16,20 = 6 *)
  check "expn: pythagorean <=20 has 6 triples" (!nsol3 = 6);
  Printf.printf "  pythagorean <=20: %d triples\n%!" !nsol3

(* 4d: x^2 with non-negative domain *)
let test_expn_nonneg () =
  let x4 = Fd.interval 0 5 in
  let z4 = Arith.e2fd (fd2e x4 **~ 2) in
  Cstr.post (fd2e z4 >=~ i2e 10);
  let nsol4 = ref 0 in
  let goal4 = Goals.Array.labeling [|x4|] in
  let count4 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x4 in
      check (Printf.sprintf "expn: %d^2 >= 10" xv) (xv * xv >= 10);
      incr nsol4; Stak.fail "next") in
  ignore (Goals.solve (goal4 &&~ count4));
  check "expn: x^2>=10 x in [0,5] has 2 solutions" (!nsol4 = 2);
  Printf.printf "  x^2>=10: %d solutions\n%!" !nsol4

(* === Multiplication *~ === *)

(* 5a: x * y = 12, x in [1,6], y in [1,6] *)
let test_mult_fixed () =
  let x = Fd.interval 1 6 in
  let y = Fd.interval 1 6 in
  Cstr.post (fd2e x *~ fd2e y =~ i2e 12);
  let nsol = ref 0 in
  let goal = Goals.Array.labeling [|x; y|] in
  let count_goal =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x and yv = Fd.int_value y in
      check (Printf.sprintf "mult: %d*%d=12" xv yv) (xv * yv = 12);
      incr nsol; Stak.fail "next") in
  ignore (Goals.solve (goal &&~ count_goal));
  check "mult: x*y=12 has 4 solutions" (!nsol = 4);
  Printf.printf "  x*y=12: %d solutions\n%!" !nsol

(* 5b: signed multiplication: x * y = -6, x in [-5,5], y in [-5,5] *)
let test_mult_signed () =
  let x2 = Fd.interval (-5) 5 in
  let y2 = Fd.interval (-5) 5 in
  Cstr.post (fd2e x2 *~ fd2e y2 =~ i2e (-6));
  let nsol2 = ref 0 in
  let goal2 = Goals.Array.labeling [|x2; y2|] in
  let count2 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x2 and yv = Fd.int_value y2 in
      check (Printf.sprintf "mult: %d*%d=-6" xv yv) (xv * yv = -6);
      incr nsol2; Stak.fail "next") in
  ignore (Goals.solve (goal2 &&~ count2));
  check "mult: x*y=-6 has solutions" (!nsol2 > 0);
  Printf.printf "  x*y=-6: %d solutions\n%!" !nsol2

(* 5c: x * y = z, enumerate all for small domain *)
let test_mult_three_vars () =
  let x3 = Fd.interval 1 4 in
  let y3 = Fd.interval 1 4 in
  let z3 = Arith.e2fd (fd2e x3 *~ fd2e y3) in
  Cstr.post (fd2e z3 <=~ i2e 8);
  let nsol3 = ref 0 in
  let goal3 = Goals.Array.labeling [|x3; y3; z3|] in
  let count3 =
    Goals.atomic ~name:"count" (fun () ->
      let xv = Fd.int_value x3 and yv = Fd.int_value y3 and zv = Fd.int_value z3 in
      check (Printf.sprintf "mult: %d*%d=%d" xv yv zv) (xv * yv = zv);
      check (Printf.sprintf "mult: %d<=8" zv) (zv <= 8);
      incr nsol3; Stak.fail "next") in
  ignore (Goals.solve (goal3 &&~ count3));
  check "mult: x*y=z, z<=8 has solutions" (!nsol3 > 0);
  Printf.printf "  x*y=z, z<=8: %d solutions\n%!" !nsol3

let run_test name f =
  Stak.reset ();
  f ();
  Printf.printf "  %s: OK\n%!" name

let () =
  Printf.printf "Division tests:\n%!";
  run_test "x/y enumerate" test_div_enumerate;
  run_test "15/y=5 propagate" test_div_propagate;
  run_test "x/y=2 constrained" test_div_constrained;
  Printf.printf "Modulo tests:\n%!";
  run_test "x%%3=1" test_mod_fixed_divisor;
  run_test "x%%y=0" test_mod_divisibility;
  run_test "x%%y=r" test_mod_three_vars;
  Printf.printf "Absolute value tests:\n%!";
  run_test "abs fixed" test_abs_fixed;
  run_test "abs diff" test_abs_diff;
  run_test "abs bidirectional" test_abs_bidirectional;
  Printf.printf "Exponentiation tests:\n%!";
  run_test "x^2=16" test_expn_square;
  run_test "x^3=27" test_expn_cube;
  run_test "pythagorean" test_expn_pythagorean;
  run_test "x^2 nonneg" test_expn_nonneg;
  Printf.printf "Multiplication tests:\n%!";
  run_test "x*y=12" test_mult_fixed;
  run_test "x*y=-6 signed" test_mult_signed;
  run_test "x*y=z" test_mult_three_vars;
  if !errors = 0 then
    Printf.printf "Nonlinear test: PASSED\n%!"
  else begin
    Printf.eprintf "Nonlinear test: %d FAILURES\n%!" !errors;
    exit 1
  end
