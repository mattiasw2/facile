(* Equation Solving (Integer Polynomial Systems)
 * Inspired by SICStus Prolog CLP(R) equation-solving examples:
 * https://sicstus.sics.se/sicstus/docs/latest/html/sicstus/Equation-Solving.html
 *
 * Integer (finite domain) versions of polynomial equation solving.
 * Key constraints: nonlinear arithmetic, multiplication, exponentiation.
 * Tests FaCiLe's handling of nonlinear constraints and propagation. *)

open Facile
open Easy

(* Problem 1: SEND + MORE = MONEY
 * Classic cryptarithmetic: each letter is a distinct digit 0-9.
 *     S E N D
 *   + M O R E
 *   ---------
 *   M O N E Y
 * Unique solution: 9567 + 1085 = 10652 *)
let send_more_money () =
  Printf.printf "SEND + MORE = MONEY\n";
  let s = Fd.interval 1 9 in
  let e = Fd.interval 0 9 in
  let n = Fd.interval 0 9 in
  let d = Fd.interval 0 9 in
  let m = Fd.interval 1 9 in
  let o = Fd.interval 0 9 in
  let r = Fd.interval 0 9 in
  let y = Fd.interval 0 9 in
  let vars = [| s; e; n; d; m; o; r; y |] in
  Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) vars);
  (* SEND + MORE = MONEY rearranged:
     1000*S + 91*E - 90*N + D - 9000*M - 900*O + 10*R - Y = 0 *)
  Cstr.post (Arith.scalprod_fd [|1000; 91; -90; 1; -9000; -900; 10; -1|] vars =~ i2e 0);

  let labeling = Goals.Array.labeling vars in
  let bt = ref 0 in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count"
      (fun () ->
        incr nsol;
        let v = Array.map Fd.int_value vars in
        Printf.printf "  %d%d%d%d + %d%d%d%d = %d%d%d%d%d\n"
          v.(0) v.(1) v.(2) v.(3) v.(4) v.(5) v.(6) v.(1)
          v.(4) v.(5) v.(2) v.(1) v.(7);
        let send_v = 1000*v.(0) + 100*v.(1) + 10*v.(2) + v.(3) in
        let more_v = 1000*v.(4) + 100*v.(5) + 10*v.(6) + v.(1) in
        let money_v = 10000*v.(4) + 1000*v.(5) + 100*v.(2) + 10*v.(1) + v.(7) in
        assert (send_v + more_v = money_v);
        Stak.fail "next")
  in
  ignore (Goals.solve ~control:(fun b -> bt := b) (labeling &&~ count_goal));
  assert (!nsol = 1);
  Printf.printf "  SEND+MORE=MONEY: %d solution, %d backtracks PASSED\n" !nsol !bt

(* Problem 2: Coupled polynomial equations
 * Solve systems of nonlinear integer equations.
 * Analogous to SICStus CLP(R) polynomial system examples. *)

(* 2a: x^2 + y^2 = 25, x + y = 7 (non-negative)
 * Solutions: (3, 4) and (4, 3) *)
let poly_system_1 () =
  Printf.printf "Polynomial system: x^2+y^2=25, x+y=7\n";
  let x = Fd.interval 0 9 in
  let y = Fd.interval 0 9 in
  let vars = [| x; y |] in
  Cstr.post (fd2e x **~ 2 +~ fd2e y **~ 2 =~ i2e 25);
  Cstr.post (fd2e x +~ fd2e y =~ i2e 7);
  let labeling = Goals.Array.labeling vars in
  let bt = ref 0 in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count"
      (fun () ->
        incr nsol;
        let xv = Fd.int_value x and yv = Fd.int_value y in
        Printf.printf "  x=%d, y=%d\n" xv yv;
        assert (xv*xv + yv*yv = 25);
        assert (xv + yv = 7);
        Stak.fail "next")
  in
  ignore (Goals.solve ~control:(fun b -> bt := b) (labeling &&~ count_goal));
  assert (!nsol = 2);
  Printf.printf "  System 1: %d solutions, %d backtracks PASSED\n" !nsol !bt

(* 2b: x*y = 6, x^2 + y^2 = 13 (signed domain)
 * Solutions: (2,3), (3,2), (-2,-3), (-3,-2) *)
let poly_system_2 () =
  Printf.printf "Polynomial system: x*y=6, x^2+y^2=13\n";
  let x = Fd.interval (-9) 9 in
  let y = Fd.interval (-9) 9 in
  let vars = [| x; y |] in
  Cstr.post (fd2e x *~ fd2e y =~ i2e 6);
  Cstr.post (fd2e x **~ 2 +~ fd2e y **~ 2 =~ i2e 13);
  let labeling = Goals.Array.labeling vars in
  let bt = ref 0 in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count"
      (fun () ->
        incr nsol;
        let xv = Fd.int_value x and yv = Fd.int_value y in
        Printf.printf "  x=%d, y=%d\n" xv yv;
        assert (xv * yv = 6);
        assert (xv*xv + yv*yv = 13);
        Stak.fail "next")
  in
  ignore (Goals.solve ~control:(fun b -> bt := b) (labeling &&~ count_goal));
  assert (!nsol = 4);
  Printf.printf "  System 2: %d solutions, %d backtracks PASSED\n" !nsol !bt

(* 2c: x^2 + y^2 + z^2 = 29, x + y + z = 9, x*y + y*z + x*z = 26 (non-negative)
 * Solutions: all 6 permutations of (2, 3, 4) *)
let poly_system_3 () =
  Printf.printf "Polynomial system: x^2+y^2+z^2=29, x+y+z=9, xy+yz+xz=26\n";
  let x = Fd.interval 0 9 in
  let y = Fd.interval 0 9 in
  let z = Fd.interval 0 9 in
  let vars = [| x; y; z |] in
  Cstr.post (fd2e x **~ 2 +~ fd2e y **~ 2 +~ fd2e z **~ 2 =~ i2e 29);
  Cstr.post (fd2e x +~ fd2e y +~ fd2e z =~ i2e 9);
  Cstr.post (fd2e x *~ fd2e y +~ fd2e y *~ fd2e z +~ fd2e x *~ fd2e z =~ i2e 26);
  let labeling = Goals.Array.labeling vars in
  let bt = ref 0 in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count"
      (fun () ->
        incr nsol;
        let xv = Fd.int_value x and yv = Fd.int_value y and zv = Fd.int_value z in
        Printf.printf "  x=%d, y=%d, z=%d\n" xv yv zv;
        assert (xv*xv + yv*yv + zv*zv = 29);
        assert (xv + yv + zv = 9);
        assert (xv*yv + yv*zv + xv*zv = 26);
        Stak.fail "next")
  in
  ignore (Goals.solve ~control:(fun b -> bt := b) (labeling &&~ count_goal));
  assert (!nsol = 6);
  Printf.printf "  System 3: %d solutions, %d backtracks PASSED\n" !nsol !bt

(* Problem 3: Pythagorean triples
 * Find all (a, b, c) with 1 <= a <= b <= c <= n and a^2 + b^2 = c^2.
 * Nonlinear enumeration benchmark analogous to SICStus high-degree example. *)
let pythagorean_triples n expected =
  Printf.printf "Pythagorean triples c <= %d\n" n;
  let a = Fd.interval 1 n in
  let b = Fd.interval 1 n in
  let c = Fd.interval 1 n in
  let vars = [| a; b; c |] in
  Cstr.post (fd2e a **~ 2 +~ fd2e b **~ 2 =~ fd2e c **~ 2);
  Cstr.post (fd2e a <=~ fd2e b);
  Cstr.post (fd2e b <=~ fd2e c);
  let labeling = Goals.Array.labeling vars in
  let bt = ref 0 in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count"
      (fun () ->
        incr nsol;
        let av = Fd.int_value a and bv = Fd.int_value b and cv = Fd.int_value c in
        if !nsol <= 10 then
          Printf.printf "  (%d, %d, %d)\n" av bv cv;
        assert (av*av + bv*bv = cv*cv);
        assert (av <= bv && bv <= cv);
        Stak.fail "next")
  in
  ignore (Goals.solve ~control:(fun b -> bt := b) (labeling &&~ count_goal));
  assert (!nsol = expected);
  Printf.printf "  Pythagorean triples c<=%d: %d triples, %d backtracks PASSED\n" n !nsol !bt

(* Problem 4: Sum of four squares (Lagrange's theorem)
 * Every positive integer n = a^2 + b^2 + c^2 + d^2.
 * Find all ordered representations (a <= b <= c <= d). *)
let four_squares target expected =
  Printf.printf "Four squares: %d = a^2+b^2+c^2+d^2\n" target;
  let max_v = truncate (sqrt (float target)) in
  let a = Fd.interval 0 max_v in
  let b = Fd.interval 0 max_v in
  let c = Fd.interval 0 max_v in
  let d = Fd.interval 0 max_v in
  let vars = [| a; b; c; d |] in
  Cstr.post (fd2e a **~ 2 +~ fd2e b **~ 2 +~ fd2e c **~ 2 +~ fd2e d **~ 2 =~ i2e target);
  Cstr.post (fd2e a <=~ fd2e b);
  Cstr.post (fd2e b <=~ fd2e c);
  Cstr.post (fd2e c <=~ fd2e d);
  let labeling = Goals.Array.labeling vars in
  let bt = ref 0 in
  let nsol = ref 0 in
  let count_goal =
    Goals.atomic ~name:"count"
      (fun () ->
        incr nsol;
        let av = Fd.int_value a and bv = Fd.int_value b
        and cv = Fd.int_value c and dv = Fd.int_value d in
        if !nsol <= 20 then
          Printf.printf "  %d = %d^2+%d^2+%d^2+%d^2\n" target av bv cv dv;
        assert (av*av + bv*bv + cv*cv + dv*dv = target);
        assert (av <= bv && bv <= cv && cv <= dv);
        Stak.fail "next")
  in
  ignore (Goals.solve ~control:(fun b -> bt := b) (labeling &&~ count_goal));
  assert (!nsol = expected);
  Printf.printf "  Four squares %d: %d representations, %d backtracks PASSED\n" target !nsol !bt

let run () =
  send_more_money ();
  poly_system_1 ();
  poly_system_2 ();
  poly_system_3 ();
  pythagorean_triples 50 20;
  pythagorean_triples 100 52;
  four_squares 100 7;
  four_squares 1000 17
