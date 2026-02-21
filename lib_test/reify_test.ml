(* Reification test — Reify.xor and Reify.not
   Logical puzzle using exclusive-or and negation of constraints,
   combined with arithmetic constraints.

   Demonstrates: Reify.xor, Reify.not, Reify.boolean *)

open Facile
open Easy

let () =
  (* 6 variables: a..f in 1..8
     - xor(a = b, c = d) — exactly one pair is equal
     - NOT(e > f) — i.e., e <= f via reification
     - NOT(a = 1) — a cannot be 1
     - a + b + c + d = 20
     - e + f = 10
     - all different among e, f, and one from each xor pair *)

  let a = Fd.interval 1 8 in
  let b = Fd.interval 1 8 in
  let c = Fd.interval 1 8 in
  let d = Fd.interval 1 8 in
  let e = Fd.interval 1 8 in
  let f = Fd.interval 1 8 in

  (* Reify.xor: exactly one of (a=b) or (c=d) holds *)
  Cstr.post (Reify.xor (fd2e a =~ fd2e b) (fd2e c =~ fd2e d));

  (* Reify.not: NOT(e > f), so e <= f *)
  Cstr.post (Reify.not (fd2e e >~ fd2e f));

  (* Reify.not: NOT(a = 1), so a <> 1 *)
  Cstr.post (Reify.not (fd2e a =~ i2e 1));

  (* Arithmetic constraints *)
  Cstr.post (fd2e a +~ fd2e b +~ fd2e c +~ fd2e d =~ i2e 20);
  Cstr.post (fd2e e +~ fd2e f =~ i2e 10);

  (* Symmetry breaking *)
  Cstr.post (fd2e a <=~ fd2e b);
  Cstr.post (fd2e c <=~ fd2e d);

  (* e and f must differ *)
  Cstr.post (fd2e e <>~ fd2e f);

  let vars = [|a; b; c; d; e; f|] in

  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let goal = Goals.Array.forall ~select:min_size Goals.indomain vars in

  if Goals.solve goal then begin
    let va = Fd.int_value a and vb = Fd.int_value b
    and vc = Fd.int_value c and vd = Fd.int_value d
    and ve = Fd.int_value e and vf = Fd.int_value f in
    Printf.printf "Reify test solution:\n";
    Printf.printf "  a=%d, b=%d, c=%d, d=%d, e=%d, f=%d\n" va vb vc vd ve vf;

    (* Verify: xor(a=b, c=d) *)
    let eq_ab = va = vb in
    let eq_cd = vc = vd in
    assert ((eq_ab && not eq_cd) || (not eq_ab && eq_cd)
            || (Printf.eprintf "FAILED: xor(%b, %b)\n" eq_ab eq_cd; false));
    Printf.printf "  xor(a=b, c=d): %b xor %b = true\n" eq_ab eq_cd;

    (* Verify: NOT(e > f), i.e. e <= f *)
    assert (ve <= vf
            || (Printf.eprintf "FAILED: e=%d > f=%d\n" ve vf; false));

    (* Verify: NOT(a = 1), i.e. a <> 1 *)
    assert (va <> 1
            || (Printf.eprintf "FAILED: a = 1\n"; false));

    (* Verify: sums *)
    assert (va + vb + vc + vd = 20
            || (Printf.eprintf "FAILED: sum abcd = %d\n" (va+vb+vc+vd); false));
    assert (ve + vf = 10
            || (Printf.eprintf "FAILED: sum ef = %d\n" (ve+vf); false));

    (* Verify: e <> f *)
    assert (ve <> vf
            || (Printf.eprintf "FAILED: e = f = %d\n" ve; false));

    Printf.printf "Reify test: PASSED\n"
  end else begin
    prerr_endline "No solution"; exit 1
  end
