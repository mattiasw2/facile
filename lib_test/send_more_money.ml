(* SEND + MORE = MONEY
   Classic cryptarithmetic puzzle.
   Each letter represents a unique digit 0-9.
   Leading digits (S, M) cannot be zero. *)

open Facile
open Easy

let () =
  (* Variables: one per letter, domain 0..9 *)
  let s = Fd.interval 1 9  (* S can't be 0 *)
  and e = Fd.interval 0 9
  and n = Fd.interval 0 9
  and d = Fd.interval 0 9
  and m = Fd.interval 1 9  (* M can't be 0 *)
  and o = Fd.interval 0 9
  and r = Fd.interval 0 9
  and y = Fd.interval 0 9 in

  let letters = [|s; e; n; d; m; o; r; y|] in

  (* All letters represent different digits *)
  Cstr.post (Alldiff.cstr letters);

  (*     S E N D
     + M O R E
     ---------
     M O N E Y

     1000*S + 100*E + 10*N + D
   + 1000*M + 100*O + 10*R + E
   = 10000*M + 1000*O + 100*N + 10*E + Y *)
  let send  = i2e 1000 *~ fd2e s +~ i2e 100 *~ fd2e e +~ i2e 10 *~ fd2e n +~ fd2e d in
  let more  = i2e 1000 *~ fd2e m +~ i2e 100 *~ fd2e o +~ i2e 10 *~ fd2e r +~ fd2e e in
  let money = i2e 10000 *~ fd2e m +~ i2e 1000 *~ fd2e o +~ i2e 100 *~ fd2e n
              +~ i2e 10 *~ fd2e e +~ fd2e y in

  Cstr.post (send +~ more =~ money);

  (* Solve with first-fail heuristic *)
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in
  let goal = Goals.Array.forall ~select:min_size Goals.indomain letters in

  if Goals.solve goal then begin
    let vs = Fd.int_value s and ve = Fd.int_value e and vn = Fd.int_value n
    and vd = Fd.int_value d and vm = Fd.int_value m and vo = Fd.int_value o
    and vr = Fd.int_value r and vy = Fd.int_value y in
    let send_v  = 1000*vs + 100*ve + 10*vn + vd in
    let more_v  = 1000*vm + 100*vo + 10*vr + ve in
    let money_v = 10000*vm + 1000*vo + 100*vn + 10*ve + vy in
    Printf.printf "  %d\n+ %d\n------\n %d\n" send_v more_v money_v;
    (* Verify *)
    assert (send_v + more_v = money_v);
    assert (vs = 9 && ve = 5 && vn = 6 && vd = 7);
    assert (vm = 1 && vo = 0 && vr = 8 && vy = 2);
    Printf.printf "SEND+MORE=MONEY: PASSED\n"
  end else begin
    prerr_endline "No solution"; exit 1
  end
