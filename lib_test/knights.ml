(* Knights and Knaves - Reification demo
   Each person is a knight (1, always tells truth) or knave (0, always lies).
   A person's statement holds iff they are a knight.

   Demonstrates: Reify.boolean, <=>~~, ||~~, &&~~ *)

open Facile
open Easy

let () =
  (* 4 people: a, b, c, d — each is 0 (knave) or 1 (knight) *)
  let a = Fd.create Domain.boolean
  and b = Fd.create Domain.boolean
  and c = Fd.create Domain.boolean
  and d = Fd.create Domain.boolean in

  let is_knight x = fd2e x =~ i2e 1 in
  let is_knave  x = fd2e x =~ i2e 0 in

  (* A says: "B is a knight"
     A is knight <=> B is knight *)
  Cstr.post (is_knight a <=>~~ is_knight b);

  (* B says: "A and C are different types"
     B is knight <=> A <> C *)
  Cstr.post (is_knight b <=>~~ (fd2e a <>~ fd2e c));

  (* C says: "There are at least 2 knights among us"
     C is knight <=> (a + b + c + d >= 2) *)
  Cstr.post (is_knight c <=>~~ (fd2e a +~ fd2e b +~ fd2e c +~ fd2e d >=~ i2e 2));

  (* D says: "A is a knave"
     D is knight <=> A is knave *)
  Cstr.post (is_knight d <=>~~ is_knave a);

  let people = [|a; b; c; d|] in
  let names = [|"A"; "B"; "C"; "D"|] in

  if Goals.solve (Goals.Array.labeling people) then begin
    Printf.printf "Knights and Knaves solution:\n";
    let vals = Array.map Fd.int_value people in
    Array.iteri (fun i v ->
      Printf.printf "  %s is a %s\n" names.(i) (if v = 1 then "knight" else "knave")) vals;
    (* Verify each statement *)
    let va = vals.(0) and vb = vals.(1) and vc = vals.(2) and vd = vals.(3) in
    let total = Array.fold_left ( + ) 0 vals in
    (* A says "B is a knight": true iff vb=1 *)
    assert ((va = 1) = (vb = 1));
    (* B says "A and C are different": true iff va<>vc *)
    assert ((vb = 1) = (va <> vc));
    (* C says "at least 2 knights": true iff sum >= 2 *)
    assert ((vc = 1) = (total >= 2));
    (* D says "A is a knave": true iff va=0 *)
    assert ((vd = 1) = (va = 0));
    Printf.printf "Knights: PASSED\n"
  end else begin
    prerr_endline "No solution"; exit 1
  end
