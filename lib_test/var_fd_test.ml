(* Var.Fd operations test — Fd.remove, Fd.values, Fd.iter
   Direct tests for finite domain variable manipulation functions.

   Demonstrates: Fd.remove, Fd.values, Fd.iter, Fd.member,
   Fd.is_var, Fd.is_bound, Fd.size, Fd.id, Fd.name, Fd.fprint *)

open Facile
open Easy

let errors = ref 0

let check name cond =
  if not cond then begin
    Printf.eprintf "FAILED: %s\n" name;
    incr errors
  end

let () =
  (* === Fd.values === *)
  let v1 = Fd.create (Domain.create [1; 3; 5; 7; 9]) in
  let vals = Fd.values v1 in
  check "values: content" (vals = [1; 3; 5; 7; 9]);
  check "values: size matches" (List.length vals = Fd.size v1);

  (* values of bound variable *)
  let v_bound = Fd.elt 42 in
  check "values bound" (Fd.values v_bound = [42]);

  (* === Fd.iter === *)
  let acc = ref [] in
  Fd.iter (fun x -> acc := x :: !acc) v1;
  check "iter: collects all" (List.rev !acc = [1; 3; 5; 7; 9]);

  (* iter on bound variable *)
  let acc2 = ref [] in
  Fd.iter (fun x -> acc2 := x :: !acc2) v_bound;
  check "iter bound" (!acc2 = [42]);

  (* === Fd.remove === *)
  let v2 = Fd.create (Domain.create [2; 4; 6; 8; 10]) in
  Fd.remove v2 6;
  check "remove: not member" (not (Fd.member v2 6));
  check "remove: size" (Fd.size v2 = 4);
  check "remove: values" (Fd.values v2 = [2; 4; 8; 10]);

  (* remove non-existent value *)
  Fd.remove v2 7;
  check "remove non-existent: unchanged" (Fd.size v2 = 4);

  (* remove at boundary *)
  Fd.remove v2 2;
  check "remove min: new min" (Fd.min v2 = 4);
  check "remove min: values" (Fd.values v2 = [4; 8; 10]);

  Fd.remove v2 10;
  check "remove max: new max" (Fd.max v2 = 8);
  check "remove max: values" (Fd.values v2 = [4; 8]);

  (* remove until singleton *)
  Fd.remove v2 4;
  check "remove to singleton: bound" (Fd.is_bound v2);
  check "remove to singleton: value" (Fd.int_value v2 = 8);

  (* === Fd.member === *)
  let v3 = Fd.interval 1 10 in
  check "member: in range" (Fd.member v3 5);
  check "member: at min" (Fd.member v3 1);
  check "member: at max" (Fd.member v3 10);
  check "member: below range" (not (Fd.member v3 0));
  check "member: above range" (not (Fd.member v3 11));

  (* === Fd.is_var / Fd.is_bound === *)
  let v4 = Fd.interval 1 5 in
  check "is_var: unbound" (Fd.is_var v4);
  check "is_bound: unbound" (not (Fd.is_bound v4));

  let v5 = Fd.elt 10 in
  check "is_var: bound" (not (Fd.is_var v5));
  check "is_bound: bound" (Fd.is_bound v5);

  (* === Fd.id and Fd.name === *)
  let v6 = Fd.create ~name:"test_var" (Domain.interval 1 10) in
  let _id = Fd.id v6 in
  let nm = Fd.name v6 in
  check "name" (nm = "test_var");

  (* === Fd.fprint === *)
  Fd.fprint stdout v6;
  Printf.printf "\n";

  (* === Fd.array with name === *)
  let arr = Fd.array ~name:"arr" 3 0 5 in
  check "array: length" (Array.length arr = 3);
  Array.iter (fun v ->
    check "array: range" (Fd.min v = 0 && Fd.max v = 5)) arr;

  (* === Integration: Fd.remove in a CSP context ===
     Solve a small puzzle using manual domain pruning with Fd.remove *)
  let a = Fd.interval 1 5 in
  let b = Fd.interval 1 5 in
  let c = Fd.interval 1 5 in

  (* Manually prune: a cannot be 2 or 4 *)
  Fd.remove a 2;
  Fd.remove a 4;
  check "prune a: values" (Fd.values a = [1; 3; 5]);

  (* b cannot be 1 *)
  Fd.remove b 1;

  Cstr.post (Alldiff.cstr [|a; b; c|]);
  Cstr.post (fd2e a +~ fd2e b +~ fd2e c =~ i2e 9);

  if Goals.solve (Goals.Array.labeling [|a; b; c|]) then begin
    let va = Fd.int_value a and vb = Fd.int_value b and vc = Fd.int_value c in
    Printf.printf "CSP with Fd.remove: a=%d, b=%d, c=%d\n" va vb vc;

    check "CSP: a in {1,3,5}" (va = 1 || va = 3 || va = 5);
    check "CSP: b <> 1" (vb <> 1);
    check "CSP: all different" (va <> vb && vb <> vc && va <> vc);
    check "CSP: sum = 9" (va + vb + vc = 9);
  end else begin
    prerr_endline "No solution for CSP with remove"; exit 1
  end;

  (* === Fd.values consistency with Fd.iter === *)
  let v7 = Fd.create (Domain.create [10; 20; 30; 40; 50]) in
  let from_values = Fd.values v7 in
  let from_iter = ref [] in
  Fd.iter (fun x -> from_iter := x :: !from_iter) v7;
  let from_iter = List.rev !from_iter in
  check "values = iter" (from_values = from_iter);

  (* Summary *)
  if !errors = 0 then
    Printf.printf "Var.Fd test: PASSED\n"
  else begin
    Printf.eprintf "Var.Fd test: %d FAILURES\n" !errors;
    exit 1
  end
