(* Custom Constraint test — Cstr.create
   Build a custom modular arithmetic constraint from scratch using
   Cstr.create with update, delay, check, not, and priority.
   Test it standalone, reified with Reify.boolean, and negated.

   Demonstrates: Cstr.create, Cstr.post, Cstr.id, Cstr.name,
   Cstr.priority, Cstr.is_solved, Cstr.active_store,
   Cstr.one, Cstr.zero *)

open Facile
open Easy

(* Custom constraint: x mod k = r *)
let rec modulo_cstr x k r =
  let update _ =
    match Fd.value x with
    | Val v ->
      if v mod k = r then true
      else Stak.fail "modulo"
    | Unk attr ->
      let dom = Var.Attr.dom attr in
      let new_dom = ref [] in
      Domain.iter (fun v ->
        if v mod k = r then new_dom := v :: !new_dom) dom;
      (match !new_dom with
       | [] -> Stak.fail "modulo"
       | _ ->
         let filtered = Domain.create (List.rev !new_dom) in
         Fd.refine x filtered;
         Fd.is_bound x)
  and delay ct =
    Fd.delay [Fd.on_refine] x ct
  and check () =
    match Fd.value x with
    | Val v -> v mod k = r
    | Unk attr ->
      let dom = Var.Attr.dom attr in
      let all_match = ref true and some_match = ref false in
      Domain.iter (fun v ->
        if v mod k = r then some_match := true
        else all_match := false) dom;
      if !all_match then true
      else if not !some_match then false
      else raise Cstr.DontKnow
  and not_fn () = not_modulo_cstr x k r
  in
  Cstr.create ~name:"modulo" ~priority:Cstr.normal
    ~check ~not:not_fn update delay

and not_modulo_cstr x k r =
  let update _ =
    match Fd.value x with
    | Val v ->
      if v mod k <> r then true
      else Stak.fail "not_modulo"
    | Unk attr ->
      let dom = Var.Attr.dom attr in
      let new_dom = ref [] in
      Domain.iter (fun v ->
        if v mod k <> r then new_dom := v :: !new_dom) dom;
      (match !new_dom with
       | [] -> Stak.fail "not_modulo"
       | _ ->
         let filtered = Domain.create (List.rev !new_dom) in
         Fd.refine x filtered;
         Fd.is_bound x)
  and delay ct =
    Fd.delay [Fd.on_refine] x ct
  and check () =
    match Fd.value x with
    | Val v -> v mod k <> r
    | Unk attr ->
      let dom = Var.Attr.dom attr in
      let all_nomatch = ref true and some_nomatch = ref false in
      Domain.iter (fun v ->
        if v mod k <> r then some_nomatch := true
        else all_nomatch := false) dom;
      if !all_nomatch then true
      else if not !some_nomatch then false
      else raise Cstr.DontKnow
  and not_fn () = modulo_cstr x k r
  in
  Cstr.create ~name:"not_modulo" ~priority:Cstr.normal
    ~check ~not:not_fn update delay

let () =
  (* === Part 1: Basic custom constraint ===
     x in 0..20, x mod 3 = 2 *)
  let x = Fd.interval 0 20 in
  let c = modulo_cstr x 3 2 in

  (* Test constraint metadata before posting *)
  let cname = Cstr.name c in
  let _cid = Cstr.id c in
  let cprio = Cstr.priority c in
  Printf.printf "Constraint: name=%s, priority=normal=%b\n" cname (cprio = Cstr.normal);
  assert (cname = "modulo");

  Cstr.post c;

  (* After posting and propagation, domain should only contain values where v mod 3 = 2 *)
  let vals = Fd.values x in
  Printf.printf "  x mod 3 = 2, domain: [";
  List.iter (fun v -> Printf.printf "%d " v) vals;
  Printf.printf "]\n";

  List.iter (fun v ->
    assert (v mod 3 = 2
            || (Printf.eprintf "FAILED: %d mod 3 = %d, expected 2\n" v (v mod 3); false)))
    vals;

  let expected = [2; 5; 8; 11; 14; 17; 20] in
  assert (vals = expected
          || (Printf.eprintf "FAILED: domain mismatch\n"; false));
  Printf.printf "Custom constraint basic: PASSED\n";

  (* === Part 2: Reified custom constraint ===
     y in 0..10, reify(y mod 4 = 1) as a boolean, constrain y >= 7 *)
  let y = Fd.interval 0 10 in
  let b = Reify.boolean (modulo_cstr y 4 1) in
  Cstr.post (fd2e y >=~ i2e 7);

  let goal2 = Goals.indomain y in

  if Goals.solve goal2 then begin
    let vy = Fd.int_value y in
    let vb = Fd.int_value b in
    Printf.printf "Reified modulo: y=%d, b=%d\n" vy vb;

    let expected_b = if vy mod 4 = 1 then 1 else 0 in
    assert (vb = expected_b
            || (Printf.eprintf "FAILED: y=%d, b=%d, expected b=%d\n" vy vb expected_b; false));
    Printf.printf "Custom constraint reified: PASSED\n"
  end else begin
    prerr_endline "No solution for reified"; exit 1
  end;

  (* === Part 3: Negated custom constraint ===
     z in 0..12, NOT(z mod 5 = 0) *)
  let z = Fd.interval 0 12 in
  Cstr.post (Reify.not (modulo_cstr z 5 0));

  let vals_z = Fd.values z in
  Printf.printf "NOT(z mod 5 = 0), domain: [";
  List.iter (fun v -> Printf.printf "%d " v) vals_z;
  Printf.printf "]\n";

  List.iter (fun v ->
    assert (v mod 5 <> 0
            || (Printf.eprintf "FAILED: %d is divisible by 5\n" v; false)))
    vals_z;
  Printf.printf "Custom constraint negated: PASSED\n";

  (* === Part 4: Cstr.one and Cstr.zero reified === *)
  let b_zero = Reify.boolean Cstr.zero in
  let b_one = Reify.boolean Cstr.one in

  if Goals.solve (Goals.Array.labeling [|b_zero; b_one|]) then begin
    let vbz = Fd.int_value b_zero in
    let vbo = Fd.int_value b_one in
    Printf.printf "Cstr.zero reified: %d, Cstr.one reified: %d\n" vbz vbo;
    assert (vbz = 0
            || (Printf.eprintf "FAILED: Cstr.zero should reify to 0\n"; false));
    assert (vbo = 1
            || (Printf.eprintf "FAILED: Cstr.one should reify to 1\n"; false));
    Printf.printf "Cstr.one/zero: PASSED\n"
  end else begin
    prerr_endline "Cstr.one/zero: no solution"; exit 1
  end;

  (* === Part 5: Cstr.active_store === *)
  let p = Fd.interval 1 100 in
  let q = Fd.interval 1 100 in
  Cstr.post (fd2e p +~ fd2e q =~ i2e 50);

  let active = Cstr.active_store () in
  Printf.printf "Active constraints: %d\n" (List.length active);
  assert (List.length active > 0
          || (Printf.eprintf "FAILED: expected active constraints\n"; false));
  Printf.printf "Cstr.active_store: PASSED\n";

  Printf.printf "Custom constraint test: PASSED\n"
