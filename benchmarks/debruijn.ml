(* De Bruijn Sequences
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/debruijn.py
 *
 * Find a de Bruijn sequence: a cyclic sequence over an alphabet of size `base`
 * in which every possible subsequence of length `n` appears exactly once.
 * Key constraints: AllDifferent, base conversion, de Bruijn shift property. *)

open Facile
open Easy

let pown b e =
  let r = ref 1 in
  for _ = 1 to e do r := !r * b done;
  !r

let solve basev n =
  let m = pown basev n in
  Printf.printf "De Bruijn: base=%d, n=%d, m=%d\n" basev n m;

  if m > 512 then
    Printf.printf "  Skipping: m=%d too large for practical solving\n" m
  else begin
    (* Node sequence: each node is a number 0..base^n-1 *)
    let x = Fd.array m 0 (m - 1) in

    (* Binary (base) representation of each node: binary[i][j] in 0..base-1 *)
    let binary = Array.init m (fun _ -> Fd.array n 0 (basev - 1)) in

    (* The output sequence (first digit of each node) *)
    let bin_code = Fd.array m 0 (basev - 1) in

    (* All nodes are different *)
    Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) x);

    (* Convert x[i] <-> binary[i]: x[i] = sum(binary[i][j] * base^(n-j-1)) *)
    for i = 0 to m - 1 do
      let terms = Array.init n (fun j ->
        fd2e binary.(i).(j) *~ i2e (pown basev (n - j - 1)))
      in
      let expr = Array.fold_left (fun acc t -> acc +~ t) (i2e 0) terms in
      Cstr.post (fd2e x.(i) =~ expr)
    done;

    (* De Bruijn property: binary[i-1][j] == binary[i][j-1] *)
    for i = 1 to m - 1 do
      for j = 1 to n - 1 do
        Cstr.post (fd2e binary.(i - 1).(j) =~ fd2e binary.(i).(j - 1))
      done
    done;

    (* Wrap-around: binary[m-1][j] == binary[0][j-1] *)
    for j = 1 to n - 1 do
      Cstr.post (fd2e binary.(m - 1).(j) =~ fd2e binary.(0).(j - 1))
    done;

    (* Convert binary -> bin_code: bin_code[i] = binary[i][0] *)
    for i = 0 to m - 1 do
      Cstr.post (fd2e bin_code.(i) =~ fd2e binary.(i).(0))
    done;

    (* Symmetry breaking: x[0] is the minimum *)
    for i = 1 to m - 1 do
      Cstr.post (fd2e x.(0) <~ fd2e x.(i))
    done;

    (* Search with first-fail on x then binary *)
    let min_size =
      Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2)
    in
    let all_vars = Array.append x (Array.concat (Array.to_list binary)) in
    let labeling = Goals.Array.forall ~select:min_size Goals.indomain all_vars in

    (* Count all solutions *)
    let nsol = ref 0 in
    let count_goal =
      Goals.atomic ~name:"count_solution"
        (fun () ->
          incr nsol;
          let xv = Array.map Fd.int_value x in
          let bcode = Array.map Fd.int_value bin_code in
          if m <= 16 then begin
            Printf.printf "  x: ";
            Array.iter (fun v -> Printf.printf "%d " v) xv;
            Printf.printf " bin_code: ";
            Array.iter (fun v -> Printf.printf "%d " v) bcode;
            Printf.printf "\n"
          end;
          Stak.fail "next_solution")
    in

    let goal = labeling &&~ count_goal in

    let bt = ref 0 in
    ignore (Goals.solve ~control:(fun b -> bt := b) goal);

    Printf.printf "  De Bruijn base=%d n=%d: %d solutions, %d backtracks\n" basev n !nsol !bt;

    (* Known: base=2, n=3 -> 2 solutions *)
    if basev = 2 && n = 3 then begin
      if !nsol <> 2 then begin
        Printf.eprintf "  FAILED: expected 2 solutions, got %d\n" !nsol;
        assert false
      end else
        Printf.printf "  De Bruijn (2,3): PASSED (matches known count 2)\n"
    end
  end

let run () =
  solve 2 3;
  solve 2 4;
  solve 3 2
