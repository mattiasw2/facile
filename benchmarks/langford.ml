(* Langford's Problem (CSPLib #24)
 * Hakank benchmark: https://github.com/hakank/hakank/blob/master/cpmpy/langford.py
 *
 * Arrange 2 sets of positive integers 1..k into a sequence of length 2k,
 * such that the two occurrences of integer i are exactly i+1 positions apart.
 * Key constraints: AllDifferent on positions, element constraints. *)

open Facile
open Easy

let solve k =
  if k mod 4 <> 0 && k mod 4 <> 3 then
    Printf.printf "Langford k=%d: no solution exists (k mod 4 must be 0 or 3)\n" k
  else begin
    (* position[i] = position of first occurrence of value (i+1)
     * position[k+i] = position of second occurrence of value (i+1) *)
    let position = Fd.array (2 * k) 0 (2 * k - 1) in
    (* solution[j] = value at position j in the final sequence *)
    let solution = Fd.array (2 * k) 1 k in

    (* All positions are different *)
    Cstr.post (Alldiff.cstr ~algo:(Alldiff.Bin_matching Var.Fd.on_subst) position);

    (* For each value i (1..k): *)
    for i = 1 to k do
      (* Gap: second occurrence is exactly i+1 positions after first *)
      Cstr.post (fd2e position.(k + i - 1) =~ fd2e position.(i - 1) +~ i2e (i + 1));

      (* Element constraints: link positions to solution values *)
      let vi = Fd.int i in
      Cstr.post (FdArray.get_cstr solution position.(i - 1) vi);
      Cstr.post (FdArray.get_cstr solution position.(k + i - 1) vi)
    done;

    (* Symmetry breaking: first element < last element *)
    Cstr.post (fd2e solution.(0) <~ fd2e solution.(2 * k - 1));

    (* Search with first-fail *)
    let min_size =
      Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2)
    in
    let labeling = Goals.Array.forall ~select:min_size Goals.indomain position in

    let bt = ref 0 in
    if Goals.solve ~control:(fun b -> bt := b) labeling then begin
      let sol = Array.map Fd.int_value solution in
      let pos = Array.map Fd.int_value position in
      Printf.printf "Langford k=%d: " k;
      Array.iter (fun v -> Printf.printf "%d" v) sol;
      Printf.printf " (%d backtracks)\n" !bt;

      (* Verify: for each value i, the two occurrences are i+1 apart *)
      for i = 1 to k do
        let p1 = pos.(i - 1) in
        let p2 = pos.(k + i - 1) in
        assert (p2 - p1 = i + 1);
        assert (sol.(p1) = i);
        assert (sol.(p2) = i)
      done;
      (* Verify: each value 1..k appears exactly twice *)
      for i = 1 to k do
        let count = Array.fold_left (fun acc v -> if v = i then acc + 1 else acc) 0 sol in
        assert (count = 2)
      done;
      Printf.printf "Langford k=%d: PASSED\n" k
    end else
      Printf.printf "Langford k=%d: no solution found\n" k
  end

let run () =
  solve 8;
  solve 11;
  solve 12;
  solve 16;
  solve 20
