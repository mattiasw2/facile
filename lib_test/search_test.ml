(* Search Strategies test
   Solve 5-queens with different search strategies to verify they all
   find valid solutions. Each strategy is set up with independent variables.

   Demonstrates: Goals.dichotomic, Goals.lds, Goals.instantiate, Goals.sigma *)

open Facile
open Easy

(* Set up queens constraints on a pre-created array *)
let post_queens_constraints n queens =
  Cstr.post (Alldiff.cstr queens);
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      let diff = j - i in
      Cstr.post (fd2e queens.(i) -~ fd2e queens.(j) <>~ i2e diff);
      Cstr.post (fd2e queens.(i) -~ fd2e queens.(j) <>~ i2e (-diff));
    done
  done

(* Verify a queens solution *)
let verify_queens v n =
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      assert (v.(i) <> v.(j)
              || (Printf.eprintf "FAILED: queens[%d]=%d = queens[%d]=%d\n" i v.(i) j v.(j); false));
      assert (abs (v.(i) - v.(j)) <> j - i
              || (Printf.eprintf "FAILED: diagonal conflict %d,%d\n" i j; false))
    done
  done

let () =
  let n = 5 in
  let min_size =
    Goals.Array.choose_index (fun a1 a2 -> Var.Attr.size a1 < Var.Attr.size a2) in

  (* All strategies share variables in a single solver instance.
     We use a single large goal that tests all strategies in sequence
     using conjunction. Each sub-problem uses independent variables. *)

  (* Variables for each strategy *)
  let q_indomain = Fd.array n 0 (n - 1) in
  let q_dichotomic = Fd.array n 0 (n - 1) in
  let q_instantiate = Fd.array n 0 (n - 1) in
  let q_lds = Fd.array n 0 (n - 1) in
  let sigma_x = Fd.interval 1 6 in

  (* Post constraints for all queens instances *)
  post_queens_constraints n q_indomain;
  post_queens_constraints n q_dichotomic;
  post_queens_constraints n q_instantiate;
  post_queens_constraints n q_lds;

  (* Results storage *)
  let sol_indomain = Array.make n 0 in
  let sol_dichotomic = Array.make n 0 in
  let sol_instantiate = Array.make n 0 in
  let sol_lds = Array.make n 0 in
  let sigma_result = ref (0, 0) in

  (* Build a combined goal that solves all sub-problems *)
  let goal =
    (* 1. indomain *)
    Goals.Array.forall ~select:min_size Goals.indomain q_indomain
    &&~ Goals.atomic (fun () ->
      Array.iteri (fun i q -> sol_indomain.(i) <- Fd.int_value q) q_indomain)

    (* 2. dichotomic *)
    &&~ Goals.Array.forall ~select:min_size Goals.dichotomic q_dichotomic
    &&~ Goals.atomic (fun () ->
      Array.iteri (fun i q -> sol_dichotomic.(i) <- Fd.int_value q) q_dichotomic)

    (* 3. instantiate with max-value selection *)
    &&~ Goals.Array.forall ~select:min_size
          (Goals.instantiate Domain.max) q_instantiate
    &&~ Goals.atomic (fun () ->
      Array.iteri (fun i q -> sol_instantiate.(i) <- Fd.int_value q) q_instantiate)

    (* 4. sigma — existential variable for x * y = 12 *)
    &&~ Goals.sigma ~domain:(Domain.interval 1 6) (fun sigma_y ->
      Goals.atomic (fun () ->
        Cstr.post (fd2e sigma_x *~ fd2e sigma_y =~ i2e 12))
      &&~ Goals.indomain sigma_x
      &&~ Goals.indomain sigma_y
      &&~ Goals.atomic (fun () ->
        sigma_result := (Fd.int_value sigma_x, Fd.int_value sigma_y)))
  in

  if Goals.solve goal then begin
    (* Verify indomain solution *)
    Printf.printf "indomain: [";
    Array.iteri (fun i x -> if i > 0 then Printf.printf ", "; Printf.printf "%d" x) sol_indomain;
    Printf.printf "]\n";
    verify_queens sol_indomain n;
    Printf.printf "Search indomain: PASSED\n";

    (* Verify dichotomic solution *)
    Printf.printf "dichotomic: [";
    Array.iteri (fun i x -> if i > 0 then Printf.printf ", "; Printf.printf "%d" x) sol_dichotomic;
    Printf.printf "]\n";
    verify_queens sol_dichotomic n;
    Printf.printf "Search dichotomic: PASSED\n";

    (* Verify instantiate solution *)
    Printf.printf "instantiate(max): [";
    Array.iteri (fun i x -> if i > 0 then Printf.printf ", "; Printf.printf "%d" x) sol_instantiate;
    Printf.printf "]\n";
    verify_queens sol_instantiate n;
    Printf.printf "Search instantiate: PASSED\n";

    (* Verify sigma *)
    let (sx, sy) = !sigma_result in
    Printf.printf "sigma: x=%d, y=%d\n" sx sy;
    assert (sx * sy = 12
            || (Printf.eprintf "FAILED: %d * %d <> 12\n" sx sy; false));
    Printf.printf "Search sigma: PASSED\n"
  end else begin
    prerr_endline "FAILED: combined goal found no solution"; exit 1
  end;

  (* === LDS in a separate solve (LDS wraps a goal and must be top-level) === *)
  let lds_base =
    Goals.Array.forall ~select:min_size Goals.indomain q_lds in
  let lds_goal = Goals.lds ~step:1 lds_base in

  if Goals.solve lds_goal then begin
    Array.iteri (fun i q -> sol_lds.(i) <- Fd.int_value q) q_lds;
    Printf.printf "lds: [";
    Array.iteri (fun i x -> if i > 0 then Printf.printf ", "; Printf.printf "%d" x) sol_lds;
    Printf.printf "]\n";
    verify_queens sol_lds n;
    Printf.printf "Search lds: PASSED\n"
  end else begin
    prerr_endline "FAILED: lds found no solution"; exit 1
  end;

  Printf.printf "Search test: PASSED\n"
