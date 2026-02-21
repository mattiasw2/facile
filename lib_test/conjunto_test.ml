(* Set Constraints demo — Conjunto module
   Assign items to groups using set variables with constraints on
   cardinality, subset, disjoint, membership, union, intersection,
   smallest, and sum_weight.

   Demonstrates: SetFd, SetDomain, Conjunto.cardinal, Conjunto.subset,
   Conjunto.disjoint, Conjunto.all_disjoint, Conjunto.mem, Conjunto.union,
   Conjunto.inter, Conjunto.smallest, Conjunto.sum_weight, Conjunto.inside,
   Conjunto.outside, Conjunto.inf_min, Goals.Conjunto.indomain *)

open Facile
open Easy

let () =
  (* Items 1..6, partition into 3 disjoint groups whose union = {1..6}.
     Group sizes: g1 has 2, g2 has 2, g3 has 2.
     Additional: subset, intersection, smallest, sum_weight constraints. *)

  let universe = SetDomain.elt_of_list [1; 2; 3; 4; 5; 6] in
  let empty = SetDomain.elt_of_list [] in

  (* Each group can contain any subset of universe *)
  let g1 = Var.SetFd.create (SetDomain.interval empty universe) in
  let g2 = Var.SetFd.create (SetDomain.interval empty universe) in
  let g3 = Var.SetFd.create (SetDomain.interval empty universe) in

  (* Groups must be pairwise disjoint *)
  Cstr.post (Conjunto.all_disjoint [|g1; g2; g3|]);

  (* Union of all groups = universe *)
  let u12 = Conjunto.union g1 g2 in
  let u123 = Conjunto.union u12 g3 in
  Cstr.post (Conjunto.subset (Var.SetFd.elt universe) u123);

  (* Cardinality constraints: each group has exactly 2 elements *)
  let c1 = Conjunto.cardinal g1 in
  let c2 = Conjunto.cardinal g2 in
  let c3 = Conjunto.cardinal g3 in
  Cstr.post (fd2e c1 =~ i2e 2);
  Cstr.post (fd2e c2 =~ i2e 2);
  Cstr.post (fd2e c3 =~ i2e 2);

  (* Item 1 must be in group 1 (Conjunto.mem) *)
  let item1 = Fd.create (Domain.interval 1 6) in
  Fd.unify item1 1;
  Cstr.post (Conjunto.mem item1 g1);

  (* Item 6 must NOT be in group 1 (Conjunto.outside) *)
  Conjunto.outside 6 g1;

  (* Symmetry breaking: order g2 < g3 (Conjunto.inf_min) *)
  Cstr.post (Conjunto.inf_min g2 g3);

  (* Subset: create a set 's' that must be a subset of g1 *)
  let s = Var.SetFd.create (SetDomain.interval empty universe) in
  Cstr.post (Conjunto.subset s g1);
  let cs = Conjunto.cardinal s in
  Cstr.post (fd2e cs =~ i2e 1); (* s has exactly 1 element *)

  (* Intersection: g1 ∩ g2 = ∅ (already enforced by disjoint, but test inter) *)
  let g1g2 = Conjunto.inter g1 g2 in

  (* Smallest element of g1 *)
  let sm = Conjunto.smallest g1 in

  (* sum_weight on g3: assign weights, constrain total *)
  let total = Conjunto.sum_weight g3 [(1, 10); (2, 20); (3, 30); (4, 40); (5, 50); (6, 60)] in
  (* g3 has 2 elements from {1..6}, so total ranges from 30 to 110 *)
  Cstr.post (fd2e total >=~ i2e 70); (* force g3 to contain higher values *)

  let goal =
    Goals.Conjunto.indomain g1
    &&~ Goals.Conjunto.indomain g2
    &&~ Goals.Conjunto.indomain g3
    &&~ Goals.Conjunto.indomain s
    &&~ Goals.Conjunto.indomain g1g2 in

  if Goals.solve goal then begin
    let v1 = Var.SetFd.elt_value g1 in
    let v2 = Var.SetFd.elt_value g2 in
    let v3 = Var.SetFd.elt_value g3 in
    let vs = Var.SetFd.elt_value s in
    let v12 = Var.SetFd.elt_value g1g2 in
    let vsm = Fd.int_value sm in
    let vtotal = Fd.int_value total in

    Printf.printf "Partition into groups:\n";
    Printf.printf "  G1: {"; SetDomain.S.iter (fun x -> Printf.printf "%d " x) v1; Printf.printf "}\n";
    Printf.printf "  G2: {"; SetDomain.S.iter (fun x -> Printf.printf "%d " x) v2; Printf.printf "}\n";
    Printf.printf "  G3: {"; SetDomain.S.iter (fun x -> Printf.printf "%d " x) v3; Printf.printf "}\n";
    Printf.printf "  S (subset of G1): {"; SetDomain.S.iter (fun x -> Printf.printf "%d " x) vs; Printf.printf "}\n";
    Printf.printf "  G1∩G2: {"; SetDomain.S.iter (fun x -> Printf.printf "%d " x) v12; Printf.printf "}\n";
    Printf.printf "  smallest(G1): %d\n" vsm;
    Printf.printf "  sum_weight(G3): %d\n" vtotal;

    (* Verify: each group has 2 elements *)
    assert (SetDomain.S.cardinal v1 = 2
            || (Printf.eprintf "FAILED: |G1| = %d, expected 2\n" (SetDomain.S.cardinal v1); false));
    assert (SetDomain.S.cardinal v2 = 2
            || (Printf.eprintf "FAILED: |G2| = %d\n" (SetDomain.S.cardinal v2); false));
    assert (SetDomain.S.cardinal v3 = 2
            || (Printf.eprintf "FAILED: |G3| = %d\n" (SetDomain.S.cardinal v3); false));

    (* Verify: groups are pairwise disjoint *)
    assert (SetDomain.S.cardinal (SetDomain.S.inter v1 v2) = 0
            || (Printf.eprintf "FAILED: G1 and G2 not disjoint\n"; false));
    assert (SetDomain.S.cardinal (SetDomain.S.inter v1 v3) = 0
            || (Printf.eprintf "FAILED: G1 and G3 not disjoint\n"; false));
    assert (SetDomain.S.cardinal (SetDomain.S.inter v2 v3) = 0
            || (Printf.eprintf "FAILED: G2 and G3 not disjoint\n"; false));

    (* Verify: union = universe *)
    let u = SetDomain.S.union (SetDomain.S.union v1 v2) v3 in
    assert (SetDomain.S.equal u universe
            || (Printf.eprintf "FAILED: union != universe\n"; false));

    (* Verify: 1 is in G1 *)
    assert (SetDomain.S.mem 1 v1
            || (Printf.eprintf "FAILED: 1 not in G1\n"; false));

    (* Verify: 6 is not in G1 *)
    assert (not (SetDomain.S.mem 6 v1)
            || (Printf.eprintf "FAILED: 6 in G1\n"; false));

    (* Verify: s ⊆ g1 *)
    assert (SetDomain.S.subset vs v1
            || (Printf.eprintf "FAILED: S not subset of G1\n"; false));
    assert (SetDomain.S.cardinal vs = 1
            || (Printf.eprintf "FAILED: |S| = %d\n" (SetDomain.S.cardinal vs); false));

    (* Verify: g1 ∩ g2 = ∅ *)
    assert (SetDomain.S.is_empty v12
            || (Printf.eprintf "FAILED: G1∩G2 not empty\n"; false));

    (* Verify: smallest *)
    assert (vsm = SetDomain.S.min_elt v1
            || (Printf.eprintf "FAILED: smallest = %d, expected %d\n" vsm (SetDomain.S.min_elt v1); false));

    (* Verify: sum_weight *)
    let weights = [(1, 10); (2, 20); (3, 30); (4, 40); (5, 50); (6, 60)] in
    let computed_sum = List.fold_left
      (fun acc (v, w) -> if SetDomain.S.mem v v3 then acc + w else acc)
      0 weights in
    assert (computed_sum = vtotal
            || (Printf.eprintf "FAILED: sum_weight = %d, computed = %d\n" vtotal computed_sum; false));
    assert (vtotal >= 70
            || (Printf.eprintf "FAILED: total = %d < 70\n" vtotal; false));

    Printf.printf "Conjunto test: PASSED\n"
  end else begin
    prerr_endline "No solution"; exit 1
  end
