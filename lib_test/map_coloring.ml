(* Map Coloring - Australia
   Color the map of Australia with 3 colors such that no two
   adjacent regions share the same color.
   Regions: WA, NT, SA, Q, NSW, V, T *)

open Facile
open Easy

let () =
  (* 3 colors: 0=Red, 1=Green, 2=Blue *)
  let wa  = Fd.interval 0 2
  and nt  = Fd.interval 0 2
  and sa  = Fd.interval 0 2
  and q   = Fd.interval 0 2
  and nsw = Fd.interval 0 2
  and v   = Fd.interval 0 2
  and t   = Fd.interval 0 2 in

  (* Adjacent regions must have different colors *)
  let diff a b = Cstr.post (fd2e a <>~ fd2e b) in
  diff wa nt;  diff wa sa;
  diff nt sa;  diff nt q;
  diff sa q;   diff sa nsw;  diff sa v;
  diff q nsw;
  diff nsw v;

  let regions = [| wa; nt; sa; q; nsw; v; t |] in
  let names   = [| "WA"; "NT"; "SA"; "Q"; "NSW"; "V"; "T" |] in
  let colors  = [| "Red"; "Green"; "Blue" |] in

  if Goals.solve (Goals.Array.labeling regions) then begin
    Printf.printf "Map coloring solution:\n";
    let vals = Array.map Fd.int_value regions in
    Array.iteri (fun i c ->
      Printf.printf "  %3s = %s\n" names.(i) colors.(c)) vals;
    (* Verify: adjacent regions have different colors *)
    let adjacencies = [| (0,1); (0,2); (1,2); (1,3); (2,3); (2,4); (2,5); (3,4); (4,5) |] in
    Array.iter (fun (i, j) ->
      assert (vals.(i) <> vals.(j)
              || (Printf.eprintf "FAILED: %s = %s\n" names.(i) names.(j); false)))
      adjacencies;
    (* Verify: all values in {0,1,2} *)
    Array.iteri (fun i c ->
      assert (c >= 0 && c <= 2
              || (Printf.eprintf "FAILED: %s out of range\n" names.(i); false))) vals;
    Printf.printf "Map coloring: PASSED\n"
  end else begin
    prerr_endline "No solution"; exit 1
  end
