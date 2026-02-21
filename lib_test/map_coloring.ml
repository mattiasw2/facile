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
    Array.iteri (fun i r ->
      Printf.printf "  %3s = %s\n" names.(i) colors.(Fd.int_value r)) regions
  end else
    prerr_endline "No solution"
