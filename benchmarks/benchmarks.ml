(* Hakank-style Combinatorial Constraint Programming Benchmarks for OCaml Facile
 *
 * Based on problems from https://github.com/hakank/hakank
 * Hakan Kjellerstrand's collection of 4,741 models across 33+ solvers.
 *
 * Run in native mode for accurate timing:
 *   cd /home/mattias/data11/fs/facile
 *   dune exec benchmarks/benchmarks.exe
 *
 * Individual benchmark:
 *   dune exec benchmarks/benchmarks.exe -- costas
 *)

let () =
  let iterations = 3 in

  let run_benchmark name f =
    Gc.compact ();
    let t0 = Unix.gettimeofday () in
    f ();
    let t1 = Unix.gettimeofday () in
    let ms = (t1 -. t0) *. 1000.0 in
    Printf.printf "  %-25s %10.3f ms\n%!" name ms;
    ms
  in

  let selected =
    if Array.length Sys.argv > 1 then
      Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1))
    else
      []
  in
  let should_run name =
    selected = [] || List.mem name selected
  in

  let benchmarks = [
    "all-interval", "All-Interval Series",    All_interval.run;
    "langford",     "Langford's Problem",     Langford.run;
    "magic-square", "Magic Squares",          Magic_square.run;
    "costas",       "Costas Arrays",          Costas_array.run;
    "tomography",   "Discrete Tomography",    Discrete_tomography.run;
    "quasigroup",   "Quasigroup Completion",  Quasigroup_completion.run;
    "subset-sum",   "Subset Sum",             Subset_sum.run;
    "debruijn",     "De Bruijn Sequences",    Debruijn.run;
    "nqueens",      "N-Queens (scaling)",     Nqueens.run;
    "golomb",       "Golomb Rulers",          Golomb_ruler.run;
    "nonogram",     "Nonograms",              Nonogram.run;
    "cumulative",   "Cumulative Scheduling",  Cumulative_scheduling.run;
    "rack",         "Rack Configuration",     Rack.run;
    "equations",    "Equation Solving",       Equation_solving.run;
    "mortgage",     "Mortgage Calculator",    Mortgage.run;
  ] in

  let active =
    List.filter (fun (key, _, _) -> should_run key) benchmarks
  in

  Printf.printf "OCaml Facile Hakank Benchmarks\n";
  Printf.printf "==============================\n";
  Printf.printf "Iterations: %d\n\n%!" iterations;

  let loop_totals = Array.make iterations 0.0 in
  for i = 0 to iterations - 1 do
    Printf.printf "=== Iteration %d/%d ===\n%!" (i + 1) iterations;
    let total =
      List.fold_left
        (fun acc (_, name, f) -> acc +. run_benchmark name f)
        0.0 active
    in
    loop_totals.(i) <- total;
    Printf.printf "--- Iteration %d total: %.3f ms ---\n\n%!" (i + 1) total
  done;

  Printf.printf "=== SUMMARY ===\n";
  Array.iteri (fun i t ->
    Printf.printf "  Iteration %d: %.3f ms\n" (i + 1) t) loop_totals;
  Printf.printf "  Best:        %.3f ms\n"
    (Array.fold_left min max_float loop_totals);
  Printf.printf "=== ALL BENCHMARKS COMPLETE ===\n%!"
