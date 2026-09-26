import Project.Drone.ExecutionScan

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

theorem bestPredecessor_exact (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target count : Nat) (previous : Array UInt64)
    (ha : UInt64Array.At initial pointer previous)
    (hRange : 3*count ≤ previous.size) (ht : target < UInt64.size) :
    TerminatesWith env «module» 15 initial
      [.i64 (UInt64.ofNat target), .i64 pointer, .i64 owner, .i64 r1,
        .i64 r0, .i64 (UInt64.ofNat count)]
      (fun final values => final = initial ∧
        values = choiceValues (bestPredecessor count r0 r1 previous target)) := by
  refine TerminatesWith.of_wp_entry_for (f := func15Def) rfl ?_
  change wp «module» func15 _ initial
    { params := [.i64 (UInt64.ofNat count), .i64 r0, .i64 r1, .i64 owner,
        .i64 pointer, .i64 (UInt64.ofNat target)],
      locals := List.replicate 19 (.i64 0) } env
  simp only [func15]
  wp_fixed_frame
  refine wp_call_tw (unreachable_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func12Def, choiceValues]
  refine wp_call_tw (scanPredecessors_exact env initial r0 r1 owner pointer
    target count 0 previous unreachable ha (by simpa using hRange) ht) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_fixed_frame [func14Def, func15Def, choiceValues]
  simp [bestPredecessor, choiceValues]

#print axioms bestPredecessor_exact
end Project.Drone.Execution
