import Project.Drone.ExecutionComputeFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 400000 in
theorem compute_guard_spec (env : HostEnv Unit) (store : Store Unit) (terrain : UInt64)
    (aux : List Value) (s : Scratch) (input : Array UInt64) (hAux : aux.length = 30)
    (hInput : UInt64Array.At store terrain input) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      { computeFrame terrain aux { s with counter := terrain } with
        values := [.i32 (if input.size = 0 ∨ 64 < input.size then 1 else 0)] } env) :
    wp Project.Drone.«module» (func25.take 19 ++ rest) Q store (computeFrame terrain aux s) env := by
  have hRead := hInput.lengthRead
  have hAddress := hInput.pointerAddress_eq
  have hBound := Nat.not_lt.mpr hInput.lengthBound
  have hZero : UInt64.ofNat input.size = 0 ↔ input.size = 0 := by
    constructor
    · intro h
      have hn := congrArg UInt64.toNat h
      simpa only [UInt64.toNat_ofNat_of_lt' hInput.size_lt, UInt64.toNat_zero] using hn
    · rintro h; rw [h]; rfl
  have hLarge : (64 : UInt64) < UInt64.ofNat input.size ↔ 64 < input.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hInput.size_lt]
    rfl
  simp only [func25, List.take, List.cons_append, List.nil_append]
  by_cases hz : input.size = 0 <;> by_cases hl : 64 < input.size
  all_goals
    compute_controls [hAux, hRead, hAddress, hBound, Nat.reducePow, UInt32.toNat_zero, UInt32.add_zero,
      Nat.add_zero, hZero, hLarge, hz, hl, Nat.not_lt.mpr hInput.generatedLengthBound]
    simpa [computeFrame, frame, Scratch.words, hZero, hLarge, hz, hl] using hNext

#print axioms compute_guard_spec
end Project.Drone.Execution
