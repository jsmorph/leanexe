import Project.Drone.Finish
import Project.Encoding.RoundTrip

/-! The encoded bytes of the drone module decode to a module whose compiled functions compute
their Lean definitions. -/

namespace Project.Drone

open Wasm Project.Pipeline Project.IR LeanExe.Examples.Drone

/-- `encode` succeeds on `drone.module`, and its bytes decode to `drone.module`. -/
theorem drone_round_trip : ∃ bytes, Wasm.Encoding.encode drone.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok drone.module :=
  Wasm.Encoding.round_trip drone.module (by decide +kernel) (by decide +kernel)

/-- `encode` succeeds on `drone.module`, and its bytes decode to a module whose every compiled
function computes its Lean definition exactly. -/
theorem drone_bytes : ∃ bytes, Wasm.Encoding.encode drone.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      ImplementsPure m 2 distanceTuple ∧ ImplementsPure m 3 altitudeTuple ∧
      ImplementsPure m 4 speed ∧ ImplementsPure m 5 ceilSqrt ∧
      ImplementsPure m 6 restSeconds ∧ ImplementsPure m 7 edgeTicksTuple ∧
      ImplementsPure m 8 chooseTuple ∧ ImplementsPure m 9 predecessorTuple ∧
      Implements m 10 advanceTuple ∧ Implements m 11 initialUnit ∧
      Implements m 12 validHeights ∧ Implements m 13 extendTuple ∧
      Implements m 14 forwardTuple ∧ Implements m 15 outputTuple ∧ Implements m 16 compute := by
  obtain ⟨bytes, success, decoded⟩ := drone_round_trip
  exact ⟨bytes, success, drone.module, decoded, distance_implements, altitude_implements,
    speed_implements, ceilSqrt_implements, restSeconds_implements, edgeTicks_implements,
    choose_implements, predecessor_implements, advance_implements, initial_implements,
    validHeights_implements, extend_implements, forward_implements, output_implements,
    compute_implements⟩

open Output Planner Forward in
/-- The bytes of `drone.module` decode to a module whose entry 16 computes `compute`: a call
with a terrain returns the words of `compute` or aborts at `unreachable`.  For valid terrain
those words are an admitted flight from rest on the ground at the first station to rest on the
ground at the last, and no admitted flight costs less; for empty or invalid terrain they are
`#[]`. -/
theorem drone_compute : ∃ bytes, Wasm.Encoding.encode drone.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 16 compute ∧
      (∀ terrain, terrainBound terrain → 0 < terrain.size →
        let r := floors terrain
        let stop := stops terrain.size.toUInt64
        let n := terrain.size - 1
        (compute terrain).size = 2 * terrain.size ∧
        Encoded r stop n 0 (rowCost (layers r stop n) 0) (compute terrain).toList ∧
        ∀ other, Flight r stop n 0 other → (rowCost (layers r stop n) 0).LE other) ∧
      (∀ terrain, terrain.size < 2 ^ 64 → ¬(terrainBound terrain ∧ 0 < terrain.size) →
        compute terrain = #[]) := by
  obtain ⟨bytes, success, decoded⟩ := drone_round_trip
  exact ⟨bytes, success, drone.module, decoded, compute_implements,
    fun terrain h hn => compute_correct terrain h hn,
    fun terrain hs h => compute_invalid terrain hs h⟩

end Project.Drone
