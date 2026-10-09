import Verified.Reflect.Command
import Examples.Drone.Flat
import Examples.Drone.WholeFlight

/-! The thirty-first program of the verified compiler: the drone planner of
`Examples/Drone/Program.lean`, compiled unchanged.  The planner finds the flight of least duration
over up to 64 stations of terrain, with the altitude above the floors as the second criterion,
among 45 states per station, and returns the altitude and speed at each station.  The program
lists `floorAt` and `best`, which `LeanExe` inlines, as functions, and the reflector reflects the
named constants `stateCount`, `infinity`, and `unreachable` as their values.  `Choice` is
represented as its three words by the instance of `Examples/Drone/Flat.lean`.  The compiler's
theorem states that the module computes `compute`, or traps at `unreachable`, which it allows on
any input since an allocation traps when memory runs out.  With the planner's own theorems,
`compute_correct` and `compute_safe`, which concern the Lean definition, `drone_compute` and
`drone_safe` state that the module's results are optimal and safe flights. -/

namespace Verified.Examples.Drone

open _root_.Examples.Drone

verified_compile compiled := [distance, altitude, speed, floorAt, ceilSqrt, restSeconds,
  edgeTicks, choose, predecessor, best, advance, initial, validHeights, extend, forward, output,
  compute]

open _root_.Examples.Drone.Output _root_.Examples.Drone.Planner
  _root_.Examples.Drone.Forward in
/-- The bytes of `compiled.module` decode to the module, whose entry 18 computes `compute`: a call
with a terrain returns the words of `compute` or traps at `unreachable`.  For valid terrain those
words are an admitted flight from rest on the ground at the first station to rest on the ground at
the last, and no admitted flight costs less.  For empty or invalid terrain they are `#[]`. -/
theorem drone_compute : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA true compiled.module 18 compute (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) ∧
    (∀ terrain, terrainBound terrain → 0 < terrain.size →
      let r := floors terrain
      let stop := stops terrain.size.toUInt64
      let n := terrain.size - 1
      (compute terrain).size = 2 * terrain.size ∧
      Encoded r stop n 0 (rowCost (layers r stop n) 0) (compute terrain).toList ∧
      ∀ other, Flight r stop n 0 other → (rowCost (layers r stop n) 0).LE other) ∧
    (∀ terrain, terrain.size < 2 ^ 64 → ¬(terrainBound terrain ∧ 0 < terrain.size) →
      compute terrain = #[]) := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.compute.implements,
    fun terrain h hn => compute_correct terrain h hn,
    fun terrain hs h => compute_invalid terrain hs h⟩

open _root_.Examples.Drone.Output in
/-- The bytes of `compiled.module` decode to the module, whose entry 18 computes `compute`, and for
valid nonempty terrain the flight that `compute` returns is safe: the clearance, speed, and
acceleration limits hold throughout the point-mass trajectory that its words define. -/
theorem drone_safe : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA true compiled.module 18 compute (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) ∧
    ∀ terrain, terrainBound terrain → 0 < terrain.size → WholeFlight.Safe terrain := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.compute.implements,
    fun terrain h hn => WholeFlight.compute_safe terrain h hn⟩

end Verified.Examples.Drone
