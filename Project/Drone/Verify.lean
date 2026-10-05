import Project.Drone.Kernels
import Project.Encoding.RoundTrip

/-! The encoded bytes of the drone module decode to a module whose compiled functions compute
their Lean definitions. -/

namespace Project.Drone

open Wasm Project.Pipeline Project.IR LeanExe.Examples.Drone

/-- `encode` succeeds on `drone.module`, and its bytes decode to `drone.module`. -/
theorem drone_round_trip : ∃ bytes, Wasm.Encoding.encode drone.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok drone.module :=
  Wasm.Encoding.round_trip drone.module (by decide +kernel) (by decide +kernel)

/-- `encode` succeeds on `drone.module`, and its bytes decode to a module whose scalar
functions compute their Lean definitions exactly. -/
theorem drone_bytes : ∃ bytes, Wasm.Encoding.encode drone.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      ImplementsPure m 2 distanceTuple ∧ ImplementsPure m 3 altitudeTuple ∧
      ImplementsPure m 4 speed ∧ ImplementsPure m 5 ceilSqrt ∧
      ImplementsPure m 6 restSeconds ∧ ImplementsPure m 7 edgeTicksTuple := by
  obtain ⟨bytes, success, decoded⟩ := drone_round_trip
  exact ⟨bytes, success, drone.module, decoded, distance_implements, altitude_implements,
    speed_implements, ceilSqrt_implements, restSeconds_implements, edgeTicks_implements⟩

end Project.Drone
