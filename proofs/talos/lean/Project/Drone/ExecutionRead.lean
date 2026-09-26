import Project.Drone.ExecutionScalar
import Project.ProofKit.CheckedArrayGet
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

theorem floorAt_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (terrain : Array UInt64) (i : Nat)
    (ha : UInt64Array.At initial pointer terrain) (hi : i < terrain.size) :
    TerminatesWith env «module» 20 initial [.i64 (UInt64.ofNat i), .i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (floorAt terrain i)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func20Def) rfl ?_
  change wp «module» func20 _ initial
    { params := [.i64 owner, .i64 pointer, .i64 (UInt64.ofNat i)],
      locals := List.replicate 4 (.i64 0) } env
  unfold func20
  simp only [List.replicate]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  change wp «module» (CheckedArrayGet.checkedGetCore 4 5 ++ _) _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 4 5 _ _ _ _ pointer terrain i []
    rfl rfl rfl ha hi _ _ ?_
  simp only [floorAt, getElem!_pos terrain i hi]
  have hfit : i+1 < UInt64.size := by have := ha.size_lt; omega
  have hi64 : i < UInt64.size := by omega
  have hAdd : ¬ UInt64.ofNat i + 1 < UInt64.ofNat i :=
    CheckedNatAdd.guard_of_fits i 1 hfit
  have hZero : UInt64.ofNat i = 0 ↔ i = 0 := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      simpa only [UInt64.toNat_ofNat_of_lt' hi64, UInt64.toNat_zero] using this
    · rintro rfl; rfl
  have hLast : UInt64.ofNat i + 1 = UInt64.ofNat terrain.size ↔ i+1 = terrain.size := by
    change UInt64.ofNat i + UInt64.ofNat 1 = UInt64.ofNat terrain.size ↔ _
    rw [← UInt64.ofNat_add, eq_comm, ha.encodedSize_eq hfit, eq_comm]
  have hLength := ha.lengthRead
  have hLengthBound := ha.generatedLengthBound
  have hAddress := ha.pointerAddress_eq
  have hLengthRead : initial.mem.read64 (UInt32.ofNat (pointer.toNat % 4294967296)) =
      UInt64.ofNat terrain.size := by
    rw [hAddress]
    exact hLength
  by_cases hz : i = 0 <;> by_cases hl : i+1 = terrain.size
  all_goals
    repeat' ((try wp_fixed_frame [func20Def, hZero, hLast, hz, hl, hAdd,
        hLengthRead, hLength, hLengthBound, hAddress]) <;>
      (refine wp_iff_cons rfl ?_;
        simp [hZero, hLast, hz, hl, hAdd, hLengthRead, hLength, hLengthBound, hAddress]))

#print axioms floorAt_exact
end Project.Drone.Execution
