import Project.Drone.ExecutionRead
import Project.ProofKit.CheckedNatMul

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

def predecessorReadFrame (r0 r1 owner pointer : UInt64) (target source : Nat)
    (previous : Array UInt64) (hi : 3*source < previous.size) : Locals :=
  { params := [.i64 r0, .i64 r1, .i64 owner, .i64 pointer,
      .i64 (UInt64.ofNat target), .i64 (UInt64.ofNat source)],
    locals := List.replicate 26 (.i64 0) ++
      [.i64 pointer, .i64 (UInt64.ofNat (3*source)), .i64 3,
        .i64 (UInt64.ofNat source), .i64 0, .i64 0, .i64 0],
    values := [.i64 previous[3*source]] }

/-- The first packed-row load in the emitted predecessor function. -/
theorem predecessor_readTime (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 owner pointer : UInt64) (target source : Nat) (previous : Array UInt64)
    (ha : UInt64Array.At initial pointer previous) (hi : 3*source < previous.size)
    (Q : Assertion Unit)
    (hNext : wp «module» (func13.drop 17) Q initial
      (predecessorReadFrame r0 r1 owner pointer target source previous hi) env) :
    wp «module» func13 Q initial
      { params := [.i64 r0, .i64 r1, .i64 owner, .i64 pointer,
          .i64 (UInt64.ofNat target), .i64 (UInt64.ofNat source)],
        locals := List.replicate 33 (.i64 0) } env := by
  have hSource : source < UInt64.size := by have := ha.size_lt; omega
  have hProduct : 3*source < UInt64.size := lt_trans hi ha.size_lt
  unfold func13
  simp only [List.replicate]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  change wp «module» (CheckedNatMul.program 34 35 ++ _) Q initial _ env
  refine CheckedNatMul.program_spec 34 35 _ _ _ _ 3 (UInt64.ofNat source) []
    rfl rfl rfl ?_ _ _ ?_
  · simpa only [UInt64.toNat_ofNat_of_lt' hSource,
      show (3 : UInt64).toNat = 3 from rfl] using hProduct
  wp_fixed_frame_step
  change wp «module» (CheckedArrayGet.checkedGetCore 32 33 ++ _) Q initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 32 33 _ _ _ _ pointer previous (3*source) []
    rfl ?_ rfl ha hi _ _ ?_
  · simp [Locals.get, UInt64.ofNat_mul]
  simpa only [predecessorReadFrame, UInt64.ofNat_mul,
    show UInt64.ofNat 3 = 3 from rfl, List.replicate, List.cons_append,
    List.nil_append, func13, List.drop] using hNext

#print axioms predecessor_readTime
end Project.Drone.Execution
