import Project.LebU32.RecyclingPositive
import Project.LebU32.RecyclingNegative
import Project.LebU32.RecyclingDispatch
import Project.LebU32.RecyclingPure

namespace Project.LebU32.Recycling
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution Spec

def loopInvariant (initial : Store Unit) (base : UInt64) (target : List UInt8) : AssertionF Unit :=
  fun store frame => ∃ heap node bytes,
    Arena initial base bytes.size heap store ∧ Buffer base heap store node bytes ∧
    ((∃ fuel v, 0 < fuel ∧ bytes.size + fuel = 10 ∧
      target = bytes.data.toList ++ lebList fuel v ∧ Running frame (UInt64.ofNat fuel) v node.root bytes.size) ∨
     (∃ fuel, target = bytes.data.toList ∧ Finished frame fuel node.root bytes.size))

def measure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 9, frame.get 0 with
  | some (.i64 done), some (.i64 fuel) => if done = 1 then 0 else fuel.toNat + 1
  | _, _ => 0

theorem measure_running (store : Store Unit) {frame : Locals} {fuel v root : UInt64} {size : Nat}
    (h : Running frame fuel v root size) : measure store frame = fuel.toNat + 1 := by
  unfold measure
  rw [h.done, h.fuel]
  simp

theorem measure_finished (store : Store Unit) {frame : Locals} {fuel root : UInt64} {size : Nat}
    (h : Finished frame fuel root size) : measure store frame = 0 := by
  unfold measure
  rw [h.done, h.fuel]
  simp

theorem running_size_bound {target : List UInt8} {bytes : ByteArray} {fuel : Nat} {v : UInt64}
    (hTarget : target.length ≤ 5) (hFuel : 0 < fuel)
    (hSplit : target = bytes.data.toList ++ lebList fuel v) : bytes.size < 5 := by
  have hLength := congrArg List.length hSplit
  have hPositive := lebList_length_pos fuel v hFuel
  simp only [List.length_append, Array.length_toList] at hLength
  change target.length = bytes.size + (lebList fuel v).length at hLength
  omega

#print axioms measure_running
#print axioms measure_finished
#print axioms running_size_bound
end Project.LebU32.Recycling
