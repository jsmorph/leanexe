import Project.ProofKit.PackedAllocationFrame
import Project.ProofKit.LocalPrefix
import Project.ProofKit.FixedArrayCapacity

namespace Project.ProofKit.PackedAllocation
open Wasm

theorem allocatedFrame_length (frame : Locals) (start : Nat)
    (need previous current capacity next result : UInt64)
    (hLower : frame.params.length ≤ start) (hBound : start + 6 ≤ frame.params.length + frame.locals.length) :
    (allocatedFrame frame start need previous current capacity next result).locals.length = frame.locals.length := by
  simp only [allocatedFrame, FixedArraySearch.frame, List.length_append, List.length_take,
    List.length_cons, List.length_nil, List.length_drop]
  omega

theorem allocatedFrame_prefix (frame : Locals) (start : Nat)
    (need previous current capacity next result : UInt64)
    (hBound : start - frame.params.length ≤ frame.locals.length) :
    (allocatedFrame frame start need previous current capacity next result).locals.take (start - frame.params.length) =
      frame.locals.take (start - frame.params.length) := by
  exact List.take_left' (by simp only [List.length_take, Nat.min_eq_left hBound])

theorem allocatedFrame_get_before (frame : Locals) (start : Nat)
    (need previous current capacity next result : UInt64)
    (hLower : frame.params.length ≤ start) (hBound : start + 6 ≤ frame.params.length + frame.locals.length)
    (index : Nat) (hIndex : index < start) :
    (allocatedFrame frame start need previous current capacity next result).get index = frame.get index := by
  apply Frame.get_of_take_eq (before := frame)
    (after := allocatedFrame frame start need previous current capacity next result)
    rfl (allocatedFrame_prefix frame start need previous current capacity next result (by omega))
  · omega
  · rw [allocatedFrame_length frame start need previous current capacity next result hLower hBound]
    omega
  · omega

theorem allocatedFrame_get_field (frame : Locals) (start : Nat)
    (need previous current capacity next result : UInt64)
    (hLower : frame.params.length ≤ start) (hBound : start + 6 ≤ frame.params.length + frame.locals.length)
    (field : Nat) (hField : field < 6) :
    (allocatedFrame frame start need previous current capacity next result).get (start + field) =
      [.i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result][field]? := by
  have hLength : (frame.locals.take (start - frame.params.length)).length = start - frame.params.length := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  simpa only [allocatedFrame, hLength, Nat.add_sub_of_le hLower] using FixedArraySearch.frame_get frame.params
    (frame.locals.take (start - frame.params.length)) (frame.locals.drop (start - frame.params.length + 6))
    need previous current capacity next result field hField

#print axioms allocatedFrame_get_before
#print axioms allocatedFrame_get_field

end Project.ProofKit.PackedAllocation

namespace Project.ProofKit.FixedArrayCapacity
open Wasm

theorem capacityFrame_prefix (frame : Locals) (slot : Nat) (word : UInt64) (count : Nat)
    (hCount : count ≤ slot - frame.params.length) :
    (capacityFrame frame slot word).locals.take count = frame.locals.take count :=
  List.take_set_of_le hCount

theorem capacityFrame_get_before (frame : Locals) (slot : Nat) (word : UInt64)
    (hLower : frame.params.length ≤ slot) (hBound : frame.validIndex slot)
    (index : Nat) (hIndex : index < slot) :
    (capacityFrame frame slot word).get index = frame.get index := by
  have hValid : slot < frame.params.length + frame.locals.length := hBound
  apply Frame.get_of_take_eq (before := frame) (after := capacityFrame frame slot word)
    rfl (capacityFrame_prefix frame slot word (slot - frame.params.length) (Nat.le_refl _))
  · omega
  · rw [capacityFrame_locals_length]; omega
  · omega

theorem capacityFrame_typed (frame : Locals) (slot : Nat) (word : UInt64)
    (h : I64Values frame.locals) : I64Values (capacityFrame frame slot word).locals := h.set _ _

theorem storeWord_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (slot : Nat) (word : UInt64)
    (hLower : frame.params.length ≤ slot) (hBound : frame.validIndex slot)
    (hValues : frame.values = [.i64 word]) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (capacityFrame frame slot word) env) :
    wp module_ (.localSet slot :: rest) Q store frame env := by
  have hValid : slot < frame.params.length + frame.locals.length := hBound
  simpa only [wp_localSet_cons, hValues, Locals.set?, Nat.not_lt.mpr hLower,
    hValid, ite_false, ite_true, capacityFrame] using hNext

#print axioms capacityFrame_get_before
#print axioms storeWord_spec

end Project.ProofKit.FixedArrayCapacity
