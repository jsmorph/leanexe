import Project.LebU32.Storage
import Project.LebU32.Frames

namespace Project.LebU32.Spec
open Wasm Project.Common Project.ProofKit Project.EulerRiemann.Execution

structure FinishedStorage (seed : Heap) (initial current : Store Unit) (count : Nat)
    (bytes : ByteArray) : Prop where
  heap : (finishedHeap seed count).At current
  size : bytes.size = count
  owner : (finishedHeap seed count).OwnsPacked current (byteNode seed (count - 1)) bytes
  pages : current.mem.pages = initial.mem.pages
  cap : ∀ module_ index, current.memoryCap module_ index = initial.memoryCap module_ index
  low : ∀ address, address < seed.top.toNat → current.mem.bytes address = initial.mem.bytes address

theorem PushedStorage.finished {seed : Heap} {initial current : Store Unit} {count : Nat}
    {bytes : ByteArray} {value : UInt64} (h : PushedStorage seed initial current count bytes value) :
    FinishedStorage seed initial current (count + 1) (bytes.push value.toUInt8) := by
  exact ⟨h.heap, by rw [ByteArray.size_push, h.size], by simpa using h.output, h.pages, h.cap, h.low⟩

structure RunningFacts (seed : Heap) (initial : Store Unit) (input : UInt64)
    (current : Store Unit) (frame : Locals) (count : Nat) (value : UInt64) (bytes : ByteArray) : Prop where
  split : lebList 10 input = bytes.data.toList ++ lebList (10 - count) value
  bound : count < (lebList 10 input).length
  frame : RunningFrame frame (UInt64.ofNat (10 - count)) value (bytePointer seed count) (UInt64.ofNat count)
  storage : RunningStorage seed initial current count bytes

def RunningState (seed : Heap) (initial : Store Unit) (input : UInt64) : AssertionF Unit :=
  fun current frame => ∃ count value bytes, RunningFacts seed initial input current frame count value bytes

def FinishedState (seed : Heap) (initial : Store Unit) (input : UInt64) : AssertionF Unit :=
  fun current frame => ∃ bytes,
    bytes.data.toList = lebList 10 input ∧
    FinishedFrame frame (UInt64.ofNat (11 - (lebList 10 input).length))
      (bytePointer seed (lebList 10 input).length) (UInt64.ofNat (lebList 10 input).length) ∧
    FinishedStorage seed initial current (lebList 10 input).length bytes

def encodingInvariant (seed : Heap) (initial : Store Unit) (input : UInt64) : AssertionF Unit :=
  fun current frame => RunningState seed initial input current frame ∨ FinishedState seed initial input current frame

def encodingMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match (frame.params[0]? : Option Value), (frame.locals[4]? : Option Value) with
  | some (.i64 fuel), some (.i64 done) => 2 * fuel.toNat + if done = 0 then 1 else 0
  | _, _ => 0

theorem measure_running (current : Store Unit) (frame : Locals) (count : Nat)
    (value pointer : UInt64)
    (hFrame : RunningFrame frame (UInt64.ofNat (10 - count)) value pointer (UInt64.ofNat count)) :
    encodingMeasure current frame = 2 * (10 - count) + 1 := by
  simp only [encodingMeasure, hFrame.params, List.getElem?_cons_zero, hFrame.done, ite_true]
  rw [UInt64.toNat_ofNat_of_lt' (by change 10 - count < 18446744073709551616; omega)]

theorem measure_finished (current : Store Unit) (frame : Locals) (count : Nat)
    (pointer : UInt64)
    (hFrame : FinishedFrame frame (UInt64.ofNat (11 - count)) pointer (UInt64.ofNat count)) :
    encodingMeasure current frame = 2 * (11 - count) := by
  simp only [encodingMeasure, hFrame.fuel, hFrame.done, show ¬(1 : UInt64) = 0 by decide, ite_false, Nat.add_zero]
  rw [UInt64.toNat_ofNat_of_lt' (by change 11 - count < 18446744073709551616; omega)]

theorem encoded_length_bound (input : UInt64) (hInput : input.toNat < 4294967296) :
    (lebList 10 input).length ≤ 5 :=
  lebList_length_of_lt 10 5 input (by decide) (by norm_num; omega) (by decide) (by decide)

#print axioms measure_running
#print axioms measure_finished
end Project.LebU32.Spec
