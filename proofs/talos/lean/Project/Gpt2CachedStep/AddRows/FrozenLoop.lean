import Project.Gpt2CachedStep.FrozenProgram
import Project.ProofKit.F32Add
import Project.ProofKit.PackedFloatFrame
import Project.ProofKit.PackedWordRead
import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.Frozen.AddRows
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def parameters (leftOwner rightOwner leftPtr rightPtr : UInt64) (left right : ByteArray) : List Wasm.Value :=
  [.i64 leftOwner, .i64 leftPtr, .i64 (UInt64.ofNat left.size),
    .i64 rightOwner, .i64 rightPtr, .i64 (UInt64.ofNat right.size)]

def loopBody : Wasm.Program :=
  match (func30[49]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def wordCode : Wasm.Program := (loopBody.drop 12).take 33

set_option maxRecDepth 32768 in
theorem emitted_loop : (func30.drop 49).take 1 = PackedGenerateLoop.program 7 20 21 wordCode := rfl

def State (params : List Wasm.Value) (left : ByteArray) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 22 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (4 * (left.size / 4)))) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem wordCode_spec (env : HostEnv Unit) (initial : Store Unit)
    (leftOwner rightOwner leftPtr rightPtr outputPtr : UInt64) (left right : ByteArray) (index : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem leftPtr.toNat left)
    (hRight : ByteArrayAt initial.mem rightPtr.toNat right)
    (hRightSize : 4 * (left.size / 4) ≤ right.size)
    (hIndex : index < left.size / 4)
    (hReady : PackedGenerateLoop.Ready 7 20 21 (left.size / 4) index outputPtr frame)
    (hState : State (parameters leftOwner rightOwner leftPtr rightPtr left right) left frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 7 20 21 (left.size / 4) index outputPtr result →
      State (parameters leftOwner rightOwner leftPtr rightPtr left right) left result →
      wp «module» rest Q initial { result with values :=
        [.i64 (LeanExe.Float32.addBits (word left index) (word right index)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (wordCode ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[1]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[14]? = some (.i64 (UInt64.ofNat (4 * (left.size / 4)))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[15]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  simp only [wordCode, loopBody, func30, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
    leftOwner leftPtr left index hInput (by omega)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env final
    rightOwner rightPtr right index hRight (by omega)).append_args
    rfl rfl rfl [.f32 (word left index), .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength, hCounter]
  simp only [F32Add.add_eq] at hNext
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 7 20 21 (left.size / 4) index outputPtr result ∧
      State (parameters leftOwner rightOwner leftPtr rightPtr left right) left result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (Wasm.IEEE32.add (word left index) (word right index)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [State, parameters, hLength, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem state_advance (params : List Wasm.Value) (left : ByteArray) (hParams : params.length = 6)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 7)
    (hState : State params left frame) :
    State params left (FixedArrayCopy.counterFrame frame 7 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [State, FixedArrayCopy.counterFrame, Locals.set, hFrameParams, hParams,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]

set_option maxRecDepth 32768 in
theorem loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (leftOwner rightOwner leftPtr rightPtr outputPtr : UInt64) (left right : ByteArray) (frame : Locals)
    (hInput : ByteArrayAt initial.mem leftPtr.toNat left)
    (hRight : ByteArrayAt initial.mem rightPtr.toNat right)
    (hRightSize : 4 * (left.size / 4) ≤ right.size)
    (hFit : outputPtr.toNat + 4 * (left.size / 4) ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * (left.size / 4) ≤ initial.mem.pages * 65536)
    (hSep : leftPtr.toNat + left.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 4 * (left.size / 4) ≤ leftPtr.toNat)
    (hRightSep : rightPtr.toNat + right.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (left.size / 4) ≤ rightPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 7 20 21 (left.size / 4) 0 outputPtr frame)
    (hState : State (parameters leftOwner rightOwner leftPtr rightPtr left right) left frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 7 20 21 (left.size / 4) (left.size / 4) outputPtr result →
      State (parameters leftOwner rightOwner leftPtr rightPtr left right) left result →
      ByteArrayAt final.mem outputPtr.toNat (addRows left right) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (left.size / 4)) →
      wp «module» rest Q final result env) :
    wp «module» ((func30.drop 49).take 1 ++ rest) Q initial frame env := by
  rw [emitted_loop]
  apply PackedGenerateLoop.program_spec (value := fun index => LeanExe.Float32.addBits (word left index) (word right index))
    (P := State (parameters leftOwner rightOwner leftPtr rightPtr left right) left)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact state_advance _ left rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact wordCode_spec env current leftOwner rightOwner leftPtr rightPtr outputPtr left right index next
      (hInput.writesRange hWrites hSep) (hRight.writesRange hWrites hRightSep) hRightSize (by omega) hReady hState Q rest hNext
  · exact hDone

#print axioms wordCode_spec
#print axioms loop_spec

end Project.Gpt2CachedStep.Frozen.AddRows
