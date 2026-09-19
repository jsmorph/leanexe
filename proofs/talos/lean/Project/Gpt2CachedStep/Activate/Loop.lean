import Project.Gpt2CachedStep.Gelu
import Project.ProofKit.PackedWordRead
import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.Activate
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def parameters (inputOwner inputPtr : UInt64) (input : ByteArray) : List Wasm.Value :=
  [.i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size)]

def loopBody : Wasm.Program :=
  match (func32[49]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def wordCode : Wasm.Program := (loopBody.drop 12).take 18

set_option maxRecDepth 32768 in
theorem emitted_loop : (func32.drop 49).take 1 = PackedGenerateLoop.program 4 15 16 wordCode := rfl

def State (params : List Wasm.Value) (input : ByteArray) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 20 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (4 * (input.size / 4)))) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem wordCode_spec (env : HostEnv Unit) (initial : Store Unit)
    (inputOwner inputPtr outputPtr : UInt64) (input : ByteArray) (index : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hIndex : index < input.size / 4)
    (hReady : PackedGenerateLoop.Ready 4 15 16 (input.size / 4) index outputPtr frame)
    (hState : State (parameters inputOwner inputPtr input) input frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 4 15 16 (input.size / 4) index outputPtr result →
      State (parameters inputOwner inputPtr input) input result →
      wp «module» rest Q initial { result with values :=
        [.i64 (gelu (word input index)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (wordCode ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[1]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[12]? = some (.i64 (UInt64.ofNat (4 * (input.size / 4)))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[13]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  simp only [wordCode, loopBody, func32, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
    inputOwner inputPtr input index hInput (by omega)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((Gelu.gelu_exact env final (word input index)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 4 15 16 (input.size / 4) index outputPtr result ∧
      State (parameters inputOwner inputPtr input) input result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (gelu (word input index)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [State, parameters, hLength, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem state_advance (params : List Wasm.Value) (input : ByteArray) (hParams : params.length = 3)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 4)
    (hState : State params input frame) :
    State params input (FixedArrayCopy.counterFrame frame 4 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [State, FixedArrayCopy.counterFrame, Locals.set, hFrameParams, hParams,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]

set_option maxRecDepth 32768 in
theorem loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (inputOwner inputPtr outputPtr : UInt64) (input : ByteArray) (frame : Locals)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hFit : outputPtr.toNat + 4 * (input.size / 4) ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * (input.size / 4) ≤ initial.mem.pages * 65536)
    (hSep : inputPtr.toNat + input.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 4 * (input.size / 4) ≤ inputPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 4 15 16 (input.size / 4) 0 outputPtr frame)
    (hState : State (parameters inputOwner inputPtr input) input frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 4 15 16 (input.size / 4) (input.size / 4) outputPtr result →
      State (parameters inputOwner inputPtr input) input result →
      ByteArrayAt final.mem outputPtr.toNat (activate input) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (input.size / 4)) →
      wp «module» rest Q final result env) :
    wp «module» ((func32.drop 49).take 1 ++ rest) Q initial frame env := by
  rw [emitted_loop]
  apply PackedGenerateLoop.program_spec (value := fun index => gelu (word input index))
    (P := State (parameters inputOwner inputPtr input) input)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact state_advance _ input rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact wordCode_spec env current inputOwner inputPtr outputPtr input index next (hInput.writesRange hWrites hSep)
      (by omega) hReady hState Q rest hNext
  · exact hDone

#print axioms wordCode_spec
#print axioms loop_spec

end Project.Gpt2CachedStep.Activate
