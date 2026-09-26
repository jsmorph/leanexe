import Project.Gpt2QuantizedLinearRows.RowScale
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def parameters (owner ptr : UInt64) (input : ByteArray) (width rows : Nat) : List Wasm.Value :=
  [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat width), .i64 (UInt64.ofNat rows)]

def scaleBody : Wasm.Program :=
  match (func3[42]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def scaleWord : Wasm.Program := (scaleBody.drop 12).take (scaleBody.length - 19)

theorem emitted_scales : (func3.drop 42).take 1 = PackedGenerateLoop.program 6 40 41 scaleWord := rfl

def ScaleState (params : List Wasm.Value) (rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 43 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧ I64Values frame.locals

set_option maxRecDepth 16384 in
theorem scaleWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr outputPtr : UInt64) (input : ByteArray) (width rows index : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem ptr.toNat input)
    (hRow : (index * width + width) * 4 ≤ input.size)
    (hReady : PackedGenerateLoop.Ready 6 40 41 rows index outputPtr frame)
    (hState : ScaleState (parameters owner ptr input width rows) rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 6 40 41 rows index outputPtr result →
      ScaleState (parameters owner ptr input width rows) rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (rowScale input (index * width) width).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (scaleWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[1]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[35]? = some (.i64 (UInt64.ofNat (4 * rows))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[36]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hFit : (UInt64.ofNat index).toNat * (UInt64.ofNat width).toNat < UInt64.size := by
    apply lt_of_le_of_lt (Nat.mul_le_mul (Nat.mod_le ..) (Nat.mod_le ..))
    have := hInput.1
    change index * width < 18446744073709551616
    omega
  simp only [scaleWord, scaleBody, func3, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  apply CheckedNatMul.guard_spec 42 43 «module» env initial _
    (UInt64.ofNat index) (UInt64.ofNat width) [.i32 (PackedGenerateLoop.address outputPtr index)]
  · rfl
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength]
  · exact hFit
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_mul]
  refine wp_call_tw ((rowScale_exact env initial owner ptr input (index * width) width hInput hRow).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 6 40 41 rows index outputPtr result ∧
      ScaleState (parameters owner ptr input width rows) rows result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (rowScale input (index * width) width).toUInt64,
      .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [ScaleState, parameters, hLength,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte, hBytes,
        I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem scaleState_advance (params : List Wasm.Value) (rows : Nat) (hParams : params.length = 5)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 6)
    (hState : ScaleState params rows frame) :
    ScaleState params rows (FixedArrayCopy.counterFrame frame 6 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [ScaleState, FixedArrayCopy.counterFrame,
    Locals.set, hFrameParams, hParams, hLength, List.length_set, List.getElem?_set,
    Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]

theorem scaleLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr outputPtr : UInt64) (input : ByteArray) (width rows : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem ptr.toNat input) (hSize : rows * width * 4 ≤ input.size)
    (hFit : outputPtr.toNat + 4 * rows ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * rows ≤ initial.mem.pages * 65536)
    (hSep : ptr.toNat + input.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 4 * rows ≤ ptr.toNat)
    (hReady : PackedGenerateLoop.Ready 6 40 41 rows 0 outputPtr frame)
    (hState : ScaleState (parameters owner ptr input width rows) rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 6 40 41 rows rows outputPtr result →
      ScaleState (parameters owner ptr input width rows) rows result →
      ByteArrayAt final.mem outputPtr.toNat (quantizeRows input width rows).scales →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * rows) →
      wp «module» rest Q final result env) :
    wp «module» ((func3.drop 42).take 1 ++ rest) Q initial frame env := by
  rw [emitted_scales]
  apply PackedGenerateLoop.program_spec (value := fun row => rowScale input (row * width) width)
    (P := ScaleState (parameters owner ptr input width rows) rows)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact scaleState_advance _ rows rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact scaleWord_spec env current owner ptr outputPtr input width rows index next
      (hInput.writesRange hWrites hSep) (by nlinarith) hReady hState Q rest hNext
  · exact hDone

#print axioms scaleWord_spec
#print axioms scaleLoop_spec

end Project.Gpt2QuantizedLinearRows.QuantizeRows
