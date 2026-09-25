import Project.Gpt2QuantizedLinearRows.ProjectionSize

namespace Project.Gpt2QuantizedLinearRows.Projection
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def inputFrame (frame : Locals) (inputPtr : UInt64) (input : ByteArray) (width rows : Nat)
    (valuePtr scalePtr : UInt64) : Locals :=
  { frame with
    locals := frame.locals
      |>.set 0 (.i64 0)
      |>.set 1 (.i64 inputPtr)
      |>.set 2 (.i64 (UInt64.ofNat input.size))
      |>.set 3 (.i64 (UInt64.ofNat width))
      |>.set 4 (.i64 (UInt64.ofNat rows))
      |>.set 10 (.i64 (UInt64.ofNat (4 * rows)))
      |>.set 9 (.i64 scalePtr)
      |>.set 8 (.i64 scalePtr)
      |>.set 7 (.i64 (UInt64.ofNat (rows * width)))
      |>.set 6 (.i64 valuePtr)
      |>.set 5 (.i64 valuePtr)
      |>.set 11 (.i64 valuePtr)
      |>.set 12 (.i64 valuePtr)
      |>.set 13 (.i64 (UInt64.ofNat (rows * width)))
      |>.set 14 (.i64 scalePtr)
      |>.set 15 (.i64 scalePtr)
      |>.set 16 (.i64 (UInt64.ofNat (4 * rows)))
    values := [] }

set_option maxRecDepth 32768 in
theorem inputCode_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) (frame : Locals)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : rows * width * 4 ≤ input.size)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCount : 4 * rows ≤ 2^32)
    (hScaleBump : takeFirstFitFrom 0 (QuantizeRows.scaleNeed rows) heap.nodes = none →
      heap.top.toNat + 48 + (QuantizeRows.scaleNeed rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (QuantizeRows.scaleNeed rows) ≤ initial.memoryCap «module» 0)
    (hByteBump : let next := heap.allocate (QuantizeRows.scaleNeed rows)
      takeFirstFitFrom 0 (QuantizeRows.byteNeed width rows) next.nodes = none →
        next.top.toNat + 48 + (QuantizeRows.byteNeed width rows).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (QuantizeRows.byteNeed width rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias)
    (hLocals : frame.locals.length = 73) (hEmpty : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, QuantizeRows.Output heap initial final input width rows →
      wp «module» rest Q final
        (inputFrame frame inputPtr input width rows (QuantizeRows.valueNode heap width rows).root
          (QuantizeRows.scaleNode heap rows).root) env) :
    wp «module» (func8.take 34 ++ rest) Q initial frame env := by
  have hRows := quantizeRows_exact env initial heap 0 inputPtr input width rows hHeap hInput hInputSize
    hInputProtected hCount hScaleBump hByteBump hPages
  simp only [func8, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hEmpty, List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_call_tw (hRows.append_args rfl rfl rfl []) ?_
  rintro final values ⟨out, rfl, rfl, hOutput⟩
  wp_packed_frame [hParams, parameters, hLocals]
  simpa only [inputFrame, hParams, parameters] using hNext final hOutput

theorem input_size_state (frame : Locals) (inputPtr : UInt64) (input : ByteArray) (width outputWidth rows : Nat)
    (valuePtr scalePtr : UInt64) (hLocals : frame.locals.length = 73) (hTyped : I64Values frame.locals) :
    OutputState frame.params valuePtr scalePtr width outputWidth rows
      (sizeFrame (inputFrame frame inputPtr input width rows valuePtr scalePtr) outputWidth rows) := by
  simp (config := { maxDischargeDepth := 64 }) only [OutputState, sizeFrame, inputFrame, hLocals,
    List.length_set, List.getElem?_set, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
    I64Values.set, hTyped, and_self]

#print axioms inputCode_spec

end Project.Gpt2QuantizedLinearRows.Projection
