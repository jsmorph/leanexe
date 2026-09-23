import Project.Gpt2QuantizedCached.GroupedProjection.ProjectionSize

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Project.Gpt2QuantizedLinearRows
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def inputFrame (frame : Locals) (inputOwner inputPtr : UInt64) (input : ByteArray) (width rows : Nat)
    (valuePtr scalePtr : UInt64) : Locals :=
  { frame with
    locals := frame.locals
      |>.set 82 (.i64 (UInt64.ofNat width))
      |>.set 83 (.i64 64)
      |>.set 0 (.i64 (UInt64.ofNat (width / 64)))
      |>.set 1 (.i64 inputOwner)
      |>.set 2 (.i64 inputPtr)
      |>.set 3 (.i64 (UInt64.ofNat input.size))
      |>.set 4 (.i64 64)
      |>.set 82 (.i64 (UInt64.ofNat rows))
      |>.set 83 (.i64 (UInt64.ofNat (width / 64)))
      |>.set 5 (.i64 (UInt64.ofNat (rows * (width / 64))))
      |>.set 11 (.i64 (UInt64.ofNat (4 * (rows * (width / 64)))))
      |>.set 10 (.i64 scalePtr)
      |>.set 9 (.i64 scalePtr)
      |>.set 8 (.i64 (UInt64.ofNat (rows * width)))
      |>.set 7 (.i64 valuePtr)
      |>.set 6 (.i64 valuePtr)
      |>.set 12 (.i64 valuePtr)
      |>.set 13 (.i64 valuePtr)
      |>.set 14 (.i64 (UInt64.ofNat (rows * width)))
      |>.set 15 (.i64 scalePtr)
      |>.set 16 (.i64 scalePtr)
      |>.set 17 (.i64 (UInt64.ofNat (4 * (rows * (width / 64)))))
    values := [] }

set_option maxRecDepth 32768 in
theorem inputCode_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) (frame : Locals)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : rows * width * 4 ≤ input.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width) (hWidth64 : width < UInt64.size)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCount : 4 * (rows * (width / 64)) ≤ 2^32)
    (hScaleBump : takeFirstFitFrom 0 (QuantizeRows.scaleNeed (rows * (width / 64))) heap.nodes = none →
      heap.top.toNat + 48 + (QuantizeRows.scaleNeed (rows * (width / 64))).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (QuantizeRows.scaleNeed (rows * (width / 64))) ≤ initial.memoryCap «module» 0)
    (hByteBump : let next := heap.allocate (QuantizeRows.scaleNeed (rows * (width / 64)))
      takeFirstFitFrom 0 (QuantizeRows.byteNeed 64 (rows * (width / 64))) next.nodes = none →
        next.top.toNat + 48 + (QuantizeRows.byteNeed 64 (rows * (width / 64))).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (QuantizeRows.byteNeed 64 (rows * (width / 64))) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias)
    (hLocals : frame.locals.length = 100) (hEmpty : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, QuantizeRows.Output heap initial final input 64 (rows * (width / 64)) →
      wp «module» rest Q final
        (inputFrame frame inputOwner inputPtr input width rows (QuantizeRows.valueNode heap 64 (rows * (width / 64))).root
          (QuantizeRows.scaleNode heap (rows * (width / 64))).root) env) :
    wp «module» (func8.take 50 ++ rest) Q initial frame env := by
  have hShape : rows * (width / 64) * 64 = rows * width := by
    rw [Nat.mul_assoc, Nat.div_mul_cancel hMultiple]
  have hRows := quantizeRows_exact env initial heap inputOwner inputPtr input 64 (rows * (width / 64))
    hHeap hInput (by simpa only [hShape] using hInputSize)
    hInputProtected hCount hScaleBump hByteBump hPages
  have hDiv : UInt64.ofNat width / 64 = UInt64.ofNat (width / 64) :=
    (UInt64.ofNat_div hWidth64 (by decide : 64 < UInt64.size)).symm
  have hGroups64 : width / 64 < UInt64.size := (Nat.div_le_self _ _).trans_lt hWidth64
  have hGroupsNe : UInt64.ofNat (width / 64) ≠ 0 := by
    intro h
    have heq := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hGroups64] at heq
    change width / 64 = 0 at heq
    have := Nat.div_mul_cancel hMultiple
    omega
  have hMul := CheckedNatMul.guard_of_nat_fits rows (width / 64)
    (by change _ < 18446744073709551616; omega) hGroupsNe
  simp only [func8, Project.Gpt2QuantizedCached.func42, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hEmpty, List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, parameters, hLocals, hDiv]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hGroupsNe)]
  wp_packed_frame [hParams, parameters, hLocals, hGroupsNe]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hMul)]
  wp_packed_frame [hParams, parameters, hLocals, ← UInt64.ofNat_mul]
  refine wp_call_tw (hRows.append_args rfl rfl rfl []) ?_
  rintro final values ⟨out, rfl, rfl, hOutput⟩
  wp_packed_frame [hParams, parameters, hLocals]
  simpa only [inputFrame, hParams, parameters, hShape] using hNext final hOutput

theorem input_size_state (frame : Locals) (inputOwner inputPtr : UInt64) (input : ByteArray) (width outputWidth rows : Nat)
    (valuePtr scalePtr : UInt64) (hLocals : frame.locals.length = 100) (hTyped : I64Values frame.locals) :
    OutputState frame.params valuePtr scalePtr width outputWidth rows
      (sizeFrame (inputFrame frame inputOwner inputPtr input width rows valuePtr scalePtr) outputWidth rows) := by
  simp (config := { maxDischargeDepth := 64 }) only [OutputState, sizeFrame, inputFrame, hLocals,
    List.length_set, List.getElem?_set, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
    I64Values.set, hTyped, and_self]

#print axioms inputCode_spec

end Project.Gpt2QuantizedCached.GroupedProjection.Projection
