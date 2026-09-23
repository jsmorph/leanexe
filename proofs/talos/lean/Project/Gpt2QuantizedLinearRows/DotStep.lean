import Project.Gpt2QuantizedLinearRows.Program
import Project.ProofKit.QuantizedDot
import Project.ProofKit.SignedByte
import Project.ProofKit.PackedByteMemory
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedLinearRows.Dot
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def stepCode : Wasm.Program :=
  match (func4[12]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

theorem emitted_loop :
    func4 = func4.take 12 ++ RangeFoldLoop.program 20 21 stepCode ++ func4.drop 13 := rfl

def Accumulator (weightOwner weightPtr inputOwner inputPtr : UInt64)
    (weights input : ByteArray) (weightOffset inputOffset width index : Nat)
    (frame : Locals) : Prop :=
  frame.params = [.i64 weightOwner, .i64 weightPtr, .i64 (UInt64.ofNat weights.size),
    .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat weightOffset), .i64 (UInt64.ofNat inputOffset),
    .i64 (UInt64.ofNat width)] ∧
  frame.locals.length = 23 ∧
  frame.locals[1]? = some (.i64 (dot weights input weightOffset inputOffset index).toUInt64) ∧
  frame.locals[13]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightOwner weightPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset inputOffset width index : Nat) (frame : Locals)
    (hweights : ByteArrayAt initial.mem weightPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hweightSize : weightOffset + width ≤ weights.size)
    (hinputSize : inputOffset + width ≤ input.size) (hindex : index < width)
    (hready : RangeFoldLoop.Ready 20 21 width index frame)
    (hacc : Accumulator weightOwner weightPtr inputOwner inputPtr weights input
      weightOffset inputOffset width index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 20 21 width (index + 1) result →
      Accumulator weightOwner weightPtr inputOwner inputPtr weights input
        weightOffset inputOffset width (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  have hcounter : frame.locals[11]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[12]? = some (.i64 (UInt64.ofNat width)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hweightFit := hweights.1
  have hinputFit := hinput.1
  have hia := CheckedNatAdd.guard_of_fits inputOffset index
    (by change inputOffset + index < 18446744073709551616; omega)
  have hwa := CheckedNatAdd.guard_of_fits weightOffset index
    (by change weightOffset + index < 18446744073709551616; omega)
  have hinc := CheckedNatAdd.guard_of_fits index 1
    (by change index + 1 < 18446744073709551616; omega)
  have hirange : inputOffset + index < input.size := by omega
  have hwrange : weightOffset + index < weights.size := by omega
  obtain ⟨hilt, hibound, hiread⟩ := PackedByteMemory.access initial.mem inputPtr input _ hinput hirange
  obtain ⟨hwlt, hwbound, hwread⟩ := PackedByteMemory.access initial.mem weightPtr weights _ hweights hwrange
  have hiofit : inputOffset + index < UInt64.size := by
    change inputOffset + index < 18446744073709551616
    omega
  have hwofit : weightOffset + index < UInt64.size := by
    change weightOffset + index < 18446744073709551616
    omega
  have hiptr : (inputPtr + UInt64.ofNat (inputOffset + index)).toNat =
      inputPtr.toNat + (inputOffset + index) := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hiofit]
    apply Nat.mod_eq_of_lt
    change _ < 18446744073709551616
    omega
  have hwptr : (weightPtr + UInt64.ofNat (weightOffset + index)).toNat =
      weightPtr.toNat + (weightOffset + index) := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hwofit]
    apply Nat.mod_eq_of_lt
    change _ < 18446744073709551616
    omega
  simp only [stepCode, func4, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hia)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1,
    ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simpa using hilt)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1,
    hiptr, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero, not_lt_of_ge hibound, hiread,
    ← SignedByte.extend8_eq, List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hwa)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1,
    ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simpa using hwlt)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1,
    hwptr, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero, not_lt_of_ge hwbound, hwread,
    ← SignedByte.extend8_eq, widen_mul, widen_add,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hinc)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, UInt64.ofNat_add, true_and]
    exact ⟨rfl, trivial⟩
  · simp only [Accumulator, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, QuantizedDot.dot_succ, and_self]

#print axioms step_spec

end Project.Gpt2QuantizedLinearRows.Dot
