import Project.Gpt2CachedStep.Program
import Project.Gpt2LinearRows.Source
import Project.ProofKit.PackedWordRead
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.CheckedNatMulArithmetic
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.LinearRows

open Project.Gpt2LinearRows (dotPrefix dotPrefix_zero dotPrefix_succ value linearRows_eq)

open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def outerBody : Wasm.Program :=
  match (func21[49]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => body
  | _ => []

def dotStep : Wasm.Program :=
  match (outerBody[40]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

def parameters (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows : Nat) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
    .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat weightOffset), .i64 (UInt64.ofNat biasOffset),
    .i64 (UInt64.ofNat inputWidth), .i64 (UInt64.ofNat outputWidth), .i64 (UInt64.ofNat rows)]

def Saved (original frame : Locals) : Prop :=
  frame.locals[0]? = original.locals[0]? ∧
  frame.locals[1]? = original.locals[1]? ∧
  frame.locals[32]? = original.locals[32]? ∧
  frame.locals[33]? = original.locals[33]?

def Accumulator (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows row column index : Nat)
    (original frame : Locals) : Prop :=
  frame.params = parameters weightsOwner inputOwner weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows ∧
  frame.locals.length = 48 ∧
  frame.locals[2]? = some (.i64 (UInt64.ofNat row)) ∧
  frame.locals[3]? = some (.i64 (UInt64.ofNat column)) ∧
  frame.locals[5]? = some (.i64 (dotPrefix weights input weightOffset inputWidth outputWidth row column index).toUInt64) ∧
  frame.locals[36]? = some (.i64 1) ∧ Saved original frame

set_option maxRecDepth 32768 in
theorem dotStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows row column index : Nat)
    (original frame : Locals) (values : List Value)
    (hweights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hinputIndex : (row * inputWidth + index) * 4 + 4 ≤ input.size)
    (hweightIndex : (weightOffset + index * outputWidth + column) * 4 + 4 ≤ weights.size)
    (hwidth : inputWidth < UInt64.size) (houtWidth : outputWidth < UInt64.size)
    (hcolumn : column < outputWidth) (hindex : index < inputWidth)
    (hready : RangeFoldLoop.Ready 45 46 inputWidth index frame values)
    (hacc : Accumulator weightsOwner inputOwner weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth
      rows row column index original frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 45 46 inputWidth (index + 1) result values →
      Accumulator weightsOwner inputOwner weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth
        rows row column (index + 1) original result → wp «module» rest Q initial result env) :
    wp «module» (dotStep ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, hrow, hcol, htotal, hstride, hsaved⟩
  simp only [parameters] at hparams
  have hcounter : frame.locals[34]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[35]? = some (.i64 (UInt64.ofNat inputWidth)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hinputSize := hinput.1
  have hweightSize := hweights.1
  have hinNonzero : UInt64.ofNat inputWidth ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hwidth] at this
    change inputWidth = 0 at this
    omega
  have houtNonzero : UInt64.ofNat outputWidth ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' houtWidth] at this
    change outputWidth = 0 at this
    omega
  have hMulRow := CheckedNatMul.guard_of_nat_fits row inputWidth
    (by change row * inputWidth < 18446744073709551616; omega) hinNonzero
  have hMulIndex := CheckedNatMul.guard_of_nat_fits index outputWidth
    (by change index * outputWidth < 18446744073709551616; omega) houtNonzero
  have hInputAdd := CheckedNatAdd.guard_of_fits (row * inputWidth) index
    (by change row * inputWidth + index < 18446744073709551616; omega)
  have hWeightAdd := CheckedNatAdd.guard_of_fits weightOffset (index * outputWidth)
    (by change weightOffset + index * outputWidth < 18446744073709551616; omega)
  have hColumnAdd := CheckedNatAdd.guard_of_fits (weightOffset + index * outputWidth) column
    (by change weightOffset + index * outputWidth + column < 18446744073709551616; omega)
  simp only [UInt64.ofNat_add, UInt64.ofNat_mul] at hInputAdd hWeightAdd hColumnAdd
  have hInc := CheckedNatAdd.guard_of_fits index 1 (by omega)
  simp only [show UInt64.ofNat 1 = 1 from rfl] at hInc
  have hinc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hinputAddr : UInt64.ofNat row * UInt64.ofNat inputWidth + UInt64.ofNat index =
      UInt64.ofNat (row * inputWidth + index) := by simp
  have hweightAddr : UInt64.ofNat weightOffset + UInt64.ofNat index * UInt64.ofNat outputWidth + UInt64.ofNat column =
      UInt64.ofNat (weightOffset + index * outputWidth + column) := by simp
  simp only [dotStep, outerBody, func21, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  repeat' first
    | wp_packed_frame [hparams, hlength, hrow, hcol, htotal, hcounter, hstop, hstride, hready.1, hinNonzero, houtNonzero]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hinNonzero, hMulRow, hInputAdd])])
  simp only [hinputAddr]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial inputOwner inputPtr input (row * inputWidth + index) hinput hinputIndex).append_args
      rfl rfl rfl values) ?_
  rintro final resultValues ⟨result, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hparams, hlength, hrow, hcol, htotal, hcounter, hstop, hstride, hready.1, hinNonzero, houtNonzero]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [houtNonzero, hMulIndex, hWeightAdd, hColumnAdd])])
  simp only [hweightAddr]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env final weightsOwner weightsPtr weights (weightOffset + index * outputWidth + column) hweights hweightIndex).append_args
      rfl rfl rfl values) ?_
  rintro final' resultValues ⟨result, rfl, rfl, rfl⟩
  wp_packed_frame [hparams, hlength, hrow, hcol, htotal, hcounter, hstop, hstride, hready.1, hinNonzero, houtNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hInc)]
  wp_packed_frame [hparams, hlength, hrow, hcol, htotal, hcounter, hstop, hstride, hready.1, hinNonzero, houtNonzero]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc, true_and]
  · simpa only [Accumulator, parameters, Saved, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hrow, hcol, hstride, dotPrefix_succ,
      LeanExe.Models.Gpt2.word, true_and, and_self] using hsaved

#print axioms dotStep_spec

end Project.Gpt2CachedStep.LinearRows
