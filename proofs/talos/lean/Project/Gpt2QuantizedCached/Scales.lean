import Project.Gpt2QuantizedCached.Program
import Project.ProofKit.QuantizedValidity
import Project.ProofKit.PackedWordAccess
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.CallRemainder

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Scales
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def validPrefix (input : ByteArray) (offset count : Nat) : Bool :=
  (List.range count).foldl (fun valid index =>
    valid && decide (0x00800000 ≤ LeanExe.Packed.getUInt32LE! input (offset + index * 4)) &&
    decide (LeanExe.Packed.getUInt32LE! input (offset + index * 4) < 0x7F800000)) true

@[simp] theorem prefix_zero (input : ByteArray) (offset : Nat) : validPrefix input offset 0 = true := rfl

theorem prefix_succ (input : ByteArray) (offset count : Nat) :
    validPrefix input offset (count + 1) = (validPrefix input offset count &&
      decide (0x00800000 ≤ LeanExe.Packed.getUInt32LE! input (offset + count * 4)) &&
      decide (LeanExe.Packed.getUInt32LE! input (offset + count * 4) < 0x7F800000)) := by
  simp only [validPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem source_eq (input : ByteArray) (offset count : Nat) :
    validScales input offset count = validPrefix input offset count := by
  simp only [validScales, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

def stepCode : Wasm.Program :=
  match (func24[12]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

theorem emitted_loop :
    func24 = func24.take 12 ++ RangeFoldLoop.program 15 16 stepCode ++ func24.drop 13 := rfl

def Accumulator (owner ptr : UInt64) (input : ByteArray) (offset count index : Nat)
    (frame : Locals) : Prop :=
  frame.params = [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat offset), .i64 (UInt64.ofNat count)] ∧
  frame.locals.length = 24 ∧
  frame.locals[1]? = some (.i64 (if validPrefix input offset index then 1 else 0)) ∧
  frame.locals[12]? = some (.i64 1)

theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (offset count index : Nat) (frame : Locals)
    (hBytes : ByteArrayAt initial.mem ptr.toNat input)
    (hSize : offset + count * 4 ≤ input.size) (hIndex : index < count)
    (hReady : RangeFoldLoop.Ready 15 16 count index frame)
    (hAcc : Accumulator owner ptr input offset count index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, RangeFoldLoop.Ready 15 16 count (index + 1) result →
      Accumulator owner ptr input offset count (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hAcc with ⟨hParams, hLength, hTotal, hStride⟩
  have hCounter : frame.locals[10]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hStop : frame.locals[11]? = some (.i64 (UInt64.ofNat count)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2
  have hFit := hBytes.1
  have hAdd := CheckedNatAdd.guard_of_fits offset (index * 4)
    (by change offset + index * 4 < 18446744073709551616; omega)
  have hInc := CheckedNatAdd.guard_of_fits index 1
    (by change index + 1 < 18446744073709551616; omega)
  have hMul : ¬ (-1 : UInt64) / 4 < UInt64.ofNat index := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by
      change index < 18446744073709551616; omega)]
    change ¬ 4611686018427387903 < index
    omega
  simp only [stepCode, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hTotal, hCounter, hStop, hStride, hReady.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hMul)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_add]
  apply PackedWordAccess.guard_spec «module» env initial _ ptr input (offset + index * 4)
    18 19 20 [] hBytes (by omega)
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength]
  · simp [UInt64.ofNat_add, UInt64.ofNat_mul]
  have hMinEq : (8388608 : UInt64) ≤ (LeanExe.Packed.getUInt32LE! input (offset + index * 4)).toUInt64 ↔
      (8388608 : UInt32) ≤ LeanExe.Packed.getUInt32LE! input (offset + index * 4) :=
    UInt32.toUInt64_le (a := 8388608) (b := LeanExe.Packed.getUInt32LE! input (offset + index * 4))
  have hMaxEq : (LeanExe.Packed.getUInt32LE! input (offset + index * 4)).toUInt64 < 2139095040 ↔
      LeanExe.Packed.getUInt32LE! input (offset + index * 4) < (2139095040 : UInt32) :=
    UInt32.toUInt64_lt (a := LeanExe.Packed.getUInt32LE! input (offset + index * 4)) (b := 2139095040)
  cases hPrefix : validPrefix input offset index <;>
    by_cases hMin : (8388608 : UInt32) ≤ LeanExe.Packed.getUInt32LE! input (offset + index * 4) <;>
    by_cases hMax : LeanExe.Packed.getUInt32LE! input (offset + index * 4) < (2139095040 : UInt32)
  all_goals
    repeat' first
      | wp_packed_frame [hParams, hLength, hTotal, hCounter, hStop, hStride, hReady.1, hPrefix]
      | (refine wp_iff_cons rfl ?_
         first
           | rw [ite_eq_left (by simpa [hMinEq, hMaxEq, hMin, hMax])]
           | rw [ite_eq_right (by simpa [hMinEq, hMaxEq, hMin, hMax])]
           | rw [ite_eq_right (by simpa using hInc)])
    apply hNext
    · simp only [RangeFoldLoop.Ready, Locals.get, hLength, List.length_set,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hStop, UInt64.ofNat_add, true_and]
      exact ⟨rfl, trivial⟩
    · simp only [Accumulator, hLength, List.length_set, List.getElem?_set,
        Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hStride, prefix_succ, hPrefix]
      simp [hMin, hMax]

#print axioms step_spec

theorem exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (offset count : Nat)
    (hBytes : ByteArrayAt initial.mem ptr.toNat input)
    (hSize : offset + count * 4 ≤ input.size) :
    TerminatesWith env «module» 24 initial
      [.i64 (UInt64.ofNat count), .i64 (UInt64.ofNat offset),
        .i64 (UInt64.ofNat input.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (if validScales input offset count then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_
  change wp «module» func24 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size),
        .i64 (UInt64.ofNat offset), .i64 (UInt64.ofNat count)],
      locals := List.replicate 24 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func24, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame []
  apply RangeFoldLoop.program_spec (count := count)
    (P := Accumulator owner ptr input offset count)
  · have := hBytes.1
    change count < 18446744073709551616
    omega
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hIndex hReady hAcc Q rest hNext
    exact step_spec env initial owner ptr input offset count index next hBytes hSize
      hIndex hReady hAcc Q rest hNext
  · intro result hReady hAcc
    rcases hAcc with ⟨hParams, hLength, hTotal, hStride⟩
    wp_packed_frame [hParams, hLength, hTotal, hReady.1]
    simp [func24Def, source_eq]

#print axioms exact
end Project.Gpt2QuantizedCached.Scales
