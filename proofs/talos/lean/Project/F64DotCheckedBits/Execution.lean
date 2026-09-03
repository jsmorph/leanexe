import Project.F64DotCheckedBits.Program
import Project.F64DotCheckedBits.Numerical
import Project.ProofKit.Array
import Project.ProofKit.CheckedArrayGet
import Project.Common
import Interpreter.Wasm.Wp.Tactic

/-!
# Exact execution scaffolding for the runtime-length binary64 dot product

The generated entry first compares the two encoded array lengths.  A mismatch
returns status one and positive-zero bits without executing floating-point
code.  Equal empty arrays similarly return status zero and positive-zero bits.

For the nonempty path, the generated loop carries the number `k` of consumed
pairs and the modeled value of that prefix.  The definitions at the end of
this file make that invariant and its decreasing measure explicit; the loop
proof can then focus on the two checked array reads and the modeled multiply-
add recurrence.
-/

namespace Project.F64DotCheckedBits.Spec

open Wasm

namespace Kernels

abbrev dot64Acc := CodeLib.Numerical.Kernels.dot64Acc
abbrev dot64List := CodeLib.Numerical.Kernels.dot64List

end Kernels

/-- Pair the two logical array views exactly as the source model does. -/
def arrayPairTerms (left right : Array UInt64) : List (UInt64 × UInt64) :=
  pairTerms left.toList right.toList

/-- Equal-sized logical arrays contribute one pair per array element. -/
theorem arrayPairTerms_length_of_eq (left right : Array UInt64)
    (hLength : left.size = right.size) :
    (arrayPairTerms left right).length = left.size := by
  simp [arrayPairTerms, pairTerms, hLength]

/-- Reading pair `k` from the zipped logical view reads element `k` from
each source array.  The optional form avoids transporting proof terms between
the array and list bounds in clients. -/
theorem arrayPairTerms_getElem?_of_eq (left right : Array UInt64) (k : Nat)
    (hLength : left.size = right.size) (hIndex : k < left.size) :
    (arrayPairTerms left right)[k]? = some (left[k], right[k]) := by
  have hRightIndex : k < right.size := by omega
  unfold arrayPairTerms pairTerms
  apply List.getElem?_zip_eq_some.mpr
  constructor
  · rw [List.getElem?_eq_getElem (by simpa using hIndex)]
    simp
  · rw [List.getElem?_eq_getElem (by simpa using hRightIndex)]
    simp

private theorem dot64Acc_append (accumulator : UInt64)
    (initialTerms suffix : List (UInt64 × UInt64)) :
    CodeLib.Numerical.Kernels.dot64Acc accumulator
        (initialTerms ++ suffix) =
      CodeLib.Numerical.Kernels.dot64Acc
        (CodeLib.Numerical.Kernels.dot64Acc accumulator initialTerms)
        suffix := by
  induction initialTerms generalizing accumulator with
  | nil => rfl
  | cons term tailTerms ih =>
      rcases term with ⟨a, b⟩
      simpa only [List.cons_append, CodeLib.Numerical.Kernels.dot64Acc] using
        ih (Wasm.IEEE64.add accumulator (Wasm.IEEE64.mul a b))

private theorem dot64List_append_singleton
    (initialTerms : List (UInt64 × UInt64)) (term : UInt64 × UInt64)
    (hPrefix : initialTerms ≠ []) :
    Kernels.dot64List (initialTerms ++ [term]) =
      Wasm.IEEE64.add (Kernels.dot64List initialTerms)
        (Wasm.IEEE64.mul term.1 term.2) := by
  cases initialTerms with
  | nil => exact (hPrefix rfl).elim
  | cons first rest =>
      rcases first with ⟨firstLeft, firstRight⟩
      rcases term with ⟨left, right⟩
      simp only [CodeLib.Numerical.Kernels.dot64List,
        CodeLib.Numerical.Kernels.dot64,
        List.cons_append]
      rw [dot64Acc_append]
      rfl

/-- Extending a nonempty prefix by one term performs exactly the generated
multiply-add update. -/
theorem dot64List_take_succ (terms : List (UInt64 × UInt64)) (k : Nat)
    (hPositive : 0 < k) (hIndex : k < terms.length) :
    Kernels.dot64List (terms.take (k + 1)) =
      Wasm.IEEE64.add (Kernels.dot64List (terms.take k))
        (Wasm.IEEE64.mul terms[k].1 terms[k].2) := by
  have hTakeLength : (terms.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hIndex)]
  have hTakeNonempty : terms.take k ≠ [] := by
    intro hNil
    have hZero := congrArg List.length hNil
    rw [hTakeLength] at hZero
    simp at hZero
    omega
  rw [List.take_add_one, List.getElem?_eq_getElem hIndex]
  exact dot64List_append_singleton (terms.take k) terms[k] hTakeNonempty

/-- The generated nonempty path seeds its accumulator with exactly the first
modeled product. -/
theorem dot64List_take_one_of_nonempty (left right : Array UInt64)
    (hLength : left.size = right.size) (hNonempty : 0 < left.size) :
    Kernels.dot64List ((arrayPairTerms left right).take 1) =
      Wasm.IEEE64.mul left[0] right[0] := by
  have hPair? := arrayPairTerms_getElem?_of_eq left right 0 hLength hNonempty
  have hTermsIndex : 0 < (arrayPairTerms left right).length := by
    rw [arrayPairTerms_length_of_eq left right hLength]
    exact hNonempty
  have hPair : (arrayPairTerms left right)[0] = (left[0], right[0]) :=
    Project.Common.getElem_of_some hPair? hTermsIndex
  have hTermsNonempty : arrayPairTerms left right ≠ [] := by
    intro hNil
    simp [hNil] at hTermsIndex
  cases hTerms : arrayPairTerms left right with
  | nil => exact (hTermsNonempty hTerms).elim
  | cons first rest =>
      have hFirst : first = (left[0], right[0]) := by
        simpa [hTerms] using hPair
      subst first
      rfl

/-- A length mismatch exits before either array element is read and before
any floating-point instruction is reached. -/
theorem unequal_lengths_exact
    (env : HostEnv Unit) (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (left right : Array UInt64)
    (hLeft : Project.ProofKit.UInt64Array.At initial leftPtr left)
    (hRight : Project.ProofKit.UInt64Array.At initial rightPtr right)
    (hLength : left.size ≠ right.size) :
    TerminatesWith env Project.F64DotCheckedBits.«module» 0 initial
      [.i64 rightPtr, .i64 leftPtr]
      (fun final values =>
        final = initial ∧ values = [.i64 0, .i64 1]) := by
  have hLeftLengthBound := hLeft.generatedLengthBound
  have hRightLengthBound := hRight.generatedLengthBound
  have hLeftAddress := hLeft.pointerAddress_eq
  have hRightAddress := hRight.pointerAddress_eq
  have hLeftLengthRead := hLeft.lengthRead
  have hRightLengthRead := hRight.lengthRead
  have hEncodedLength :
      UInt64.ofNat left.size ≠ UInt64.ofNat right.size := by
    intro hEncoded
    apply hLength
    have hNatural := congrArg UInt64.toNat hEncoded
    rw [UInt64.toNat_ofNat_of_lt' hLeft.size_lt,
      UInt64.toNat_ofNat_of_lt' hRight.size_lt] at hNatural
    exact hNatural
  apply TerminatesWith.of_wp_entry_for
    (f := Project.F64DotCheckedBits.func0Def)
  · simp [Project.F64DotCheckedBits.«module»]
  · change wp Project.F64DotCheckedBits.«module»
      Project.F64DotCheckedBits.func0 _ initial
      { params := [.i64 leftPtr, .i64 rightPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold Project.F64DotCheckedBits.func0
    wp_run_with []
    refine ⟨hLeftLengthBound, ?_⟩
    rw [hLeftAddress, hLeftLengthRead]
    refine ⟨hRightLengthBound, ?_⟩
    rw [hRightAddress, hRightLengthRead]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hEncodedLength])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run <;> simp [Project.F64DotCheckedBits.func0Def]

/-- Equal empty arrays take the accepted empty branch and return status zero
and positive-zero bits, again without executing floating-point code. -/
theorem equal_empty_exact
    (env : HostEnv Unit) (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (left right : Array UInt64)
    (hLeft : Project.ProofKit.UInt64Array.At initial leftPtr left)
    (hRight : Project.ProofKit.UInt64Array.At initial rightPtr right)
    (hLength : left.size = right.size) (hEmpty : left.size = 0) :
    TerminatesWith env Project.F64DotCheckedBits.«module» 0 initial
      [.i64 rightPtr, .i64 leftPtr]
      (fun final values =>
        final = initial ∧ values = [.i64 0, .i64 0]) := by
  have hLeftLengthBound := hLeft.generatedLengthBound
  have hRightLengthBound := hRight.generatedLengthBound
  have hLeftAddress := hLeft.pointerAddress_eq
  have hRightAddress := hRight.pointerAddress_eq
  have hLeftLengthRead := hLeft.lengthRead
  have hRightLengthRead := hRight.lengthRead
  have hEncodedLength :
      UInt64.ofNat left.size = UInt64.ofNat right.size :=
    congrArg UInt64.ofNat hLength
  have hEncodedEmpty : UInt64.ofNat left.size = 0 := by
    simp [hEmpty]
  apply TerminatesWith.of_wp_entry_for
    (f := Project.F64DotCheckedBits.func0Def)
  · simp [Project.F64DotCheckedBits.«module»]
  · change wp Project.F64DotCheckedBits.«module»
      Project.F64DotCheckedBits.func0 _ initial
      { params := [.i64 leftPtr, .i64 rightPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold Project.F64DotCheckedBits.func0
    wp_run_with []
    refine ⟨hLeftLengthBound, ?_⟩
    rw [hLeftAddress, hLeftLengthRead]
    refine ⟨hRightLengthBound, ?_⟩
    rw [hRightAddress, hRightLengthRead]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hEncodedLength])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run_with []
    refine ⟨hLeftLengthBound, ?_⟩
    rw [hLeftAddress, hLeftLengthRead]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hEncodedEmpty])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run <;> simp [Project.F64DotCheckedBits.func0Def]

/-! ## Nonempty-loop invariant

The compiler uses locals 4 and 5 for the loop-carried index and accumulator.
The other eighteen locals are scratch values whose exact contents do not
belong in the mathematical invariant. -/

private def loopFrame (leftPtr rightPtr index accumulator : UInt64)
    (local2 local3 local6 local7 local8 local9 local10 local11 local12
      local13 local14 local15 local16 local17 local18 local19 local20 local21 :
      UInt64) (values : List Value := []) : Locals :=
  { params := [.i64 leftPtr, .i64 rightPtr],
    locals :=
      [.i64 local2, .i64 local3,
       .i64 index, .i64 accumulator,
       .i64 local6, .i64 local7, .i64 local8, .i64 local9,
       .i64 local10, .i64 local11, .i64 local12, .i64 local13,
       .i64 local14, .i64 local15, .i64 local16, .i64 local17,
       .i64 local18, .i64 local19, .i64 local20, .i64 local21],
    values := values }

/-- Frame shape while the nonempty path stages its two seed element loads. -/
private def seedFrame (leftPtr rightPtr staged : UInt64)
    (values : List Value) : Locals :=
  { params := [.i64 leftPtr, .i64 rightPtr],
    locals :=
      [.i64 1,
       .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
       .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
       .i64 0, .i64 0,
       .i64 staged,
       .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    values := values }

/-- At loop entry, `k` pairs have been consumed and local 5 is exactly the
modeled result for that nonempty prefix. -/
private def loopInvariant (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (terms : List (UInt64 × UInt64)) :
    AssertionF Unit :=
  fun current frame =>
    current = initial ∧
      ∃ k : Nat, 1 ≤ k ∧ k ≤ terms.length ∧
        ∃ local2 local3 local6 local7 local8 local9 local10 local11 local12
          local13 local14 local15 local16 local17 local18 local19 local20 local21 :
          UInt64,
          frame = loopFrame leftPtr rightPtr (UInt64.ofNat k)
            (Kernels.dot64List (terms.take k)) local2 local3 local6 local7
            local8 local9 local10 local11 local12 local13 local14 local15
            local16 local17 local18 local19 local20 local21

/-- The number of input pairs still unconsumed by the generated loop. -/
private def loopMeasure (terms : List (UInt64 × UInt64))
    (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 4 with
  | some (.i64 index) => terms.length - index.toNat
  | _ => 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- Equal nonempty arrays execute the generated multiply-add loop and return
exactly Talos's pure modeled binary64 dot product. -/
theorem equal_nonempty_exact
    (env : HostEnv Unit) (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (left right : Array UInt64)
    (hLeft : Project.ProofKit.UInt64Array.At initial leftPtr left)
    (hRight : Project.ProofKit.UInt64Array.At initial rightPtr right)
    (hLength : left.size = right.size) (hNonempty : 0 < left.size) :
    TerminatesWith env Project.F64DotCheckedBits.«module» 0 initial
      [.i64 rightPtr, .i64 leftPtr]
      (fun final values =>
        final = initial ∧
          values = [.i64 (Kernels.dot64List (arrayPairTerms left right)),
            .i64 0]) := by
  have hLeftLengthBound := hLeft.generatedLengthBound
  have hRightLengthBound := hRight.generatedLengthBound
  have hLeftAddress := hLeft.pointerAddress_eq
  have hRightAddress := hRight.pointerAddress_eq
  have hLeftLengthRead := hLeft.lengthRead
  have hRightLengthRead := hRight.lengthRead
  have hEncodedLength :
      UInt64.ofNat left.size = UInt64.ofNat right.size :=
    congrArg UInt64.ofNat hLength
  have hEncodedNonempty : UInt64.ofNat left.size ≠ 0 := by
    intro hZero
    have hNatural := congrArg UInt64.toNat hZero
    rw [UInt64.toNat_ofNat_of_lt' hLeft.size_lt] at hNatural
    exact (Nat.ne_of_gt hNonempty) (by simpa using hNatural)
  have hRightNonempty : 0 < right.size := by omega
  have hTermsLength : (arrayPairTerms left right).length = left.size :=
    arrayPairTerms_length_of_eq left right hLength
  have hSeed :
      Kernels.dot64List ((arrayPairTerms left right).take 1) =
        Wasm.IEEE64.mul left[0] right[0] :=
    dot64List_take_one_of_nonempty left right hLength hNonempty
  apply TerminatesWith.of_wp_entry_for
    (f := Project.F64DotCheckedBits.func0Def)
  · simp [Project.F64DotCheckedBits.«module»]
  · change wp Project.F64DotCheckedBits.«module»
      Project.F64DotCheckedBits.func0 _ initial
      { params := [.i64 leftPtr, .i64 rightPtr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold Project.F64DotCheckedBits.func0
    wp_run_with []
    refine ⟨hLeftLengthBound, ?_⟩
    rw [hLeftAddress, hLeftLengthRead]
    refine ⟨hRightLengthBound, ?_⟩
    rw [hRightAddress, hRightLengthRead]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hEncodedLength])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run_with []
    refine ⟨hLeftLengthBound, ?_⟩
    rw [hLeftAddress, hLeftLengthRead]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hEncodedNonempty])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    simp only [Locals.get, Locals.set?, Function.toLocals,
      Function.numParams, List.take, List.drop, List.replicate, List.length,
      List.map, ValueType.zero]
    simp only [wp_constI64_cons, wp_localSet_cons, Locals.set?,
      Function.numParams, List.length]
    simp only [wp_localGet_cons, wp_localSet_cons, Locals.get, Locals.set?,
      Function.numParams, List.length]
    simp only [wp_constI64_cons, wp_localSet_cons, Locals.set?,
      Function.numParams, List.length]
    change wp Project.F64DotCheckedBits.«module»
      (Project.ProofKit.CheckedArrayGet.checkedGetCore 15 16 ++ _)
      _ initial (seedFrame leftPtr rightPtr leftPtr []) env
    refine Project.ProofKit.CheckedArrayGet.checkedGetCore_spec
      (pointerLocal := 15) (indexLocal := 16)
      (module_ := Project.F64DotCheckedBits.«module») (env := env)
      (store := initial) (frame := seedFrame leftPtr rightPtr leftPtr [])
      (pointer := leftPtr) (input := left) (index := 0) (tail := [])
      (hPointer := rfl) (hIndex := rfl) (hValues := rfl)
      (hArray := hLeft) (hIndexBound := hNonempty)
      (Q := _) (rest := _) ?_
    simp only [seedFrame, wp_f64ReinterpretI64_cons]
    simp only [wp_localGet_cons, wp_localSet_cons, Locals.get, Locals.set?,
      Function.numParams, List.length]
    simp only [wp_constI64_cons, wp_localSet_cons, Locals.set?,
      Function.numParams, List.length]
    change wp Project.F64DotCheckedBits.«module»
      (Project.ProofKit.CheckedArrayGet.checkedGetCore 15 16 ++ _)
      _ initial (seedFrame leftPtr rightPtr rightPtr [.f64 left[0]]) env
    refine Project.ProofKit.CheckedArrayGet.checkedGetCore_spec
      (pointerLocal := 15) (indexLocal := 16)
      (module_ := Project.F64DotCheckedBits.«module») (env := env)
      (store := initial)
      (frame := seedFrame leftPtr rightPtr rightPtr [.f64 left[0]])
      (pointer := rightPtr) (input := right) (index := 0)
      (tail := [.f64 left[0]])
      (hPointer := rfl) (hIndex := rfl) (hValues := rfl)
      (hArray := hRight) (hIndexBound := hRightNonempty)
      (Q := _) (rest := _) ?_
    wp_run [seedFrame]
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := loopInvariant initial leftPtr rightPtr
        (arrayPairTerms left right))
      (μ := loopMeasure (arrayPairTerms left right))
    · refine ⟨rfl, 1, by omega, ?_, 1,
        Wasm.IEEE64.mul left[0] right[0],
        0, 0, 0, 0, 0, 0, 0, 0, 0, rightPtr, 0, 0, 0, 0, 0, 0, ?_⟩
      · rw [hTermsLength]
        exact hNonempty
      · simp [loopFrame, hSeed, Wasm.f64Mul]
    · rintro current frame
        ⟨rfl, k, hkPositive, hkLength,
          local2, local3, local6, local7, local8, local9, local10, local11,
          local12, local13, local14, local15, local16, local17, local18,
          local19, local20, local21, rfl⟩
      have hkLeftLe : k ≤ left.size := by omega
      have hkLt64 : k < UInt64.size :=
        lt_of_le_of_lt hkLeftLe hLeft.size_lt
      have hkToNat : (UInt64.ofNat k).toNat = k :=
        UInt64.toNat_ofNat_of_lt' hkLt64
      simp only [loopFrame]
      wp_run_with []
      refine ⟨hLeftLengthBound, ?_⟩
      rw [hLeftAddress, hLeftLengthRead]
      by_cases hEnd : k = (arrayPairTerms left right).length
      · have hNotLt : ¬ UInt64.ofNat k < UInt64.ofNat left.size := by
          rw [UInt64.lt_iff_toNat_lt, hkToNat,
            UInt64.toNat_ofNat_of_lt' hLeft.size_lt]
          omega
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hNotLt])]
        wp_run_with []
        refine ⟨hLeftLengthBound, ?_⟩
        rw [hLeftAddress, hLeftLengthRead]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hNotLt])]
        subst k
        wp_run_with [List.take_length, Project.F64DotCheckedBits.func0Def]
      · have hkTermsLt : k < (arrayPairTerms left right).length :=
          Nat.lt_of_le_of_ne hkLength hEnd
        have hkLeft : k < left.size := by omega
        have hkRight : k < right.size := by omega
        have hEncodedLt : UInt64.ofNat k < UInt64.ofNat left.size := by
          rw [UInt64.lt_iff_toNat_lt, hkToNat,
            UInt64.toNat_ofNat_of_lt' hLeft.size_lt]
          exact hkLeft
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hEncodedLt])]
        change wp Project.F64DotCheckedBits.«module» _ _ current
          (loopFrame leftPtr rightPtr (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local2 local3 (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local8 local9 local10 local11 local12 local13 local14 leftPtr
            local16 local17 local18 local19 local20 local21) env
        rw [wp_localGet_cons]
        simp only [loopFrame, Locals.get, List.length, Nat.reduceAdd,
          Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
        rw [wp_f64ReinterpretI64_cons]
        simp only
        rw [wp_localGet_cons]
        simp only [loopFrame, Locals.get, List.length, Nat.reduceAdd,
          Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
        rw [wp_localSet_cons]
        simp only [loopFrame, Locals.set?, Function.numParams, List.length,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.set_cons_zero, List.set_cons_succ]
        rw [wp_localGet_cons]
        simp only [loopFrame, Locals.get, List.length, Nat.reduceAdd,
          Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
        rw [wp_localSet_cons]
        simp only [loopFrame, Locals.set?, Function.numParams, List.length,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.set_cons_zero, List.set_cons_succ]
        change wp Project.F64DotCheckedBits.«module»
          (Project.ProofKit.CheckedArrayGet.checkedGetCore 15 16 ++ _)
          _ current
          (loopFrame leftPtr rightPtr (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local2 local3 (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local8 local9 local10 local11 local12 local13 local14 leftPtr
            (UInt64.ofNat k) local17 local18 local19 local20 local21
            [.f64 (Kernels.dot64List
              ((arrayPairTerms left right).take k))]) env
        refine Project.ProofKit.CheckedArrayGet.checkedGetCore_spec
          (pointerLocal := 15) (indexLocal := 16)
          (module_ := Project.F64DotCheckedBits.«module») (env := env)
          (store := current)
          (frame := loopFrame leftPtr rightPtr (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local2 local3 (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local8 local9 local10 local11 local12 local13 local14 leftPtr
            (UInt64.ofNat k) local17 local18 local19 local20 local21
            [.f64 (Kernels.dot64List
              ((arrayPairTerms left right).take k))])
          (pointer := leftPtr) (input := left) (index := k)
          (tail := [.f64 (Kernels.dot64List
            ((arrayPairTerms left right).take k))])
          (hPointer := rfl) (hIndex := rfl) (hValues := rfl)
          (hArray := hLeft) (hIndexBound := hkLeft)
          (Q := _) (rest := _) ?_
        simp only [loopFrame, wp_f64ReinterpretI64_cons]
        rw [wp_localGet_cons]
        simp only [loopFrame, Locals.get, List.length, Nat.reduceAdd,
          Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
        rw [wp_localSet_cons]
        simp only [loopFrame, Locals.set?, Function.numParams, List.length,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.set_cons_zero, List.set_cons_succ]
        rw [wp_localGet_cons]
        simp only [loopFrame, Locals.get, List.length, Nat.reduceAdd,
          Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
        rw [wp_localSet_cons]
        simp only [loopFrame, Locals.set?, Function.numParams, List.length,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.set_cons_zero, List.set_cons_succ]
        change wp Project.F64DotCheckedBits.«module»
          (Project.ProofKit.CheckedArrayGet.checkedGetCore 15 16 ++ _)
          _ current
          (loopFrame leftPtr rightPtr (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local2 local3 (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local8 local9 local10 local11 local12 local13 local14 rightPtr
            (UInt64.ofNat k) local17 local18 local19 local20 local21
            [.f64 left[k], .f64 (Kernels.dot64List
              ((arrayPairTerms left right).take k))]) env
        refine Project.ProofKit.CheckedArrayGet.checkedGetCore_spec
          (pointerLocal := 15) (indexLocal := 16)
          (module_ := Project.F64DotCheckedBits.«module») (env := env)
          (store := current)
          (frame := loopFrame leftPtr rightPtr (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local2 local3 (UInt64.ofNat k)
            (Kernels.dot64List ((arrayPairTerms left right).take k))
            local8 local9 local10 local11 local12 local13 local14 rightPtr
            (UInt64.ofNat k) local17 local18 local19 local20 local21
            [.f64 left[k], .f64 (Kernels.dot64List
              ((arrayPairTerms left right).take k))])
          (pointer := rightPtr) (input := right) (index := k)
          (tail := [.f64 left[k], .f64 (Kernels.dot64List
            ((arrayPairTerms left right).take k))])
          (hPointer := rfl) (hIndex := rfl) (hValues := rfl)
          (hArray := hRight) (hIndexBound := hkRight)
          (Q := _) (rest := _) ?_
        have hPair? :=
          arrayPairTerms_getElem?_of_eq left right k hLength hkLeft
        have hPair :
            (arrayPairTerms left right)[k] = (left[k], right[k]) :=
          Project.Common.getElem_of_some hPair? hkTermsLt
        have hNextAccumulator :
            Wasm.IEEE64.add
                (Kernels.dot64List ((arrayPairTerms left right).take k))
                (Wasm.IEEE64.mul left[k] right[k]) =
              Kernels.dot64List
                ((arrayPairTerms left right).take (k + 1)) := by
          rw [dot64List_take_succ (arrayPairTerms left right) k
            (by omega) hkTermsLt, hPair]
        have hLeftSizeLt : left.size < UInt64.size := hLeft.size_lt
        have hkSuccLt64 : k + 1 < UInt64.size := by omega
        have hkSuccToNat : (UInt64.ofNat (k + 1)).toNat = k + 1 :=
          UInt64.toNat_ofNat_of_lt' hkSuccLt64
        have hkAddToNat : (UInt64.ofNat k + 1).toNat = k + 1 := by
          rw [UInt64.toNat_add, hkToNat]
          have hOne : (1 : UInt64).toNat = 1 := rfl
          rw [hOne, Nat.mod_eq_of_lt hkSuccLt64]
        have hkAdd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat.inj
          rw [hkAddToNat, hkSuccToNat]
        have hkNoWrap : ¬ UInt64.ofNat k + 1 < UInt64.ofNat k := by
          intro hWrap
          rw [UInt64.lt_iff_toNat_lt, hkAddToNat, hkToNat] at hWrap
          omega
        wp_run [loopFrame, Wasm.f64Mul, Wasm.f64Add,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, if_false, if_true,
          List.getElem?_cons_zero, List.getElem?_cons_succ,
          List.set_cons_zero, List.set_cons_succ, hNextAccumulator, hkAdd]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hkNoWrap])]
        wp_run [loopFrame, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
          if_false, if_true, List.getElem?_cons_zero,
          List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
          hNextAccumulator, hkAdd]
        wp_run_with []
        refine ⟨hLeftLengthBound, ?_⟩
        rw [hLeftAddress, hLeftLengthRead]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hEncodedLt])]
        wp_run [loopFrame, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
          if_false, if_true, List.getElem?_cons_zero,
          List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
          hNextAccumulator, hkAdd]
        simp only [List.cons_append, List.nil_append]
        simp only [ne_eq, eq_self, not_true_eq_false, if_false]
        refine ⟨?_, ?_⟩
        · refine ⟨rfl, k + 1, by omega, by omega,
            local2, local3,
            UInt64.ofNat k,
            Kernels.dot64List ((arrayPairTerms left right).take k),
            Kernels.dot64List ((arrayPairTerms left right).take (k + 1)),
            UInt64.ofNat (k + 1), UInt64.ofNat (k + 1),
            Kernels.dot64List ((arrayPairTerms left right).take (k + 1)),
            local12, local13, local14, leftPtr, 1,
            UInt64.ofNat (k + 1), 0, UInt64.ofNat (k + 1),
            Kernels.dot64List ((arrayPairTerms left right).take (k + 1)),
            1, rfl⟩
        · simp [loopMeasure, Locals.get, hkSuccToNat, hkAddToNat, hkToNat]
          omega

#print axioms arrayPairTerms_length_of_eq
#print axioms arrayPairTerms_getElem?_of_eq
#print axioms dot64List_take_succ
#print axioms dot64List_take_one_of_nonempty
#print axioms unequal_lengths_exact
#print axioms equal_empty_exact
#print axioms equal_nonempty_exact

end Project.F64DotCheckedBits.Spec
