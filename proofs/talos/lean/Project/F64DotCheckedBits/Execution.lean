import Project.F64DotCheckedBits.Program
import Project.F64DotCheckedBits.Numerical
import Project.ProofKit.Array
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
    (scratch : Fin 18 → UInt64) : Locals :=
  { params := [.i64 leftPtr, .i64 rightPtr],
    locals :=
      [.i64 (scratch 0), .i64 (scratch 1),
       .i64 index, .i64 accumulator,
       .i64 (scratch 2), .i64 (scratch 3), .i64 (scratch 4),
       .i64 (scratch 5), .i64 (scratch 6), .i64 (scratch 7),
       .i64 (scratch 8), .i64 (scratch 9), .i64 (scratch 10),
       .i64 (scratch 11), .i64 (scratch 12), .i64 (scratch 13),
       .i64 (scratch 14), .i64 (scratch 15), .i64 (scratch 16),
       .i64 (scratch 17)],
    values := [] }

/-- At loop entry, `k` pairs have been consumed and local 5 is exactly the
modeled result for that nonempty prefix. -/
private def loopInvariant (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (terms : List (UInt64 × UInt64)) :
    AssertionF Unit :=
  fun current frame =>
    current = initial ∧
      ∃ k : Nat, 1 ≤ k ∧ k ≤ terms.length ∧
        ∃ scratch : Fin 18 → UInt64,
          frame = loopFrame leftPtr rightPtr (UInt64.ofNat k)
            (Kernels.dot64List (terms.take k)) scratch

/-- The number of input pairs still unconsumed by the generated loop. -/
private def loopMeasure (terms : List (UInt64 × UInt64))
    (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 4 with
  | some (.i64 index) => terms.length - index.toNat
  | _ => 0

#print axioms arrayPairTerms_length_of_eq
#print axioms arrayPairTerms_getElem?_of_eq
#print axioms dot64List_take_succ
#print axioms unequal_lengths_exact
#print axioms equal_empty_exact

end Project.F64DotCheckedBits.Spec
