import Project.Beck.ExecutionContainsStep
import Project.Beck.Basis
import Project.ProofKit.BlockLoop
import Project.ProofKit.RangeFoldLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

def containsInv (initial : Store Unit) (xs : Array UInt64) (owner pointer value : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index scratch,
    index ≤ xs.size ∧ (∀ job < index, xs[job]! ≠ value) ∧
      frame = containsFrame xs owner pointer value index false scratch

def containsDone (initial : Store Unit) (xs : Array UInt64) (owner pointer value : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index found scratch,
    contains xs value = found ∧ frame = containsFrame xs owner pointer value index found scratch

theorem containsLoop_exact (env : HostEnv Unit) (initial : Store Unit) (xs : Array UInt64)
    (owner pointer value : UInt64) (scratch : ContainsScratch)
    (array : UInt64Array.At initial pointer xs)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ index found scratch, contains xs value = found →
      wp «module» rest Q initial (containsFrame xs owner pointer value index found scratch) env) :
    wp «module» ([.block 0 0 [.loop 0 0 containsBody]] ++ rest) Q initial
      (containsFrame xs owner pointer value 0 false scratch) env := by
  apply BlockLoop.program_spec «module» env initial _ containsBody
    (containsInv initial xs owner pointer value) (containsDone initial xs owner pointer value)
    (RangeFoldLoop.measure 17 xs.size)
  · rintro store frame ⟨_, index, scratch, _, _, rfl⟩
    rfl
  · rintro store frame ⟨_, index, found, scratch, _, rfl⟩
    rfl
  · exact ⟨rfl, 0, scratch, by omega, by simp, rfl⟩
  · rintro store frame ⟨same, index, currentScratch, bounded, processed, rfl⟩
    subst store
    have indexFits : index < UInt64.size := lt_of_le_of_lt bounded array.size_lt
    change wp «module» ([.localGet 17, .localGet 18, .geUI64, .br_if 1] ++ containsBody.drop 4)
      _ initial _ env
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, containsFrame,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ↓reduceIte, wp_geUI64_cons, wp_br_if_cons]
    by_cases last : index = xs.size
    · subst index
      simp only [show xs.size.toUInt64 ≤ xs.size.toUInt64 from Nat.le_refl _, ↓reduceIte]
      change containsDone initial xs owner pointer value initial (containsFrame xs owner pointer value xs.size false currentScratch)
      exact ⟨rfl, _, false, currentScratch, (Basis.contains_false_iff xs value).mpr processed, rfl⟩
    · have less : index < xs.size := by omega
      have guard : ¬xs.size.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' array.size_lt,
          UInt64.toNat_ofNat_of_lt' indexFits]
        omega
      simp only [ge_iff_le, guard, ↓reduceIte]
      apply containsStep_exact env initial xs owner pointer value index currentScratch array less
      · intro absent
        change containsInv initial xs owner pointer value initial _ ∧ _
        refine ⟨⟨rfl, index + 1, _, by omega, ?_, rfl⟩, ?_⟩
        · intro job hj
          by_cases equal : job = index
          · subst job
            simpa only [getElem!_pos xs index less] using absent
          · exact processed job (by omega)
        · simp only [RangeFoldLoop.measure, containsFrame, Locals.get, List.length,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
            ↓reduceIte, UInt64.toNat_ofNat_of_lt' indexFits,
            UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by have := array.size_lt; omega)]
          omega
      · intro present
        change containsDone initial xs owner pointer value initial _
        refine ⟨rfl, index, true, _, ?_, rfl⟩
        cases absent : contains xs value with
        | false =>
          have different := (Basis.contains_false_iff xs value).mp absent index less
          exact False.elim (different (by simpa only [getElem!_pos xs index less] using present))
        | true => rfl
  · rintro store frame ⟨rfl, index, found, finalScratch, correct, rfl⟩
    exact next index found finalScratch correct

theorem contains_exact (env : HostEnv Unit) (initial : Store Unit) (xs : Array UInt64)
    (owner pointer value : UInt64) (array : UInt64Array.At initial pointer xs) :
    TerminatesWith env «module» 20 initial [.i64 value, .i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (contains xs value))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func20Def) rfl ?_
  change wp «module» func20 _ initial
    { params := [.i64 owner, .i64 pointer, .i64 value], locals := List.replicate 26 (.i64 0) } env
  have lengthRead : initial.mem.read64 (UInt32.ofNat (pointer.toNat % 2 ^ 32)) =
      UInt64.ofNat xs.size := by
    simp only [Nat.reducePow]
    rw [array.pointerAddress_eq]
    exact array.lengthRead
  have lengthBound : (UInt32.ofNat (pointer.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]
    rw [array.pointerAddress_eq]
    exact array.lengthBound
  simp only [func20]
  wp_fixed_frame [lengthRead, lengthBound, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr lengthBound)]
  change wp «module» ([.block 0 0 [.loop 0 0 containsBody]] ++ func20.drop 17) _ initial
    (containsFrame xs owner pointer value 0 false (fun k => if k.val = 11 then .i64 pointer else .i64 0)) env
  apply containsLoop_exact env initial xs owner pointer value _ array
  intro index found scratch correct
  cases found <;>
    simp only [func20, List.drop, containsFrame, boolWord, Bool.false_eq_true, ↓reduceIte]
  all_goals
    repeat' ((try wp_fixed_frame [func20Def, correct, boolWord]) <;>
      (refine wp_iff_cons rfl ?_; try simp))

#print axioms contains_exact

end Project.Beck.Execution
