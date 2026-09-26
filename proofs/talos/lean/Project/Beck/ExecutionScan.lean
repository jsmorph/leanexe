import Project.Beck.ExecutionScanStep
import Project.Beck.Loop
import Project.ProofKit.BlockLoop
import Project.ProofKit.RangeFoldLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

def frozenInv (initial : Store Unit) (point : Point) (owner pointer : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index scratch,
    index ≤ point.numerators.size ∧ (∀ job < index, frozen point job = true) ∧
      frame = frozenFrame point owner pointer index false scratch

def frozenDone (initial : Store Unit) (point : Point) (owner pointer : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index found scratch,
    allFrozen point = !found ∧ frame = frozenFrame point owner pointer index found scratch

theorem frozenLoop_exact (env : HostEnv Unit) (initial : Store Unit) (point : Point)
    (owner pointer : UInt64) (scratch : ScanScratch)
    (array : UInt64Array.At initial pointer point.numerators)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ index found scratch, allFrozen point = !found →
      wp «module» rest Q initial (frozenFrame point owner pointer index found scratch) env) :
    wp «module» ([.block 0 0 [.loop 0 0 frozenBody]] ++ rest) Q initial
      (frozenFrame point owner pointer 0 false scratch) env := by
  apply BlockLoop.program_spec «module» env initial _ frozenBody
    (frozenInv initial point owner pointer) (frozenDone initial point owner pointer)
    (RangeFoldLoop.measure 25 point.numerators.size)
  · rintro store frame ⟨_, index, scratch, _, _, rfl⟩
    rfl
  · rintro store frame ⟨_, index, found, scratch, _, rfl⟩
    rfl
  · exact ⟨rfl, 0, scratch, by omega, by simp, rfl⟩
  · rintro store frame ⟨same, index, currentScratch, bounded, processed, rfl⟩
    subst store
    have indexFits : index < UInt64.size := lt_of_le_of_lt bounded array.size_lt
    change wp «module» ([.localGet 25, .localGet 26, .geUI64, .br_if 1] ++ frozenBody.drop 4)
      _ initial _ env
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, frozenFrame,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ↓reduceIte, wp_geUI64_cons, wp_br_if_cons]
    by_cases last : index = point.numerators.size
    · subst index
      simp only [show point.numerators.size.toUInt64 ≤ point.numerators.size.toUInt64 from Nat.le_refl _, ↓reduceIte]
      change frozenDone initial point owner pointer initial (frozenFrame point owner pointer point.numerators.size false currentScratch)
      exact ⟨rfl, _, false, currentScratch, (Loop.allFrozen_iff point).mpr processed, rfl⟩
    · have less : index < point.numerators.size := by omega
      have guard : ¬point.numerators.size.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' array.size_lt,
          UInt64.toNat_ofNat_of_lt' indexFits]
        omega
      simp only [ge_iff_le, guard, ↓reduceIte]
      apply frozenStep_exact env initial point owner pointer index currentScratch array less
      · intro currentFrozen
        change frozenInv initial point owner pointer initial _ ∧ _
        refine ⟨⟨rfl, index + 1, _, by omega, ?_, rfl⟩, ?_⟩
        · intro job hj
          by_cases equal : job = index
          · simpa [equal] using currentFrozen
          · exact processed job (by omega)
        · simp only [RangeFoldLoop.measure, frozenFrame, Locals.get, List.length,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
            ↓reduceIte, UInt64.toNat_ofNat_of_lt' indexFits,
            UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by have := array.size_lt; omega)]
          omega
      · intro currentLive
        change frozenDone initial point owner pointer initial _
        refine ⟨rfl, index, true, _, ?_, rfl⟩
        apply Bool.eq_false_iff.mpr
        intro all
        have yes := (Loop.allFrozen_iff point).mp all index less
        simp [currentLive] at yes
  · rintro store frame ⟨rfl, index, found, finalScratch, correct, rfl⟩
    exact next index found finalScratch correct

theorem allFrozen_exact (env : HostEnv Unit) (initial : Store Unit) (point : Point)
    (owner pointer : UInt64) (array : UInt64Array.At initial pointer point.numerators) :
    TerminatesWith env «module» 13 initial (pointValues point owner pointer)
      (fun final values => final = initial ∧ values = [.i64 (boolWord (allFrozen point))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func13Def) rfl ?_
  change wp «module» func13 _ initial
    { params := [.i64 point.denominator, .i64 owner, .i64 pointer], locals := List.replicate 32 (.i64 0) } env
  have lengthRead : initial.mem.read64 (UInt32.ofNat (pointer.toNat % 2 ^ 32)) =
      UInt64.ofNat point.numerators.size := by
    simp only [Nat.reducePow]
    rw [array.pointerAddress_eq]
    exact array.lengthRead
  have lengthBound : (UInt32.ofNat (pointer.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]
    rw [array.pointerAddress_eq]
    exact array.lengthBound
  simp only [func13]
  wp_fixed_frame [lengthRead, lengthBound, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr lengthBound)]
  change wp «module» ([.block 0 0 [.loop 0 0 frozenBody]] ++ func13.drop 17) _ initial
    (frozenFrame point owner pointer 0 false (fun k => if k.val = 19 then .i64 pointer else .i64 0)) env
  apply frozenLoop_exact env initial point owner pointer _ array
  intro index found scratch correct
  cases found <;>
    simp only [func13, List.drop, frozenFrame, boolWord, Bool.false_eq_true, ↓reduceIte]
  all_goals
    repeat' ((try wp_fixed_frame [func13Def, pointValues, correct, boolWord]) <;>
      (refine wp_iff_cons rfl ?_; try simp))

#print axioms allFrozen_exact

end Project.Beck.Execution
