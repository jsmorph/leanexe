import Project.ClobDepth.MissingCopyInvariant
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Missing-price level copy

The missing-price branch copies every old level word into the fresh
stride-two array.  The loop theorem applies the semantic transition from
`MissingCopyInvariant` at each iteration.
-/

namespace Project.ClobDepth.MissingCopy

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.MissingCopyInvariant

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_missing_copy" "(" hParams:term "," hLocals:term ","
    hValues:term "," hSource:term "," hTotal:term ","
    hTarget:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hSource), ($hTotal), ($hTarget)])

set_option Elab.async false in
theorem missingCopyProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (target source capacity : UInt64) (levels : List LevelL)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hSource : base.locals[10]? = some (.i64 source))
    (hTotal : base.locals[12]? =
      some (.i64 (UInt64.ofNat levels.length * 2)))
    (hTarget : base.locals[14]? = some (.i64 target))
    (hTotalU : (UInt64.ofNat levels.length * 2).toNat =
      levels.length * 2)
    (hTotal64 : levels.length * 2 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + ((levels.length + 1) * 2 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + ((levels.length + 1) * 2 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target ((levels.length + 1) * 2))
      (flatWordsRegion source (levels.length * 2)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hInit : CopyInvariant st0 base target source capacity levels st0 base)
    (hDone : ∀ st1,
      CopyInvariant st0 base target source capacity levels st1
        (copyLoopFrame base (levels.length * 2)) →
      wp «module» rest Q st1
        (copyLoopFrame base (levels.length * 2)) env) :
    wp «module» (Entry.missingCopyProg ++ rest) Q st0 base env := by
  have hSource' : base.locals[10] = .i64 source := by
    apply Option.some.inj
    calc
      some base.locals[10] = base.locals[10]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 source) := hSource
  have hTotal' : base.locals[12] =
      .i64 (UInt64.ofNat levels.length * 2) := by
    apply Option.some.inj
    calc
      some base.locals[12] = base.locals[12]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat levels.length * 2)) := hTotal
  have hTarget' : base.locals[14] = .i64 target := by
    apply Option.some.inj
    calc
      some base.locals[14] = base.locals[14]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 target) := hTarget
  simp only [Entry.missingCopyProg, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := CopyInvariant st0 base target source capacity levels)
    (μ := copyMeasure (levels.length * 2))
  · exact hInit
  · rintro st1 s1 ⟨word, hWord, rfl, hState⟩
    have hWordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [Entry.missingCopyBodyProg, copyLoopFrame]
    wp_run_missing_copy
      (hParams, hLocals, hValues, hSource', hTotal', hTarget')
    by_cases hEnd : word = levels.length * 2
    · have hge : UInt64.ofNat word ≥
          UInt64.ofNat levels.length * 2 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hWordU, hTotalU]
        omega
      rw [if_pos hge]
      try simp
      subst word
      apply hDone
      exact ⟨levels.length * 2, le_rfl, rfl, hState⟩
    · have hnge : ¬UInt64.ofNat word ≥
          UInt64.ofNat levels.length * 2 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hWordU, hTotalU]
        omega
      rw [if_neg hnge]
      try simp
      have hWordLt : word < levels.length * 2 :=
        Nat.lt_of_le_of_ne hWord hEnd
      have hSourceBound := hState.sourceCurrent.levelWord_bound_flat
        word hWordLt
      have hTargetLt : target.toNat + (word + 1) * 8 < 4294967296 := by
        omega
      have hTargetBound :
          (target.toNat + (word + 1) * 8) % 4294967296 + 8 ≤
            st1.mem.pages * 65536 := by
        rw [Nat.mod_eq_of_lt hTargetLt, hState.pages]
        omega
      rw [if_neg (Nat.not_lt.mpr hSourceBound),
        if_neg (Nat.not_lt.mpr hTargetBound)]
      refine ⟨?_, ?_⟩
      · have hWordNext : UInt64.ofNat word + 1 =
            UInt64.ofNat (word + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hWordU, size_eq]; omega), hWordU,
            toNat_ofNat_lt (by omega)]
        refine ⟨word + 1, by omega, ?_, ?_⟩
        · simp only [copyLoopFrame, hWordNext]
        · simpa only [copyWriteStore, LevelCopyInvariant.copyWriteStore] using
            hState.advance hWordLt hTarget48 hSource32 hTarget32 hsep
      · simp [copyMeasure, hLocals, hWordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobDepth.MissingCopy
