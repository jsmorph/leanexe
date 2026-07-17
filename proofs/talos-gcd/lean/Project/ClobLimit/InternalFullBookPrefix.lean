import Project.ClobLimit.InternalFullBookAlloc
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Full-fill book prefix copy

The full-fill branch stores the smaller book length and copies every flat word
before the matched order.  The loop retains the source book, the fresh target
header, and an outside-target memory frame.  Its copied-word fact supplies the
prefix premise for erased-array reconstruction.
-/

namespace Project.ClobLimit.InternalFullBookPrefix

open Wasm Project.Common Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_prefix" "(" hParams:term "," hLocals:term ","
    hValues:term "," hSource:term "," hPrefix:term ","
    hLength:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hSource), ($hPrefix), ($hLength)])

def prefixCopyFrame (base : Locals)
    (need previous current capacity next target : UInt64)
    (word : Nat) : Locals :=
  { params := base.params
    locals := ((InternalFullBookBump.allocFrame base need previous current
      capacity next target).locals.set 51 (.i64 target)).set 52
        (.i64 (UInt64.ofNat word))
    values := [] }

def prefixCopyInv (st0 : Store Unit) (base : Locals)
    (need previous current capacity next target source g2 arrayCapacity
      newLength : UInt64)
    (os : List OrderL) (targetWords prefixWords : Nat) : AssertionF Unit :=
  fun st s =>
    ∃ word : Nat, word ≤ prefixWords ∧
      s = prefixCopyFrame base need previous current capacity next target
        word ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        st0.globals.globals.set 2 (.i64 (g2 + 1)) ∧
      FreshFixedArrayAt st target arrayCapacity 5 ∧
      st.mem.read64 target.toUInt32 = newLength ∧
      OrdersAt st source os ∧
      MemEqOutsideFlatWords st0 st target targetWords ∧
      ∀ copied : Nat, copied < word →
        orderWord st target copied = orderWord st0 source copied

def prefixCopyMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[52]? with
  | some (Value.i64 word) => total - word.toNat
  | _ => 0

def fullBookPrefixBodyProg : Wasm.Program :=
  [
  .localGet 63,
  .localGet 59,
  .geUI64,
  .br_if 1,
  .localGet 62,
  .localGet 63,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 56,
  .localGet 63,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet 63,
  .constI64 1,
  .addI64,
  .localSet 63,
  .br 0
  ]

def fullBookPrefixProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 71,
  .localSet 62,
  .localGet 62,
  .wrapI64,
  .localGet 61,
  .store64 0,
  .constI64 0,
  .localSet 63,
  .block 0 0 [
    .loop 0 0 fullBookPrefixBodyProg
  ]
  ]

set_option Elab.async false in
theorem fullBookPrefixProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (need previous current capacity next target source g2 arrayCapacity
      newLength : UInt64)
    (os : List OrderL) (targetWords prefixWords : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[45]? = some (.i64 source))
    (hPrefixLocal : base.locals[48]? =
      some (.i64 (UInt64.ofNat prefixWords)))
    (hLengthLocal : base.locals[50]? = some (.i64 newLength))
    (hPrefixU : (UInt64.ofNat prefixWords).toNat = prefixWords)
    (hPrefix64 : prefixWords < UInt64.size)
    (hPrefixTarget : prefixWords ≤ targetWords)
    (hPrefixSource : prefixWords ≤ os.length * 5)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : source.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (targetWords + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat + (targetWords + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint (flatWordsRegion target targetWords)
      (flatWordsRegion source (os.length * 5)))
    (hg2 : st0.globals.globals[2]? = some (.i64 g2))
    (hFresh : FreshFixedArrayAt st0 target arrayCapacity 5)
    (hOrders : OrdersAt st0 source os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      prefixCopyInv st0 base need previous current capacity next target source
          g2 arrayCapacity newLength os targetWords prefixWords st1
          (prefixCopyFrame base need previous current capacity next target
            prefixWords) →
        (∀ copied : Nat, copied < prefixWords →
          orderWord st1 target copied = orderWord st0 source copied) →
        wp «module» rest Q st1
          (prefixCopyFrame base need previous current capacity next target
            prefixWords) env) :
    wp «module» (fullBookPrefixProg ++ rest) Q st0
      (InternalFullBookBump.allocFrame base need previous current capacity
        next target) env := by
  have hSourceGet : base.locals[45] = .i64 source := by
    apply Option.some.inj
    calc
      some base.locals[45] = base.locals[45]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 source) := hSourceLocal
  have hPrefixGet : base.locals[48] =
      .i64 (UInt64.ofNat prefixWords) := by
    apply Option.some.inj
    calc
      some base.locals[48] = base.locals[48]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat prefixWords)) := hPrefixLocal
  have hLengthGet : base.locals[50] = .i64 newLength := by
    apply Option.some.inj
    calc
      some base.locals[50] = base.locals[50]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 newLength) := hLengthLocal
  simp only [fullBookPrefixProg, List.cons_append, List.nil_append,
    InternalFullBookBump.allocFrame]
  wp_run_prefix (hParams, hLocals, hValues, hSourceGet, hPrefixGet,
    hLengthGet)
  simp only [hg2]
  have hLengthBound : target.toNat % 4294967296 + 8 ≤
      st0.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := prefixCopyInv st0 base need previous current capacity next target
      source g2 arrayCapacity newLength os targetWords prefixWords)
    (μ := prefixCopyMeasure prefixWords)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [prefixCopyFrame, InternalFullBookBump.allocFrame, hValues]
    · exact Mem.write64_pages ..
    · rfl
    · refine FreshFixedArrayAt.write64_data hFresh hTarget48 ?_
      rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
    · rw [toUInt32_eq_ofNat, Mem.read64_write64_same]
    · have hFrame := hOrders.frame_write64_flatWordsDisjoint hSource32
          hTarget32 (slot := 0) (value := newLength) (by omega) hsep
      simpa only [OrdersAt, Nat.zero_mul, Nat.add_zero] using hFrame
    · intro a ha
      rw [write64_bytes_ne _ _ _ (by
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        rcases ha with ha | ha <;> omega)]
    · intro copied hcopied
      omega
  · rintro st1 s1
      ⟨word, hword, rfl, hPages, hGlobals, hFresh1, hLength, hOrders1,
        hOutside, hCopied⟩
    have hwordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [fullBookPrefixBodyProg, prefixCopyFrame,
      InternalFullBookBump.allocFrame]
    wp_run_prefix (hParams, hLocals, hValues, hSourceGet, hPrefixGet,
      hLengthGet)
    by_cases hwordEnd : word = prefixWords
    · have hge : UInt64.ofNat word ≥ UInt64.ofNat prefixWords := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hPrefixU]
        omega
      rw [if_pos hge]
      try simp
      subst word
      apply hDone
      · exact ⟨prefixWords, le_rfl, rfl, hPages, hGlobals, hFresh1,
          hLength, hOrders1, hOutside, hCopied⟩
      · exact hCopied
    · have hnge : ¬ UInt64.ofNat word ≥ UInt64.ofNat prefixWords := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hPrefixU]
        omega
      rw [if_neg hnge]
      try simp
      have hwordLt : word < prefixWords :=
        Nat.lt_of_le_of_ne hword hwordEnd
      have hsourceBound := hOrders1.orderWord_bound_flat word (by omega)
      have htargetLt : target.toNat + (word + 1) * 8 < 4294967296 := by
        omega
      have htargetBound :
          (target.toNat + (word + 1) * 8) % 4294967296 + 8 ≤
            st1.mem.pages * 65536 := by
        rw [Nat.mod_eq_of_lt htargetLt, hPages]
        omega
      rw [if_neg (Nat.not_lt.mpr hsourceBound),
        if_neg (Nat.not_lt.mpr htargetBound)]
      refine ⟨?_, ?_⟩
      · have hwordNext : UInt64.ofNat word + 1 =
            UInt64.ofNat (word + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hwordU, size_eq]; omega), hwordU,
            toNat_ofNat_lt (by omega)]
        refine ⟨word + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [prefixCopyFrame, InternalFullBookBump.allocFrame,
            hwordNext]
        · rw [Mem.write64_pages, hPages]
        · exact hGlobals
        · refine FreshFixedArrayAt.write64_data hFresh1 hTarget48 ?_
          rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt htargetLt]
          omega
        · rw [read64_write64_ne _ _ _ _ (by
              simp only [toUInt32_eq_ofNat, toUInt32_ofNat_mod_toNat]
              rw [Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt htargetLt]
              omega)]
          exact hLength
        · simpa only using
            hOrders1.frame_write64_flatWordsDisjoint hSource32 hTarget32
              (slot := word + 1)
              (value := st1.mem.read64 (UInt32.ofNat
                ((source.toNat + (word + 1) * 8) % 4294967296)))
              (by omega) hsep
        · exact hOutside.write64 hTarget32 (by omega)
        · intro copied hcopied
          unfold orderWord
          by_cases hcopiedWord : copied = word
          · subst copied
            rw [Mem.read64_write64_same]
            have hCurrent := hOrders1.orderWord_eq_flat word (by omega)
            have hInitial := hOrders.orderWord_eq_flat word (by omega)
            unfold orderWord at hCurrent hInitial
            exact hCurrent.trans hInitial.symm
          · rw [read64_write64_ne _ _ _ _ (by
                simp only [toUInt32_ofNat_mod_toNat]
                rw [Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt htargetLt]
                omega)]
            have hPrevious := hCopied copied (by omega)
            unfold orderWord at hPrevious
            exact hPrevious
      · simp [prefixCopyMeasure, hLocals, hwordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobLimit.InternalFullBookPrefix
