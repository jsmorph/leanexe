import Project.ClobMatchFuel.BookErasePrefix
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Full-fill book suffix copy

The full-fill suffix loop skips the matched five-word order while copying the
remaining words into the allocated book.  This proof retains the prefix facts
from the preceding phase and reconstructs the exact erased order list.
-/

namespace Project.ClobMatchFuel.BookEraseSuffix

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.BookErasePrefix

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_suffix" "(" hParams:term "," hLocals:term ","
    hSource:term "," hPrefix:term ","
    hSuffix:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals),
    ($hSource), ($hPrefix), ($hSuffix)])

def eraseSuffixInv (st0 : Store Unit) (base : Locals)
    (need previous current capacity next target source g2 arrayCapacity newLength : UInt64)
    (os : List OrderL) (prefixWords suffixWords : Nat) : AssertionF Unit :=
  fun st s =>
    ∃ word : Nat, word ≤ suffixWords ∧
      s = eraseCopyFrame base need previous current capacity next target word ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        st0.globals.globals.set 2 (.i64 (g2 + 1)) ∧
      FreshOrderArrayAt st target arrayCapacity ∧
      st.mem.read64 target.toUInt32 = newLength ∧
      OrdersAt st source os ∧
      (∀ copied : Nat, copied < prefixWords →
        orderWord st target copied = orderWord st0 source copied) ∧
      ∀ copied : Nat, copied < word →
        orderWord st target (prefixWords + copied) =
          orderWord st0 source (prefixWords + 5 + copied)

def eraseSuffixMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[64]? with
  | some (Value.i64 word) => total - word.toNat
  | _ => 0

def eraseResultFrame (base : Locals)
    (need previous current capacity next target : UInt64)
    (suffixWords : Nat) : Locals :=
  { eraseCopyFrame base need previous current capacity next target suffixWords with
    values := [.i64 target] }

def eraseSuffixBodyProg : Wasm.Program :=
  [
  .localGet 73,
  .localGet 70,
  .geUI64,
  .br_if 1,
  .localGet 72,
  .localGet 69,
  .localGet 73,
  .addI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 66,
  .localGet 69,
  .constI64 5,
  .addI64,
  .localGet 73,
  .addI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet 73,
  .constI64 1,
  .addI64,
  .localSet 73,
  .br 0
]

def eraseSuffixProg : Wasm.Program :=
  [
  .constI64 0,
  .localSet 73,
  .block 0 0 [
    .loop 0 0 eraseSuffixBodyProg
  ],
  .localGet 72
]

set_option Elab.async false in
theorem eraseSuffixProg_spec
    (env : HostEnv Unit) (st0 st1 : Store Unit) (base : Locals)
    (need previous current capacity next target source g2 arrayCapacity newLength : UInt64)
    (os : List OrderL) (i targetWords prefixWords suffixWords : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hPrefixLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat prefixWords)))
    (hSuffixLocal : base.locals[61]? =
      some (.i64 (UInt64.ofNat suffixWords)))
    (hPrefixU : (UInt64.ofNat prefixWords).toNat = prefixWords)
    (hSuffixU : (UInt64.ofNat suffixWords).toNat = suffixWords)
    (hSuffix64 : suffixWords < UInt64.size)
    (hi : i < os.length)
    (hPrefixWords : prefixWords = i * 5)
    (hSuffixWords : suffixWords = (os.length - 1 - i) * 5)
    (hTargetWords : targetWords = (os.length - 1) * 5)
    (hNewLength : newLength = UInt64.ofNat (os.length - 1))
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : source.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (targetWords + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat + (targetWords + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint (flatWordsRegion target targetWords)
      (flatWordsRegion source (os.length * 5)))
    (hPages : st1.mem.pages = st0.mem.pages)
    (hGlobals : st1.globals.globals =
      st0.globals.globals.set 2 (.i64 (g2 + 1)))
    (hFresh : FreshOrderArrayAt st1 target arrayCapacity)
    (hLength : st1.mem.read64 target.toUInt32 = newLength)
    (hOrders0 : OrdersAt st0 source os)
    (hOrders1 : OrdersAt st1 source os)
    (hPrefix : ∀ copied : Nat, copied < prefixWords →
      orderWord st1 target copied = orderWord st0 source copied)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st2,
      eraseSuffixInv st0 base need previous current capacity next target source
          g2 arrayCapacity newLength os prefixWords suffixWords st2
          (eraseCopyFrame base need previous current capacity next target
            suffixWords) →
        OrdersAt st2 target (os.eraseIdx i) →
        wp «module» rest Q st2
          (eraseResultFrame base need previous current capacity next target
            suffixWords) env) :
    wp «module» (eraseSuffixProg ++ rest) Q st1
      (eraseCopyFrame base need previous current capacity next target
        prefixWords) env := by
  have hSourceGet : base.locals[57] = .i64 source := by
    apply Option.some.inj
    calc
      some base.locals[57] = base.locals[57]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 source) := hSourceLocal
  have hPrefixGet : base.locals[60] =
      .i64 (UInt64.ofNat prefixWords) := by
    apply Option.some.inj
    calc
      some base.locals[60] = base.locals[60]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat prefixWords)) := hPrefixLocal
  have hSuffixGet : base.locals[61] =
      .i64 (UInt64.ofNat suffixWords) := by
    apply Option.some.inj
    calc
      some base.locals[61] = base.locals[61]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat suffixWords)) := hSuffixLocal
  simp only [eraseSuffixProg, List.cons_append, List.nil_append,
    eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame]
  wp_run_suffix (hParams, hLocals, hSourceGet, hPrefixGet,
    hSuffixGet)
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := eraseSuffixInv st0 base need previous current capacity next target
      source g2 arrayCapacity newLength os prefixWords suffixWords)
    (μ := eraseSuffixMeasure suffixWords)
  · exact ⟨0, Nat.zero_le _, rfl, hPages, hGlobals, hFresh, hLength,
      hOrders1, hPrefix, by
        intro copied hcopied
        omega⟩
  · rintro st2 s2
      ⟨word, hword, rfl, hPages2, hGlobals2, hFresh2, hLength2,
        hOrders2, hPrefix2, hSuffix2⟩
    have hwordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [eraseSuffixBodyProg, eraseCopyFrame,
      BookAllocSearch.bookAllocSearchFrame]
    wp_run_suffix (hParams, hLocals, hSourceGet, hPrefixGet,
      hSuffixGet)
    by_cases hwordEnd : word = suffixWords
    · have hge : UInt64.ofNat word ≥ UInt64.ofNat suffixWords := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hSuffixU]
        omega
      rw [if_pos hge]
      try simp
      subst word
      apply hDone
      · exact ⟨suffixWords, le_rfl, rfl, hPages2, hGlobals2, hFresh2,
          hLength2, hOrders2, hPrefix2, hSuffix2⟩
      · apply OrdersAt.eraseIdx_ofFlatWords hi hOrders0
        · simpa only [toUInt32_eq_ofNat, hNewLength] using hLength2
        · rw [Nat.mod_eq_of_lt (by omega), hPages2]
          omega
        · intro j hj field hfield
          have hcopy := hPrefix2 (j * 5 + field) (by
            rw [hPrefixWords]
            omega)
          exact hcopy
        · intro j hji hj field hfield
          have hcopy := hSuffix2 ((j - i) * 5 + field) (by
            rw [hSuffixWords]
            omega)
          have hdst : i * 5 + ((j - i) * 5 + field) =
              j * 5 + field := by omega
          have hsrc : i * 5 + 5 + ((j - i) * 5 + field) =
              (j + 1) * 5 + field := by omega
          rw [hPrefixWords, hdst, hsrc] at hcopy
          exact hcopy
        · intro j hj field hfield
          rw [Nat.mod_eq_of_lt (by
            rw [hTargetWords] at hTarget32
            omega), hPages2]
          rw [hTargetWords] at hTargetFit
          omega
    · have hnge : ¬ UInt64.ofNat word ≥ UInt64.ofNat suffixWords := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hSuffixU]
        omega
      rw [if_neg hnge]
      try simp
      have hwordLt : word < suffixWords :=
        Nat.lt_of_le_of_ne hword hwordEnd
      have hsourceWord : prefixWords + 5 + word < os.length * 5 := by
        rw [hSuffixWords] at hwordLt
        rw [hPrefixWords]
        omega
      have hsourceBound :=
        hOrders2.orderWord_bound_flat (prefixWords + 5 + word) hsourceWord
      have htargetLt :
          target.toNat + (prefixWords + word + 1) * 8 < 4294967296 := by
        rw [hPrefixWords, hSuffixWords, hTargetWords] at *
        omega
      have htargetBound :
          (target.toNat + (prefixWords + word + 1) * 8) %
              4294967296 + 8 ≤ st2.mem.pages * 65536 := by
        rw [Nat.mod_eq_of_lt htargetLt, hPages2]
        rw [hPrefixWords, hSuffixWords, hTargetWords] at *
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
        · simp only [eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
            hwordNext]
        · rw [Mem.write64_pages, hPages2]
        · exact hGlobals2
        · refine FreshFixedArrayAt.write64_data hFresh2 hTarget48 ?_
          rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt htargetLt]
          omega
        · rw [read64_write64_ne _ _ _ _ (by
              simp only [toUInt32_eq_ofNat, toUInt32_ofNat_mod_toNat]
              rw [Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt htargetLt]
              omega)]
          exact hLength2
        · simpa only using
            hOrders2.frame_write64_flatWordsDisjoint hSource32 hTarget32
              (slot := prefixWords + word + 1)
              (value := st2.mem.read64 (UInt32.ofNat
                ((source.toNat + (prefixWords + 5 + word + 1) * 8) %
                  4294967296)))
              (by
                rw [hPrefixWords, hSuffixWords, hTargetWords] at *
                omega) hsep
        · intro copied hcopied
          unfold orderWord
          rw [read64_write64_ne _ _ _ _ (by
            simp only [toUInt32_ofNat_mod_toNat]
            rw [Nat.mod_eq_of_lt (by
                rw [hPrefixWords, hSuffixWords, hTargetWords] at *
                omega), Nat.mod_eq_of_lt htargetLt]
            omega)]
          have hPrevious := hPrefix2 copied hcopied
          unfold orderWord at hPrevious
          exact hPrevious
        · intro copied hcopied
          unfold orderWord
          by_cases hcopiedWord : copied = word
          · subst copied
            rw [Mem.read64_write64_same]
            have hCurrent := hOrders2.orderWord_eq_flat
              (prefixWords + 5 + word) hsourceWord
            have hInitial := hOrders0.orderWord_eq_flat
              (prefixWords + 5 + word) hsourceWord
            unfold orderWord at hCurrent hInitial
            exact hCurrent.trans hInitial.symm
          · rw [read64_write64_ne _ _ _ _ (by
                simp only [toUInt32_ofNat_mod_toNat]
                rw [Nat.mod_eq_of_lt (by
                    rw [hPrefixWords, hSuffixWords, hTargetWords] at *
                    omega), Nat.mod_eq_of_lt htargetLt]
                omega)]
            have hPrevious := hSuffix2 copied (by omega)
            unfold orderWord at hPrevious
            exact hPrevious
      · simp [eraseSuffixMeasure, hLocals, hwordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobMatchFuel.BookEraseSuffix
