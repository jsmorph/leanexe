import Project.ClobLimit.InternalPartialTradeAlloc
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Partial-trade copy

After allocation, the partial-fill branch initializes the extended trade
length and copies every old trade word.  This module proves that loop and its
target-payload memory frame.
-/

namespace Project.ClobLimit.InternalPartialTradeCopy

open Wasm Project.Common Project.Clob Project.ClobLimit

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_trade" "(" hParams:term "," hLocals:term ","
    hValues:term "," hSource:term "," hTotal:term ","
    hLength:term "," hTarget:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hSource), ($hTotal), ($hLength), ($hTarget)])

def partialTradeCopyFrame (base : Locals) (target : UInt64)
    (word : Nat) : Locals :=
  { params := base.params
    locals := (base.locals.set 49 (.i64 target)).set 50
      (.i64 (UInt64.ofNat word))
    values := [] }

def partialTradeCopyInv (st0 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity newLength : UInt64)
    (ts : List TradeL) : AssertionF Unit :=
  fun st s =>
    ∃ word : Nat, word ≤ ts.length * 4 ∧
      s = partialTradeCopyFrame base target word ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        st0.globals.globals.set 2 (.i64 (g2 + 1)) ∧
      FreshFixedArrayAt st target arrayCapacity 4 ∧
      st.mem.read64 target.toUInt32 = newLength ∧
      TradesAt st source ts ∧
      MemEqOutsideFlatWords st0 st target ((ts.length + 1) * 4) ∧
      ∀ copied : Nat, copied < word →
        tradeWord st target copied = tradeWord st0 source copied

def partialTradeCopyMeasure (total : Nat) (_ : Store Unit)
    (s : Locals) : Nat :=
  match s.locals[50]? with
  | some (Value.i64 word) => total - word.toNat
  | _ => 0

def partialTradeCopyBodyProg : Wasm.Program :=
  [
  .localGet 61,
  .localGet 58,
  .geUI64,
  .br_if 1,
  .localGet 60,
  .localGet 61,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 56,
  .localGet 61,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet 61,
  .constI64 1,
  .addI64,
  .localSet 61,
  .br 0
  ]

def partialTradeCopyProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 73,
  .localSet 60,
  .localGet 60,
  .wrapI64,
  .localGet 59,
  .store64 0,
  .constI64 0,
  .localSet 61,
  .block 0 0 [
    .loop 0 0 partialTradeCopyBodyProg
  ]
  ]

set_option Elab.async false in
theorem partialTradeCopyProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity newLength : UInt64)
    (ts : List TradeL)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[45]? = some (.i64 source))
    (hTotalLocal : base.locals[47]? =
      some (.i64 (UInt64.ofNat ts.length * 4)))
    (hLengthLocal : base.locals[48]? = some (.i64 newLength))
    (hTargetLocal : base.locals[62]? = some (.i64 target))
    (hTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTotal64 : ts.length * 4 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : source.toNat + (ts.length * 4 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + ((ts.length + 1) * 4 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + ((ts.length + 1) * 4 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target ((ts.length + 1) * 4))
      (flatWordsRegion source (ts.length * 4)))
    (hg2 : st0.globals.globals[2]? = some (.i64 g2))
    (hFresh : FreshFixedArrayAt st0 target arrayCapacity 4)
    (hTrades : TradesAt st0 source ts)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      partialTradeCopyInv st0 base target source g2 arrayCapacity newLength ts
          st1 (partialTradeCopyFrame base target (ts.length * 4)) →
        wp «module» rest Q st1
          (partialTradeCopyFrame base target (ts.length * 4)) env) :
    wp «module» (partialTradeCopyProg ++ rest) Q st0 base env := by
  have hSourceGet : base.locals[45] = .i64 source := by
    apply Option.some.inj
    calc
      some base.locals[45] = base.locals[45]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 source) := hSourceLocal
  have hTotalGet : base.locals[47] =
      .i64 (UInt64.ofNat ts.length * 4) := by
    apply Option.some.inj
    calc
      some base.locals[47] = base.locals[47]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat ts.length * 4)) := hTotalLocal
  have hLengthGet : base.locals[48] = .i64 newLength := by
    apply Option.some.inj
    calc
      some base.locals[48] = base.locals[48]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 newLength) := hLengthLocal
  have hTargetGet : base.locals[62] = .i64 target := by
    apply Option.some.inj
    calc
      some base.locals[62] = base.locals[62]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 target) := hTargetLocal
  simp only [partialTradeCopyProg, List.cons_append, List.nil_append]
  wp_run_trade (hParams, hLocals, hValues, hSourceGet, hTotalGet,
    hLengthGet, hTargetGet)
  simp only [hg2]
  have hLengthBound : target.toNat % 4294967296 + 8 ≤
      st0.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := partialTradeCopyInv st0 base target source g2 arrayCapacity
      newLength ts)
    (μ := partialTradeCopyMeasure (ts.length * 4))
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [partialTradeCopyFrame]
    · exact Mem.write64_pages ..
    · rfl
    · refine FreshFixedArrayAt.write64_data hFresh hTarget48 ?_
      rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
    · rw [toUInt32_eq_ofNat, Mem.read64_write64_same]
    · have hFrame := hTrades.frame_write64_flatWordsDisjoint hSource32
          hTarget32 (slot := 0) (value := newLength) (by omega) hsep
      simpa only [TradesAt, Nat.zero_mul, Nat.add_zero] using hFrame
    · intro a ha
      rw [write64_bytes_ne _ _ _ (by
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        rcases ha with ha | ha <;> omega)]
    · intro copied hcopied
      omega
  · rintro st1 s1
      ⟨word, hword, rfl, hPages, hGlobals, hFresh1, hLength,
        hTrades1, hOutside, hCopied⟩
    have hwordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [partialTradeCopyBodyProg, partialTradeCopyFrame]
    wp_run_trade (hParams, hLocals, hValues, hSourceGet, hTotalGet,
      hLengthGet, hTargetGet)
    by_cases hwordEnd : word = ts.length * 4
    · have hge : UInt64.ofNat word ≥ UInt64.ofNat ts.length * 4 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hTotalU]
        omega
      rw [if_pos hge]
      try simp
      subst word
      apply hDone
      exact ⟨ts.length * 4, le_rfl, rfl, hPages, hGlobals, hFresh1,
        hLength, hTrades1, hOutside, hCopied⟩
    · have hnge : ¬ UInt64.ofNat word ≥
          UInt64.ofNat ts.length * 4 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hTotalU]
        omega
      rw [if_neg hnge]
      try simp
      have hwordLt : word < ts.length * 4 :=
        Nat.lt_of_le_of_ne hword hwordEnd
      have hsourceBound := hTrades1.tradeWord_bound_flat word hwordLt
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
        · simp only [partialTradeCopyFrame, hwordNext]
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
            hTrades1.frame_write64_flatWordsDisjoint hSource32 hTarget32
              (slot := word + 1)
              (value := st1.mem.read64 (UInt32.ofNat
                ((source.toNat + (word + 1) * 8) % 4294967296)))
              (by omega) hsep
        · exact hOutside.write64 hTarget32 (by omega)
        · intro copied hcopied
          unfold tradeWord
          by_cases hcopiedWord : copied = word
          · subst copied
            rw [Mem.read64_write64_same]
            have hCurrent := hTrades1.tradeWord_eq_flat word hwordLt
            have hInitial := hTrades.tradeWord_eq_flat word hwordLt
            unfold tradeWord at hCurrent hInitial
            exact hCurrent.trans hInitial.symm
          · rw [read64_write64_ne _ _ _ _ (by
                simp only [toUInt32_ofNat_mod_toNat]
                rw [Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt htargetLt]
                omega)]
            have hPrevious := hCopied copied (by omega)
            unfold tradeWord at hPrevious
            exact hPrevious
      · simp [partialTradeCopyMeasure, hLocals, hwordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobLimit.InternalPartialTradeCopy
