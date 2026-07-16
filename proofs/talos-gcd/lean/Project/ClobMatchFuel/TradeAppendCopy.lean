import Project.ClobMatchFuel.BookReplaceFinish
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Matched-trade prefix copy

Each successful match copies the existing trade array into a fresh array before
storing one appended trade.  This proof covers the post-allocation counter,
length store, and complete old-trade prefix copy.
-/

namespace Project.ClobMatchFuel.TradeAppendCopy

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation

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

def tradeCopyFrame (base : Locals) (target : UInt64) (word : Nat) : Locals :=
  { params := base.params
    locals := (base.locals.set 61 (.i64 target)).set 62
      (.i64 (UInt64.ofNat word))
    values := [] }

def tradeCopyInv (st0 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity newLength : UInt64)
    (ts : List TradeL) : AssertionF Unit :=
  fun st s =>
    ∃ word : Nat, word ≤ ts.length * 4 ∧
      s = tradeCopyFrame base target word ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        st0.globals.globals.set 2 (.i64 (g2 + 1)) ∧
      FreshTradeArrayAt st target arrayCapacity ∧
      st.mem.read64 target.toUInt32 = newLength ∧
      TradesAt st source ts ∧
      MemEqOutsideFlatWords st0 st target ((ts.length + 1) * 4) ∧
      ∀ copied : Nat, copied < word →
        tradeWord st target copied = tradeWord st0 source copied

def tradeCopyMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[62]? with
  | some (Value.i64 word) => total - word.toNat
  | _ => 0

def tradeCopyBodyProg : Wasm.Program :=
  [
  .localGet 71,
  .localGet 68,
  .geUI64,
  .br_if 1,
  .localGet 70,
  .localGet 71,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 66,
  .localGet 71,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet 71,
  .constI64 1,
  .addI64,
  .localSet 71,
  .br 0
]

def tradeCopyProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 83,
  .localSet 70,
  .localGet 70,
  .wrapI64,
  .localGet 69,
  .store64 0,
  .constI64 0,
  .localSet 71,
  .block 0 0 [
    .loop 0 0 tradeCopyBodyProg
  ]
]

set_option Elab.async false in
theorem tradeCopyProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity newLength : UInt64)
    (ts : List TradeL)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hTotalLocal : base.locals[59]? =
      some (.i64 (UInt64.ofNat ts.length * 4)))
    (hLengthLocal : base.locals[60]? = some (.i64 newLength))
    (hTargetLocal : base.locals[74]? = some (.i64 target))
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
    (hFresh : FreshTradeArrayAt st0 target arrayCapacity)
    (hTrades : TradesAt st0 source ts)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      tradeCopyInv st0 base target source g2 arrayCapacity newLength ts st1
        (tradeCopyFrame base target (ts.length * 4)) →
      wp «module» rest Q st1
        (tradeCopyFrame base target (ts.length * 4)) env) :
    wp «module» (tradeCopyProg ++ rest) Q st0 base env := by
  have hSourceGet : base.locals[57] = .i64 source := by
    apply Option.some.inj
    calc
      some base.locals[57] = base.locals[57]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 source) := hSourceLocal
  have hTotalGet : base.locals[59] =
      .i64 (UInt64.ofNat ts.length * 4) := by
    apply Option.some.inj
    calc
      some base.locals[59] = base.locals[59]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat ts.length * 4)) := hTotalLocal
  have hLengthGet : base.locals[60] = .i64 newLength := by
    apply Option.some.inj
    calc
      some base.locals[60] = base.locals[60]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 newLength) := hLengthLocal
  have hTargetGet : base.locals[74] = .i64 target := by
    apply Option.some.inj
    calc
      some base.locals[74] = base.locals[74]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 target) := hTargetLocal
  simp only [tradeCopyProg, List.cons_append, List.nil_append]
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
    (Inv := tradeCopyInv st0 base target source g2 arrayCapacity newLength ts)
    (μ := tradeCopyMeasure (ts.length * 4))
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [tradeCopyFrame]
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
    simp only [tradeCopyBodyProg, tradeCopyFrame]
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
        · simp only [tradeCopyFrame, hwordNext]
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
      · simp [tradeCopyMeasure, hLocals, hwordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobMatchFuel.TradeAppendCopy
