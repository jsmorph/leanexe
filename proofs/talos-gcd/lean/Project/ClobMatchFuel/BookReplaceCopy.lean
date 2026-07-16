import Project.ClobMatchFuel.BookReplaceStore
import Project.ClobMatchFuel.BookErasePrefix
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Partial-fill book copy

The partial-fill branch copies the complete input book into a fresh array
before replacing one order quantity.  This proof covers the post-allocation
counter, length store, copy loop, and structured reconstruction.
-/

namespace Project.ClobMatchFuel.BookReplaceCopy

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_replace" "(" hParams:term "," hLocals:term ","
    hValues:term "," hSource:term "," hLength:term "," hTotal:term ","
    hTarget:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues), ($hSource),
    ($hLength), ($hTotal), ($hTarget)])

def replaceCopyFrame (base : Locals) (target : UInt64) (word : Nat) : Locals :=
  { params := base.params
    locals := (base.locals.set 61 (.i64 target)).set 62
      (.i64 (UInt64.ofNat word))
    values := [] }

def replaceCopyInv (st0 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity : UInt64) (os : List OrderL) :
    AssertionF Unit :=
  fun st s =>
    ∃ word : Nat, word ≤ os.length * 5 ∧
      s = replaceCopyFrame base target word ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        st0.globals.globals.set 2 (.i64 (g2 + 1)) ∧
      FreshOrderArrayAt st target arrayCapacity ∧
      st.mem.read64 target.toUInt32 = UInt64.ofNat os.length ∧
      OrdersAt st source os ∧
      ∀ copied : Nat, copied < word →
        orderWord st target copied = orderWord st0 source copied

def replaceCopyMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[62]? with
  | some (Value.i64 word) => total - word.toNat
  | _ => 0

def replaceCopyBodyProg : Wasm.Program :=
  [
  .localGet 71,
  .localGet 69,
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

def replaceCopyProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 84,
  .localSet 70,
  .localGet 70,
  .wrapI64,
  .localGet 68,
  .store64 0,
  .constI64 0,
  .localSet 71,
  .block 0 0 [
    .loop 0 0 replaceCopyBodyProg
  ]
]

set_option Elab.async false in
theorem replaceCopyProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (target source g2 arrayCapacity : UInt64) (os : List OrderL)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hLengthLocal : base.locals[59]? =
      some (.i64 (UInt64.ofNat os.length)))
    (hTotalLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat os.length * 5)))
    (hTargetLocal : base.locals[75]? = some (.i64 target))
    (hTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hTotal64 : os.length * 5 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : source.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat + (os.length * 5 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint (flatWordsRegion target (os.length * 5))
      (flatWordsRegion source (os.length * 5)))
    (hg2 : st0.globals.globals[2]? = some (.i64 g2))
    (hFresh : FreshOrderArrayAt st0 target arrayCapacity)
    (hOrders : OrdersAt st0 source os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      replaceCopyInv st0 base target source g2 arrayCapacity os st1
          (replaceCopyFrame base target (os.length * 5)) →
        OrdersAt st1 target os →
        wp «module» rest Q st1
          (replaceCopyFrame base target (os.length * 5)) env) :
    wp «module» (replaceCopyProg ++ rest) Q st0 base env := by
  have hSourceGet : base.locals[57] = .i64 source := by
    apply Option.some.inj
    calc
      some base.locals[57] = base.locals[57]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 source) := hSourceLocal
  have hLengthGet : base.locals[59] =
      .i64 (UInt64.ofNat os.length) := by
    apply Option.some.inj
    calc
      some base.locals[59] = base.locals[59]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat os.length)) := hLengthLocal
  have hTotalGet : base.locals[60] =
      .i64 (UInt64.ofNat os.length * 5) := by
    apply Option.some.inj
    calc
      some base.locals[60] = base.locals[60]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat os.length * 5)) := hTotalLocal
  have hTargetGet : base.locals[75] = .i64 target := by
    apply Option.some.inj
    calc
      some base.locals[75] = base.locals[75]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 target) := hTargetLocal
  simp only [replaceCopyProg, List.cons_append, List.nil_append]
  wp_run_replace (hParams, hLocals, hValues, hSourceGet, hLengthGet, hTotalGet,
    hTargetGet)
  simp only [hg2]
  have hLengthBound : target.toNat % 4294967296 + 8 ≤
      st0.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := replaceCopyInv st0 base target source g2 arrayCapacity os)
    (μ := replaceCopyMeasure (os.length * 5))
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [replaceCopyFrame]
    · exact Mem.write64_pages ..
    · rfl
    · refine FreshFixedArrayAt.write64_data hFresh hTarget48 ?_
      rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
    · rw [toUInt32_eq_ofNat, Mem.read64_write64_same]
    · have hFrame := hOrders.frame_write64_flatWordsDisjoint hSource32
          hTarget32 (slot := 0) (value := UInt64.ofNat os.length)
          (by omega) hsep
      simpa only [OrdersAt, Nat.zero_mul, Nat.add_zero] using hFrame
    · intro copied hcopied
      omega
  · rintro st1 s1
      ⟨word, hword, rfl, hPages, hGlobals, hFresh1, hLength, hOrders1,
        hCopied⟩
    have hwordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [replaceCopyBodyProg, replaceCopyFrame]
    wp_run_replace (hParams, hLocals, hValues, hSourceGet, hLengthGet, hTotalGet,
      hTargetGet)
    by_cases hwordEnd : word = os.length * 5
    · have hge : UInt64.ofNat word ≥
          (UInt64.ofNat os.length) * 5 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hTotalU]
        omega
      rw [if_pos hge]
      try simp
      subst word
      apply hDone
      · exact ⟨os.length * 5, le_rfl, rfl, hPages, hGlobals,
          hFresh1, hLength, hOrders1, hCopied⟩
      · apply OrdersAt.ofFlatWords
        · simpa only [toUInt32_eq_ofNat] using hLength
        · rw [Nat.mod_eq_of_lt (by omega), hPages]
          omega
        · intro j hj field hfield
          calc
            orderWord st1 target (j * 5 + field) =
                orderWord st0 source (j * 5 + field) :=
              hCopied (j * 5 + field) (by omega)
            _ = os[j]!.word field :=
              hOrders.orderWord_eq j field hj hfield
        · intro j hj field hfield
          rw [Nat.mod_eq_of_lt (by omega), hPages]
          omega
    · have hnge : ¬ UInt64.ofNat word ≥
          (UInt64.ofNat os.length) * 5 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hwordU, hTotalU]
        omega
      rw [if_neg hnge]
      try simp
      have hwordLt : word < os.length * 5 :=
        Nat.lt_of_le_of_ne hword hwordEnd
      have hsourceBound := hOrders1.orderWord_bound_flat word hwordLt
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
        refine ⟨word + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [replaceCopyFrame, hwordNext]
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
        · intro copied hcopied
          unfold orderWord
          by_cases hcopiedWord : copied = word
          · subst copied
            rw [Mem.read64_write64_same]
            have hCurrent := hOrders1.orderWord_eq_flat word hwordLt
            have hInitial := hOrders.orderWord_eq_flat word hwordLt
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
      · simp [replaceCopyMeasure, hLocals, hwordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobMatchFuel.BookReplaceCopy
