import Verified.Wasi.SysFlatCall

/-! The result code of a flat call: the loads of the result words that the host left at the
scratch addresses, and the code that pushes words from consecutive locals. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Runtime

theorem resultWords_shift (errno : UInt64) (output : LeanExe.Bytes) :
    ∀ (params : List Param) (outputs : List LeanExe.Bytes) (index : Nat),
    resultWords params ⟨errno, output :: outputs⟩ (index + 1) =
      resultWords params ⟨errno, outputs⟩ index
  | [], _, _ => rfl
  | param :: params, outputs, index => by
    cases param <;>
      simp only [resultWords, Reply.word, List.getElem?_cons_succ,
        resultWords_shift errno output params outputs]

theorem resultBytes_shift (errno : UInt64) (output : LeanExe.Bytes) :
    ∀ (params : List Param) (outputs : List LeanExe.Bytes) (index : Nat),
    resultBytes params ⟨errno, output :: outputs⟩ (index + 1) =
      resultBytes params ⟨errno, outputs⟩ index
  | [], _, _ => rfl
  | param :: params, outputs, index => by
    cases param <;>
      simp only [resultBytes, Reply.bytes, List.getElem?_cons_succ,
        resultBytes_shift errno output params outputs]

theorem resultWords_empty (errno : UInt64) :
    ∀ (params : List Param) (index : Nat),
    resultWords params ⟨errno, []⟩ index = List.replicate (params.countP Param.isResult) 0
  | [], _ => rfl
  | param :: params, index => by
    cases param <;>
      simp [resultWords, Reply.word, Param.isResult, List.countP_cons, List.replicate_succ,
        resultWords_empty errno params]

theorem resultBytes_empty (errno : UInt64) :
    ∀ (params : List Param) (index : Nat),
    resultBytes params ⟨errno, []⟩ index = LeanExe.Bytes.empty
  | [], _ => rfl
  | param :: params, index => by
    cases param <;> simp [resultBytes, Reply.bytes, resultBytes_empty errno params]

theorem resultWords_length (reply : Reply) :
    ∀ (params : List Param) (index : Nat),
    (resultWords params reply index).length = params.countP Param.isResult
  | [], _ => rfl
  | param :: params, index => by
    cases param <;>
      simp [resultWords, Param.isResult, List.countP_cons, resultWords_length reply params]

/-- The code that pushes the words of consecutive locals from `first`. -/
theorem wp_push_words {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {rest : Program} {Q : Assertion α} :
    ∀ (words : List UInt64) (first : Nat) (s : Locals),
    (∀ i, i < words.length → s.get (first + i) = some (.i64 (words.getD i 0))) →
    wp m rest Q st { s with values := (words.map .i64).reverse ++ s.values } env →
    wp m ((List.range words.length).map (fun index => .localGet (first + index)) ++ rest) Q st s
      env
  | [], _, s, _, h => by simpa using h
  | word :: words, first, s, held, h => by
    have hFirst : s.get (first + 0) = some (.i64 word) := by simpa using held 0 (by simp)
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append,
      wp_localGet_cons, hFirst]
    have shifted : ((fun index => Instruction.localGet (first + index)) ∘ Nat.succ) =
        fun index => Instruction.localGet (first + 1 + index) := by
      funext index
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      omega
    rw [shifted]
    refine wp_push_words words (first + 1) _ (fun i hi => ?_) ?_
    · have := held (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    · simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append] using h

/-- Locals that agree with `s` outside `count` positions from `target`. -/
structure LocalsOutside (s s' : Locals) (target count : Nat) : Prop where
  params : s'.params = s.params
  length : s'.locals.length = s.locals.length
  others : ∀ j, j < target ∨ target + count ≤ j → s'.get j = s.get j

/-- The loads of the result words: each result word that the host left at its scratch address
loads into its local as the little-endian value of the reply's output. -/
theorem wp_sys_loads {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {root : UInt32}
    {sizes : List Nat} {errno : UInt64} (hMemory : 16 ≤ st.mem.pages * 65536) :
    ∀ (params : List Param) (values : List UInt64) (slot target : Nat)
      (outputs : List LeanExe.Bytes) (s : Locals) (rest : Program) (Q : Assertion α),
    params.all Param.flatKind = true → params.count .output ≤ 1 →
    slot + 8 * params.countP Param.isResult ≤ 16 →
    ShownAt st.mem (outputRegions params sizes (flatArgs params values)
      (flatPointers params root slot)) outputs →
    outputs.map (fun output => output.data.size) =
      outputSizesOf params sizes (flatArgs params values) →
    s.params.length ≤ target →
    target + params.countP Param.isResult ≤ s.params.length + s.locals.length →
    (∀ s' : Locals, LocalsOutside s s' target (params.countP Param.isResult) →
      (∀ i, i < params.countP Param.isResult →
        s'.get (target + i) = some (.i64 ((resultWords params ⟨errno, outputs⟩ 0).getD i 0))) →
      wp m rest Q st { s' with values := s.values } env) →
    wp m (sysLoadCode params slot target ++ rest) Q st s env
  | [], _, _, target, outputs, s, rest, Q, _, _, _, _, _, _, _, h => by
    simpa [sysLoadCode] using h s ⟨rfl, rfl, fun _ _ => rfl⟩ (fun i hi => by simp at hi)
  | param :: params, values, slot, target, outputs, s, rest, Q, kinds, outputCount, room, shown,
      outputSizes, low, high, h => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input => simp [Param.flatKind] at kinds
    | reported => simp [Param.flatKind] at kinds
    | word32 | word64 | enum32 =>
      simp only [sysLoadCode]
      simp only [flatArgs, flatPointers, outputRegions, outputSizesOf,
        List.tail_cons] at shown outputSizes
      refine wp_sys_loads (errno := errno) hMemory params values.tail slot target outputs s rest Q kinds.2
        (by simpa [List.count_cons] using outputCount)
        (by simpa [Param.isResult, List.countP_cons] using room) shown outputSizes low
        (by simpa [Param.isResult, List.countP_cons] using high) ?_
      intro s' outside held
      exact h s' (by simpa [Param.isResult, List.countP_cons] using outside)
        (by simpa [resultWords, Param.isResult, List.countP_cons] using held)
    | output =>
      simp only [sysLoadCode]
      simp only [flatArgs, flatPointers, outputRegions, outputSizesOf,
        List.tail_cons] at shown outputSizes
      cases outputs with
      | nil => simp [ShownAt] at shown
      | cons output outputs =>
        simp only [ShownAt, ite_true] at shown
        simp only [List.map_cons, List.cons.injEq] at outputSizes
        refine wp_sys_loads (errno := errno) hMemory params values.tail slot target outputs s rest Q kinds.2
          (by simp [List.count_cons] at outputCount; omega)
          (by simpa [Param.isResult, List.countP_cons] using room) shown.2 outputSizes.2 low
          (by simpa [Param.isResult, List.countP_cons] using high) ?_
        intro s' outside held
        refine h s' (by simpa [Param.isResult, List.countP_cons] using outside) ?_
        intro i hi
        rw [resultWords, resultWords_shift]
        exact held i (by simpa [Param.isResult, List.countP_cons] using hi)
    | result32 | result64 =>
      have slotRoom : slot + 8 ≤ 16 := by simp [Param.isResult, List.countP_cons] at room; omega
      have slotNat : (UInt32.ofNat slot).toNat = slot :=
        UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; omega)
      have pointer : (UInt32.ofNat slot).toUInt64.toUInt32 = UInt32.ofNat slot := by
        apply UInt32.toNat_inj.mp
        rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, slotNat, Nat.mod_eq_of_lt (by omega)]
      have targetLow : s.params.length ≤ target := low
      have targetHigh : target < s.params.length + s.locals.length := by
        simp [Param.isResult, List.countP_cons] at high; omega
      simp only [flatArgs, flatPointers, outputRegions, outputSizesOf] at shown outputSizes
      cases outputs with
      | nil => simp [ShownAt] at shown
      | cons output outputs =>
        simp only [ShownAt, ite_true, List.headD_cons] at shown
        simp only [List.map_cons, List.cons.injEq] at outputSizes
        obtain ⟨at_, shown⟩ := shown
        have continue_ : ∀ word : UInt64, word = littleEndian output →
            wp m (sysLoadCode params (slot + 8) (target + 1) ++ rest) Q st
              (setLocal { s with values := s.values } target (.i64 word)) env := by
          intro word wordEq
          have nextLow : (setLocal { s with values := s.values } target (.i64 word)).params.length ≤
              target + 1 := by
            change s.params.length ≤ target + 1
            omega
          have nextHigh : target + 1 + params.countP Param.isResult ≤
              (setLocal { s with values := s.values } target (.i64 word)).params.length +
                (setLocal { s with values := s.values } target (.i64 word)).locals.length := by
            simp only [setLocal, List.length_set]
            simp [Param.isResult, List.countP_cons] at high
            omega
          refine wp_sys_loads (errno := errno) hMemory params values (slot + 8) (target + 1)
            outputs _ rest Q kinds.2 (by simpa [List.count_cons] using outputCount)
            (by simp [Param.isResult, List.countP_cons] at room; omega) shown outputSizes.2
            nextLow nextHigh ?_
          intro s' outside held
          refine h s' ⟨outside.params, ?_, ?_⟩ ?_
          · rw [outside.length]
            simp [setLocal, List.length_set]
          · intro j hj
            rw [outside.others j (by simp [Param.isResult, List.countP_cons] at hj ⊢; omega)]
            rw [Locals.get_setLocal_ne (by simpa using targetLow)
              (by simp [Param.isResult, List.countP_cons] at hj; omega)]
          · intro i hi
            cases i with
            | zero =>
              rw [Nat.add_zero, outside.others target (by omega)]
              simp only [Nat.add_zero, resultWords, Reply.word, List.getElem?_cons_zero,
                Option.map_some, Option.getD_some, List.getD_cons_zero]
              rw [Locals.get_setLocal_same (by simpa using targetLow) (by simpa using targetHigh),
                wordEq]
            | succ i =>
              have := held i (by simp [Param.isResult, List.countP_cons] at hi; omega)
              rw [show target + (i + 1) = target + 1 + i by omega, this]
              simp only [resultWords, resultWords_shift, List.getD_cons_succ]
        first
          | (simp only [sysLoadCode, List.cons_append, wp_const_cons, wp_load32_cons, slotNat,
              UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero, wp_extendUI32_cons]
             rw [ite_eq_right (by omega)]
             refine wp_localSet_local targetLow targetHigh ?_
             exact continue_ _ (by
               rw [← littleEndian_read32 at_ outputSizes.1, pointer]))
          | (simp only [sysLoadCode, List.cons_append, wp_const_cons, wp_load64_cons, slotNat,
              UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
             rw [ite_eq_right (by omega)]
             refine wp_localSet_local targetLow targetHigh ?_
             exact continue_ _ (by
               rw [← littleEndian_read64 at_ outputSizes.1, pointer]))

end Verified.Wasi
