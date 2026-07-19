import Project.LebU32.Defs
import Project.LebU32.Copy

/-!
# The allocation continuation of the final-byte iteration

Split from `posIterLemma` at the state after the five header writes.  In
the parent proof the goal at this point is internally large, and context
extension or constructor splitting there stalls the elaborator.  This
lemma restates that goal from scratch, so the bound conjuncts and the
copy-loop phase elaborate against a term of ordinary size.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem posIterAllocWp (env : HostEnv Unit) (st st1 : Store Unit)
    (n g0 g2 : UInt64) (k : Nat) (v : UInt64) (written : List UInt8)
    (e : Nat → UInt64) (m0 : Nat) (POST : Assertion Unit)
    (hn32 : n.toNat < 4294967296)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hL5 : (lebList 10 n).length ≤ 5)
    (hsplit : lebList 10 n = written ++ lebList (10 - k) v)
    (hwlen : written.length = k)
    (hkL : k < (lebList 10 n).length)
    (hrest : v / 128 = 0)
    (hm0 : 2 * (10 - k) + 1 ≤ m0)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hFT : ∀ (st' : Store Unit) (s' : Locals),
      lInv st n g0 g2 st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } ∧
      lMeasure st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } <
        m0 →
      POST (.Fallthrough st' s'))
    (hkU : (UInt64.ofNat k).toNat = k)
    (hcap8 : (UInt64.ofNat k + 1 + 7) / 8 * 8 = 8)
    (h56k : (g0 + UInt64.ofNat (56 * k)).toNat = g0.toNat + 56 * k)
    (h56kM : (56 * UInt64.ofNat k).toNat = 56 * k)
    (hnewtopN : (g0 + 56 * UInt64.ofNat k + 48 + 8).toNat =
      g0.toNat + 56 * k + 56)
    (h56kN : (g0 + 56 * UInt64.ofNat k).toNat = g0.toNat + 56 * k)
    (hno_wrap : ¬ (g0 + 56 * UInt64.ofNat k + 48 + 8 <
      g0 + 56 * UInt64.ofNat k))
    (hle_wrap : g0 + 56 * UInt64.ofNat k ≤
      g0 + 56 * UInt64.ofNat k + 48 + 8)
    (hsub1T : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1).toNat =
      g0.toNat + 56 * k + 55)
    (hp32L : ((UInt32.ofNat st.mem.pages).toUInt64).toNat = st.mem.pages)
    (hgeM : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1 ≤
      (UInt32.ofNat st.mem.pages).toUInt64)
    (h48kN : (g0 + 56 * UInt64.ofNat k + 48).toNat = g0.toNat + 56 * k + 48)
    (hsubHdr : ∀ (c : UInt64), c.toNat ≤ 48 →
      (g0 + 56 * UInt64.ofNat k + 48 - c).toNat =
        g0.toNat + 56 * k + 48 - c.toNat)
    (hs40 : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat = g0.toNat + 56 * k + 8)
    (hs32 : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat = g0.toNat + 56 * k + 16)
    (hs24 : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat = g0.toNat + 56 * k + 24)
    (hs16 : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat = g0.toNat + 56 * k + 32)
    (hs8 : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat = g0.toNat + 56 * k + 40)
    (hs40m : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat % 4294967296 =
      g0.toNat + 56 * k + 8)
    (hs32m : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat % 4294967296 =
      g0.toNat + 56 * k + 16)
    (hs24m : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat % 4294967296 =
      g0.toNat + 56 * k + 24)
    (hs16m : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat % 4294967296 =
      g0.toNat + 56 * k + 32)
    (hs8m : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat % 4294967296 =
      g0.toNat + 56 * k + 40)
    (hs0m : (g0.toNat + 56 * k) % 4294967296 = g0.toNat + 56 * k)
    (hcap : ¬ (UInt64.ofNat k + 1 + 7) / 8 * 8 < 8)
    (hbytes : ∀ i < k,
      st1.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!)
    (hlen : st1.globals.globals.length = st.globals.globals.length)
    (h0L : st1.globals.globals[0]? = some (.i64 (g0 + UInt64.ofNat (56 * k))))
    (h1L : st1.globals.globals[1]? = some (.i64 0))
    (h2L : st1.globals.globals[2]? = some (.i64 (g2 + UInt64.ofNat k)))
    (h3L : st1.globals.globals[3]? = st.globals.globals[3]?)
    (h4L : st1.globals.globals[4]? = st.globals.globals[4]?)
    (h5L : st1.globals.globals[5]? = st.globals.globals[5]?)
    (hpgL : st1.mem.pages = st.mem.pages)
    (hloL : ∀ a < g0.toNat, st1.mem.bytes a = st.mem.bytes a) :
    wp «module»
      [Instruction.block 0 0
          [Instruction.loop 0 0
              [Instruction.localGet 30, Instruction.localGet 26,
                Instruction.geUI64, Instruction.br_if 1,
                Instruction.localGet 28, Instruction.localGet 30,
                Instruction.addI64, Instruction.wrapI64,
                Instruction.localGet 25, Instruction.localGet 30,
                Instruction.addI64, Instruction.wrapI64,
                Instruction.load8U 0, Instruction.store8 0,
                Instruction.localGet 30, Instruction.constI64 1,
                Instruction.addI64, Instruction.localSet 30,
                Instruction.br 0]],
        Instruction.localGet 28, Instruction.localGet 26,
        Instruction.addI64, Instruction.wrapI64, Instruction.localGet 27,
        Instruction.wrapI64, Instruction.store8 0, Instruction.localGet 28,
        Instruction.localSet 12, Instruction.localGet 12,
        Instruction.localSet 5, Instruction.localGet 12,
        Instruction.localSet 6, Instruction.localGet 11,
        Instruction.constI64 1, Instruction.addI64, Instruction.localSet 7,
        Instruction.constI64 1, Instruction.localSet 8]
      POST
      { globals :=
          { globals :=
              (st1.globals.globals.set 0
                (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8))).set 2
                (.i64 (g2 + UInt64.ofNat k + 1)) },
        mem :=
          (((((st1.mem.write64
            (UInt32.ofNat ((g0.toNat + 56 * k) % 4294967296))
            5501223100278326855).write64
            (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 40).toNat %
              4294967296)) 1).write64
            (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 32).toNat %
              4294967296)) 8).write64
            (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 24).toNat %
              4294967296)) 0).write64
            (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 16).toNat %
              4294967296)) 0).write64
            (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 8).toNat %
              4294967296)) 0,
        extraMems := st1.extraMems, dataSegments := st1.dataSegments,
        tables := st1.tables, elementSegments := st1.elementSegments,
        exns := st1.exns, gcHeap := st1.gcHeap, host := st1.host }
      { params :=
          [Value.i64 (UInt64.ofNat (10 - k)), Value.i64 v,
            Value.i64 (bufPtr g0 k), Value.i64 (bufPtr g0 k),
            Value.i64 (UInt64.ofNat k)],
        locals :=
          [Value.i64 0, Value.i64 0, Value.i64 0, Value.i64 0,
            Value.i64 (v % 128 &&& 255), Value.i64 (bufPtr g0 k),
            Value.i64 (UInt64.ofNat k), Value.i64 (e 12), Value.i64 (e 13),
            Value.i64 (e 14), Value.i64 (e 15), Value.i64 (e 16),
            Value.i64 (e 17), Value.i64 (e 18), Value.i64 (e 19),
            Value.i64 (e 20), Value.i64 (e 21), Value.i64 (e 22),
            Value.i64 (e 23), Value.i64 (e 24), Value.i64 (bufPtr g0 k),
            Value.i64 (UInt64.ofNat k), Value.i64 (v % 128 &&& 255),
            Value.i64 (g0 + 56 * UInt64.ofNat k + 48),
            Value.i64 (UInt64.ofNat k + 1), Value.i64 0, Value.i64 8,
            Value.i64 0, Value.i64 0,
            Value.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8),
            Value.i64 ((g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1),
            Value.i64 (g0 + 56 * UInt64.ofNat k + 48)],
        values := [] }
      env := by
  try simp only [h2L]
  try wp_run
  try simp [hTrap]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun stC sC =>
      ∃ j : Nat, j ≤ k ∧
        sC = cFramePos g0 v k j e ∧
        stC.globals.globals =
          (st1.globals.globals.set 0
            (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8))).set 2
            (.i64 (g2 + UInt64.ofNat k + 1)) ∧
        stC.mem.pages = st1.mem.pages ∧
        (∀ i : Nat, i < j →
          stC.mem.bytes (g0.toNat + 56 * k + 48 + i) =
            written[i]!) ∧
        (∀ i : Nat, i < k →
          stC.mem.bytes (objBase g0 (k - 1) + 48 + i) =
            written[i]!) ∧
        (∀ a : Nat, a < g0.toNat →
          stC.mem.bytes a = st.mem.bytes a))
    (μ := fun _ sC =>
      match sC.locals with
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
          _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
          _ :: _ :: _ :: _ :: .i64 l30 :: _ =>
          k + 1 - l30.toNat
      | _ => 0)
  · refine ⟨0, Nat.zero_le _, by simp [cFramePos], rfl, ?_, ?_,
      ?_, ?_⟩
    · simp [Mem.write64_pages]
    · intro i hi
      omega
    · intro i hi
      dsimp only
      rw [write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs8m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs16m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs24m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs32m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs40m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs0m]
          try simp only [objBase]
          omega)]
      exact hbytes i hi
    · intro a ha
      dsimp only
      rw [write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs8m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs16m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs24m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs32m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs40m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs0m]
          try simp only [objBase]
          omega)]
      exact hloL a ha
  · rintro stC sC ⟨j, hjk, rfl, hglC, hpgC, hdst, hsrc, hloC⟩
    have hjU : (UInt64.ofNat j).toNat = j := by u64_omega
    by_cases hjend : j = k
    · subst hjend
      simp only [cFramePos]
      wp_run
      try simp [hTrap]
      have hk9 : j ≤ 9 := by omega
      have hg0b : g0.toNat < 4294967296 := by omega
      have hpgCL : stC.mem.pages = st.mem.pages := hpgC.trans hpgL
      have hbaseN : (g0 + 56 * UInt64.ofNat j + 48).toNat =
          g0.toNat + 56 * j + 48 := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
          show (48 : UInt64).toNat = 48 from rfl,
          show (56 : UInt64).toNat = 56 from rfl]
        have hs : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
        omega
      have hnw : g0.toNat + 56 * j + 48 + j < 4294967296 := by omega
      have hbuf1 : bufPtr g0 (j + 1) = g0 + 56 * UInt64.ofNat j + 48 := by
        unfold bufPtr objBase
        rw [if_neg (by omega), Nat.add_sub_cancel]
        apply UInt64.toNat.inj
        rw [hbaseN, toNat_ofNat_lt (n := g0.toNat + 56 * j + 48)
          (by rw [size_eq]; omega)]
      have hkadd : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) := by
        apply UInt64.toNat.inj
        rw [toNat_add_one, hkU,
          toNat_ofNat_lt (by rw [size_eq]; omega)]
        try rw [hkU, size_eq]
        try omega
      have hbyte : UInt8.ofNat ((v.toNat % 128 &&& 255) % 4294967296) =
          (v % 128).toUInt8 := by
        have hb : (v.toNat % 128 &&& 255) % 4294967296 = v.toNat % 128 := by
          rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod]
          omega
        apply UInt8.toNat.inj
        rw [hb]
        simp only [UInt8.toNat_ofNat', UInt64.toUInt8, UInt64.toNat_mod,
          show (128 : UInt64).toNat = 128 from rfl]
        try omega
      have hfinal : lebList (10 - j) v = [(v % 128).toUInt8] := by
        rw [show 10 - j = (9 - j) + 1 from by omega]
        exact lebList_final _ _ hrest
      have hgetl : ∀ i : Nat, i < j →
          (written ++ [(v % 128).toUInt8])[i]! = written[i]! := by
        intro i hi
        rw [getElem_bang _ _ (by simp; omega),
          getElem_bang _ _ (by omega)]
        exact List.getElem_append_left (by omega)
      have hgetk : (written ++ [(v % 128).toUInt8])[j]! =
          (v % 128).toUInt8 := by
        rw [getElem_bang _ _ (by simp; omega)]
        exact List.getElem_concat_length hwlen.symm _
      have hnw : g0.toNat + 56 * j + 48 + j < 4294967296 := by omega
      refine ⟨by
        rw [Nat.mod_eq_of_lt hnw]
        rw [show stC.mem.pages = st.mem.pages from hpgCL]
        omega, ?_⟩
      apply hFT
      constructor
      · refine ⟨j + 1, v, written ++ [(v % 128).toUInt8], true,
          (fun i =>
            if i = 1 then v
            else if i = 2 then bufPtr g0 j
            else if i = 3 then bufPtr g0 j
            else if i = 4 then UInt64.ofNat j
            else if i = 9 then v % 128 &&& 255
            else if i = 10 then bufPtr g0 j
            else if i = 11 then UInt64.ofNat j
            else if i = 12 then g0 + 56 * UInt64.ofNat j + 48
            else if i = 25 then bufPtr g0 j
            else if i = 26 then UInt64.ofNat j
            else if i = 27 then v % 128 &&& 255
            else if i = 28 then g0 + 56 * UInt64.ofNat j + 48
            else if i = 29 then UInt64.ofNat j + 1
            else if i = 30 then UInt64.ofNat j
            else if i = 31 then 8
            else if i = 32 then 0
            else if i = 33 then 0
            else if i = 34 then g0 + 56 * UInt64.ofNat j + 48 + 8
            else if i = 35 then
              (g0 + 56 * UInt64.ofNat j + 48 + 8 - 1) / 65536 + 1
            else if i = 36 then g0 + 56 * UInt64.ofNat j + 48
            else e i),
          ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hsplit, hfinal]
          simp
        · simp [hwlen]
        · rw [show (11 : Nat) - (j + 1) = 10 - j from by omega]
          simp only [lFrame, hbuf1, hkadd, cFramePos, if_true,
            List.take_zero, List.drop_zero]
          norm_num
        · intro i hi
          simp only [objBase]
          rw [show j + 1 - 1 = j from by omega]
          by_cases hik : i = j
          · subst hik
            rw [write8_bytes_same' _ _ _ (by
              rw [toUInt32_ofNat_mod_toNat]
              exact (Nat.mod_eq_of_lt (by omega)).symm)]
            rw [hgetk]
            exact hbyte
          · rw [write8_bytes_ne _ _ _ (by
              rw [toUInt32_ofNat_mod_toNat]
              rw [Nat.mod_eq_of_lt hnw]
              omega)]
            rw [hgetl i (by omega)]
            exact hdst i (by omega)
        · rw [hglC]
          simp [hlen]
        · rw [hglC]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 0))]
          rw [List.getElem?_set]
          have hl0 : 0 < st1.globals.globals.length :=
            (List.getElem?_eq_some_iff.mp h0L).choose
          simp only [if_pos rfl, hl0, decide_true, Nat.lt_irrefl,
            ite_true, Option.some.injEq, Value.i64.injEq]
          apply UInt64.toNat.inj
          simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
            show (48 : UInt64).toNat = 48 from rfl,
            show (8 : UInt64).toNat = 8 from rfl,
            show (56 : UInt64).toNat = 56 from rfl]
          have hs : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
          omega
        · rw [hglC]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 1))]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (0 = 1))]
          exact h1L
        · rw [hglC]
          rw [List.getElem?_set]
          have hl2 : 2 < st1.globals.globals.length :=
            (List.getElem?_eq_some_iff.mp h2L).choose
          simp [hl2]
          apply UInt64.toNat.inj
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat',
            show (1 : UInt64).toNat = 1 from rfl]
          have hs : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
          omega
        · rw [hglC]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 3))]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (0 = 3))]
          exact h3L
        · rw [hglC]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 4))]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (0 = 4))]
          exact h4L
        · rw [hglC]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 5))]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (0 = 5))]
          exact h5L
        · rw [write8_pages, hpgC, hpgL]
        · intro a ha
          rw [write8_bytes_ne _ _ _ (by
            rw [toUInt32_ofNat_mod_toNat]
            rw [Nat.mod_eq_of_lt hnw]
            omega)]
          exact hloC a ha
      · simp only [lMeasure, show ((1 : UInt64) = 0) = False from by simp,
          if_false, Nat.add_zero]
        rw [toNat_ofNat_lt (by rw [size_eq]; omega)]
        omega
    · have hjlt : j < k := Nat.lt_of_le_of_ne hjk hjend
      have hnge : ¬ (UInt64.ofNat j ≥ UInt64.ofNat k) := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hjU, hkU]
        omega
      change wp «module» copyBody _ stC (cFramePos g0 v k j e) env
      refine copyStepPos env st stC n g0 v k j written e
        ((st1.globals.globals.set 0
          (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8))).set 2
          (.i64 (g2 + UInt64.ofNat k + 1)))
        (cFramePos g0 v k j e).values _ hFit32 hFit hPages (by omega)
        hwlen hjlt hglC (hpgC.trans hpgL) hdst hsrc hloC
        (hvals := by rfl) (hTrap := ?_) (hB0 := ?_)
      · intro st' msg
        simp [hTrap]
      · rintro st' s' ⟨hframe', hgl', hpg', hdst', hsrc', hlo'⟩
        refine ⟨⟨j + 1, by omega, hframe', hgl',
          hpg'.trans hpgL.symm, hdst', hsrc', hlo'⟩, ?_⟩
        rw [hframe']
        simp only [cFramePos]
        rw [toNat_ofNat_lt (by rw [size_eq]; omega), hjU]
        omega


end Project.LebU32.Spec
