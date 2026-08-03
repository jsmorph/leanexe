import Project.LebU32.Frame
import Project.LebU32.IterResult

/-!
# Completed continuation-byte iteration

This module proves the allocation tail after the negative copy loop exits and
constructs the next outer-loop invariant.  The caller retains only the copy
loop and a theorem application at its exit branch.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

def negAllocTail : Program :=
  [Instruction.localGet 28, Instruction.localGet 26,
    Instruction.addI64, Instruction.wrapI64, Instruction.localGet 27,
    Instruction.wrapI64, Instruction.store8 0, Instruction.localGet 28,
    Instruction.localSet 17, Instruction.localGet 17,
    Instruction.localSet 18, Instruction.localGet 17,
    Instruction.localSet 19, Instruction.localGet 16,
    Instruction.constI64 1, Instruction.addI64, Instruction.localSet 20,
    Instruction.localGet 13, Instruction.localSet 21,
    Instruction.localGet 18, Instruction.localSet 22,
    Instruction.localGet 19, Instruction.localSet 23,
    Instruction.localGet 20, Instruction.localSet 24,
    Instruction.localGet 21, Instruction.localSet 1,
    Instruction.localGet 22, Instruction.localSet 2,
    Instruction.localGet 23, Instruction.localSet 3,
    Instruction.localGet 24, Instruction.localSet 4,
    Instruction.localGet 0, Instruction.constI64 1,
    Instruction.subI64, Instruction.localSet 0]

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem negAllocDone (env : HostEnv Unit) (st st1 stC : Store Unit)
    (n g0 g2 v : UInt64) (j : Nat) (written : List UInt8)
    (e : Nat → UInt64) (m0 : Nat) (POST : Assertion Unit)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hL5 : (lebList 10 n).length ≤ 5)
    (hsplit : lebList 10 n = written ++ lebList (10 - j) v)
    (hwlen : written.length = j)
    (hjL : j < (lebList 10 n).length)
    (hcont : ¬ v / 128 = 0)
    (hm0 : 2 * (10 - j) + 1 ≤ m0)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hFT : ∀ (st' : Store Unit) (s' : Locals),
      lInv st n g0 g2 st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } ∧
      lMeasure st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } <
        m0 →
      POST (.Fallthrough st' s'))
    (hjU : (UInt64.ofNat j).toNat = j)
    (hglC : stC.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 56 * UInt64.ofNat j + 48 + 8))).set 2
        (.i64 (g2 + UInt64.ofNat j + 1)))
    (hpgC : stC.mem.pages = st1.mem.pages)
    (hdst : ∀ i : Nat, i < j →
      stC.mem.bytes (g0.toNat + 56 * j + 48 + i) = written[i]!)
    (hloC : ∀ a : Nat, a < g0.toNat →
      stC.mem.bytes a = st.mem.bytes a)
    (hlen : st1.globals.globals.length = st.globals.globals.length)
    (h0L : st1.globals.globals[0]? =
      some (.i64 (g0 + UInt64.ofNat (56 * j))))
    (h1L : st1.globals.globals[1]? = some (.i64 0))
    (h2L : st1.globals.globals[2]? = some (.i64 (g2 + UInt64.ofNat j)))
    (h3L : st1.globals.globals[3]? = st.globals.globals[3]?)
    (h4L : st1.globals.globals[4]? = st.globals.globals[4]?)
    (h5L : st1.globals.globals[5]? = st.globals.globals[5]?)
    (hpgL : st1.mem.pages = st.mem.pages) :
    wp «module» negAllocTail POST stC (cFrameNeg g0 v j j e) env := by
  unfold negAllocTail
  rw [cFrameNeg_eq_flat]
  wp_run_folded []
  try simp [hTrap]
  have hj9 : j ≤ 9 := by omega
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
  have hjadd : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one, hjU, toNat_ofNat_lt (by rw [size_eq]; omega)]
    try rw [hjU, size_eq]
    try omega
  have hfuel : UInt64.ofNat (10 - j) - 1 =
      UInt64.ofNat (10 - (j + 1)) := by
    apply UInt64.toNat.inj
    rw [toNat_sub_le _ _ (by
      rw [toNat_ofNat_lt (by rw [size_eq]; omega),
        show (1 : UInt64).toNat = 1 from rfl]
      omega)]
    rw [toNat_ofNat_lt (by rw [size_eq]; omega),
      toNat_ofNat_lt (by rw [size_eq]; omega),
      show (1 : UInt64).toNat = 1 from rfl]
    omega
  have hvlow : v.toNat % 128 < 128 := by omega
  have hbyte : UInt8.ofNat
      (((v.toNat % 128 + 128) % 18446744073709551616 &&& 255) %
        4294967296) = (v % 128 + 128).toUInt8 := by
    have h1 : (v.toNat % 128 + 128) % 18446744073709551616 =
        v.toNat % 128 + 128 := Nat.mod_eq_of_lt (by omega)
    have h2 : (v.toNat % 128 + 128) &&& 255 = v.toNat % 128 + 128 := by
      rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
    apply UInt8.toNat.inj
    simp only [UInt8.toNat_ofNat', UInt64.toUInt8, UInt64.toNat_add,
      UInt64.toNat_mod, show (128 : UInt64).toNat = 128 from rfl]
    have hs : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
    omega
  have hcont10 : lebList (10 - j) v =
      (v % 128 + 128).toUInt8 :: lebList (10 - (j + 1)) (v / 128) := by
    have h10j : 10 - j = (9 - j) + 1 := by omega
    have h9j : 9 - j = 10 - (j + 1) := by omega
    rw [h10j, lebList_cont _ _ hcont, h9j]
  have hgetl : ∀ i : Nat, i < j →
      (written ++ [(v % 128 + 128).toUInt8])[i]! = written[i]! := by
    intro i hi
    rw [getElem_bang _ _ (by simp; omega), getElem_bang _ _ (by omega)]
    exact List.getElem_append_left (by omega)
  have hgetj : (written ++ [(v % 128 + 128).toUInt8])[j]! =
      (v % 128 + 128).toUInt8 := by
    rw [getElem_bang _ _ (by simp; omega)]
    exact List.getElem_concat_length hwlen.symm _
  refine ⟨by rw [Nat.mod_eq_of_lt hnw, hpgCL]; omega, ?_⟩
  apply hFT
  constructor
  · refine ⟨j + 1, v / 128,
      written ++ [(v % 128 + 128).toUInt8], false,
      (fun i =>
        if i = 13 then v / 128
        else if i = 14 then v % 128 + 128 &&& 255
        else if i = 15 then bufPtr g0 j
        else if i = 16 then UInt64.ofNat j
        else if i = 17 then g0 + 56 * UInt64.ofNat j + 48
        else if i = 18 then g0 + 56 * UInt64.ofNat j + 48
        else if i = 19 then g0 + 56 * UInt64.ofNat j + 48
        else if i = 20 then UInt64.ofNat j + 1
        else if i = 21 then v / 128
        else if i = 22 then g0 + 56 * UInt64.ofNat j + 48
        else if i = 23 then g0 + 56 * UInt64.ofNat j + 48
        else if i = 24 then UInt64.ofNat j + 1
        else if i = 25 then bufPtr g0 j
        else if i = 26 then UInt64.ofNat j
        else if i = 27 then v % 128 + 128 &&& 255
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
    · rw [hsplit, hcont10]
      simp
    · simp [hwlen]
    · simp only [if_false, Bool.false_eq_true]
      simp only [lFrame, hbuf1, hjadd, hfuel]
      norm_num
    · intro i hi
      simp only [objBase]
      rw [show j + 1 - 1 = j from by omega]
      by_cases hij : i = j
      · subst hij
        rw [write8_bytes_same' _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat]
          exact (Nat.mod_eq_of_lt (by omega)).symm)]
        rw [hgetj]
        exact hbyte
      · rw [write8_bytes_ne _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt hnw]
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
      simp only [hl0, ite_true, Option.some.injEq, Value.i64.injEq]
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
    · have hgeq : g2 + UInt64.ofNat j + 1 =
          g2 + UInt64.ofNat (j + 1) := by
        apply UInt64.toNat.inj
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat',
          show (1 : UInt64).toNat = 1 from rfl]
        have hs : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
        omega
      rw [hglC, List.getElem?_set]
      have hl2 : 2 < st1.globals.globals.length :=
        (List.getElem?_eq_some_iff.mp h2L).choose
      simp only [List.length_set]
      rw [if_pos hl2]
      exact congrArg (fun x => some (Value.i64 x)) hgeq
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
        rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt hnw]
        omega)]
      exact hloC a ha
  · simp only [lMeasure]
    rw [hfuel, toNat_ofNat_lt (by rw [size_eq]; omega)]
    have h01 : (if True then (1 : Nat) else 0) = 1 := by simp
    rw [h01]
    omega

end Project.LebU32.Spec
