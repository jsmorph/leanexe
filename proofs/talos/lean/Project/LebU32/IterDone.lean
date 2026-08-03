import Project.LebU32.Frame
import Project.LebU32.IterResult

/-!
# Completed final-byte iteration

This module proves the allocation tail after the copy loop exits.  Keeping the
tail and its `PosResult` construction out of the loop theorem prevents the
instruction continuation from entering every dependent record field.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem posAllocDone (env : HostEnv Unit) (st st1 stC : Store Unit)
    (n g0 g2 v : UInt64) (j : Nat) (written : List UInt8)
    (e : Nat → UInt64) (m0 : Nat) (POST : Assertion Unit)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hL5 : (lebList 10 n).length ≤ 5)
    (hsplit : lebList 10 n = written ++ lebList (10 - j) v)
    (hwlen : written.length = j)
    (hjL : j < (lebList 10 n).length)
    (hrest : v / 128 = 0)
    (hm0 : 2 * (10 - j) + 1 ≤ m0)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
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
    wp «module» posAllocTail (posPOST st n g0 g2 m0 POST) stC
      (cFramePos g0 v j j e) env := by
  unfold posAllocTail
  rw [cFramePos_eq_flat]
  wp_run_folded []
  try simp [posPOST, hTrap]
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
    rw [toNat_add_one, hjU,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    try rw [hjU, size_eq]
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
  have hgetj : (written ++ [(v % 128).toUInt8])[j]! =
      (v % 128).toUInt8 := by
    rw [getElem_bang _ _ (by simp; omega)]
    exact List.getElem_concat_length hwlen.symm _
  refine ⟨by
    rw [Nat.mod_eq_of_lt hnw]
    rw [show stC.mem.pages = st.mem.pages from hpgCL]
    omega, ?_⟩
  apply Nonempty.intro
  refine {
    k := j + 1
    v := v
    written := written ++ [(v % 128).toUInt8]
    done := true
    e := fun i =>
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
        else e i
    split := by
      rw [hsplit, hfinal]
      simp
    writtenLength := by simp [hwlen]
    indexBound := by omega
    frame := by
      rw [show (11 : Nat) - (j + 1) = 10 - j from by omega]
      simp only [lFrame, hbuf1, hjadd, if_true,
        List.take_zero, List.drop_zero]
      norm_num
    bytes := by
      intro i hi
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
          rw [toUInt32_ofNat_mod_toNat]
          rw [Nat.mod_eq_of_lt hnw]
          omega)]
        rw [hgetl i (by omega)]
        exact hdst i (by omega)
    globalsLength := by
      rw [hglC]
      simp [hlen]
    global0 := by
      rw [hglC]
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
    global1 := by
      rw [hglC]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (2 = 1))]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (0 = 1))]
      exact h1L
    global2 := by
      rw [hglC]
      rw [List.getElem?_set]
      have hl2 : 2 < st1.globals.globals.length :=
        (List.getElem?_eq_some_iff.mp h2L).choose
      simp [hl2]
      apply UInt64.toNat.inj
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat',
        show (1 : UInt64).toNat = 1 from rfl]
      have hs : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
      omega
    global3 := by
      rw [hglC]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (2 = 3))]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (0 = 3))]
      exact h3L
    global4 := by
      rw [hglC]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (2 = 4))]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (0 = 4))]
      exact h4L
    global5 := by
      rw [hglC]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (2 = 5))]
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (0 = 5))]
      exact h5L
    pages := by rw [write8_pages, hpgC, hpgL]
    below := by
      intro a ha
      rw [write8_bytes_ne _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt hnw]
        omega)]
      exact hloC a ha
    measure := by
      simp only [lMeasure, show ((1 : UInt64) = 0) = False from by simp,
        if_false, Nat.add_zero]
      rw [toNat_ofNat_lt (by rw [size_eq]; omega)]
      omega
  }

end Project.LebU32.Spec
