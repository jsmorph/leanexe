import Project.LebU32.Defs

/-!
# The byte-copy step of the buffer push

One continue iteration of the copy loop inside a push: reads byte `j`
from the old buffer, writes it to the new buffer, and advances.  Split
into its own file for elaboration memory; the interface hands back the
facts the caller's invariant needs, generically over the postcondition.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

def copyBody : Wasm.Program :=
  [.localGet 30, .localGet 26, .geUI64, .br_if 1,
   .localGet 28, .localGet 30, .addI64, .wrapI64,
   .localGet 25, .localGet 30, .addI64, .wrapI64,
   .load8U 0, .store8 0,
   .localGet 30, .constI64 1, .addI64, .localSet 30, .br 0]

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem copyStepPos (env : HostEnv Unit) (st stC : Store Unit)
    (n g0 v : UInt64) (k j : Nat) (written : List UInt8)
    (e : Nat → UInt64) (gbase vals0 : List Value)
    (CPOST : Assertion Unit)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hk8 : k ≤ 8)
    (hwlen : written.length = k)
    (hjlt : j < k)
    (hglC : stC.globals.globals = gbase)
    (hpgC : stC.mem.pages = st.mem.pages)
    (hdst : ∀ i : Nat, i < j →
      stC.mem.bytes (g0.toNat + 56 * k + 48 + i) = written[i]!)
    (hsrc : ∀ i : Nat, i < k →
      stC.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!)
    (hloC : ∀ a : Nat, a < g0.toNat → stC.mem.bytes a = st.mem.bytes a)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      CPOST (.Trap st' msg) = False)
    (hvals : vals0 = [])
    (hB0 : ∀ (st' : Store Unit) (s' : Locals),
      ({ s' with values := s'.values.take 0 ++ vals0.drop 0 } =
        cFramePos g0 v k (j + 1) e ∧
       st'.globals.globals = gbase ∧
       st'.mem.pages = st.mem.pages ∧
       (∀ i : Nat, i < j + 1 →
         st'.mem.bytes (g0.toNat + 56 * k + 48 + i) = written[i]!) ∧
       (∀ i : Nat, i < k →
         st'.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!) ∧
       (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a)) →
      CPOST (.Break 0 st' s')) :
    wp «module» copyBody CPOST stC (cFramePos g0 v k j e) env := by
  have hjU : (UInt64.ofNat j).toNat = j :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hkU : (UInt64.ofNat k).toNat = k :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  unfold copyBody
  simp only [cFramePos]
  wp_run
  try simp [hTrap]
  have hnge : ¬ (UInt64.ofNat j ≥ UInt64.ofNat k) := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le, hjU, hkU]
    omega
  rw [if_neg hnge]
  try wp_run
  try simp [hTrap]
  have hbufN : (bufPtr g0 k).toNat = g0.toNat + 56 * (k - 1) + 48 := by
    unfold bufPtr objBase
    rw [if_neg (by omega)]
    exact toNat_ofNat_lt (by rw [size_eq]; omega)
  have hjadd : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one, hjU,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    try rw [hjU, size_eq]
    try omega
  have hval : stC.mem.read8
      (UInt32.ofNat (((bufPtr g0 k).toNat + j) %
        4294967296)) = written[j]! := by
    rw [Mem.read8, toUInt32_ofNat_mod_toNat, hbufN]
    rw [Nat.mod_eq_of_lt (by omega)]
    have := hsrc j hjlt
    simp only [objBase] at this
    exact this
  refine ⟨by rw [hbufN]; omega, by omega, ?_⟩
  apply hB0
  refine ⟨?_, hglC, ?_, ?_, ?_, ?_⟩
  · simp only [cFramePos, hvals, List.take_zero, List.drop_zero,
      List.nil_append]
    rw [hjadd]
  · rw [write8_pages]
    exact hpgC
  · intro i hi
    by_cases hij : i = j
    · subst hij
      rw [write8_bytes_same' _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat]
        exact (Nat.mod_eq_of_lt (by omega)).symm)]
      exact hval
    · rw [write8_bytes_ne _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat]
        omega)]
      exact hdst i (by omega)
  · intro i hi
    rw [write8_bytes_ne _ _ _ (by
      rw [toUInt32_ofNat_mod_toNat]
      simp only [objBase]
      rw [show (g0.toNat + 56 * k + 48 + j) % 4294967296 =
        g0.toNat + 56 * k + 48 + j from by omega]
      omega)]
    exact hsrc i hi
  · intro a ha
    rw [write8_bytes_ne _ _ _ (by
      rw [toUInt32_ofNat_mod_toNat]
      rw [show (g0.toNat + 56 * k + 48 + j) % 4294967296 =
        g0.toNat + 56 * k + 48 + j from by omega]
      omega)]
    exact hloC a ha

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem copyStepNeg (env : HostEnv Unit) (st stC : Store Unit)
    (n g0 v : UInt64) (k j : Nat) (written : List UInt8)
    (e : Nat → UInt64) (gbase vals0 : List Value)
    (CPOST : Assertion Unit)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hk8 : k ≤ 8)
    (hwlen : written.length = k)
    (hjlt : j < k)
    (hglC : stC.globals.globals = gbase)
    (hpgC : stC.mem.pages = st.mem.pages)
    (hdst : ∀ i : Nat, i < j →
      stC.mem.bytes (g0.toNat + 56 * k + 48 + i) = written[i]!)
    (hsrc : ∀ i : Nat, i < k →
      stC.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!)
    (hloC : ∀ a : Nat, a < g0.toNat → stC.mem.bytes a = st.mem.bytes a)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      CPOST (.Trap st' msg) = False)
    (hvals : vals0 = [])
    (hB0 : ∀ (st' : Store Unit) (s' : Locals),
      ({ s' with values := s'.values.take 0 ++ vals0.drop 0 } =
        cFrameNeg g0 v k (j + 1) e ∧
       st'.globals.globals = gbase ∧
       st'.mem.pages = st.mem.pages ∧
       (∀ i : Nat, i < j + 1 →
         st'.mem.bytes (g0.toNat + 56 * k + 48 + i) = written[i]!) ∧
       (∀ i : Nat, i < k →
         st'.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!) ∧
       (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a)) →
      CPOST (.Break 0 st' s')) :
    wp «module» copyBody CPOST stC (cFrameNeg g0 v k j e) env := by
  have hjU : (UInt64.ofNat j).toNat = j :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hkU : (UInt64.ofNat k).toNat = k :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  unfold copyBody
  simp only [cFrameNeg]
  wp_run
  try simp [hTrap]
  have hnge : ¬ (UInt64.ofNat j ≥ UInt64.ofNat k) := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le, hjU, hkU]
    omega
  rw [if_neg hnge]
  try wp_run
  try simp [hTrap]
  have hbufN : (bufPtr g0 k).toNat = g0.toNat + 56 * (k - 1) + 48 := by
    unfold bufPtr objBase
    rw [if_neg (by omega)]
    exact toNat_ofNat_lt (by rw [size_eq]; omega)
  have hjadd : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one, hjU,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    try rw [hjU, size_eq]
    try omega
  have hval : stC.mem.read8
      (UInt32.ofNat (((bufPtr g0 k).toNat + j) %
        4294967296)) = written[j]! := by
    rw [Mem.read8, toUInt32_ofNat_mod_toNat, hbufN]
    rw [Nat.mod_eq_of_lt (by omega)]
    have := hsrc j hjlt
    simp only [objBase] at this
    exact this
  refine ⟨by rw [hbufN]; omega, by omega, ?_⟩
  apply hB0
  refine ⟨?_, hglC, ?_, ?_, ?_, ?_⟩
  · simp only [cFrameNeg, hvals, List.take_zero, List.drop_zero,
      List.nil_append]
    rw [hjadd]
  · rw [write8_pages]
    exact hpgC
  · intro i hi
    by_cases hij : i = j
    · subst hij
      rw [write8_bytes_same' _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat]
        exact (Nat.mod_eq_of_lt (by omega)).symm)]
      exact hval
    · rw [write8_bytes_ne _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat]
        omega)]
      exact hdst i (by omega)
  · intro i hi
    rw [write8_bytes_ne _ _ _ (by
      rw [toUInt32_ofNat_mod_toNat]
      simp only [objBase]
      rw [show (g0.toNat + 56 * k + 48 + j) % 4294967296 =
        g0.toNat + 56 * k + 48 + j from by omega]
      omega)]
    exact hsrc i hi
  · intro a ha
    rw [write8_bytes_ne _ _ _ (by
      rw [toUInt32_ofNat_mod_toNat]
      rw [show (g0.toNat + 56 * k + 48 + j) % 4294967296 =
        g0.toNat + 56 * k + 48 + j from by omega]
      omega)]
    exact hloC a ha

end Project.LebU32.Spec
