module

public import LeanExe.A64.Proof.WasiProgram

@[expose] public section

/-!
The platforms and the launch of an executable of `genWasiElf`.  `modulePlatform L G` maps less
than the data segment's platform, which maps less than `wasiPlatform L sp top`, so a run of the
module's code is a run of the runtime's and of the process's (`Platform.Le`).  The scratch's bytes
and every byte from `2^32` up lie outside `modulePlatform`'s Normal memory, the former by its
definition and the latter because the data segment ends below `2^32`.  `InitialStack` reads only
bytes from `2^32` up, so two memories that agree there meet it together (`InitialStack.congr`).
-/

namespace LeanExe.A64

theorem modulePlatform_le (L : ElfLayout) (G : Scratch) :
    (modulePlatform L G).Le (elfPlatform L) :=
  ⟨fun a h => by
    simp only [modulePlatform, Bool.and_eq_true] at h
    exact h.1, rfl, rfl⟩

theorem elfPlatform_le_wasi (L : ElfLayout) (sp top : UInt64) :
    (elfPlatform L).Le (wasiPlatform L sp top) :=
  ⟨fun a h => by simp [wasiPlatform, h], rfl, rfl⟩

theorem modulePlatform_le_wasi (L : ElfLayout) (G : Scratch) (sp top : UInt64) :
    (modulePlatform L G).Le (wasiPlatform L sp top) :=
  (modulePlatform_le L G).trans (elfPlatform_le_wasi L sp top)

/-- A byte of the data segment outside the scratch is Normal memory of `modulePlatform`. -/
theorem modulePlatform_normal {L : ElfLayout} {G : Scratch} {a : UInt64}
    (h : (elfPlatform L).normal a = true)
    (hs : a.toNat < G.base.toNat ∨ G.base.toNat + scratchSize ≤ a.toNat) :
    (modulePlatform L G).normal a = true := by
  simp only [modulePlatform, h, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not,
    not_and, UInt64.le_iff_toNat_le]
  omega

/-- The scratch's bytes are no Normal memory of `modulePlatform`. -/
theorem modulePlatform_scratch {L : ElfLayout} {G : Scratch} {j : Nat} (hj : j < scratchSize)
    (hG : G.base.toNat + scratchSize < 2 ^ 64) :
    (modulePlatform L G).normal (G.base + UInt64.ofNat j) = false := by
  have e : (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
    unfold scratchSize at hj hG
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at hG ⊢
    omega
  simp only [modulePlatform, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq,
    UInt64.le_iff_toNat_le, e]
  exact .inr ⟨by omega, by omega⟩

/-- A byte from `2^32` up is no Normal memory of `modulePlatform` when the data segment ends
below `2^32`. -/
theorem modulePlatform_high {L : ElfLayout} {G : Scratch} {a : UInt64}
    (hL : L.area.toNat + L.dataMem ≤ 2 ^ 32) (ha : 2 ^ 32 ≤ a.toNat) :
    (modulePlatform L G).normal a = false := by
  simp only [modulePlatform, elfPlatform, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_and, UInt64.le_iff_toNat_le]
  exact .inl fun _ => by omega

/-- An address below `b`, or 8 or more above it, lies outside the 8 bytes from `b`. -/
theorem not_within8 {a b : UInt64} (h : a.toNat < b.toNat ∨ b.toNat + 8 ≤ a.toNat)
    (hb : b.toNat + 8 ≤ 2 ^ 64) : ¬ a - b < 8 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub]
  have := a.toNat_lt
  have := b.toNat_lt
  simp only [UInt64.reduceToNat, Nat.reducePow] at *
  omega

theorem readList_congr {m m' : UInt64 → UInt8} :
    ∀ (n : Nat) (a : UInt64), (∀ j < n, m' (a + UInt64.ofNat j) = m (a + UInt64.ofNat j)) →
      readList m' a n = readList m a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    rw [add_ofNat_zero] at h0
    have ih := readList_congr (m := m) (m' := m') n (a + 1) fun j hj => by
      rw [LeanExe.Linux.succ_ofNat]
      exact h (j + 1) (by omega)
    rw [readList, readList, h0, ih]

/-- Two memories that agree from `2^32` up meet `InitialStack` together. -/
theorem InitialStack.congr {args environ : List (List UInt8)} {sp top : UInt64}
    {m m' : UInt64 → UInt8} (h : InitialStack args environ sp top m)
    (hm : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → m' a = m a) : InitialStack args environ sp top m' := by
  have hab : 4294967296 ≤ sp.toNat := h.above
  have hbe : top.toNat < 9223372036854775808 := h.below
  have hwo := h.words
  have word : ∀ n, sp.toNat + n + 8 ≤ top.toNat →
      load64 m' (sp + UInt64.ofNat n) = load64 m (sp + UInt64.ofNat n) := by
    intro n hn
    apply load64_congr
    intro k hk
    apply hm
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  have str : ∀ n s, sp.toNat + n + 8 ≤ top.toNat →
      StringAt sp top m (sp + UInt64.ofNat n) s → StringAt sp top m' (sp + UInt64.ofNat n) s := by
    intro n s hn ⟨h1, h2, h3, h4⟩
    rw [StringAt, word n hn]
    refine ⟨h1, h2, h3, ?_⟩
    rw [readList_congr _ _ fun j hj => hm _ (by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
      omega)]
    exact h4
  have w0 := word 0 (by omega)
  rw [add_ofNat_zero] at w0
  refine ⟨h.above, h.below, hwo, by rw [w0]; exact h.argc,
    fun i hi => str _ _ (by omega) (h.argv i hi), by rw [word _ (by omega)]; exact h.argvEnd,
    fun j hj => str _ _ (by omega) (h.envp j hj), by rw [word _ (by omega)]; exact h.envpEnd⟩

end LeanExe.A64
