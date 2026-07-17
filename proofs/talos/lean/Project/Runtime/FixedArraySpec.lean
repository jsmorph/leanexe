import Project.Runtime.Spec

namespace Project.Runtime

open Wasm Project.Common

private def fixedFrame (p len stride i j : UInt64) : Locals :=
  { params := [.i64 p],
    locals := [.i64 1, .i64 2, .i64 len, .i64 stride, .i64 0, .i64 j,
      .i64 i, .i64 0],
    values := [] }

/-- Releasing a refcount-one fixed array with no pointer fields frees the
array without reading or releasing its element words. -/
theorem release_frees_fixed_array_zero_mask
    (env : HostEnv Unit) (m : Module) (id : Nat) (st : Store Unit)
    (p g1 g4 g5 : UInt64) (len stride : Nat)
    (hf : m.funcs[id - m.imports.length]? = some (releaseFuncDef id))
    (hImp : m.imports[id]? = none)
    (hlen32 : len < 4294967296)
    (hstride32 : stride < 4294967296)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat + 8 ≤ st.mem.pages * 65536)
    (hmagic : st.mem.read64 ((p - 48).toUInt32) = 5501223100278326855)
    (hrc : st.mem.read64 ((p - 40).toUInt32) = 1)
    (hkind : st.mem.read64 ((p - 24).toUInt32) = 2)
    (hlen : st.mem.read64 p.toUInt32 = UInt64.ofNat len)
    (hstride : st.mem.read64 ((p - 16).toUInt32) = UInt64.ofNat stride)
    (hmask : st.mem.read64 ((p - 8).toUInt32) = 0)
    (hg1 : st.globals.globals[1]? = some (.i64 g1))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5)) :
    TerminatesWith (m := m) (id := id) (initial := st) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st.mem.write64 ((p - 40).toUInt32) 0).write64
          ((p - 8).toUInt32) g1 ∧
        st'.globals.globals =
          ((st.globals.globals.set 4 (.i64 (g4 + 1))).set 5
            (.i64 (g5 + 1))).set 1 (.i64 p)) := by
  have hp0 : ¬p = 0 := by
    intro h
    rw [h] at hp48
    simp at hp48
  have hsubN : ∀ c : UInt64, c.toNat ≤ 48 →
      (p - c).toNat = p.toNat - c.toNat :=
    fun c hc => toNat_sub_le _ _ (by omega)
  have hbridge : ∀ c : UInt64, c.toNat ≤ 48 →
      UInt32.ofNat ((p - c).toNat % 4294967296) = (p - c).toUInt32 := by
    intro c hc
    rw [toUInt32_eq_ofNat]
  have hmagic' : st.mem.read64
      (UInt32.ofNat ((p - 48).toNat % 4294967296)) =
      5501223100278326855 := by
    rw [hbridge 48 (by decide)]
    exact hmagic
  have hrc' : st.mem.read64
      (UInt32.ofNat ((p - 40).toNat % 4294967296)) = 1 := by
    rw [hbridge 40 (by decide)]
    exact hrc
  have hkind' : st.mem.read64
      (UInt32.ofNat ((p - 24).toNat % 4294967296)) = 2 := by
    rw [hbridge 24 (by decide)]
    exact hkind
  have hstride' : st.mem.read64
      (UInt32.ofNat ((p - 16).toNat % 4294967296)) =
      UInt64.ofNat stride := by
    rw [hbridge 16 (by decide)]
    exact hstride
  have hmask' : st.mem.read64
      (UInt32.ofNat ((p - 8).toNat % 4294967296)) = 0 := by
    rw [hbridge 8 (by decide)]
    exact hmask
  have hlen' : st.mem.read64
      (UInt32.ofNat (p.toNat % 4294967296)) = UInt64.ofNat len := by
    rw [← toUInt32_eq_ofNat]
    exact hlen
  have h40N : (p - 40).toNat = p.toNat - 40 := by
    rw [hsubN 40 (by decide), show (40 : UInt64).toNat = 40 from rfl]
  have h8N : (p - 8).toNat = p.toNat - 8 := by
    rw [hsubN 8 (by decide), show (8 : UInt64).toNat = 8 from rfl]
  have ha40 : UInt32.ofNat ((p - 40).toNat % 4294967296) =
      p.toUInt32 - 40 := by
    apply UInt32.toNat.inj
    rw [toUInt32_ofNat_mod_toNat, h40N,
      Wasm.UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]
        rw [show (40 : UInt32).toNat = 40 from rfl, toUInt32_toNat]
        omega)]
    rw [show (40 : UInt32).toNat = 40 from rfl, toUInt32_toNat]
    omega
  have ha8 : UInt32.ofNat ((p - 8).toNat % 4294967296) =
      p.toUInt32 - 8 := by
    apply UInt32.toNat.inj
    rw [toUInt32_ofNat_mod_toNat, h8N,
      Wasm.UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]
        rw [show (8 : UInt32).toNat = 8 from rfl, toUInt32_toNat]
        omega)]
    rw [show (8 : UInt32).toNat = 8 from rfl, toUInt32_toNat]
    omega
  have hlenU : (UInt64.ofNat len).toNat = len :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hstrideU : (UInt64.ofNat stride).toNat = stride :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  refine TerminatesWith.of_wp_entry_for hf ?_ hImp
  change wp m (releaseBody id) _ st
    { params := [.i64 p],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0],
      values := [] } env
  unfold releaseBody
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hp0])]
  wp_run
  try simp
  refine ⟨by
    rw [hsubN 48 (by decide), show (48 : UInt64).toNat = 48 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega, ?_⟩
  simp only [hmagic']
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run
  try simp
  refine ⟨by
    rw [hsubN 40 (by decide), show (40 : UInt64).toNat = 40 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega, ?_⟩
  simp only [hrc']
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run
  try simp only [hg4]
  try wp_run
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run
  try simp
  refine ⟨by
    rw [hsubN 24 (by decide), show (24 : UInt64).toNat = 24 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega, ?_⟩
  simp only [hkind']
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run
  try simp
  refine ⟨by rw [Nat.mod_eq_of_lt hp32]; omega, ?_⟩
  simp only [hlen']
  try wp_run
  try simp
  refine ⟨by
    rw [hsubN 16 (by decide), show (16 : UInt64).toNat = 16 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega, ?_⟩
  simp only [hstride']
  try wp_run
  try simp
  refine ⟨by
    rw [hsubN 8 (by decide), show (8 : UInt64).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega, ?_⟩
  simp only [hmask']
  try wp_run
  try simp
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun stL sL =>
      ∃ i : Nat, ∃ j : UInt64, i ≤ len ∧
        sL = fixedFrame p (UInt64.ofNat len) (UInt64.ofNat stride)
          (UInt64.ofNat i) j ∧
        stL.mem = st.mem ∧
        stL.globals.globals = st.globals.globals.set 4 (.i64 (g4 + 1)))
    (μ := fun _ sL =>
      match sL.locals with
      | _ :: _ :: _ :: _ :: _ :: _ :: .i64 i :: _ => len + 1 - i.toNat
      | _ => 0)
  · refine ⟨0, 0, Nat.zero_le _, ?_, rfl, rfl⟩
    simp [fixedFrame]
  · rintro stL sL ⟨i, j, hile, rfl, hmemL, hglobalsL⟩
    have hiU : (UInt64.ofNat i).toNat = i :=
      toNat_ofNat_lt (by rw [size_eq]; omega)
    simp only [fixedFrame]
    wp_run
    try simp
    by_cases hiend : i = len
    · have hge : UInt64.ofNat i ≥ UInt64.ofNat len := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hiU, hlenU]
        omega
      rw [if_pos hge]
      subst i
      try simp
      try wp_run
      simp only [hglobalsL, List.getElem?_set,
        if_neg (by omega : ¬(4 = 5)), hg5]
      try wp_run
      try simp
      refine ⟨by
        rw [hmemL, h40N, Nat.mod_eq_of_lt (by omega)]
        omega, ?_⟩
      simp only [hg1]
      try wp_run
      try simp
      refine ⟨by
        rw [hmemL, h8N, Nat.mod_eq_of_lt (by omega)]
        omega, ?_⟩
      try wp_run
      try simp
      refine ⟨?_, ?_⟩
      · simp [releaseFuncDef]
      · rw [hmemL, ha40, ha8]
    · have hilt : i < len := Nat.lt_of_le_of_ne hile hiend
      have hnge : ¬UInt64.ofNat i ≥ UInt64.ofNat len := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hiU, hlenU]
        omega
      rw [if_neg hnge]
      try simp
      try wp_run
      try simp
      apply wp_block_cons
      apply wp_loop_cons
        (Inv := fun stI sI =>
          ∃ k : Nat, k ≤ stride ∧
            sI = fixedFrame p (UInt64.ofNat len) (UInt64.ofNat stride)
              (UInt64.ofNat i) (UInt64.ofNat k) ∧
            stI.mem = st.mem ∧
            stI.globals.globals =
              st.globals.globals.set 4 (.i64 (g4 + 1)))
        (μ := fun _ sI =>
          match sI.locals with
          | _ :: _ :: _ :: _ :: _ :: .i64 k :: _ =>
              stride + 1 - k.toNat
          | _ => 0)
      · refine ⟨0, Nat.zero_le _, ?_, hmemL, hglobalsL⟩
        simp [fixedFrame]
      · rintro stI sI ⟨k, hkle, rfl, hmemI, hglobalsI⟩
        have hkU : (UInt64.ofNat k).toNat = k :=
          toNat_ofNat_lt (by rw [size_eq]; omega)
        simp only [fixedFrame]
        wp_run
        try simp
        by_cases hkend : k = stride
        · have hge : UInt64.ofNat k ≥ UInt64.ofNat stride := by
            rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hstrideU]
            omega
          rw [if_pos hge]
          subst k
          try simp
          try wp_run
          try simp
          have hiadd : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
            apply UInt64.toNat.inj
            rw [toNat_add_one, hiU,
              toNat_ofNat_lt (by rw [size_eq]; omega)]
            rw [size_eq]
            omega
          rw [hiadd]
          refine ⟨⟨i + 1, by omega, rfl, hmemI, hglobalsI⟩, ?_⟩
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        · have hklt : k < stride := Nat.lt_of_le_of_ne hkle hkend
          have hnge : ¬UInt64.ofNat k ≥ UInt64.ofNat stride := by
            rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hstrideU]
            omega
          rw [if_neg hnge]
          try simp
          try wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          try simp
          have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
            apply UInt64.toNat.inj
            rw [toNat_add_one, hkU,
              toNat_ofNat_lt (by rw [size_eq]; omega)]
            rw [size_eq]
            omega
          rw [hkadd]
          refine ⟨⟨k + 1, by omega, rfl, hmemI, hglobalsI⟩, ?_⟩
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega

end Project.Runtime
