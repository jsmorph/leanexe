import Project.PairFree.Base

/-!
# Release of the shared pair

Releasing the pair array walks the two cells, decrements the shared child,
frees it, and frees the parent in front of it.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

def rFrame (p l1 l2 l3 l4 l5 l6 l7 l8 : UInt64) : Locals :=
  { params := [.i64 p],
    locals := [.i64 l1, .i64 l2, .i64 l3, .i64 l4, .i64 l5, .i64 l6, .i64 l7,
      .i64 l8],
    values := [] }

/-- Releasing the pair array frees the whole two-level graph: the walk over
the two cells calls the release function on the shared child twice, first
decrementing it from two to one and then freeing it, and the parent then
frees itself in front of the child on the free list. -/
theorem func7_frees_pair (env : HostEnv Unit) (st4 : Store Unit)
    (p c r4 r5 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hpfit32 : p.toNat + 56 < 4294967296)
    (hpfit : p.toNat + 56 ≤ st4.mem.pages * 65536)
    (hc48 : 48 ≤ c.toNat)
    (hsep : c.toNat + 56 ≤ p.toNat)
    (hpm : st4.mem.read64 (UInt32.ofNat ((p.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hpr : st4.mem.read64 (UInt32.ofNat ((p.toNat - 40) % 4294967296)) = 1)
    (hpk : st4.mem.read64 (UInt32.ofNat ((p.toNat - 24) % 4294967296)) = 2)
    (hpw : st4.mem.read64 (UInt32.ofNat ((p.toNat - 16) % 4294967296)) = 3)
    (hpmask : st4.mem.read64 (UInt32.ofNat ((p.toNat - 8) % 4294967296)) = 1)
    (hplen : st4.mem.read64 (UInt32.ofNat (p.toNat % 4294967296)) = 2)
    (hc8 : st4.mem.read64 (UInt32.ofNat ((p.toNat + 8) % 4294967296)) = c)
    (hc32 : st4.mem.read64 (UInt32.ofNat ((p.toNat + 32) % 4294967296)) = c)
    (hcm : st4.mem.read64 (UInt32.ofNat ((c.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hcr : st4.mem.read64 (UInt32.ofNat ((c.toNat - 40) % 4294967296)) = 2)
    (hck : st4.mem.read64 (UInt32.ofNat ((c.toNat - 24) % 4294967296)) = 0)
    (hg1 : st4.globals.globals[1]? = some (.i64 0))
    (hg4 : st4.globals.globals[4]? = some (.i64 r4))
    (hg5 : st4.globals.globals[5]? = some (.i64 r5)) :
    TerminatesWith (m := «module») (id := 7) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem.pages = st4.mem.pages ∧
        st'.globals.globals[1]? = some (.i64 p) ∧
        st'.globals.globals[2]? = st4.globals.globals[2]? ∧
        st'.globals.globals[3]? = st4.globals.globals[3]? ∧
        st'.globals.globals[4]? = some (.i64 (r4 + 1 + 1 + 1)) ∧
        st'.globals.globals[5]? = some (.i64 (r5 + 1 + 1)) ∧
        st'.mem.read64 (UInt32.ofNat ((p.toNat - 40) % 4294967296)) = 0 ∧
        st'.mem.read64 (UInt32.ofNat ((c.toNat - 40) % 4294967296)) = 0 ∧
        (∀ a : Nat, a < c.toNat - 48 → st'.mem.bytes a = st4.mem.bytes a)) := by
  have hp0 : ¬ (p = 0) := by
    intro h
    have := congrArg UInt64.toNat h
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0] at this
    omega
  have hc0 : ¬ (c = 0) := by
    intro h
    have := congrArg UInt64.toNat h
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0] at this
    omega
  have hsubP : ∀ q : UInt64, q.toNat ≤ 48 → (p - q).toNat = p.toNat - q.toNat := by
    intro q hq
    rw [UInt64.toNat_sub]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hP48 : (p - 48).toNat = p.toNat - 48 := hsubP 48 (by rfl)
  have hP40 : (p - 40).toNat = p.toNat - 40 := hsubP 40 (by decide)
  have hP24 : (p - 24).toNat = p.toNat - 24 := hsubP 24 (by decide)
  have hP16 : (p - 16).toNat = p.toNat - 16 := hsubP 16 (by decide)
  have hP8 : (p - 8).toNat = p.toNat - 8 := hsubP 8 (by decide)
  have hpm' : st4.mem.read64 (UInt32.ofNat ((p - 48).toNat % 4294967296)) =
      5501223100278326855 := by
    rw [hP48]
    exact hpm
  have hpr' : st4.mem.read64 (UInt32.ofNat ((p - 40).toNat % 4294967296)) =
      1 := by
    rw [hP40]
    exact hpr
  have hpk' : st4.mem.read64 (UInt32.ofNat ((p - 24).toNat % 4294967296)) =
      2 := by
    rw [hP24]
    exact hpk
  apply TerminatesWith.of_wp_entry_for (f := func7Def)
  · simp [«module»]
  · change wp «module» func7 _ st4
      { params := [.i64 p],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0],
        values := [] } env
    unfold func7
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hp0])]
    wp_run
    try simp
    refine ⟨by omega, ?_⟩
    simp only [hpm']
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp
    refine ⟨by omega, ?_⟩
    simp only [hpr']
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp only [hg4]
    try wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp
    refine ⟨by omega, ?_⟩
    simp only [hpk']
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    try wp_run
    try simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    wp_run
    try simp
    have hpw' : st4.mem.read64 (UInt32.ofNat ((p - 16).toNat % 4294967296)) =
        3 := by
      rw [hP16]
      exact hpw
    have hpmask' : st4.mem.read64 (UInt32.ofNat ((p - 8).toNat % 4294967296)) =
        1 := by
      rw [hP8]
      exact hpmask
    refine ⟨by omega, by omega, by omega, ?_⟩
    try simp only [hplen, hpw', hpmask']
    try wp_run
    try simp
    have hsubC : ∀ q : UInt64, q.toNat ≤ 48 →
        (c - q).toNat = c.toNat - q.toNat := by
      intro q hq
      rw [UInt64.toNat_sub]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hC48 : (c - 48).toNat = c.toNat - 48 := hsubC 48 (by rfl)
    have hC40 : (c - 40).toNat = c.toNat - 40 := hsubC 40 (by decide)
    have hC24 : (c - 24).toNat = c.toNat - 24 := hsubC 24 (by decide)
    have hC8 : (c - 8).toNat = c.toNat - 8 := hsubC 8 (by decide)
    have hcmB : st4.mem.read64 ((c - 48).toUInt32) = 5501223100278326855 := by
      rw [toUInt32_eq_ofNat, hC48]
      exact hcm
    have hcrB : st4.mem.read64 ((c - 40).toUInt32) = 2 := by
      rw [toUInt32_eq_ofNat, hC40]
      exact hcr
    have hckB : st4.mem.read64 ((c - 24).toUInt32) = 0 := by
      rw [toUInt32_eq_ofNat, hC24]
      exact hck
    have hc32P : c.toNat < 4294967296 := by omega
    have hglen5 : 5 < st4.globals.globals.length :=
      (List.getElem?_eq_some_iff.mp hg5).choose
    have hglen4 : 4 < st4.globals.globals.length := by omega
    have hcu32 : c.toUInt32.toNat = c.toNat := by
      rw [toUInt32_toNat]
      omega
    have haC40 : (c - 40).toUInt32 = c.toUInt32 - 40 := by
      apply UInt32.toNat.inj
      rw [toUInt32_eq_ofNat, hC40, toUInt32_ofNat_mod_toNat,
        Wasm.UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          have hb : (40 : UInt32).toNat = 40 := rfl
          rw [hb, hcu32]
          omega)]
      have hb : (40 : UInt32).toNat = 40 := rfl
      rw [hb, hcu32]
      omega
    have haC8 : (c - 8).toUInt32 = c.toUInt32 - 8 := by
      apply UInt32.toNat.inj
      rw [toUInt32_eq_ofNat, hC8, toUInt32_ofNat_mod_toNat,
        Wasm.UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          have hb : (8 : UInt32).toNat = 8 := rfl
          rw [hb, hcu32]
          omega)]
      have hb : (8 : UInt32).toNat = 8 := rfl
      rw [hb, hcu32]
      omega
    have hglen1 : 1 < st4.globals.globals.length := by omega
    have hcfit : c.toNat ≤ st4.mem.pages * 65536 := by omega
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun stX sX =>
        (sX = rFrame p 1 2 2 3 1 0 0 0 ∧
          stX.mem = st4.mem ∧
          stX.mem.pages = st4.mem.pages ∧
          stX.globals.globals =
            st4.globals.globals.set 4 (.i64 (r4 + 1))) ∨
        (sX = rFrame p 1 2 2 3 1 3 1 c ∧
          stX.mem = st4.mem.write64 ((c - 40).toUInt32) 1 ∧
          stX.mem.pages = st4.mem.pages ∧
          stX.globals.globals =
            (st4.globals.globals.set 4 (.i64 (r4 + 1))).set 4
              (.i64 (r4 + 1 + 1))) ∨
        (sX = rFrame p 1 2 2 3 1 3 2 c ∧
          stX.mem = ((st4.mem.write64 ((c - 40).toUInt32) 1).write64
            ((c - 40).toUInt32) 0).write64 ((c - 8).toUInt32) 0 ∧
          stX.mem.pages = st4.mem.pages ∧
          stX.globals.globals =
            (((((st4.globals.globals.set 4 (.i64 (r4 + 1))).set 4
              (.i64 (r4 + 1 + 1))).set 4 (.i64 (r4 + 1 + 1 + 1))).set 5
              (.i64 (r5 + 1))).set 1 (.i64 c))))
      (μ := fun _ sX =>
        match sX.locals with
        | _ :: _ :: _ :: _ :: _ :: _ :: .i64 l7 :: _ => 2 - l7.toNat
        | _ => 0)
    · exact Or.inl ⟨by simp [rFrame], rfl, rfl, rfl⟩
    · rintro stX sX
        (⟨rfl, hm, hpgX, hglX⟩ | ⟨rfl, hm, hpgX, hglX⟩ | ⟨rfl, hm, hpgX, hglX⟩)
      · -- item 0: the first child release decrements the shared count
        simp only [rFrame]
        wp_run
        try simp
        apply wp_block_cons
        apply wp_loop_cons
          (Inv := fun stY sY =>
            (sY = rFrame p 1 2 2 3 1 0 0 0 ∧
              stY.mem = st4.mem ∧
              stY.mem.pages = st4.mem.pages ∧
              stY.globals.globals =
                st4.globals.globals.set 4 (.i64 (r4 + 1))) ∨
            (∃ sl : Nat, 1 ≤ sl ∧ sl ≤ 3 ∧
              sY = rFrame p 1 2 2 3 1 (UInt64.ofNat sl) 0 c ∧
              stY.mem = st4.mem.write64 ((c - 40).toUInt32) 1 ∧
              stY.mem.pages = st4.mem.pages ∧
              stY.globals.globals =
                (st4.globals.globals.set 4 (.i64 (r4 + 1))).set 4
                  (.i64 (r4 + 1 + 1))))
          (μ := fun _ sY =>
            match sY.locals with
            | _ :: _ :: _ :: _ :: _ :: .i64 l6 :: _ => 3 - l6.toNat
            | _ => 0)
        · exact Or.inl ⟨by simp [rFrame], hm, hpgX, hglX⟩
        · rintro stY sY
            (⟨rfl, hmY, hpgY, hglY⟩ | ⟨sl, hsl1, hsl3, rfl, hmY, hpgY, hglY⟩)
          · -- slot 0 of item 0: load the child and call release on it
            simp only [rFrame]
            wp_run
            try simp
            refine wp_iff_cons rfl ?_
            rw [if_pos (by decide)]
            wp_run
            try simp
            refine ⟨by omega, ?_⟩
            have hc8Y : stY.mem.read64
                (UInt32.ofNat ((p.toNat + 8) % 4294967296)) = c := by
              rw [hmY]
              exact hc8
            simp only [hc8Y]
            refine wp_call_tw (func7_decrements env _ c 2 (r4 + 1)
              hc48 hc32P (by rw [hpgY]; exact hcfit)
              (by rw [hmY]; exact hcmB)
              (by rw [hmY]; exact hcrB)
              (by decide)
              (by rw [hglY]
                  simp [hglen4])) ?_
            rintro st5 vs5 ⟨rfl, hm5, hgl5⟩
            wp_run
            try simp
            refine ⟨1, by omega, by omega, by norm_num, ?_, ?_, ?_⟩
            · rw [hm5, hmY, haC40]
              rw [show (2 - 1 : UInt64) = 1 from rfl]
            · rw [hm5, Mem.write64_pages, hpgY]
            · rw [hgl5, hglY]
              simp [List.set_set]
          · obtain rfl | rfl | rfl : sl = 1 ∨ sl = 2 ∨ sl = 3 := by omega
            · simp only [rFrame]
              wp_run
              try simp
              refine wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_run
              try simp
              refine ⟨2, by omega, by omega, by decide, ?_, hpgY, ?_⟩
              · rw [hmY, haC40]
              · rw [hglY]
                simp [List.set_set]
            · simp only [rFrame]
              wp_run
              try simp
              refine wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_run
              try simp
              refine ⟨3, by omega, by omega, by decide, ?_, hpgY, ?_⟩
              · rw [hmY, haC40]
              · rw [hglY]
                simp [List.set_set]
            · simp only [rFrame]
              wp_run
              try simp
              refine ⟨?_, hpgY, ?_⟩
              · rw [hmY, haC40]
              · rw [hglY]
                simp [List.set_set]
      · -- item 1: the second child release frees it onto the free list
        simp only [rFrame]
        wp_run
        try simp
        apply wp_block_cons
        apply wp_loop_cons
          (Inv := fun stY sY =>
            (sY = rFrame p 1 2 2 3 1 0 1 c ∧
              stY.mem = st4.mem.write64 ((c - 40).toUInt32) 1 ∧
              stY.mem.pages = st4.mem.pages ∧
              stY.globals.globals = (st4.globals.globals.set 4 (.i64 (r4 + 1))).set 4 (.i64 (r4 + 1 + 1))) ∨
            (∃ sl : Nat, 1 ≤ sl ∧ sl ≤ 3 ∧
              sY = rFrame p 1 2 2 3 1 (UInt64.ofNat sl) 1 c ∧
              stY.mem = ((st4.mem.write64 ((c - 40).toUInt32) 1).write64
                ((c - 40).toUInt32) 0).write64 ((c - 8).toUInt32) 0 ∧
              stY.mem.pages = st4.mem.pages ∧
              stY.globals.globals = ((((st4.globals.globals.set 4 (.i64 (r4 + 1))).set 4
                (.i64 (r4 + 1 + 1))).set 4 (.i64 (r4 + 1 + 1 + 1))).set 5
                (.i64 (r5 + 1))).set 1 (.i64 c)))
          (μ := fun _ sY =>
            match sY.locals with
            | _ :: _ :: _ :: _ :: _ :: .i64 l6 :: _ => 3 - l6.toNat
            | _ => 0)
        · exact Or.inl ⟨by simp [rFrame], hm, hpgX, hglX⟩
        · rintro stY sY
            (⟨rfl, hmY, hpgY, hglY⟩ | ⟨sl, hsl1, hsl3, rfl, hmY, hpgY, hglY⟩)
          · -- slot 0 of item 1: free the child
            simp only [rFrame]
            wp_run
            try simp
            refine wp_iff_cons rfl ?_
            rw [if_pos (by decide)]
            wp_run
            try simp
            refine ⟨by omega, ?_⟩
            have hc32Y : stY.mem.read64
                (UInt32.ofNat ((p.toNat + 32) % 4294967296)) = c := by
              rw [hmY]
              rw [read64_write64_ne _ _ _ _
                (by rw [toUInt32_eq_ofNat, hC40]
                    simp only [toUInt32_ofNat_mod_toNat]
                    omega)]
              exact hc32
            simp only [hc32Y]
            refine wp_call_tw (func7_frees_fresh_raw env _ c 0 (r4 + 1 + 1)
              r5 hc48 hc32P (by rw [hpgY]; exact hcfit)
              ?_ ?_ ?_ ?_ ?_ ?_) ?_
            · rw [hmY]
              rw [read64_write64_ne _ _ _ _
                (by rw [toUInt32_eq_ofNat, toUInt32_eq_ofNat, hC48, hC40]
                    simp only [toUInt32_ofNat_mod_toNat]
                    omega)]
              exact hcmB
            · rw [hmY, Mem.read64_write64_same]
            · rw [hmY]
              rw [read64_write64_ne _ _ _ _
                (by rw [toUInt32_eq_ofNat, toUInt32_eq_ofNat, hC24, hC40]
                    simp only [toUInt32_ofNat_mod_toNat]
                    omega)]
              exact hckB
            · rw [hglY]
              simp [hglen1]
              exact (List.getElem?_eq_some_iff.mp hg1).choose_spec
            · rw [hglY]
              simp [hglen4]
            · rw [hglY]
              simp [hglen5]
              exact (List.getElem?_eq_some_iff.mp hg5).choose_spec
            rintro st6 vs6 ⟨rfl, hm6, hgl6⟩
            wp_run
            try simp
            refine ⟨1, by omega, by omega, by decide, ?_, ?_, ?_⟩
            · rw [hm6, hmY, haC40, haC8]
            · rw [hm6, Mem.write64_pages, Mem.write64_pages, hpgY]
            · rw [hgl6, hglY]
              simp [List.set_set]
          · obtain rfl | rfl | rfl : sl = 1 ∨ sl = 2 ∨ sl = 3 := by omega
            · simp only [rFrame]
              wp_run
              try simp
              refine wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_run
              try simp
              refine ⟨2, by omega, by omega, by decide, ?_, hpgY, ?_⟩
              · rw [hmY, haC40, haC8]
              · rw [hglY]
                simp [List.set_set]
            · simp only [rFrame]
              wp_run
              try simp
              refine wp_iff_cons rfl ?_
              rw [if_neg (by decide)]
              wp_run
              try simp
              refine ⟨3, by omega, by omega, by decide, ?_, hpgY, ?_⟩
              · rw [hmY, haC40, haC8]
              · rw [hglY]
                simp [List.set_set]
            · simp only [rFrame]
              wp_run
              try simp
              refine ⟨?_, hpgY, ?_⟩
              · rw [hmY, haC40, haC8]
              · rw [hglY]
                simp [List.set_set]
      · -- item 2: the walk ends and the parent frees itself
        simp only [rFrame]
        wp_run
        try simp
        have hg5X : stX.globals.globals[5]? = some (.i64 (r5 + 1)) := by
          rw [hglX]
          simp [hglen5]
        have hg1X : stX.globals.globals[1]? = some (.i64 c) := by
          rw [hglX]
          simp [hglen1]
        rw [hg5X, hg1X]
        try simp
        have haP40 : UInt32.ofNat ((p - 40).toNat % 4294967296) =
            UInt32.ofNat ((p.toNat - 40) % 4294967296) := by
          rw [hP40]
        have haP8 : UInt32.ofNat ((p - 8).toNat % 4294967296) =
            UInt32.ofNat ((p.toNat - 8) % 4294967296) := by
          rw [hP8]
        have haC40n : (c - 40).toUInt32 =
            UInt32.ofNat ((c.toNat - 40) % 4294967296) := by
          rw [toUInt32_eq_ofNat, hC40]
        have haC8n : (c - 8).toUInt32 =
            UInt32.ofNat ((c.toNat - 8) % 4294967296) := by
          rw [toUInt32_eq_ofNat, hC8]
        have hlenX : stX.globals.globals.length =
            st4.globals.globals.length := by
          rw [hglX]
          simp
        have hX1 : 1 < stX.globals.globals.length := by omega
        have hX4 : 4 < stX.globals.globals.length := by omega
        have hX5 : 5 < stX.globals.globals.length := by omega
        refine ⟨by omega, by omega, by simp [func7Def], hpgX, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_⟩
        · simp [hX1]
        · rw [hglX]
          simp
        · rw [hglX]
          simp
        · rw [hglX]
          simp [hglen4]
        · simp [hX5]
        · rw [haP40, haP8]
          rw [read64_write64_ne _ _ _ _
            (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            Mem.read64_write64_same]
        · rw [haP40, haP8]
          rw [read64_write64_ne _ _ _ _
            (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
          rw [hm, haC40n, haC8n]
          rw [read64_write64_ne _ _ _ _
            (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            Mem.read64_write64_same]
        · intro a ha
          rw [haP40, haP8]
          rw [write64_bytes_lo _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
          rw [hm, haC40n, haC8n]
          rw [write64_bytes_lo _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]

end Project.PairFree.Spec
