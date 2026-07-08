import Project.BoxFree.Program
import Project.Common
import Project.Runtime.Spec
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call
import Std.Tactic.BVDecide

/-!
# Specification for `boxFreeStats`

The export builds a one-link scalar chain, a node holding the value seven
and a nil box, and releases it.  The release function takes its slots
branch on both objects: the node's walk skips two unmasked slots, calls
itself on the nil box at the masked one, and frees the node; the nil box's
walk finds a null child at the masked slot, which returns without touching
anything, and frees the box.  The theorem pins the measured value at the
literal 202: two releases, two frees, the whole graph reclaimed.
-/

namespace Project.BoxFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576
set_option Elab.async false

/-- Releasing a null pointer returns immediately and changes nothing. -/
theorem func6_null (env : HostEnv Unit) (st4 : Store Unit) :
    TerminatesWith (m := «module») (id := 6) (initial := st4) (env := env)
      [.i64 0]
      (fun st' vs => vs = [] ∧ st' = st4) :=
  Project.Runtime.release_null env «module» 6 st4 (by rfl) rfl

private def rFrame (p l1 l2 l3 l4 l5 l6 l7 l8 : UInt64) : Locals :=
  { params := [.i64 p],
    locals := [.i64 l1, .i64 l2, .i64 l3, .i64 l4, .i64 l5, .i64 l6, .i64 l7,
      .i64 l8],
    values := [] }

/-- Releasing a slots object whose masked slot holds null: the walk calls
release on the null child, which returns untouched, and the object frees
onto the free list. -/
theorem func6_frees_leaf (env : HostEnv Unit) (st4 : Store Unit)
    (p g1v r4 r5 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat + 24 < 4294967296)
    (hpfit : p.toNat + 24 ≤ st4.mem.pages * 65536)
    (hpm : st4.mem.read64 (UInt32.ofNat ((p.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hpr : st4.mem.read64 (UInt32.ofNat ((p.toNat - 40) % 4294967296)) = 1)
    (hpk : st4.mem.read64 (UInt32.ofNat ((p.toNat - 24) % 4294967296)) = 1)
    (hpl : st4.mem.read64 (UInt32.ofNat ((p.toNat - 16) % 4294967296)) = 3)
    (hpmask : st4.mem.read64 (UInt32.ofNat ((p.toNat - 8) % 4294967296)) = 4)
    (hslot2 : st4.mem.read64 (UInt32.ofNat ((p.toNat + 16) % 4294967296)) = 0)
    (hg1 : st4.globals.globals[1]? = some (.i64 g1v))
    (hg4 : st4.globals.globals[4]? = some (.i64 r4))
    (hg5 : st4.globals.globals[5]? = some (.i64 r5)) :
    TerminatesWith (m := «module») (id := 6) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st4.mem.write64 (p.toUInt32 - 40) 0).write64
          (p.toUInt32 - 8) g1v ∧
        st'.globals.globals =
          ((st4.globals.globals.set 4 (.i64 (r4 + 1))).set 5
            (.i64 (r5 + 1))).set 1 (.i64 p)) := by
  have hp0 : ¬ (p = 0) := by
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
      1 := by
    rw [hP24]
    exact hpk
  have hpl' : st4.mem.read64 (UInt32.ofNat ((p - 16).toNat % 4294967296)) =
      3 := by
    rw [hP16]
    exact hpl
  have hpmask' : st4.mem.read64 (UInt32.ofNat ((p - 8).toNat % 4294967296)) =
      4 := by
    rw [hP8]
    exact hpmask
  apply TerminatesWith.of_wp_entry_for (f := func6Def)
  · simp [«module»]
  · change wp «module» func6 _ st4
      { params := [.i64 p],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0],
        values := [] } env
    unfold func6
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
    rw [if_pos (by decide)]
    wp_run
    try simp
    refine ⟨by omega, by omega, ?_⟩
    try simp only [hpl', hpmask']
    try wp_run
    try simp
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun stX sX =>
        ∃ sl : Nat, sl ≤ 3 ∧
          sX = rFrame p 1 1 3 0 4 (UInt64.ofNat sl) 0
            (if sl ≤ 2 then 0 else 0) ∧
          stX.mem = st4.mem ∧
          stX.mem.pages = st4.mem.pages ∧
          stX.globals.globals = st4.globals.globals.set 4 (.i64 (r4 + 1)))
      (μ := fun _ sX =>
        match sX.locals with
        | _ :: _ :: _ :: _ :: _ :: .i64 l6 :: _ => 4 - l6.toNat
        | _ => 0)
    · exact ⟨0, by omega, by simp [rFrame], rfl, rfl, rfl⟩
    · rintro stX sX ⟨sl, hsl, rfl, hm, hpg, hgl⟩
      obtain rfl | rfl | rfl | rfl : sl = 0 ∨ sl = 1 ∨ sl = 2 ∨ sl = 3 := by
        omega
      · simp only [rFrame]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_run
        try simp
        refine ⟨1, by omega, by decide, hm, hpg, hgl⟩
      · simp only [rFrame]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_run
        try simp
        refine ⟨2, by omega, by decide, hm, hpg, hgl⟩
      · simp only [rFrame]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by decide)]
        wp_run
        try simp
        refine ⟨by omega, ?_⟩
        have hslot2X : stX.mem.read64
            (UInt32.ofNat ((p.toNat + 16) % 4294967296)) = 0 := by
          rw [hm]
          exact hslot2
        simp only [hslot2X]
        refine wp_call_tw (func6_null env _) ?_
        rintro st5 vs5 ⟨rfl, rfl⟩
        wp_run
        try simp
        refine ⟨3, by omega, by decide, hm, hpg, hgl⟩
      · simp only [rFrame]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_run
        try simp
        have hglen : 5 < st4.globals.globals.length :=
          (List.getElem?_eq_some_iff.mp hg5).choose
        have hg5X : stX.globals.globals[5]? = some (.i64 r5) := by
          rw [hgl, List.getElem?_set]
          simp only [if_neg (by omega : ¬ (4 = 5))]
          exact hg5
        have hg1X : stX.globals.globals[1]? = some (.i64 g1v) := by
          rw [hgl, List.getElem?_set]
          simp only [if_neg (by omega : ¬ (4 = 1))]
          exact hg1
        rw [hg5X, hg1X]
        try simp
        have haP40 : UInt32.ofNat ((p - 40).toNat % 4294967296) =
            p.toUInt32 - 40 := by
          apply UInt32.toNat.inj
          rw [toUInt32_ofNat_mod_toNat, hP40,
            Wasm.UInt32.toNat_sub_of_le _ _ (by
              rw [UInt32.le_iff_toNat_le]
              have hb : (40 : UInt32).toNat = 40 := rfl
              rw [hb, toUInt32_toNat]
              omega)]
          have hb : (40 : UInt32).toNat = 40 := rfl
          rw [hb, toUInt32_toNat]
          omega
        have haP8 : UInt32.ofNat ((p - 8).toNat % 4294967296) =
            p.toUInt32 - 8 := by
          apply UInt32.toNat.inj
          rw [toUInt32_ofNat_mod_toNat, hP8,
            Wasm.UInt32.toNat_sub_of_le _ _ (by
              rw [UInt32.le_iff_toNat_le]
              have hb : (8 : UInt32).toNat = 8 := rfl
              rw [hb, toUInt32_toNat]
              omega)]
          have hb : (8 : UInt32).toNat = 8 := rfl
          rw [hb, toUInt32_toNat]
          omega
        try simp only [hm, haP40, haP8]
        refine ⟨by omega, by omega, by simp [func6Def], trivial, ?_⟩
        rw [hgl]

/-- Releasing the node: the walk skips two unmasked slots, frees the nil
box through the recursive call at the masked slot, and the node then frees
itself in front of it. -/
theorem func6_frees_node (env : HostEnv Unit) (st4 : Store Unit)
    (p c g1v r4 r5 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat + 24 < 4294967296)
    (hpfit : p.toNat + 24 ≤ st4.mem.pages * 65536)
    (hc48 : 48 ≤ c.toNat)
    (hsep : c.toNat + 56 ≤ p.toNat)
    (hpm : st4.mem.read64 (UInt32.ofNat ((p.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hpr : st4.mem.read64 (UInt32.ofNat ((p.toNat - 40) % 4294967296)) = 1)
    (hpk : st4.mem.read64 (UInt32.ofNat ((p.toNat - 24) % 4294967296)) = 1)
    (hpl : st4.mem.read64 (UInt32.ofNat ((p.toNat - 16) % 4294967296)) = 3)
    (hpmask : st4.mem.read64 (UInt32.ofNat ((p.toNat - 8) % 4294967296)) = 4)
    (hslot2 : st4.mem.read64 (UInt32.ofNat ((p.toNat + 16) % 4294967296)) = c)
    (hcm : st4.mem.read64 (UInt32.ofNat ((c.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hcr : st4.mem.read64 (UInt32.ofNat ((c.toNat - 40) % 4294967296)) = 1)
    (hck : st4.mem.read64 (UInt32.ofNat ((c.toNat - 24) % 4294967296)) = 1)
    (hcl : st4.mem.read64 (UInt32.ofNat ((c.toNat - 16) % 4294967296)) = 3)
    (hcmask : st4.mem.read64 (UInt32.ofNat ((c.toNat - 8) % 4294967296)) = 4)
    (hcslot2 : st4.mem.read64 (UInt32.ofNat ((c.toNat + 16) % 4294967296)) = 0)
    (hg1 : st4.globals.globals[1]? = some (.i64 g1v))
    (hg4 : st4.globals.globals[4]? = some (.i64 r4))
    (hg5 : st4.globals.globals[5]? = some (.i64 r5)) :
    TerminatesWith (m := «module») (id := 6) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (((st4.mem.write64 (c.toUInt32 - 40) 0).write64
          (c.toUInt32 - 8) g1v).write64 (p.toUInt32 - 40) 0).write64
          (p.toUInt32 - 8) c ∧
        st'.globals.globals =
          (((((st4.globals.globals.set 4 (.i64 (r4 + 1))).set 4
            (.i64 (r4 + 1 + 1))).set 5 (.i64 (r5 + 1))).set 1
            (.i64 c)).set 5 (.i64 (r5 + 1 + 1))).set 1 (.i64 p)) := by
  have hp0 : ¬ (p = 0) := by
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
      1 := by
    rw [hP24]
    exact hpk
  have hpl' : st4.mem.read64 (UInt32.ofNat ((p - 16).toNat % 4294967296)) =
      3 := by
    rw [hP16]
    exact hpl
  have hpmask' : st4.mem.read64 (UInt32.ofNat ((p - 8).toNat % 4294967296)) =
      4 := by
    rw [hP8]
    exact hpmask
  apply TerminatesWith.of_wp_entry_for (f := func6Def)
  · simp [«module»]
  · change wp «module» func6 _ st4
      { params := [.i64 p],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0],
        values := [] } env
    unfold func6
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
    rw [if_pos (by decide)]
    wp_run
    try simp
    refine ⟨by omega, by omega, ?_⟩
    try simp only [hpl', hpmask']
    try wp_run
    try simp
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun stX sX =>
        (∃ sl : Nat, sl ≤ 2 ∧
          sX = rFrame p 1 1 3 0 4 (UInt64.ofNat sl) 0 0 ∧
          stX.mem = st4.mem ∧
          stX.mem.pages = st4.mem.pages ∧
          stX.globals.globals =
            st4.globals.globals.set 4 (.i64 (r4 + 1))) ∨
        (sX = rFrame p 1 1 3 0 4 3 0 c ∧
          stX.mem = (st4.mem.write64 (c.toUInt32 - 40) 0).write64
            (c.toUInt32 - 8) g1v ∧
          stX.mem.pages = st4.mem.pages ∧
          stX.globals.globals =
            ((((st4.globals.globals.set 4 (.i64 (r4 + 1))).set 4
              (.i64 (r4 + 1 + 1))).set 5 (.i64 (r5 + 1))).set 1 (.i64 c))))
      (μ := fun _ sX =>
        match sX.locals with
        | _ :: _ :: _ :: _ :: _ :: .i64 l6 :: _ => 4 - l6.toNat
        | _ => 0)
    · exact Or.inl ⟨0, by omega, by simp [rFrame], rfl, rfl, rfl⟩
    · rintro stX sX
        (⟨sl, hsl, rfl, hm, hpg, hgl⟩ | ⟨rfl, hm, hpg, hgl⟩)
      · obtain rfl | rfl | rfl : sl = 0 ∨ sl = 1 ∨ sl = 2 := by omega
        · simp only [rFrame]
          wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by decide)]
          wp_run
          try simp
          exact ⟨1, by omega, by decide, hm, hpg, hgl⟩
        · simp only [rFrame]
          wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by decide)]
          wp_run
          try simp
          exact ⟨2, by omega, by decide, hm, hpg, hgl⟩
        · simp only [rFrame]
          wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_pos (by decide)]
          wp_run
          try simp
          refine ⟨by omega, ?_⟩
          have hslot2X : stX.mem.read64
              (UInt32.ofNat ((p.toNat + 16) % 4294967296)) = c := by
            rw [hm]
            exact hslot2
          simp only [hslot2X]
          refine wp_call_tw (func6_frees_leaf env _ c g1v (r4 + 1) r5
            hc48 (by omega) (by rw [hpg]; omega)
            (by rw [hm]; exact hcm)
            (by rw [hm]; exact hcr)
            (by rw [hm]; exact hck)
            (by rw [hm]; exact hcl)
            (by rw [hm]; exact hcmask)
            (by rw [hm]; exact hcslot2)
            (by rw [hgl, List.getElem?_set]
                simp only [if_neg (by omega : ¬ (4 = 1))]
                exact hg1)
            (by rw [hgl, List.getElem?_set]
                have hlen4 : 4 < st4.globals.globals.length := by
                  have := (List.getElem?_eq_some_iff.mp hg5).choose
                  omega
                simp [hlen4])
            (by rw [hgl, List.getElem?_set]
                simp only [if_neg (by omega : ¬ (4 = 5))]
                exact hg5)) ?_
          rintro st5 vs5 ⟨rfl, hm5, hgl5⟩
          wp_run
          try simp
          refine Or.inr ⟨?_, ?_, ?_⟩
          · rw [hm5, hm]
          · rw [hm5, Mem.write64_pages, Mem.write64_pages, hpg]
          · rw [hgl5, hgl]
            simp [List.set_set]
      · simp only [rFrame]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        wp_run
        try simp
        have hglen : 5 < st4.globals.globals.length :=
          (List.getElem?_eq_some_iff.mp hg5).choose
        have hg5X : stX.globals.globals[5]? = some (.i64 (r5 + 1)) := by
          rw [hgl]
          simp [List.getElem?_set, hglen]
        have hg1X : stX.globals.globals[1]? = some (.i64 c) := by
          rw [hgl]
          simp [List.getElem?_set, (by omega : 1 < st4.globals.globals.length)]
        rw [hg5X, hg1X]
        try simp
        have haP40 : UInt32.ofNat ((p - 40).toNat % 4294967296) =
            p.toUInt32 - 40 := by
          apply UInt32.toNat.inj
          rw [toUInt32_ofNat_mod_toNat, hP40,
            Wasm.UInt32.toNat_sub_of_le _ _ (by
              rw [UInt32.le_iff_toNat_le]
              have hb : (40 : UInt32).toNat = 40 := rfl
              rw [hb, toUInt32_toNat]
              omega)]
          have hb : (40 : UInt32).toNat = 40 := rfl
          rw [hb, toUInt32_toNat]
          omega
        have haP8 : UInt32.ofNat ((p - 8).toNat % 4294967296) =
            p.toUInt32 - 8 := by
          apply UInt32.toNat.inj
          rw [toUInt32_ofNat_mod_toNat, hP8,
            Wasm.UInt32.toNat_sub_of_le _ _ (by
              rw [UInt32.le_iff_toNat_le]
              have hb : (8 : UInt32).toNat = 8 := rfl
              rw [hb, toUInt32_toNat]
              omega)]
          have hb : (8 : UInt32).toNat = 8 := rfl
          rw [hb, toUInt32_toNat]
          omega
        try simp only [hm, haP40, haP8, Mem.write64_pages]
        refine ⟨by omega, by omega, by simp [func6Def], trivial, ?_⟩
        rw [hgl]
        simp [List.set_set]

private def eFrame
    (l6 l7 l8 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 : UInt64) :
    Locals :=
  { params := [],
    locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 l6,
      .i64 l7, .i64 l8, .i64 0, .i64 0, .i64 l11, .i64 l12, .i64 l13,
      .i64 l14, .i64 l15, .i64 l16, .i64 l17, .i64 l18, .i64 l19, .i64 l20,
      .i64 l21, .i64 l22],
    values := [] }

private def boxPhase2 : Wasm.Program :=
  [
  .block 0 0 [
    .loop 0 0 [
      .localGet 13,
      .constI64 (0 : UInt64),
      .eqI64,
      .br_if 1,
      .localGet 16,
      .constI64 (0 : UInt64),
      .neI64,
      .br_if 1,
      .localGet 13,
      .constI64 (32 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 14,
      .localGet 13,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 15,
      .localGet 14,
      .localGet 11,
      .geUI64,
      .iff 0 0 [
        .localGet 12,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .localGet 15,
          .globalSet 1
        ] [
          .localGet 12,
          .constI64 (8 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 15,
          .store64 (0 : UInt32)
        ],
        .localGet 13,
        .constI64 (48 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (5501223100278326855 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (40 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (32 : UInt64),
        .subI64,
        .wrapI64,
        .localGet 14,
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (24 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (16 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (3 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (8 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (4 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .localSet 16
      ] [
        .localGet 13,
        .localSet 12,
        .localGet 15,
        .localSet 13
      ],
      .br 0
    ]
  ],
  .localGet 16,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localGet 11,
    .addI64,
    .localSet 14,
    .localGet 14,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 14,
    .constI64 (1 : UInt64),
    .subI64,
    .constI64 (65536 : UInt64),
    .divUI64,
    .constI64 (1 : UInt64),
    .addI64,
    .localSet 15,
    .memorySize,
    .extendUI32,
    .localGet 15,
    .ltUI64,
    .iff 0 0 [
      .localGet 15,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const (4294967295 : UInt32),
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localSet 16,
    .localGet 14,
    .globalSet 0,
    .localGet 16,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 11,
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (3 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (4 : UInt64),
    .store64 (0 : UInt32)
  ] [],
  .globalGet 2,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 2,
  .localGet 16,
  .localSet 5,
  .localGet 5,
  .constI64 (0 : UInt64),
  .addI64,
  .wrapI64,
  .localGet 6,
  .store64 (0 : UInt32),
  .localGet 5,
  .constI64 (8 : UInt64),
  .addI64,
  .wrapI64,
  .localGet 7,
  .store64 (0 : UInt32),
  .localGet 5,
  .constI64 (16 : UInt64),
  .addI64,
  .wrapI64,
  .localGet 8,
  .store64 (0 : UInt32),
  .localGet 5,
  .localSet 0,
  .globalGet 4,
  .localSet 1,
  .globalGet 5,
  .localSet 2,
  .localGet 0,
  .call 6,
  .globalGet 5,
  .localSet 3,
  .globalGet 4,
  .localGet 1,
  .subI64,
  .constI64 (100 : UInt64),
  .mulI64,
  .localGet 3,
  .localGet 2,
  .subI64,
  .addI64,
  .localSet 4,
  .localGet 4
]

set_option Elab.async false in
/-- Phase two of the export: the node allocation over the already built nil
box, the release call tearing both down, and the measured counters. -/
private theorem boxPhase2_spec (env : HostEnv Unit) (st1 : Store Unit)
    (g0 g2 g3 g4 g5 : UInt64)
    (hFit32 : g0.toNat + 144 < 4294967296)
    (hFit : g0.toNat + 144 ≤ st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hg0 : st1.globals.globals[0]? = some (.i64 (g0 + 48 + 24)))
    (hg1 : st1.globals.globals[1]? = some (.i64 0))
    (hg2 : st1.globals.globals[2]? = some (.i64 (g2 + 1)))
    (hg3 : st1.globals.globals[3]? = some (.i64 g3))
    (hg4 : st1.globals.globals[4]? = some (.i64 g4))
    (hg5 : st1.globals.globals[5]? = some (.i64 g5))
    (hn0 : st1.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hn8 : st1.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hn24 : st1.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 1)
    (hn32 : st1.mem.read64 (UInt32.ofNat ((g0.toNat + 32) % 4294967296)) = 3)
    (hn40 : st1.mem.read64 (UInt32.ofNat ((g0.toNat + 40) % 4294967296)) = 4)
    (hn64 : st1.mem.read64 (UInt32.ofNat ((g0.toNat + 64) % 4294967296)) = 0) :
    wp «module» boxPhase2
      (fun c =>
        match c with
        | .Fallthrough st' s' =>
            (List.take func2Def.results.length s'.values =
              [Value.i64 202] ∧
            st'.globals.globals[1]? = some (.i64 (g0 + 48 + 24 + 48)) ∧
            st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
            st'.globals.globals[3]? = some (.i64 g3) ∧
            st'.globals.globals[4]? = some (.i64 (g4 + 1 + 1)) ∧
            st'.globals.globals[5]? = some (.i64 (g5 + 1 + 1)))
        | .Return st' vs =>
            (List.take func2Def.results.length vs =
              [Value.i64 202] ∧
            st'.globals.globals[1]? = some (.i64 (g0 + 48 + 24 + 48)) ∧
            st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
            st'.globals.globals[3]? = some (.i64 g3) ∧
            st'.globals.globals[4]? = some (.i64 (g4 + 1 + 1)) ∧
            st'.globals.globals[5]? = some (.i64 (g5 + 1 + 1)))
        | _ => False)
      st1
      (eFrame 1 7 (g0 + 48) 24 0 0 0 0 0 24 0 0 (g0 + 48 + 24)
        ((g0 + 48 + 24 - 1) / 65536 + 1) (g0 + 48)) env := by
  have hg0_32 : g0.toNat < 4294967296 := by omega
  simp only [boxPhase2, eFrame]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun stY sY =>
      sY = eFrame 1 7 (g0 + 48) 24 0 0 0 0 0 24 0 0 (g0 + 48 + 24)
        ((g0 + 48 + 24 - 1) / 65536 + 1) (g0 + 48) ∧
      stY.mem = st1.mem ∧
      stY.mem.pages = st1.mem.pages ∧
      stY.globals.globals = st1.globals.globals)
    (μ := fun _ _ => 0)
  · exact ⟨by simp [eFrame], rfl, rfl, rfl⟩
  · rintro stY sY ⟨rfl, hmY, hpgY, hglY⟩
    simp only [eFrame]
    wp_run
    try simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    have hg0Y : stY.globals.globals[0]? =
        some (.i64 (g0 + 48 + 24)) := by
      rw [hglY]
      exact hg0
    try simp only [hg0Y]
    try wp_run
    have hno_wrap2 : ¬ (g0 + 48 + 24 + 48 + 24 < g0 + 48 + 24) := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add,
        UInt64.toNat_add, UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (24 : UInt64).toNat = 24 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hno_wrap2])]
    wp_run
    try simp
    have h144 : (g0 + 48 + 24 + 48 + 24 : UInt64).toNat =
        g0.toNat + 144 := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add,
        UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (24 : UInt64).toNat = 24 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsub1b : (g0 + 48 + 24 + 48 + 24 - 1 : UInt64).toNat =
        g0.toNat + 143 := by
      rw [UInt64.toNat_sub, h144]
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [h1]
      omega
    have hpn2 : ((g0 + 48 + 24 + 48 + 24 - 1) / 65536 + 1 : UInt64).toNat =
        (g0.toNat + 143) / 65536 + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_div, hsub1b]
      have h65536 : (65536 : UInt64).toNat = 65536 := rfl
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [h65536, h1]
      omega
    have hp32Y : ((UInt32.ofNat stY.mem.pages).toUInt64).toNat =
        stY.mem.pages := by
      have hlt : stY.mem.pages < UInt32.size := by
        have hs : UInt32.size = 4294967296 := rfl
        rw [hpgY]
        omega
      have h1 : (UInt32.ofNat stY.mem.pages).toNat = stY.mem.pages :=
        UInt32.toNat_ofNat_of_lt' hlt
      simp [h1]
    have hgeM2 : (g0 + 48 + 24 + 48 + 24 - 1) / 65536 + 1 ≤
        (UInt32.ofNat stY.mem.pages).toUInt64 := by
      rw [UInt64.le_iff_toNat_le, hpn2, hp32Y, hpgY]
      omega
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hgeM2])]
    wp_run
    try simp only [hg0Y]
    try wp_run
    try simp
    have hsubBG : ∀ q : UInt64, q.toNat ≤ 48 →
        (g0 + 48 + 24 + 48 - q).toNat =
        g0.toNat + 120 - q.toNat := by
      intro q hq
      rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_add,
        UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (24 : UInt64).toNat = 24 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsubB40 : (g0 + 48 + 24 + 48 - 40 : UInt64).toNat =
        g0.toNat + 80 := by
      have h := hsubBG 40 (by decide)
      have hb : (40 : UInt64).toNat = 40 := rfl
      rw [hb] at h
      rw [h]
      omega
    have hsubB32 : (g0 + 48 + 24 + 48 - 32 : UInt64).toNat =
        g0.toNat + 88 := by
      have h := hsubBG 32 (by decide)
      have hb : (32 : UInt64).toNat = 32 := rfl
      rw [hb] at h
      rw [h]
      omega
    have hsubB24 : (g0 + 48 + 24 + 48 - 24 : UInt64).toNat =
        g0.toNat + 96 := by
      have h := hsubBG 24 (by decide)
      have hb : (24 : UInt64).toNat = 24 := rfl
      rw [hb] at h
      rw [h]
      omega
    have hsubB16 : (g0 + 48 + 24 + 48 - 16 : UInt64).toNat =
        g0.toNat + 104 := by
      have h := hsubBG 16 (by decide)
      have hb : (16 : UInt64).toNat = 16 := rfl
      rw [hb] at h
      rw [h]
      omega
    have hsubB8 : (g0 + 48 + 24 + 48 - 8 : UInt64).toNat =
        g0.toNat + 112 := by
      have h := hsubBG 8 (by decide)
      have hb : (8 : UInt64).toNat = 8 := rfl
      rw [hb] at h
      rw [h]
      omega
    rw [hsubB40, hsubB32, hsubB24, hsubB16, hsubB8]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      ?_⟩
    have hg2Y : stY.globals.globals[2]? = some (.i64 (g2 + 1)) := by
      rw [hglY]
      exact hg2
    try simp only [hg2Y]
    try wp_run
    try simp only [hg2Y]
    try wp_run
    refine ⟨by omega, by omega, by omega, ?_⟩
    have hg4Y : stY.globals.globals[4]? = some (.i64 g4) := by
      rw [hglY]
      exact hg4
    have hg5Y : stY.globals.globals[5]? = some (.i64 g5) := by
      rw [hglY]
      exact hg5
    try simp only [hg4Y, hg5Y]
    try wp_run
    try simp
    have hXm : (g0.toNat + 48 + 24 + 48) % 18446744073709551616 =
        g0.toNat + 120 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [hXm]
    have hNm : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) = 5501223100278326855 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    have hNr : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) = 1 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    have hNk : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) = 1 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    have hNl : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) = 3 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    have hNmask : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) = 4 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    have hNs2 : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) = (g0 + 48) := by
      rw [Mem.read64_write64_same]
    have hCm : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      rw [hmY]
      exact hn0
    have hCr : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      rw [hmY]
      exact hn8
    have hCk : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 1 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      rw [hmY]
      exact hn24
    have hCl : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 32) % 4294967296)) = 3 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      rw [hmY]
      exact hn32
    have hCmask : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 40) % 4294967296)) = 4 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      rw [hmY]
      exact hn40
    have hCs2 : (((((((((stY.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + 24) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 80) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 88) % 4294967296)) 24).write64 (UInt32.ofNat ((g0.toNat + 96) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 104) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 112) % 4294967296)) 4).write64 (UInt32.ofNat ((g0.toNat + 120) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 120 + 8) % 4294967296)) 7).write64 (UInt32.ofNat ((g0.toNat + 120 + 16) % 4294967296)) (g0 + 48)).read64
        (UInt32.ofNat ((g0.toNat + 64) % 4294967296)) = 0 := by
      rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      rw [hmY]
      exact hn64
    have hnodeN : (g0 + 48 + 24 + 48 : UInt64).toNat = g0.toNat + 120 := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (24 : UInt64).toNat = 24 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hchildN : (g0 + 48 : UInt64).toNat = g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      rw [ha]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    rw [show (g0.toNat + 48 + 24) = g0.toNat + 72 from by omega] at hNm
    have hlen5 : 5 < st1.globals.globals.length :=
      (List.getElem?_eq_some_iff.mp hg5).choose
    refine wp_call_tw (func6_frees_node env _
      (g0 + 48 + 24 + 48) (g0 + 48) 0 g4 g5
      (by rw [hnodeN]; omega)
      (by rw [hnodeN]; omega)
      (by rw [hnodeN, Mem.write64_pages, Mem.write64_pages, Mem.write64_pages,
            Mem.write64_pages, Mem.write64_pages, Mem.write64_pages,
            Mem.write64_pages, Mem.write64_pages, Mem.write64_pages, hpgY]
          omega)
      (by rw [hchildN]; omega)
      (by rw [hchildN, hnodeN]; omega)
      (by rw [show (g0 + 48 + 24 + 48 : UInt64).toNat - 48 = g0.toNat + 72 from
            by rw [hnodeN]; omega]
          exact hNm)
      (by rw [show (g0 + 48 + 24 + 48 : UInt64).toNat - 40 = g0.toNat + 80 from
            by rw [hnodeN]; omega]
          exact hNr)
      (by rw [show (g0 + 48 + 24 + 48 : UInt64).toNat - 24 = g0.toNat + 96 from
            by rw [hnodeN]; omega]
          exact hNk)
      (by rw [show (g0 + 48 + 24 + 48 : UInt64).toNat - 16 = g0.toNat + 104 from
            by rw [hnodeN]; omega]
          exact hNl)
      (by rw [show (g0 + 48 + 24 + 48 : UInt64).toNat - 8 = g0.toNat + 112 from
            by rw [hnodeN]; omega]
          exact hNmask)
      (by rw [show (g0 + 48 + 24 + 48 : UInt64).toNat + 16 = g0.toNat + 120 + 16
            from by rw [hnodeN]]
          exact hNs2)
      (by rw [show (g0 + 48 : UInt64).toNat - 48 = g0.toNat from
            by rw [hchildN]; omega]
          exact hCm)
      (by rw [show (g0 + 48 : UInt64).toNat - 40 = g0.toNat + 8 from
            by rw [hchildN]; omega]
          exact hCr)
      (by rw [show (g0 + 48 : UInt64).toNat - 24 = g0.toNat + 24 from
            by rw [hchildN]; omega]
          exact hCk)
      (by rw [show (g0 + 48 : UInt64).toNat - 16 = g0.toNat + 32 from
            by rw [hchildN]; omega]
          exact hCl)
      (by rw [show (g0 + 48 : UInt64).toNat - 8 = g0.toNat + 40 from
            by rw [hchildN]; omega]
          exact hCmask)
      (by rw [show (g0 + 48 : UInt64).toNat + 16 = g0.toNat + 64 from
            by rw [hchildN]]
          exact hCs2)
      (by dsimp only
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 1))]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (0 = 1))]
          rw [hglY]
          exact hg1)
      (by dsimp only
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 4))]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (0 = 4))]
          rw [hglY]
          exact hg4)
      (by dsimp only
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (2 = 5))]
          rw [List.getElem?_set]
          simp only [if_neg (by omega : ¬ (0 = 5))]
          rw [hglY]
          exact hg5)) ?_
    rintro st6 vs6 ⟨rfl, hm6, hgl6⟩
    wp_run
    try simp
    have h6g5 : st6.globals.globals[5]? = some (.i64 (g5 + 1 + 1)) := by
      rw [hgl6, hglY]
      simp [List.getElem?_set, hlen5]
    have h6g4 : st6.globals.globals[4]? = some (.i64 (g4 + 1 + 1)) := by
      rw [hgl6, hglY]
      simp [List.getElem?_set, (by omega : 4 < st1.globals.globals.length)]
    have h6g1 : st6.globals.globals[1]? =
        some (.i64 (g0 + 48 + 24 + 48)) := by
      rw [hgl6, hglY]
      simp [List.getElem?_set, (by omega : 1 < st1.globals.globals.length)]
    have h6g2 : st6.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) := by
      rw [hgl6, hglY]
      simp [List.getElem?_set, (by omega : 2 < st1.globals.globals.length)]
    have h6g3 : st6.globals.globals[3]? = some (.i64 g3) := by
      rw [hgl6, hglY]
      simp [List.getElem?_set]
      exact hg3
    rw [h6g5, h6g4]
    have hs4 : (g4 + 1 + 1 - g4 : UInt64) = 2 := by bv_decide
    have hs5 : (g5 + 1 + 1 - g5 : UInt64) = 2 := by bv_decide
    try simp only [hs4, hs5]
    try simp only [h6g1, h6g2, h6g3, h6g4, h6g5]
    refine ⟨?_, trivial, trivial, trivial, trivial, trivial⟩
    first
    | decide
    | simp [func2Def]
    | (simp only [func2Def]; decide)


/-- The export builds the one-link chain and frees it: two releases, two
frees, the measured value is the literal 202. -/
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.boxFreeStats"]
def BoxFreeSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (g0 g2 g3 g4 g5 : UInt64),
    g0.toNat + 144 < 4294967296 →
    g0.toNat + 144 ≤ st.mem.pages * 65536 →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 0) →
    st.globals.globals[2]? = some (.i64 g2) →
    st.globals.globals[3]? = some (.i64 g3) →
    st.globals.globals[4]? = some (.i64 g4) →
    st.globals.globals[5]? = some (.i64 g5) →
    TerminatesWith (m := «module») (id := 2) (initial := st) (env := env)
      []
      (fun st' vs =>
        vs = [.i64 202] ∧
        st'.globals.globals[1]? = some (.i64 (g0 + 48 + 24 + 48)) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
        st'.globals.globals[3]? = some (.i64 g3) ∧
        st'.globals.globals[4]? = some (.i64 (g4 + 1 + 1)) ∧
        st'.globals.globals[5]? = some (.i64 (g5 + 1 + 1)))

@[proves Project.BoxFree.Spec.BoxFreeSpec]
theorem boxFreeStats_correct : BoxFreeSpec := by
  intro env st g0 g2 g3 g4 g5 hFit32 hFit hPages hg0 hg1 hg2 hg3 hg4 hg5
  have hg0_32 : g0.toNat < 4294967296 := by omega
  apply TerminatesWith.of_wp_entry_for (f := func2Def)
  · simp [«module»]
  · change wp «module» func2 _ st
      { params := [],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func2
    wp_run
    try simp only [hg1]
    try wp_run
    try simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by decide)]
    wp_run
    try simp only [hg1]
    try wp_run
    try simp
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun stX sX => stX = st ∧
        sX = eFrame 1 7 0 0 0 0 0 0 0 24 0 0 0 0 0)
      (μ := fun _ _ => 0)
    · exact ⟨rfl, by simp [eFrame]⟩
    · rintro stX sX ⟨rfl, rfl⟩
      simp only [eFrame]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      try simp only [hg0]
      try wp_run
      have hno_wrap : ¬ (g0 + 48 + 24 < g0) := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (24 : UInt64).toNat = 24 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hno_wrap])]
      wp_run
      try simp
      have h72 : (g0 + 48 + 24 : UInt64).toNat = g0.toNat + 72 := by
        rw [UInt64.toNat_add, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (24 : UInt64).toNat = 24 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub1 : (g0 + 48 + 24 - 1 : UInt64).toNat = g0.toNat + 71 := by
        rw [UInt64.toNat_sub, h72]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1]
        omega
      have hpn : ((g0 + 48 + 24 - 1) / 65536 + 1 : UInt64).toNat =
          (g0.toNat + 71) / 65536 + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_div, hsub1]
        have h65536 : (65536 : UInt64).toNat = 65536 := rfl
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h65536, h1]
        omega
      have hp32X : ((UInt32.ofNat stX.mem.pages).toUInt64).toNat =
          stX.mem.pages := by
        have hlt : stX.mem.pages < UInt32.size := by
          have hs : UInt32.size = 4294967296 := rfl
          omega
        have h1 : (UInt32.ofNat stX.mem.pages).toNat = stX.mem.pages :=
          UInt32.toNat_ofNat_of_lt' hlt
        simp [h1]
      have hgeM : (g0 + 48 + 24 - 1) / 65536 + 1 ≤
          (UInt32.ofNat stX.mem.pages).toUInt64 := by
        rw [UInt64.le_iff_toNat_le, hpn, hp32X]
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hgeM])]
      wp_run
      try simp only [hg0]
      try wp_run
      try simp
      have hsubG : ∀ q : UInt64, q.toNat ≤ 48 →
          (g0 + 48 - q).toNat = g0.toNat + 48 - q.toNat := by
        intro q hq
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub48 : (g0 + 48 - 48 : UInt64).toNat = g0.toNat + 0 := by
        have h := hsubG 48 (by decide)
        have hb : (48 : UInt64).toNat = 48 := rfl
        rw [hb] at h
        rw [h]
        omega
      have hsub40 : (g0 + 48 - 40 : UInt64).toNat = g0.toNat + 8 := by
        have h := hsubG 40 (by decide)
        have hb : (40 : UInt64).toNat = 40 := rfl
        rw [hb] at h
        rw [h]
        omega
      have hsub32 : (g0 + 48 - 32 : UInt64).toNat = g0.toNat + 16 := by
        have h := hsubG 32 (by decide)
        have hb : (32 : UInt64).toNat = 32 := rfl
        rw [hb] at h
        rw [h]
        omega
      have hsub24 : (g0 + 48 - 24 : UInt64).toNat = g0.toNat + 24 := by
        have h := hsubG 24 (by decide)
        have hb : (24 : UInt64).toNat = 24 := rfl
        rw [hb] at h
        rw [h]
        omega
      have hsub16 : (g0 + 48 - 16 : UInt64).toNat = g0.toNat + 32 := by
        have h := hsubG 16 (by decide)
        have hb : (16 : UInt64).toNat = 16 := rfl
        rw [hb] at h
        rw [h]
        omega
      have hsub8 : (g0 + 48 - 8 : UInt64).toNat = g0.toNat + 40 := by
        have h := hsubG 8 (by decide)
        have hb : (8 : UInt64).toNat = 8 := rfl
        rw [hb] at h
        rw [h]
        omega
      try simp only [hg2]
      try wp_run
      try simp
      rw [hsub40, hsub32, hsub24, hsub16, hsub8]
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, ?_⟩
      refine wp_iff_cons rfl ?_
      rw [if_neg (by decide)]
      try wp_run
      try simp
      refine wp_iff_cons rfl ?_
      rw [if_neg (by decide)]
      wp_run
      try simp only [hg1]
      try wp_run
      try simp
      try simp only [hg1]
      try wp_run
      change wp «module» boxPhase2 _ _ _ env
      change wp «module» _ _ _ (eFrame 1 7 (g0 + 48) 24 0 0 0 0 0 24 0 0
        (g0 + 48 + 24) ((g0 + 48 + 24 - 1) / 65536 + 1) (g0 + 48)) env
      refine wp.imp (boxPhase2_spec env _ g0 g2 g3 g4 g5 hFit32
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
      · simp only [Mem.write64_pages]
        exact hFit
      · simp only [Mem.write64_pages]
        exact hPages
      · simp [List.getElem?_set, (List.getElem?_eq_some_iff.mp hg0).choose]
      · simp [List.getElem?_set]
        exact hg1
      · simp [List.getElem?_set, (List.getElem?_eq_some_iff.mp hg2).choose]
      · simp [List.getElem?_set]
        exact hg3
      · simp [List.getElem?_set]
        exact hg4
      · simp [List.getElem?_set]
        exact hg5
      · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
      · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
      · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
      · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
      · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
      · rw [show (((g0.toNat + 48) % 18446744073709551616 + 16) %
            4294967296 : Nat) = (g0.toNat + 64) % 4294967296 from by omega]
        rw [Mem.read64_write64_same]
      · intro c h
        cases c <;> exact h
end Project.BoxFree.Spec
