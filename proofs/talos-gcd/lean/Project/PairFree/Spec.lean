import Project.PairFree.Program
import Project.Common
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call
import Std.Tactic.BVDecide

/-!
# Specification for `sharedPairFreeStats`

The export builds the shared pair through the compiled `sharedPushPair`
helper and then releases it.  The release function's array branch walks the
two cells and calls itself on the shared child twice: the first call
decrements the child's refcount from two to one, the second frees it onto
the free list, and the parent then frees itself in front of it.  The theorem
composes four function-level results: the helper's construction, the
decrement path, the raw free path, and the array path whose two recursive
calls consume the child lemmas at their concrete states.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

macro "wp_run_big" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD])

/-- The rounded allocation size for a payload of `n` bytes. -/
private def allocSize (n : Nat) : Nat :=
  (n + 7) / 8 * 8

private def allocSizeU (len : UInt64) : UInt64 :=
  (len + 1 + 7) / 8 * 8

/-- Releasing a nonzero raw object with refcount one puts it at the head of
the free list: the refcount slot is cleared, the next-pointer slot receives
the old free-list head, global 1 points at the object, and the release and
free counters advance. -/
theorem func7_frees_fresh_raw (env : HostEnv Unit) (st4 : Store Unit)
    (p g1v c4 c5 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 ((p - 48).toUInt32) = 5501223100278326855)
    (hrc : st4.mem.read64 ((p - 40).toUInt32) = 1)
    (hkind : st4.mem.read64 ((p - 24).toUInt32) = 0)
    (hg1 : st4.globals.globals[1]? = some (.i64 g1v))
    (hg4 : st4.globals.globals[4]? = some (.i64 c4))
    (hg5 : st4.globals.globals[5]? = some (.i64 c5)) :
    TerminatesWith (m := «module») (id := 7) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st4.mem.write64 ((p - 40).toUInt32) 0).write64
          ((p - 8).toUInt32) g1v ∧
        st'.globals.globals =
          ((st4.globals.globals.set 4 (.i64 (c4 + 1))).set 5
            (.i64 (c5 + 1))).set 1 (.i64 p)) := by
  have hp0 : ¬ (p = 0) := by
    intro h
    rw [h] at hp48
    simp at hp48
  have hsub : ∀ c : UInt64, c.toNat ≤ 48 →
      ((p - c).toUInt32).toNat = p.toNat - c.toNat := by
    intro c hc
    rw [toUInt32_toNat, UInt64.toNat_sub]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubN : ∀ c : UInt64, c.toNat ≤ 48 → (p - c).toNat = p.toNat - c.toNat := by
    intro c hc
    rw [UInt64.toNat_sub]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have h48N : (p - 48).toNat = p.toNat - 48 := hsubN 48 (by rfl)
  have h40N : (p - 40).toNat = p.toNat - 40 := hsubN 40 (by decide)
  have h24N : (p - 24).toNat = p.toNat - 24 := hsubN 24 (by decide)
  have h8N : (p - 8).toNat = p.toNat - 8 := hsubN 8 (by decide)
  have h48 : ((p - 48).toUInt32).toNat = p.toNat - 48 := hsub 48 (by rfl)
  have hmagic' : st4.mem.read64 (UInt32.ofNat ((p - 48).toNat % 4294967296)) =
      5501223100278326855 := by
    rw [← toUInt32_eq_ofNat]
    exact hmagic
  have hrc' : st4.mem.read64 (UInt32.ofNat ((p - 40).toNat % 4294967296)) =
      1 := by
    rw [← toUInt32_eq_ofNat]
    exact hrc
  have hkind' : st4.mem.read64 (UInt32.ofNat ((p - 24).toNat % 4294967296)) =
      0 := by
    rw [← toUInt32_eq_ofNat]
    exact hkind
  have hpu32 : p.toUInt32.toNat = p.toNat := by
    rw [toUInt32_toNat]
    omega
  have ha40 : UInt32.ofNat ((p - 40).toNat % 4294967296) = p.toUInt32 - 40 := by
    apply UInt32.toNat.inj
    rw [toUInt32_ofNat_mod_toNat,
      Wasm.UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]
        have hc : (40 : UInt32).toNat = 40 := rfl
        rw [hc, hpu32]
        omega)]
    have hc : (40 : UInt32).toNat = 40 := rfl
    rw [hc, hpu32]
    omega
  have hu8 : (p.toUInt32 - 8).toNat = p.toNat - 8 := by
    rw [Wasm.UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le]
      have hc : (8 : UInt32).toNat = 8 := rfl
      rw [hc, hpu32]
      omega)]
    have hc : (8 : UInt32).toNat = 8 := rfl
    rw [hc, hpu32]
  have ha8 : UInt32.ofNat ((p - 8).toNat % 4294967296) = p.toUInt32 - 8 := by
    apply UInt32.toNat.inj
    rw [toUInt32_ofNat_mod_toNat,
      Wasm.UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]
        have hc : (8 : UInt32).toNat = 8 := rfl
        rw [hc, hpu32]
        omega)]
    have hc : (8 : UInt32).toNat = 8 := rfl
    rw [hc, hpu32]
    omega
  have h40 : ((p - 40).toUInt32).toNat = p.toNat - 40 := hsub 40 (by decide)
  have h24 : ((p - 24).toUInt32).toNat = p.toNat - 24 := hsub 24 (by decide)
  have h8 : ((p - 8).toUInt32).toNat = p.toNat - 8 := hsub 8 (by decide)
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
    simp only [hmagic']
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp
    refine ⟨by omega, ?_⟩
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
    refine ⟨by omega, ?_⟩
    simp only [hkind']
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp only [hg5]
    try wp_run
    try simp only [hg1]
    try wp_run
    try simp
    try simp only [ha40, ha8]
    rw [hg5, hg1]
    try simp
    try simp [func7Def]
    exact ⟨by omega, by omega⟩

/-- Releasing an object whose refcount exceeds one decrements it and
returns: one store, one counter, nothing else. -/
theorem func7_decrements (env : HostEnv Unit) (st4 : Store Unit)
    (p c c4 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 ((p - 48).toUInt32) = 5501223100278326855)
    (hrc : st4.mem.read64 ((p - 40).toUInt32) = c)
    (hc1 : 1 < c.toNat)
    (hg4 : st4.globals.globals[4]? = some (.i64 c4)) :
    TerminatesWith (m := «module») (id := 7) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = st4.mem.write64 ((p - 40).toUInt32) (c - 1) ∧
        st'.globals.globals =
          st4.globals.globals.set 4 (.i64 (c4 + 1))) := by
  have hp0 : ¬ (p = 0) := by
    intro h
    rw [h] at hp48
    simp at hp48
  have hsub : ∀ q : UInt64, q.toNat ≤ 48 →
      ((p - q).toUInt32).toNat = p.toNat - q.toNat := by
    intro q hq
    rw [toUInt32_toNat, UInt64.toNat_sub]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have h48 : ((p - 48).toUInt32).toNat = p.toNat - 48 := hsub 48 (by rfl)
  have h40 : ((p - 40).toUInt32).toNat = p.toNat - 40 := hsub 40 (by decide)
  have hsubN : ∀ q : UInt64, q.toNat ≤ 48 → (p - q).toNat = p.toNat - q.toNat := by
    intro q hq
    rw [UInt64.toNat_sub]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have h48N : (p - 48).toNat = p.toNat - 48 := hsubN 48 (by rfl)
  have h40N : (p - 40).toNat = p.toNat - 40 := hsubN 40 (by decide)
  have hmagic' : st4.mem.read64 (UInt32.ofNat ((p - 48).toNat % 4294967296)) =
      5501223100278326855 := by
    rw [← toUInt32_eq_ofNat]
    exact hmagic
  have hrc' : st4.mem.read64 (UInt32.ofNat ((p - 40).toNat % 4294967296)) =
      c := by
    rw [← toUInt32_eq_ofNat]
    exact hrc
  have hcne : ¬ (c = 0) := by
    intro h
    rw [h] at hc1
    simp at hc1
  have hlt : (1 : UInt64) < c := by
    rw [UInt64.lt_iff_toNat_lt]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    exact hc1
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
    simp only [hmagic']
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp
    refine ⟨by omega, ?_⟩
    simp only [hrc']
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hcne])]
    wp_run
    try simp only [hg4]
    try wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hlt])]
    wp_run
    try simp
    have ha40 : UInt32.ofNat ((p - 40).toNat % 4294967296) =
        p.toUInt32 - 40 := by
      apply UInt32.toNat.inj
      rw [toUInt32_ofNat_mod_toNat,
        Wasm.UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          have hc : (40 : UInt32).toNat = 40 := rfl
          rw [hc, toUInt32_toNat]
          omega)]
      have hc : (40 : UInt32).toNat = 40 := rfl
      rw [hc, toUInt32_toNat]
      omega
    try simp only [ha40]
    exact ⟨by omega, by simp [func7Def], trivial⟩

private def vFrame
    (p0 ptr len l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19
      l20 l21 l22 l23 l24 : UInt64) : Locals :=
  { params := [.i64 p0, .i64 ptr, .i64 len],
    locals := [.i64 l3, .i64 l4, .i64 l5, .i64 l6, .i64 l7, .i64 l8, .i64 l9,
      .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15, .i64 l16,
      .i64 l17, .i64 l18, .i64 l19, .i64 l20, .i64 l21, .i64 l22, .i64 l23,
      .i64 l24],
    values := [] }

/-- Copy-loop invariant for the temporary: as in the push proofs, plus the
byte-array header facts the later phases read back. -/
private def vInv (st0 : Store Unit) (ptr g0 g2 : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ bytes.length ∧
      s = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 0 0 0 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k) (allocSizeU (UInt64.ofNat bytes.length)) 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) (g0 + 48) ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        ((st0.globals.globals.set 0
          (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
          (.i64 (g2 + 1))) ∧
      (∀ a : Nat, a < g0.toNat → st.mem.bytes a = st0.mem.bytes a) ∧
      (∀ i : Nat, i < k → st.mem.bytes (g0.toNat + 48 + i) = bytes[i]!) ∧
      st.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
        5501223100278326855 ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
        allocSizeU (UInt64.ofNat bytes.length) ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0

private def vMeasure (bytes : List UInt8) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: .i64 l18 :: _ =>
      bytes.length - l18.toNat
  | _ => 0

/-- The compiled `sharedPushPair` helper: builds the temporary, the pair
array aliasing it twice, and retains the shared child once.  The
postcondition exposes every header and cell fact the release function's
array branch reads. -/
theorem func0_builds
    (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 g3 g4 g5 : UInt64)
    (bytes : List UInt8)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hg3 : st.globals.globals[3]? = some (.i64 g3))
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5))
    (hInput : BytesAt st ptr bytes) :
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr, .i64 0]
      (fun st' vs =>
        vs = [.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48), .i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)] ∧
        st'.mem.pages = st.mem.pages ∧
        st'.globals.globals[0]? = some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)) ∧
        st'.globals.globals[1]? = some (.i64 0) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
        st'.globals.globals[3]? = some (.i64 (g3 + 1)) ∧
        st'.globals.globals[4]? = some (.i64 g4) ∧
        st'.globals.globals[5]? = some (.i64 g5) ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) =
          5501223100278326855 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 40) %
          4294967296)) = 1 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 24) %
          4294967296)) = 2 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 16) %
          4294967296)) = 3 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 8) %
          4294967296)) = 1 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) %
          4294967296)) = 2 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) %
          4294967296)) = g0 + 48 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) %
          4294967296)) = g0 + 48 ∧
        st'.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
          5501223100278326855 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 2 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0) := by
  have hg0_32 : g0.toNat < 4294967296 := by
    have := hFit32
    unfold allocSize at this
    omega
  have hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1) := by
    unfold allocSize
    omega
  have hszN_ge8 : 8 ≤ allocSize (bytes.length + 1) := by
    unfold allocSize
    omega
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hadd17 : (UInt64.ofNat bytes.length + 1 + 7).toNat = bytes.length + 8 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hlenU]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h7 : (7 : UInt64).toNat = 7 := rfl
    rw [h1, h7]
    omega
  have hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1) := by
    unfold allocSizeU allocSize
    rw [UInt64.toNat_mul, UInt64.toNat_div, hadd17]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    have : (bytes.length + 8) / 8 * 8 < 18446744073709551616 := by
      omega
    omega
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 0, .i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func0
    have hraw : ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8).toNat =
        allocSize (bytes.length + 1) := hszU
    have hnot_lt8 :
        ¬ ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8 < (8 : UInt64)) := by
      rw [UInt64.lt_iff_toNat_lt, hraw]
      have h8 : (8 : UInt64).toNat = 8 := rfl
      rw [h8]
      omega
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hnot_lt8])]
    wp_run
    try simp only [hg1]
    try wp_run
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun st1 s1 => st1 = st ∧
        s1 = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 0 0 0 0 0 0 ptr (UInt64.ofNat bytes.length) 33 0 (UInt64.ofNat bytes.length + 1) 0 (allocSizeU (UInt64.ofNat bytes.length)) 0 0 0 0 0)
      (μ := fun _ _ => 0)
    · constructor
      · rfl
      · simp [vFrame, allocSizeU]
    · rintro st1 s1 ⟨rfl, rfl⟩
      simp only [vFrame]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      try simp only [hg0]
      try wp_run
      have hno_wrap :
          ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) < g0) := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48, hszU]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hno_wrap])]
      wp_run
      simp
      have h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
          g0.toNat + 48 + allocSize (bytes.length + 1) := by
        rw [UInt64.toNat_add, UInt64.toNat_add, hszU]
        have h48 : (48 : UInt64).toNat = 48 := rfl
        rw [h48]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub1 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1).toNat =
          g0.toNat + 48 + allocSize (bytes.length + 1) - 1 := by
        rw [UInt64.toNat_sub, h17]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1]
        omega
      have hpn : ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536
          + 1).toNat =
          (g0.toNat + 48 + allocSize (bytes.length + 1) - 1) / 65536 + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_div, hsub1]
        have h65536 : (65536 : UInt64).toNat = 65536 := rfl
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h65536, h1]
        omega
      have hp32 : ((UInt32.ofNat st1.mem.pages).toUInt64).toNat = st1.mem.pages := by
        have hlt : st1.mem.pages < UInt32.size := by
          have hs : UInt32.size = 4294967296 := rfl
          omega
        have h1 : (UInt32.ofNat st1.mem.pages).toNat = st1.mem.pages :=
          UInt32.toNat_ofNat_of_lt' hlt
        simp [h1]
      have hng : ¬ ((UInt32.ofNat st1.mem.pages).toUInt64 <
          (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) := by
        rw [UInt64.lt_iff_toNat_lt, hp32, hpn]
        omega
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hng])]
      wp_run
      try simp only [hg0]
      try wp_run
      try simp
      have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (40 : UInt64).toNat = 40 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (32 : UInt64).toNat = 32 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (24 : UInt64).toNat = 24 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (16 : UInt64).toNat = 16 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      have hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        have hb : (8 : UInt64).toNat = 8 := rfl
        rw [ha, hb]
        have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
        omega
      rw [hsub40, hsub32, hsub24, hsub16, hsub8]
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
      simp only [hg2]
      apply wp_block_cons
      apply wp_loop_cons (Inv := vInv st1 ptr g0 g2 bytes) (μ := vMeasure bytes)
      · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [vFrame]
        · rfl
        · rfl
        · intro a ha
          rw [write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
        · intro i hi
          omega
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
        · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
            Mem.read64_write64_same]
      · rintro st2 s2 ⟨k, hk, rfl, hpg, hgl, hlo, hpref, hh0, hh8, hh16, hh24⟩
        have hkU : (UInt64.ofNat k).toNat = k :=
          toNat_ofNat_lt (by rw [size_eq]; omega)
        simp only [vFrame]
        wp_run
        try simp
        by_cases hkend : k = bytes.length
        · -- all bytes copied: exit, store the bang, then phase two
          have hle : (UInt64.ofNat bytes.length) ≤ (UInt64.ofNat k) := by
            rw [UInt64.le_iff_toNat_le, hkU, hlenU]
            omega
          have hge : UInt64.ofNat k ≥ UInt64.ofNat bytes.length := hle
          rw [if_pos hge]
          try simp
          subst hkend
          refine ⟨by omega, ?_⟩
          try wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by decide)]
          have hglen : 3 < st1.globals.globals.length := by
            obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hg3
            exact h
          have hg0len : 0 < st1.globals.globals.length := by omega
          have hg1len : 1 < st1.globals.globals.length := by omega
          have hg2len : 2 < st1.globals.globals.length := by omega
          have hgnil : ¬ st1.globals.globals = [] := by
            intro h
            rw [h] at hglen
            simp at hglen
          have hg1S : st2.globals.globals[1]? = some (.i64 0) := by
            rw [hgl]
            rw [List.getElem?_set, List.getElem?_set]
            simp only [if_neg (by omega : ¬ (2 = 1)), if_neg (by omega : ¬ (0 = 1))]
            exact hg1
          wp_run
          try simp only [hg1S]
          try wp_run
          try simp
          have h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
              g0.toNat + 48 + allocSize (bytes.length + 1) := by
            rw [UInt64.toNat_add, UInt64.toNat_add, hszU]
            have h48 : (48 : UInt64).toNat = 48 := rfl
            rw [h48]
            have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
            omega
          apply wp_block_cons
          apply wp_loop_cons
            (Inv := fun stX sX =>
              stX = { st2 with mem := (st2.mem.write8
                (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
                33) } ∧
              sX = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48) (UInt64.ofNat bytes.length + 1) 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) /
                  65536 + 1) 0)
            (μ := fun _ _ => 0)
          · exact ⟨rfl, by simp [vFrame]⟩
          · rintro stX sX ⟨rfl, rfl⟩
            simp only [vFrame]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            set stB : Store Unit := { st2 with mem := (st2.mem.write8
              (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
              33) } with hstB
            have hg0S : stB.globals.globals[0]? =
                some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))) := by
              rw [hstB]
              dsimp only
              rw [hgl]
              rw [List.getElem?_set, List.getElem?_set]
              simp only [if_neg (by omega : ¬ (2 = 0)),
                if_pos (rfl : (0 : Nat) = 0)]
              simp [hg0len]
            wp_run_big
            try simp only [hg0S]
            try wp_run_big
            have hno_wrap2 :
                ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 <
                  g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) := by
              rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add, h17]
              have ha : (48 : UInt64).toNat = 48 := rfl
              have hb : (56 : UInt64).toNat = 56 := rfl
              rw [ha, hb]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp [hno_wrap2])]
            wp_run_big
            try simp
            have h17b : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
                56).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) := by
              rw [UInt64.toNat_add, UInt64.toNat_add, h17]
              have ha : (48 : UInt64).toNat = 48 := rfl
              have hb : (56 : UInt64).toNat = 56 := rfl
              rw [ha, hb]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hsub1b : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
                56 - 1).toNat =
                g0.toNat + 152 + allocSize (bytes.length + 1) - 1 := by
              rw [UInt64.toNat_sub, h17b]
              have h1 : (1 : UInt64).toNat = 1 := rfl
              rw [h1]
              omega
            have hpn2 : ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
                56 - 1) / 65536 + 1).toNat =
                (g0.toNat + 152 + allocSize (bytes.length + 1) - 1) / 65536 +
                  1 := by
              rw [UInt64.toNat_add, UInt64.toNat_div, hsub1b]
              have h65536 : (65536 : UInt64).toNat = 65536 := rfl
              have h1 : (1 : UInt64).toNat = 1 := rfl
              rw [h65536, h1]
              omega
            have hpgB : stB.mem.pages = st1.mem.pages := by
              rw [hstB]
              dsimp only
              rw [write8_pages, hpg]
            have hp32b : ((UInt32.ofNat st1.mem.pages).toUInt64).toNat =
                st1.mem.pages := by
              have hlt : st1.mem.pages < UInt32.size := by
                have hs : UInt32.size = 4294967296 := rfl
                omega
              have h1 : (UInt32.ofNat st1.mem.pages).toNat = st1.mem.pages :=
                UInt32.toNat_ofNat_of_lt' hlt
              simp [h1]
            have hgeM : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
                56 - 1) / 65536 + 1 ≤
                UInt64.ofNat (st1.mem.pages % 4294967296) := by
              rw [UInt64.le_iff_toNat_le, hpn2,
                toNat_ofNat_lt (by rw [size_eq]; omega)]
              omega
            try simp only [hpgB]
            try wp_run_big
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp [hgeM])]
            wp_run_big
            try simp only [hg0S]
            try wp_run_big
            try simp
            try simp only [hg0S]
            try wp_run_big
            try simp
            have hB48 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
                48).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) := by
              rw [UInt64.toNat_add, h17]
              have ha : (48 : UInt64).toNat = 48 := rfl
              rw [ha]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hsubB40 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
                48 - 40).toNat =
                g0.toNat + 96 + allocSize (bytes.length + 1) - 40 := by
              rw [UInt64.toNat_sub, hB48]
              have hb : (40 : UInt64).toNat = 40 := rfl
              rw [hb]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hsubB32 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
                48 - 32).toNat =
                g0.toNat + 96 + allocSize (bytes.length + 1) - 32 := by
              rw [UInt64.toNat_sub, hB48]
              have hb : (32 : UInt64).toNat = 32 := rfl
              rw [hb]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hsubB24 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
                48 - 24).toNat =
                g0.toNat + 96 + allocSize (bytes.length + 1) - 24 := by
              rw [UInt64.toNat_sub, hB48]
              have hb : (24 : UInt64).toNat = 24 := rfl
              rw [hb]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hsubB16 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
                48 - 16).toNat =
                g0.toNat + 96 + allocSize (bytes.length + 1) - 16 := by
              rw [UInt64.toNat_sub, hB48]
              have hb : (16 : UInt64).toNat = 16 := rfl
              rw [hb]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hsubB8 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
                48 - 8).toNat =
                g0.toNat + 96 + allocSize (bytes.length + 1) - 8 := by
              rw [UInt64.toNat_sub, hB48]
              have hb : (8 : UInt64).toNat = 8 := rfl
              rw [hb]
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            rw [hsubB40, hsubB32, hsubB24, hsubB16, hsubB8]
            refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
              ?_⟩
            have hg2S : stB.globals.globals[2]? = some (.i64 (g2 + 1)) := by
              rw [hstB]
              dsimp only
              rw [hgl]
              rw [List.getElem?_set]
              simp [hg2len]
            simp only [hg2S]
            try wp_run_big
            try simp
            refine ⟨by omega, by omega, by omega, by omega, by omega,
              by omega, by omega, by omega, ?_⟩
            have hXmod : (g0.toNat + 48 +
                (allocSizeU (UInt64.ofNat bytes.length)).toNat) %
                18446744073709551616 =
                g0.toNat + 48 +
                  (allocSizeU (UInt64.ofNat bytes.length)).toNat :=
              Nat.mod_eq_of_lt (by omega)
            simp only [hXmod]
            have hM0 : (g0.toNat) % 4294967296 = g0.toNat :=
              Nat.mod_eq_of_lt (by omega)
            have hM8 : (g0.toNat + 8) % 4294967296 = g0.toNat + 8 :=
              Nat.mod_eq_of_lt (by omega)
            have hMg : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat :=
              Nat.mod_eq_of_lt (by omega)
            have hMh40 : (g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 :=
              Nat.mod_eq_of_lt (by omega)
            have hMh32 : (g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 32 :=
              Nat.mod_eq_of_lt (by omega)
            have hMh24 : (g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 :=
              Nat.mod_eq_of_lt (by omega)
            have hMh16 : (g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 :=
              Nat.mod_eq_of_lt (by omega)
            have hMh8 : (g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 :=
              Nat.mod_eq_of_lt (by omega)
            have hMc0 : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 :=
              Nat.mod_eq_of_lt (by omega)
            have hMc8 : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8 :=
              Nat.mod_eq_of_lt (by omega)
            have hMc16 : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16 :=
              Nat.mod_eq_of_lt (by omega)
            have hMc24 : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24 :=
              Nat.mod_eq_of_lt (by omega)
            have hMc32 : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32 :=
              Nat.mod_eq_of_lt (by omega)
            have hMc40 : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40 :=
              Nat.mod_eq_of_lt (by omega)
            have hMc48 : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48 :=
              Nat.mod_eq_of_lt (by omega)
            have hpne : ¬ ((g0 + 48 : UInt64) = 0) := by
              intro h
              have := congrArg UInt64.toNat h
              rw [UInt64.toNat_add] at this
              have hc : (48 : UInt64).toNat = 48 := rfl
              have h0 : (0 : UInt64).toNat = 0 := rfl
              rw [hc, h0] at this
              have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
              omega
            have hcell : (((((((((((((stB.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296)) 56).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296)) (UInt64.ofNat bytes.length + 1)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296)) (UInt64.ofNat bytes.length + 1)).read64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) = g0 + 48 := by
              rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                Mem.read64_write64_same]
            have hmagic2 : (((((((((((((stB.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296)) 56).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296)) (UInt64.ofNat bytes.length + 1)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296)) (UInt64.ofNat bytes.length + 1)).read64
                (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855 := by
              rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              rw [hstB]
              dsimp only
              rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hh0
            have hrc2 : (((((((((((((stB.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296)) 56).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296)) (UInt64.ofNat bytes.length + 1)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296)) (UInt64.ofNat bytes.length + 1)).read64
                (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 := by
              rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              rw [hstB]
              dsimp only
              rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hh8
            simp only [hcell]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp [hpne])]
            wp_run_big
            try simp
            have hmagic2e := hmagic2
            rw [hstB] at hmagic2e
            dsimp only at hmagic2e
            try simp only [hmagic2, hmagic2e]
            try wp_run_big
            try simp
            refine ⟨by omega, ?_⟩
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run_big
            try simp
            refine ⟨by omega, ?_⟩
            have hrc2e := hrc2
            rw [show (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) =
                (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) from by
              rw [hsub40]] at hrc2e
            rw [hstB] at hrc2e
            have hrc2d := hrc2e
            dsimp only at hrc2d
            rw [hrc2e]
            try wp_run_big
            try simp
            refine wp_iff_cons rfl ?_
            rw [if_neg (by decide)]
            wp_run_big
            have hg3S : ((stB.globals.globals.set 0
                (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) +
                  48 + 56))).set 2 (Value.i64 (g2 + 1 + 1)))[3]? =
                some (Value.i64 g3) := by
              rw [hstB]
              dsimp only
              rw [hgl]
              simp [List.getElem?_set, hglen]
              exact (List.getElem?_eq_some_iff.mp hg3).choose_spec
            try simp only [hg3S]
            try wp_run_big
            try simp
            have hlenB : stB.globals.globals.length =
                st1.globals.globals.length := by
              rw [hstB]
              dsimp only
              rw [hgl]
              simp
            have h0B : 0 < stB.globals.globals.length := by omega
            have h2B : 2 < stB.globals.globals.length := by omega
            have h3B : 3 < stB.globals.globals.length := by omega
            have haddr40 : (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) =
                (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) := by
              rw [hsub40]
            have hh0e : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
                5501223100278326855 := by
              rw [hstB]
              dsimp only
              rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hh0
            have hh24e : stB.mem.read64
                (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0 := by
              rw [hstB]
              dsimp only
              rw [read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              exact hh24
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [func0Def]
            · exact hpgB
            · simp [List.getElem?_set, h0B]
            · rw [hstB]
              dsimp only
              exact hg1S
            · simp [List.getElem?_set, h2B]
            · simp [List.getElem?_set, h3B]
            · rw [hstB]
              dsimp only
              rw [hgl]
              simp [List.getElem?_set, hglen]
              exact hg4
            · rw [hstB]
              dsimp only
              rw [hgl]
              simp [List.getElem?_set, hglen]
              exact hg5
            · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
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
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                Mem.read64_write64_same]
            · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
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
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                hh0e]
            · rw [haddr40, Mem.read64_write64_same]
            · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                hh24e]

        · -- copy one byte and continue
          have hklt : k < bytes.length := Nat.lt_of_le_of_ne hk hkend
          have hnotle : ¬ ((UInt64.ofNat bytes.length) ≤ (UInt64.ofNat k)) := by
            rw [UInt64.le_iff_toNat_le, hkU, hlenU]
            omega
          have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat bytes.length) := hnotle
          rw [if_neg hnge]
          try simp
          obtain ⟨hread, hbound⟩ := hInput k hklt
          have hsrcN : (ptr + UInt64.ofNat k).toNat = ptr.toNat + k := by
            rw [UInt64.toNat_add, hkU]
            have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
            omega
          have hsrc32 : (ptr + UInt64.ofNat k).toUInt32 =
              UInt32.ofNat ((ptr.toNat + k) % 4294967296) := by
            rw [toUInt32_eq_ofNat, hsrcN]
          rw [hsrc32] at hread hbound
          rw [toUInt32_ofNat_mod_toNat] at hbound
          have hkadd : (UInt64.ofNat k + 1) = UInt64.ofNat (k + 1) := by
            apply UInt64.toNat.inj
            rw [toNat_add_one, hkU, toNat_ofNat_lt (by rw [size_eq]; omega)]
            rw [hkU]
            rw [size_eq]
            omega
          have hreadval : st2.mem.read8
              (UInt32.ofNat ((ptr.toNat + k) % 4294967296)) = bytes[k]! := by
            rw [Mem.read8, toUInt32_ofNat_mod_toNat]
            rw [Nat.mod_eq_of_lt (by omega)]
            rw [hlo (ptr.toNat + k) (by omega)]
            have hthis := hread
            rw [Mem.read8, toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega)] at hthis
            exact hthis
          rw [hreadval]
          refine ⟨by omega, by omega,
            ⟨k + 1, hklt, ?_, hpg, hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · rw [← hkadd]
            simp only [vFrame]
          · intro a ha
            rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
            exact hlo a ha
          · intro i hi
            by_cases hieq : i = k
            · subst hieq
              rw [write8_bytes_hit _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
            · rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
              exact hpref i (by omega)
          · rw [read64_write8_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh0
          · rw [read64_write8_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh8
          · rw [read64_write8_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh16
          · rw [read64_write8_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh24
          · simp [vMeasure]
            omega

private def rFrame (p l1 l2 l3 l4 l5 l6 l7 l8 : UInt64) : Locals :=
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
                  simp [List.getElem?_set, hglen4])) ?_
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
              simp [List.getElem?_set, hglen1]
              exact (List.getElem?_eq_some_iff.mp hg1).choose_spec
            · rw [hglY]
              simp [List.getElem?_set, hglen4]
            · rw [hglY]
              simp [List.getElem?_set, hglen5]
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
          simp [List.getElem?_set, hglen5]
        have hg1X : stX.globals.globals[1]? = some (.i64 c) := by
          rw [hglX]
          simp [List.getElem?_set, hglen1]
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
        · simp [List.getElem?_set, hX1]
        · rw [hglX]
          simp [List.getElem?_set]
        · rw [hglX]
          simp [List.getElem?_set]
        · rw [hglX]
          simp [List.getElem?_set, hglen4]
        · simp [List.getElem?_set, hX5]
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

/-- The export builds the shared pair and frees it: three releases and two
frees tear down the whole two-level graph, and the measured value is the
literal 302. -/
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.sharedPairFreeStats"]
def PairFreeSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 g3 g4 g5 : UInt64)
    (bytes : List UInt8),
    bytes.length + 1 < 4294967296 →
    ptr.toNat + bytes.length < 4294967296 →
    ptr.toNat + bytes.length ≤ g0.toNat →
    g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296 →
    g0.toNat + 152 + allocSize (bytes.length + 1) ≤ st.mem.pages * 65536 →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 0) →
    st.globals.globals[2]? = some (.i64 g2) →
    st.globals.globals[3]? = some (.i64 g3) →
    st.globals.globals[4]? = some (.i64 g4) →
    st.globals.globals[5]? = some (.i64 g5) →
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun st' vs =>
        vs = [.i64 302] ∧
        st'.globals.globals[1]? = some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
        st'.globals.globals[3]? = some (.i64 (g3 + 1)) ∧
        st'.globals.globals[4]? = some (.i64 (g4 + 1 + 1 + 1)) ∧
        st'.globals.globals[5]? = some (.i64 (g5 + 1 + 1)))

@[proves Project.PairFree.Spec.PairFreeSpec]
theorem sharedPairFreeStats_correct : PairFreeSpec := by
  intro env st ptr g0 g2 g3 g4 g5 bytes hLen hPtr32 hBelow hFit32 hFit hPages
    hg0 hg1 hg2 hg3 hg4 hg5 hInput
  have hg0_32 : g0.toNat < 4294967296 := by
    have := hFit32
    unfold allocSize at this
    omega
  have hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1) := by
    unfold allocSize
    omega
  have hszN_ge8 : 8 ≤ allocSize (bytes.length + 1) := by
    unfold allocSize
    omega
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hadd17 : (UInt64.ofNat bytes.length + 1 + 7).toNat = bytes.length + 8 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hlenU]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h7 : (7 : UInt64).toNat = 7 := rfl
    rw [h1, h7]
    omega
  have hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat = allocSize (bytes.length + 1) := by
    unfold allocSizeU allocSize
    rw [UInt64.toNat_mul, UInt64.toNat_div, hadd17]
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h8]
    have : (bytes.length + 8) / 8 * 8 < 18446744073709551616 := by
      omega
    omega
  have harr : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, hszU]
    have hc : (48 : UInt64).toNat = 48 := rfl
    rw [hc]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hchild : (g0 + 48 : UInt64).toNat = g0.toNat + 48 := by
    rw [UInt64.toNat_add]
    have hc : (48 : UInt64).toNat = 48 := rfl
    rw [hc]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» func3 _ st
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func3
    wp_run
    refine wp_call_tw (func0_builds env st ptr g0 g2 g3 g4 g5 bytes hLen
      hPtr32 hBelow hFit32 hFit hPages hg0 hg1 hg2 hg3 hg4 hg5 hInput) ?_
    rintro st2 vs2 ⟨rfl, hpg2, h0', h1', h2', h3', h4', h5', hpm', hpr', hpk',
      hpw', hpmask', hplen', hc8', hc32', hcm', hcr', hck'⟩
    wp_run
    try simp only [h4']
    try wp_run
    try simp only [h5']
    try wp_run
    try simp
    refine wp_call_tw (func7_frees_pair env _
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48) (g0 + 48) g4 g5
      (by rw [harr]; omega)
      (by rw [harr]; omega)
      (by rw [harr, hpg2]; omega)
      (by rw [hchild]; omega)
      (by rw [hchild, harr]; omega)
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat - 48 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat from by
            rw [harr, hszU]; omega]
          exact hpm')
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat - 40 = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 from by
            rw [harr]]
          exact hpr')
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat - 24 = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 from by
            rw [harr]]
          exact hpk')
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat - 16 = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 from by
            rw [harr]]
          exact hpw')
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat - 8 = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 from by
            rw [harr]]
          exact hpmask')
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 from by
            rw [harr, hszU]; omega]
          exact hplen')
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat + 8 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8 from by
            rw [harr, hszU]; omega]
          exact hc8')
      (by rw [show (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat + 32 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32 from by
            rw [harr, hszU]; omega]
          exact hc32')
      (by rw [show (g0 + 48 : UInt64).toNat - 48 = g0.toNat from by
            rw [hchild]; omega]
          exact hcm')
      (by rw [show (g0 + 48 : UInt64).toNat - 40 = g0.toNat + 8 from by
            rw [hchild]; omega]
          exact hcr')
      (by rw [show (g0 + 48 : UInt64).toNat - 24 = g0.toNat + 24 from by
            rw [hchild]; omega]
          exact hck')
      h1' h4' h5') ?_
    rintro st3 vs3 ⟨rfl, hpg3, hg1'', hg2'', hg3'', hg4'', hg5'', hprc'',
      hcrc'', hlo3⟩
    wp_run
    try simp only [hg5'']
    try wp_run
    try simp only [hg4'']
    try wp_run
    try simp
    have hsub3 : (g4 + 1 + 1 + 1 - g4 : UInt64) = 3 := by bv_decide
    have hsub2 : (g5 + 1 + 1 - g5 : UInt64) = 2 := by bv_decide
    refine ⟨?_, hg1'', ?_, ?_⟩
    · simp [func3Def, hsub3, hsub2]
    · rw [hg2'']
      exact h2'
    · rw [hg3'']
      exact h3'

end Project.PairFree.Spec
