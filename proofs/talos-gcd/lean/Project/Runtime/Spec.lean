/-
  Module-generic specifications for the shared runtime functions.  Each
  theorem takes the module and the function index as parameters, with a
  lookup hypothesis discharged per module by `rfl`, so artifact proofs
  consume runtime behavior without re-proving it.
-/

import Project.Runtime.Defs
import Project.Common
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.Runtime

open Wasm Project.Common

/-- The exported retain: checks the magic word, requires a live refcount,
increments it in place, advances the retain counter, and returns the
pointer unchanged. -/
theorem retain_spec (env : HostEnv Unit) (m : Module) (id : Nat)
    (st4 : Store Unit) (p c r3 : UInt64)
    (hf : m.funcs[id - m.imports.length]? = some retainFuncDef)
    (hImp : m.imports[id]? = none)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 (UInt32.ofNat ((p.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hrc : st4.mem.read64 (UInt32.ofNat ((p.toNat - 40) % 4294967296)) = c)
    (hc0 : 0 < c.toNat)
    (hg3 : st4.globals.globals[3]? = some (.i64 r3)) :
    TerminatesWith (m := m) (id := id) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [.i64 p] ∧
        st'.mem = st4.mem.write64 (p.toUInt32 - 40) (c + 1) ∧
        st'.globals.globals =
          st4.globals.globals.set 3 (.i64 (r3 + 1))) := by
  have hpne : ¬ (p = 0) := by
    intro h
    have := congrArg UInt64.toNat h
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0] at this
    omega
  have hcne : ¬ (c = 0) := by
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
  have hmagic' : st4.mem.read64 (UInt32.ofNat ((p - 48).toNat % 4294967296)) =
      5501223100278326855 := by
    rw [hP48]
    exact hmagic
  have hrc' : st4.mem.read64 (UInt32.ofNat ((p - 40).toNat % 4294967296)) =
      c := by
    rw [hP40]
    exact hrc
  refine TerminatesWith.of_wp_entry_for hf ?_ hImp
  change wp m retainBody _ st4
    { params := [.i64 p],
      locals := [.i64 0],
      values := [] } env
  unfold retainBody
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hpne])]
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
  try simp only [hg3]
  try wp_run
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
  exact ⟨by omega, by simp [retainFuncDef], by rw [haP40]⟩


/-- Releasing the null pointer returns immediately and changes nothing. -/
theorem release_null (env : HostEnv Unit) (m : Module) (id : Nat)
    (st4 : Store Unit)
    (hf : m.funcs[id - m.imports.length]? = some (releaseFuncDef id))
    (hImp : m.imports[id]? = none) :
    TerminatesWith (m := m) (id := id) (initial := st4) (env := env)
      [.i64 0]
      (fun st' vs => vs = [] ∧ st' = st4) := by
  refine TerminatesWith.of_wp_entry_for hf ?_ hImp
  change wp m (releaseBody id) _ st4
    { params := [.i64 0],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0],
      values := [] } env
  unfold releaseBody
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_pos (by decide)]
  wp_run
  try simp
  simp [releaseFuncDef]

/-- Releasing a shared object (refcount above one) decrements the count
in place and advances the release counter; nothing is freed. -/
theorem release_decrements (env : HostEnv Unit) (m : Module) (id : Nat)
    (st4 : Store Unit)
    (p c c4 : UInt64)
    (hf : m.funcs[id - m.imports.length]? = some (releaseFuncDef id))
    (hImp : m.imports[id]? = none)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 ((p - 48).toUInt32) = 5501223100278326855)
    (hrc : st4.mem.read64 ((p - 40).toUInt32) = c)
    (hc1 : 1 < c.toNat)
    (hg4 : st4.globals.globals[4]? = some (.i64 c4)) :
    TerminatesWith (m := m) (id := id) (initial := st4) (env := env)
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
  refine TerminatesWith.of_wp_entry_for hf ?_ hImp
  change wp m (releaseBody id) _ st4
    { params := [.i64 p],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0],
      values := [] } env
  unfold releaseBody
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
  exact ⟨by omega, by simp [releaseFuncDef], trivial⟩

/-- Releasing a raw-kind object at refcount one frees it: the count word
zeroes, the object links onto the free list, and the release and free
counters advance. -/
theorem release_frees_fresh_raw (env : HostEnv Unit) (m : Module) (id : Nat)
    (st4 : Store Unit)
    (p g1v c4 c5 : UInt64)
    (hf : m.funcs[id - m.imports.length]? = some (releaseFuncDef id))
    (hImp : m.imports[id]? = none)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 ((p - 48).toUInt32) = 5501223100278326855)
    (hrc : st4.mem.read64 ((p - 40).toUInt32) = 1)
    (hkind : st4.mem.read64 ((p - 24).toUInt32) = 0)
    (hg1 : st4.globals.globals[1]? = some (.i64 g1v))
    (hg4 : st4.globals.globals[4]? = some (.i64 c4))
    (hg5 : st4.globals.globals[5]? = some (.i64 c5)) :
    TerminatesWith (m := m) (id := id) (initial := st4) (env := env)
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
  refine TerminatesWith.of_wp_entry_for hf ?_ hImp
  change wp m (releaseBody id) _ st4
    { params := [.i64 p],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0],
      values := [] } env
  unfold releaseBody
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
  try simp [releaseFuncDef]
  exact ⟨by omega, by omega⟩

end Project.Runtime
