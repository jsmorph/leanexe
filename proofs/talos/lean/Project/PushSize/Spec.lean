import Project.PushSize.Program
import Project.Common
import Project.Runtime.Spec
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `pushBangSize`

The generated export allocates a fresh byte array, copies the input, appends
the byte `33`, releases the temporary, and returns its length.  The theorem
runs from any store whose free list is empty and whose heap top leaves room
for the allocation: the release path then puts the temporary at the head of
the free list with its refcount cleared and its capacity intact, the alloc,
release, and free counters each advance by one, and every byte below the old
heap top is unchanged.  The release function's raw-object path is proved as
its own theorem, `func4_frees_fresh_raw`, and consumed through the call rule.
-/

namespace Project.PushSize.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

/-- The rounded allocation size for a payload of `n` bytes. -/
private def allocSize (n : Nat) : Nat :=
  (n + 7) / 8 * 8

private def allocSizeU (len : UInt64) : UInt64 :=
  (len + 1 + 7) / 8 * 8

/-- Releasing a nonzero raw object with refcount one puts it at the head of
the free list: the refcount slot is cleared, the next-pointer slot receives
the old free-list head, global 1 points at the object, and the release and
free counters advance. -/
theorem func4_frees_fresh_raw (env : HostEnv Unit) (st4 : Store Unit)
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
    TerminatesWith (m := «module») (id := 4) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st4.mem.write64 ((p - 40).toUInt32) 0).write64
          ((p - 8).toUInt32) g1v ∧
        st'.globals.globals =
          ((st4.globals.globals.set 4 (.i64 (c4 + 1))).set 5
            (.i64 (c5 + 1))).set 1 (.i64 p)) :=
  Project.Runtime.release_frees_fresh_raw env «module» 4 st4 p g1v c4 c5
    (by rfl) rfl hp48 hp32 hfit hmagic hrc hkind hg1 hg4 hg5

private def vFrame
    (ptr len l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17
      l18 : UInt64) : Locals :=
  { params := [.i64 ptr, .i64 len],
    locals := [.i64 l2, .i64 l3, .i64 l4, .i64 l5, .i64 l6, .i64 l7, .i64 l8,
      .i64 l9, .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15,
      .i64 l16, .i64 l17, .i64 l18],
    values := [] }

/-- Copy-loop invariant: `k` input bytes are in the result region, nothing
below the old heap top has changed, the allocator state is the
post-allocation state, and the header of the fresh object reads back
magic, refcount one, its capacity, and the raw kind. -/
private def vInv (st0 : Store Unit) (ptr g0 g2 : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ bytes.length ∧
      s = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 0 ptr (UInt64.ofNat bytes.length) 33
        (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k)
        (allocSizeU (UInt64.ofNat bytes.length)) 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1)
        (g0 + 48) ∧
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
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: .i64 l12 :: _ =>
      bytes.length - l12.toNat
  | _ => 0

/-- The generated export `pushBangSize` allocates a temporary holding
`input ++ [33]`, releases it onto the free list, and returns its length. -/
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.pushBangSize"]
def PushSizeSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 g4 g5 : UInt64)
    (bytes : List UInt8),
    bytes.length + 1 < 4294967296 →
    ptr.toNat + bytes.length < 4294967296 →
    ptr.toNat + bytes.length ≤ g0.toNat →
    g0.toNat + 48 + allocSize (bytes.length + 1) < 4294967296 →
    g0.toNat + 48 + allocSize (bytes.length + 1) ≤ st.mem.pages * 65536 →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 0) →
    st.globals.globals[2]? = some (.i64 g2) →
    st.globals.globals[4]? = some (.i64 g4) →
    st.globals.globals[5]? = some (.i64 g5) →
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (UInt64.ofNat bytes.length + 1)] ∧
        st'.globals.globals[0]? =
          some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))) ∧
        st'.globals.globals[1]? = some (.i64 (g0 + 48)) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1)) ∧
        st'.globals.globals[3]? = st.globals.globals[3]? ∧
        st'.globals.globals[4]? = some (.i64 (g4 + 1)) ∧
        st'.globals.globals[5]? = some (.i64 (g5 + 1)) ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 0 ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
          allocSizeU (UInt64.ofNat bytes.length) ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 40) % 4294967296)) = 0 ∧
        (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a))

@[proves Project.PushSize.Spec.PushSizeSpec]
theorem pushBangSize_correct : PushSizeSpec := by
  intro env st ptr g0 g2 g4 g5 bytes hLen hPtr32 hBelow hFit32 hFit hPages
    hg0 hg1 hg2 hg4 hg5 hInput
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
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0],
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
        s1 = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
          (UInt64.ofNat bytes.length) 0 0 ptr (UInt64.ofNat bytes.length) 33
          0 (UInt64.ofNat bytes.length + 1) 0
          (allocSizeU (UInt64.ofNat bytes.length)) 0 0 0 0 0)
      (μ := fun _ _ => 0)
    · constructor
      · rfl
      · simp [vFrame, allocSizeU]
    · rintro st1 s1 ⟨rfl, rfl⟩
      simp only [vFrame]
      wp_run
      -- the free list is empty, so the walk exits on its first test
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
      have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
        rw [UInt64.toNat_sub, UInt64.toNat_add]
        have ha : (48 : UInt64).toNat = 48 := rfl
        rw [ha]
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
        · -- all bytes copied: exit, store the bang, release, return
          have hle : (UInt64.ofNat bytes.length) ≤ (UInt64.ofNat k) := by
            rw [UInt64.le_iff_toNat_le, hkU, hlenU]
            omega
          have hge : UInt64.ofNat k ≥ UInt64.ofNat bytes.length := hle
          rw [if_pos hge]
          try simp
          subst hkend
          have hgp : (g0 + 48 : UInt64).toNat = g0.toNat + 48 := by
            rw [UInt64.toNat_add]
            have hc : (48 : UInt64).toNat = 48 := rfl
            rw [hc]
            have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
            omega
          have hb0 : ((g0 + 48 - 48 : UInt64)).toUInt32 =
              UInt32.ofNat (g0.toNat % 4294967296) := by
            rw [toUInt32_eq_ofNat, hsub48]
          have hb40 : ((g0 + 48 - 40 : UInt64)).toUInt32 =
              UInt32.ofNat ((g0.toNat + 8) % 4294967296) := by
            rw [toUInt32_eq_ofNat, hsub40]
          have hb24 : ((g0 + 48 - 24 : UInt64)).toUInt32 =
              UInt32.ofNat ((g0.toNat + 24) % 4294967296) := by
            rw [toUInt32_eq_ofNat, hsub24]
          have hb8 : ((g0 + 48 - 8 : UInt64)).toUInt32 =
              UInt32.ofNat ((g0.toNat + 40) % 4294967296) := by
            rw [toUInt32_eq_ofNat, hsub8]
          have hglen : 5 < st1.globals.globals.length := by
            obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hg5
            exact h
          have hg0len : 0 < st1.globals.globals.length := by omega
          have hg1len : 1 < st1.globals.globals.length := by omega
          have hg2len : 2 < st1.globals.globals.length := by omega
          have hg4len : 4 < st1.globals.globals.length := by omega
          have hgnil : ¬ st1.globals.globals = [] := by
            intro h
            rw [h] at hglen
            simp at hglen
          refine ⟨by omega, ?_⟩
          refine wp_call_tw (func4_frees_fresh_raw env _ (g0 + 48) 0 g4 g5
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
          · rw [hgp]
            omega
          · rw [hgp]
            omega
          · dsimp only
            rw [write8_pages, hpg]
            omega
          · dsimp only
            rw [hb0, read64_write8_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh0
          · dsimp only
            rw [hb40, read64_write8_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh8
          · dsimp only
            rw [hb24, read64_write8_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh24
          · dsimp only
            rw [hgl]
            simp [List.getElem?_set, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
            exact (List.getElem?_eq_some_iff.mp hg1).choose_spec
          · dsimp only
            rw [hgl]
            simp [List.getElem?_set, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
            exact (List.getElem?_eq_some_iff.mp hg4).choose_spec
          · dsimp only
            rw [hgl]
            simp [List.getElem?_set, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
            exact (List.getElem?_eq_some_iff.mp hg5).choose_spec
          rintro st3 vs ⟨rfl, hmem3, hgl3⟩
          rw [hb40, hb8] at hmem3
          dsimp only at hgl3
          rw [hgl] at hgl3
          wp_run
          try simp
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [func0Def]
          · rw [hgl3]
            simp [List.getElem?_set, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
          · rw [hgl3]
            simp [List.getElem?_set, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
          · rw [hgl3]
            simp [List.getElem?_set, hg2, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
          · rw [hgl3]
            simp [List.getElem?_set, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
          · rw [hgl3]
            simp [List.getElem?_set, hg4, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
          · rw [hgl3]
            simp [List.getElem?_set, hg5, hgnil, hg0len, hg1len, hg2len, hg4len, hglen]
          · rw [hmem3]
            rw [read64_write64_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              Mem.read64_write64_same]
          · rw [hmem3]
            rw [read64_write64_ne _ _ _ _
              (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              read64_write64_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              read64_write8_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            exact hh16
          · rw [hmem3]
            rw [Mem.read64_write64_same]
          · intro a ha
            rw [hmem3]
            rw [write64_bytes_ne _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write64_bytes_ne _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write8_bytes_ne _ _ _
                (by rw [toUInt32_ofNat_mod_toNat]; omega)]
            exact hlo a ha
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

end Project.PushSize.Spec
