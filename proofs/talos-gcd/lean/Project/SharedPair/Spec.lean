import Project.SharedPair.Program
import Project.Common
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Specification for `sharedPushPair`

The export builds `input ++ [33]` once and returns the two-element array
`#[appended, appended]`.  The literal transfers ownership of the temporary at
its first element and retains it at the second, so the returned structure
holds two references backed by a refcount of exactly two.  The theorem runs
from any store whose free list is empty and whose heap top leaves room for
both allocations: the array cells alias the single temporary, the retain
counter advances by one, the alloc counter by two, and everything below the
old heap top is unchanged.  This is the first proof of the inline retain
sequence the compiler emits for shared children.
-/

namespace Project.SharedPair.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

/-- The rounded allocation size for a payload of `n` bytes. -/
macro "wp_run_big" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD])

private def allocSize (n : Nat) : Nat :=
  (n + 7) / 8 * 8

private def allocSizeU (len : UInt64) : UInt64 :=
  (len + 1 + 7) / 8 * 8

private def vFrame
    (ptr len l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19
      l20 l21 l22 : UInt64) : Locals :=
  { params := [.i64 ptr, .i64 len],
    locals := [.i64 l2, .i64 l3, .i64 l4, .i64 l5, .i64 l6, .i64 l7, .i64 l8,
      .i64 l9, .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15,
      .i64 l16, .i64 l17, .i64 l18, .i64 l19, .i64 l20, .i64 l21, .i64 l22],
    values := [] }

/-- Copy-loop invariant for the temporary: as in the push proofs, plus the
byte-array header facts the later phases read back. -/
private def vInv (st0 : Store Unit) (ptr g0 g2 : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ bytes.length ∧
      s = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k)
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
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      .i64 l16 :: _ =>
      bytes.length - l16.toNat
  | _ => 0

/-- The generated export builds the temporary, then the pair array whose two
elements alias it, and retains the shared child once. -/
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.sharedPushPair"]
def SharedPairSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 g3 : UInt64)
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
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)] ∧
        st'.globals.globals[0]? =
          some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
            56)) ∧
        st'.globals.globals[1]? = some (.i64 0) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
        st'.globals.globals[3]? = some (.i64 (g3 + 1)) ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 2 ∧
        (∀ i : Nat, i < bytes.length + 1 →
          st'.mem.bytes (g0.toNat + 48 + i) = (bytes ++ [33])[i]!) ∧
        (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a))

@[proves Project.SharedPair.Spec.SharedPairSpec]
theorem sharedPushPair_correct : SharedPairSpec := by
  intro env st ptr g0 g2 g3 bytes hLen hPtr32 hBelow hFit32 hFit hPages
    hg0 hg1 hg2 hg3 hInput
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
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
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
          (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr
          (UInt64.ofNat bytes.length) 33 0 (UInt64.ofNat bytes.length + 1) 0
          (allocSizeU (UInt64.ofNat bytes.length)) 0 0 0 0 0)
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
              sX = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
                (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
                (UInt64.ofNat bytes.length + 1) 0 0 ptr
                (UInt64.ofNat bytes.length) 33 (g0 + 48)
                (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56
                0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
                ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) /
                  65536 + 1)
                0)
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
            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [func0Def]
            · simp [List.getElem?_set, h0B]
            · rw [hstB]
              dsimp only
              exact hg1S
            · simp [List.getElem?_set, h2B]
            · simp [List.getElem?_set, h3B]
            · rw [haddr40, Mem.read64_write64_same]
            · intro i hi
              rw [write64_bytes_ne _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              rw [write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              rw [hstB]
              dsimp only
              by_cases hieq : i = bytes.length
              · subst hieq
                rw [write8_bytes_hit _ _ _
                  (by rw [toUInt32_ofNat_mod_toNat]; omega)]
                rw [List.getElem?_append_right (Nat.le_refl _)]
                simp
              · have hilt : i < bytes.length := by omega
                rw [write8_bytes_ne _ _ _
                  (by rw [toUInt32_ofNat_mod_toNat]; omega)]
                rw [hpref i hilt, getBang_eq hilt]
                rw [List.getElem?_append_left hilt, List.getElem?_eq_getElem hilt]
                simp
            · intro a ha
              rw [write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              rw [write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
                write64_bytes_lo _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
              rw [hstB]
              dsimp only
              rw [write8_bytes_ne _ _ _
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

/-- The exported retain: a nonzero pointer with a valid header and a live
refcount gains exactly one count, the retain counter advances, and the
pointer is returned.  This is the host-facing function 3; the inline retain
sequence inside the entry is proved as part of `sharedPushPair_correct`. -/
theorem func3_retains (env : HostEnv Unit) (st4 : Store Unit)
    (p c r3 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 (UInt32.ofNat ((p.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hrc : st4.mem.read64 (UInt32.ofNat ((p.toNat - 40) % 4294967296)) = c)
    (hc0 : 0 < c.toNat)
    (hg3 : st4.globals.globals[3]? = some (.i64 r3)) :
    TerminatesWith (m := «module») (id := 3) (initial := st4) (env := env)
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
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» func3 _ st4
      { params := [.i64 p],
        locals := [.i64 0],
        values := [] } env
    unfold func3
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
    exact ⟨by omega, by simp [func3Def], by rw [haP40]⟩

end Project.SharedPair.Spec
