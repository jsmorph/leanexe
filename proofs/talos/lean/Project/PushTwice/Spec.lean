import Project.PushTwice.Empty
import Project.PushTwice.Reuse

/-!
# Specification for `pushTwiceSizes`

The export calls the compiled `pushBangSize` helper twice.  Each call
allocates a temporary holding `input ++ [byte]`, reads its length, and
releases it.  The first call allocates by extending the heap and leaves the
temporary on the free list; the second call's allocation finds that node and
takes the allocator's unlink path, so the heap top advances by one rounded
allocation for two allocations performed.  The helper's two behaviours are
proved as separate theorems over function 0 and composed through the call
rule; the release function's raw path is `func5_frees_fresh_raw`.
-/

namespace Project.PushTwice.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576
/-- The export performs two allocations but extends the heap once: the first
call's released temporary is reused by the second call's allocation, so the
heap top advances by a single rounded allocation while the alloc, release,
and free counters each advance by two. -/
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.pushTwiceSizes"]
def PushTwiceSpec : Prop :=
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
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun st' vs =>
        vs = [.i64 ((UInt64.ofNat bytes.length + 1) +
          (UInt64.ofNat bytes.length + 1))] ∧
        st'.globals.globals[0]? =
          some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))) ∧
        st'.globals.globals[1]? = some (.i64 (g0 + 48)) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
        st'.globals.globals[3]? = st.globals.globals[3]? ∧
        st'.globals.globals[4]? = some (.i64 (g4 + 1 + 1)) ∧
        st'.globals.globals[5]? = some (.i64 (g5 + 1 + 1)) ∧
        (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a))

@[proves Project.PushTwice.Spec.PushTwiceSpec]
theorem pushTwiceSizes_correct : PushTwiceSpec := by
  intro env st ptr g0 g2 g4 g5 bytes hLen hPtr32 hBelow hFit32 hFit hPages
    hg0 hg1 hg2 hg4 hg5 hInput
  have hg0_32 : g0.toNat < 4294967296 := by
    have := hFit32
    unfold allocSize at this
    omega
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length := by u64_omega
  have hlen1 : (UInt64.ofNat bytes.length + 1).toNat = bytes.length + 1 := by
    rw [UInt64.toNat_add, hlenU]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  apply TerminatesWith.of_wp_entry_for (f := func1Def)
  · simp [«module»]
  · change wp «module» func1 _ st
      { params := [.i64 ptr, .i64 (UInt64.ofNat bytes.length)],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func1
    wp_run
    refine wp_call_tw (func0_empty env st ptr g0 g2 g4 g5 bytes hLen hPtr32
      hBelow hFit32 hFit hPages hg0 hg1 hg2 hg4 hg5 hInput) ?_
    rintro st2 vs ⟨rfl, hpg2, hg0', hg1', hg2', hg3', hg4', hg5', hrc', hcap',
      hnext', hlo2⟩
    wp_run
    have hInput2 : BytesAt st2 ptr bytes := by
      intro i hi
      obtain ⟨hr, hb⟩ := hInput i hi
      constructor
      · rw [Mem.read8, toUInt32_eq_ofNat, toUInt32_ofNat_mod_toNat]
        rw [Mem.read8, toUInt32_eq_ofNat, toUInt32_ofNat_mod_toNat] at hr
        have haddr : (ptr + UInt64.ofNat i).toNat = ptr.toNat + i := by
          rw [UInt64.toNat_add, toNat_ofNat_lt (by rw [size_eq]; omega)]
          have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
          omega
        rw [haddr] at hr ⊢
        rw [Nat.mod_eq_of_lt (by omega)] at hr ⊢
        rw [hlo2 (ptr.toNat + i) (by omega)]
        exact hr
      · rw [hpg2]
        exact hb
    refine wp_call_tw (func0_reuse env st2 ptr g0 (g2 + 1) (g4 + 1) (g5 + 1)
      bytes hLen hPtr32 hBelow hFit32 (by rw [hpg2]; exact hFit)
      (by rw [hpg2]; exact hPages) hg0' hg1' hg2' hg4' hg5' hcap' hnext'
      hInput2) ?_
    rintro st3 vs ⟨rfl, hpg3, hg0'', hg1'', hg2'', hg3'', hg4'', hg5'', hrc'',
      hcap'', hnext'', hlo3⟩
    wp_run
    try simp
    have hno_wrap : ¬ ((UInt64.ofNat bytes.length + 1) +
        (UInt64.ofNat bytes.length + 1) < UInt64.ofNat bytes.length + 1) := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, hlen1]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hno_wrap])]
    wp_run
    try simp
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hg0''
    · exact hg1''
    · exact hg2''
    · rw [hg3'']
      exact hg3'
    · exact hg4''
    · exact hg5''
    · intro a ha
      rw [hlo3 a ha]
      exact hlo2 a ha

end Project.PushTwice.Spec
