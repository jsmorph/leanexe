import Project.PairFree.Builds
import Project.PairFree.Frees

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
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length := by u64_omega
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
