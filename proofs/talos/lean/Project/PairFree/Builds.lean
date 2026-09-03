import Project.PairFree.BuildTail

/-!
# Construction of the shared pair

The compiled `sharedPushPair` helper builds the temporary, the pair array
aliasing it twice, and retains the shared child once.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

private def pairPhase2Head : Wasm.Program :=
  pairAfterProg.take 8

private theorem pairAfter_split :
    pairAfterProg = pairPhase2Head ++ pairBuildTail := by
  simp only [pairPhase2Head, pairBuildTail, List.take_append_drop]

/-- The bang store and second-allocation phase from the copy loop's
exit, generic over the loop context's postcondition.  The done premise
takes the export's postcondition facts, furnished by the result pack. -/
private theorem buildsPhase2 (env : HostEnv Unit) (st1 st2 : Store Unit)
    (ptr g0 g2 g3 g4 g5 : UInt64) (bytes : List UInt8)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hg0_32 : g0.toNat < 4294967296)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hg1 : st1.globals.globals[1]? = some (.i64 0))
    (hg2 : st1.globals.globals[2]? = some (.i64 g2))
    (hg3 : st1.globals.globals[3]? = some (.i64 g3))
    (hg4 : st1.globals.globals[4]? = some (.i64 g4))
    (hg5 : st1.globals.globals[5]? = some (.i64 g5))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16)
    (hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24)
    (hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32)
    (hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40)
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hglen : 3 < st1.globals.globals.length)
    (hpg : st2.mem.pages = st1.mem.pages)
    (hgl : st2.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
        (.i64 (g2 + 1)))
    (hlo : ∀ a < g0.toNat, st2.mem.bytes a = st1.mem.bytes a)
    (hpref : ∀ i < bytes.length,
      st2.mem.bytes (g0.toNat + 48 + i) = bytes[i]!)
    (hh0 : st2.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh16 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
      allocSizeU (UInt64.ofNat bytes.length))
    (hh24 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) =
      0)
    (POST : Assertion Unit)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hDone : ∀ (st' : Store Unit) (s' : Locals),
      pairBuildResult st1 ptr g0 g2 g3 g4 g5 bytes st' s' →
      POST (.Fallthrough st' s'))
    (sP : Locals)
    (hsP : sP = { vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48) (UInt64.ofNat bytes.length + 1) 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) (g0 + 48) with values := [Value.i32 0] }) :
    wp «module» pairAfterProg POST
      { st2 with mem := (st2.mem.write8
          (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296)) 33) }
      sP env := by
  subst hsP
  rw [pairAfter_split]
  simp only [pairPhase2Head, pairAfterProg, List.take]
  have PA := buildsArith st1 g0 bytes hFit32 h17 hsub40 hg0_32 hlenU hszU
    hszN_ge hszN_ge8 hFit hPages
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
  wp_run_folded []
  change wp «module»
    (.constI64 0 :: .localSet 24 :: .constI64 0 :: .localSet 20 ::
      .globalGet 1 :: .localSet 21 :: .block 0 0 _ :: pairBuildTail)
    POST _ _ env
  wp_run_folded []
  rw [hg1S]
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  have h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hszU]
    rw [PA.1]
    omega
  let blockPOST : Assertion Unit := fun cont =>
    match cont with
    | .Fallthrough st' s' =>
      wp «module» pairBuildTail POST st' { s' with values := [] } env
    | .Break 0 st' s' =>
      wp «module» pairBuildTail POST st' { s' with values := [] } env
    | .Break (k + 1) st' s' => POST (.Break k st' s')
    | other => POST other
  let loopInv : AssertionF Unit := fun stX sX =>
    stX = { st2 with mem := (st2.mem.write8
      (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
      33) } ∧
    sX = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
      (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
      (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
      (UInt64.ofNat bytes.length) 33 (g0 + 48)
      (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
      ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) /
        65536 + 1) 0
  apply wp_block_cons
  refine wp.conseq (Q := blockPOST) ?_ ?_
  · intro cont h
    cases cont with
    | Fallthrough st' s' =>
      simpa only [blockPOST, List.take, List.drop, List.nil_append] using h
    | Break k st' s' =>
      cases k with
      | zero =>
        simpa only [blockPOST, List.take, List.drop, List.nil_append] using h
      | succ k =>
        simpa only [blockPOST] using h
    | Return st' values => simpa only [blockPOST] using h
    | Trap st' message => simpa only [blockPOST] using h
    | Invalid message => simpa only [blockPOST] using h
    | OutOfFuel => simpa only [blockPOST] using h
    | ReturnCall id st' values => simpa only [blockPOST] using h
    | Throwing tag args st' s' => simpa only [blockPOST] using h
  · apply wp_loop_cons
      (Q := blockPOST)
      (Inv := loopInv)
      (μ := fun _ _ => 0)
    · simp only [loopInv]
      simp [vFrame]
    · apply wp_loop_body_intro (m := «module») (env := env)
        (ps := 0) (rs := 0) (rest := []) (Q := blockPOST)
        (Inv := loopInv) (μ := fun _ _ => 0) (by
        intro st' msg
        simpa only [blockPOST] using hTrap st' msg)
      intro stX sX hInv POST' hTrap' _ _ hBreak
      simp only [loopInv] at hInv
      rcases hInv with ⟨rfl, rfl⟩
      wp_run_folded []
      simp
      apply hBreak 0
      change wp «module» pairBuildTail POST
        { st2 with mem := (st2.mem.write8
          (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
          33) }
        (vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
          (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
          (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
          (UInt64.ofNat bytes.length) 33 (g0 + 48)
          (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
          (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
          ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) /
            65536 + 1) 0) env
      exact buildsTail env st1 st2 ptr g0 g2 g3 g4 g5 bytes hLen hPtr32
        hBelow hFit32 hg0_32 hlenU hszU hszN_ge hszN_ge8 hFit hPages hg1
        hg2 hg3 hg4 hg5 hsub40 hsub32 hsub24 hsub16 hsub8 h17 hglen hpg hgl
        hh0 hh8 hh24 POST hTrap hDone


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
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length := by u64_omega
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
      have hb1 : g0.toNat % 4294967296 + 8 ≤ st1.mem.pages * 65536 := by
        omega
      have hb2 : (g0.toNat + 8) % 4294967296 + 8 ≤ st1.mem.pages * 65536 := by
        omega
      have hb3 : (g0.toNat + 16) % 4294967296 + 8 ≤ st1.mem.pages * 65536 := by
        omega
      have hb4 : (g0.toNat + 24) % 4294967296 + 8 ≤ st1.mem.pages * 65536 := by
        omega
      have hb5 : (g0.toNat + 32) % 4294967296 + 8 ≤ st1.mem.pages * 65536 := by
        omega
      have hb6 : (g0.toNat + 40) % 4294967296 + 8 ≤ st1.mem.pages * 65536 := by
        omega
      simp only [hg2]
      refine and6_and ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ ?_
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
        refine buildsBody env st1 st2 ptr g0 g2 bytes k _
          (bytes.length - k) hLen hPtr32 hBelow hFit32 hg0_32 hlenU hFit
          hPages hszU hszN_ge hszN_ge8 hInput hk hpg hgl hlo hpref hh0 hh8
          hh16 hh24 rfl ?_ ?_ ?_ _ rfl
        · intro st' msg
          rfl
        · intro st' s' h
          wp_run
          exact ⟨h.1, by
            have := h.2
            simp only [vMeasure, vFrame] at this ⊢
            u64_omega⟩
        · intro st' s' hx
          obtain ⟨hkeq, hst', hs'⟩ := hx
          subst hkeq
          rw [hst', hs']
          wp_run_folded []
          try simp
          refine ⟨by omega, ?_⟩
          try wp_run_folded []
          try wp_run_folded []
          try simp
          refine buildsPhase2 env st1 st2 ptr g0 g2 g3 g4 g5 bytes
            hLen hPtr32 hBelow hFit32 hg0_32 hlenU hszU hszN_ge hszN_ge8
            hFit hPages hg1 hg2 hg3 hg4 hg5 hsub40 hsub32 hsub24 hsub16
            hsub8 h17 (by
              obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hg3
              exact h) hpg hgl hlo hpref hh0 hh8 hh16 hh24 _ ?_ ?_ _ rfl
          · intro stt msg
            rfl
          · intro stt ss h
            simp only [pairBuildResult] at h
            try wp_run
            try simp
            exact h
end Project.PairFree.Spec
