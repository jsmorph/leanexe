import Project.LebU32.Iter
import Project.LebU32.NegIter

/-!
# The compiled `u32lebFuel` loop returns exactly `lebList 10 n`

The outer fuel loop runs under `lInv`; each iteration dispatches on the
rest test to the final-byte lemma (`posIterLemma`) or the continuation
lemma (`negIterLemma`).  The loop exits once the done flag is set, and
the function tail reads back the buffer pointer and length.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem func0_encodes (env : HostEnv Unit) (st : Store Unit)
    (n g0 g2 : UInt64)
    (hn32 : n.toNat < 4294967296)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2)) :
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 n, .i64 10]
      (fun st' vs =>
        vs = [.i64 (UInt64.ofNat (lebList 10 n).length),
              .i64 (bufPtr g0 (lebList 10 n).length),
              .i64 (bufPtr g0 (lebList 10 n).length)] ∧
        (∀ i : Nat, i < (lebList 10 n).length →
          st'.mem.bytes (objBase g0 ((lebList 10 n).length - 1) + 48 + i) =
            (lebList 10 n)[i]!) ∧
        st'.globals.globals[0]? =
          some (.i64 (g0 + UInt64.ofNat (56 * (lebList 10 n).length))) ∧
        st'.globals.globals[1]? = some (.i64 0) ∧
        st'.globals.globals[2]? =
          some (.i64 (g2 + UInt64.ofNat (lebList 10 n).length)) ∧
        st'.globals.globals[3]? = st.globals.globals[3]? ∧
        st'.globals.globals[4]? = st.globals.globals[4]? ∧
        st'.globals.globals[5]? = st.globals.globals[5]? ∧
        st'.mem.pages = st.mem.pages ∧
        (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a)) := by
  have hL5 : (lebList 10 n).length ≤ 5 := by
    refine lebList_length_of_lt 10 5 n (by omega) ?_ (by omega) (by omega)
    have : (128 : Nat) ^ 5 = 34359738368 := by norm_num
    omega
  have hL1 : 0 < (lebList 10 n).length := lebList_length_pos 10 n (by omega)
  refine TerminatesWith.of_wp_entry_for (f := func0Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 10, .i64 n, .i64 0, .i64 0, .i64 0],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0],
        values := [] } env
    unfold func0
    wp_run
    apply wp_block_cons
    apply wp_loop_cons (Inv := lInv st n g0 g2) (μ := lMeasure)
    · exact ⟨0, n, [], false, fun _ => 0, by simp, rfl, by omega,
        by simp [lFrame, bufPtr], by simp, rfl,
        by simpa using hg0, hg1, by simpa using hg2, rfl, rfl, rfl, rfl,
        fun a _ => rfl⟩
    · rintro stL sL ⟨k, v, written, done, e, hsplit, hwlen, hkle, hframe,
        hbytes, hlen, h0L, h1L, h2L, h3L, h4L, h5L, hpgL, hloL⟩
      cases done with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hframe hsplit
        subst hframe
        have hkL : k < (lebList 10 n).length := by
          have hpos : 0 < (lebList (10 - k) v).length :=
            lebList_length_pos _ _ (by omega)
          have hlen' := congrArg List.length hsplit
          simp only [List.length_append] at hlen'
          omega
        have hkU : (UInt64.ofNat k).toNat = k :=
          toNat_ofNat_lt (by rw [size_eq]; omega)
        have hfuelne : UInt64.ofNat (10 - k) ≠ 0 := by
          intro h
          have h2 := congrArg UInt64.toNat h
          rw [toNat_ofNat_lt (by rw [size_eq]; omega),
            show (0 : UInt64).toNat = 0 from rfl] at h2
          omega
        simp only [lFrame]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hfuelne])]
        try wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        try wp_run
        try simp
        by_cases hrest : v / 128 = 0
        · refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hrest])]
          try wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_pos (by decide)]
          try wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_pos (by decide)]
          have hfU : (UInt64.ofNat (10 - k)).toNat = 10 - k :=
            toNat_ofNat_lt (by rw [size_eq]; omega)
          refine posIterLemma env st stL n g0 g2 k v written
            (fun i => if i = 25 then v else if i = 26 then 128 else e i)
            (lMeasure stL (lFrame (UInt64.ofNat (10 - k)) v (bufPtr g0 k)
              (bufPtr g0 k) (UInt64.ofNat k) 0 0 0 0 e))
            _ hn32 hFit32 hFit hPages hL5 hsplit hwlen hkL hrest hbytes
            hlen h0L h1L h2L h3L h4L h5L hpgL hloL ?_ ?_ ?_ _ ?_
          · simp [lMeasure, lFrame, hfU]
          · intro st' msg
            rfl
          · intro st' s' h
            wp_run
            exact h
          · rfl
        · refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hrest])]
          try wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by decide)]
          try wp_run
          try simp
          refine wp_iff_cons rfl ?_
          rw [if_neg (by decide)]
          have hfU : (UInt64.ofNat (10 - k)).toNat = 10 - k :=
            toNat_ofNat_lt (by rw [size_eq]; omega)
          refine negIterLemma env st stL n g0 g2 k v written
            (fun i => if i = 25 then v else if i = 26 then 128 else e i)
            (lMeasure stL (lFrame (UInt64.ofNat (10 - k)) v (bufPtr g0 k)
              (bufPtr g0 k) (UInt64.ofNat k) 0 0 0 0 e))
            _ hn32 hFit32 hFit hPages hL5 hsplit hwlen hkL hrest hbytes
            hlen h0L h1L h2L h3L h4L h5L hpgL hloL ?_ ?_ ?_ _ ?_
          · simp [lMeasure, lFrame, hfU]
          · intro st' msg
            rfl
          · intro st' s' h
            wp_run
            exact h
          · rfl
      | true =>
        simp only [if_true] at hframe hsplit
        subst hframe
        have hwritten : written = lebList 10 n := by
          simpa using hsplit.symm
        have hkL : k = (lebList 10 n).length := by
          rw [← hwritten, hwlen]
        have hfuelne : UInt64.ofNat (11 - k) ≠ 0 := by
          intro h
          have h2 := congrArg UInt64.toNat h
          rw [toNat_ofNat_lt (by rw [size_eq]; omega),
            show (0 : UInt64).toNat = 0 from rfl] at h2
          omega
        simp only [lFrame]
        wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hfuelne])]
        try wp_run
        try simp
        refine wp_iff_cons rfl ?_
        rw [if_neg (by decide)]
        try wp_run
        try simp
        subst hkL
        have hmul : UInt64.ofNat (56 * (lebList 10 n).length) =
            56 * UInt64.ofNat (lebList 10 n).length := by
          apply UInt64.toNat.inj
          simp only [UInt64.toNat_ofNat', UInt64.toNat_mul,
            show (56 : UInt64).toNat = 56 from rfl]
          have hs : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
          omega
        refine ⟨?_, ?_, ?_, h1L, h2L, h3L, h4L, h5L, hpgL, hloL⟩
        · simp [func0Def]
        · intro i hi
          have hb := hbytes i hi
          rw [hwritten] at hb
          simpa using hb
        · rw [h0L, hmul]

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
/-- The exported encoder: for every `n` below `2 ^ 32` the artifact returns a
pointer to a buffer holding exactly the bytes of `lebList 10 n`, together
with its length. -/
theorem u32lebU64_correct (env : HostEnv Unit) (st : Store Unit)
    (n g0 g2 : UInt64)
    (hn32 : n.toNat < 4294967296)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2)) :
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      [.i64 n]
      (fun st' vs =>
        vs = [.i64 (UInt64.ofNat (lebList 10 n).length),
              .i64 (bufPtr g0 (lebList 10 n).length)] ∧
        (∀ i : Nat, i < (lebList 10 n).length →
          st'.mem.bytes (objBase g0 ((lebList 10 n).length - 1) + 48 + i) =
            (lebList 10 n)[i]!) ∧
        st'.mem.pages = st.mem.pages ∧
        (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a)) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func1 _ st
      { params := [.i64 n],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func1
    wp_run
    refine wp_call_tw (func0_encodes env st n g0 g2 hn32 hFit32 hFit hPages
      hg0 hg1 hg2) ?_
    rintro st' vs ⟨hvs, hbytes, h0, h1, h2, h3, h4, h5, hpg, hlo⟩
    subst hvs
    wp_run
    try simp
    exact ⟨by simp [func1Def], fun i hi => by simpa using hbytes i hi,
      hpg, hlo⟩


end Project.LebU32.Spec
