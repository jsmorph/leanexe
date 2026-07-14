import Project.ClobCancel.Scan
import Interpreter.Wasm.Wp.Call

/-!
# The `cancel` theorem

`func3` scans once for the argument id and records the first matching index
plus one.  An absent id returns status three and the borrowed input pointer.
The found branch allocates a fresh array and copies every other order.
-/

namespace Project.ClobCancel.Spec

open Wasm Project.Common Project.Clob Project.ClobQuote.Step
  Project.ClobQuote.Spec Project.ClobCancel

set_option maxHeartbeats 64000000
set_option maxRecDepth 1048576

def orderArrayBytes (n : Nat) : Nat :=
  8 + n * 5 * 8

def orderArrayBytesU (n : Nat) : UInt64 :=
  8 + UInt64.ofNat n * 5 * 8

abbrev FreshOrderArrayAt (st : Store Unit) (ptr capacity : UInt64) : Prop :=
  FreshFixedArrayAt st ptr capacity 5

private def cAllocFrame (ptr cid f2 f3 f4 f5 f6 idx len : UInt64) : Locals :=
  { params := [.i64 ptr, .i64 cid],
    locals := [.i64 f2, .i64 f3, .i64 f4, .i64 f5, .i64 f6,
      .i64 (idx + 1), .i64 0, .i64 0, .i64 ptr, .i64 idx, .i64 0,
      .i64 0, .i64 0, .i64 ptr, .i64 idx, .i64 len,
      .i64 (idx * 5), .i64 ((len - 1 - idx) * 5), .i64 (len - 1),
      .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 ((8 + (len - 1) * 5 * 8 + 7) / 8 * 8),
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    values := [] }

private def orderWord (st : Store Unit) (ptr : UInt64) (w : Nat) : UInt64 :=
  st.mem.read64
    (UInt32.ofNat ((ptr.toNat + (w + 1) * 8) % 4294967296))

private def cCopyFrame (ptr cid f2 f3 f4 f5 f6 g0 : UInt64)
    (i n k : Nat) : Locals :=
  { params := [.i64 ptr, .i64 cid],
    locals := [.i64 f2, .i64 f3, .i64 f4, .i64 f5, .i64 f6,
      .i64 (UInt64.ofNat i + 1), .i64 0, .i64 0, .i64 ptr,
      .i64 (UInt64.ofNat i), .i64 0, .i64 0, .i64 0, .i64 ptr,
      .i64 (UInt64.ofNat i), .i64 (UInt64.ofNat n),
      .i64 (UInt64.ofNat i * 5),
      .i64 ((UInt64.ofNat n - 1 - UInt64.ofNat i) * 5),
      .i64 (UInt64.ofNat n - 1), .i64 (g0 + 48), .i64 (UInt64.ofNat k),
      .i64 0, .i64 0,
      .i64 ((8 + (UInt64.ofNat n - 1) * 5 * 8 + 7) / 8 * 8),
      .i64 0, .i64 0,
      .i64 (g0 + 48 +
        (8 + (UInt64.ofNat n - 1) * 5 * 8 + 7) / 8 * 8),
      .i64 ((g0 + 48 +
        (8 + (UInt64.ofNat n - 1) * 5 * 8 + 7) / 8 * 8 - 1) /
          65536 + 1),
      .i64 (g0 + 48)],
    values := [] }

private def cCopyInv (st0 : Store Unit) (ptr cid g0 g2 : UInt64)
    (f2 f3 f4 f5 f6 : UInt64) (os : List OrderL) (i done dst src total : Nat) :
    AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ total ∧
      s = cCopyFrame ptr cid f2 f3 f4 f5 f6 g0 i os.length k ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        ((st0.globals.globals.set 0
          (.i64 (g0 + 48 + orderArrayBytesU (os.length - 1)))).set 2
          (.i64 (g2 + 1))) ∧
      FreshOrderArrayAt st (g0 + 48)
        (orderArrayBytesU (os.length - 1)) ∧
      st.mem.read64 ((g0 + 48).toUInt32) =
        UInt64.ofNat (os.length - 1) ∧
      (∀ a : Nat, a < g0.toNat → st.mem.bytes a = st0.mem.bytes a) ∧
      (∀ w : Nat, w < done →
        orderWord st (g0 + 48) w = orderWord st0 ptr w) ∧
      (∀ q : Nat, q < k →
        orderWord st (g0 + 48) (dst + q) = orderWord st0 ptr (src + q))

private def cCopyMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
    _ :: _ :: _ :: _ :: _ :: _ :: _ :: .i64 k :: _ => total - k.toNat
  | _ => 0

theorem func1_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 1) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 0] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func1 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func1
    wp_run
    simp [func1Def]

theorem func2_spec (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith (m := «module») (id := 2) (initial := st) (env := env)
      []
      (fun st' vs => vs = [.i64 3] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func2 _ st
      { params := [], locals := [.i64 0], values := [] } env
    unfold func2
    wp_run
    simp [func2Def]

/-- Canceling an absent id returns status three and the borrowed input
pointer, leaving the store unchanged. -/
def CancelNotFoundSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr cid : UInt64)
    (os : List OrderL),
    os.length < 4294967296 →
    OrdersAt st ptr os →
    idIdx os cid = none →
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 cid, .i64 ptr]
      (fun st' vs => vs = [.i64 ptr, .i64 3] ∧ st' = st)

@[proves Project.ClobCancel.Spec.CancelNotFoundSpec]
theorem cancel_notFound : CancelNotFoundSpec := by
  intro env st ptr cid os hlen hIn hAbsent
  have hHead := hIn.1.1
  have hHeadB := hIn.1.2
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» func3 _ st
      { params := [.i64 ptr, .i64 cid],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func3
    wp_run
    try simp
    rw [hHead]
    refine ⟨hHeadB, ?_⟩
    refine scanIndex_spec os hlen hIn ?_ ?_
    · intro _h f2 f3 f4 f5 f6
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      simp
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      refine wp_call_tw (func2_spec env st) ?_
      rintro st' vs ⟨rfl, rfl⟩
      wp_run
      simp [func3Def]
    · intro i hi
      rw [hAbsent] at hi
      cases hi

theorem cancel_found
    (env : HostEnv Unit) (st : Store Unit) (ptr cid g0 g2 : UInt64)
    (os : List OrderL) (i : Nat)
    (hlen : os.length < 4294967296)
    (hInput32 : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hBelow : ptr.toNat + (os.length * 5 + 1) * 8 ≤ g0.toNat)
    (hFit32 : g0.toNat + 48 + orderArrayBytes (os.length - 1) < 4294967296)
    (hFit : g0.toNat + 48 + orderArrayBytes (os.length - 1) ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hIn : OrdersAt st ptr os)
    (hFound : idIdx os cid = some i) :
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 cid, .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (g0 + 48), .i64 0] ∧
        OrdersAt st' (g0 + 48) (os.eraseIdx i) ∧
        FreshOrderArrayAt st' (g0 + 48) (orderArrayBytesU (os.length - 1)) ∧
        st'.mem.pages = st.mem.pages ∧
        st'.globals.globals =
          ((st.globals.globals.set 0
            (.i64 (g0 + 48 + orderArrayBytesU (os.length - 1)))).set 2
            (.i64 (g2 + 1))) ∧
        ∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a) := by
  have hi : i < os.length := by
    unfold idIdx at hFound
    exact (List.findIdx?_eq_some_iff_findIdx_eq.mp hFound).1
  have hiU : (UInt64.ofNat i).toNat = i :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hlenU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have houtU : (UInt64.ofNat (os.length - 1)).toNat = os.length - 1 :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hlenSub : UInt64.ofNat os.length - 1 =
      UInt64.ofNat (os.length - 1) := by
    apply UInt64.toNat.inj
    rw [toNat_sub_le _ _ (by simp [hlenU]; omega), hlenU, houtU]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
  have hbytesU : (orderArrayBytesU (os.length - 1)).toNat =
      orderArrayBytes (os.length - 1) := by
    unfold orderArrayBytesU orderArrayBytes
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul, houtU]
    have h5 : (5 : UInt64).toNat = 5 := rfl
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h5, h8]
    omega
  have hround : (orderArrayBytesU (os.length - 1) + 7) / 8 * 8 =
      orderArrayBytesU (os.length - 1) := by
    have h7 : (7 : UInt64).toNat = 7 := rfl
    have h8 : (8 : UInt64).toNat = 8 := rfl
    have hbytesLt : orderArrayBytes (os.length - 1) + 7 < UInt64.size := by
      rw [size_eq]
      unfold orderArrayBytes
      omega
    have hadd7 : (orderArrayBytesU (os.length - 1) + 7).toNat =
        orderArrayBytes (os.length - 1) + 7 := by
      rw [UInt64.toNat_add, hbytesU, h7, Nat.mod_eq_of_lt hbytesLt]
    have hroundedNat :
        (orderArrayBytes (os.length - 1) + 7) / 8 * 8 =
          orderArrayBytes (os.length - 1) := by
      unfold orderArrayBytes
      omega
    have hbytesLt' : orderArrayBytes (os.length - 1) < UInt64.size := by
      omega
    apply UInt64.toNat.inj
    rw [UInt64.toNat_mul, UInt64.toNat_div, hadd7]
    change (orderArrayBytes (os.length - 1) + 7) / 8 * 8 % UInt64.size =
      (orderArrayBytesU (os.length - 1)).toNat
    rw [hroundedNat, hbytesU, Nat.mod_eq_of_lt hbytesLt']
  have hpreU : (UInt64.ofNat i * 5).toNat = i * 5 := by
    rw [UInt64.toNat_mul, hiU]
    have h5 : (5 : UInt64).toNat = 5 := rfl
    rw [h5, Nat.mod_eq_of_lt]
    omega
  have hsuffixBase :
      (UInt64.ofNat os.length - 1 - UInt64.ofNat i).toNat =
        os.length - 1 - i := by
    rw [hlenSub, toNat_sub_le _ _ (by rw [houtU, hiU]; omega), houtU,
      hiU]
  have hsuffixU :
      ((UInt64.ofNat os.length - 1 - UInt64.ofNat i) * 5).toNat =
        (os.length - 1 - i) * 5 := by
    rw [UInt64.toNat_mul, hsuffixBase]
    have h5 : (5 : UInt64).toNat = 5 := rfl
    rw [h5, Nat.mod_eq_of_lt]
    omega
  have henc0 : UInt64.ofNat i + 1 ≠ 0 := by
    intro h
    have h' := congrArg UInt64.toNat h
    rw [toNat_add_one (by rw [hiU, size_eq]; omega), hiU] at h'
    simp at h'
  have hHead := hIn.1.1
  have hHeadB := hIn.1.2
  apply TerminatesWith.of_wp_entry_for (f := func3Def)
  · simp [«module»]
  · change wp «module» func3 _ st
      { params := [.i64 ptr, .i64 cid],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func3
    wp_run
    try simp
    rw [hHead]
    refine ⟨hHeadB, ?_⟩
    refine scanIndex_spec os hlen hIn ?_ ?_
    · intro hNone
      rw [hFound] at hNone
      cases hNone
    · intro j hj f2 f3 f4 f5 f6
      have hji : j = i := (Option.some.inj (hFound.symm.trans hj)).symm
      subst j
      wp_run
      simp [henc0]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run
      simp
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_call_tw (func1_spec env st) ?_
      rintro st1 vs ⟨rfl, rfl⟩
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp [henc0])]
      wp_run
      refine wp_iff_cons rfl ?_
      have hencLt : ¬ (UInt64.ofNat i + 1 < (1 : UInt64)) := by
        rw [UInt64.lt_iff_toNat_lt,
          toNat_add_one (by rw [hiU, size_eq]; omega), hiU]
        simp
      simp [hencLt]
      refine ⟨hHeadB, ?_⟩
      rw [hHead]
      refine wp_iff_cons rfl ?_
      have hiltU : UInt64.ofNat i < UInt64.ofNat os.length := by
        rw [UInt64.lt_iff_toNat_lt, hiU,
          toNat_ofNat_lt (by rw [size_eq]; omega)]
        exact hi
      simp [hiltU]
      refine ⟨hHeadB, ?_⟩
      rw [hHead]
      refine wp_iff_cons rfl ?_
      simp [hiltU]
      have hcapacity :
          (8 + (UInt64.ofNat os.length - 1) * 5 * 8 + 7) / 8 * 8 =
            orderArrayBytesU (os.length - 1) := by
        rw [hlenSub]
        change (orderArrayBytesU (os.length - 1) + 7) / 8 * 8 = _
        exact hround
      have hcapGe : ¬ (orderArrayBytesU (os.length - 1) < (8 : UInt64)) := by
        rw [UInt64.lt_iff_toNat_lt, hbytesU]
        have h8 : (8 : UInt64).toNat = 8 := rfl
        rw [h8]
        unfold orderArrayBytes
        omega
      refine wp_iff_cons rfl ?_
      simp [hcapacity, hcapGe]
      try simp only [hg1]
      try wp_run
      apply wp_block_cons
      apply wp_loop_cons
        (Inv := fun st2 s2 => st2 = st1 ∧
          s2 = cAllocFrame ptr cid f2 f3 f4 f5 f6 (UInt64.ofNat i)
            (UInt64.ofNat os.length))
        (μ := fun _ _ => 0)
      · constructor
        · rfl
        · simpa [cAllocFrame] using hcapacity.symm
      · rintro st2 s2 ⟨rfl, rfl⟩
        simp only [cAllocFrame]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        simp only [hg0]
        have hnoWrap : ¬
            (g0 + 48 +
                (8 + (UInt64.ofNat os.length - 1) * 5 * 8 + 7) / 8 * 8 <
              g0) := by
          rw [hcapacity, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
            UInt64.toNat_add, hbytesU]
          have h48 : (48 : UInt64).toNat = 48 := rfl
          rw [h48]
          omega
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hnoWrap])]
        wp_run
        simp
        have htop :
            (g0 + 48 +
                (8 + (UInt64.ofNat os.length - 1) * 5 * 8 + 7) / 8 * 8).toNat =
              g0.toNat + 48 + orderArrayBytes (os.length - 1) := by
          rw [hcapacity, UInt64.toNat_add, UInt64.toNat_add, hbytesU]
          have h48 : (48 : UInt64).toNat = 48 := rfl
          rw [h48]
          omega
        have htopSub :
            (g0 + 48 +
                (8 + (UInt64.ofNat os.length - 1) * 5 * 8 + 7) / 8 * 8 -
              1).toNat =
              g0.toNat + 48 + orderArrayBytes (os.length - 1) - 1 := by
          rw [toNat_sub_le _ _ (by rw [htop]; simp; omega), htop]
          have h1 : (1 : UInt64).toNat = 1 := rfl
          rw [h1]
        have hpagesNeeded :
            ((g0 + 48 +
                    (8 + (UInt64.ofNat os.length - 1) * 5 * 8 + 7) / 8 * 8 -
                  1) /
                65536 + 1).toNat =
              (g0.toNat + 48 + orderArrayBytes (os.length - 1) - 1) /
                  65536 +
                1 := by
          rw [UInt64.toNat_add, UInt64.toNat_div, htopSub]
          have h65536 : (65536 : UInt64).toNat = 65536 := rfl
          have h1 : (1 : UInt64).toNat = 1 := rfl
          rw [h65536, h1]
          omega
        have hmemorySize :
            ((UInt32.ofNat st2.mem.pages).toUInt64).toNat = st2.mem.pages := by
          have hlt : st2.mem.pages < UInt32.size := by
            have hs : UInt32.size = 4294967296 := rfl
            omega
          have hnat : (UInt32.ofNat st2.mem.pages).toNat = st2.mem.pages :=
            UInt32.toNat_ofNat_of_lt' hlt
          simp [hnat]
        have hnoGrow : ¬
            ((UInt32.ofNat st2.mem.pages).toUInt64 <
              (g0 + 48 +
                      (8 + (UInt64.ofNat os.length - 1) * 5 * 8 + 7) / 8 * 8 -
                    1) /
                  65536 +
                1) := by
          rw [UInt64.lt_iff_toNat_lt, hmemorySize, hpagesNeeded]
          omega
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hnoGrow])]
        wp_run
        simp only [hg0]
        try wp_run
        try simp
        have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
          rw [UInt64.toNat_sub, UInt64.toNat_add]
          have ha : (48 : UInt64).toNat = 48 := rfl
          have hb : (40 : UInt64).toNat = 40 := rfl
          rw [ha, hb]
          have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
          omega
        have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
          rw [UInt64.toNat_sub, UInt64.toNat_add]
          have ha : (48 : UInt64).toNat = 48 := rfl
          rw [ha]
          have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
          omega
        have hnewNat : (g0 + 48).toNat = g0.toNat + 48 := by
          rw [UInt64.toNat_add]
          have h48 : (48 : UInt64).toNat = 48 := rfl
          rw [h48]
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
        refine ⟨by
          rw [Nat.mod_eq_of_lt (by omega)]
          have hFit' := hFit
          unfold orderArrayBytes at hFit'
          omega, ?_⟩
        apply wp_block_cons
        apply wp_loop_cons
          (Inv := cCopyInv st2 ptr cid g0 g2 f2 f3 f4 f5 f6 os i
            0 0 0 (i * 5))
          (μ := cCopyMeasure (i * 5))
        · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [cCopyFrame]
          · rfl
          · simp only [hcapacity]
          · unfold FreshOrderArrayAt FreshFixedArrayAt
            simp only [toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24,
              hsub16, hsub8]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · read_frames
            · read_frames
            · read_frames
              exact hcapacity
            · read_frames
            · read_frames
            · read_frames
          · rw [toUInt32_eq_ofNat, hnewNat, Mem.read64_write64_same,
              hlenSub]
          · intro a ha
            rw [write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega),
              write64_bytes_lo _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
          · intro w hw
            omega
          · intro q hq
            omega
        · rintro st3 s3
            ⟨k, hk, rfl, hpg, hgl, hfresh, hlength, hlo, hfixed, hcurrent⟩
          have hkU : (UInt64.ofNat k).toNat = k :=
            toNat_ofNat_lt (by rw [size_eq]; omega)
          simp only [cCopyFrame]
          wp_run
          try simp
          by_cases hkend : k = i * 5
          · have hge : UInt64.ofNat k ≥ UInt64.ofNat i * 5 := by
              rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hpreU]
              omega
            rw [if_pos hge]
            try simp
            subst hkend
            apply wp_block_cons
            apply wp_loop_cons
              (Inv := cCopyInv st2 ptr cid g0 g2 f2 f3 f4 f5 f6 os i
                (i * 5) (i * 5) (i * 5 + 5) ((os.length - 1 - i) * 5))
              (μ := cCopyMeasure ((os.length - 1 - i) * 5))
            · refine ⟨0, Nat.zero_le _, ?_, hpg, hgl, hfresh, hlength, hlo,
                ?_, ?_⟩
              · simp [cCopyFrame]
              · intro w hw
                simpa using hcurrent w hw
              · intro q hq
                omega
            · rintro st4 s4
                ⟨k, hk, rfl, hpg4, hgl4, hfresh4, hlength4, hlo4, hprefix,
                  hsuffix⟩
              have hkU : (UInt64.ofNat k).toNat = k :=
                toNat_ofNat_lt (by rw [size_eq]; omega)
              simp only [cCopyFrame]
              wp_run
              try simp
              by_cases hkend : k = (os.length - 1 - i) * 5
              · have hge : UInt64.ofNat k ≥
                    (UInt64.ofNat os.length - 1 - UInt64.ofNat i) * 5 := by
                  rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hsuffixU]
                  omega
                rw [if_pos hge]
                try simp
                subst hkend
                have hreadPrefix (j r : Nat) (hj : j < i) (hr : r < 5) :
                    st4.mem.read64 (UInt32.ofNat (((g0 + 48).toNat +
                        (j * 5 + r + 1) * 8) % 4294967296)) =
                      st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                        (j * 5 + r + 1) * 8) % 4294967296)) := by
                  have hc := hprefix (j * 5 + r) (by omega)
                  unfold orderWord at hc
                  rw [hnewNat] at hc
                  rw [hnewNat]
                  exact hc
                have hreadSuffix (j r : Nat) (hji : i ≤ j)
                    (hj : j < os.length - 1) (hr : r < 5) :
                    st4.mem.read64 (UInt32.ofNat (((g0 + 48).toNat +
                        (j * 5 + r + 1) * 8) % 4294967296)) =
                      st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                        ((j + 1) * 5 + r + 1) * 8) % 4294967296)) := by
                  have hc := hsuffix ((j - i) * 5 + r) (by omega)
                  unfold orderWord at hc
                  rw [hnewNat] at hc
                  have hdst : i * 5 + ((j - i) * 5 + r) = j * 5 + r := by
                    omega
                  have hsrc : i * 5 + 5 + ((j - i) * 5 + r) =
                      (j + 1) * 5 + r := by
                    omega
                  rw [hdst, hsrc] at hc
                  rw [hnewNat]
                  exact hc
                have houtBound (j r : Nat) (hj : j < os.length - 1)
                    (hr : r < 5) :
                    ((g0 + 48).toNat + (j * 5 + r + 1) * 8) %
                          4294967296 + 8 ≤
                      st4.mem.pages * 65536 := by
                  rw [hnewNat, Nat.mod_eq_of_lt (by
                    unfold orderArrayBytes at hFit32
                    omega), hpg4]
                  have hFit' := hFit
                  unfold orderArrayBytes at hFit'
                  omega
                refine ⟨by simp [func3Def], ?_, hfresh4, hpg4, hgl4, hlo4⟩
                refine ⟨?_, ?_⟩
                · refine ⟨?_, ?_⟩
                  · rw [List.length_eraseIdx_of_lt hi]
                    simpa only [toUInt32_eq_ofNat] using hlength4
                  · rw [hnewNat, Nat.mod_eq_of_lt (by omega), hpg4]
                    have hFit' := hFit
                    unfold orderArrayBytes at hFit'
                    omega
                · intro j hj
                  have hjOut : j < os.length - 1 := by
                    rw [List.length_eraseIdx_of_lt hi] at hj
                    exact hj
                  rw [getElem!_pos (os.eraseIdx i) j hj,
                    List.getElem_eraseIdx hj]
                  by_cases hji : j < i
                  · rw [dif_pos hji]
                    obtain ⟨⟨hr1, _⟩, ⟨hr2, _⟩, ⟨hr3, _⟩, ⟨hr4, _⟩,
                      ⟨hr5, _⟩⟩ := hIn.2 j (by omega)
                    have hget : os[j]! = os[j] :=
                      getElem!_pos os j (by omega)
                    rw [hget] at hr1 hr2 hr3 hr4 hr5
                    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
                      ⟨?_, ?_⟩⟩
                    · calc
                        _ = _ := by simpa using hreadPrefix j 0 hji (by omega)
                        _ = _ := hr1
                    · simpa using houtBound j 0 hjOut (by omega)
                    · calc
                        _ = _ := by simpa using hreadPrefix j 1 hji (by omega)
                        _ = _ := hr2
                    · simpa using houtBound j 1 hjOut (by omega)
                    · calc
                        _ = _ := by simpa using hreadPrefix j 2 hji (by omega)
                        _ = _ := hr3
                    · simpa using houtBound j 2 hjOut (by omega)
                    · calc
                        _ = _ := by simpa using hreadPrefix j 3 hji (by omega)
                        _ = _ := hr4
                    · simpa using houtBound j 3 hjOut (by omega)
                    · calc
                        _ = _ := by simpa using hreadPrefix j 4 hji (by omega)
                        _ = _ := hr5
                    · simpa using houtBound j 4 hjOut (by omega)
                  · rw [dif_neg hji]
                    have hji' : i ≤ j := by omega
                    obtain ⟨⟨hr1, _⟩, ⟨hr2, _⟩, ⟨hr3, _⟩, ⟨hr4, _⟩,
                      ⟨hr5, _⟩⟩ := hIn.2 (j + 1) (by omega)
                    have hget : os[j + 1]! = os[j + 1] :=
                      getElem!_pos os (j + 1) (by omega)
                    rw [hget] at hr1 hr2 hr3 hr4 hr5
                    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
                      ⟨?_, ?_⟩⟩
                    · calc
                        _ = _ := by
                          simpa using hreadSuffix j 0 hji' hjOut (by omega)
                        _ = _ := hr1
                    · simpa using houtBound j 0 hjOut (by omega)
                    · calc
                        _ = _ := by
                          simpa using hreadSuffix j 1 hji' hjOut (by omega)
                        _ = _ := hr2
                    · simpa using houtBound j 1 hjOut (by omega)
                    · calc
                        _ = _ := by
                          simpa using hreadSuffix j 2 hji' hjOut (by omega)
                        _ = _ := hr3
                    · simpa using houtBound j 2 hjOut (by omega)
                    · calc
                        _ = _ := by
                          simpa using hreadSuffix j 3 hji' hjOut (by omega)
                        _ = _ := hr4
                    · simpa using houtBound j 3 hjOut (by omega)
                    · calc
                        _ = _ := by
                          simpa using hreadSuffix j 4 hji' hjOut (by omega)
                        _ = _ := hr5
                    · simpa using houtBound j 4 hjOut (by omega)
              · have hnge : ¬ (UInt64.ofNat k ≥
                    (UInt64.ofNat os.length - 1 - UInt64.ofNat i) * 5) := by
                  rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hsuffixU]
                  omega
                rw [if_neg hnge]
                try simp
                have hklt : k < (os.length - 1 - i) * 5 :=
                  Nat.lt_of_le_of_ne hk hkend
                have hsrcRead :
                    st4.mem.read64
                        (UInt32.ofNat ((ptr.toNat +
                          (i * 5 + 5 + k + 1) * 8) % 4294967296)) =
                      orderWord st2 ptr (i * 5 + 5 + k) := by
                  unfold orderWord
                  apply read64_congr
                  intro b hb
                  rw [toUInt32_ofNat_mod_toNat,
                    Nat.mod_eq_of_lt (by omega)]
                  exact hlo4 _ (by omega)
                have hdstLt :
                    g0.toNat + 48 + (i * 5 + k + 1) * 8 <
                      4294967296 := by
                  unfold orderArrayBytes at hFit32
                  omega
                refine ⟨?_, ?_, ?_, ?_⟩
                · rw [Nat.mod_eq_of_lt (by omega), hpg4]
                  have hFit' := hFit
                  unfold orderArrayBytes at hFit'
                  omega
                · rw [Nat.mod_eq_of_lt hdstLt, hpg4]
                  have hFit' := hFit
                  unfold orderArrayBytes at hFit'
                  have hwordFit :
                      g0.toNat + 48 + (i * 5 + k + 1) * 8 + 8 ≤
                        g0.toNat + 48 +
                          orderArrayBytes (os.length - 1) := by
                    unfold orderArrayBytes
                    omega
                  exact hwordFit.trans hFit'
                · have hkNext :
                      UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
                    apply UInt64.toNat.inj
                    rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
                      toNat_ofNat_lt (by rw [size_eq]; omega)]
                  refine ⟨k + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simp only [cCopyFrame, hkNext]
                  · rw [Mem.write64_pages, hpg4]
                  · exact hgl4
                  · obtain ⟨hh0, hh8, hh16, hh24, hh32, hh40⟩ := hfresh4
                    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                      rw [read64_write64_ne _ _ _ _
                        (by
                          simp only [toUInt32_eq_ofNat, hsub48, hsub40,
                            hsub32, hsub24, hsub16, hsub8,
                            toUInt32_ofNat_mod_toNat]
                          omega)]
                    · exact hh0
                    · exact hh8
                    · exact hh16
                    · exact hh24
                    · exact hh32
                    · exact hh40
                  · rw [read64_write64_ne _ _ _ _
                      (by
                        simp only [toUInt32_eq_ofNat, hnewNat,
                          toUInt32_ofNat_mod_toNat]
                        omega)]
                    exact hlength4
                  · intro a ha
                    rw [write64_bytes_lo _ _ _
                      (by
                        rw [toUInt32_ofNat_mod_toNat,
                          Nat.mod_eq_of_lt hdstLt]
                        omega)]
                    exact hlo4 a ha
                  · intro w hw
                    unfold orderWord
                    rw [hnewNat, read64_write64_ne _ _ _ _
                      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
                    have hp := hprefix w hw
                    unfold orderWord at hp
                    rw [hnewNat] at hp
                    exact hp
                  · intro q hq
                    unfold orderWord
                    rw [hnewNat]
                    by_cases hqk : q = k
                    · subst hqk
                      rw [Mem.read64_write64_same]
                      have hs := hsrcRead
                      unfold orderWord at hs
                      exact hs
                    · rw [read64_write64_ne _ _ _ _
                          (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
                      have hs := hsuffix q (by omega)
                      unfold orderWord at hs
                      rw [hnewNat] at hs
                      exact hs
                · simp [cCopyMeasure, hkU]
                  rw [Nat.mod_eq_of_lt (by omega)]
                  omega
          · have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat i * 5) := by
              rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hpreU]
              omega
            rw [if_neg hnge]
            try simp
            have hklt : k < i * 5 := Nat.lt_of_le_of_ne hk hkend
            have hsrcRead :
                st3.mem.read64
                    (UInt32.ofNat ((ptr.toNat + (k + 1) * 8) % 4294967296)) =
                  orderWord st2 ptr k := by
              unfold orderWord
              apply read64_congr
              intro b hb
              rw [toUInt32_ofNat_mod_toNat,
                Nat.mod_eq_of_lt (by omega)]
              exact hlo _ (by omega)
            have hdstLt : g0.toNat + 48 + (k + 1) * 8 < 4294967296 := by
              unfold orderArrayBytes at hFit32
              omega
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [Nat.mod_eq_of_lt (by omega), hpg]
              have hFit' := hFit
              unfold orderArrayBytes at hFit'
              omega
            · rw [Nat.mod_eq_of_lt hdstLt, hpg]
              have hFit' := hFit
              unfold orderArrayBytes at hFit'
              have hwordFit :
                  g0.toNat + 48 + (k + 1) * 8 + 8 ≤
                    g0.toNat + 48 + orderArrayBytes (os.length - 1) := by
                unfold orderArrayBytes
                omega
              exact hwordFit.trans hFit'
            · have hkNext : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
                apply UInt64.toNat.inj
                rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
                  toNat_ofNat_lt (by rw [size_eq]; omega)]
              refine ⟨k + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp only [cCopyFrame, hkNext]
              · rw [Mem.write64_pages, hpg]
              · exact hgl
              · obtain ⟨hh0, hh8, hh16, hh24, hh32, hh40⟩ := hfresh
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                  rw [read64_write64_ne _ _ _ _
                    (by
                      simp only [toUInt32_eq_ofNat, hsub48, hsub40, hsub32,
                        hsub24, hsub16, hsub8, toUInt32_ofNat_mod_toNat]
                      omega)]
                · exact hh0
                · exact hh8
                · exact hh16
                · exact hh24
                · exact hh32
                · exact hh40
              · rw [read64_write64_ne _ _ _ _
                  (by
                    simp only [toUInt32_eq_ofNat, hnewNat,
                      toUInt32_ofNat_mod_toNat]
                    omega)]
                exact hlength
              · intro a ha
                rw [write64_bytes_lo _ _ _
                  (by
                    rw [toUInt32_ofNat_mod_toNat,
                      Nat.mod_eq_of_lt hdstLt]
                    omega)]
                exact hlo a ha
              · intro w hw
                omega
              · intro q hq
                unfold orderWord
                rw [hnewNat]
                by_cases hqk : q = k
                · subst hqk
                  simp only [Nat.zero_add]
                  rw [Mem.read64_write64_same]
                  have hs := hsrcRead
                  unfold orderWord at hs
                  exact hs
                · rw [read64_write64_ne _ _ _ _
                      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
                  have hc := hcurrent q (by omega)
                  unfold orderWord at hc
                  rw [hnewNat] at hc
                  exact hc
            · simp [cCopyMeasure, hkU]
              rw [Nat.mod_eq_of_lt (by omega)]
              omega

/-- `CancelFoundReady` packages the allocator facts used by the found branch.
The input lies below the heap top, and the fresh result fits in initialized
memory without address wraparound.  The missing branch does not use it. -/
def CancelFoundReady (st : Store Unit) (ptr g0 g2 : UInt64)
    (os : List OrderL) : Prop :=
  ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296 ∧
  ptr.toNat + (os.length * 5 + 1) * 8 ≤ g0.toNat ∧
  g0.toNat + 48 + orderArrayBytes (os.length - 1) < 4294967296 ∧
  g0.toNat + 48 + orderArrayBytes (os.length - 1) ≤
    st.mem.pages * 65536 ∧
  st.mem.pages ≤ 65536 ∧
  st.globals.globals[0]? = some (.i64 g0) ∧
  st.globals.globals[1]? = some (.i64 0) ∧
  st.globals.globals[2]? = some (.i64 g2)

/-- `CancelPost` follows the two source branches selected by `idIdx`.  A
missing id returns the borrowed input with an unchanged store.  A found id
returns a refcount-one array with the erased contents, exact allocator
counters, and the stated memory frame. -/
def CancelPost (st st' : Store Unit) (ptr cid g0 g2 : UInt64)
    (os : List OrderL) (vs : List Value) : Prop :=
  match idIdx os cid with
  | none => vs = [.i64 ptr, .i64 3] ∧ st' = st
  | some i =>
      vs = [.i64 (g0 + 48), .i64 0] ∧
      OrdersAt st' (g0 + 48) (os.eraseIdx i) ∧
      FreshOrderArrayAt st' (g0 + 48) (orderArrayBytesU (os.length - 1)) ∧
      st'.mem.pages = st.mem.pages ∧
      st'.globals.globals =
        ((st.globals.globals.set 0
          (.i64 (g0 + 48 + orderArrayBytesU (os.length - 1)))).set 2
          (.i64 (g2 + 1))) ∧
      ∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a

/-- `CancelSpec` covers both branches of source `cancel` for every represented
order array.  The found branch requires initialized allocator state and
address space for its fresh result.  The missing branch retains its smaller
precondition and exact unchanged-store result. -/
@[spec_of "lean" "LeanExe.Examples.Clob.cancel"]
def CancelSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr cid g0 g2 : UInt64)
    (os : List OrderL),
    os.length < 4294967296 →
    OrdersAt st ptr os →
    (∀ i : Nat, idIdx os cid = some i → CancelFoundReady st ptr g0 g2 os) →
    TerminatesWith (m := «module») (id := 3) (initial := st) (env := env)
      [.i64 cid, .i64 ptr]
      (fun st' vs => CancelPost st st' ptr cid g0 g2 os vs)

@[proves Project.ClobCancel.Spec.CancelSpec]
theorem cancel_correct : CancelSpec := by
  intro env st ptr cid g0 g2 os hlen hIn hReady
  cases hidx : idIdx os cid with
  | none =>
      simpa [CancelPost, hidx] using
        cancel_notFound env st ptr cid os hlen hIn hidx
  | some i =>
      obtain ⟨hInput32, hBelow, hFit32, hFit, hPages, hg0, hg1, hg2⟩ :=
        hReady i hidx
      simpa [CancelPost, hidx] using
        cancel_found env st ptr cid g0 g2 os i hlen hInput32 hBelow hFit32
          hFit hPages hg0 hg1 hg2 hIn hidx

end Project.ClobCancel.Spec
