import Project.ClobQuote.Step
import Project.ClobQuote.Epilogue

/-!
# The `quote` export theorem

`func10` reads the array length at the input pointer, loops over the
elements loading five fields each, calls `func9` to advance the six-field
accumulator, and returns the accumulator.  The theorem: for every order
list in memory, the export returns the fields of the source fold and
leaves the store untouched.
-/

set_option maxHeartbeats 64000000

namespace Project.ClobQuote.Spec

open Wasm Project.Common Project.Clob Project.ClobQuote Project.ClobQuote.Step

/-- The fold over the consumed prefix. -/
def foldTake (os : List OrderL) (k : Nat) : QuoteL :=
  (os.take k).foldl quoteStepL qInit

theorem foldTake_succ (os : List OrderL) (k : Nat) (h : k < os.length) :
    foldTake os (k + 1) = quoteStepL (foldTake os k) os[k]! := by
  unfold foldTake
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rw [List.foldl_append]
  simp [List.getElem?_eq_getElem h]

theorem foldTake_length (os : List OrderL) :
    foldTake os os.length = quoteFold os := by
  unfold foldTake quoteFold
  rw [List.take_length]

private def qFrame (ptr n idx b1 b2 b3 b4 b5 b6
    s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22
    s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34
    s46 s47 s48 s49 s50 s51 s52 s53 : UInt64) : Locals :=
  { params := [.i64 ptr],
    locals := [.i64 b1, .i64 b2, .i64 b3, .i64 b4, .i64 b5, .i64 b6,
      .i64 s7, .i64 s8, .i64 s9, .i64 s10, .i64 s11,
      .i64 s12, .i64 s13, .i64 s14, .i64 s15, .i64 s16, .i64 s17,
      .i64 s18, .i64 s19, .i64 s20, .i64 s21, .i64 s22,
      .i64 s23, .i64 s24, .i64 s25, .i64 s26, .i64 s27, .i64 s28,
      .i64 s29, .i64 s30, .i64 s31, .i64 s32, .i64 s33, .i64 s34,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 ptr, .i64 n, .i64 idx, .i64 n, .i64 n,
      .i64 s46, .i64 s47, .i64 s48, .i64 s49, .i64 s50, .i64 s51,
      .i64 s52, .i64 s53,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    values := [] }

private def qInv (st0 : Store Unit) (ptr : UInt64) (os : List OrderL) :
    AssertionF Unit :=
  fun st s =>
    st = st0 ∧
    ∃ k : Nat, k ≤ os.length ∧
    ∃ s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22
      s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34
      s46 s47 s48 s49 s50 s51 s52 s53 : UInt64,
      s = qFrame ptr (UInt64.ofNat os.length) (UInt64.ofNat k)
        (foldTake os k).hasBid (foldTake os k).bidPrice
        (foldTake os k).bidQty (foldTake os k).hasAsk
        (foldTake os k).askPrice (foldTake os k).askQty
        s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22
        s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34
        s46 s47 s48 s49 s50 s51 s52 s53

private def qMeasure (os : List OrderL) (_ : Store Unit) (s : Locals) :
    Nat :=
  match s.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
    _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
    _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
    .i64 idx :: _ => os.length - idx.toNat
  | _ => 0

/-- The export returns the six fields of the source fold over the order
array and leaves the store unchanged. -/
@[spec_of "lean" "LeanExe.Examples.Clob.quote"]
def ClobQuoteSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL),
    os.length < 4294967296 →
    OrdersAt st ptr os →
    TerminatesWith (m := «module») (id := 10) (initial := st) (env := env)
      [.i64 ptr]
      (fun st' vs =>
        vs = quoteVals (quoteFold os) ∧ st' = st)

@[proves Project.ClobQuote.Spec.ClobQuoteSpec]
theorem quote_correct : ClobQuoteSpec := by
  intro env st ptr os hlen hInput
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  have hlenU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  apply TerminatesWith.of_wp_entry_for (f := func10Def)
  · simp [«module»]
  · change wp «module» func10 _ st
      { params := [.i64 ptr],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func10
    wp_run
    try simp
    rw [hHead]
    refine ⟨hHeadB, ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    try simp
    apply wp_block_cons
    apply wp_loop_cons (Inv := qInv st ptr os) (μ := qMeasure os)
    · exact ⟨rfl, 0, Nat.zero_le _,
        0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0,
        ptr, 0, 0, 0, 0, 0, 0, 0,
        by simp [qFrame, foldTake, qInit]⟩
    · rintro st2 s2 ⟨rfl, k, hk, s7, s8, s9, s10, s11, s12, s13, s14,
        s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27,
        s28, s29, s30, s31, s32, s33, s34, s46, s47, s48, s49, s50, s51,
        s52, s53, rfl⟩
      have hkU : (UInt64.ofNat k).toNat = k :=
        toNat_ofNat_lt (by rw [size_eq]; omega)
      simp only [qFrame]
      wp_run
      try simp
      by_cases hkend : k = os.length
      · have hge : UInt64.ofNat k ≥ UInt64.ofNat os.length := by
          rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
          omega
        rw [if_pos hge]
        try wp_run
        try simp
        subst hkend
        simp [func10Def, foldTake_length, quoteVals]
      · have hklt : k < os.length := Nat.lt_of_le_of_ne hk hkend
        have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat os.length) := by
          rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
          omega
        rw [if_neg hnge]
        wp_run
        try simp
        obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩,
          ⟨hr5, hb5⟩⟩ := hElems k hklt
        refine ⟨hb1, hb2, hb3, hb4, hb5, ?_⟩
        rw [hr1, hr2, hr3, hr4, hr5]
        refine wp_call_tw (func9_spec env st2
          (foldTake os k).hasBid (foldTake os k).bidPrice
          (foldTake os k).bidQty (foldTake os k).hasAsk
          (foldTake os k).askPrice (foldTake os k).askQty
          os[k]!.oid os[k]!.otrader os[k]!.oside os[k]!.oprice
          os[k]!.oqty) ?_
        rintro st' vs ⟨hvs, rfl⟩
        rw [(foldTake_succ os k hklt).symm] at hvs
        generalize hq : foldTake os (k + 1) = qn at hvs
        obtain rfl := hvs
        simp only [quoteVals]
        refine epilogueA ?_
        refine epilogueB ?_
        refine epilogueC ?_
        refine epilogueD ?_
        refine epilogueE ?_
        have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
            toNat_ofNat_lt (by rw [size_eq]; omega)]
        rw [hkadd, ← hq]
        refine ⟨⟨rfl, k + 1, by omega, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, rfl⟩, ?_⟩
        simp only [qMeasure]
        rw [show (UInt64.ofNat (k + 1)).toNat = k + 1 from
          toNat_ofNat_lt (by rw [size_eq]; omega), hkU]
        omega
end Project.ClobQuote.Spec
