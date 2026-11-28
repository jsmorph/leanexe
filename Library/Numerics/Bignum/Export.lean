module

public import Library.Numerics.Bignum.Bound

@[expose] public section

/-!
The text exports equal their specifications, and their generated bounds have closed forms.  Each
binary export other than comparison applies one integer function between `intOfText` of its operands
and `intToText` of the result, so `textOp_eq` and `textDivOp_eq` prove the pattern once for any
function `g` of `BigInt`s that computes an integer function `f` on canonical arguments, and each
export instantiates them by `rfl`.  A text of `D` digits denotes an integer below `10^D ≤ 2^(32 D)`,
so its magnitude has at most `D` limbs (`denote_mag_size`), and every result `f a b` of the exports
has `|f a b| ≤ (|a| + 1) (|b| + 1)`, so its magnitude has at most `s.size + t.size` limbs.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open Library.Numerics.Decimal.Int64Text (denote digitWords digitWords_length_le_iff)

/-! ## Sizes of the operands -/

theorem pow_ten_le_base (D : ℕ) : 10 ^ D ≤ base ^ D :=
  Nat.pow_le_pow_left (by rw [base_eq]; norm_num) D

/-- A text of the grammar denotes an integer below `10` to the power of its length. -/
theorem denote_natAbs_lt {s : Array UInt64} {z : ℤ} (h : denote s.toList = some z) :
    z.natAbs < 10 ^ s.size := by
  have hp := print_of_denote h
  have hsz := printSpec_size z
  rw [hp] at hsz
  have hl := (digitWords_length_le_iff z.natAbs (digitWords z.natAbs).length
    (Library.Numerics.Decimal.Int64Text.digitWords_length_pos _)).mp le_rfl
  exact lt_of_lt_of_le hl (Nat.pow_le_pow_right (by norm_num) (by split at hsz <;> omega))

theorem mag_size_le_of_lt {z : ℤ} {D : ℕ} (h : z.natAbs < 10 ^ D) :
    (BigInt.ofInt z).mag.size ≤ D :=
  (size_limbsOf_le_iff _ _).mpr (lt_of_lt_of_le h (pow_ten_le_base D))

theorem denote_mag_size {s : Array UInt64} {z : ℤ} (h : denote s.toList = some z) :
    (BigInt.ofInt z).mag.size ≤ s.size := mag_size_le_of_lt (denote_natAbs_lt h)

/-- Print after read on the program: every text that `intOfText` accepts is `intToText` of the
integer it returns. -/
theorem intToText_of_read {s : Array UInt64} {x : BigInt} (hs : s.size < 2 ^ 32)
    (h : intOfText s = (true, x)) : intToText x = s := by
  rw [intOfText_eq s hs] at h
  obtain ⟨z, rfl, hp⟩ := print_of_readSpec h
  have hd : denote s.toList = some z := by rw [← hp]; exact denote_print z
  rw [intToText_eq (by have := denote_mag_size hd; omega), hp]

/-! ## The patterns of the text exports -/

/-- The text export of an integer function other than a division. -/
def textOp (g : BigInt → BigInt → BigInt) (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then (0, intToText (g a.2 b.2)) else (2, #[])
  else (1, #[])

/-- The text export of a division. -/
def textDivOp (g : BigInt → BigInt → BigInt) (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then
      (if b.2.mag.size.toUInt64 == 0 then (3, #[]) else (0, intToText (g a.2 b.2)))
    else (2, #[])
  else (1, #[])

theorem textAdd_def : textAdd = textOp intAdd := rfl
theorem textSub_def : textSub = textOp intSub := rfl
theorem textMul_def : textMul = textOp intMul := rfl
theorem textTDiv_def : textTDiv = textDivOp fun x y => (intTDivMod x y).1 := rfl
theorem textTMod_def : textTMod = textDivOp fun x y => (intTDivMod x y).2 := rfl
theorem textEDiv_def : textEDiv = textDivOp fun x y => (intEDivMod x y).1 := rfl
theorem textEMod_def : textEMod = textDivOp fun x y => (intEDivMod x y).2 := rfl

/-- The conditions under which a function of `BigInt`s computes an integer function whose result
the printer can write. -/
structure Computes (g : BigInt → BigInt → BigInt) (f : ℤ → ℤ → ℤ) : Prop where
  eq : ∀ a b, (BigInt.ofInt a).mag.size < 2 ^ 32 → (BigInt.ofInt b).mag.size < 2 ^ 32 →
    g (.ofInt a) (.ofInt b) = .ofInt (f a b)
  le : ∀ a b, (f a b).natAbs ≤ (a.natAbs + 1) * (b.natAbs + 1)

theorem result_mag_size {f : ℤ → ℤ → ℤ}
    (hf : ∀ a b, (f a b).natAbs ≤ (a.natAbs + 1) * (b.natAbs + 1)) {s t : Array UInt64}
    {a b : ℤ} (ha : denote s.toList = some a) (hb : denote t.toList = some b) :
    (BigInt.ofInt (f a b)).mag.size ≤ s.size + t.size + 1 := by
  apply mag_size_le_of_lt
  have h1 := denote_natAbs_lt ha
  have h2 := denote_natAbs_lt hb
  have h3 := Nat.mul_le_mul (show a.natAbs + 1 ≤ 10 ^ s.size by omega)
    (show b.natAbs + 1 ≤ 10 ^ t.size by omega)
  have h4 : 10 ^ s.size * 10 ^ t.size < 10 ^ (s.size + t.size + 1) := by
    rw [← pow_add, pow_succ]; have : 0 < 10 ^ (s.size + t.size) := by positivity
    omega
  have := hf a b
  omega

theorem readSpec_of_denote {s : Array UInt64} {z : ℤ} (h : denote s.toList = some z) :
    readSpec s = (true, .ofInt z) := by unfold readSpec; rw [h]

theorem readSpec_of_none {s : Array UInt64} (h : denote s.toList = none) :
    readSpec s = (false, .ofInt 0) := by unfold readSpec; rw [h]

theorem textOp_eq {g : BigInt → BigInt → BigInt} {f : ℤ → ℤ → ℤ} (hg : Computes g f)
    (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textOp g s t = textBinary false f s t := by
  unfold textOp textBinary
  rw [intOfText_eq s (by omega), intOfText_eq t (by omega)]
  cases ha : denote s.toList with
  | none => rw [readSpec_of_none ha]; rfl
  | some a =>
    cases hb : denote t.toList with
    | none => rw [readSpec_of_denote ha, readSpec_of_none hb]; rfl
    | some b =>
      rw [readSpec_of_denote ha, readSpec_of_denote hb]
      have hsa := denote_mag_size ha
      have hsb := denote_mag_size hb
      have hr := result_mag_size hg.le ha hb
      dsimp only
      rw [hg.eq a b (by omega) (by omega), intToText_eq (by omega)]
      simp

theorem textDivOp_eq {g : BigInt → BigInt → BigInt} {f : ℤ → ℤ → ℤ} (hg : Computes g f)
    (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textDivOp g s t = textBinary true f s t := by
  unfold textDivOp textBinary
  rw [intOfText_eq s (by omega), intOfText_eq t (by omega)]
  cases ha : denote s.toList with
  | none => rw [readSpec_of_none ha]; rfl
  | some a =>
    cases hb : denote t.toList with
    | none => rw [readSpec_of_denote ha, readSpec_of_none hb]; rfl
    | some b =>
      rw [readSpec_of_denote ha, readSpec_of_denote hb]
      have hsa := denote_mag_size ha
      have hsb := denote_mag_size hb
      have hr := result_mag_size hg.le ha hb
      dsimp only
      simp only [↓reduceIte]
      rw [show (BigInt.ofInt b).mag = limbsOf b.natAbs from rfl,
        limbsOf_beq_zero (by simp only [BigInt.ofInt] at hsb; omega)]
      by_cases hb0 : b = 0
      · simp [hb0]
      · rw [ite_eq_right (show ¬ decide (b.natAbs = 0) = true by simpa using hb0),
          ite_eq_right (show ¬ (True ∧ b = 0) by simpa using hb0),
          hg.eq a b (by omega) (by omega), intToText_eq (by omega)]

/-! ## The integer functions of the exports -/

theorem prod_expand (x y : ℕ) : (x + 1) * (y + 1) = x * y + x + y + 1 := by ring

theorem computes_add : Computes intAdd (· + ·) :=
  ⟨fun _ _ ha hb => intAdd_eq ha hb, fun a b => by
    have := Int.natAbs_add_le a b; rw [prod_expand]; omega⟩

theorem computes_sub : Computes intSub (· - ·) :=
  ⟨fun _ _ ha hb => intSub_eq ha hb, fun a b => by
    have := Int.natAbs_sub_le a b; rw [prod_expand]; omega⟩

theorem computes_mul : Computes intMul (· * ·) :=
  ⟨fun _ _ ha hb => intMul_eq ha hb, fun a b => by
    rw [Int.natAbs_mul, prod_expand]; omega⟩

theorem computes_tdiv : Computes (fun x y => (intTDivMod x y).1) Int.tdiv :=
  ⟨fun _ _ ha hb => by rw [intTDivMod_eq ha hb]; rfl, fun a b => by
    rw [Int.natAbs_tdiv, prod_expand]
    have := Nat.div_le_self a.natAbs b.natAbs
    have : a.natAbs.div b.natAbs = a.natAbs / b.natAbs := rfl
    omega⟩

theorem computes_tmod : Computes (fun x y => (intTDivMod x y).2) Int.tmod :=
  ⟨fun _ _ ha hb => by rw [intTDivMod_eq ha hb]; rfl, fun a b => by
    rw [Int.natAbs_tmod, prod_expand]
    have := Nat.mod_le a.natAbs b.natAbs
    omega⟩

theorem computes_ediv : Computes (fun x y => (intEDivMod x y).1) (· / ·) :=
  ⟨fun _ _ ha hb => by rw [intEDivMod_eq ha hb]; rfl, fun a b => by
    have := Int.natAbs_ediv_le_natAbs a b
    rw [prod_expand]
    omega⟩

theorem computes_emod : Computes (fun x y => (intEDivMod x y).2) (· % ·) :=
  ⟨fun _ _ ha hb => by rw [intEDivMod_eq ha hb]; rfl, fun a b => by
    by_cases hb : b = 0
    · subst hb; simp
    · have h1 := Int.emod_nonneg a hb
      have h2 := Int.emod_lt a hb
      have : (a % b).natAbs < b.natAbs := by omega
      rw [prod_expand]
      omega⟩

/-! ## The text exports -/

theorem textAdd_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textAdd s t = textAddSpec s t := by
  rw [textAdd_def, textOp_eq computes_add s t hs ht]; rfl

theorem textSub_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textSub s t = textSubSpec s t := by
  rw [textSub_def, textOp_eq computes_sub s t hs ht]; rfl

theorem textMul_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textMul s t = textMulSpec s t := by
  rw [textMul_def, textOp_eq computes_mul s t hs ht]; rfl

theorem textTDiv_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textTDiv s t = textTDivSpec s t := by
  rw [textTDiv_def, textDivOp_eq computes_tdiv s t hs ht]; rfl

theorem textTMod_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textTMod s t = textTModSpec s t := by
  rw [textTMod_def, textDivOp_eq computes_tmod s t hs ht]; rfl

theorem textEDiv_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textEDiv s t = textEDivSpec s t := by
  rw [textEDiv_def, textDivOp_eq computes_ediv s t hs ht]; rfl

theorem textEMod_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textEMod s t = textEModSpec s t := by
  rw [textEMod_def, textDivOp_eq computes_emod s t hs ht]; rfl

theorem textNeg_eq (s : Array UInt64) (hs : s.size < 2 ^ 30) : textNeg s = textNegSpec s := by
  unfold textNeg textNegSpec textUnary
  rw [intOfText_eq s (by omega)]
  cases ha : denote s.toList with
  | none => rw [readSpec_of_none ha]; rfl
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    dsimp only
    rw [intNeg_eq (by omega), intToText_eq (by
      have : (BigInt.ofInt (-a)).mag.size = (BigInt.ofInt a).mag.size := by
        simp [BigInt.ofInt]
      omega)]
    simp

theorem textCmp_eq (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    textCmp s t = textCmpSpec s t := by
  unfold textCmp textCmpSpec
  rw [intOfText_eq s (by omega), intOfText_eq t (by omega)]
  cases ha : denote s.toList with
  | none => rw [readSpec_of_none ha]; rfl
  | some a =>
    cases hb : denote t.toList with
    | none => rw [readSpec_of_denote ha, readSpec_of_none hb]; rfl
    | some b =>
      rw [readSpec_of_denote ha, readSpec_of_denote hb]
      have hsa := denote_mag_size ha
      have hsb := denote_mag_size hb
      dsimp only
      rw [intCmp_eq (by omega) (by omega)]
      simp

/-! ## Bounds of the text exports -/

theorem eta_ofInt (z : ℤ) :
    ({ neg := (BigInt.ofInt z).neg, mag := (BigInt.ofInt z).mag } : BigInt) = BigInt.ofInt z := rfl

/-- The cost of the Euclidean correction that the generated bounds expand inline. -/
theorem ecorr_le (x y : BigInt) (hx : x.mag.size < 2 ^ 32) (hy : y.mag.size < 2 ^ 32)
    (hy0 : y.mag.size ≠ 0) :
    (if ((intTDivMod x y).2.neg && y.mag.size.toUInt64 != 0) = true then
        Verified.blockCost (UInt64.toNat 0) +
            Verified.growCost (({ toList := [] } : Array UInt64).size + 1) 1 +
            compiled.natAdd.bound ((intTDivMod x y).1.mag, #[1]) +
          compiled.natSub.bound (y.mag, (intTDivMod x y).2.mag)
      else 0) ≤ 104 * x.mag.size + 88 * y.mag.size + 616 := by
  split
  · obtain ⟨s1, s2⟩ := natDivMod_size x.mag y.mag hx hy hy0
    have hq : (intTDivMod x y).1.mag.size ≤ x.mag.size := s1
    have hr : (intTDivMod x y).2.mag.size ≤ y.mag.size := s2
    have h2 := natAdd_bound_le (intTDivMod x y).1.mag #[1] (by omega) (by simp)
    have h3 := natSub_bound_le y.mag (intTDivMod x y).2.mag hy (by omega)
    rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq, Verified.growCost_eq]
    have h1s : (#[1] : Array UInt64).size = 1 := rfl
    have h0s : ({ toList := [] } : Array UInt64).size = 0 := rfl
    rw [h1s] at h2
    rw [h0s]
    have : max (intTDivMod x y).1.mag.size 1 ≤ x.mag.size + 1 := by omega
    have : max y.mag.size (intTDivMod x y).2.mag.size = y.mag.size := by omega
    omega
  · omega

theorem ofInt_canonical_facts (z : ℤ) : Digits (BigInt.ofInt z).mag := (canonical_limbsOf _).1

theorem textAdd_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textAdd.bound (s, t) ≤ 200 * (s.size + t.size) + 1006 := by
  rw [compiled.textAdd.bound_eq, intOfText_eq s (by omega), intOfText_eq t (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    cases hb : denote t.toList with
    | none =>
      rw [readSpec_of_none hb]
      simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
        Verified.blockCost_eq]
      omega
    | some b =>
      rw [readSpec_of_denote hb]
      have hsb := denote_mag_size hb
      have hr := result_mag_size computes_add.le ha hb
      simp only [↓reduceIte]
      refine le_trans (Nat.add_le_add hbs (Nat.add_le_add hbt (Nat.add_le_add
        (intAdd_bound_le _ _ ?_ ?_) (intToText_bound_le _ ?_ ?_)))) ?_
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show Digits (intAdd (.ofInt a) (.ofInt b)).mag
        rw [intAdd_eq (by omega) (by omega)]; exact ofInt_canonical_facts _
      · show (intAdd (.ofInt a) (.ofInt b)).mag.size < 2 ^ 32
        rw [intAdd_eq (by omega) (by omega)]; omega
      · show 2 * s.size + 128 + (2 * t.size + 128 + (104 * max (BigInt.ofInt a).mag.size
          (BigInt.ofInt b).mag.size + 232 + (94 * (intAdd (.ofInt a) (.ofInt b)).mag.size + 424)))
          ≤ _
        rw [intAdd_eq (by omega) (by omega)]
        have : max (BigInt.ofInt a).mag.size (BigInt.ofInt b).mag.size ≤ s.size + t.size := by
          omega
        omega

theorem textSub_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textSub.bound (s, t) ≤ 200 * (s.size + t.size) + 1006 := by
  rw [compiled.textSub.bound_eq, intOfText_eq s (by omega), intOfText_eq t (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    cases hb : denote t.toList with
    | none =>
      rw [readSpec_of_none hb]
      simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
        Verified.blockCost_eq]
      omega
    | some b =>
      rw [readSpec_of_denote hb]
      have hsb := denote_mag_size hb
      have hr := result_mag_size computes_sub.le ha hb
      simp only [↓reduceIte]
      refine le_trans (Nat.add_le_add hbs (Nat.add_le_add hbt (Nat.add_le_add
        (intSub_bound_le _ _ ?_ ?_) (intToText_bound_le _ ?_ ?_)))) ?_
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show Digits (intSub (.ofInt a) (.ofInt b)).mag
        rw [computes_sub.eq a b (by omega) (by omega)]; exact ofInt_canonical_facts _
      · show (intSub (.ofInt a) (.ofInt b)).mag.size < 2 ^ 32
        rw [computes_sub.eq a b (by omega) (by omega)]; omega
      · show 2 * s.size + 128 + (2 * t.size + 128 + (104 * max (BigInt.ofInt a).mag.size (BigInt.ofInt b).mag.size + 232 +
          (94 * (intSub (.ofInt a) (.ofInt b)).mag.size + 424))) ≤ _
        rw [computes_sub.eq a b (by omega) (by omega)]
        have : max (BigInt.ofInt a).mag.size (BigInt.ofInt b).mag.size ≤ s.size + t.size := by
          omega
        omega

theorem textMul_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textMul.bound (s, t) ≤ 112 * (s.size + t.size) + 886 := by
  rw [compiled.textMul.bound_eq, intOfText_eq s (by omega), intOfText_eq t (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    cases hb : denote t.toList with
    | none =>
      rw [readSpec_of_none hb]
      simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
        Verified.blockCost_eq]
      omega
    | some b =>
      rw [readSpec_of_denote hb]
      have hsb := denote_mag_size hb
      have hr := result_mag_size computes_mul.le ha hb
      simp only [↓reduceIte]
      refine le_trans (Nat.add_le_add hbs (Nat.add_le_add hbt (Nat.add_le_add
        (intMul_bound_le _ _ ?_ ?_) (intToText_bound_le _ ?_ ?_)))) ?_
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show Digits (intMul (.ofInt a) (.ofInt b)).mag
        rw [computes_mul.eq a b (by omega) (by omega)]; exact ofInt_canonical_facts _
      · show (intMul (.ofInt a) (.ofInt b)).mag.size < 2 ^ 32
        rw [computes_mul.eq a b (by omega) (by omega)]; omega
      · show 2 * s.size + 128 + (2 * t.size + 128 + (16 * ((BigInt.ofInt a).mag.size + (BigInt.ofInt b).mag.size) + 112 +
          (94 * (intMul (.ofInt a) (.ofInt b)).mag.size + 424))) ≤ _
        rw [computes_mul.eq a b (by omega) (by omega)]
        omega

theorem textNeg_bound_le (s : Array UInt64) (hs : s.size < 2 ^ 30) :
    compiled.textNeg.bound s ≤ 104 * s.size + 608 := by
  rw [compiled.textNeg.bound_eq, intOfText_eq s (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    have hn : (BigInt.ofInt (-a)).mag.size = (BigInt.ofInt a).mag.size := by
      simp [BigInt.ofInt]
    simp only [↓reduceIte]
    refine le_trans (Nat.add_le_add hbs (Nat.add_le_add
      (intNeg_bound_le _ ?_) (intToText_bound_le _ ?_ ?_))) ?_
    · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
    · show Digits (intNeg (.ofInt a)).mag
      rw [intNeg_eq (by omega)]; exact ofInt_canonical_facts _
    · show (intNeg (.ofInt a)).mag.size < 2 ^ 32
      rw [intNeg_eq (by omega)]; omega
    · show 2 * s.size + 128 + (8 * (BigInt.ofInt a).mag.size + 56 +
        (94 * (intNeg (.ofInt a)).mag.size + 424)) ≤ _
      rw [intNeg_eq (by omega)]
      omega

theorem textCmp_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textCmp.bound (s, t) ≤ 2 * (s.size + t.size) + 256 := by
  rw [compiled.textCmp.bound_eq]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  split <;> omega

theorem textTDiv_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textTDiv.bound (s, t) ≤ 240 * (s.size + t.size) + 1598 := by
  rw [compiled.textTDiv.bound_eq, intOfText_eq s (by omega), intOfText_eq t (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    cases hb : denote t.toList with
    | none =>
      rw [readSpec_of_none hb]
      simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
        Verified.blockCost_eq]
      omega
    | some b =>
      rw [readSpec_of_denote hb]
      have hsb := denote_mag_size hb
      have hr := result_mag_size computes_tdiv.le ha hb
      simp only [↓reduceIte]
      split
      · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
      rename_i hz
      have hb0 : (BigInt.ofInt b).mag.size ≠ 0 := by
        rw [size_toUInt64_beq_zero (by omega)] at hz; simpa using hz
      refine le_trans (Nat.add_le_add hbs (Nat.add_le_add hbt (Nat.add_le_add
        (divCost_le _ _ ?_ ?_) (intToText_bound_le _ ?_ ?_)))) ?_
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show Digits (intTDivMod (.ofInt a) (.ofInt b)).1.mag
        rw [intTDivMod_eq (by omega) (by omega)]; exact ofInt_canonical_facts _
      · show (intTDivMod (.ofInt a) (.ofInt b)).1.mag.size < 2 ^ 32
        rw [intTDivMod_eq (by omega) (by omega)]; simp only [intTDivModSpec]; omega
      · show 2 * s.size + 128 + (2 * t.size + 128 + (128 * (BigInt.ofInt a).mag.size + 144 * (BigInt.ofInt b).mag.size + 824 +
          (94 * (intTDivMod (.ofInt a) (.ofInt b)).1.mag.size + 424))) ≤ _
        rw [intTDivMod_eq (by omega) (by omega)]
        simp only [intTDivModSpec]
        omega

theorem textTMod_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textTMod.bound (s, t) ≤ 240 * (s.size + t.size) + 1598 := by
  rw [compiled.textTMod.bound_eq, intOfText_eq s (by omega), intOfText_eq t (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    cases hb : denote t.toList with
    | none =>
      rw [readSpec_of_none hb]
      simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
        Verified.blockCost_eq]
      omega
    | some b =>
      rw [readSpec_of_denote hb]
      have hsb := denote_mag_size hb
      have hr := result_mag_size computes_tmod.le ha hb
      simp only [↓reduceIte]
      split
      · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
      rename_i hz
      have hb0 : (BigInt.ofInt b).mag.size ≠ 0 := by
        rw [size_toUInt64_beq_zero (by omega)] at hz; simpa using hz
      refine le_trans (Nat.add_le_add hbs (Nat.add_le_add hbt (Nat.add_le_add
        (divCost_le _ _ ?_ ?_) (intToText_bound_le _ ?_ ?_)))) ?_
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show Digits (intTDivMod (.ofInt a) (.ofInt b)).2.mag
        rw [intTDivMod_eq (by omega) (by omega)]; exact ofInt_canonical_facts _
      · show (intTDivMod (.ofInt a) (.ofInt b)).2.mag.size < 2 ^ 32
        rw [intTDivMod_eq (by omega) (by omega)]; simp only [intTDivModSpec]; omega
      · show 2 * s.size + 128 + (2 * t.size + 128 + (128 * (BigInt.ofInt a).mag.size + 144 * (BigInt.ofInt b).mag.size + 824 +
          (94 * (intTDivMod (.ofInt a) (.ofInt b)).2.mag.size + 424))) ≤ _
        rw [intTDivMod_eq (by omega) (by omega)]
        simp only [intTDivModSpec]
        omega

theorem textEDiv_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textEDiv.bound (s, t) ≤ 344 * (s.size + t.size) + 2214 := by
  rw [compiled.textEDiv.bound_eq, intOfText_eq s (by omega), intOfText_eq t (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    cases hb : denote t.toList with
    | none =>
      rw [readSpec_of_none hb]
      simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
        Verified.blockCost_eq]
      omega
    | some b =>
      rw [readSpec_of_denote hb]
      have hsb := denote_mag_size hb
      have hr := result_mag_size computes_ediv.le ha hb
      simp only [↓reduceIte]
      split
      · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
      rename_i hz
      have hb0 : (BigInt.ofInt b).mag.size ≠ 0 := by
        rw [size_toUInt64_beq_zero (by omega)] at hz; simpa using hz
      refine le_trans (Nat.add_le_add hbs (Nat.add_le_add hbt (Nat.add_le_add
        (Nat.add_le_add (divCost_le _ _ ?_ ?_) (ecorr_le _ _ ?_ ?_ ?_)) (intToText_bound_le _ ?_ ?_)))) ?_
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size ≠ 0; exact hb0
      · show Digits (intEDivMod (.ofInt a) (.ofInt b)).1.mag
        rw [intEDivMod_eq (by omega) (by omega)]; exact ofInt_canonical_facts _
      · show (intEDivMod (.ofInt a) (.ofInt b)).1.mag.size < 2 ^ 32
        rw [intEDivMod_eq (by omega) (by omega)]; simp only [intEDivModSpec]; omega
      · show 2 * s.size + 128 + (2 * t.size + 128 + (128 * (BigInt.ofInt a).mag.size + 144 * (BigInt.ofInt b).mag.size + 824 +
          (104 * (BigInt.ofInt a).mag.size + 88 * (BigInt.ofInt b).mag.size + 616) +
          (94 * (intEDivMod (.ofInt a) (.ofInt b)).1.mag.size + 424))) ≤ _
        rw [intEDivMod_eq (by omega) (by omega)]
        simp only [intEDivModSpec]
        omega

theorem textEMod_bound_le (s t : Array UInt64) (hs : s.size < 2 ^ 30) (ht : t.size < 2 ^ 30) :
    compiled.textEMod.bound (s, t) ≤ 344 * (s.size + t.size) + 2214 := by
  rw [compiled.textEMod.bound_eq, intOfText_eq s (by omega), intOfText_eq t (by omega)]
  have hbs := intOfText_bound_le s (by omega)
  have hbt := intOfText_bound_le t (by omega)
  cases ha : denote s.toList with
  | none =>
    rw [readSpec_of_none ha]
    simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
      Verified.blockCost_eq]
    omega
  | some a =>
    rw [readSpec_of_denote ha]
    have hsa := denote_mag_size ha
    cases hb : denote t.toList with
    | none =>
      rw [readSpec_of_none hb]
      simp only [Bool.false_eq_true, ↓reduceIte, show UInt64.toNat 0 = 0 from rfl,
        Verified.blockCost_eq]
      omega
    | some b =>
      rw [readSpec_of_denote hb]
      have hsb := denote_mag_size hb
      have hr := result_mag_size computes_emod.le ha hb
      simp only [↓reduceIte]
      split
      · rw [show UInt64.toNat 0 = 0 from rfl, Verified.blockCost_eq]; omega
      rename_i hz
      have hb0 : (BigInt.ofInt b).mag.size ≠ 0 := by
        rw [size_toUInt64_beq_zero (by omega)] at hz; simpa using hz
      refine le_trans (Nat.add_le_add hbs (Nat.add_le_add hbt (Nat.add_le_add
        (Nat.add_le_add (divCost_le _ _ ?_ ?_) (ecorr_le _ _ ?_ ?_ ?_)) (intToText_bound_le _ ?_ ?_)))) ?_
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt a).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size < 2 ^ 32; omega
      · show (BigInt.ofInt b).mag.size ≠ 0; exact hb0
      · show Digits (intEDivMod (.ofInt a) (.ofInt b)).2.mag
        rw [intEDivMod_eq (by omega) (by omega)]; exact ofInt_canonical_facts _
      · show (intEDivMod (.ofInt a) (.ofInt b)).2.mag.size < 2 ^ 32
        rw [intEDivMod_eq (by omega) (by omega)]; simp only [intEDivModSpec]; omega
      · show 2 * s.size + 128 + (2 * t.size + 128 + (128 * (BigInt.ofInt a).mag.size + 144 * (BigInt.ofInt b).mag.size + 824 +
          (104 * (BigInt.ofInt a).mag.size + 88 * (BigInt.ofInt b).mag.size + 616) +
          (94 * (intEDivMod (.ofInt a) (.ofInt b)).2.mag.size + 424))) ≤ _
        rw [intEDivMod_eq (by omega) (by omega)]
        simp only [intEDivModSpec]
        omega

end Library.Numerics.Bignum
