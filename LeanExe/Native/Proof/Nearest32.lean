import LeanExe.Native.Proof.Floats32
import LeanExe.ProofKit.F32Nearest
import LeanExe.ProofKit.F32Decoded

/-!
The simulation of `f32.nearest`, which `nearest32Stmt` computes from the word of the float.

Talos's `nearest` of a value with biased exponent `e` other than 255 is `roundScaledMagnitude`
of its sign and `roundShift magnitude 149`, the magnitude rounded to an integer
(`nearest_finite`).  For `e ≥ 150` the magnitude is an integer, and the result is the value
(`nearest_big`); for `e < 126` it is below one half, and the result is a zero of the value's
sign (`nearest_small`); otherwise the rounding is `roundShift` of the significand `m` by
`150 - e` (`roundShift_scale`), which the C code computes with shifts and masks, and the packing
is `fromInt` of the integer, negated for a negative value (`nearest_mid`, `negate_roundScaled`).
For `e = 255` the result is the infinity or the canonical NaN, which the canonicalization gives.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## Talos's `nearest` -/

theorem roundShift_scale (m s a : Nat) (hs : 1 ≤ s) :
    IEEE32.roundShift (m * 2 ^ a) (s + a) = IEEE32.roundShift m s := by
  have hp : 0 < 2 ^ a := Nat.two_pow_pos a
  have hu : 2 ^ (s + a) = 2 ^ s * 2 ^ a := Nat.pow_add 2 s a
  have hs2 : 2 ^ s = 2 ^ (s - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  have hq : m * 2 ^ a / 2 ^ (s + a) = m / 2 ^ s := by
    rw [hu, Nat.mul_div_mul_right _ _ hp]
  have hr : m * 2 ^ a % 2 ^ (s + a) = m % 2 ^ s * 2 ^ a := by
    rw [hu, Nat.mul_mod_mul_right]
  have hh : 2 ^ (s + a) / 2 = 2 ^ s / 2 * 2 ^ a := by
    rw [hu, hs2, Nat.mul_right_comm (2 ^ (s - 1)) 2 (2 ^ a), Nat.mul_div_cancel _ (by decide),
      Nat.mul_div_cancel _ (by decide)]
  unfold IEEE32.roundShift
  simp only [hq, hr, hh, Nat.mul_lt_mul_right hp]

theorem roundShift_exact (k s : Nat) (hs : 1 ≤ s) : IEEE32.roundShift (k * 2 ^ s) s = k := by
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2 : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
  have hh : 0 < 2 ^ s / 2 := Nat.div_pos h2 (by decide)
  unfold IEEE32.roundShift
  simp only [Nat.mul_div_cancel _ hp, Nat.mul_mod_left, hh, ↓reduceIte]

theorem nearest_finite (x : UInt32) (he : IEEE32.exponent x ≠ 255) :
    IEEE32.nearest x = IEEE32.roundScaledMagnitude (IEEE32.sign x)
      (IEEE32.roundShift (IEEE32.scaledMagnitude x) 149 * 2 ^ 149) :=
  (LeanExe.ProofKit.F32Nearest.nearest_eq x).symm.trans
    (LeanExe.ProofKit.F32Nearest.nearestBits_finite x he)

theorem negate_encodeFinite_false (e f : Nat) (he : e < 255) (hf : f < 2 ^ 23) :
    IEEE32.negate (IEEE32.encodeFinite false e f) = IEEE32.encodeFinite true e f := by
  have hv : (IEEE32.encodeFinite false e f).toNat = e * 2 ^ 23 + f := by
    unfold IEEE32.encodeFinite
    rw [UInt32.toNat_ofNat']
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    omega
  unfold IEEE32.negate IEEE32.sign IEEE32.exponent IEEE32.fraction
  rw [hv]
  have h1 : decide (2 ^ 31 ≤ e * 2 ^ 23 + f) = false := by
    simp only [decide_eq_false_iff_not, not_le]; omega
  have h2 : (e * 2 ^ 23 + f) / 2 ^ 23 % 2 ^ 8 = e := by omega
  have h3 : (e * 2 ^ 23 + f) % 2 ^ 23 = f := by omega
  rw [h1, h2, h3]
  rfl

/-- The negation of a positive rounding is the negative rounding. -/
theorem negate_roundScaled (n : Nat) :
    IEEE32.negate (IEEE32.roundScaledMagnitude false n) = IEEE32.roundScaledMagnitude true n := by
  unfold IEEE32.roundScaledMagnitude
  split
  · exact negate_encodeFinite_false 0 n (by omega) (by omega)
  split
  · exact negate_encodeFinite_false 1 (n - 2 ^ 23) (by omega) (by omega)
  rename_i h1 h2
  have hn : n ≠ 0 := by omega
  have hr := CodeLib.IEEE32.roundShift_bounds n (n.log2 - 23)
  have hhigh := Nat.lt_log2_self (n := n)
  have hlog : 24 ≤ n.log2 := by
    by_contra h
    have : n.log2 + 1 ≤ 24 := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) this
    omega
  have hsplit' : 2 ^ (n.log2 + 1) = 2 ^ 24 * 2 ^ (n.log2 - 23) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hq2 : n / 2 ^ (n.log2 - 23) < 2 ^ 24 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [← hsplit']; exact hhigh)
  dsimp only
  generalize Wasm.IEEE32.roundShift n (n.log2 - 23) = R at hr ⊢
  by_cases hR : R = 2 ^ 24
  · have hR' : (R == 2 ^ 24) = true := by simp [hR]
    simp only [hR', ↓reduceIte]
    by_cases hx : 255 ≤ n.log2 - 23 + 1 + 1
    · simp only [hx, ↓reduceIte]
      decide
    · simp only [hx, ↓reduceIte]
      exact negate_encodeFinite_false _ _ (by omega) (by simp)
  · have hR' : (R == 2 ^ 24) = false := by simpa using hR
    simp only [hR', Bool.false_eq_true, ↓reduceIte]
    by_cases hx : 255 ≤ n.log2 - 23 + 1
    · simp only [hx, ↓reduceIte]
      decide
    · simp only [hx, ↓reduceIte]
      exact negate_encodeFinite_false _ _ (by omega) (by omega)

theorem fromInt_nat (q : Nat) :
    IEEE32.fromInt (q : _root_.Int) = IEEE32.roundScaledMagnitude false (q * 2 ^ 149) := by
  have h : decide ((q : _root_.Int) < 0) = false := by simp
  unfold IEEE32.fromInt
  rw [h, Int.natAbs_natCast]

theorem scaledMagnitude_normal (x : UInt32) (he : IEEE32.exponent x ≠ 0) :
    IEEE32.scaledMagnitude x = (2 ^ 23 + IEEE32.fraction x) * 2 ^ (IEEE32.exponent x - 1) := by
  unfold IEEE32.scaledMagnitude
  simp [he]

theorem exponent_lt (x : UInt32) : IEEE32.exponent x < 256 := by
  unfold IEEE32.exponent; omega

theorem fraction_lt (x : UInt32) : IEEE32.fraction x < 2 ^ 23 := by
  unfold IEEE32.fraction; omega

/-- An integral value: `nearest` returns it. -/
theorem nearest_big (x : UInt32) (h1 : 150 ≤ IEEE32.exponent x) (h2 : IEEE32.exponent x ≠ 255) :
    IEEE32.nearest x = x := by
  rw [nearest_finite x h2]
  have hm := scaledMagnitude_normal x (by omega)
  have hk : IEEE32.scaledMagnitude x =
      (2 ^ 23 + IEEE32.fraction x) * 2 ^ (IEEE32.exponent x - 150) * 2 ^ 149 := by
    rw [hm, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have hz : IEEE32.scaledMagnitude x ≠ 0 := by
    rw [hm]; exact Nat.mul_ne_zero (by omega) (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  rw [hk, roundShift_exact _ _ (by omega), ← hk]
  exact LeanExe.ProofKit.F32Decoded.roundScaled_value x h2 hz

/-- A magnitude below one half: `nearest` returns the zero of the value's sign. -/
theorem nearest_small (x : UInt32) (h : IEEE32.exponent x < 126) :
    IEEE32.nearest x = IEEE32.signMask (IEEE32.sign x) := by
  rw [nearest_finite x (by omega)]
  have hb : IEEE32.scaledMagnitude x < 2 ^ 148 := by
    have hf := fraction_lt x
    by_cases hz : IEEE32.exponent x = 0
    · have : IEEE32.scaledMagnitude x = IEEE32.fraction x := by
        unfold IEEE32.scaledMagnitude; simp [hz]
      rw [this]
      calc IEEE32.fraction x < 2 ^ 23 := hf
        _ ≤ 2 ^ 148 := Nat.pow_le_pow_right (by decide) (by decide)
    · rw [scaledMagnitude_normal x hz]
      calc (2 ^ 23 + IEEE32.fraction x) * 2 ^ (IEEE32.exponent x - 1)
          < 2 ^ 24 * 2 ^ (IEEE32.exponent x - 1) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
        _ ≤ 2 ^ 24 * 2 ^ 124 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
        _ = 2 ^ 148 := by rw [← Nat.pow_add]
  have h0 : IEEE32.roundShift (IEEE32.scaledMagnitude x) 149 = 0 := by
    unfold IEEE32.roundShift
    have hq : IEEE32.scaledMagnitude x / 2 ^ 149 = 0 :=
      Nat.div_eq_of_lt (by
        calc IEEE32.scaledMagnitude x < 2 ^ 148 := hb
          _ ≤ 2 ^ 149 := Nat.pow_le_pow_right (by decide) (by decide))
    have hr : IEEE32.scaledMagnitude x % 2 ^ 149 = IEEE32.scaledMagnitude x :=
      Nat.mod_eq_of_lt (by
        calc IEEE32.scaledMagnitude x < 2 ^ 148 := hb
          _ ≤ 2 ^ 149 := Nat.pow_le_pow_right (by decide) (by decide))
    have hh : (2 : Nat) ^ 149 / 2 = 2 ^ 148 := by decide
    simp only [hq, hr, hh, hb, ↓reduceIte]
  rw [h0, Nat.zero_mul, LeanExe.ProofKit.F32Packing.signMask_eq_encode]
  unfold IEEE32.roundScaledMagnitude
  simp

/-- A magnitude from one half up to `2^23`: `nearest` rounds the significand by `150 - e`. -/
theorem nearest_mid (x : UInt32) (h1 : 126 ≤ IEEE32.exponent x) (h2 : IEEE32.exponent x < 150) :
    IEEE32.nearest x = IEEE32.roundScaledMagnitude (IEEE32.sign x)
      (IEEE32.roundShift (2 ^ 23 + IEEE32.fraction x) (150 - IEEE32.exponent x) * 2 ^ 149) := by
  rw [nearest_finite x (by omega), scaledMagnitude_normal x (by omega)]
  have hq : IEEE32.roundShift ((2 ^ 23 + IEEE32.fraction x) * 2 ^ (IEEE32.exponent x - 1)) 149 =
      IEEE32.roundShift (2 ^ 23 + IEEE32.fraction x) (150 - IEEE32.exponent x) := by
    rw [show (149 : Nat) = (150 - IEEE32.exponent x) + (IEEE32.exponent x - 1) by omega]
    exact roundShift_scale _ _ _ (by omega)
  rw [hq]

/-- An exponent of 255: the infinity, or the canonical NaN for a NaN. -/
theorem nearest_255 (x : UInt32) (h : IEEE32.exponent x = 255) :
    IEEE32.nearest x = canonOf32 x := by
  unfold IEEE32.nearest IEEE32.roundIntegral canonOf32
  by_cases hn : IEEE32.isNaN x = true
  · simp [hn]
  · have hi : IEEE32.isInfinite x = true := by
      simp only [IEEE32.isNaN, IEEE32.isInfinite, h, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
        ne_eq, true_and, not_not] at hn ⊢
      exact hn
    simp [hn, hi]

/-! ## The words of the C code -/

theorem toNat_u32 {n : Nat} (h : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n :=
  UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 2 ^ 32 from rfl]; exact h)

theorem exponent_word (x : UInt32) :
    ((x >>> UInt32.ofNat 23) &&& UInt32.ofNat 255).toNat = IEEE32.exponent x := by
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, toNat_u32 (by decide), toNat_u32 (by decide)]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  rfl

theorem significand_word (x : UInt32) :
    ((x &&& UInt32.ofNat 0x7FFFFF) + UInt32.ofNat 0x800000).toNat = 2 ^ 23 + IEEE32.fraction x := by
  have hf : (x &&& UInt32.ofNat 0x7FFFFF).toNat = IEEE32.fraction x := by
    rw [UInt32.toNat_and, toNat_u32 (by decide),
      show (0x7FFFFF : Nat) = 2 ^ 23 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rfl
  rw [UInt32.toNat_add, hf, toNat_u32 (by decide)]
  have := fraction_lt x
  omega

theorem sign_word (x : UInt32) : (x >>> UInt32.ofNat 31 ≠ 0) = (IEEE32.sign x = true) := by
  have h : (x >>> UInt32.ofNat 31).toNat = x.toNat / 2 ^ 31 := by
    rw [UInt32.toNat_shiftRight, toNat_u32 (by decide), Nat.shiftRight_eq_div_pow]
  unfold IEEE32.sign
  have hx := x.toNat_lt
  apply propext
  rw [decide_eq_true_iff, ne_eq, ← UInt32.toNat_inj, h]
  simp only [UInt32.toNat_zero]
  omega

/-! ## The C code -/

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- The temporaries that code with scratch slots from height `h` up keeps: the slots below `h`,
the locals, `brk`, and `lim`. -/
def Keeps (h : Nat) (le le' : temp_env) : Prop :=
  Frame h le le' ∧ (∀ i, le'[localId i]? = le[localId i]?) ∧
    (le'[brkId]? = le[brkId]? ∧ le'[limId]? = le[limId]?)

theorem Keeps.refl (h : Nat) (le : temp_env) : Keeps h le le :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem Keeps.insert {h k : Nat} (le : temp_env) (hk : h ≤ k) (t : VT) (v : val) :
    Keeps h le (le.insert (slotId k t) v) :=
  ⟨Frame.insert_slot _ _ _ _ hk, fun i => te_insert_ne _ (slotId_ne_localId _ _ i),
    te_insert_ne _ (slotId_ne_brkId _ _), te_insert_ne _ (slotId_ne_limId _ _)⟩

theorem Keeps.trans {h : Nat} {a b d : temp_env} (x : Keeps h a b) (y : Keeps h b d) :
    Keeps h a d :=
  ⟨x.1.trans y.1, fun i => (y.2.1 i).trans (x.2.1 i), y.2.2.1.trans x.2.2.1,
    y.2.2.2.trans x.2.2.2⟩

/-- A lookup past an insertion of another temporary. -/
theorem lk {le : temp_env} {a b : ident} {v w : val} (h : le[a]? = some v) (hne : b ≠ a) :
    (le.insert b w)[a]? = some v := by
  rw [te_insert_ne _ hne]; exact h

theorem cond_bool (m : mem) (b : Prop) [Decidable b] :
    bool_val (.Vint (if b then 1 else 0)) tint m = some (decide b) := by
  by_cases hb : b <;> simp [hb, bool_int]

theorem cond_uint (m : mem) (v : UInt32) : bool_val (.Vint v) tuint m = some (decide (v ≠ 0)) :=
  bool_uint m v

theorem eval_w {le : temp_env} {m : mem} {k : Nat} {v : UInt32}
    (h : le[slotId k .i32]? = some (.Vint v)) :
    eval_expr A E.ge empty_env le m (tmp k .i32) (.Vint v) :=
  .eval_Etempvar _ _ _ h

theorem eval_cint {le : temp_env} {m : mem} (n : Nat) :
    eval_expr A E.ge empty_env le m (cint n) (.Vint (UInt32.ofNat n)) :=
  .eval_Econst_int _ _

/-- The rounding of the significand that the C code makes, as Talos's `roundShift`. -/
theorem round_words (mt s : UInt32) (hs : 1 ≤ s.toNat) (hs' : s.toNat ≤ 24)
    (hm : mt.toNat < 2 ^ 24) :
    let q0 := mt >>> s
    let r := mt &&& ((UInt32.ofNat 1 <<< s) - UInt32.ofNat 1)
    let hh := UInt32.ofNat 1 <<< (s - UInt32.ofNat 1)
    (if hh < r then q0 + UInt32.ofNat 1
      else if r = hh then (if q0 &&& UInt32.ofNat 1 ≠ 0 then q0 + UInt32.ofNat 1 else q0)
      else q0).toNat = IEEE32.roundShift mt.toNat s.toNat := by
  intro q0 r hh
  have hq0 : q0.toNat = mt.toNat / 2 ^ s.toNat := by
    simp only [q0, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : s.toNat < 32)]
  have hpow : (UInt32.ofNat 1 <<< s).toNat = 2 ^ s.toNat := by
    rw [UInt32.toNat_shiftLeft, toNat_u32 (by decide), Nat.mod_eq_of_lt (by omega : s.toNat < 32),
      Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  have hr : r.toNat = mt.toNat % 2 ^ s.toNat := by
    have hp1 : 1 ≤ 2 ^ s.toNat := Nat.one_le_two_pow
    have hmask : ((UInt32.ofNat 1 <<< s) - UInt32.ofNat 1).toNat = 2 ^ s.toNat - 1 := by
      rw [UInt32.toNat_sub, hpow, toNat_u32 (by decide)]
      have : 2 ^ s.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    simp only [r, UInt32.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
  have hhh : hh.toNat = 2 ^ s.toNat / 2 := by
    have hsub : (s - UInt32.ofNat 1).toNat = s.toNat - 1 := by
      rw [UInt32.toNat_sub, toNat_u32 (by decide)]; omega
    simp only [hh, UInt32.toNat_shiftLeft, toNat_u32 (by decide : 1 < 2 ^ 32), hsub,
      Nat.mod_eq_of_lt (by omega : s.toNat - 1 < 32), Nat.shiftLeft_eq, Nat.one_mul]
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    rw [show s.toNat = s.toNat - 1 + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    congr 1
  have hq0lt : q0.toNat + 1 < 2 ^ 32 := by
    rw [hq0]
    have := Nat.div_le_self mt.toNat (2 ^ s.toNat)
    omega
  have hadd : (q0 + UInt32.ofNat 1).toNat = q0.toNat + 1 := by
    rw [UInt32.toNat_add, toNat_u32 (by decide)]; omega
  have hodd : (q0 &&& UInt32.ofNat 1 ≠ 0) ↔ q0.toNat % 2 ≠ 0 := by
    rw [ne_eq, ← UInt32.toNat_inj, UInt32.toNat_and, toNat_u32 (by decide),
      show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp
  have hlt : hh < r ↔ 2 ^ s.toNat / 2 < mt.toNat % 2 ^ s.toNat := by
    rw [UInt32.lt_iff_toNat_lt, hhh, hr]
  have heq : r = hh ↔ mt.toNat % 2 ^ s.toNat = 2 ^ s.toNat / 2 := by
    rw [← UInt32.toNat_inj, hhh, hr]
  simp only [IEEE32.roundShift, ← hq0]
  by_cases c1 : mt.toNat % 2 ^ s.toNat < 2 ^ s.toNat / 2
  · have n1 : ¬ hh < r := by rw [hlt]; omega
    have n2 : ¬ r = hh := by rw [heq]; omega
    rw [ite_eq_right n1, ite_eq_right n2, ite_eq_left c1]
  · by_cases c2 : 2 ^ s.toNat / 2 < mt.toNat % 2 ^ s.toNat
    · rw [ite_eq_left (hlt.mpr c2), ite_eq_right c1, ite_eq_left c2, hadd]
    · have n1 : ¬ hh < r := by rw [hlt]; exact c2
      have y2 : r = hh := heq.mpr (by omega)
      rw [ite_eq_right n1, ite_eq_left y2, ite_eq_right c1, ite_eq_right c2]
      by_cases c3 : q0.toNat % 2 = 0
      · have n3 : ¬ (q0 &&& UInt32.ofNat 1 ≠ 0) := by rw [hodd]; omega
        rw [ite_eq_right n3, ite_eq_left (by simp [c3])]
      · rw [ite_eq_left (hodd.mpr c3), ite_eq_right (by simp [c3]), hadd]

end

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- The rounding statement of `nearest32Stmt`: the slot at height `h + 3` gets the quotient
rounded up when the remainder at `h + 4` exceeds the half at `h + 5`, or equals it and the
quotient is odd. -/
theorem exec_round32 {le : temp_env} {m : mem} {h : Nat} {q0 r hh : UInt32}
    (hq : le[slotId (h + 3) .i32]? = some (.Vint q0))
    (hr : le[slotId (h + 4) .i32]? = some (.Vint r))
    (hh' : le[slotId (h + 5) .i32]? = some (.Vint hh)) :
    let q := if hh < r then q0 + UInt32.ofNat 1
      else if r = hh then (if q0 &&& UInt32.ofNat 1 ≠ 0 then q0 + UInt32.ofNat 1 else q0)
      else q0
    ∃ le', exec_stmt A X E.ge empty_env le m
      (.Sifthenelse (.Ebinop .Ogt (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
        (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
        (.Sifthenelse (.Ebinop .Oeq (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
          (.Sifthenelse (.Ebinop .Oand (tmp (h + 3) .i32) (cint 1) tuint)
            (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
            .Sskip)
          .Sskip)) E0 le' m .Out_normal ∧
      le'[slotId (h + 3) .i32]? = some (.Vint q) ∧
      (∀ id, id ≠ slotId (h + 3) .i32 → le'[id]? = le[id]?) := by
  intro q
  have hinc : exec_stmt A X E.ge empty_env le m
      (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint)) E0
      (le.insert (slotId (h + 3) .i32) (.Vint (q0 + UInt32.ofNat 1))) m .Out_normal :=
    .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (eval_w hq) (eval_cint 1)
      (sem_add_ii A m q0 _))
  have hgt : eval_expr A E.ge empty_env le m
      (.Ebinop .Ogt (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
      (.Vint (if hh < r then 1 else 0)) :=
    .eval_Ebinop _ _ _ _ _ _ _ (eval_w hr) (eval_w hh') (sem_gt_ii A m r hh)
  have heq : eval_expr A E.ge empty_env le m
      (.Ebinop .Oeq (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
      (.Vint (if r = hh then 1 else 0)) :=
    .eval_Ebinop _ _ _ _ _ _ _ (eval_w hr) (eval_w hh') (sem_eq_ii A m r hh)
  have hodd : eval_expr A E.ge empty_env le m (.Ebinop .Oand (tmp (h + 3) .i32) (cint 1) tuint)
      (.Vint (q0 &&& UInt32.ofNat 1)) :=
    .eval_Ebinop _ _ _ _ _ _ _ (eval_w hq) (eval_cint 1) (sem_and_ii A m q0 _)
  have hkeep : ∀ v, ∀ id, id ≠ slotId (h + 3) .i32 →
      (le.insert (slotId (h + 3) .i32) v)[id]? = le[id]? :=
    fun v id hid => te_insert_ne _ (Ne.symm hid)
  by_cases c1 : hh < r
  · have hq' : q = q0 + UInt32.ofNat 1 := ite_eq_left c1
    refine ⟨_, .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hgt (by simp only [typeof]; rw [cond_bool, decide_eq_true c1])
      hinc, by rw [hq']; exact te_insert_same _ _ _, hkeep _⟩
  · by_cases c2 : r = hh
    · by_cases c3 : q0 &&& UInt32.ofNat 1 ≠ 0
      · have hq' : q = q0 + UInt32.ofNat 1 :=
          (ite_eq_right c1).trans ((ite_eq_left c2).trans (ite_eq_left c3))
        refine ⟨_, .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hgt
          (by simp only [typeof]; rw [cond_bool, decide_eq_false c1])
          (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ heq (by simp only [typeof]; rw [cond_bool, decide_eq_true c2])
            (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hodd
              (by simp only [typeof]; rw [cond_uint, decide_eq_true c3]) hinc)),
          by rw [hq']; exact te_insert_same _ _ _, hkeep _⟩
      · have hq' : q = q0 :=
          (ite_eq_right c1).trans ((ite_eq_left c2).trans (ite_eq_right c3))
        refine ⟨le, .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hgt
          (by simp only [typeof]; rw [cond_bool, decide_eq_false c1])
          (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ heq (by simp only [typeof]; rw [cond_bool, decide_eq_true c2])
            (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hodd
              (by simp only [typeof]; rw [cond_uint, decide_eq_false c3]) (.exec_Sskip _ _ _))),
          by rw [hq']; exact hq, fun _ _ => rfl⟩
    · have hq' : q = q0 := (ite_eq_right c1).trans (ite_eq_right c2)
      refine ⟨le, .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hgt
        (by simp only [typeof]; rw [cond_bool, decide_eq_false c1])
        (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ heq (by simp only [typeof]; rw [cond_bool, decide_eq_false c2])
          (.exec_Sskip _ _ _)),
        by rw [hq']; exact hq, fun _ _ => rfl⟩

theorem cast_uint_single (m : mem) (q : UInt32) :
    sem_cast (.Vint q) tuint tfloat m = some (.Vsingle (IEEE32.fromInt (q.toNat : _root_.Int))) := by
  show some (val.Vsingle (cast_int_single .Unsigned q)) = _
  rfl

theorem sem_neg_single (m : mem) (f : UInt32) :
    sem_unary_operation .Oneg (.Vsingle f) tfloat m = some (.Vsingle (IEEE32.negate f)) := rfl

theorem not_nan_signMask (b : Bool) : IEEE32.isNaN (IEEE32.signMask b) = false := by
  cases b <;> decide

theorem canonOf32_of_num {v : UInt32} (h : IEEE32.isNaN v = false) : canonOf32 v = v := by
  simp [canonOf32, h]

/-- A lookup of a slot past an insertion of another slot. -/
theorem lk_slot {le : temp_env} {a b : Nat} {t u : VT} {v w : val}
    (h : le[slotId a t]? = some v) (hne : a ≠ b ∨ t ≠ u) :
    (le.insert (slotId b u) w)[slotId a t]? = some v := by
  rcases hne with hne | hne
  · exact lk h (slotId_ne_of_height u t (Ne.symm hne))
  · by_cases hab : a = b
    · subst hab; exact lk h (slotId_ne_of_type a (Ne.symm hne))
    · exact lk h (slotId_ne_of_height u t (Ne.symm hab))

set_option maxRecDepth 100000 in
/-- `nearest32Stmt h` sets the float slot at height `h` to Talos's `nearest` of the float,
changing only slots from height `h` up and `lx_pun`. -/
theorem exec_nearest32 (hE : EnvOk E) {α : Type} {st : Store α} {le : temp_env} {m : mem}
    {h : Nat} {x : UInt32} (hx : le[slotId h .f32]? = some (.Vsingle x))
    (hst : StoreRel E st m) (hs : StatusRel E m 0) :
    ∃ le' m', exec_stmt A X E.ge empty_env le m (nearest32Stmt h) E0 le' m' .Out_normal ∧
      le'[slotId h .f32]? = some (.Vsingle (IEEE32.nearest x)) ∧ Keeps h le le' ∧
      StoreRel E st m' ∧ StatusRel E m' 0 := by
  have x1 := exec_punBits32 (A := A) (X := X) (k := h) hE hx hst
  have hst1 := hst.store_pun hE .Mfloat32 (.Vsingle x)
  have hs1 := hs.store_pun hE .Mfloat32 (.Vsingle x)
  generalize Mem.stored .Mfloat32 m E.pun 0 (.Vsingle x) = m1 at x1 hst1 hs1
  generalize hle1 : le.insert (slotId h .i32) (.Vint x) = le1 at x1
  have hu1 : le1[slotId h .i32]? = some (.Vint x) := by rw [← hle1]; exact te_insert_same _ _ _
  have hx1 : le1[slotId h .f32]? = some (.Vsingle x) := by
    rw [← hle1]; exact lk_slot hx (.inr (by decide))
  have k1 : Keeps h le le1 := by rw [← hle1]; exact Keeps.insert le (Nat.le_refl h) .i32 _
  -- the exponent
  obtain ⟨ev, hevd⟩ : ∃ ev, ev = (x >>> UInt32.ofNat 23) &&& UInt32.ofNat 255 := ⟨_, rfl⟩
  have hev : ev.toNat = IEEE32.exponent x := by rw [hevd]; exact exponent_word x
  have x2 : exec_stmt A X E.ge empty_env le1 m1 (.Sset (slotId (h + 1) .i32)
      (.Ebinop .Oand (.Ebinop .Oshr (tmp h .i32) (cint 23) tuint) (cint 255) tuint)) E0
      (le1.insert (slotId (h + 1) .i32) (.Vint ev)) m1 .Out_normal := by
    refine .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _
      (.eval_Ebinop _ _ _ _ _ _ _ (eval_w hu1) (eval_cint 23) (sem_shr_ii A m1 x _ (by decide)))
      (eval_cint 255) ?_)
    rw [hevd]; exact sem_and_ii A m1 _ _
  generalize hle2 : le1.insert (slotId (h + 1) .i32) (.Vint ev) = le2 at x2
  have hu2 : le2[slotId h .i32]? = some (.Vint x) := by rw [← hle2]; exact lk_slot hu1 (.inl (by omega))
  have he2 : le2[slotId (h + 1) .i32]? = some (.Vint ev) := by rw [← hle2]; exact te_insert_same _ _ _
  have hx2 : le2[slotId h .f32]? = some (.Vsingle x) := by rw [← hle2]; exact lk_slot hx1 (.inl (by omega))
  have k2 : Keeps h le le2 := by rw [← hle2]; exact k1.trans (Keeps.insert le1 (by omega) .i32 _)
  -- the sign
  have hsgn : ∀ (le' : temp_env) (m' : mem), le'[slotId h .i32]? = some (.Vint x) →
      eval_expr A E.ge empty_env le' m' (.Ebinop .Oshr (tmp h .i32) (cint 31) tuint)
        (.Vint (x >>> UInt32.ofNat 31)) :=
    fun le' m' hu => .eval_Ebinop _ _ _ _ _ _ _ (eval_w hu) (eval_cint 31)
      (sem_shr_ii A m' x _ (by decide))
  have hbsgn : ∀ m' : mem, bool_val (.Vint (x >>> UInt32.ofNat 31)) tuint m' =
      some (IEEE32.sign x) := by
    intro m'
    rw [cond_uint]
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, sign_word]
  -- the conditions on the exponent
  have hge : eval_expr A E.ge empty_env le2 m1 (.Ebinop .Oge (tmp (h + 1) .i32) (cint 150) tint)
      (.Vint (if ev ≥ UInt32.ofNat 150 then 1 else 0)) :=
    .eval_Ebinop _ _ _ _ _ _ _ (eval_w he2) (eval_cint 150) (sem_ge_ii A m1 ev _)
  have hlt126 : eval_expr A E.ge empty_env le2 m1 (.Ebinop .Olt (tmp (h + 1) .i32) (cint 126) tint)
      (.Vint (if ev < UInt32.ofNat 126 then 1 else 0)) :=
    .eval_Ebinop _ _ _ _ _ _ _ (eval_w he2) (eval_cint 126) (sem_lt_ii A m1 ev _)
  have hge_iff : ev ≥ UInt32.ofNat 150 ↔ 150 ≤ IEEE32.exponent x := by
    rw [ge_iff_le, UInt32.le_iff_toNat_le, toNat_u32 (by decide), hev]
  have hlt_iff : ev < UInt32.ofNat 126 ↔ IEEE32.exponent x < 126 := by
    rw [UInt32.lt_iff_toNat_lt, toNat_u32 (by decide), hev]
  -- the three cases, each leaving the float slot with a value whose canonical form is Talos's
  obtain ⟨le3, v, x3, hv3, hcv, k3⟩ : ∃ le3 v, exec_stmt A X E.ge empty_env le2 m1
      (.Sifthenelse (.Ebinop .Oge (tmp (h + 1) .i32) (cint 150) tint) .Sskip
        (.Sifthenelse (.Ebinop .Olt (tmp (h + 1) .i32) (cint 126) tint)
          (.Sifthenelse (.Ebinop .Oshr (tmp h .i32) (cint 31) tuint)
            (.Sset (slotId h .f32) (.Eunop .Oneg (.Econst_single 0 tfloat) tfloat))
            (.Sset (slotId h .f32) (.Econst_single 0 tfloat)))
          (seqList [
            .Sset (slotId (h + 2) .i32) (.Ebinop .Osub (cint 150) (tmp (h + 1) .i32) tuint),
            .Sset (slotId (h + 3) .i32) (.Ebinop .Oshr
              (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
              (tmp (h + 2) .i32) tuint),
            .Sset (slotId (h + 4) .i32) (.Ebinop .Oand
              (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
              (.Ebinop .Osub (.Ebinop .Oshl (cint 1) (tmp (h + 2) .i32) tuint) (cint 1) tuint) tuint),
            .Sset (slotId (h + 5) .i32)
              (.Ebinop .Oshl (cint 1) (.Ebinop .Osub (tmp (h + 2) .i32) (cint 1) tuint) tuint),
            .Sifthenelse (.Ebinop .Ogt (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
              (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
              (.Sifthenelse (.Ebinop .Oeq (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
                (.Sifthenelse (.Ebinop .Oand (tmp (h + 3) .i32) (cint 1) tuint)
                  (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
                  .Sskip)
                .Sskip),
            .Sset (slotId h .f32) (.Ecast (tmp (h + 3) .i32) tfloat),
            .Sifthenelse (.Ebinop .Oshr (tmp h .i32) (cint 31) tuint)
              (.Sset (slotId h .f32) (.Eunop .Oneg (tmp h .f32) tfloat)) .Sskip])))
      E0 le3 m1 .Out_normal ∧ le3[slotId h .f32]? = some (.Vsingle v) ∧
      canonOf32 v = IEEE32.nearest x ∧ Keeps h le2 le3 := by
    by_cases cA : 150 ≤ IEEE32.exponent x
    · refine ⟨le2, x, .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hge
        (by simp only [typeof]; rw [cond_bool, decide_eq_true (hge_iff.mpr cA)]) (.exec_Sskip _ _ _), hx2, ?_, Keeps.refl _ _⟩
      by_cases h255 : IEEE32.exponent x = 255
      · exact (nearest_255 x h255).symm
      · rw [nearest_big x cA h255, canonOf32_of_num]
        simp [IEEE32.isNaN, h255]
    · have nA : ¬ ev ≥ UInt32.ofNat 150 := fun h' => cA (hge_iff.mp h')
      by_cases cB : IEEE32.exponent x < 126
      · have yB : ev < UInt32.ofNat 126 := hlt_iff.mpr cB
        cases hsx : IEEE32.sign x
        · refine ⟨le2.insert (slotId h .f32) (.Vsingle 0), 0,
            .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hge (by simp only [typeof]; rw [cond_bool, decide_eq_false nA])
              (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hlt126 (by simp only [typeof]; rw [cond_bool, decide_eq_true yB])
                (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ (hsgn le2 m1 hu2)
                  (by simp only [typeof]; rw [hbsgn, hsx]) (.exec_Sset _ _ _ _ _ _ (.eval_Econst_single _ _)))),
            te_insert_same _ _ _, ?_, Keeps.insert le2 (Nat.le_refl h) .f32 _⟩
          rw [nearest_small x cB, hsx]; rfl
        · refine ⟨le2.insert (slotId h .f32) (.Vsingle (IEEE32.negate 0)), IEEE32.negate 0,
            .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hge (by simp only [typeof]; rw [cond_bool, decide_eq_false nA])
              (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hlt126 (by simp only [typeof]; rw [cond_bool, decide_eq_true yB])
                (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ (hsgn le2 m1 hu2)
                  (by simp only [typeof]; rw [hbsgn, hsx])
                  (.exec_Sset _ _ _ _ _ _ (.eval_Eunop _ _ _ _ _ (.eval_Econst_single _ _)
                    (sem_neg_single m1 0))))),
            te_insert_same _ _ _, ?_, Keeps.insert le2 (Nat.le_refl h) .f32 _⟩
          rw [nearest_small x cB, hsx]; decide
      · have nB : ¬ ev < UInt32.ofNat 126 := fun h' => cB (hlt_iff.mp h')
        have hE1 : 126 ≤ IEEE32.exponent x := by omega
        have hE2 : IEEE32.exponent x < 150 := by omega
        -- s = 150 - e
        obtain ⟨s, hsd⟩ : ∃ s, s = UInt32.ofNat 150 - ev := ⟨_, rfl⟩
        have hsn : s.toNat = 150 - IEEE32.exponent x := by
          rw [hsd, UInt32.toNat_sub, toNat_u32 (by decide), hev]; omega
        have y1 : exec_stmt A X E.ge empty_env le2 m1
            (.Sset (slotId (h + 2) .i32) (.Ebinop .Osub (cint 150) (tmp (h + 1) .i32) tuint)) E0
            (le2.insert (slotId (h + 2) .i32) (.Vint s)) m1 .Out_normal := by
          refine .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (eval_cint 150) (eval_w he2) ?_)
          rw [hsd]; exact sem_sub_ii' A m1 _ _
        generalize hle4 : le2.insert (slotId (h + 2) .i32) (.Vint s) = le4 at y1
        have hu4 : le4[slotId h .i32]? = some (.Vint x) := by
          rw [← hle4]; exact lk_slot hu2 (.inl (by omega))
        have hs4 : le4[slotId (h + 2) .i32]? = some (.Vint s) := by
          rw [← hle4]; exact te_insert_same _ _ _
        -- the significand
        obtain ⟨mt, hmtd⟩ : ∃ mt, mt = (x &&& UInt32.ofNat 0x7FFFFF) + UInt32.ofNat 0x800000 :=
          ⟨_, rfl⟩
        have hmt : mt.toNat = 2 ^ 23 + IEEE32.fraction x := by rw [hmtd]; exact significand_word x
        have hmant : ∀ le' : temp_env, le'[slotId h .i32]? = some (.Vint x) →
            eval_expr A E.ge empty_env le' m1
              (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
              (.Vint mt) := by
          intro le' hu
          refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (eval_w hu)
            (eval_cint 0x7FFFFF) (sem_and_ii A m1 x _)) (eval_cint 0x800000) ?_
          rw [hmtd]; exact sem_add_ii A m1 _ _
        have hs32 : s.toNat < 32 := by rw [hsn]; omega
        have y2 : exec_stmt A X E.ge empty_env le4 m1
            (.Sset (slotId (h + 3) .i32) (.Ebinop .Oshr
              (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
              (tmp (h + 2) .i32) tuint)) E0
            (le4.insert (slotId (h + 3) .i32) (.Vint (mt >>> s))) m1 .Out_normal :=
          .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (hmant le4 hu4) (eval_w hs4)
            (sem_shr_ii A m1 mt s hs32))
        generalize hle5 : le4.insert (slotId (h + 3) .i32) (.Vint (mt >>> s)) = le5 at y2
        have hu5 : le5[slotId h .i32]? = some (.Vint x) := by
          rw [← hle5]; exact lk_slot hu4 (.inl (by omega))
        have hs5 : le5[slotId (h + 2) .i32]? = some (.Vint s) := by
          rw [← hle5]; exact lk_slot hs4 (.inl (by omega))
        have hq5 : le5[slotId (h + 3) .i32]? = some (.Vint (mt >>> s)) := by
          rw [← hle5]; exact te_insert_same _ _ _
        have hpow32 : (UInt32.ofNat 1 <<< s).toNat < 2 ^ 32 := UInt32.toNat_lt _
        have y3 : exec_stmt A X E.ge empty_env le5 m1
            (.Sset (slotId (h + 4) .i32) (.Ebinop .Oand
              (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
              (.Ebinop .Osub (.Ebinop .Oshl (cint 1) (tmp (h + 2) .i32) tuint) (cint 1) tuint) tuint))
            E0 (le5.insert (slotId (h + 4) .i32)
              (.Vint (mt &&& ((UInt32.ofNat 1 <<< s) - UInt32.ofNat 1)))) m1 .Out_normal :=
          .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (hmant le5 hu5)
            (.eval_Ebinop _ _ _ _ _ _ _
              (.eval_Ebinop _ _ _ _ _ _ _ (eval_cint 1) (eval_w hs5) (sem_shl_ii A m1 _ s hs32))
              (eval_cint 1) (sem_sub_ii' A m1 _ _))
            (sem_and_ii A m1 _ _))
        generalize hle6 : le5.insert (slotId (h + 4) .i32)
          (.Vint (mt &&& ((UInt32.ofNat 1 <<< s) - UInt32.ofNat 1))) = le6 at y3
        have hs6 : le6[slotId (h + 2) .i32]? = some (.Vint s) := by
          rw [← hle6]; exact lk_slot hs5 (.inl (by omega))
        have hsm1 : (s - UInt32.ofNat 1).toNat < 32 := by
          rw [UInt32.toNat_sub, toNat_u32 (by decide)]; omega
        have y4 : exec_stmt A X E.ge empty_env le6 m1
            (.Sset (slotId (h + 5) .i32)
              (.Ebinop .Oshl (cint 1) (.Ebinop .Osub (tmp (h + 2) .i32) (cint 1) tuint) tuint)) E0
            (le6.insert (slotId (h + 5) .i32) (.Vint (UInt32.ofNat 1 <<< (s - UInt32.ofNat 1))))
            m1 .Out_normal :=
          .exec_Sset _ _ _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (eval_cint 1)
            (.eval_Ebinop _ _ _ _ _ _ _ (eval_w hs6) (eval_cint 1) (sem_sub_ii' A m1 s _))
            (sem_shl_ii A m1 _ _ hsm1))
        generalize hle7 : le6.insert (slotId (h + 5) .i32)
          (.Vint (UInt32.ofNat 1 <<< (s - UInt32.ofNat 1))) = le7 at y4
        have hq7 : le7[slotId (h + 3) .i32]? = some (.Vint (mt >>> s)) := by
          rw [← hle7, ← hle6]; exact lk_slot (lk_slot hq5 (.inl (by omega))) (.inl (by omega))
        have hr7 : le7[slotId (h + 4) .i32]? =
            some (.Vint (mt &&& ((UInt32.ofNat 1 <<< s) - UInt32.ofNat 1))) := by
          rw [← hle7, ← hle6]; exact lk_slot (te_insert_same _ _ _) (.inl (by omega))
        have hh7 : le7[slotId (h + 5) .i32]? =
            some (.Vint (UInt32.ofNat 1 <<< (s - UInt32.ofNat 1))) := by
          rw [← hle7]; exact te_insert_same _ _ _
        have hu7 : le7[slotId h .i32]? = some (.Vint x) := by
          rw [← hle7, ← hle6]; exact lk_slot (lk_slot hu5 (.inl (by omega))) (.inl (by omega))
        have hx7 : le7[slotId h .f32]? = some (.Vsingle x) := by
          rw [← hle7, ← hle6, ← hle5, ← hle4]
          exact lk_slot (lk_slot (lk_slot (lk_slot hx2 (.inl (by omega))) (.inl (by omega)))
            (.inl (by omega))) (.inl (by omega))
        obtain ⟨le8, y5, hq8, hk8⟩ := exec_round32 (A := A) (X := X) (E := E) (m := m1) hq7 hr7 hh7
        generalize hqd : (if UInt32.ofNat 1 <<< (s - UInt32.ofNat 1) <
              mt &&& ((UInt32.ofNat 1 <<< s) - UInt32.ofNat 1) then (mt >>> s) + UInt32.ofNat 1
            else if mt &&& ((UInt32.ofNat 1 <<< s) - UInt32.ofNat 1) =
                UInt32.ofNat 1 <<< (s - UInt32.ofNat 1) then
              (if (mt >>> s) &&& UInt32.ofNat 1 ≠ 0 then (mt >>> s) + UInt32.ofNat 1 else mt >>> s)
            else mt >>> s) = q at hq8
        have hqn : q.toNat = IEEE32.roundShift (2 ^ 23 + IEEE32.fraction x) (150 - IEEE32.exponent x) := by
          rw [← hqd, ← hmt, ← hsn]
          exact round_words mt s (by rw [hsn]; omega) (by rw [hsn]; omega)
            (by rw [hmt]; have := fraction_lt x; omega)
        have hu8 : le8[slotId h .i32]? = some (.Vint x) := by
          rw [hk8 _ (slotId_ne_of_height _ _ (by omega))]; exact hu7
        have y6 : exec_stmt A X E.ge empty_env le8 m1
            (.Sset (slotId h .f32) (.Ecast (tmp (h + 3) .i32) tfloat)) E0
            (le8.insert (slotId h .f32) (.Vsingle (IEEE32.fromInt (q.toNat : _root_.Int)))) m1
            .Out_normal :=
          .exec_Sset _ _ _ _ _ _ (.eval_Ecast _ _ _ _ (eval_w hq8) (cast_uint_single m1 q))
        generalize hle9 : le8.insert (slotId h .f32)
          (.Vsingle (IEEE32.fromInt (q.toNat : _root_.Int))) = le9 at y6
        have hu9 : le9[slotId h .i32]? = some (.Vint x) := by
          rw [← hle9]; exact lk_slot hu8 (.inr (by decide))
        have ht9 : le9[slotId h .f32]? = some (.Vsingle (IEEE32.fromInt (q.toNat : _root_.Int))) := by
          rw [← hle9]; exact te_insert_same _ _ _
        have hk78 : Keeps h le7 le8 :=
          ⟨fun h' hh t => hk8 _ (slotId_ne_of_height _ _ (by omega)),
            fun i => hk8 _ (slotId_ne_localId _ _ i).symm, hk8 _ (slotId_ne_brkId _ _).symm,
            hk8 _ (slotId_ne_limId _ _).symm⟩
        have k7 : Keeps h le2 le7 := by
          rw [← hle7, ← hle6, ← hle5, ← hle4]
          exact (((Keeps.insert le2 (by omega) .i32 _).trans (Keeps.insert _ (by omega) .i32 _)).trans
            (Keeps.insert _ (by omega) .i32 _)).trans (Keeps.insert _ (by omega) .i32 _)
        have k9 : Keeps h le2 le9 := by
          rw [← hle9]; exact (k7.trans hk78).trans (Keeps.insert _ (Nat.le_refl h) .f32 _)
        have hmid := nearest_mid x hE1 hE2
        rw [← hqn] at hmid
        have hcond : ∀ e, exec_stmt A X E.ge empty_env le2 m1 (seqList [
              .Sset (slotId (h + 2) .i32) (.Ebinop .Osub (cint 150) (tmp (h + 1) .i32) tuint),
              .Sset (slotId (h + 3) .i32) (.Ebinop .Oshr
                (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
                (tmp (h + 2) .i32) tuint),
              .Sset (slotId (h + 4) .i32) (.Ebinop .Oand
                (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
                (.Ebinop .Osub (.Ebinop .Oshl (cint 1) (tmp (h + 2) .i32) tuint) (cint 1) tuint) tuint),
              .Sset (slotId (h + 5) .i32)
                (.Ebinop .Oshl (cint 1) (.Ebinop .Osub (tmp (h + 2) .i32) (cint 1) tuint) tuint),
              .Sifthenelse (.Ebinop .Ogt (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
                (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
                (.Sifthenelse (.Ebinop .Oeq (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
                  (.Sifthenelse (.Ebinop .Oand (tmp (h + 3) .i32) (cint 1) tuint)
                    (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
                    .Sskip)
                  .Sskip),
              .Sset (slotId h .f32) (.Ecast (tmp (h + 3) .i32) tfloat),
              .Sifthenelse (.Ebinop .Oshr (tmp h .i32) (cint 31) tuint)
                (.Sset (slotId h .f32) (.Eunop .Oneg (tmp h .f32) tfloat)) .Sskip]) E0 e m1
              .Out_normal →
            exec_stmt A X E.ge empty_env le2 m1
              (.Sifthenelse (.Ebinop .Oge (tmp (h + 1) .i32) (cint 150) tint) .Sskip
                (.Sifthenelse (.Ebinop .Olt (tmp (h + 1) .i32) (cint 126) tint)
                  (.Sifthenelse (.Ebinop .Oshr (tmp h .i32) (cint 31) tuint)
                    (.Sset (slotId h .f32) (.Eunop .Oneg (.Econst_single 0 tfloat) tfloat))
                    (.Sset (slotId h .f32) (.Econst_single 0 tfloat)))
                  (seqList [
                    .Sset (slotId (h + 2) .i32) (.Ebinop .Osub (cint 150) (tmp (h + 1) .i32) tuint),
                    .Sset (slotId (h + 3) .i32) (.Ebinop .Oshr
                      (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint)
                        (cint 0x800000) tuint)
                      (tmp (h + 2) .i32) tuint),
                    .Sset (slotId (h + 4) .i32) (.Ebinop .Oand
                      (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint)
                        (cint 0x800000) tuint)
                      (.Ebinop .Osub (.Ebinop .Oshl (cint 1) (tmp (h + 2) .i32) tuint) (cint 1) tuint)
                      tuint),
                    .Sset (slotId (h + 5) .i32)
                      (.Ebinop .Oshl (cint 1) (.Ebinop .Osub (tmp (h + 2) .i32) (cint 1) tuint) tuint),
                    .Sifthenelse (.Ebinop .Ogt (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
                      (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
                      (.Sifthenelse (.Ebinop .Oeq (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
                        (.Sifthenelse (.Ebinop .Oand (tmp (h + 3) .i32) (cint 1) tuint)
                          (.Sset (slotId (h + 3) .i32)
                            (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
                          .Sskip)
                        .Sskip),
                    .Sset (slotId h .f32) (.Ecast (tmp (h + 3) .i32) tfloat),
                    .Sifthenelse (.Ebinop .Oshr (tmp h .i32) (cint 31) tuint)
                      (.Sset (slotId h .f32) (.Eunop .Oneg (tmp h .f32) tfloat)) .Sskip])))
              E0 e m1 .Out_normal := fun e he =>
          .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hge (by simp only [typeof]; rw [cond_bool, decide_eq_false nA])
            (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hlt126 (by simp only [typeof]; rw [cond_bool, decide_eq_false nB]) he)
        have hfirst : ∀ (e : temp_env) (s7 : statement), exec_stmt A X E.ge empty_env le9 m1 s7 E0 e m1
            .Out_normal →
            exec_stmt A X E.ge empty_env le2 m1 (.Ssequence
              (.Sset (slotId (h + 2) .i32) (.Ebinop .Osub (cint 150) (tmp (h + 1) .i32) tuint))
              (.Ssequence (.Sset (slotId (h + 3) .i32) (.Ebinop .Oshr
                (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
                (tmp (h + 2) .i32) tuint))
              (.Ssequence (.Sset (slotId (h + 4) .i32) (.Ebinop .Oand
                (.Ebinop .Oadd (.Ebinop .Oand (tmp h .i32) (cint 0x7FFFFF) tuint) (cint 0x800000) tuint)
                (.Ebinop .Osub (.Ebinop .Oshl (cint 1) (tmp (h + 2) .i32) tuint) (cint 1) tuint) tuint))
              (.Ssequence (.Sset (slotId (h + 5) .i32)
                (.Ebinop .Oshl (cint 1) (.Ebinop .Osub (tmp (h + 2) .i32) (cint 1) tuint) tuint))
              (.Ssequence (.Sifthenelse (.Ebinop .Ogt (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
                (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
                (.Sifthenelse (.Ebinop .Oeq (tmp (h + 4) .i32) (tmp (h + 5) .i32) tint)
                  (.Sifthenelse (.Ebinop .Oand (tmp (h + 3) .i32) (cint 1) tuint)
                    (.Sset (slotId (h + 3) .i32) (.Ebinop .Oadd (tmp (h + 3) .i32) (cint 1) tuint))
                    .Sskip)
                  .Sskip))
              (.Ssequence (.Sset (slotId h .f32) (.Ecast (tmp (h + 3) .i32) tfloat)) s7))))))
              E0 e m1 .Out_normal := fun e s7 h7 =>
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ y1 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ y2
            (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ y3 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ y4
              (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ y5 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ y6 h7)))))
        cases hsx : IEEE32.sign x
        · refine ⟨le9, IEEE32.fromInt (q.toNat : _root_.Int),
            hcond _ (hfirst _ _ (.exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ (hsgn le9 m1 hu9)
              (by simp only [typeof]; rw [hbsgn, hsx]) (.exec_Sskip _ _ _))), ht9, ?_, k9⟩
          rw [hmid, hsx, fromInt_nat,
            canonOf32_of_num (LeanExe.ProofKit.F32Nearest.isNaN_roundScaledMagnitude _ _)]
        · refine ⟨le9.insert (slotId h .f32)
            (.Vsingle (IEEE32.negate (IEEE32.fromInt (q.toNat : _root_.Int)))),
            IEEE32.negate (IEEE32.fromInt (q.toNat : _root_.Int)),
            hcond _ (hfirst _ _ (.exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ (hsgn le9 m1 hu9)
              (by simp only [typeof]; rw [hbsgn, hsx])
              (.exec_Sset _ _ _ _ _ _ (.eval_Eunop _ _ _ _ _ (.eval_Etempvar _ _ _ ht9)
                (sem_neg_single m1 _))))),
            te_insert_same _ _ _, ?_, k9.trans (Keeps.insert _ (Nat.le_refl h) .f32 _)⟩
          rw [hmid, hsx, fromInt_nat, negate_roundScaled,
            canonOf32_of_num (LeanExe.ProofKit.F32Nearest.isNaN_roundScaledMagnitude _ _)]
  -- the canonicalization
  obtain ⟨le4, m4, x4, hslot, hk4, hst4, hs4⟩ := exec_canon32 (A := A) (X := X) hE hv3 hst1 hs1
  refine ⟨le4, m4, ?_, by rw [hslot, hcv], ?_, hst4, hs4⟩
  · exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ x1 (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ x2
      (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ x3 x4))
  · refine (k2.trans k3).trans ⟨fun h' hh t => hk4 _ (slotId_ne_of_height _ _ (by omega)),
      fun i => hk4 _ (slotId_ne_localId _ _ i).symm, hk4 _ (slotId_ne_brkId _ _).symm,
        hk4 _ (slotId_ne_limId _ _).symm⟩

end

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

theorem sim_f32Nearest (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f32Nearest := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f32 hinv.stack
      simp only [execOne.eq_def, hvs]
      obtain ⟨le', m', hx', hslot, hk, hst, hs⟩ :=
        exec_nearest32 (A := A) (X := X) hE hx hinv.store hinv.status
      exact push_exec_scratch hrest hinv.locals hinv.brk hinv.lim hb hx' hslot rfl hk.1 hk.2.1 hk.2.2 hst hs

end

end LeanExe.Native
