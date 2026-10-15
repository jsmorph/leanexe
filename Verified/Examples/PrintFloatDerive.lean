import Verified.Examples.PrintFloatDigits
import Verified.Examples.ParseFloatDigits

/-!
The layouts as numbers of RFC 8259's grammar.  For `t ≥ 1`, `sci_derives` shows that
`sciLayout neg t k` denotes `(-1)^neg · t · 10^k`, and `ecma_derives` shows the same for
`ecmaLayout neg t k`, except for the plain layout with trailing zeros (`0 ≤ k` and the point
position `k + digits` at most 21), which denotes `(-1)^neg · (t · 10^k) · 10^0`.
-/

namespace Verified.Examples.PrintFloatDerive
open StrconvGrammar StrconvRound PrintFloatDigits ParseFloatDigits ParseFloatScan

theorem ascii_e : ascii "e" = [0x65] := rfl

theorem ascii_zero_point : ascii "0." = ascii "0" ++ ascii "." := rfl

theorem digitsOf_ne (n : ℕ) : digitsOf n ≠ [] := by
  intro h
  have := dlen_pos n
  unfold dlen at this
  rw [h] at this
  simp at this

/-- The digits of a positive number: a first digit from 1 to 9 and further digits. -/
theorem digits_cons (t : ℕ) (ht : 1 ≤ t) :
    ∃ c rest, digitsOf t = c :: rest ∧ 0x31 ≤ c ∧ c ≤ 0x39 ∧
      ∀ b ∈ rest, isDigit b = true := by
  have hd := digitsOf_digits t
  have hh := digitsOf_head t ht
  have hne := digitsOf_ne t
  cases hcr : digitsOf t with
  | nil => exact absurd hcr hne
  | cons c rest =>
    rw [hcr] at hd hh
    have hc := hd c (by simp)
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hc0 : c ≠ 0x30 := hh
    refine ⟨c, rest, rfl, ?_, hc.2, fun b hb => hd b (List.mem_cons_of_mem _ hb)⟩
    have h1 := hc.1
    rw [UInt8.le_iff_toNat_le, show (0x30 : UInt8).toNat = 48 from rfl] at h1
    have hne' : c.toNat ≠ 48 := fun h => hc0 (UInt8.toNat_inj.mp h)
    rw [UInt8.le_iff_toNat_le, show (0x31 : UInt8).toNat = 49 from rfl]
    omega

theorem sign_json (neg : Bool) : Sign false (if neg then ascii "-" else []) neg := by
  cases neg
  · exact Sign.none false
  · exact Sign.minus false

theorem marker_e : (0x65 : UInt8) ∈ ascii "eE" := by rw [ascii_eE]; decide

/-- The exponent of the scientific layout. -/
theorem exp_sci (x : ℤ) :
    OptExponent (ascii "eE") (ascii "e" ++ (if x < 0 then ascii "-" else []) ++ digitsOf x.natAbs)
      x := by
  apply OptExponent.some
  rw [ascii_e]
  by_cases h : x < 0
  · rw [ite_eq_left h]
    have := Exponent.minus 0x65 (digitsOf x.natAbs) marker_e (digitsOf_ne _)
      (digitsOf_digits _)
    rw [decValue_digitsOf, show -((x.natAbs : ℕ) : ℤ) = x by omega] at this
    simpa only [List.cons_append, List.nil_append] using this
  · rw [ite_eq_right h]
    have := Exponent.plain 0x65 (digitsOf x.natAbs) marker_e (digitsOf_ne _)
      (digitsOf_digits _)
    rw [decValue_digitsOf, show ((x.natAbs : ℕ) : ℤ) = x by omega] at this
    simpa only [List.cons_append, List.nil_append, List.append_nil] using this

/-- The exponent of the ECMAScript layout. -/
theorem exp_ecma (x : ℤ) :
    OptExponent (ascii "eE")
      (ascii "e" ++ (if 0 ≤ x then ascii "+" else ascii "-") ++ digitsOf x.natAbs) x := by
  apply OptExponent.some
  rw [ascii_e]
  by_cases h : 0 ≤ x
  · rw [ite_eq_left h]
    have := Exponent.plus 0x65 (digitsOf x.natAbs) marker_e (digitsOf_ne _)
      (digitsOf_digits _)
    rw [decValue_digitsOf, show ((x.natAbs : ℕ) : ℤ) = x by omega] at this
    simpa only [List.cons_append, List.nil_append] using this
  · rw [ite_eq_right h]
    have := Exponent.minus 0x65 (digitsOf x.natAbs) marker_e (digitsOf_ne _)
      (digitsOf_digits _)
    rw [decValue_digitsOf, show -((x.natAbs : ℕ) : ℤ) = x by omega] at this
    simpa only [List.cons_append, List.nil_append] using this

/-- The fraction of the layouts with a point after the first digit. -/
theorem frac_one (c : UInt8) (rest : List UInt8) (hrest : ∀ b ∈ rest, isDigit b = true) :
    JsonFrac (if (c :: rest).length = 1 then [] else ascii "." ++ (c :: rest).drop 1)
      ((c :: rest).drop 1) := by
  rcases rest with _ | ⟨b, r⟩
  · rw [ite_eq_left (show [c].length = 1 from rfl)]
    exact JsonFrac.none
  · rw [ite_eq_right (show ¬ (c :: b :: r).length = 1 by simp)]
    exact JsonFrac.some (b :: r) (by simp) hrest

/-- The significand and exponent of the layouts with an exponent: the first digit, the others
after a point, and the exponent `x`. -/
theorem sci_ds (neg : Bool) (c : UInt8) (rest : List UInt8) (hc1 : 0x31 ≤ c) (hc2 : c ≤ 0x39)
    (hrest : ∀ b ∈ rest, isDigit b = true) (xs : List UInt8) (x : ℤ)
    (hx : OptExponent (ascii "eE") xs x) :
    Derives false ((if neg then ascii "-" else []) ++ ((c :: rest).take 1 ++
        (if (c :: rest).length = 1 then [] else ascii "." ++ (c :: rest).drop 1) ++ xs))
      (.dec neg (decValue (c :: rest)) (x - ((c :: rest).length - 1 : ℕ))) := by
  have hi : JsonInt ((c :: rest).take 1) := JsonInt.nonzero c [] hc1 hc2 (by simp)
  have h := Derives.json _ _ _ _ _ neg x (sign_json neg) hi (frac_one c rest hrest) hx
  rw [List.take_append_drop, List.length_drop] at h
  simpa only [List.append_assoc] using h

/-- **The scientific layout is a number of RFC 8259's grammar.** -/
theorem sci_derives (neg : Bool) (t : ℕ) (k : ℤ) (ht : 1 ≤ t) :
    Derives false (sciLayout neg t k) (.dec neg t k) := by
  obtain ⟨c, rest, hcr, hc1, hc2, hrest⟩ := digits_cons t ht
  have h := sci_ds neg c rest hc1 hc2 hrest _ _ (exp_sci (k + (rest.length + 1 : ℕ) - 1))
  rw [← hcr, decValue_digitsOf] at h
  have hl : (digitsOf t).length = rest.length + 1 := by rw [hcr]; rfl
  rw [hl, show k + ((rest.length + 1 : ℕ) : ℤ) - 1 - ((rest.length + 1 - 1 : ℕ) : ℤ) = k by
    omega] at h
  unfold sciLayout
  dsimp only
  rw [hl]
  simpa only [List.append_assoc] using h

/-- **The ECMAScript layout is a number of RFC 8259's grammar**, of the value `t · 10^k`. -/
theorem ecma_derives (neg : Bool) (t : ℕ) (k : ℤ) (ht : 1 ≤ t) :
    Derives false (ecmaLayout neg t k) (.dec neg t k) ∨
      ∃ z : ℕ, k = z ∧ Derives false (ecmaLayout neg t k) (.dec neg (t * 10 ^ z) 0) := by
  obtain ⟨c, rest, hcr, hc1, hc2, hrest⟩ := digits_cons t ht
  have hval := decValue_digitsOf t
  have hdig := digitsOf_digits t
  obtain ⟨L, hL⟩ : ∃ L, L = (digitsOf t).length := ⟨_, rfl⟩
  have hL1 : (digitsOf t).length = rest.length + 1 := by rw [hcr]; rfl
  unfold ecmaLayout
  dsimp only
  rw [← hL]
  by_cases h1 : (L : ℤ) ≤ k + L ∧ k + L ≤ 21
  · -- the digits and zeros
    rw [ite_eq_left h1]
    right
    refine ⟨(k + L - L).toNat, by omega, ?_⟩
    have hz : ∀ b ∈ List.replicate (k + L - L).toNat (0x30 : UInt8), isDigit b = true := by
      intro b hb
      rw [List.eq_of_mem_replicate hb]
      decide
    have hi : JsonInt (digitsOf t ++ List.replicate (k + L - L).toNat 0x30) := by
      rw [hcr, List.cons_append]
      refine JsonInt.nonzero c _ hc1 hc2 ?_
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hrest b hb
      · exact hz b hb
    have h := Derives.json _ _ _ _ _ neg 0 (sign_json neg) hi JsonFrac.none OptExponent.none
    simp only [List.append_nil, List.length_nil, Nat.cast_zero, sub_zero] at h
    rw [decValue_append, hval,
      (decValue_eq_zero _ hz).mpr (fun b hb => List.eq_of_mem_replicate hb), add_zero,
      List.length_replicate] at h
    exact h
  rw [ite_eq_right h1]
  by_cases h2 : 0 < k + L ∧ k + L ≤ 21
  · -- a point inside the digits
    rw [ite_eq_left h2]
    left
    obtain ⟨m, hm⟩ : ∃ m, m = (k + L).toNat := ⟨_, rfl⟩
    rw [← hm]
    have hm0 : 1 ≤ m := by omega
    have hmL : m < L := by omega
    have hi : JsonInt ((digitsOf t).take m) := by
      rw [hcr, show m = (m - 1) + 1 by omega, List.take_succ_cons]
      exact JsonInt.nonzero c _ hc1 hc2 (fun b hb => hrest b (List.mem_of_mem_take hb))
    have hf : JsonFrac (ascii "." ++ (digitsOf t).drop m) ((digitsOf t).drop m) := by
      refine JsonFrac.some _ ?_ (fun b hb => hdig b (List.mem_of_mem_drop hb))
      rw [← List.length_pos_iff, List.length_drop]
      omega
    have h := Derives.json _ _ _ _ _ neg 0 (sign_json neg) hi hf OptExponent.none
    rw [List.take_append_drop, hval, List.length_drop, ← hL,
      show (0 : ℤ) - ((L - m : ℕ) : ℤ) = k by omega] at h
    simpa only [List.append_assoc, List.append_nil] using h
  rw [ite_eq_right h2]
  by_cases h3 : -6 < k + L ∧ k + L ≤ 0
  · -- `0.`, zeros, and the digits
    rw [ite_eq_left h3]
    left
    obtain ⟨z, hz⟩ : ∃ z, z = (-(k + L)).toNat := ⟨_, rfl⟩
    rw [← hz]
    have hzd : ∀ b ∈ List.replicate z (0x30 : UInt8), isDigit b = true := by
      intro b hb
      rw [List.eq_of_mem_replicate hb]
      decide
    have hf : JsonFrac (ascii "." ++ (List.replicate z 0x30 ++ digitsOf t))
        (List.replicate z 0x30 ++ digitsOf t) := by
      refine JsonFrac.some _ (by simp [digitsOf_ne]) ?_
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hzd b hb
      · exact hdig b hb
    have h := Derives.json _ _ _ _ _ neg 0 (sign_json neg) JsonInt.zero hf OptExponent.none
    rw [decValue_append, decValue_append, hval,
      (decValue_eq_zero _ hzd).mpr (fun b hb => List.eq_of_mem_replicate hb),
      show decValue (ascii "0") = 0 from rfl, List.length_append, List.length_replicate, ← hL,
      show (0 : ℤ) - ((z + L : ℕ) : ℤ) = k by omega] at h
    rw [ascii_zero_point]
    simpa only [List.append_assoc, List.append_nil, zero_mul, zero_add] using h
  · -- an exponent
    rw [ite_eq_right h3]
    left
    have h := sci_ds neg c rest hc1 hc2 hrest _ _ (exp_ecma (k + L - 1))
    rw [← hcr, hval, ← hL, show k + (L : ℤ) - 1 - ((L - 1 : ℕ) : ℤ) = k by omega] at h
    simpa only [List.append_assoc] using h

#print axioms sci_derives
#print axioms ecma_derives

end Verified.Examples.PrintFloatDerive
