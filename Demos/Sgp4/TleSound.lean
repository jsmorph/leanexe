import Demos.Sgp4.Tle
import Demos.Sgp4.BoxSound
import LeanExe.Dialect.Lemmas
import LeanExe.ProofKit.Signed64Value

/-!
The layout of a two-line element set and the soundness of its reader.  `WellFormed s1 s2` states
the layout that `Tle.read` checks, and `elements s1 s2` is the element set that the digits of two
lines denote, as real numbers.  `read_status` states that `read` returns status 0 exactly for the
lines of the layout, `read_encloses` that its intervals contain the element set, and
`propagate_sound` and `propagate_status` state the results of `sgp4Box_sound` and `status_sound`
for the lines.
-/

namespace Demos.Sgp4.Tle

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 LeanExe.ProofKit

/-! ### The layout and the values -/

/-- The byte is a digit. -/
def IsDigit (c : UInt64) : Prop := 48 ≤ c ∧ c ≤ 57

/-- The value of a digit, and 0 for any other byte. -/
def digitValue (c : UInt64) : ℕ := if 48 ≤ c ∧ c ≤ 57 then c.toNat - 48 else 0

/-- The number that the `k` bytes from column `start` denote. -/
def value (s : Array UInt64) (start k : ℕ) : ℕ :=
  Nat.fold k (fun j _ v => v * 10 + digitValue s[start + j]!) 0

/-- The `k` bytes from column `start` are digits. -/
def Digits (s : Array UInt64) (start k : ℕ) : Prop := ∀ j < k, IsDigit s[start + j]!

/-- Two columns hold two digits, or a space and a digit. -/
def Padded2 (s : Array UInt64) (start : UInt64) : Prop :=
  IsDigit (byteAt s (start + 1)) ∧ (IsDigit (byteAt s start) ∨ byteAt s start = 32)

/-- Three columns hold digits after spaces, with a digit last. -/
def Padded3 (s : Array UInt64) (start : UInt64) : Prop :=
  IsDigit (byteAt s (start + 2)) ∧
    ((IsDigit (byteAt s (start + 1)) ∧ (IsDigit (byteAt s start) ∨ byteAt s start = 32)) ∨
      (byteAt s (start + 1) = 32 ∧ byteAt s start = 32))

/-- The weight of a byte in the checksum: a digit's value, 1 for a minus sign, 0 otherwise. -/
def weight (c : UInt64) : ℕ := if 48 ≤ c ∧ c ≤ 57 then c.toNat - 48 else if c = 45 then 1 else 0

/-- The sum of the weights of the first 68 columns, modulo 10. -/
def checksumValue (s : Array UInt64) : ℕ := Nat.fold 68 (fun i _ a => a + weight s[i]!) 0 % 10

/-- A line of 69 bytes that begins with `first` and a space and ends with its checksum. -/
def Framed (s : Array UInt64) (first : UInt64) : Prop :=
  s.size = 69 ∧ byteAt s 0 = first ∧ byteAt s 1 = 32 ∧
    (byteAt s 68).toNat = checksumValue s + 48

/-- Line 1: the frame and the columns of the drag term. -/
def Layout1 (s : Array UInt64) : Prop :=
  Framed s 49 ∧ byteAt s 52 = 32 ∧ (byteAt s 53 = 32 ∨ byteAt s 53 = 43 ∨ byteAt s 53 = 45) ∧
    Digits s 54 5 ∧ (byteAt s 59 = 43 ∨ byteAt s 59 = 45) ∧ IsDigit (byteAt s 60) ∧
    byteAt s 61 = 32

/-- Line 2: the frame and the columns of the six fields. -/
def Layout2 (s : Array UInt64) : Prop :=
  Framed s 50 ∧ byteAt s 7 = 32 ∧
    Padded3 s 8 ∧ byteAt s 11 = 46 ∧ Digits s 12 4 ∧ byteAt s 16 = 32 ∧
    Padded3 s 17 ∧ byteAt s 20 = 46 ∧ Digits s 21 4 ∧ byteAt s 25 = 32 ∧
    Digits s 26 7 ∧ byteAt s 33 = 32 ∧
    Padded3 s 34 ∧ byteAt s 37 = 46 ∧ Digits s 38 4 ∧ byteAt s 42 = 32 ∧
    Padded3 s 43 ∧ byteAt s 46 = 46 ∧ Digits s 47 4 ∧ byteAt s 51 = 32 ∧
    Padded2 s 52 ∧ byteAt s 54 = 46 ∧ Digits s 55 8

/-- The catalog fields of the two lines hold the same bytes. -/
def SameObject (s1 s2 : Array UInt64) : Prop :=
  byteAt s1 2 = byteAt s2 2 ∧ byteAt s1 3 = byteAt s2 3 ∧ byteAt s1 4 = byteAt s2 4 ∧
    byteAt s1 5 = byteAt s2 5 ∧ byteAt s1 6 = byteAt s2 6

/-- The two lines of an element set in the layout that the reader accepts. -/
def WellFormed (s1 s2 : Array UInt64) : Prop := Layout1 s1 ∧ Layout2 s2 ∧ SameObject s1 s2

/-- An angle in degrees: three columns, a point, and four digits from column `start`. -/
noncomputable def angleValue (s : Array UInt64) (start : ℕ) : ℝ :=
  ((value s start 3 * 10000 + value s (start + 4) 4 : ℕ) : ℝ) / 10 ^ 4

/-- The drag term: the five digits `m` as `0.m` times ten to the signed exponent, with the sign
of column 54. -/
noncomputable def dragValue (s : Array UInt64) : ℝ :=
  let m : ℝ := (value s 54 5 : ℕ)
  let x := digitValue (byteAt s 60)
  let magnitude := if byteAt s 59 = 45 then m / 10 ^ (5 + x) else m * 10 ^ x / 10 ^ 5
  if byteAt s 53 = 45 then -magnitude else magnitude

/-- The element set that the digits of two lines denote. -/
noncomputable def elements (s1 s2 : Array UInt64) : Model.Elements where
  n := ((value s2 52 2 * 100000000 + value s2 55 8 : ℕ) : ℝ) / 10 ^ 8
  e := ((value s2 26 7 : ℕ) : ℝ) / 10 ^ 7
  incl := angleValue s2 8
  node := angleValue s2 17
  argp := angleValue s2 34
  m := angleValue s2 43
  bstar := dragValue s1

/-! ### Digits and numbers -/

theorem isDigit_iff (c : UInt64) : isDigit c = true ↔ IsDigit c := by
  simp [isDigit, IsDigit]

theorem digitValue_le (c : UInt64) : digitValue c ≤ 9 := by
  unfold digitValue
  by_cases h : 48 ≤ c ∧ c ≤ 57
  · simp only [h, and_self, ite_true]
    have := UInt64.le_iff_toNat_le.mp h.2
    simp only [UInt64.reduceToNat] at this
    omega
  · simp only [h, ite_false]
    omega

theorem digitOf_toNat (c : UInt64) : (digitOf c).toNat = digitValue c := by
  unfold digitOf digitValue
  by_cases h : 48 ≤ c ∧ c ≤ 57
  · simp only [h, and_self, ite_true]
    rw [UInt64.toNat_sub_of_le c 48 h.1]
    rfl
  · simp only [h, ite_false]
    rfl

theorem index_toNat (start : UInt64) (k : ℕ) (h : start.toNat + k < 2 ^ 64) :
    (start + UInt64.ofNat k).toNat = start.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  omega

theorem value_succ (s : Array UInt64) (start k : ℕ) :
    value s start (k + 1) = value s start k * 10 + digitValue s[start + k]! := by
  simp [value, Nat.fold_succ]

theorem fieldNat_spec (s : Array UInt64) (start k : UInt64) (hk : k.toNat ≤ 18)
    (hs : start.toNat + k.toNat < 2 ^ 64) :
    (fieldNat s start k).toNat = value s start.toNat k.toNat ∧
      value s start.toNat k.toNat < 10 ^ k.toNat := by
  have key := LeanExe.Dialect.loop_induction (n := k) (init := (0 : UInt64))
    (f := fun j v => v * 10 + digitOf (byteAt s (start + j)))
    (fun j v => v.toNat = value s start.toNat j ∧ v.toNat < 10 ^ j)
    ⟨by simp [value], by simp⟩
    (by
      intro j v hj ⟨h1, h2⟩
      have hidx := index_toNat start j (by omega)
      have hb : byteAt s (start + UInt64.ofNat j) = s[start.toNat + j]! := by
        unfold byteAt; rw [hidx]
      have hd := digitOf_toNat s[start.toNat + j]!
      have hle := digitValue_le s[start.toNat + j]!
      have hp : 10 ^ j ≤ 10 ^ 17 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hv : (v * 10 + digitOf (byteAt s (start + UInt64.ofNat j))).toNat =
          v.toNat * 10 + digitValue s[start.toNat + j]! := by
        rw [hb, UInt64.toNat_add, UInt64.toNat_mul, hd]
        simp only [UInt64.reduceToNat]
        omega
      refine ⟨?_, ?_⟩
      · rw [hv, value_succ, h1]
      · rw [hv, pow_succ]
        omega)
  exact ⟨key.1, by rw [← key.1]; exact key.2⟩

theorem allDigits_spec (s : Array UInt64) (start k : UInt64)
    (hs : start.toNat + k.toNat < 2 ^ 64) :
    allDigits s start k = true ↔ Digits s start.toNat k.toNat := by
  exact LeanExe.Dialect.loop_induction (n := k) (init := true)
    (f := fun j b => b && isDigit (byteAt s (start + j)))
    (fun j b => b = true ↔ ∀ i < j, IsDigit s[start.toNat + i]!)
    (by simp)
    (by
      intro j b hj h
      have hidx := index_toNat start j (by omega)
      have hb : byteAt s (start + UInt64.ofNat j) = s[start.toNat + j]! := by
        unfold byteAt; rw [hidx]
      rw [Bool.and_eq_true, h, isDigit_iff, hb]
      constructor
      · rintro ⟨a, b'⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact a i h'
        · rw [h']; exact b'
      · intro a
        exact ⟨fun i hi => a i (by omega), a j (by omega)⟩)

theorem checksum_spec (s : Array UInt64) : (checksum s).toNat = checksumValue s := by
  have key := LeanExe.Dialect.loop_induction (n := 68) (init := (0 : UInt64))
    (f := fun i acc =>
      let c := byteAt s i
      acc + (if 48 ≤ c ∧ c ≤ 57 then c - 48 else if c == 45 then 1 else 0))
    (fun j a => a.toNat = Nat.fold j (fun i _ a => a + weight s[i]!) 0 ∧ a.toNat ≤ 9 * j)
    ⟨by simp, by simp⟩
    (by
      intro j a hj ⟨h1, h2⟩
      simp only [UInt64.reduceToNat] at hj
      have hto : (UInt64.ofNat j).toNat = j :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have hb : byteAt s (UInt64.ofNat j) = s[j]! := by unfold byteAt; rw [hto]
      have hw : (if 48 ≤ s[j]! ∧ s[j]! ≤ 57 then s[j]! - 48
          else if s[j]! == 45 then 1 else 0 : UInt64).toNat = weight s[j]! ∧
          weight s[j]! ≤ 9 := by
        unfold weight
        by_cases h : 48 ≤ s[j]! ∧ s[j]! ≤ 57
        · simp only [h, and_self, ite_true]
          have := UInt64.le_iff_toNat_le.mp h.2
          simp only [UInt64.reduceToNat] at this
          refine ⟨?_, by omega⟩
          rw [UInt64.toNat_sub_of_le _ _ h.1]
          rfl
        · by_cases h' : s[j]! = 45 <;> simp [h, h']
      simp only [hb]
      refine ⟨?_, ?_⟩
      · rw [UInt64.toNat_add, hw.1, Nat.fold_succ, ← h1]
        omega
      · rw [UInt64.toNat_add, hw.1]
        omega)
  unfold checksum checksumValue
  rw [UInt64.toNat_mod, key.1]
  rfl

theorem pow10_spec (k : UInt64) (hk : k.toNat ≤ 19) : (pow10 k).toNat = 10 ^ k.toNat := by
  exact LeanExe.Dialect.loop_induction (n := k) (init := (1 : UInt64)) (f := fun _ p => p * 10)
    (fun j p => p.toNat = 10 ^ j) (by simp)
    (by
      intro j p hj h
      have hp : 10 ^ (j + 1) ≤ 10 ^ 19 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [UInt64.toNat_mul, h]
      simp only [UInt64.reduceToNat]
      rw [pow_succ] at hp ⊢
      omega)

/-- The interval of `m / 10 ^ k` contains that number. -/
theorem scaled_encloses (m k : UInt64) (hm : m.toNat ≤ 2 ^ 53) (hk : k.toNat ≤ 15) :
    Encloses (scaled m k) ((m.toNat : ℝ) / 10 ^ k.toNat) := by
  unfold scaled
  have hp := pow10_spec k (by omega)
  have h10 : 10 ^ k.toNat ≤ 10 ^ 15 := Nat.pow_le_pow_right (by norm_num) hk
  refine encloses_ratio' (m := (m.toNat : ℤ)) (k := ((10 ^ k.toNat : ℕ) : ℤ)) ?_ ?_ ?_ ?_ ?_
  · rw [Signed64Value.toInt_toInt64, ite_eq_left (by omega)]
  · rw [Signed64Value.toInt_toInt64, hp, ite_eq_left (by omega)]
  · rw [Int.natAbs_natCast]; exact hm
  · rw [Int.natAbs_natCast]; omega
  · push_cast; rfl

/-! ### The reader -/

theorem framed_iff (s : Array UInt64) (first : UInt64) (hs : s.size < 2 ^ 64) :
    framed s first = true ↔ Framed s first := by
  have h1 : s.size.toUInt64 = 69 ↔ s.size = 69 := by
    rw [← UInt64.toNat_inj]
    show (UInt64.ofNat s.size).toNat = (69 : UInt64).toNat ↔ _
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
    simp only [UInt64.reduceToNat]
  have h2 : byteAt s 68 = checksum s + 48 ↔ (byteAt s 68).toNat = checksumValue s + 48 := by
    have hc := checksum_spec s
    have hlt : checksumValue s < 10 := by unfold checksumValue; omega
    rw [← UInt64.toNat_inj, UInt64.toNat_add, hc]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  simp only [framed, Framed, Bool.and_eq_true, beq_iff_eq, h1, h2, and_assoc]

theorem padded2_iff (s : Array UInt64) (start : UInt64) :
    padded2 s start = true ↔ Padded2 s start := by
  simp only [padded2, Padded2, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, isDigit_iff]

theorem padded3_iff (s : Array UInt64) (start : UInt64) :
    padded3 s start = true ↔ Padded3 s start := by
  simp only [padded3, Padded3, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, isDigit_iff]

theorem layout1_iff (s : Array UInt64) (hs : s.size < 2 ^ 64) :
    layout1 s = true ↔ Layout1 s := by
  simp only [layout1, Layout1, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, isDigit_iff,
    framed_iff s 49 hs, allDigits_spec s 54 5 (by decide), UInt64.reduceToNat, and_assoc,
    or_assoc]

theorem layout2_iff (s : Array UInt64) (hs : s.size < 2 ^ 64) :
    layout2 s = true ↔ Layout2 s := by
  simp only [layout2, Layout2, Bool.and_eq_true, beq_iff_eq, framed_iff s 50 hs, padded2_iff,
    padded3_iff, allDigits_spec s 12 4 (by decide), allDigits_spec s 21 4 (by decide),
    allDigits_spec s 26 7 (by decide), allDigits_spec s 38 4 (by decide),
    allDigits_spec s 47 4 (by decide), allDigits_spec s 55 8 (by decide), UInt64.reduceToNat,
    and_assoc]

theorem sameObject_iff (s1 s2 : Array UInt64) : sameObject s1 s2 = true ↔ SameObject s1 s2 := by
  simp only [sameObject, SameObject, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- **The reader accepts exactly the lines of the layout.** -/
theorem read_status (s1 s2 : Array UInt64) (h1 : s1.size < 2 ^ 64) (h2 : s2.size < 2 ^ 64) :
    (read s1 s2).status = 0 ↔ WellFormed s1 s2 := by
  have hw : (layout1 s1 && layout2 s2 && sameObject s1 s2) = true ↔ WellFormed s1 s2 := by
    simp only [WellFormed, Bool.and_eq_true, layout1_iff s1 h1, layout2_iff s2 h2,
      sameObject_iff, and_assoc]
  unfold read
  by_cases h : (layout1 s1 && layout2 s2 && sameObject s1 s2) = true
  · simp only [h, ite_true]
    exact ⟨fun _ => hw.mp h, fun _ => trivial⟩
  · simp only [h, Bool.false_eq_true, ite_false]
    exact ⟨fun h9 => absurd h9 (by decide), fun w => absurd (hw.mpr w) h⟩

theorem angle_encloses (s : Array UInt64) (start : UInt64) (hs : start.toNat + 8 < 2 ^ 64) :
    Encloses (angle s start) (angleValue s start.toNat) := by
  unfold angle angleValue
  obtain ⟨a1, a2⟩ := fieldNat_spec s start 3 (by decide)
    (by simp only [UInt64.reduceToNat]; omega)
  have h4 : (start + 4).toNat = start.toNat + 4 := index_toNat start 4 (by omega)
  obtain ⟨b1, b2⟩ := fieldNat_spec s (start + 4) 4 (by decide)
    (by rw [h4]; simp only [UInt64.reduceToNat]; omega)
  rw [h4] at b1 b2
  simp only [UInt64.reduceToNat] at a1 a2 b1 b2
  have e : (fieldNat s start 3 * 10000 + fieldNat s (start + 4) 4).toNat =
      value s start.toNat 3 * 10000 + value s (start.toNat + 4) 4 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, a1, b1]
    simp only [UInt64.reduceToNat]
    omega
  have h := scaled_encloses (fieldNat s start 3 * 10000 + fieldNat s (start + 4) 4) 4
    (by rw [e]; omega) (by decide)
  rw [e] at h
  simpa only [UInt64.reduceToNat] using h

theorem dragTerm_encloses (s : Array UInt64) : Encloses (dragTerm s) (dragValue s) := by
  simp only [dragTerm, dragValue]
  obtain ⟨m1, m2⟩ := fieldNat_spec s 54 5 (by decide) (by decide)
  simp only [UInt64.reduceToNat] at m1 m2
  have hx := digitOf_toNat (byteAt s 60)
  have hx9 := digitValue_le (byteAt s 60)
  have magnitude : Encloses
      (if byteAt s 59 == 45 then scaled (fieldNat s 54 5) (5 + digitOf (byteAt s 60))
        else if digitOf (byteAt s 60) ≤ 5 then scaled (fieldNat s 54 5) (5 - digitOf (byteAt s 60))
        else ofInt (fieldNat s 54 5 * pow10 (digitOf (byteAt s 60) - 5)).toInt64)
      (if byteAt s 59 = 45 then ((value s 54 5 : ℕ) : ℝ) / 10 ^ (5 + digitValue (byteAt s 60))
        else ((value s 54 5 : ℕ) : ℝ) * 10 ^ digitValue (byteAt s 60) / 10 ^ 5) := by
    by_cases h : byteAt s 59 = 45
    · simp only [h, beq_self_eq_true, ite_true]
      have hk : (5 + digitOf (byteAt s 60)).toNat = 5 + digitValue (byteAt s 60) := by
        rw [UInt64.toNat_add, hx]
        simp only [UInt64.reduceToNat]
        omega
      have e := scaled_encloses (fieldNat s 54 5) (5 + digitOf (byteAt s 60))
        (by rw [m1]; omega) (by rw [hk]; omega)
      rwa [hk, m1] at e
    · have hb : (byteAt s 59 == 45) = false := beq_eq_false_iff_ne.mpr h
      simp only [hb, h, Bool.false_eq_true, ite_false]
      by_cases hle : digitOf (byteAt s 60) ≤ 5
      · simp only [hle, ite_true]
        have hn : digitValue (byteAt s 60) ≤ 5 := by
          have := UInt64.le_iff_toNat_le.mp hle
          rw [hx] at this
          simpa only [UInt64.reduceToNat] using this
        have hk : (5 - digitOf (byteAt s 60)).toNat = 5 - digitValue (byteAt s 60) := by
          rw [UInt64.toNat_sub_of_le _ _ hle, hx]
          rfl
        have e := scaled_encloses (fieldNat s 54 5) (5 - digitOf (byteAt s 60))
          (by rw [m1]; omega) (by rw [hk]; omega)
        rw [hk, m1] at e
        have q : ((value s 54 5 : ℕ) : ℝ) * 10 ^ digitValue (byteAt s 60) / 10 ^ 5 =
            ((value s 54 5 : ℕ) : ℝ) / 10 ^ (5 - digitValue (byteAt s 60)) := by
          have p : (10 : ℝ) ^ 5 =
              10 ^ (5 - digitValue (byteAt s 60)) * 10 ^ digitValue (byteAt s 60) := by
            rw [← pow_add]
            congr 1
            omega
          rw [p]
          field_simp
        rwa [q]
      · simp only [hle, ite_false]
        have hn : 5 < digitValue (byteAt s 60) := by
          have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
          rw [hx] at this
          simpa only [UInt64.reduceToNat] using this
        have h5 : (5 : UInt64) ≤ digitOf (byteAt s 60) := by
          rw [UInt64.le_iff_toNat_le, hx]
          simp only [UInt64.reduceToNat]
          omega
        have hk : (digitOf (byteAt s 60) - 5).toNat = digitValue (byteAt s 60) - 5 := by
          rw [UInt64.toNat_sub_of_le _ _ h5, hx]
          rfl
        have hp := pow10_spec (digitOf (byteAt s 60) - 5) (by rw [hk]; omega)
        rw [hk] at hp
        have h4 : 10 ^ (digitValue (byteAt s 60) - 5) ≤ 10 ^ 4 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have e : (fieldNat s 54 5 * pow10 (digitOf (byteAt s 60) - 5)).toNat =
            value s 54 5 * 10 ^ (digitValue (byteAt s 60) - 5) := by
          rw [UInt64.toNat_mul, m1, hp]
          have : value s 54 5 * 10 ^ (digitValue (byteAt s 60) - 5) < 100000 * 10 ^ 4 :=
            Nat.mul_lt_mul_of_lt_of_le m2 h4 (by positivity)
          omega
        have bound : value s 54 5 * 10 ^ (digitValue (byteAt s 60) - 5) < 100000 * 10 ^ 4 :=
          Nat.mul_lt_mul_of_lt_of_le m2 h4 (by positivity)
        refine encloses_ofInt'
          (m := ((value s 54 5 * 10 ^ (digitValue (byteAt s 60) - 5) : ℕ) : ℤ)) ?_ ?_ ?_
        · rw [Signed64Value.toInt_toInt64, e, ite_eq_left (by omega)]
        · rw [Int.natAbs_natCast]; omega
        · push_cast
          have p : (10 : ℝ) ^ digitValue (byteAt s 60) =
              10 ^ (digitValue (byteAt s 60) - 5) * 10 ^ 5 := by
            rw [← pow_add]
            congr 1
            omega
          rw [p]
          field_simp
  by_cases hs : byteAt s 53 = 45
  · simp only [hs, beq_self_eq_true, ite_true]
    exact encloses_neg magnitude
  · have hb : (byteAt s 53 == 45) = false := beq_eq_false_iff_ne.mpr hs
    simp only [hb, hs, Bool.false_eq_true, ite_false]
    exact magnitude

/-- **The intervals of an accepted element set contain its decimal values.** -/
theorem read_encloses (s1 s2 : Array UInt64) (h : (read s1 s2).status = 0) :
    Input (read s1 s2).n (read s1 s2).e (read s1 s2).incl (read s1 s2).node (read s1 s2).argp
      (read s1 s2).m (read s1 s2).bstar (elements s1 s2) := by
  unfold read at h ⊢
  by_cases hc : (layout1 s1 && layout2 s2 && sameObject s1 s2) = true
  · simp only [hc, ite_true]
    refine ⟨?_, ?_, angle_encloses s2 8 (by decide), angle_encloses s2 17 (by decide),
      angle_encloses s2 34 (by decide), angle_encloses s2 43 (by decide), dragTerm_encloses s1⟩
    · obtain ⟨a1, a2⟩ := fieldNat_spec s2 52 2 (by decide) (by decide)
      obtain ⟨b1, b2⟩ := fieldNat_spec s2 55 8 (by decide) (by decide)
      simp only [UInt64.reduceToNat] at a1 a2 b1 b2
      have e : (fieldNat s2 52 2 * 100000000 + fieldNat s2 55 8).toNat =
          value s2 52 2 * 100000000 + value s2 55 8 := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, a1, b1]
        simp only [UInt64.reduceToNat]
        omega
      have q := scaled_encloses (fieldNat s2 52 2 * 100000000 + fieldNat s2 55 8) 8
        (by rw [e]; omega) (by decide)
      rw [e] at q
      simpa only [UInt64.reduceToNat, elements] using q
    · obtain ⟨a1, a2⟩ := fieldNat_spec s2 26 7 (by decide) (by decide)
      simp only [UInt64.reduceToNat] at a1 a2
      have q := scaled_encloses (fieldNat s2 26 7) 7 (by rw [a1]; omega) (by decide)
      rw [a1] at q
      simp only [UInt64.reduceToNat] at q
      show Encloses (clamp (scaled (fieldNat s2 26 7) 7) 0.0 1.0) (((value s2 26 7 : ℕ) : ℝ) / 10 ^ 7)
      intro hc
      obtain ⟨sa, f⟩ := clamp_sound hc
      have hlt : ((value s2 26 7 : ℕ) : ℝ) < 10 ^ 7 := by exact_mod_cast a2
      refine f _ (q sa) ?_ ?_
      · rw [zero_lit_value.2]; positivity
      · rw [one_value.2]
        rw [div_le_one (by positivity)]
        exact hlt.le
  · simp only [hc, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem read_values (s1 s2 : Array UInt64) :
    (read s1 s2).status = 0 ∨ (read s1 s2).status = 10 := by
  unfold read
  split_ifs <;> simp

variable {logTab expTab : Array UInt64} {s1 s2 : Array UInt64} {t : Interval} {t' : ℝ}

/-- For lines whose result has status 0 or 6, the lines have the layout, and the intervals
contain the position and the velocity of the model for their element set. -/
theorem propagate_sound (h1 : s1.size < 2 ^ 64) (h2 : s2.size < 2 ^ 64) (ht : Encloses t t')
    (hs : (propagateWith Trig.invPi Trig.halfPi logTab expTab s1 s2 t).status = 0 ∨
      (propagateWith Trig.invPi Trig.halfPi logTab expTab s1 s2 t).status = 6) :
    WellFormed s1 s2 ∧
      Inside (propagateWith Trig.invPi Trig.halfPi logTab expTab s1 s2 t) (elements s1 s2)
        t' := by
  simp only [propagateWith] at hs ⊢
  by_cases hf : ((read s1 s2).status == 0) = true
  · simp only [hf, ite_true] at hs ⊢
    have h0 := beq_iff_eq.mp hf
    exact ⟨(read_status s1 s2 h1 h2).mp h0, sgp4Box_sound (read_encloses s1 s2 h0) ht hs⟩
  · simp only [hf, Bool.false_eq_true, ite_false] at hs
    have h0 : ¬(read s1 s2).status = 0 := fun h => hf (beq_iff_eq.mpr h)
    have h9 : (read s1 s2).status = 10 := (read_values s1 s2).resolve_left h0
    have hn : (noBox (read s1 s2).status).status = 10 := h9
    rw [hn] at hs
    rcases hs with h | h <;> exact absurd h (by decide)

/-- For lines whose result has a status other than 7 and 10, the lines have the layout, and the
status is the model's status for their element set. -/
theorem propagate_status (h1 : s1.size < 2 ^ 64) (h2 : s2.size < 2 ^ 64) (ht : Encloses t t')
    {k : UInt64} (hk : (propagateWith Trig.invPi Trig.halfPi logTab expTab s1 s2 t).status = k)
    (hs : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 9) :
    WellFormed s1 s2 ∧ Model.status (elements s1 s2) t' = k := by
  simp only [propagateWith] at hk
  by_cases hf : ((read s1 s2).status == 0) = true
  · simp only [hf, ite_true] at hk
    have h0 := beq_iff_eq.mp hf
    exact ⟨(read_status s1 s2 h1 h2).mp h0, status_sound (read_encloses s1 s2 h0) ht hk hs⟩
  · simp only [hf, Bool.false_eq_true, ite_false] at hk
    have h0 : ¬(read s1 s2).status = 0 := fun h => hf (beq_iff_eq.mpr h)
    have h9 : (read s1 s2).status = 10 := (read_values s1 s2).resolve_left h0
    have hn : (noBox (read s1 s2).status).status = 10 := h9
    rw [hn] at hk
    rw [← hk] at hs
    rcases hs with h | h | h | h | h | h | h <;> exact absurd h (by decide)

end Demos.Sgp4.Tle
