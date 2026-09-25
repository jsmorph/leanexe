import Project.RunningSum.Arithmetic

namespace Project.RunningSum

theorem magnitude_lt_pow (bytes : ByteArray) (h : AsciiDigits bytes) :
    magnitude bytes < 10 ^ bytes.size := lowValue_lt bytes h bytes.size

theorem magnitude_ge_pow (bytes : ByteArray) (h : Canonical bytes) (hn : 0 < bytes.size) :
    10 ^ (bytes.size - 1) ≤ magnitude bytes := by
  have hd : 1 ≤ digit bytes (bytes.size - 1) := by
    rcases h.2 with hz | hp
    · omega
    · simp only [digit, show bytes.size - 1 < bytes.size by omega, ite_true]
      rw [show bytes.size - 1 - (bytes.size - 1) = 0 by omega]
      omega
  have he : bytes.size = (bytes.size - 1) + 1 := by omega
  unfold magnitude
  rw [he, lowValue]
  simp only [Nat.add_sub_cancel]
  have hp : 0 < 10 ^ (bytes.size - 1) := by positivity
  nlinarith

theorem magnitude_lt_of_size (a b : ByteArray) (ha : Canonical a) (hb : Canonical b)
    (hs : a.size < b.size) : magnitude a < magnitude b := by
  have hupper := magnitude_lt_pow a ha.1
  have hlower := magnitude_ge_pow b hb (by omega)
  have hp : 10 ^ a.size ≤ 10 ^ (b.size - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem high_digits_equal (a b : ByteArray) (n m : Nat) (hn : n ≤ m)
    (h : ∀ i, n ≤ i → i < m → digit a i = digit b i) :
    lowValue a m + lowValue b n = lowValue b m + lowValue a n := by
  induction m with
  | zero =>
    have he : n = 0 := by omega
    simp [he, lowValue]
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n
      omega
    · have hp := ih (by omega) (fun i hi him => h i hi (by omega))
      have hd := h m (by omega) (by omega)
      simp only [lowValue, hd]
      omega

theorem magnitude_eq_of_bytes (a b : ByteArray) (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : magnitude a = magnitude b := by
  have he := high_digits_equal a b 0 a.size (by omega) (by
    intro i hi him
    simp only [digit, him, ← hs, ite_true]
    rw [h _ (by omega)])
  simpa [lowValue, magnitude, hs] using he

theorem magnitude_lt_of_first (a b : ByteArray) (ha : AsciiDigits a) (hb : AsciiDigits b)
    (hs : a.size = b.size) (k : Nat) (hk : k < a.size)
    (hprefix : ∀ i, i < k → a[i]! = b[i]!) (hlt : a[k]!.toNat < b[k]!.toNat) :
    magnitude a < magnitude b := by
  let n := a.size - 1 - k
  have hn : n < a.size := by dsimp [n]; omega
  have hindex : a.size - 1 - n = k := by dsimp [n]; omega
  have hda : digit a n = a[k]!.toNat - 48 := by simp [digit, hn, hindex]
  have hdb : digit b n = b[k]!.toNat - 48 := by simp [digit, ← hs, hn, hindex]
  have hba := ha k hk
  have hbb := hb k (by omega)
  have hdiff : digit a n + 1 ≤ digit b n := by rw [hda, hdb]; omega
  have hla := lowValue_lt a ha n
  have hlb := lowValue_lt b hb n
  have hp : 0 < 10 ^ n := by positivity
  have hlow : lowValue a (n + 1) < lowValue b (n + 1) := by
    simp only [lowValue]
    nlinarith
  have he := high_digits_equal a b (n + 1) a.size (by omega) (by
    intro i hi him
    have hk' : a.size - 1 - i < k := by dsimp [n] at hi; omega
    simp only [digit, him, ← hs, ite_true]
    rw [hprefix _ hk'])
  unfold magnitude
  rw [← hs]
  omega

theorem first_difference_lt (a b : ByteArray) (ha : AsciiDigits a) (hb : AsciiDigits b)
    (hs : a.size = b.size) (k : Nat) (hk : k < a.size)
    (hprefix : ∀ i, i < k → a[i]! = b[i]!) (hne : a[k]! ≠ b[k]!) :
    (magnitude a < magnitude b) ↔ a[k]! < b[k]! := by
  constructor
  · intro hlt
    by_contra hnot
    have hne' : a[k]!.toNat ≠ b[k]!.toNat := fun h => hne (UInt8.toNat.inj h)
    have hrev : b[k]!.toNat < a[k]!.toNat := by
      rw [UInt8.lt_iff_toNat_lt] at hnot
      omega
    have := magnitude_lt_of_first b a hb ha hs.symm k (by omega)
      (fun i hi => (hprefix i hi).symm) hrev
    omega
  · intro hlt
    exact magnitude_lt_of_first a b ha hb hs k hk hprefix (UInt8.lt_iff_toNat_lt.mp hlt)

end Project.RunningSum
