import Library.Numerics.Arithmetic.Uscale.Compiled
import Library.Numerics.Arithmetic.Uscale.UscaleDiv
import Verified.Master

/-! The master theorems of `Uscale`.  Each states the value of an array of limbs, least significant
first, as `Nat.ofDigits (2 ^ 32)` of its elements, which `val_eq` proves equal to
`UscaleTheorem.val` of the proofs.  In the docstrings, the name of an array also denotes its
value. -/

namespace Library.Numerics.Arithmetic.Uscale

open LeanExe.Pipeline (Moved)

theorem val_eq (a : Array UInt64) :
    UscaleTheorem.val a = Nat.ofDigits (2 ^ 32) (a.toList.map UInt64.toNat) := by
  unfold UscaleTheorem.val
  induction a.toList with
  | nil => rfl
  | cons x xs ih => simp [UscaleTheorem.valL, Nat.ofDigits_cons, ih]

theorem mulSmall_export :
    ({ name := "mulSmall", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem shl_export :
    ({ name := "shl", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem le_export :
    ({ name := "le", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sub_export :
    ({ name := "sub", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem wordBits_export :
    ({ name := "wordBits", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem bitLen_export :
    ({ name := "bitLen", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem divBits_export :
    ({ name := "divBits", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem scaledQuot_export :
    ({ name := "scaledQuot", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mulPow10_export :
    ({ name := "mulPow10", funcIdx := 14 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem pow10_export :
    ({ name := "pow10", funcIdx := 15 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `mulSmall`, called on an array `a` of limbs below `2 ^ 32` and words `m` and `c`
below `2 ^ 32`, returns an array of `a.size + 1` limbs below `2 ^ 32` whose value is
`a · m + c`. -/
theorem mulSmall_master :
    Verified.Master compiled.module compiled.tables "mulSmall" compiled.mulSmall.bound
      (fun x : Array UInt64 × UInt64 × UInt64 =>
        (∀ v ∈ x.1.toList, v.toNat < 2 ^ 32) ∧ x.2.1.toNat < 2 ^ 32 ∧ x.2.2.toNat < 2 ^ 32)
      (fun x (y : Array UInt64) => (∀ v ∈ y.toList, v.toNat < 2 ^ 32) ∧
        Nat.ofDigits (2 ^ 32) (y.toList.map UInt64.toNat) =
          Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat) * x.2.1.toNat + x.2.2.toNat ∧
        y.size = x.1.size + 1) :=
  .of_trapFree (.ofA compiled.mulSmall.trapFree) nofun mulSmall_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ ⟨ha, hm, hc⟩ => by
      obtain ⟨h1, h2, h3⟩ :=
        UscaleTheorem.mulSmall_spec x.1 x.2.1 x.2.2 ha hxs.values.size_lt hm hc
      simp only [val_eq] at h2
      exact ⟨h1, h2, h3⟩

#print axioms mulSmall_master

/-- The export `shl`, called on an array `a` of fewer than `2 ^ 32` limbs below `2 ^ 32` and a
word `k`, returns an array of `a.size + 1 + k / 32` limbs below `2 ^ 32` whose value is
`a · 2 ^ k`. -/
theorem shl_master :
    Verified.Master compiled.module compiled.tables "shl" compiled.shl.bound
      (fun x : Array UInt64 × UInt64 =>
        (∀ v ∈ x.1.toList, v.toNat < 2 ^ 32) ∧ x.1.size < 2 ^ 32)
      (fun x (y : Array UInt64) => (∀ v ∈ y.toList, v.toNat < 2 ^ 32) ∧
        Nat.ofDigits (2 ^ 32) (y.toList.map UInt64.toNat) =
          Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat) * 2 ^ x.2.toNat ∧
        y.size = x.1.size + 1 + x.2.toNat / 32) :=
  .of_trapFree (.ofA compiled.shl.trapFree) nofun shl_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨ha, hs⟩ => by
      obtain ⟨h1, h2, h3⟩ := UscaleTheorem.shl_spec x.1 x.2 ha hs
      simp only [val_eq] at h2
      exact ⟨h1, h2, h3⟩

#print axioms shl_master

/-- The export `le`, called on arrays `a` and `b` of fewer than `2 ^ 32` limbs below `2 ^ 32`,
returns whether `a ≤ b`. -/
theorem le_master :
    Verified.Master compiled.module compiled.tables "le" compiled.le.bound
      (fun x : Array UInt64 × Array UInt64 =>
        (∀ v ∈ x.1.toList, v.toNat < 2 ^ 32) ∧ (∀ v ∈ x.2.toList, v.toNat < 2 ^ 32) ∧
          x.1.size < 2 ^ 32 ∧ x.2.size < 2 ^ 32)
      (fun x (y : Bool) => y = decide (Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat) ≤
        Nat.ofDigits (2 ^ 32) (x.2.toList.map UInt64.toNat))) :=
  .of_trapFree (.ofA compiled.le.trapFree) nofun le_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨ha, hb, hsa, hsb⟩ => by
      rw [← val_eq, ← val_eq]
      exact UscaleTheorem.le_spec x.1 x.2 ha hb hsa hsb

#print axioms le_master

/-- The export `sub`, called on arrays `a` and `b` of limbs below `2 ^ 32`, with fewer than
`2 ^ 32` limbs in `a` and `b ≤ a`, returns an array of `a.size` limbs below `2 ^ 32` whose value
is `a - b`. -/
theorem sub_master :
    Verified.Master compiled.module compiled.tables "sub" compiled.sub.bound
      (fun x : Array UInt64 × Array UInt64 =>
        (∀ v ∈ x.1.toList, v.toNat < 2 ^ 32) ∧ (∀ v ∈ x.2.toList, v.toNat < 2 ^ 32) ∧
          x.1.size < 2 ^ 32 ∧
          Nat.ofDigits (2 ^ 32) (x.2.toList.map UInt64.toNat) ≤
            Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat))
      (fun x (y : Array UInt64) => (∀ v ∈ y.toList, v.toNat < 2 ^ 32) ∧
        Nat.ofDigits (2 ^ 32) (y.toList.map UInt64.toNat) =
          Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat) -
            Nat.ofDigits (2 ^ 32) (x.2.toList.map UInt64.toNat) ∧
        y.size = x.1.size) :=
  .of_trapFree (.ofA compiled.sub.trapFree) nofun sub_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, _, ⟨_, _, hbs⟩⟩ ⟨ha, hb, hs, hle⟩ => by
      rw [← val_eq, ← val_eq] at hle
      obtain ⟨h1, h2, h3⟩ :=
        UscaleTheorem.sub_spec x.1 x.2 ha hb hs hbs.values.size_lt hle
      simp only [val_eq] at h2
      exact ⟨h1, h2, h3⟩

#print axioms sub_master

/-- The export `wordBits`, called on a word `x`, returns the number of bits of `x`, `Nat.size`. -/
theorem wordBits_master :
    Verified.Master compiled.module compiled.tables "wordBits" compiled.wordBits.bound
      (fun _ => True) (fun (x : UInt64) (y : UInt64) => y.toNat = Nat.size x.toNat) :=
  .of_trapFree (.ofA compiled.wordBits.trapFree) nofun wordBits_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => UscaleTheorem.wordBits_spec x

#print axioms wordBits_master

/-- The export `bitLen`, called on an array `a` of fewer than `2 ^ 32` limbs below `2 ^ 32`,
returns the number of bits of `a`, `Nat.size`. -/
theorem bitLen_master :
    Verified.Master compiled.module compiled.tables "bitLen" compiled.bitLen.bound
      (fun a : Array UInt64 => (∀ v ∈ a.toList, v.toNat < 2 ^ 32) ∧ a.size < 2 ^ 32)
      (fun a (y : UInt64) =>
        y.toNat = Nat.size (Nat.ofDigits (2 ^ 32) (a.toList.map UInt64.toNat))) :=
  .of_trapFree (.ofA compiled.bitLen.trapFree) nofun bitLen_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ a _ ⟨ha, hs⟩ => by
      rw [← val_eq]
      exact UscaleTheorem.bitLen_spec a ha hs

#print axioms bitLen_master

/-- The export `divBits`, called on a moved array `n` and an array `d` of fewer than `2 ^ 31`
limbs below `2 ^ 32` and a word `bits ≤ 63`, where `0 < d` and `n < d · 2 ^ bits`, returns the
word `n / d` and an array of `n.size` limbs below `2 ^ 32` whose value is `n % d`. -/
theorem divBits_master :
    Verified.Master compiled.module compiled.tables "divBits" compiled.divBits.bound
      (fun x : Moved (Array UInt64) × Array UInt64 × UInt64 =>
        (∀ v ∈ x.1.val.toList, v.toNat < 2 ^ 32) ∧ (∀ v ∈ x.2.1.toList, v.toNat < 2 ^ 32) ∧
          x.1.val.size < 2 ^ 31 ∧ x.2.1.size < 2 ^ 31 ∧ x.2.2.toNat ≤ 63 ∧
          0 < Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) ∧
          Nat.ofDigits (2 ^ 32) (x.1.val.toList.map UInt64.toNat) <
            Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) * 2 ^ x.2.2.toNat)
      (fun x (y : UInt64 × Array UInt64) =>
        y.1.toNat = Nat.ofDigits (2 ^ 32) (x.1.val.toList.map UInt64.toNat) /
          Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) ∧
        (∀ v ∈ y.2.toList, v.toNat < 2 ^ 32) ∧
        Nat.ofDigits (2 ^ 32) (y.2.toList.map UInt64.toNat) =
          Nat.ofDigits (2 ^ 32) (x.1.val.toList.map UInt64.toNat) %
            Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) ∧
        y.2.size = x.1.val.size) :=
  .of_trapFree (.ofA compiled.divBits.trapFree) nofun divBits_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hn, hd, hsn, hsd, hb, hpos, hlt⟩ => by
      rw [← val_eq] at hpos
      rw [← val_eq, ← val_eq] at hlt
      obtain ⟨h1, h2, h3, h4⟩ :=
        UscaleTheorem.divBits_spec x.1.val x.2.1 x.2.2 hn hd hsn hsd hb hpos hlt
      simp only [val_eq] at h1 h3
      exact ⟨h1, h2, h3, h4⟩

#print axioms divBits_master

/-- The export `scaledQuot`, called on arrays `n` and `d` of fewer than `2 ^ 30` limbs below
`2 ^ 32` and words `sn`, `sd` below `2 ^ 30` and `bits ≤ 63`, where `0 < d` and
`n · 2 ^ sn < d · 2 ^ sd · 2 ^ bits`, returns the word `⌊n · 2 ^ sn / (d · 2 ^ sd)⌋` and whether
that division leaves a remainder. -/
theorem scaledQuot_master :
    Verified.Master compiled.module compiled.tables "scaledQuot" compiled.scaledQuot.bound
      (fun x : Array UInt64 × Array UInt64 × UInt64 × UInt64 × UInt64 =>
        (∀ v ∈ x.1.toList, v.toNat < 2 ^ 32) ∧ (∀ v ∈ x.2.1.toList, v.toNat < 2 ^ 32) ∧
          x.1.size < 2 ^ 30 ∧ x.2.1.size < 2 ^ 30 ∧ x.2.2.1.toNat < 2 ^ 30 ∧
          x.2.2.2.1.toNat < 2 ^ 30 ∧ x.2.2.2.2.toNat ≤ 63 ∧
          0 < Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) ∧
          Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat) * 2 ^ x.2.2.1.toNat <
            Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) * 2 ^ x.2.2.2.1.toNat *
              2 ^ x.2.2.2.2.toNat)
      (fun x (y : UInt64 × Bool) =>
        y.1.toNat = Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat) * 2 ^ x.2.2.1.toNat /
          (Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) * 2 ^ x.2.2.2.1.toNat) ∧
        y.2 = decide (Nat.ofDigits (2 ^ 32) (x.1.toList.map UInt64.toNat) * 2 ^ x.2.2.1.toNat %
          (Nat.ofDigits (2 ^ 32) (x.2.1.toList.map UInt64.toNat) * 2 ^ x.2.2.2.1.toNat) ≠ 0)) :=
  .of_trapFree (.ofA compiled.scaledQuot.trapFree) nofun scaledQuot_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hn, hd, hsn, hsd, hsn', hsd', hb, hpos, hlt⟩ => by
      rw [← val_eq] at hpos
      rw [← val_eq, ← val_eq] at hlt
      rw [← val_eq, ← val_eq]
      exact UscaleTheorem.scaledQuot_spec x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 hn hd hsn hsd
        hsn' hsd' hb hpos hlt

#print axioms scaledQuot_master

/-- The export `mulPow10`, called on a moved array `a` of fewer than `2 ^ 31` limbs below
`2 ^ 32` and a word `k` below `2 ^ 20`, returns an array of `a.size + k / 9 + 1` limbs below
`2 ^ 32` whose value is `a · 10 ^ k`. -/
theorem mulPow10_master :
    Verified.Master compiled.module compiled.tables "mulPow10" compiled.mulPow10.bound
      (fun x : Moved (Array UInt64) × UInt64 =>
        (∀ v ∈ x.1.val.toList, v.toNat < 2 ^ 32) ∧ x.1.val.size < 2 ^ 31 ∧ x.2.toNat < 2 ^ 20)
      (fun x (y : Array UInt64) => (∀ v ∈ y.toList, v.toNat < 2 ^ 32) ∧
        Nat.ofDigits (2 ^ 32) (y.toList.map UInt64.toNat) =
          Nat.ofDigits (2 ^ 32) (x.1.val.toList.map UInt64.toNat) * 10 ^ x.2.toNat ∧
        y.size = x.1.val.size + x.2.toNat / 9 + 1) :=
  .of_trapFree (.ofA compiled.mulPow10.trapFree) nofun mulPow10_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨ha, hs, hk⟩ => by
      obtain ⟨h1, h2, h3⟩ := UscaleTheorem.mulPow10_spec x.1.val x.2 ha hs hk
      simp only [val_eq] at h2
      exact ⟨h1, h2, h3⟩

#print axioms mulPow10_master

/-- The export `pow10`, called on a word `k` below `2 ^ 20`, returns an array of `k / 9 + 2`
limbs below `2 ^ 32` whose value is `10 ^ k`. -/
theorem pow10_master :
    Verified.Master compiled.module compiled.tables "pow10" compiled.pow10.bound
      (fun k : UInt64 => k.toNat < 2 ^ 20)
      (fun k (y : Array UInt64) => (∀ v ∈ y.toList, v.toNat < 2 ^ 32) ∧
        Nat.ofDigits (2 ^ 32) (y.toList.map UInt64.toNat) = 10 ^ k.toNat ∧
        y.size = k.toNat / 9 + 2) :=
  .of_trapFree (.ofA compiled.pow10.trapFree) nofun pow10_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ k _ hk => by
      obtain ⟨h1, h2, h3⟩ := UscaleTheorem.pow10_spec k hk
      simp only [val_eq] at h2
      exact ⟨h1, h2, h3⟩

#print axioms pow10_master

end Library.Numerics.Arithmetic.Uscale
