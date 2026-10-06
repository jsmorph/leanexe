import Project.Smalltalk.Loops

namespace Project.Smalltalk.ValidationLoop

theorem fold_checks (check : Nat → Bool) (n : Nat) :
    Nat.fold n (fun i _ ok => ok && check i) true = true ↔ ∀ i, i < n → check i = true := by
  induction n with
  | zero => simp [Nat.fold]
  | succ n ih =>
    rw [Nat.fold_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨earlier, last⟩ i within
      by_cases same : i = n
      · subst i; exact last
      · exact earlier i (by omega)
    · intro all
      exact ⟨fun i within => all i (by omega), all n (by omega)⟩

theorem loop_checks (check : UInt64 → Bool) (count : UInt64) :
    LeanExe.loop count true (fun i ok => ok && check i) = true ↔
      ∀ i : UInt64, i < count → check i = true := by
  change Nat.fold count.toNat (fun i _ ok => ok && check i.toUInt64) true = true ↔ _
  rw [fold_checks]
  constructor
  · intro all i within
    have checked := all i.toNat (UInt64.lt_iff_toNat_lt.mp within)
    simpa only [UInt64.ofNat_toNat] using checked
  · intro all i within
    have size : i < UInt64.size := Nat.lt_trans within count.toNat_lt_size
    exact all i.toUInt64 (UInt64.lt_iff_toNat_lt.mpr (by rw [UInt64.toNat_ofNat_of_lt' size]; exact within))

end Project.Smalltalk.ValidationLoop
