prelude

theorem implicationComposition :
    (p q r : Prop) → (q → r) → (p → q) → p → r :=
  fun p q r f g hp => f (g hp)
