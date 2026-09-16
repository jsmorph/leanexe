prelude

theorem implicationLet : (p : Prop) → p → p :=
  fun p hp => let unused : p := hp; hp
