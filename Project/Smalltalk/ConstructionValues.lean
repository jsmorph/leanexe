import Project.Smalltalk.Construction

namespace Project.Smalltalk.ConstructionValues
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory

inductive Values (s : Array UInt64) (cap : Nat) : UInt64 → List UInt64 → Prop
  | nil : Values s cap 0 []
  | cons {head tail value rest} : Handle cap head → field s head 0 = 7 →
      field s head 2 = value → field s head 3 = tail → Values s cap tail rest →
      Values s cap head (value :: rest)

theorem transfer {s t : Array UInt64} {cap : Nat} {head : UInt64} {values : List UInt64}
    (original : Values s cap head values)
    (same : ∀ h, Handle cap h → field s h 0 = 7 → ∀ k : UInt64, k.toNat < 8 → field t h k = field s h k) :
    Values t cap head values := by
  induction original with
  | nil => exact .nil
  | cons handle tag value next _ ih =>
    exact .cons handle ((same _ handle tag 0 (by decide)).trans tag)
      ((same _ handle tag 2 (by decide)).trans value) ((same _ handle tag 3 (by decide)).trans next) ih

theorem prepend_values {s t : Array UInt64} {cap : Nat} {value : UInt64} {values : List UInt64}
    (effect : Construction.Effect s t cap value) (original : Values s cap (read s 19) values) :
    Values t cap (read t 19) (value :: values) := by
  have retained := transfer original (fun h handle tag k bound =>
    effect.previous h handle (by rw [tag]; decide) k bound)
  exact .cons effect.head effect.tag effect.value effect.next retained

theorem empty_iff_zero {s : Array UInt64} {cap : Nat} {head : UInt64} {values : List UInt64}
    (list : Values s cap head values) : values = [] ↔ head = 0 := by
  cases list with
  | nil => simp
  | cons handle _ _ _ _ =>
    have nonzero : head ≠ 0 := by
      intro zero
      have lower := handle.1
      rw [zero] at lower
      contradiction
    simp [nonzero]

theorem head_matches {s : Array UInt64} {cap : Nat} {head : UInt64} {values : List UInt64}
    (list : Values s cap head values) : PointerTypes.Matches s cap 7 head := by
  cases list with
  | nil => exact Or.inl rfl
  | cons handle tag _ _ _ => exact Or.inr ⟨handle, tag⟩

end Project.Smalltalk.ConstructionValues
