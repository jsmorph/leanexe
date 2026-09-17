import LeanExe.WGSL.Source

namespace LeanExe.WGSL.Source

def LocalsBound (values bounds : List Nat) : Prop :=
  ∀ (i n : Nat), bounds[i]? = some n → ∃ value, values[i]? = some value ∧ value ≤ n

theorem LocalsBound.cons {values bounds value bound}
    (h : LocalsBound values bounds) (hv : value ≤ bound) :
    LocalsBound (value :: values) (bound :: bounds) := by
  intro i n hi
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            exact ⟨value, rfl, hi ▸ hv⟩
  | succ i => exact h i n hi

theorem Index.bound_le {shape : Shape} {ranges values : List Nat} {row col bound : Nat}
    (hr : row < shape.rows) (hc : col < shape.cols) (hv : LocalsBound values ranges)
    (i : Index) (h : i.bound shape ranges = .ok bound) :
    i.eval row col values ≤ bound := by
  induction i generalizing bound with
  | lit n =>
      simp only [Index.bound] at h
      split at h <;> cases h
      exact Nat.le_refl _
  | row => cases h; simp only [Index.eval]; omega
  | col => cases h; simp only [Index.eval]; omega
  | «local» slot =>
      simp only [Index.bound] at h
      cases hg : ranges[slot]? with
      | none => simp [hg] at h
      | some n =>
          simp only [hg] at h
          cases h
          obtain ⟨v, hg, hle⟩ := hv slot bound hg
          simpa [Index.eval, hg] using hle
  | add a b ha hb =>
      cases ea : a.bound shape ranges with
      | error error => simp [Index.bound, ea, bind, Except.bind] at h
      | ok na =>
          cases eb : b.bound shape ranges with
          | error error => simp [Index.bound, ea, eb, bind, Except.bind] at h
          | ok nb =>
              simp only [Index.bound, ea, eb, Except.bind, bind, pure, Except.pure] at h
              split at h <;> cases h
              exact Nat.add_le_add (ha ea) (hb eb)
  | mul a b ha hb =>
      cases ea : a.bound shape ranges with
      | error error => simp [Index.bound, ea, bind, Except.bind] at h
      | ok na =>
          cases eb : b.bound shape ranges with
          | error error => simp [Index.bound, ea, eb, bind, Except.bind] at h
          | ok nb =>
              simp only [Index.bound, ea, eb, Except.bind, bind, pure, Except.pure] at h
              split at h <;> cases h
              exact Nat.mul_le_mul (ha ea) (hb eb)

/-- The integer operations performed by the shader, including u32 wraparound. -/
def Index.word (row col : UInt32) (locals : List UInt32) : Index → UInt32
  | .lit n => UInt32.ofNat n
  | .row => row
  | .col => col
  | .local i => locals[i]?.getD 0
  | .add a b => a.word row col locals + b.word row col locals
  | .mul a b => a.word row col locals * b.word row col locals

theorem Index.word_eq {shape : Shape} {ranges : List Nat} {values : List UInt32}
    {row col : UInt32} {bound : Nat}
    (hr : row.toNat < shape.rows) (hc : col.toNat < shape.cols)
    (hv : LocalsBound (values.map UInt32.toNat) ranges)
    (i : Index) (h : i.bound shape ranges = .ok bound) :
    (i.word row col values).toNat = i.eval row.toNat col.toNat (values.map UInt32.toNat) := by
  induction i generalizing bound with
  | lit n =>
      simp only [Index.bound] at h
      split at h <;> cases h
      simp only [Index.word, Index.eval, UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
  | row => rfl
  | col => rfl
  | «local» slot =>
      simp only [Index.word, Index.eval, List.getElem?_map]
      cases values[slot]? <;> rfl
  | add a b ha hb =>
      cases ea : a.bound shape ranges with
      | error error => simp [Index.bound, ea, bind, Except.bind] at h
      | ok na =>
          cases eb : b.bound shape ranges with
          | error error => simp [Index.bound, ea, eb, bind, Except.bind] at h
          | ok nb =>
              simp only [Index.bound, ea, eb, Except.bind, bind, pure, Except.pure] at h
              split at h <;> cases h
              have ba := a.bound_le hr hc hv ea
              have bb := b.bound_le hr hc hv eb
              simp only [Index.word, Index.eval, UInt32.toNat_add, ha ea, hb eb]
              exact Nat.mod_eq_of_lt (by omega)
  | mul a b ha hb =>
      cases ea : a.bound shape ranges with
      | error error => simp [Index.bound, ea, bind, Except.bind] at h
      | ok na =>
          cases eb : b.bound shape ranges with
          | error error => simp [Index.bound, ea, eb, bind, Except.bind] at h
          | ok nb =>
              simp only [Index.bound, ea, eb, Except.bind, bind, pure, Except.pure] at h
              split at h <;> cases h
              have hle := Nat.mul_le_mul (a.bound_le hr hc hv ea) (b.bound_le hr hc hv eb)
              simp only [Index.word, Index.eval, UInt32.toNat_mul, ha ea, hb eb]
              exact Nat.mod_eq_of_lt (by omega)

end LeanExe.WGSL.Source
