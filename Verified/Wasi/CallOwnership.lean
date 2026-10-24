import Verified.Wasi.CallArguments

namespace Verified.Wasi

theorem EffectSig.placeArgs_facts {S : List Sig} {context : List Ty}
    (signature : EffectSig)
    (args : (i : Fin signature.params.length) → Expr S context (signature.params.get i))
    (valid : signature.placeArgs args = true) :
    (∀ i, (signature.params.get i).scalar = false → (args i).isPlace = true) ∧
    (∀ i : Fin signature.params.length, signature.mode i = .owned → ∃ x, args i = .var x) ∧
    (∀ i, (args i).placeArgs = true) := by
  simp only [EffectSig.placeArgs, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at valid
  obtain ⟨⟨places, variableArgs⟩, nested⟩ := valid
  refine ⟨?_, ?_, ?_⟩
  · intro i scalar
    cases place : (args i).isPlace with
    | true => rfl
    | false =>
        have selected := le_argsAny (fun j => !(signature.params.get j).scalar &&
          !(args j).isPlace) i (by rw [scalar, place]; rfl)
        rw [places] at selected
        exact nomatch selected
  · intro i owned
    apply Expr.exists_var
    cases variableIndex : (args i).varIndex?.isNone with
    | false => rfl
    | true =>
        have selected := le_argsAny (fun j => signature.mode j == .owned &&
          (args j).varIndex?.isNone) i (by
            simp only [owned, beq_self_eq_true, variableIndex, Bool.and_self])
        rw [variableArgs] at selected
        exact nomatch selected
  · intro i
    cases valid : (args i).placeArgs with
    | true => rfl
    | false =>
        have selected := le_argsAny (fun j => !(args j).placeArgs) i (by rw [valid]; rfl)
        rw [nested] at selected
        exact nomatch selected

theorem EffectSig.kept_owned {S : List Sig} {context : List Ty}
    (signature : EffectSig) (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr S context (signature.params.get i))
    (variableArgs : ∀ i : Fin signature.params.length, signature.mode i = .owned →
      ∃ x, args i = .var x) :
    ∀ i : Fin signature.params.length, signature.mode i = .owned →
      ∃ x : Var context (signature.params.get i), args i = .var x ∧
        (((live x.index || argsAny fun j => (args j).uses x.index) &&
            !(argsAny fun j => signature.callMoves slots live args j &&
              (args j).uses x.index)) = false →
          (slots.getD x.index default).mode = .owned ∧
          ∀ j, j ≠ i → (signature.params.get j).scalar = false →
            (args j).uses x.index = false) := by
  intro i owned
  obtain ⟨x, expression⟩ := variableArgs i owned
  refine ⟨x, expression, fun dead => ?_⟩
  have used : (args i).uses x.index = true := by rw [expression]; simp only [Expr.uses, beq_self_eq_true]
  have anyUsed : (argsAny fun j => (args j).uses x.index) = true := le_argsAny _ i used
  simp only [anyUsed, Bool.or_true, Bool.true_and, Bool.not_eq_false'] at dead
  obtain ⟨j, _, _, _, _, sourceOwned, _, otherArgs⟩ := signature.callMoves_moved slots live args variableArgs _ dead
  have same : j = i := by
    by_contra different
    have unused := otherArgs i (Ne.symm different) (paramMode_owned owned)
    rw [used] at unused
    exact nomatch unused
  subst j
  exact ⟨sourceOwned, otherArgs⟩

theorem EffectSig.live_kept {S : List Sig} {context : List Ty}
    (signature : EffectSig) (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr S context (signature.params.get i))
    (variableArgs : ∀ i : Fin signature.params.length, signature.mode i = .owned →
      ∃ x, args i = .var x) (index : Nat) (retained : live index = true) :
    ((live index || argsAny fun j => (args j).uses index) &&
      !(argsAny fun j => signature.callMoves slots live args j && (args j).uses index)) = true := by
  have notMoved : (argsAny fun j => signature.callMoves slots live args j &&
      (args j).uses index) = false := by
    cases moved : argsAny fun j => signature.callMoves slots live args j && (args j).uses index with
    | false => rfl
    | true =>
        obtain ⟨_, _, _, _, _, _, dead, _⟩ := signature.callMoves_moved slots live args variableArgs _ moved
        rw [retained] at dead
        exact nomatch dead
  simp only [retained, notMoved, Bool.true_or, Bool.not_false, Bool.and_self]

end Verified.Wasi
