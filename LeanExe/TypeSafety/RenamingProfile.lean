import LeanExe.TypeSafety.Renaming
import LeanExe.TypeSafety.Profile

/-!
# Renaming preserves syntactic relevance

Free occurrences follow the existential image of an arbitrary index mapping.
The map need not be injective: several free variables may merge, while lifting
protects all locally bound variables. Consequently admission is unchanged.

Preservation of `parametersUsed` applies only to a prefix protected by lifting.
It does not make newly inserted function parameters used, establish a theorem
about changed programs/signatures, or assert an operational correspondence.
-/

namespace LeanExe.TypeSafety
namespace Renaming

/-- Lifting fixes every index in the newly introduced prefix. -/
theorem liftN_prefix (mapping : Renaming) (bounded : index < count) :
    liftN count mapping index = index := by
  induction count generalizing index with
  | zero => exact False.elim (Nat.not_lt_zero _ bounded)
  | succ count ih =>
      cases index with
      | zero => rfl
      | succ index => exact congrArg Nat.succ (ih (Nat.lt_of_succ_lt_succ bounded))

/-- Free indices are shifted past the prefix on both sides of the mapping. -/
theorem liftN_suffix (mapping : Renaming) (count index : Nat) :
    liftN count mapping (index + count) = mapping index + count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ ih

/-- A protected index has exactly one preimage, even for a noninjective map. -/
theorem liftN_preimage_prefix (mapping : Renaming) (bounded : target < count) :
    liftN count mapping source = target ↔ source = target := by
  induction count generalizing source target with
  | zero => exact False.elim (Nat.not_lt_zero _ bounded)
  | succ count ih =>
      cases source with
      | zero =>
          cases target with
          | zero => exact Iff.rfl
          | succ target => constructor <;> intro impossible <;> cases impossible
      | succ source =>
          cases target with
          | zero => constructor <;> intro impossible <;> cases impossible
          | succ target =>
              change (liftN count mapping source + 1 = target + 1) ↔ source + 1 = target + 1
              simpa only [Nat.succ.injEq] using ih (Nat.lt_of_succ_lt_succ bounded)

/-- Every preimage of a free index is itself free, with the same prefix removed. -/
theorem liftN_preimage_suffix (mapping : Renaming) (count source target : Nat) :
    liftN count mapping source = target + count ↔
      ∃ index, source = index + count ∧ mapping index = target := by
  induction count generalizing source with
  | zero =>
      constructor
      · intro mapped
        exact ⟨source, rfl, mapped⟩
      · intro witness
        obtain ⟨index, same, mapped⟩ := witness
        cases same
        exact mapped
  | succ count ih =>
      cases source with
      | zero =>
          constructor
          · intro impossible
            cases impossible
          · intro witness
            obtain ⟨index, impossible, _⟩ := witness
            cases impossible
      | succ source =>
          constructor
          · intro mapped
            obtain ⟨index, same, mapped⟩ := (ih source).mp (Nat.succ.inj mapped)
            exact ⟨index, congrArg Nat.succ same, mapped⟩
          · intro witness
            obtain ⟨index, same, mapped⟩ := witness
            exact congrArg Nat.succ ((ih source).mpr ⟨index, Nat.succ.inj same, mapped⟩)

/-- Transport an occurrence witness through a lifted free-variable mapping. -/
theorem exists_liftN_suffix (mapping : Renaming) (count target : Nat) (used : Nat → Prop) :
    (∃ source, liftN count mapping source = target + count ∧ used source) ↔
      ∃ source, mapping source = target ∧ used (source + count) := by
  constructor
  · intro witness
    obtain ⟨source, mapped, occurs⟩ := witness
    obtain ⟨index, same, originalMapped⟩ :=
      (liftN_preimage_suffix mapping count source target).mp mapped
    cases same
    exact ⟨index, originalMapped, occurs⟩
  · intro witness
    obtain ⟨source, mapped, occurs⟩ := witness
    refine ⟨source + count, ?_, occurs⟩
    rw [liftN_suffix, mapped]

/-- Disjunction transports occurrence witnesses without identifying predicate functions. -/
theorem occurrenceImage_or (mapping : Renaming) (index : Nat)
    {left right : Bool} {leftUses rightUses : Nat → Bool}
    (leftLaw : left = true ↔ ∃ source, mapping source = index ∧ leftUses source = true)
    (rightLaw : right = true ↔ ∃ source, mapping source = index ∧ rightUses source = true) :
    (left || right) = true ↔
      ∃ source, mapping source = index ∧ (leftUses source || rightUses source) = true := by
  constructor
  · intro checked
    rcases (Iff.of_eq (Bool.or_eq_true _ _)).mp checked with leftChecked | rightChecked
    · obtain ⟨source, mapped, used⟩ := leftLaw.mp leftChecked
      exact ⟨source, mapped, (Iff.of_eq (Bool.or_eq_true _ _)).mpr (.inl used)⟩
    · obtain ⟨source, mapped, used⟩ := rightLaw.mp rightChecked
      exact ⟨source, mapped, (Iff.of_eq (Bool.or_eq_true _ _)).mpr (.inr used)⟩
  · intro witness
    obtain ⟨source, mapped, used⟩ := witness
    apply (Iff.of_eq (Bool.or_eq_true _ _)).mpr
    rcases (Iff.of_eq (Bool.or_eq_true _ _)).mp used with leftUsed | rightUsed
    · exact .inl (leftLaw.mpr ⟨source, mapped, leftUsed⟩)
    · exact .inr (rightLaw.mpr ⟨source, mapped, rightUsed⟩)

theorem occurrenceImage_false (mapping : Renaming) (index : Nat) :
    false = true ↔ ∃ source, mapping source = index ∧ false = true := by
  constructor
  · intro impossible
    cases impossible
  · intro witness
    obtain ⟨_, _, impossible⟩ := witness
    exact impossible

end Renaming

mutual
/-- Free occurrences are exactly the existential image of the source occurrences. -/
theorem uses_rename_iff (mapping : Renaming) (expr : Expr) (index : Nat) :
    uses index (expr.rename mapping) = true ↔
      ∃ source, mapping source = index ∧ uses source expr = true := by
  cases expr with
  | var found =>
      -- Nat BEq is the decidable-equality test; avoid its broader LawfulBEq instance.
      change decide (mapping found = index) = true ↔
        ∃ source, mapping source = index ∧ decide (found = source) = true
      constructor
      · intro checked
        exact ⟨found, of_decide_eq_true checked, decide_eq_true rfl⟩
      · intro witness
        obtain ⟨source, mapped, same⟩ := witness
        cases of_decide_eq_true same
        exact decide_eq_true mapped
  | unit | bool _ | nat _ | word _ _ | arrayEmpty _ =>
      exact Renaming.occurrenceImage_false mapping index
  | fst value | snd value | inl _ value | inr _ value | wordOfNat _ value
  | wordToNat _ value | wordCast _ _ value | arraySize value =>
      exact uses_rename_iff mapping value index
  | pair left right | unitCase left right | natBin _ left right | natCmp _ left right
  | structEq left right | wordBin _ _ left right | wordCmp _ _ left right
  | arrayGet? left right | arrayPush? left right | arrayAppend? left right =>
      exact Renaming.occurrenceImage_or mapping index
        (uses_rename_iff mapping left index) (uses_rename_iff mapping right index)
  | ifE condition yes no =>
      exact Renaming.occurrenceImage_or mapping index
        (Renaming.occurrenceImage_or mapping index
          (uses_rename_iff mapping condition index) (uses_rename_iff mapping yes index))
        (uses_rename_iff mapping no index)
  | arraySet? array position replacement =>
      exact Renaming.occurrenceImage_or mapping index
        (Renaming.occurrenceImage_or mapping index
          (uses_rename_iff mapping array index) (uses_rename_iff mapping position index))
        (uses_rename_iff mapping replacement index)
  | letE bound body =>
      have bodyLaw := (uses_rename_iff (Renaming.lift mapping) body (index + 1)).trans
        (Renaming.exists_liftN_suffix mapping 1 index (fun source => uses source body = true))
      exact Renaming.occurrenceImage_or mapping index (uses_rename_iff mapping bound index) bodyLaw
  | split pair body =>
      have bodyLaw := (uses_rename_iff (Renaming.liftN 2 mapping) body (index + 2)).trans
        (Renaming.exists_liftN_suffix mapping 2 index (fun source => uses source body = true))
      exact Renaming.occurrenceImage_or mapping index (uses_rename_iff mapping pair index) bodyLaw
  | sumCase scrutinee left right =>
      have leftLaw := (uses_rename_iff (Renaming.lift mapping) left (index + 1)).trans
        (Renaming.exists_liftN_suffix mapping 1 index (fun source => uses source left = true))
      have rightLaw := (uses_rename_iff (Renaming.lift mapping) right (index + 1)).trans
        (Renaming.exists_liftN_suffix mapping 1 index (fun source => uses source right = true))
      exact Renaming.occurrenceImage_or mapping index
        (Renaming.occurrenceImage_or mapping index
          (uses_rename_iff mapping scrutinee index) leftLaw) rightLaw
  | natCase scrutinee zeroBody succBody =>
      have succLaw := (uses_rename_iff (Renaming.lift mapping) succBody (index + 1)).trans
        (Renaming.exists_liftN_suffix mapping 1 index (fun source => uses source succBody = true))
      exact Renaming.occurrenceImage_or mapping index
        (Renaming.occurrenceImage_or mapping index
          (uses_rename_iff mapping scrutinee index) (uses_rename_iff mapping zeroBody index)) succLaw
  | call _ arguments | dataCtor _ _ arguments => exact usesArgs_rename_iff mapping arguments index
  | dataCase _ _ scrutinee branches =>
      exact Renaming.occurrenceImage_or mapping index
        (uses_rename_iff mapping scrutinee index) (usesBranches_rename_iff mapping branches index)

theorem usesArgs_rename_iff (mapping : Renaming) (arguments : List Expr) (index : Nat) :
    usesArgs index (renameArgs mapping arguments) = true ↔
      ∃ source, mapping source = index ∧ usesArgs source arguments = true := by
  cases arguments with
  | nil => exact Renaming.occurrenceImage_false mapping index
  | cons head tail =>
      exact Renaming.occurrenceImage_or mapping index
        (uses_rename_iff mapping head index) (usesArgs_rename_iff mapping tail index)

theorem usesBranches_rename_iff (mapping : Renaming) (branches : List (Nat × Expr)) (index : Nat) :
    usesBranches index (renameBranches mapping branches) = true ↔
      ∃ source, mapping source = index ∧ usesBranches source branches = true := by
  cases branches with
  | nil => exact Renaming.occurrenceImage_false mapping index
  | cons branch rest =>
      obtain ⟨arity, body⟩ := branch
      have bodyLaw := (uses_rename_iff (Renaming.liftN arity mapping) body (index + arity)).trans
        (Renaming.exists_liftN_suffix mapping arity index (fun source => uses source body = true))
      exact Renaming.occurrenceImage_or mapping index bodyLaw
        (usesBranches_rename_iff mapping rest index)
end

/-- Boolean equality needs only equivalence of its true cases. -/
theorem Renaming.bool_eq_of_true_iff {left right : Bool}
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · cases same.mpr rfl
  · cases same.mp rfl
  · rfl

/-- Renaming free variables neither creates nor removes a protected binder's use. -/
theorem uses_rename_liftN_prefix (mapping : Renaming) (expr : Expr)
    (bounded : index < count) :
    uses index (expr.rename (Renaming.liftN count mapping)) = uses index expr := by
  apply Renaming.bool_eq_of_true_iff
  constructor
  · intro checked
    obtain ⟨source, mapped, used⟩ :=
      (uses_rename_iff (Renaming.liftN count mapping) expr index).mp checked
    have same := (Renaming.liftN_preimage_prefix mapping bounded).mp mapped
    cases same
    exact used
  · intro used
    exact (uses_rename_iff (Renaming.liftN count mapping) expr index).mpr
      ⟨index, Renaming.liftN_prefix mapping bounded, used⟩

/-- Only the already protected prefix has its parameter-use test preserved. -/
theorem parametersUsed_rename_liftN (mapping : Renaming) (expr : Expr) (count : Nat) :
    parametersUsed count (expr.rename (Renaming.liftN count mapping)) =
      parametersUsed count expr := by
  apply Renaming.bool_eq_of_true_iff
  constructor
  · intro checked
    apply parametersUsed_iff.mpr
    intro index bounded
    have used := parametersUsed_iff.mp checked index bounded
    rw [uses_rename_liftN_prefix mapping expr bounded] at used
    exact used
  · intro checked
    apply parametersUsed_iff.mpr
    intro index bounded
    rw [uses_rename_liftN_prefix mapping expr bounded]
    exact parametersUsed_iff.mp checked index bounded

mutual
/-- Internal source relevance is invariant under arbitrary free-variable mappings. -/
theorem admissible_rename (mapping : Renaming) (expr : Expr) :
    admissible (expr.rename mapping) = admissible expr := by
  cases expr with
  | var _ | unit | bool _ | nat _ | word _ _ | arrayEmpty _ | fst _ | snd _ => rfl
  | inl _ value | inr _ value | wordOfNat _ value
  | wordToNat _ value | wordCast _ _ value | arraySize value =>
      exact admissible_rename mapping value
  | pair left right | unitCase left right | natBin _ left right | natCmp _ left right
  | structEq left right | wordBin _ _ left right | wordCmp _ _ left right
  | arrayGet? left right | arrayPush? left right | arrayAppend? left right =>
      simp only [Expr.rename, admissible,
        admissible_rename mapping left, admissible_rename mapping right]
  | ifE condition yes no =>
      simp only [Expr.rename, admissible, admissible_rename mapping condition,
        admissible_rename mapping yes, admissible_rename mapping no]
  | arraySet? array index replacement =>
      simp only [Expr.rename, admissible, admissible_rename mapping array,
        admissible_rename mapping index, admissible_rename mapping replacement]
  | letE bound body =>
      have localUse : uses 0 (body.rename (Renaming.lift mapping)) = uses 0 body :=
        uses_rename_liftN_prefix mapping body (count := 1) (by decide)
      simp only [Expr.rename, admissible, admissible_rename mapping bound,
        admissible_rename (Renaming.lift mapping) body, localUse]
  | split pair body =>
      have leftUse := uses_rename_liftN_prefix mapping body (count := 2) (index := 0) (by decide)
      have rightUse := uses_rename_liftN_prefix mapping body (count := 2) (index := 1) (by decide)
      simp only [Expr.rename, admissible, admissible_rename mapping pair,
        admissible_rename (Renaming.liftN 2 mapping) body, leftUse, rightUse]
  | sumCase scrutinee left right =>
      have leftUse : uses 0 (left.rename (Renaming.lift mapping)) = uses 0 left :=
        uses_rename_liftN_prefix mapping left (count := 1) (by decide)
      have rightUse : uses 0 (right.rename (Renaming.lift mapping)) = uses 0 right :=
        uses_rename_liftN_prefix mapping right (count := 1) (by decide)
      simp only [Expr.rename, admissible, admissible_rename mapping scrutinee,
        admissible_rename (Renaming.lift mapping) left, leftUse,
        admissible_rename (Renaming.lift mapping) right, rightUse]
  | natCase scrutinee zeroBody succBody =>
      have succUse : uses 0 (succBody.rename (Renaming.lift mapping)) = uses 0 succBody :=
        uses_rename_liftN_prefix mapping succBody (count := 1) (by decide)
      simp only [Expr.rename, admissible, admissible_rename mapping scrutinee,
        admissible_rename mapping zeroBody, admissible_rename (Renaming.lift mapping) succBody,
        succUse]
  | call _ arguments | dataCtor _ _ arguments => exact admissibleArgs_rename mapping arguments
  | dataCase _ _ scrutinee branches =>
      simp only [Expr.rename, admissible, admissible_rename mapping scrutinee,
        admissibleBranches_rename mapping branches]

theorem admissibleArgs_rename (mapping : Renaming) (arguments : List Expr) :
    admissibleArgs (renameArgs mapping arguments) = admissibleArgs arguments := by
  cases arguments with
  | nil => rfl
  | cons head tail =>
      simp only [renameArgs, admissibleArgs,
        admissible_rename mapping head, admissibleArgs_rename mapping tail]

theorem admissibleBranches_rename (mapping : Renaming) (branches : List (Nat × Expr)) :
    admissibleBranches (renameBranches mapping branches) = admissibleBranches branches := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      obtain ⟨arity, body⟩ := branch
      simp only [renameBranches, admissibleBranches,
        admissible_rename (Renaming.liftN arity mapping) body,
        parametersUsed_rename_liftN mapping body arity, admissibleBranches_rename mapping rest]
end

/-- Context transport preserves both raw typing and internal source relevance. -/
theorem ProfileTyped.rename (typed : ProfileTyped declarations signatures Γ expr τ)
    (mapping : RenamingTyped Γ Γ' ρ) :
    ProfileTyped declarations signatures Γ' (expr.rename ρ) τ := by
  exact ⟨typed.1.rename mapping, (admissible_rename ρ expr).trans typed.2⟩

/-- Public inference still separately checks formation of the inserted context. -/
theorem ProfileTyped.weaken (typed : ProfileTyped declarations signatures Γ expr τ)
    (extra : Context) :
    ProfileTyped declarations signatures (extra ++ Γ)
      (expr.rename (fun index => index + extra.length)) τ :=
  typed.rename (RenamingTyped.shift Γ extra)

end LeanExe.TypeSafety
