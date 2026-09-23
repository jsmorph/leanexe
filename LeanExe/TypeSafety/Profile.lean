import LeanExe.TypeSafety.Safety

/-!
# A strict profile with syntactic relevance

Admission requires each introduced binding to occur in its scope. Products are
eliminated by `split`, with both field binders used; `fst` and `snd` remain raw
core forms but are rejected here. `unitCase` eliminates Unit without introducing
a binder. Every declared function parameter must occur in its body.

Occurrence is syntactic: a use in either conditional branch suffices. This is
neither an all-path demand analysis nor a semantic necessity test. Duplication
is permitted, so the profile is not linear. These checks constrain source
admission; the runtime invariant is still the core's `StateTyped` judgment.

The Boolean checks do not replace type checking. `ProfileTyped` and
`ProfileProgramTyped` explicitly require the independent core typing judgments.
-/

namespace LeanExe.TypeSafety

mutual
/-- Whether a de Bruijn variable occurs, accounting for each nested binder. -/
def uses (index : Nat) : Expr → Bool
  | .var found => found == index
  | .unit | .bool _ | .nat _ => false
  | .letE bound body => uses index bound || uses (index + 1) body
  | .ifE condition yes no => uses index condition || uses index yes || uses index no
  | .pair left right => uses index left || uses index right
  | .fst pair | .snd pair => uses index pair
  | .split pair body => uses index pair || uses (index + 2) body
  | .unitCase scrutinee body => uses index scrutinee || uses index body
  | .inl _ payload | .inr _ payload => uses index payload
  | .sumCase scrutinee left right =>
      uses index scrutinee || uses (index + 1) left || uses (index + 1) right
  | .natBin _ left right | .natCmp _ left right => uses index left || uses index right
  | .call _ arguments => usesArgs index arguments
  | .arrayEmpty _ => false
  | .arraySize array => uses index array
  | .arrayGet? array position => uses index array || uses index position
  | .arraySet? array position replacement =>
      uses index array || uses index position || uses index replacement
  | .arrayPush? array value => uses index array || uses index value
  | .arrayAppend? left right => uses index left || uses index right
  | .dataCtor _ _ fields => usesArgs index fields
  | .dataCase _ _ scrutinee branches => uses index scrutinee || usesBranches index branches

/-- Occurrence in a finite argument list. -/
def usesArgs (index : Nat) : List Expr → Bool
  | [] => false
  | argument :: rest => uses index argument || usesArgs index rest

/-- Pattern fields precede the captured context; each explicit arity shifts outer indices. -/
def usesBranches (index : Nat) : List (Nat × Expr) → Bool
  | [] => false
  | (arity, body) :: rest => uses (index + arity) body || usesBranches index rest
end

/-- All indices in a function's parameter environment must occur in its body. -/
def parametersUsed : Nat → Expr → Bool
  | 0, _ => true
  | count + 1, body => parametersUsed count body && uses count body

mutual
/-- The decidable source restriction, separate from the expression typing rules. -/
def admissible : Expr → Bool
  | .var _ | .unit | .bool _ | .nat _ => true
  | .letE bound body => admissible bound && (admissible body && uses 0 body)
  | .ifE condition yes no => admissible condition && (admissible yes && admissible no)
  | .pair left right => admissible left && admissible right
  | .fst _ | .snd _ => false
  | .split pair body =>
      admissible pair && (admissible body && (uses 0 body && uses 1 body))
  | .unitCase scrutinee body => admissible scrutinee && admissible body
  | .inl _ payload | .inr _ payload => admissible payload
  | .sumCase scrutinee left right =>
      admissible scrutinee &&
        (admissible left && (uses 0 left && (admissible right && uses 0 right)))
  | .natBin _ left right | .natCmp _ left right => admissible left && admissible right
  | .call _ arguments => admissibleArgs arguments
  | .arrayEmpty _ => true
  | .arraySize array => admissible array
  | .arrayGet? array index => admissible array && admissible index
  | .arraySet? array index replacement =>
      admissible array && (admissible index && admissible replacement)
  | .arrayPush? array value => admissible array && admissible value
  | .arrayAppend? left right => admissible left && admissible right
  | .dataCtor _ _ fields => admissibleArgs fields
  | .dataCase _ _ scrutinee branches => admissible scrutinee && admissibleBranches branches

/-- Every argument must itself satisfy the source restriction. -/
def admissibleArgs : List Expr → Bool
  | [] => true
  | argument :: rest => admissible argument && admissibleArgs rest

/-- Every branch is admitted and every declared pattern field has a syntactic use. -/
def admissibleBranches : List (Nat × Expr) → Bool
  | [] => true
  | (arity, body) :: rest =>
      admissible body && (parametersUsed arity body && admissibleBranches rest)
end

/-- Check every body, every parameter, and exact program/signature alignment. -/
def programAdmissible : Program → Signatures → Bool
  | [], [] => true
  | body :: bodies, signature :: signatures =>
      admissible body &&
        (parametersUsed signature.params.length body && programAdmissible bodies signatures)
  | _, _ => false

def ProfileTyped (declarations : DataDecls) (signatures : Signatures)
    (Γ : Context) (expr : Expr) (τ : Ty) : Prop :=
  ExprTyped declarations signatures Γ expr τ ∧ admissible expr = true

def ProfileProgramTyped (declarations : DataDecls) (program : Program)
    (signatures : Signatures) : Prop :=
  ProgramTyped declarations program signatures ∧ programAdmissible program signatures = true

theorem usesArgs_iff : usesArgs index arguments = true ↔
    ∃ argument ∈ arguments, uses index argument = true := by
  induction arguments with
  | nil =>
      constructor
      · intro impossible
        cases impossible
      · intro witness
        obtain ⟨argument, member, _⟩ := witness
        cases member
  | cons argument rest ih =>
      constructor
      · intro checked
        -- The direct equation avoids the quotient dependency of `Bool.or_eq_true_iff`.
        rcases (Iff.of_eq (Bool.or_eq_true _ _)).mp checked with here | later
        · exact ⟨argument, .head _, here⟩
        · obtain ⟨found, member, used⟩ := ih.mp later
          exact ⟨found, .tail _ member, used⟩
      · intro witness
        obtain ⟨found, member, used⟩ := witness
        cases member with
        | head => exact (Iff.of_eq (Bool.or_eq_true _ _)).mpr (.inl used)
        | tail _ member =>
            exact (Iff.of_eq (Bool.or_eq_true _ _)).mpr (.inr (ih.mpr ⟨found, member, used⟩))

theorem usesBranches_iff : usesBranches index branches = true ↔
    ∃ branch ∈ branches, uses (index + branch.1) branch.2 = true := by
  induction branches with
  | nil =>
      constructor
      · intro impossible
        cases impossible
      · intro witness
        obtain ⟨branch, member, _⟩ := witness
        cases member
  | cons branch rest ih =>
      obtain ⟨arity, body⟩ := branch
      constructor
      · intro checked
        rcases (Iff.of_eq (Bool.or_eq_true _ _)).mp checked with here | later
        · exact ⟨_, .head _, here⟩
        · obtain ⟨found, member, used⟩ := ih.mp later
          exact ⟨found, .tail _ member, used⟩
      · intro witness
        obtain ⟨found, member, used⟩ := witness
        cases member with
        | head => exact (Iff.of_eq (Bool.or_eq_true _ _)).mpr (.inl used)
        | tail _ member =>
            exact (Iff.of_eq (Bool.or_eq_true _ _)).mpr (.inr (ih.mpr ⟨found, member, used⟩))

theorem parametersUsed_iff : parametersUsed count body = true ↔
    ∀ index, index < count → uses index body = true := by
  induction count with
  | zero =>
      constructor
      · intro _ index bounded
        exact False.elim (Nat.not_lt_zero index bounded)
      · intro _
        rfl
  | succ count ih =>
      constructor
      · intro checked index bounded
        obtain ⟨earlier, last⟩ := Bool.and_eq_true_iff.mp checked
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ bounded) with smaller | same
        · exact ih.mp earlier index smaller
        · cases same
          exact last
      · intro allUsed
        apply Bool.and_eq_true_iff.mpr
        exact ⟨ih.mpr (fun index bounded =>
          allUsed index (Nat.lt_trans bounded (Nat.lt_succ_self count))),
          allUsed count (Nat.lt_succ_self count)⟩

theorem admissible_let_iff : admissible (.letE bound body) = true ↔
    admissible bound = true ∧ admissible body = true ∧ uses 0 body = true := by
  simp [admissible, Bool.and_eq_true]

theorem admissible_split_iff : admissible (.split pair body) = true ↔
    admissible pair = true ∧ admissible body = true ∧
      uses 0 body = true ∧ uses 1 body = true := by
  simp [admissible, Bool.and_eq_true]

theorem admissible_sumCase_iff : admissible (.sumCase scrutinee left right) = true ↔
    admissible scrutinee = true ∧ admissible left = true ∧ uses 0 left = true ∧
      admissible right = true ∧ uses 0 right = true := by
  simp [admissible, Bool.and_eq_true]

theorem admissible_unitCase_iff : admissible (.unitCase scrutinee body) = true ↔
    admissible scrutinee = true ∧ admissible body = true := by
  simp [admissible, Bool.and_eq_true]

theorem admissibleArgs_iff : admissibleArgs arguments = true ↔
    ∀ argument ∈ arguments, admissible argument = true := by
  induction arguments with
  | nil =>
      constructor
      · intro _ argument member
        cases member
      · intro _
        rfl
  | cons argument rest ih =>
      constructor
      · intro checked found member
        obtain ⟨here, later⟩ := Bool.and_eq_true_iff.mp checked
        cases member with
        | head => exact here
        | tail _ member => exact ih.mp later found member
      · intro allAdmissible
        exact Bool.and_eq_true_iff.mpr
          ⟨allAdmissible argument (.head _),
            ih.mpr (fun found member => allAdmissible found (.tail _ member))⟩

theorem admissibleBranches_iff : admissibleBranches branches = true ↔
    ∀ branch ∈ branches, admissible branch.2 = true ∧
      ∀ index, index < branch.1 → uses index branch.2 = true := by
  induction branches with
  | nil =>
      constructor
      · intro _ branch member
        cases member
      · intro _
        rfl
  | cons branch rest ih =>
      obtain ⟨arity, body⟩ := branch
      constructor
      · intro checked found member
        obtain ⟨bodyAdmitted, tail⟩ := Bool.and_eq_true_iff.mp checked
        obtain ⟨allUsed, restAdmitted⟩ := Bool.and_eq_true_iff.mp tail
        cases member with
        | head => exact ⟨bodyAdmitted, parametersUsed_iff.mp allUsed⟩
        | tail _ member => exact ih.mp restAdmitted found member
      · intro allAdmitted
        have head := allAdmitted (arity, body) (.head _)
        exact Bool.and_eq_true_iff.mpr ⟨head.1,
          Bool.and_eq_true_iff.mpr ⟨parametersUsed_iff.mpr head.2,
            ih.mpr (fun found member => allAdmitted found (.tail _ member))⟩⟩

theorem admissible_dataCtor_iff : admissible (.dataCtor dataId constructor fields) = true ↔
    ∀ field ∈ fields, admissible field = true :=
  admissibleArgs_iff

theorem admissible_dataCase_iff :
    admissible (.dataCase dataId result scrutinee branches) = true ↔
      admissible scrutinee = true ∧
        ∀ branch ∈ branches, admissible branch.2 = true ∧
          ∀ index, index < branch.1 → uses index branch.2 = true := by
  constructor
  · intro checked
    obtain ⟨scrutineeAdmitted, branchesAdmitted⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨scrutineeAdmitted, admissibleBranches_iff.mp branchesAdmitted⟩
  · intro admitted
    exact Bool.and_eq_true_iff.mpr ⟨admitted.1, admissibleBranches_iff.mpr admitted.2⟩

theorem programAdmissible_cons_iff :
    programAdmissible (body :: bodies) (signature :: signatures) = true ↔
      admissible body = true ∧
        parametersUsed signature.params.length body = true ∧
        programAdmissible bodies signatures = true := by
  simp [programAdmissible, Bool.and_eq_true]

theorem programAdmissible_length
    (checked : programAdmissible program signatures = true) :
    program.length = signatures.length := by
  induction program generalizing signatures with
  | nil =>
      cases signatures with
      | nil => rfl
      | cons signature signatures => simp [programAdmissible] at checked
  | cons body bodies ih =>
      cases signatures with
      | nil => simp [programAdmissible] at checked
      | cons signature signatures =>
          have checkedRest := (programAdmissible_cons_iff.mp checked).2.2
          exact congrArg Nat.succ (ih checkedRest)

/-- Every declared function has an admitted body using every parameter index. -/
theorem programAdmissible_lookup
    (checked : programAdmissible program signatures = true)
    (found : lookup signatures function = some signature) :
    ∃ body, lookup program function = some body ∧ admissible body = true ∧
      ∀ index, index < signature.params.length → uses index body = true := by
  induction program generalizing signatures function with
  | nil =>
      cases signatures with
      | nil => simp [lookup] at found
      | cons signature signatures => simp [programAdmissible] at checked
  | cons body bodies ih =>
      cases signatures with
      | nil => simp [lookup] at found
      | cons signature' signatures =>
          obtain ⟨hbody, hparams, hrest⟩ := programAdmissible_cons_iff.mp checked
          cases function with
          | zero =>
              simp only [lookup, Option.some.injEq] at found
              subst signature
              exact ⟨body, rfl, hbody, parametersUsed_iff.mp hparams⟩
          | succ function => exact ih hrest found

/-- Source admission inherits core safety; relevance is not a runtime invariant. -/
theorem profile_type_safety (hprogram : ProfileProgramTyped declarations program signatures)
    (typed : ProfileTyped declarations signatures [] expr τ)
    (execution : Steps program (initial expr) final) :
    StateTyped declarations signatures final τ ∧ ¬ Stuck program final :=
  closed_type_safety hprogram.1 typed.1 execution

theorem profile_return_type (hprogram : ProfileProgramTyped declarations program signatures)
    (typed : ProfileTyped declarations signatures [] expr τ)
    (execution : Steps program (initial expr) (.ret value [])) : ValueTyped declarations value τ :=
  return_type hprogram.1 typed.1 execution

theorem profile_overflow_is_justified (hprogram : ProfileProgramTyped declarations program signatures)
    (typed : ProfileTyped declarations signatures [] expr τ)
    (execution : Steps program (initial expr) (.overflow operation left right)) :
    Overflow operation left right :=
  overflow_is_justified hprogram.1 typed.1 execution

end LeanExe.TypeSafety
