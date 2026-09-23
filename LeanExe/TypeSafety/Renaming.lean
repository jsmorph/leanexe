import LeanExe.TypeSafety.Core

/-!
# Binder-safe renaming and raw typing

Renamings move free de Bruijn indices and lift beneath each explicit binder.
Their laws are pointwise or equalities of expressions, never function equality.
Function IDs, nominal IDs, types, constructor tags, and branch arities do not move.

This module proves syntax laws and raw context-indexed typing preservation only.
Public admission still checks the formation of an inserted context. No profile,
new-function-parameter relevance, inference-equivalence, or execution-simulation
claim follows from this checkpoint.
-/

namespace LeanExe.TypeSafety

abbrev Renaming := Nat → Nat

namespace Renaming

def lift (mapping : Renaming) : Renaming
  | 0 => 0
  | index + 1 => mapping index + 1

def liftN : Nat → Renaming → Renaming
  | 0, mapping => mapping
  | count + 1, mapping => lift (liftN count mapping)

theorem lift_congr (same : ∀ index, first index = second index) (index : Nat) :
    lift first index = lift second index := by
  cases index with
  | zero => rfl
  | succ index => exact congrArg Nat.succ (same index)

theorem liftN_congr (same : ∀ index, first index = second index) (count index : Nat) :
    liftN count first index = liftN count second index := by
  induction count generalizing index with
  | zero => exact same index
  | succ count ih => exact lift_congr ih index

theorem lift_identity (identity : ∀ index, mapping index = index) (index : Nat) :
    lift mapping index = index := by
  cases index with
  | zero => rfl
  | succ index => exact congrArg Nat.succ (identity index)

theorem liftN_identity (identity : ∀ index, mapping index = index) (count index : Nat) :
    liftN count mapping index = index := by
  induction count generalizing index with
  | zero => exact identity index
  | succ count ih => exact lift_identity ih index

theorem lift_composes (composes : ∀ index, second (first index) = combined index) (index : Nat) :
    lift second (lift first index) = lift combined index := by
  cases index with
  | zero => rfl
  | succ index => exact congrArg Nat.succ (composes index)

theorem liftN_composes (composes : ∀ index, second (first index) = combined index)
    (count index : Nat) : liftN count second (liftN count first index) = liftN count combined index := by
  induction count generalizing index with
  | zero => exact composes index
  | succ count ih => exact lift_composes ih index

end Renaming

mutual
def Expr.rename (mapping : Renaming) : Expr → Expr
  | .var index => .var (mapping index)
  | .unit => .unit
  | .bool value => .bool value
  | .nat value => .nat value
  | .word width value => .word width value
  | .letE bound body => .letE (bound.rename mapping) (body.rename (Renaming.lift mapping))
  | .ifE condition yes no => .ifE (condition.rename mapping) (yes.rename mapping) (no.rename mapping)
  | .pair left right => .pair (left.rename mapping) (right.rename mapping)
  | .fst pair => .fst (pair.rename mapping)
  | .snd pair => .snd (pair.rename mapping)
  | .split pair body => .split (pair.rename mapping) (body.rename (Renaming.liftN 2 mapping))
  | .unitCase scrutinee body => .unitCase (scrutinee.rename mapping) (body.rename mapping)
  | .inl other payload => .inl other (payload.rename mapping)
  | .inr other payload => .inr other (payload.rename mapping)
  | .sumCase scrutinee left right => .sumCase (scrutinee.rename mapping)
      (left.rename (Renaming.lift mapping)) (right.rename (Renaming.lift mapping))
  | .natCase scrutinee zeroBody succBody => .natCase (scrutinee.rename mapping)
      (zeroBody.rename mapping) (succBody.rename (Renaming.lift mapping))
  | .natBin operation left right => .natBin operation (left.rename mapping) (right.rename mapping)
  | .natCmp operation left right => .natCmp operation (left.rename mapping) (right.rename mapping)
  | .structEq left right => .structEq (left.rename mapping) (right.rename mapping)
  | .wordBin width operation left right =>
      .wordBin width operation (left.rename mapping) (right.rename mapping)
  | .wordCmp width operation left right =>
      .wordCmp width operation (left.rename mapping) (right.rename mapping)
  | .wordOfNat target value => .wordOfNat target (value.rename mapping)
  | .wordToNat source value => .wordToNat source (value.rename mapping)
  | .wordCast source target value => .wordCast source target (value.rename mapping)
  | .call function arguments => .call function (renameArgs mapping arguments)
  | .arrayEmpty item => .arrayEmpty item
  | .arraySize array => .arraySize (array.rename mapping)
  | .arrayGet? array index => .arrayGet? (array.rename mapping) (index.rename mapping)
  | .arraySet? array index replacement =>
      .arraySet? (array.rename mapping) (index.rename mapping) (replacement.rename mapping)
  | .arrayPush? array value => .arrayPush? (array.rename mapping) (value.rename mapping)
  | .arrayAppend? left right => .arrayAppend? (left.rename mapping) (right.rename mapping)
  | .dataCtor dataId constructor fields => .dataCtor dataId constructor (renameArgs mapping fields)
  | .dataCase dataId result scrutinee branches =>
      .dataCase dataId result (scrutinee.rename mapping) (renameBranches mapping branches)

def renameArgs (mapping : Renaming) : List Expr → List Expr
  | [] => []
  | head :: tail => head.rename mapping :: renameArgs mapping tail

def renameBranches (mapping : Renaming) : List (Nat × Expr) → List (Nat × Expr)
  | [] => []
  | (arity, body) :: rest =>
      (arity, body.rename (Renaming.liftN arity mapping)) :: renameBranches mapping rest
end

mutual
theorem Expr.rename_congr (same : ∀ index, first index = second index) (expr : Expr) :
    expr.rename first = expr.rename second := by
  cases expr with
  | var index => exact congrArg Expr.var (same index)
  | unit | bool _ | nat _ | word _ _ | arrayEmpty _ => rfl
  | letE bound body =>
      simp only [Expr.rename, Expr.rename_congr same bound,
        Expr.rename_congr (Renaming.lift_congr same) body]
  | ifE condition yes no =>
      simp only [Expr.rename, Expr.rename_congr same condition, Expr.rename_congr same yes,
        Expr.rename_congr same no]
  | pair left right | unitCase left right | natBin _ left right | natCmp _ left right
  | structEq left right | wordBin _ _ left right | wordCmp _ _ left right
  | arrayGet? left right | arrayPush? left right | arrayAppend? left right =>
      simp only [Expr.rename, Expr.rename_congr same left, Expr.rename_congr same right]
  | fst value | snd value | inl _ value | inr _ value | wordOfNat _ value
  | wordToNat _ value | wordCast _ _ value | arraySize value =>
      simp only [Expr.rename, Expr.rename_congr same value]
  | split pair body =>
      simp only [Expr.rename, Expr.rename_congr same pair,
        Expr.rename_congr (Renaming.liftN_congr same 2) body]
  | sumCase scrutinee left right =>
      simp only [Expr.rename, Expr.rename_congr same scrutinee,
        Expr.rename_congr (Renaming.lift_congr same) left,
        Expr.rename_congr (Renaming.lift_congr same) right]
  | natCase scrutinee zeroBody succBody =>
      simp only [Expr.rename, Expr.rename_congr same scrutinee, Expr.rename_congr same zeroBody,
        Expr.rename_congr (Renaming.lift_congr same) succBody]
  | arraySet? array index replacement =>
      simp only [Expr.rename, Expr.rename_congr same array, Expr.rename_congr same index,
        Expr.rename_congr same replacement]
  | call _ arguments | dataCtor _ _ arguments =>
      simp only [Expr.rename, renameArgs_congr same arguments]
  | dataCase _ _ scrutinee branches =>
      simp only [Expr.rename, Expr.rename_congr same scrutinee,
        renameBranches_congr same branches]

theorem renameArgs_congr (same : ∀ index, first index = second index) (arguments : List Expr) :
    renameArgs first arguments = renameArgs second arguments := by
  cases arguments with
  | nil => rfl
  | cons head tail =>
      simp only [renameArgs, Expr.rename_congr same head, renameArgs_congr same tail]

theorem renameBranches_congr (same : ∀ index, first index = second index)
    (branches : List (Nat × Expr)) :
    renameBranches first branches = renameBranches second branches := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      obtain ⟨arity, body⟩ := branch
      simp only [renameBranches, Expr.rename_congr (Renaming.liftN_congr same arity) body,
        renameBranches_congr same rest]

end

mutual
theorem Expr.rename_identity_of (identity : ∀ index, mapping index = index) (expr : Expr) :
    expr.rename mapping = expr := by
  cases expr with
  | var index => exact congrArg Expr.var (identity index)
  | unit | bool _ | nat _ | word _ _ | arrayEmpty _ => rfl
  | letE bound body =>
      simp only [Expr.rename, Expr.rename_identity_of identity bound,
        Expr.rename_identity_of (Renaming.lift_identity identity) body]
  | ifE condition yes no =>
      simp only [Expr.rename, Expr.rename_identity_of identity condition,
        Expr.rename_identity_of identity yes, Expr.rename_identity_of identity no]
  | pair left right | unitCase left right | natBin _ left right | natCmp _ left right
  | structEq left right | wordBin _ _ left right | wordCmp _ _ left right
  | arrayGet? left right | arrayPush? left right | arrayAppend? left right =>
      simp only [Expr.rename, Expr.rename_identity_of identity left,
        Expr.rename_identity_of identity right]
  | fst value | snd value | inl _ value | inr _ value | wordOfNat _ value
  | wordToNat _ value | wordCast _ _ value | arraySize value =>
      simp only [Expr.rename, Expr.rename_identity_of identity value]
  | split pair body =>
      simp only [Expr.rename, Expr.rename_identity_of identity pair,
        Expr.rename_identity_of (Renaming.liftN_identity identity 2) body]
  | sumCase scrutinee left right =>
      simp only [Expr.rename, Expr.rename_identity_of identity scrutinee,
        Expr.rename_identity_of (Renaming.lift_identity identity) left,
        Expr.rename_identity_of (Renaming.lift_identity identity) right]
  | natCase scrutinee zeroBody succBody =>
      simp only [Expr.rename, Expr.rename_identity_of identity scrutinee,
        Expr.rename_identity_of identity zeroBody,
        Expr.rename_identity_of (Renaming.lift_identity identity) succBody]
  | arraySet? array index replacement =>
      simp only [Expr.rename, Expr.rename_identity_of identity array,
        Expr.rename_identity_of identity index, Expr.rename_identity_of identity replacement]
  | call _ arguments | dataCtor _ _ arguments =>
      simp only [Expr.rename, renameArgs_identity_of identity arguments]
  | dataCase _ _ scrutinee branches =>
      simp only [Expr.rename, Expr.rename_identity_of identity scrutinee,
        renameBranches_identity_of identity branches]

theorem renameArgs_identity_of (identity : ∀ index, mapping index = index)
    (arguments : List Expr) :
    renameArgs mapping arguments = arguments := by
  cases arguments with
  | nil => rfl
  | cons head tail =>
      simp only [renameArgs, Expr.rename_identity_of identity head,
        renameArgs_identity_of identity tail]

theorem renameBranches_identity_of (identity : ∀ index, mapping index = index)
    (branches : List (Nat × Expr)) :
    renameBranches mapping branches = branches := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      obtain ⟨arity, body⟩ := branch
      simp only [renameBranches,
        Expr.rename_identity_of (Renaming.liftN_identity identity arity) body,
        renameBranches_identity_of identity rest]

end

mutual
theorem Expr.rename_comp_of (composes : ∀ index, second (first index) = combined index)
    (expr : Expr) :
    (expr.rename first).rename second = expr.rename combined := by
  cases expr with
  | var index => exact congrArg Expr.var (composes index)
  | unit | bool _ | nat _ | word _ _ | arrayEmpty _ => rfl
  | letE bound body =>
      simp only [Expr.rename, Expr.rename_comp_of composes bound,
        Expr.rename_comp_of (Renaming.lift_composes composes) body]
  | ifE condition yes no =>
      simp only [Expr.rename, Expr.rename_comp_of composes condition,
        Expr.rename_comp_of composes yes, Expr.rename_comp_of composes no]
  | pair left right | unitCase left right | natBin _ left right | natCmp _ left right
  | structEq left right | wordBin _ _ left right | wordCmp _ _ left right
  | arrayGet? left right | arrayPush? left right | arrayAppend? left right =>
      simp only [Expr.rename, Expr.rename_comp_of composes left, Expr.rename_comp_of composes right]
  | fst value | snd value | inl _ value | inr _ value | wordOfNat _ value
  | wordToNat _ value | wordCast _ _ value | arraySize value =>
      simp only [Expr.rename, Expr.rename_comp_of composes value]
  | split pair body =>
      simp only [Expr.rename, Expr.rename_comp_of composes pair,
        Expr.rename_comp_of (Renaming.liftN_composes composes 2) body]
  | sumCase scrutinee left right =>
      simp only [Expr.rename, Expr.rename_comp_of composes scrutinee,
        Expr.rename_comp_of (Renaming.lift_composes composes) left,
        Expr.rename_comp_of (Renaming.lift_composes composes) right]
  | natCase scrutinee zeroBody succBody =>
      simp only [Expr.rename, Expr.rename_comp_of composes scrutinee,
        Expr.rename_comp_of composes zeroBody,
        Expr.rename_comp_of (Renaming.lift_composes composes) succBody]
  | arraySet? array index replacement =>
      simp only [Expr.rename, Expr.rename_comp_of composes array,
        Expr.rename_comp_of composes index, Expr.rename_comp_of composes replacement]
  | call _ arguments | dataCtor _ _ arguments =>
      simp only [Expr.rename, renameArgs_comp_of composes arguments]
  | dataCase _ _ scrutinee branches =>
      simp only [Expr.rename, Expr.rename_comp_of composes scrutinee,
        renameBranches_comp_of composes branches]

theorem renameArgs_comp_of (composes : ∀ index, second (first index) = combined index)
    (arguments : List Expr) :
    renameArgs second (renameArgs first arguments) = renameArgs combined arguments := by
  cases arguments with
  | nil => rfl
  | cons head tail =>
      simp only [renameArgs, Expr.rename_comp_of composes head, renameArgs_comp_of composes tail]

theorem renameBranches_comp_of (composes : ∀ index, second (first index) = combined index)
    (branches : List (Nat × Expr)) :
    renameBranches second (renameBranches first branches) = renameBranches combined branches := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      obtain ⟨arity, body⟩ := branch
      simp only [renameBranches, Expr.rename_comp_of (Renaming.liftN_composes composes arity) body,
        renameBranches_comp_of composes rest]

end

theorem Expr.rename_id (expr : Expr) : expr.rename (fun index => index) = expr :=
  Expr.rename_identity_of (fun _ => rfl) expr

theorem renameArgs_id (arguments : List Expr) : renameArgs (fun index => index) arguments = arguments :=
  renameArgs_identity_of (fun _ => rfl) arguments

theorem renameBranches_id (branches : List (Nat × Expr)) :
    renameBranches (fun index => index) branches = branches :=
  renameBranches_identity_of (fun _ => rfl) branches

theorem Expr.rename_comp (first second : Renaming) (expr : Expr) :
    (expr.rename first).rename second = expr.rename (fun index => second (first index)) :=
  Expr.rename_comp_of (fun _ => rfl) expr

theorem renameArgs_comp (first second : Renaming) (arguments : List Expr) :
    renameArgs second (renameArgs first arguments) =
      renameArgs (fun index => second (first index)) arguments :=
  renameArgs_comp_of (fun _ => rfl) arguments

theorem renameBranches_comp (first second : Renaming) (branches : List (Nat × Expr)) :
    renameBranches second (renameBranches first branches) =
      renameBranches (fun index => second (first index)) branches :=
  renameBranches_comp_of (fun _ => rfl) branches

/-- Every valid source-context lookup is preserved at its renamed index. -/
def RenamingTyped (source target : Context) (mapping : Renaming) : Prop :=
  ∀ {index τ}, lookup source index = some τ → lookup target (mapping index) = some τ

theorem RenamingTyped.lookup (typed : RenamingTyped source target mapping)
    (found : lookup source index = some τ) : lookup target (mapping index) = some τ := typed found

theorem RenamingTyped.refl (Γ : Context) : RenamingTyped Γ Γ (fun index => index) := fun found => found

theorem RenamingTyped.comp (first : RenamingTyped Γ Γ' firstMap)
    (second : RenamingTyped Γ' Γ'' secondMap) :
    RenamingTyped Γ Γ'' (fun index => secondMap (firstMap index)) := fun found => second (first found)

theorem RenamingTyped.lift (typed : RenamingTyped source target mapping) :
    RenamingTyped (α :: source) (α :: target) (Renaming.lift mapping) := by
  intro index τ found
  cases index with
  | zero => exact found
  | succ index => exact typed found

theorem RenamingTyped.liftN (typed : RenamingTyped source target mapping) (prefixTypes : Context) :
    RenamingTyped (prefixTypes ++ source) (prefixTypes ++ target)
      (Renaming.liftN prefixTypes.length mapping) := by
  induction prefixTypes with
  | nil => exact typed
  | cons _ _ ih => exact ih.lift

/-- Inserting an arbitrary context before all free variables preserves raw typing lookups. -/
theorem RenamingTyped.shift (Γ extra : Context) :
    RenamingTyped Γ (extra ++ Γ) (fun index => index + extra.length) := by
  induction extra with
  | nil => exact fun found => found
  | cons _ _ ih => exact fun found => ih found

mutual
/-- A context-respecting renaming preserves the raw expression judgment. -/
theorem ExprTyped.rename (typed : ExprTyped declarations signatures Γ expr τ)
    (mapping : RenamingTyped Γ Γ' ρ) :
    ExprTyped declarations signatures Γ' (expr.rename ρ) τ := by
  cases typed with
  | var found => exact .var (mapping found)
  | unit => exact .unit
  | bool => exact .bool
  | nat bounded => exact .nat bounded
  | word bounded => exact .word bounded
  | letE bound body => exact .letE (bound.rename mapping) (body.rename mapping.lift)
  | ifE condition yes no =>
      exact .ifE (condition.rename mapping) (yes.rename mapping) (no.rename mapping)
  | pair left right => exact .pair (left.rename mapping) (right.rename mapping)
  | fst pair => exact .fst (pair.rename mapping)
  | snd pair => exact .snd (pair.rename mapping)
  | split pair body =>
      exact .split (pair.rename mapping)
        (body.rename (RenamingTyped.lift (RenamingTyped.lift mapping)))
  | unitCase scrutinee body => exact .unitCase (scrutinee.rename mapping) (body.rename mapping)
  | inl payload formed => exact .inl (payload.rename mapping) formed
  | inr payload formed => exact .inr (payload.rename mapping) formed
  | sumCase scrutinee left right =>
      exact .sumCase (scrutinee.rename mapping)
        (left.rename mapping.lift) (right.rename mapping.lift)
  | natCase scrutinee zeroBody succBody =>
      exact .natCase (scrutinee.rename mapping)
        (zeroBody.rename mapping) (succBody.rename mapping.lift)
  | natBin operation left right =>
      exact .natBin operation (left.rename mapping) (right.rename mapping)
  | natCmp operation left right =>
      exact .natCmp operation (left.rename mapping) (right.rename mapping)
  | structEq left right domain =>
      exact .structEq (left.rename mapping) (right.rename mapping) domain
  | wordBin width operation left right =>
      exact .wordBin width operation (left.rename mapping) (right.rename mapping)
  | wordCmp width operation left right =>
      exact .wordCmp width operation (left.rename mapping) (right.rename mapping)
  | wordOfNat target value => exact .wordOfNat target (value.rename mapping)
  | wordToNat source value => exact .wordToNat source (value.rename mapping)
  | wordCast source target value => exact .wordCast source target (value.rename mapping)
  | call found arguments => exact .call found (arguments.rename mapping)
  | arrayEmpty formed => exact .arrayEmpty formed
  | arraySize array => exact .arraySize (array.rename mapping)
  | arrayGet? array index => exact .arrayGet? (array.rename mapping) (index.rename mapping)
  | arraySet? array index replacement =>
      exact .arraySet? (array.rename mapping) (index.rename mapping) (replacement.rename mapping)
  | arrayPush? array value => exact .arrayPush? (array.rename mapping) (value.rename mapping)
  | arrayAppend? left right => exact .arrayAppend? (left.rename mapping) (right.rename mapping)
  | dataCtor foundData foundCtor fields => exact .dataCtor foundData foundCtor (fields.rename mapping)
  | dataCase found formed scrutinee branches =>
      exact .dataCase found formed (scrutinee.rename mapping) (branches.rename mapping)

theorem ArgsTyped.rename (typed : ArgsTyped declarations signatures Γ arguments types)
    (mapping : RenamingTyped Γ Γ' ρ) :
    ArgsTyped declarations signatures Γ' (renameArgs ρ arguments) types := by
  cases typed with
  | nil => exact .nil
  | cons head tail => exact .cons (head.rename mapping) (tail.rename mapping)

theorem BranchesTyped.rename
    (typed : BranchesTyped declarations signatures Γ branches constructors result)
    (mapping : RenamingTyped Γ Γ' ρ) :
    BranchesTyped declarations signatures Γ' (renameBranches ρ branches)
      constructors result := by
  cases typed with
  | nil => exact .nil
  | cons arity body rest =>
      cases arity
      exact .cons rfl (body.rename (mapping.liftN _)) (rest.rename mapping)
end

/-- Raw weakening does not assert formation of the inserted context. -/
theorem ExprTyped.weaken (typed : ExprTyped declarations signatures Γ expr τ)
    (extra : Context) :
    ExprTyped declarations signatures (extra ++ Γ)
      (expr.rename (fun index => index + extra.length)) τ :=
  typed.rename (RenamingTyped.shift Γ extra)

/-- Insert a context below a preserved prefix of local binders. -/
theorem ExprTyped.weakenUnder
    (typed : ExprTyped declarations signatures (prefixTypes ++ Γ) expr τ) (extra : Context) :
    ExprTyped declarations signatures (prefixTypes ++ (extra ++ Γ))
      (expr.rename (Renaming.liftN prefixTypes.length (fun index => index + extra.length))) τ :=
  typed.rename (RenamingTyped.liftN (RenamingTyped.shift Γ extra) prefixTypes)

end LeanExe.TypeSafety
