import LeanExe.TypeSafety.ArrayValues

/-!
# Explicit call-by-value operational semantics

This is a left-to-right environment/continuation machine for the independent
core. Its evaluation order is a specification choice of this core, not a claim
about demand-based LeanExe extraction. Only the selected conditional or sum
branch executes. A let-bound expression evaluates before its body.
Call arguments evaluate left to right in the caller environment. The callee
receives a fresh environment containing exactly those argument values in order:
the first argument has index zero. Continuations retain any caller bindings
needed after the result returns. Recursive calls are allowed.

`step` returns `none` both for terminal states and for malformed/stuck states.
Consequently progress is substantive: a missing variable, a non-Boolean
condition, or a projection from a scalar is not silently relabeled a failure.
The only failure terminal is checked natural-number addition overflow. Checked
array operations evaluate all operands from left to right; bounds and growth
failures return `inl unit` as ordinary data. Nominal construction evaluates fields
in order. Matching checks both nominal identity and the selected branch arity,
then prepends fields in declaration order to the captured lexical environment.
-/

namespace LeanExe.TypeSafety

inductive Frame where
  | letBody (body : Expr) (env : Env)
  | ifBranches (yes no : Expr) (env : Env)
  | pairLeft (right : Expr) (env : Env)
  | pairRight (left : Value)
  | fst
  | snd
  | splitBody (body : Expr) (env : Env)
  | unitBody (body : Expr) (env : Env)
  | inl
  | inr
  | sumBranches (left right : Expr) (env : Env)
  | addLeft (right : Expr) (env : Env)
  | addRight (left : Value)
  /-- Arguments already computed, remaining argument expressions, and caller environment. -/
  | callArgs (function : Nat) (done : Env) (remaining : List Expr) (env : Env)
  | arraySize
  | arrayGetArray (index : Expr) (env : Env)
  | arrayGetIndex (elements : List Value)
  | arraySetArray (index replacement : Expr) (env : Env)
  | arraySetIndex (elements : List Value) (replacement : Expr) (env : Env)
  | arraySetValue (elements : List Value) (index : Nat)
  | arrayPushArray (value : Expr) (env : Env)
  | arrayPushValue (elements : List Value)
  | arrayAppendLeft (right : Expr) (env : Env)
  | arrayAppendRight (left : List Value)
  | dataFields (dataId constructor : Nat) (done : Env) (remaining : List Expr) (env : Env)
  | dataBranches (dataId : Nat) (branches : List (Nat × Expr)) (env : Env)
  deriving Repr

abbrev Kont := List Frame

inductive State where
  | eval (expr : Expr) (env : Env) (kont : Kont)
  | ret (value : Value) (kont : Kont)
  | overflow (left right : Nat)
  deriving Repr

/-- A missing function remains stuck rather than becoming a permitted failure. -/
def enterCall (program : Program) (function : Nat) (arguments : Env) (kont : Kont) :
    Option State :=
  (lookup program function).map (fun body => .eval body arguments kont)

/-- Deterministic one-step execution, with malformed configurations stuck. -/
def step (program : Program) : State → Option State
  | .eval (.var index) env kont => (lookup env index).map (.ret · kont)
  | .eval .unit _ kont => some (.ret .unit kont)
  | .eval (.bool b) _ kont => some (.ret (.bool b) kont)
  | .eval (.nat n) _ kont => some (.ret (.nat n) kont)
  | .eval (.letE bound body) env kont =>
      some (.eval bound env (.letBody body env :: kont))
  | .eval (.ifE condition yes no) env kont =>
      some (.eval condition env (.ifBranches yes no env :: kont))
  | .eval (.pair left right) env kont =>
      some (.eval left env (.pairLeft right env :: kont))
  | .eval (.fst pair) env kont => some (.eval pair env (.fst :: kont))
  | .eval (.snd pair) env kont => some (.eval pair env (.snd :: kont))
  | .eval (.split pair body) env kont =>
      some (.eval pair env (.splitBody body env :: kont))
  | .eval (.unitCase scrutinee body) env kont =>
      some (.eval scrutinee env (.unitBody body env :: kont))
  | .eval (.inl payload) env kont => some (.eval payload env (.inl :: kont))
  | .eval (.inr payload) env kont => some (.eval payload env (.inr :: kont))
  | .eval (.sumCase scrutinee left right) env kont =>
      some (.eval scrutinee env (.sumBranches left right env :: kont))
  | .eval (.add left right) env kont =>
      some (.eval left env (.addLeft right env :: kont))
  | .eval (.call function []) _ kont => enterCall program function [] kont
  | .eval (.call function (argument :: rest)) env kont =>
      some (.eval argument env (.callArgs function [] rest env :: kont))
  | .eval (.arrayEmpty _) _ kont => some (.ret (.array []) kont)
  | .eval (.arraySize array) env kont => some (.eval array env (.arraySize :: kont))
  | .eval (.arrayGet? array index) env kont =>
      some (.eval array env (.arrayGetArray index env :: kont))
  | .eval (.arraySet? array index replacement) env kont =>
      some (.eval array env (.arraySetArray index replacement env :: kont))
  | .eval (.arrayPush? array value) env kont =>
      some (.eval array env (.arrayPushArray value env :: kont))
  | .eval (.arrayAppend? left right) env kont =>
      some (.eval left env (.arrayAppendLeft right env :: kont))
  | .eval (.dataCtor dataId constructor []) _ kont =>
      some (.ret (.data dataId constructor []) kont)
  | .eval (.dataCtor dataId constructor (field :: rest)) env kont =>
      some (.eval field env (.dataFields dataId constructor [] rest env :: kont))
  | .eval (.dataCase dataId _ scrutinee branches) env kont =>
      some (.eval scrutinee env (.dataBranches dataId branches env :: kont))
  | .ret _ [] => none
  | .ret value (.letBody body env :: kont) =>
      some (.eval body (value :: env) kont)
  | .ret (.bool b) (.ifBranches yes no env :: kont) =>
      some (.eval (if b then yes else no) env kont)
  | .ret value (.pairLeft right env :: kont) =>
      some (.eval right env (.pairRight value :: kont))
  | .ret right (.pairRight left :: kont) => some (.ret (.pair left right) kont)
  | .ret (.pair left _) (.fst :: kont) => some (.ret left kont)
  | .ret (.pair _ right) (.snd :: kont) => some (.ret right kont)
  | .ret (.pair left right) (.splitBody body env :: kont) =>
      some (.eval body (left :: right :: env) kont)
  | .ret .unit (.unitBody body env :: kont) => some (.eval body env kont)
  | .ret value (.inl :: kont) => some (.ret (.inl value) kont)
  | .ret value (.inr :: kont) => some (.ret (.inr value) kont)
  | .ret (.inl payload) (.sumBranches left _ env :: kont) =>
      some (.eval left (payload :: env) kont)
  | .ret (.inr payload) (.sumBranches _ right env :: kont) =>
      some (.eval right (payload :: env) kont)
  | .ret value (.addLeft right env :: kont) =>
      some (.eval right env (.addRight value :: kont))
  | .ret (.nat right) (.addRight (.nat left) :: kont) =>
      if left + right < nat64Limit then
        some (.ret (.nat (left + right)) kont)
      else some (.overflow left right)
  | .ret value (.callArgs function done [] _ :: kont) =>
      enterCall program function (done ++ [value]) kont
  | .ret value (.callArgs function done (argument :: rest) env :: kont) =>
      some (.eval argument env (.callArgs function (done ++ [value]) rest env :: kont))
  | .ret (.array elements) (.arraySize :: kont) => some (.ret (.nat elements.length) kont)
  | .ret (.array elements) (.arrayGetArray index env :: kont) =>
      some (.eval index env (.arrayGetIndex elements :: kont))
  | .ret (.nat index) (.arrayGetIndex elements :: kont) =>
      some (.ret (ArrayValues.get? elements index) kont)
  | .ret (.array elements) (.arraySetArray index replacement env :: kont) =>
      some (.eval index env (.arraySetIndex elements replacement env :: kont))
  | .ret (.nat index) (.arraySetIndex elements replacement env :: kont) =>
      some (.eval replacement env (.arraySetValue elements index :: kont))
  | .ret value (.arraySetValue elements index :: kont) =>
      some (.ret (ArrayValues.set? elements index value) kont)
  | .ret (.array elements) (.arrayPushArray value env :: kont) =>
      some (.eval value env (.arrayPushValue elements :: kont))
  | .ret value (.arrayPushValue elements :: kont) =>
      some (.ret (ArrayValues.push? elements value) kont)
  | .ret (.array left) (.arrayAppendLeft right env :: kont) =>
      some (.eval right env (.arrayAppendRight left :: kont))
  | .ret (.array right) (.arrayAppendRight left :: kont) =>
      some (.ret (ArrayValues.append? left right) kont)
  | .ret value (.dataFields dataId constructor done [] _ :: kont) =>
      some (.ret (.data dataId constructor (done ++ [value])) kont)
  | .ret value (.dataFields dataId constructor done (field :: rest) env :: kont) =>
      some (.eval field env
        (.dataFields dataId constructor (done ++ [value]) rest env :: kont))
  | .ret (.data actualId constructor fields) (.dataBranches dataId branches env :: kont) =>
      if actualId = dataId then
        match lookup branches constructor with
        | none => none
        | some (arity, body) =>
            if arity = fields.length then some (.eval body (fields ++ env) kont) else none
      else none
  | .ret _ (_ :: _) => none
  | .overflow _ _ => none

def Step (program : Program) (before after : State) : Prop := step program before = some after

/-- A return or an arithmetically justified overflow, never arbitrary stuckness. -/
def Terminal : State → Prop
  | .ret _ [] => True
  | .overflow left right =>
      left < nat64Limit ∧ right < nat64Limit ∧ nat64Limit ≤ left + right
  | _ => False

/-- The captured environment is part of each suspended expression's invariant. -/
inductive FrameTyped (declarations : DataDecls) (signatures : Signatures) : Frame → Ty → Ty → Prop where
  | letBody : ExprTyped declarations signatures (α :: Γ) body β → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.letBody body env) α β
  | ifBranches : ExprTyped declarations signatures Γ yes τ →
      ExprTyped declarations signatures Γ no τ → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.ifBranches yes no env) .bool τ
  | pairLeft : ExprTyped declarations signatures Γ right β → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.pairLeft right env) α (.prod α β)
  | pairRight : ValueTyped declarations left α →
      FrameTyped declarations signatures (.pairRight left) β (.prod α β)
  | fst : FrameTyped declarations signatures .fst (.prod α β) α
  | snd : FrameTyped declarations signatures .snd (.prod α β) β
  | splitBody : ExprTyped declarations signatures (α :: β :: Γ) body τ → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.splitBody body env) (.prod α β) τ
  | unitBody : ExprTyped declarations signatures Γ body τ → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.unitBody body env) .unit τ
  | inl : TyWF declarations β → FrameTyped declarations signatures .inl α (.sum α β)
  | inr : TyWF declarations α → FrameTyped declarations signatures .inr β (.sum α β)
  | sumBranches : ExprTyped declarations signatures (α :: Γ) left τ →
      ExprTyped declarations signatures (β :: Γ) right τ →
      EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.sumBranches left right env) (.sum α β) τ
  | addLeft : ExprTyped declarations signatures Γ right .nat64 → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.addLeft right env) .nat64 .nat64
  | addRight : ValueTyped declarations left .nat64 →
      FrameTyped declarations signatures (.addRight left) .nat64 .nat64

  | callArgs (found : lookup signatures function = some ⟨params, result⟩) :
      EnvTyped declarations done doneTypes →
      ArgsTyped declarations signatures Γ remaining remainingTypes →
      EnvTyped declarations env Γ → doneTypes ++ (α :: remainingTypes) = params →
      FrameTyped declarations signatures (.callArgs function done remaining env) α result
  | arraySize : FrameTyped declarations signatures .arraySize (.array α) .nat64
  | arrayGetArray : ExprTyped declarations signatures Γ index .nat64 → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.arrayGetArray index env) (.array α) (.sum .unit α)
  | arrayGetIndex : ValuesTyped declarations elements α → elements.length < nat64Limit →
      FrameTyped declarations signatures (.arrayGetIndex elements) .nat64 (.sum .unit α)
  | arraySetArray : ExprTyped declarations signatures Γ index .nat64 →
      ExprTyped declarations signatures Γ replacement α → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.arraySetArray index replacement env)
        (.array α) (.sum .unit (.array α))
  | arraySetIndex : ValuesTyped declarations elements α → elements.length < nat64Limit →
      ExprTyped declarations signatures Γ replacement α → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.arraySetIndex elements replacement env)
        .nat64 (.sum .unit (.array α))
  | arraySetValue : ValuesTyped declarations elements α → elements.length < nat64Limit →
      index < nat64Limit →
      FrameTyped declarations signatures (.arraySetValue elements index) α (.sum .unit (.array α))
  | arrayPushArray : ExprTyped declarations signatures Γ value α → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.arrayPushArray value env) (.array α) (.sum .unit (.array α))
  | arrayPushValue : ValuesTyped declarations elements α → elements.length < nat64Limit →
      FrameTyped declarations signatures (.arrayPushValue elements) α (.sum .unit (.array α))
  | arrayAppendLeft : ExprTyped declarations signatures Γ right (.array α) →
      EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.arrayAppendLeft right env) (.array α) (.sum .unit (.array α))
  | arrayAppendRight : ValuesTyped declarations left α → left.length < nat64Limit →
      FrameTyped declarations signatures (.arrayAppendRight left) (.array α) (.sum .unit (.array α))

  | dataFields (foundData : lookup declarations dataId = some constructors)
      (foundCtor : lookup constructors constructor = some fieldTypes) :
      EnvTyped declarations done doneTypes →
      ArgsTyped declarations signatures Γ remaining remainingTypes →
      EnvTyped declarations env Γ → doneTypes ++ (α :: remainingTypes) = fieldTypes →
      FrameTyped declarations signatures (.dataFields dataId constructor done remaining env)
        α (.data dataId)
  | dataBranches (foundData : lookup declarations dataId = some constructors) :
      TyWF declarations result →
      BranchesTyped declarations signatures Γ branches constructors result →
      EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.dataBranches dataId branches env) (.data dataId) result

/-- A continuation consumes the current type and eventually returns the result type. -/
inductive KontTyped (declarations : DataDecls) (signatures : Signatures) : Kont → Ty → Ty → Prop where
  | nil : TyWF declarations τ → KontTyped declarations signatures [] τ τ
  | cons : FrameTyped declarations signatures frame α β → KontTyped declarations signatures rest β τ →
      KontTyped declarations signatures (frame :: rest) α τ

inductive StateTyped (declarations : DataDecls) (signatures : Signatures) : State → Ty → Prop where
  | eval : ExprTyped declarations signatures Γ expr α → EnvTyped declarations env Γ →
      KontTyped declarations signatures kont α τ →
      StateTyped declarations signatures (.eval expr env kont) τ
  | ret : ValueTyped declarations value α → KontTyped declarations signatures kont α τ →
      StateTyped declarations signatures (.ret value kont) τ
  | overflow : left < nat64Limit → right < nat64Limit → nat64Limit ≤ left + right →
      TyWF declarations τ → StateTyped declarations signatures (.overflow left right) τ

/-- Reflexive, transitive execution; it does not assume termination. -/
inductive Steps (program : Program) : State → State → Prop where
  | refl : Steps program state state
  | tail : Steps program first middle → Step program middle last → Steps program first last

def initial (expr : Expr) : State := .eval expr [] []

/-- A well-formed input type determines a well-formed frame output type. -/
theorem FrameTyped.wellFormed (typed : FrameTyped declarations signatures frame α β)
    (hprogram : ProgramTyped declarations program signatures) (input : TyWF declarations α) :
    TyWF declarations β := by
  cases typed with
  | letBody body env =>
      exact body.wellFormed hprogram.declarationsWF hprogram.signaturesWF
        (.cons input env.wellFormed)
  | ifBranches yes _ env =>
      exact yes.wellFormed hprogram.declarationsWF hprogram.signaturesWF env.wellFormed
  | pairLeft right env =>
      exact .prod input
        (right.wellFormed hprogram.declarationsWF hprogram.signaturesWF env.wellFormed)
  | pairRight left => exact .prod left.wellFormed input
  | fst => exact input.prod_left
  | snd => exact input.prod_right
  | splitBody body env =>
      exact body.wellFormed hprogram.declarationsWF hprogram.signaturesWF
        (.cons input.prod_left (.cons input.prod_right env.wellFormed))
  | unitBody body env =>
      exact body.wellFormed hprogram.declarationsWF hprogram.signaturesWF env.wellFormed
  | inl other => exact .sum input other
  | inr other => exact .sum other input
  | sumBranches left _ env =>
      exact left.wellFormed hprogram.declarationsWF hprogram.signaturesWF
        (.cons input.sum_left env.wellFormed)
  | addLeft _ _ | addRight _ => exact .nat64
  | callArgs found _ _ _ _ => exact (hprogram.signaturesWF.lookup found).result
  | arraySize => exact .nat64
  | arrayGetArray _ _ => exact .sum .unit input.array_item
  | arrayGetIndex elements _ => exact .sum .unit elements.wellFormed
  | arraySetArray _ _ _ => exact .sum .unit input
  | arraySetIndex elements _ _ _ => exact .sum .unit (.array elements.wellFormed)
  | arraySetValue _ _ _ => exact .sum .unit (.array input)
  | arrayPushArray _ _ => exact .sum .unit input
  | arrayPushValue elements _ => exact .sum .unit (.array elements.wellFormed)
  | arrayAppendLeft _ _ | arrayAppendRight _ _ => exact .sum .unit input
  | dataFields found _ _ _ _ _ => exact .data (lookup_lt found)
  | dataBranches _ result _ _ => exact result

theorem KontTyped.wellFormed (typed : KontTyped declarations signatures kont α τ)
    (hprogram : ProgramTyped declarations program signatures) (input : TyWF declarations α) :
    TyWF declarations τ := by
  induction typed with
  | nil result => exact result
  | cons frame rest ih => exact ih (frame.wellFormed hprogram input)

/-- Public runtime typing never assigns a malformed result, including at overflow. -/
theorem StateTyped.wellFormed (typed : StateTyped declarations signatures state τ)
    (hprogram : ProgramTyped declarations program signatures) : TyWF declarations τ := by
  cases typed with
  | eval expr env kont =>
      exact kont.wellFormed hprogram
        (expr.wellFormed hprogram.declarationsWF hprogram.signaturesWF env.wellFormed)
  | ret value kont => exact kont.wellFormed hprogram value.wellFormed
  | overflow _ _ _ result => exact result

theorem initial_typed (hprogram : ProgramTyped declarations program signatures)
    (typed : ExprTyped declarations signatures [] expr τ) :
    StateTyped declarations signatures (initial expr) τ :=
  .eval typed .nil (.nil (typed.wellFormed hprogram.declarationsWF hprogram.signaturesWF .nil))

theorem step_deterministic (left : Step program state next₁) (right : Step program state next₂) :
    next₁ = next₂ := by
  exact Option.some.inj (left.symm.trans right)

end LeanExe.TypeSafety
