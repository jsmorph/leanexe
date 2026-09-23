import LeanExe.TypeSafety.ArrayValues

/-!
# Explicit call-by-value operational semantics

This is a left-to-right environment/continuation machine for the independent
core. Its evaluation order is a specification choice of this core, not a claim
about demand-based LeanExe extraction. Only the selected conditional, sum, or
natural-number branch executes. Natural successor patterns bind the predecessor
at index zero; the zero arm introduces no binder. A let-bound expression evaluates
before its body.
Call arguments evaluate left to right in the caller environment. The callee
receives a fresh environment containing exactly those argument values in order:
the first argument has index zero. Continuations retain any caller bindings
needed after the result returns. Recursive calls are allowed.

`step` returns `none` both for terminal states and for malformed/stuck states.
Consequently progress is substantive: a missing variable, a non-Boolean
condition, or a projection from a scalar is not silently relabeled a failure.
The only failure terminal is checked natural-number addition or multiplication
overflow, recording the operation and both operands. Checked
array operations evaluate all operands from left to right; bounds and growth
failures return `inl unit` as ordinary data. Nominal construction evaluates fields
in order. Matching checks both nominal identity and the selected branch arity,
then prepends fields in declaration order to the captured lexical environment.
Word operations check runtime width tags; their modular results and conversions
produce ordinary values and introduce no failure terminal.
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
  | natBranches (zeroBody succBody : Expr) (env : Env)
  | natBinLeft (operation : NatBinOp) (right : Expr) (env : Env)
  | natCmpLeft (operation : NatCmpOp) (right : Expr) (env : Env)
  | natBinRight (operation : NatBinOp) (left : Value)
  | natCmpRight (operation : NatCmpOp) (left : Value)
  | wordBinLeft (width : WordWidth) (operation : WordBinOp) (right : Expr) (env : Env)
  | wordBinRight (width : WordWidth) (operation : WordBinOp) (left : Value)
  | wordCmpLeft (width : WordWidth) (operation : NatCmpOp) (right : Expr) (env : Env)
  | wordCmpRight (width : WordWidth) (operation : NatCmpOp) (left : Value)
  | wordOfNat (target : WordWidth)
  | wordToNat (source : WordWidth)
  | wordCast (source target : WordWidth)
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
  | overflow (operation : NatOverflowOp) (left right : Nat)
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
  | .eval (.word width n) _ kont => some (.ret (.word width n) kont)
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
  | .eval (.inl _ payload) env kont => some (.eval payload env (.inl :: kont))
  | .eval (.inr _ payload) env kont => some (.eval payload env (.inr :: kont))
  | .eval (.sumCase scrutinee left right) env kont =>
      some (.eval scrutinee env (.sumBranches left right env :: kont))
  | .eval (.natCase scrutinee zeroBody succBody) env kont =>
      some (.eval scrutinee env (.natBranches zeroBody succBody env :: kont))
  | .eval (.natBin operation left right) env kont =>
      some (.eval left env (.natBinLeft operation right env :: kont))
  | .eval (.natCmp operation left right) env kont =>
      some (.eval left env (.natCmpLeft operation right env :: kont))
  | .eval (.wordBin width operation left right) env kont =>
      some (.eval left env (.wordBinLeft width operation right env :: kont))
  | .eval (.wordCmp width operation left right) env kont =>
      some (.eval left env (.wordCmpLeft width operation right env :: kont))
  | .eval (.wordOfNat target value) env kont => some (.eval value env (.wordOfNat target :: kont))
  | .eval (.wordToNat source value) env kont => some (.eval value env (.wordToNat source :: kont))
  | .eval (.wordCast source target value) env kont =>
      some (.eval value env (.wordCast source target :: kont))
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
  | .ret (.nat 0) (.natBranches zeroBody _ env :: kont) =>
      some (.eval zeroBody env kont)
  | .ret (.nat (predecessor + 1)) (.natBranches _ succBody env :: kont) =>
      some (.eval succBody (.nat predecessor :: env) kont)
  | .ret value (.natBinLeft operation right env :: kont) =>
      some (.eval right env (.natBinRight operation value :: kont))
  | .ret (.nat right) (.natBinRight operation (.nat left) :: kont) =>
      match evalNatBin operation left right with
      | .value result => some (.ret (.nat result) kont)
      | .overflow fault => some (.overflow fault left right)
  | .ret value (.natCmpLeft operation right env :: kont) =>
      some (.eval right env (.natCmpRight operation value :: kont))
  | .ret (.nat right) (.natCmpRight operation (.nat left) :: kont) =>
      some (.ret (.bool (operation.apply left right)) kont)
  | .ret value (.wordBinLeft width operation right env :: kont) =>
      some (.eval right env (.wordBinRight width operation value :: kont))
  | .ret (.word rightWidth right) (.wordBinRight width operation (.word leftWidth left) :: kont) =>
      if leftWidth = width ∧ rightWidth = width then
        some (.ret (.word width (evalWordBin width operation left right)) kont)
      else none
  | .ret value (.wordCmpLeft width operation right env :: kont) =>
      some (.eval right env (.wordCmpRight width operation value :: kont))
  | .ret (.word rightWidth right) (.wordCmpRight width operation (.word leftWidth left) :: kont) =>
      if leftWidth = width ∧ rightWidth = width then
        some (.ret (.bool (operation.apply left right)) kont)
      else none
  | .ret (.nat value) (.wordOfNat target :: kont) =>
      some (.ret (.word target (normalizeWord target value)) kont)
  | .ret (.word actual value) (.wordToNat source :: kont) =>
      if actual = source then some (.ret (.nat value) kont) else none
  | .ret (.word actual value) (.wordCast source target :: kont) =>
      if actual = source then some (.ret (.word target (normalizeWord target value)) kont) else none
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
  | .overflow _ _ _ => none

/-- Source conveniences execute through the ordinary generic frames. -/
theorem step_add : step program (.eval (.add left right) env kont) =
    some (.eval left env (.natBinLeft .add right env :: kont)) := rfl

theorem step_succ : step program (.eval (.succ value) env kont) =
    some (.eval value env (.natBinLeft .add (.nat 1) env :: kont)) := rfl

theorem step_pred : step program (.eval (.pred value) env kont) =
    some (.eval value env (.natBinLeft .sub (.nat 1) env :: kont)) := rfl

theorem step_wordNot : step program (.eval (.wordNot width value) env kont) =
    some (.eval value env (.wordBinLeft width .bitXor (.word width (wordMask width)) env :: kont)) := rfl

theorem step_boolToNat : step program (.eval (.boolToNat value) env kont) =
    some (.eval value env (.ifBranches (.nat 1) (.nat 0) env :: kont)) := rfl

theorem step_natCase : step program (.eval (.natCase scrutinee zeroBody succBody) env kont) =
    some (.eval scrutinee env (.natBranches zeroBody succBody env :: kont)) := rfl

theorem step_natCase_zero : step program (.ret (.nat 0) (.natBranches zeroBody succBody env :: kont)) =
    some (.eval zeroBody env kont) := rfl

theorem step_natCase_succ :
    step program (.ret (.nat (predecessor + 1)) (.natBranches zeroBody succBody env :: kont)) =
      some (.eval succBody (.nat predecessor :: env) kont) := rfl

def Step (program : Program) (before after : State) : Prop := step program before = some after

/-- A return or an arithmetically justified overflow, never arbitrary stuckness. -/
def Terminal : State → Prop
  | .ret _ [] => True
  | .overflow operation left right => Overflow operation left right
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
  | natBranches : ExprTyped declarations signatures Γ zeroBody τ →
      ExprTyped declarations signatures (.nat64 :: Γ) succBody τ → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.natBranches zeroBody succBody env) .nat64 τ
  | natBinLeft (operation : NatBinOp) :
      ExprTyped declarations signatures Γ right .nat64 → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.natBinLeft operation right env) .nat64 .nat64
  | natBinRight (operation : NatBinOp) : ValueTyped declarations left .nat64 →
      FrameTyped declarations signatures (.natBinRight operation left) .nat64 .nat64
  | natCmpLeft (operation : NatCmpOp) :
      ExprTyped declarations signatures Γ right .nat64 → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.natCmpLeft operation right env) .nat64 .bool
  | natCmpRight (operation : NatCmpOp) : ValueTyped declarations left .nat64 →
      FrameTyped declarations signatures (.natCmpRight operation left) .nat64 .bool

  | wordBinLeft (width : WordWidth) (operation : WordBinOp) :
      ExprTyped declarations signatures Γ right (.word width) → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.wordBinLeft width operation right env) (.word width) (.word width)
  | wordBinRight (width : WordWidth) (operation : WordBinOp) :
      ValueTyped declarations left (.word width) →
      FrameTyped declarations signatures (.wordBinRight width operation left) (.word width) (.word width)
  | wordCmpLeft (width : WordWidth) (operation : NatCmpOp) :
      ExprTyped declarations signatures Γ right (.word width) → EnvTyped declarations env Γ →
      FrameTyped declarations signatures (.wordCmpLeft width operation right env) (.word width) .bool
  | wordCmpRight (width : WordWidth) (operation : NatCmpOp) :
      ValueTyped declarations left (.word width) →
      FrameTyped declarations signatures (.wordCmpRight width operation left) (.word width) .bool
  | wordOfNat (target : WordWidth) :
      FrameTyped declarations signatures (.wordOfNat target) .nat64 (.word target)
  | wordToNat (source : WordWidth) :
      FrameTyped declarations signatures (.wordToNat source) (.word source) .nat64
  | wordCast (source target : WordWidth) :
      FrameTyped declarations signatures (.wordCast source target) (.word source) (.word target)

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
  | overflow : left < nat64Limit → right < nat64Limit → nat64Limit ≤ operation.apply left right →
      TyWF declarations τ → StateTyped declarations signatures (.overflow operation left right) τ

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
  | natBranches zeroBody _ env =>
      exact zeroBody.wellFormed hprogram.declarationsWF hprogram.signaturesWF env.wellFormed
  | natBinLeft _ _ _ | natBinRight _ _ => exact .nat64
  | natCmpLeft _ _ _ | natCmpRight _ _ => exact .bool
  | wordBinLeft _ _ _ _ | wordBinRight _ _ _ | wordOfNat _ | wordCast _ _ => exact .word
  | wordCmpLeft _ _ _ _ | wordCmpRight _ _ _ => exact .bool
  | wordToNat _ => exact .nat64
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
