import LeanExe.TypeSafety.WordOperations

/-!
# An independent first-order core

This module does not import the extractor, IR evaluator, or WebAssembly emitter.
Expressions and values are untyped syntax; their typing judgments are separate.
Variables use de Bruijn indices, with index zero denoting the newest binding.
On entry to a function body, its fresh parameter environment places the first
argument at index zero, the second at index one, and so on. Local bindings then
prepend their values to that environment. Nominal constructor patterns similarly
bind the first field at index zero and prepend all fields to the captured context.

The fragment contains `Unit`, `Bool`, bounded natural numbers, products, binary
sums, bindings, conditionals, bounded-natural arithmetic and comparisons, and
direct first-order calls. Words of widths 8, 32, and 64 support modular arithmetic,
unsigned comparisons, finite bit operations, masked logical shifts, and conversions.
`nat64` is a bounded natural-number interpretation, not modular unsigned
arithmetic: addition and multiplication may overflow; subtraction saturates;
division and remainder specify their zero-divisor behavior. Function bodies may
call any declared function, including themselves;
typing imposes no termination condition. Nominal declarations admit arbitrary
mutual recursion through strictly positive first-order fields, with exhaustive
constructor patterns. Formation is checked separately and required by typing.

Persistent arrays contain homogeneous finite sequences with length below
`nat64Limit`. Reads, replacement, growth, and concatenation expose checked sum
results; their typing is independent of any physical storage representation.

Words have explicit 8/32/64-bit widths and canonical bounded literal values.
Arithmetic is modular, comparisons are unsigned, and explicit conversions
normalize to the target width. Word arithmetic does not raise Nat overflow.
-/

namespace LeanExe.TypeSafety

inductive Expr where
  | var (index : Nat)
  | unit
  | bool (value : Bool)
  | nat (value : Nat)
  | word (width : WordWidth) (value : Nat)
  | letE (bound body : Expr)
  | ifE (condition yes no : Expr)
  | pair (left right : Expr)
  | fst (pair : Expr)
  | snd (pair : Expr)
  /-- The body binds the left field at index zero and the right field at index one. -/
  | split (pair body : Expr)
  /-- Unit elimination evaluates the scrutinee and introduces no field binders. -/
  | unitCase (scrutinee body : Expr)
  /-- The absent summand is explicit; the payload determines the inhabited summand. -/
  | inl (otherTy : Ty) (payload : Expr)
  | inr (otherTy : Ty) (payload : Expr)
  /-- Each branch binds its selected payload at index zero. -/
  | sumCase (scrutinee left right : Expr)
  | natBin (operation : NatBinOp) (left right : Expr)
  | natCmp (operation : NatCmpOp) (left right : Expr)
  | wordBin (width : WordWidth) (operation : WordBinOp) (left right : Expr)
  | wordCmp (width : WordWidth) (operation : NatCmpOp) (left right : Expr)
  | wordOfNat (target : WordWidth) (value : Expr)
  | wordToNat (source : WordWidth) (value : Expr)
  | wordCast (source target : WordWidth) (value : Expr)
  | call (function : Nat) (arguments : List Expr)
  | arrayEmpty (item : Ty)
  | arraySize (array : Expr)
  | arrayGet? (array index : Expr)
  | arraySet? (array index replacement : Expr)
  | arrayPush? (array value : Expr)
  | arrayAppend? (left right : Expr)
  | dataCtor (dataId constructor : Nat) (fields : List Expr)
  /-- Branches are in constructor order, with explicit field arity and body. -/
  | dataCase (dataId : Nat) (result : Ty) (scrutinee : Expr)
      (branches : List (Nat × Expr))
  deriving Repr

/-- Transparent source conveniences; each operand occurs once in the expanded syntax. -/
abbrev Expr.add (left right : Expr) : Expr := .natBin .add left right
abbrev Expr.succ (value : Expr) : Expr := .natBin .add value (.nat 1)
abbrev Expr.pred (value : Expr) : Expr := .natBin .sub value (.nat 1)
abbrev Expr.boolToNat (value : Expr) : Expr := .ifE value (.nat 1) (.nat 0)

/-- Finite-width complement evaluates its operand once, then XORs the canonical mask. -/
abbrev Expr.wordNot (width : WordWidth) (value : Expr) : Expr :=
  .wordBin width .bitXor value (.word width (wordMask width))

inductive Value where
  | unit
  | bool (value : Bool)
  | nat (value : Nat)
  | word (width : WordWidth) (value : Nat)
  | pair (left right : Value)
  | inl (payload : Value)
  | inr (payload : Value)
  | array (elements : List Value)
  | data (dataId constructor : Nat) (fields : List Value)
  deriving Repr

abbrev Env := List Value

/-- Body and signature indices identify functions; there are no function values. -/
abbrev Program := List Expr

mutual
inductive ExprTyped (declarations : DataDecls) (signatures : Signatures) :
    Context → Expr → Ty →
      Prop where
  | var (found : lookup Γ index = some τ) : ExprTyped declarations signatures Γ (.var index) τ
  | unit : ExprTyped declarations signatures Γ .unit .unit
  | bool : ExprTyped declarations signatures Γ (.bool b) .bool
  | nat (bounded : n < nat64Limit) : ExprTyped declarations signatures Γ (.nat n) .nat64
  | word (bounded : n < width.modulus) :
      ExprTyped declarations signatures Γ (.word width n) (.word width)
  | letE : ExprTyped declarations signatures Γ bound α →
      ExprTyped declarations signatures (α :: Γ) body β →
      ExprTyped declarations signatures Γ (.letE bound body) β
  | ifE : ExprTyped declarations signatures Γ condition .bool →
      ExprTyped declarations signatures Γ yes τ →
      ExprTyped declarations signatures Γ no τ →
      ExprTyped declarations signatures Γ (.ifE condition yes no) τ
  | pair : ExprTyped declarations signatures Γ left α → ExprTyped declarations signatures Γ right β →
      ExprTyped declarations signatures Γ (.pair left right) (.prod α β)
  | fst : ExprTyped declarations signatures Γ pair (.prod α β) →
      ExprTyped declarations signatures Γ (.fst pair) α
  | snd : ExprTyped declarations signatures Γ pair (.prod α β) →
      ExprTyped declarations signatures Γ (.snd pair) β
  | split : ExprTyped declarations signatures Γ pair (.prod α β) →
      ExprTyped declarations signatures (α :: β :: Γ) body τ →
      ExprTyped declarations signatures Γ (.split pair body) τ
  | unitCase : ExprTyped declarations signatures Γ scrutinee .unit →
      ExprTyped declarations signatures Γ body τ →
      ExprTyped declarations signatures Γ (.unitCase scrutinee body) τ
  | inl : ExprTyped declarations signatures Γ payload α → TyWF declarations β →
      ExprTyped declarations signatures Γ (.inl β payload) (.sum α β)
  | inr : ExprTyped declarations signatures Γ payload β → TyWF declarations α →
      ExprTyped declarations signatures Γ (.inr α payload) (.sum α β)
  | sumCase : ExprTyped declarations signatures Γ scrutinee (.sum α β) →
      ExprTyped declarations signatures (α :: Γ) left τ →
      ExprTyped declarations signatures (β :: Γ) right τ →
      ExprTyped declarations signatures Γ (.sumCase scrutinee left right) τ
  | natBin (operation : NatBinOp) : ExprTyped declarations signatures Γ left .nat64 →
      ExprTyped declarations signatures Γ right .nat64 →
      ExprTyped declarations signatures Γ (.natBin operation left right) .nat64

  | natCmp (operation : NatCmpOp) : ExprTyped declarations signatures Γ left .nat64 →
      ExprTyped declarations signatures Γ right .nat64 →
      ExprTyped declarations signatures Γ (.natCmp operation left right) .bool

  | wordBin (width : WordWidth) (operation : WordBinOp) :
      ExprTyped declarations signatures Γ left (.word width) →
      ExprTyped declarations signatures Γ right (.word width) →
      ExprTyped declarations signatures Γ (.wordBin width operation left right) (.word width)
  | wordCmp (width : WordWidth) (operation : NatCmpOp) :
      ExprTyped declarations signatures Γ left (.word width) →
      ExprTyped declarations signatures Γ right (.word width) →
      ExprTyped declarations signatures Γ (.wordCmp width operation left right) .bool
  | wordOfNat (target : WordWidth) : ExprTyped declarations signatures Γ value .nat64 →
      ExprTyped declarations signatures Γ (.wordOfNat target value) (.word target)
  | wordToNat (source : WordWidth) : ExprTyped declarations signatures Γ value (.word source) →
      ExprTyped declarations signatures Γ (.wordToNat source value) .nat64
  | wordCast (source target : WordWidth) :
      ExprTyped declarations signatures Γ value (.word source) →
      ExprTyped declarations signatures Γ (.wordCast source target value) (.word target)

  | call (found : lookup signatures function = some ⟨params, result⟩) :
      ArgsTyped declarations signatures Γ arguments params →
      ExprTyped declarations signatures Γ (.call function arguments) result
  | arrayEmpty : TyWF declarations α → ExprTyped declarations signatures Γ (.arrayEmpty α) (.array α)
  | arraySize : ExprTyped declarations signatures Γ array (.array α) →
      ExprTyped declarations signatures Γ (.arraySize array) .nat64
  | arrayGet? : ExprTyped declarations signatures Γ array (.array α) →
      ExprTyped declarations signatures Γ index .nat64 →
      ExprTyped declarations signatures Γ (.arrayGet? array index) (.sum .unit α)
  | arraySet? : ExprTyped declarations signatures Γ array (.array α) →
      ExprTyped declarations signatures Γ index .nat64 →
      ExprTyped declarations signatures Γ replacement α →
      ExprTyped declarations signatures Γ (.arraySet? array index replacement) (.sum .unit (.array α))
  | arrayPush? : ExprTyped declarations signatures Γ array (.array α) →
      ExprTyped declarations signatures Γ value α →
      ExprTyped declarations signatures Γ (.arrayPush? array value) (.sum .unit (.array α))
  | arrayAppend? : ExprTyped declarations signatures Γ left (.array α) →
      ExprTyped declarations signatures Γ right (.array α) →
      ExprTyped declarations signatures Γ (.arrayAppend? left right) (.sum .unit (.array α))

  | dataCtor (foundData : lookup declarations dataId = some constructors)
      (foundCtor : lookup constructors constructor = some fieldTypes) :
      ArgsTyped declarations signatures Γ fields fieldTypes →
      ExprTyped declarations signatures Γ (.dataCtor dataId constructor fields) (.data dataId)
  | dataCase (foundData : lookup declarations dataId = some constructors) :
      TyWF declarations result →
      ExprTyped declarations signatures Γ scrutinee (.data dataId) →
      BranchesTyped declarations signatures Γ branches constructors result →
      ExprTyped declarations signatures Γ (.dataCase dataId result scrutinee branches) result

inductive ArgsTyped (declarations : DataDecls) (signatures : Signatures) :
    Context → List Expr →
      List Ty → Prop where
  | nil : ArgsTyped declarations signatures Γ [] []
  | cons : ExprTyped declarations signatures Γ argument α →
      ArgsTyped declarations signatures Γ rest types →
      ArgsTyped declarations signatures Γ (argument :: rest) (α :: types)

/-- Every constructor has one branch; its field binders follow declaration order. -/
inductive BranchesTyped (declarations : DataDecls) (signatures : Signatures)
    : Context → List (Nat × Expr) → DataDecl → Ty → Prop where
  | nil : BranchesTyped declarations signatures Γ [] [] result
  | cons : arity = fields.length →
      ExprTyped declarations signatures (fields ++ Γ) body result →
      BranchesTyped declarations signatures Γ rest constructors result →
      BranchesTyped declarations signatures Γ ((arity, body) :: rest) (fields :: constructors) result

end

theorem ExprTyped.add (left : ExprTyped declarations signatures Γ leftExpr .nat64)
    (right : ExprTyped declarations signatures Γ rightExpr .nat64) :
    ExprTyped declarations signatures Γ (.add leftExpr rightExpr) .nat64 :=
  .natBin .add left right

theorem ExprTyped.succ (typed : ExprTyped declarations signatures Γ value .nat64) :
    ExprTyped declarations signatures Γ (.succ value) .nat64 :=
  .natBin .add typed (.nat (by decide))

theorem ExprTyped.pred (typed : ExprTyped declarations signatures Γ value .nat64) :
    ExprTyped declarations signatures Γ (.pred value) .nat64 :=
  .natBin .sub typed (.nat (by decide))

theorem ExprTyped.boolToNat (typed : ExprTyped declarations signatures Γ value .bool) :
    ExprTyped declarations signatures Γ (.boolToNat value) .nat64 :=
  .ifE typed (.nat (by decide)) (.nat (by decide))

theorem ExprTyped.wordNot (typed : ExprTyped declarations signatures Γ value (.word width)) :
    ExprTyped declarations signatures Γ (.wordNot width value) (.word width) :=
  .wordBin width .bitXor typed (.word (wordMask_bounded width))

/-- All function bodies use the same global signature table, allowing recursion. -/
inductive BodiesTyped (declarations : DataDecls) (signatures : Signatures) :
    Program →
      Signatures → Prop where
  | nil : BodiesTyped declarations signatures [] []
  | cons : ExprTyped declarations signatures signature.params body signature.result →
      BodiesTyped declarations signatures bodies rest →
      BodiesTyped declarations signatures (body :: bodies) (signature :: rest)

/-- Formation and exact body/signature alignment are independent admission obligations. -/
structure ProgramTyped (declarations : DataDecls) (program : Program)
    (signatures : Signatures) : Prop where
  declarationsWF : DeclarationsWF declarations
  signaturesWF : SignaturesWF declarations signatures
  bodies : BodiesTyped declarations signatures program signatures

/-- A declared callee exists and its body is typed in its parameter context. -/
theorem BodiesTyped.lookup (typed : BodiesTyped declarations signatures program bodySignatures)
    (found : lookup bodySignatures function = some signature) :
    ∃ body, lookup program function = some body ∧
      ExprTyped declarations signatures signature.params body signature.result := by
  induction typed generalizing function signature with
  | nil => simp [LeanExe.TypeSafety.lookup] at found
  | cons hbody hrest ih =>
      cases function with
      | zero =>
          simp only [LeanExe.TypeSafety.lookup, Option.some.injEq] at found
          subst signature
          exact ⟨_, rfl, hbody⟩
      | succ function => exact ih found

mutual
inductive ValueTyped (declarations : DataDecls) : Value → Ty → Prop where
  | unit : ValueTyped declarations .unit .unit
  | bool : ValueTyped declarations (.bool b) .bool
  | nat (bounded : n < nat64Limit) : ValueTyped declarations (.nat n) .nat64
  | word (bounded : n < width.modulus) : ValueTyped declarations (.word width n) (.word width)
  | pair : ValueTyped declarations left α → ValueTyped declarations right β →
      ValueTyped declarations (.pair left right) (.prod α β)
  | inl : ValueTyped declarations payload α → TyWF declarations β →
      ValueTyped declarations (.inl payload) (.sum α β)
  | inr : ValueTyped declarations payload β → TyWF declarations α →
      ValueTyped declarations (.inr payload) (.sum α β)
  | array : ValuesTyped declarations elements α → elements.length < nat64Limit →
      ValueTyped declarations (.array elements) (.array α)

  | data (foundData : lookup declarations dataId = some constructors)
      (foundCtor : lookup constructors constructor = some fieldTypes) :
      EnvTyped declarations fields fieldTypes →
      ValueTyped declarations (.data dataId constructor fields) (.data dataId)

/-- An abstract array stores a finite homogeneous sequence of values. -/
inductive ValuesTyped (declarations : DataDecls) : List Value → Ty → Prop where
  | nil : TyWF declarations α → ValuesTyped declarations [] α
  | cons : ValueTyped declarations value α → ValuesTyped declarations rest α →
      ValuesTyped declarations (value :: rest) α

inductive EnvTyped (declarations : DataDecls) : Env → Context → Prop where
  | nil : EnvTyped declarations [] []
  | cons : ValueTyped declarations value τ → EnvTyped declarations env Γ →
      EnvTyped declarations (value :: env) (τ :: Γ)
end

/-- Argument accumulation preserves the correspondence between values and types. -/
theorem EnvTyped.append (left : EnvTyped declarations env Γ) (right : EnvTyped declarations env' Δ) :
    EnvTyped declarations (env ++ env') (Γ ++ Δ) := by
  induction env generalizing Γ with
  | nil => cases left; exact right
  | cons value env ih =>
      cases left with
      | cons hvalue henv => exact .cons hvalue (ih henv)

/-- A typed variable always has a value of its declared type. -/
theorem EnvTyped.lookup (henv : EnvTyped declarations env Γ)
    (found : lookup Γ index = some τ) :
    ∃ value, lookup env index = some value ∧ ValueTyped declarations value τ := by
  induction env generalizing Γ index τ with
  | nil => cases henv; cases found
  | cons value env ih =>
      cases henv with
      | cons hvalue henv =>
          cases index with
          | zero => cases found; exact ⟨_, rfl, hvalue⟩
          | succ index => exact ih henv found

mutual
/-- Formation follows from typing even for types absent from a runtime payload. -/
theorem ValueTyped.wellFormed (typed : ValueTyped declarations value τ) :
    TyWF declarations τ := by
  cases typed with
  | unit => exact .unit
  | bool => exact .bool
  | nat _ => exact .nat64
  | word _ => exact .word
  | pair left right => exact .prod left.wellFormed right.wellFormed
  | inl payload other => exact .sum payload.wellFormed other
  | inr payload other => exact .sum other payload.wellFormed
  | array elements _ => exact .array elements.wellFormed
  | data foundData _ _ => exact .data (lookup_lt foundData)

theorem ValuesTyped.wellFormed (typed : ValuesTyped declarations elements τ) :
    TyWF declarations τ := by
  cases typed with
  | nil item => exact item
  | cons head _ => exact head.wellFormed
end

theorem EnvTyped.wellFormed (typed : EnvTyped declarations env Γ) : TypesWF declarations Γ := by
  induction env generalizing Γ with
  | nil => cases typed; exact .nil
  | cons value rest ih =>
      cases typed with
      | cons head tail => exact .cons head.wellFormed (ih tail)

theorem EnvTyped.length (typed : EnvTyped declarations env Γ) : env.length = Γ.length := by
  induction env generalizing Γ with
  | nil => cases typed; rfl
  | cons value rest ih =>
      cases typed with
      | cons head tail => exact congrArg Nat.succ (ih tail)

/-- Formation includes intermediate types, not just annotations at the root. -/
theorem ExprTyped.wellFormed (typed : ExprTyped declarations signatures Γ expr τ)
    (hdeclarations : DeclarationsWF declarations) (hsignatures : SignaturesWF declarations signatures)
    (hcontext : TypesWF declarations Γ) : TyWF declarations τ := by
  cases typed with
  | var found => exact hcontext.lookup found
  | unit => exact .unit
  | bool => exact .bool
  | nat _ => exact .nat64
  | word _ => exact .word
  | letE bound body =>
      exact body.wellFormed hdeclarations hsignatures
        (.cons (bound.wellFormed hdeclarations hsignatures hcontext) hcontext)
  | ifE _ yes _ => exact yes.wellFormed hdeclarations hsignatures hcontext
  | pair left right =>
      exact .prod (left.wellFormed hdeclarations hsignatures hcontext)
        (right.wellFormed hdeclarations hsignatures hcontext)
  | fst pair => exact (pair.wellFormed hdeclarations hsignatures hcontext).prod_left
  | snd pair => exact (pair.wellFormed hdeclarations hsignatures hcontext).prod_right
  | split pair body =>
      have formed := pair.wellFormed hdeclarations hsignatures hcontext
      exact body.wellFormed hdeclarations hsignatures
        (.cons formed.prod_left (.cons formed.prod_right hcontext))
  | unitCase _ body => exact body.wellFormed hdeclarations hsignatures hcontext
  | inl payload other =>
      exact .sum (payload.wellFormed hdeclarations hsignatures hcontext) other
  | inr payload other =>
      exact .sum other (payload.wellFormed hdeclarations hsignatures hcontext)
  | sumCase scrutinee left _ =>
      have formed := scrutinee.wellFormed hdeclarations hsignatures hcontext
      exact left.wellFormed hdeclarations hsignatures (.cons formed.sum_left hcontext)
  | natBin _ _ _ => exact .nat64
  | natCmp _ _ _ => exact .bool
  | wordBin _ _ _ _ | wordOfNat _ _ | wordCast _ _ _ => exact .word
  | wordCmp _ _ _ _ => exact .bool
  | wordToNat _ _ => exact .nat64
  | call found _ => exact (hsignatures.lookup found).result
  | arrayEmpty item => exact .array item
  | arraySize _ => exact .nat64
  | arrayGet? array _ =>
      exact .sum .unit (array.wellFormed hdeclarations hsignatures hcontext).array_item
  | arraySet? array _ _ =>
      exact .sum .unit (array.wellFormed hdeclarations hsignatures hcontext)
  | arrayPush? array _ => exact .sum .unit (array.wellFormed hdeclarations hsignatures hcontext)
  | arrayAppend? left _ => exact .sum .unit (left.wellFormed hdeclarations hsignatures hcontext)
  | dataCtor found _ _ => exact .data (lookup_lt found)
  | dataCase _ result _ _ => exact result

theorem ArgsTyped.wellFormed (typed : ArgsTyped declarations signatures Γ arguments types)
    (hdeclarations : DeclarationsWF declarations) (hsignatures : SignaturesWF declarations signatures)
    (hcontext : TypesWF declarations Γ) : TypesWF declarations types := by
  induction arguments generalizing types with
  | nil => cases typed; exact .nil
  | cons argument rest ih =>
      cases typed with
      | cons head tail =>
          exact .cons (head.wellFormed hdeclarations hsignatures hcontext) (ih tail)

/-- Exhaustive branch alignment makes every declared constructor selectable. -/
theorem BranchesTyped.lookup (typed : BranchesTyped declarations signatures Γ branches constructors τ)
    (found : lookup constructors constructor = some fields) :
    ∃ arity body, lookup branches constructor = some (arity, body) ∧
      arity = fields.length ∧ ExprTyped declarations signatures (fields ++ Γ) body τ := by
  induction branches generalizing constructors constructor with
  | nil => cases typed; cases found
  | cons branch rest ih =>
      cases typed with
      | cons arity body tail =>
          cases constructor with
          | zero => cases found; exact ⟨_, _, rfl, arity, body⟩
          | succ constructor => exact ih tail found

theorem BranchesTyped.length
    (typed : BranchesTyped declarations signatures Γ branches constructors τ) :
    branches.length = constructors.length := by
  induction branches generalizing constructors with
  | nil => cases typed; rfl
  | cons branch rest ih =>
      cases typed with
      | cons _ _ tail => exact congrArg Nat.succ (ih tail)

theorem ValueTyped.bool_canonical (h : ValueTyped declarations value .bool) :
    ∃ b, value = .bool b := by
  cases h with
  | bool => exact ⟨_, rfl⟩

theorem ValueTyped.unit_canonical (h : ValueTyped declarations value .unit) : value = .unit := by
  cases h
  rfl

theorem ValueTyped.nat_canonical (h : ValueTyped declarations value .nat64) :
    ∃ n, value = .nat n ∧ n < nat64Limit := by
  cases h with
  | nat bounded => exact ⟨_, rfl, bounded⟩

theorem ValueTyped.word_canonical (typed : ValueTyped declarations value (.word width)) :
    ∃ n, value = .word width n ∧ n < width.modulus := by
  cases typed with
  | word bounded => exact ⟨_, rfl, bounded⟩

theorem ValueTyped.prod_canonical (h : ValueTyped declarations value (.prod α β)) :
    ∃ left right, value = .pair left right ∧
      ValueTyped declarations left α ∧ ValueTyped declarations right β := by
  cases h with
  | pair hleft hright => exact ⟨_, _, rfl, hleft, hright⟩

theorem ValueTyped.sum_canonical (h : ValueTyped declarations value (.sum α β)) :
    (∃ payload, value = .inl payload ∧ ValueTyped declarations payload α) ∨
    (∃ payload, value = .inr payload ∧ ValueTyped declarations payload β) := by
  cases h with
  | inl hpayload _ => exact .inl ⟨_, rfl, hpayload⟩
  | inr hpayload _ => exact .inr ⟨_, rfl, hpayload⟩

theorem ValueTyped.array_canonical (h : ValueTyped declarations value (.array α)) :
    ∃ elements, value = .array elements ∧ ValuesTyped declarations elements α ∧
      elements.length < nat64Limit := by
  cases h with
  | array helements bounded => exact ⟨_, rfl, helements, bounded⟩

theorem ValueTyped.data_canonical (typed : ValueTyped declarations value (.data dataId)) :
    ∃ constructor fields constructors fieldTypes,
      value = .data dataId constructor fields ∧
      lookup declarations dataId = some constructors ∧
      lookup constructors constructor = some fieldTypes ∧
      EnvTyped declarations fields fieldTypes := by
  cases typed with
  | data foundData foundCtor fields => exact ⟨_, _, _, _, rfl, foundData, foundCtor, fields⟩

end LeanExe.TypeSafety
