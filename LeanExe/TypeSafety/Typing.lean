import LeanExe.TypeSafety.Profile

/-!
# Executable typing and admission

Raw inference corresponds exactly to the declarative expression judgment. Like
that judgment, it does not validate unused ambient declarations, signatures, or
context entries. Public admission checks validate all of those inputs. Explicit
sum annotations make expression types unique; runtime values remain unannotated.
All checks recurse over finite syntax, not over program execution or unfolding
of recursive datatype declarations.
-/

namespace LeanExe.TypeSafety

mutual
/-- Structural inference, corresponding to `ExprTyped` without ambient admission. -/
def inferRaw (declarations : DataDecls) (signatures : Signatures) (Γ : Context) :
    Expr → Option Ty
  | .var index => lookup Γ index
  | .unit => some .unit
  | .bool _ => some .bool
  | .nat value => if value < nat64Limit then some .nat64 else none
  | .word width value => if value < width.modulus then some (.word width) else none
  | .letE bound body =>
      match inferRaw declarations signatures Γ bound with
      | some α => inferRaw declarations signatures (α :: Γ) body
      | none => none
  | .ifE condition yes no =>
      if inferRaw declarations signatures Γ condition = some .bool then
        match inferRaw declarations signatures Γ yes with
        | some τ => if inferRaw declarations signatures Γ no = some τ then some τ else none
        | none => none
      else none
  | .pair left right =>
      match inferRaw declarations signatures Γ left, inferRaw declarations signatures Γ right with
      | some α, some β => some (.prod α β)
      | _, _ => none
  | .fst pair =>
      match inferRaw declarations signatures Γ pair with
      | some (.prod α _) => some α
      | _ => none
  | .snd pair =>
      match inferRaw declarations signatures Γ pair with
      | some (.prod _ β) => some β
      | _ => none
  | .split pair body =>
      match inferRaw declarations signatures Γ pair with
      | some (.prod α β) => inferRaw declarations signatures (α :: β :: Γ) body
      | _ => none
  | .unitCase scrutinee body =>
      if inferRaw declarations signatures Γ scrutinee = some .unit then
        inferRaw declarations signatures Γ body
      else none
  | .inl other payload =>
      if tyWellFormed declarations other then
        match inferRaw declarations signatures Γ payload with
        | some α => some (.sum α other)
        | none => none
      else none
  | .inr other payload =>
      if tyWellFormed declarations other then
        match inferRaw declarations signatures Γ payload with
        | some β => some (.sum other β)
        | none => none
      else none
  | .sumCase scrutinee left right =>
      match inferRaw declarations signatures Γ scrutinee with
      | some (.sum α β) =>
          match inferRaw declarations signatures (α :: Γ) left with
          | some τ =>
              if inferRaw declarations signatures (β :: Γ) right = some τ then some τ else none
          | none => none
      | _ => none
  | .natCase scrutinee zeroBody succBody =>
      if inferRaw declarations signatures Γ scrutinee = some .nat64 then
        match inferRaw declarations signatures Γ zeroBody with
        | some τ =>
            if inferRaw declarations signatures (.nat64 :: Γ) succBody = some τ then some τ else none
        | none => none
      else none
  | .natBin _ left right =>
      if inferRaw declarations signatures Γ left = some .nat64 then
        if inferRaw declarations signatures Γ right = some .nat64 then some .nat64 else none
      else none
  | .natCmp _ left right =>
      if inferRaw declarations signatures Γ left = some .nat64 then
        if inferRaw declarations signatures Γ right = some .nat64 then some .bool else none
      else none
  | .wordBin width _ left right =>
      if inferRaw declarations signatures Γ left = some (.word width) then
        if inferRaw declarations signatures Γ right = some (.word width) then some (.word width)
        else none
      else none
  | .wordCmp width _ left right =>
      if inferRaw declarations signatures Γ left = some (.word width) then
        if inferRaw declarations signatures Γ right = some (.word width) then some .bool else none
      else none
  | .wordOfNat target value =>
      if inferRaw declarations signatures Γ value = some .nat64 then some (.word target) else none
  | .wordToNat source value =>
      if inferRaw declarations signatures Γ value = some (.word source) then some .nat64 else none
  | .wordCast source target value =>
      if inferRaw declarations signatures Γ value = some (.word source) then some (.word target)
      else none
  | .call function arguments =>
      match lookup signatures function with
      | some signature =>
          if checkArgsRaw declarations signatures Γ arguments signature.params then
            some signature.result
          else none
      | none => none
  | .arrayEmpty item => if tyWellFormed declarations item then some (.array item) else none
  | .arraySize array =>
      match inferRaw declarations signatures Γ array with
      | some (.array _) => some .nat64
      | _ => none
  | .arrayGet? array index =>
      match inferRaw declarations signatures Γ array with
      | some (.array α) =>
          if inferRaw declarations signatures Γ index = some .nat64 then some (.sum .unit α)
          else none
      | _ => none
  | .arraySet? array index replacement =>
      match inferRaw declarations signatures Γ array with
      | some (.array α) =>
          if inferRaw declarations signatures Γ index = some .nat64 then
            if inferRaw declarations signatures Γ replacement = some α then
              some (.sum .unit (.array α))
            else none
          else none
      | _ => none
  | .arrayPush? array value =>
      match inferRaw declarations signatures Γ array with
      | some (.array α) =>
          if inferRaw declarations signatures Γ value = some α then
            some (.sum .unit (.array α))
          else none
      | _ => none
  | .arrayAppend? left right =>
      match inferRaw declarations signatures Γ left with
      | some (.array α) =>
          if inferRaw declarations signatures Γ right = some (.array α) then
            some (.sum .unit (.array α))
          else none
      | _ => none
  | .dataCtor dataId constructor fields =>
      match lookup declarations dataId with
      | some constructors =>
          match lookup constructors constructor with
          | some fieldTypes =>
              if checkArgsRaw declarations signatures Γ fields fieldTypes then some (.data dataId)
              else none
          | none => none
      | none => none
  | .dataCase dataId result scrutinee branches =>
      if tyWellFormed declarations result then
        if inferRaw declarations signatures Γ scrutinee = some (.data dataId) then
          match lookup declarations dataId with
          | some constructors =>
              if checkBranchesRaw declarations signatures Γ branches constructors result then
                some result
              else none
          | none => none
        else none
      else none

/-- Exact argument arity and types, checked in source order. -/
def checkArgsRaw (declarations : DataDecls) (signatures : Signatures) (Γ : Context) :
    List Expr → List Ty → Bool
  | [], [] => true
  | argument :: rest, α :: types =>
      decide (inferRaw declarations signatures Γ argument = some α) &&
        checkArgsRaw declarations signatures Γ rest types
  | _, _ => false

/-- Exact constructor coverage, explicit field arity, and a common branch result. -/
def checkBranchesRaw (declarations : DataDecls) (signatures : Signatures) (Γ : Context) :
    List (Nat × Expr) → DataDecl → Ty → Bool
  | [], [], _ => true
  | (arity, body) :: rest, fields :: constructors, result =>
      decide (arity = fields.length) &&
        (decide (inferRaw declarations signatures (fields ++ Γ) body = some result) &&
          checkBranchesRaw declarations signatures Γ rest constructors result)
  | _, _, _ => false
end

mutual
/-- Every declarative derivation is accepted with exactly its result type. -/
theorem inferRaw_complete (typed : ExprTyped declarations signatures Γ expr τ) :
    inferRaw declarations signatures Γ expr = some τ := by
  cases typed with
  | var found => exact found
  | unit | bool => rfl
  | nat bounded | word bounded => simp [inferRaw, bounded]
  | letE bound body => simp [inferRaw, inferRaw_complete bound, inferRaw_complete body]
  | ifE condition yes no =>
      simp [inferRaw, inferRaw_complete condition, inferRaw_complete yes, inferRaw_complete no]
  | pair left right => simp [inferRaw, inferRaw_complete left, inferRaw_complete right]
  | fst pair | snd pair => simp [inferRaw, inferRaw_complete pair]
  | split pair body => simp [inferRaw, inferRaw_complete pair, inferRaw_complete body]
  | unitCase scrutinee body =>
      simp [inferRaw, inferRaw_complete scrutinee, inferRaw_complete body]
  | inl payload other | inr payload other =>
      simp [inferRaw, tyWellFormed_iff.mpr other, inferRaw_complete payload]
  | sumCase scrutinee left right =>
      simp [inferRaw, inferRaw_complete scrutinee, inferRaw_complete left, inferRaw_complete right]
  | natCase scrutinee zeroBody succBody =>
      simp [inferRaw, inferRaw_complete scrutinee, inferRaw_complete zeroBody,
        inferRaw_complete succBody]
  | natBin _ left right | natCmp _ left right =>
      simp [inferRaw, inferRaw_complete left, inferRaw_complete right]
  | wordBin _ _ left right | wordCmp _ _ left right =>
      simp [inferRaw, inferRaw_complete left, inferRaw_complete right]
  | wordOfNat _ value | wordToNat _ value | wordCast _ _ value =>
      simp [inferRaw, inferRaw_complete value]
  | call found arguments => simp [inferRaw, found, checkArgsRaw_complete arguments]
  | arrayEmpty item => simp [inferRaw, tyWellFormed_iff.mpr item]
  | arraySize array => simp [inferRaw, inferRaw_complete array]
  | arrayGet? array index => simp [inferRaw, inferRaw_complete array, inferRaw_complete index]
  | arraySet? array index replacement =>
      simp [inferRaw, inferRaw_complete array, inferRaw_complete index, inferRaw_complete replacement]
  | arrayPush? array value => simp [inferRaw, inferRaw_complete array, inferRaw_complete value]
  | arrayAppend? left right => simp [inferRaw, inferRaw_complete left, inferRaw_complete right]
  | dataCtor foundData foundCtor fields =>
      simp [inferRaw, foundData, foundCtor, checkArgsRaw_complete fields]
  | dataCase foundData result scrutinee branches =>
      simp [inferRaw, foundData, tyWellFormed_iff.mpr result,
        inferRaw_complete scrutinee, checkBranchesRaw_complete branches]

theorem checkArgsRaw_complete (typed : ArgsTyped declarations signatures Γ arguments types) :
    checkArgsRaw declarations signatures Γ arguments types = true := by
  cases typed with
  | nil => rfl
  | cons head tail => simp [checkArgsRaw, inferRaw_complete head, checkArgsRaw_complete tail]

theorem checkBranchesRaw_complete
    (typed : BranchesTyped declarations signatures Γ branches constructors result) :
    checkBranchesRaw declarations signatures Γ branches constructors result = true := by
  cases typed with
  | nil => rfl
  | cons arity body tail =>
      simp [checkBranchesRaw, arity, inferRaw_complete body, checkBranchesRaw_complete tail]
end

mutual
/-- Raw inference produces a derivation without assuming ambient formation. -/
theorem inferRaw_sound (inferred : inferRaw declarations signatures Γ expr = some τ) :
    ExprTyped declarations signatures Γ expr τ := by
  cases expr with
  | var index => exact .var inferred
  | unit => cases inferred; exact .unit
  | bool value => cases inferred; exact .bool
  | nat value =>
      simp only [inferRaw] at inferred
      split at inferred
      · cases inferred; exact .nat (by assumption)
      · cases inferred
  | word width value =>
      simp only [inferRaw] at inferred
      split at inferred
      · cases inferred; exact .word (by assumption)
      · cases inferred
  | letE bound body =>
      cases found : inferRaw declarations signatures Γ bound with
      | none => simp [inferRaw, found] at inferred
      | some α =>
          have result : inferRaw declarations signatures (α :: Γ) body = some τ := by
            simpa only [inferRaw, found] using inferred
          exact .letE (inferRaw_sound found) (inferRaw_sound result)
  | ifE condition yes no =>
      simp only [inferRaw] at inferred
      split at inferred
      next conditionType =>
        cases yesType : inferRaw declarations signatures Γ yes with
        | none => simp [yesType] at inferred
        | some result =>
            simp only [yesType] at inferred
            split at inferred
            next noType =>
              cases inferred
              exact .ifE (inferRaw_sound conditionType) (inferRaw_sound yesType)
                (inferRaw_sound noType)
            next => cases inferred
      next => cases inferred
  | pair left right =>
      cases leftType : inferRaw declarations signatures Γ left with
      | none => simp [inferRaw, leftType] at inferred
      | some α =>
          cases rightType : inferRaw declarations signatures Γ right with
          | none => simp [inferRaw, leftType, rightType] at inferred
          | some β =>
              simp only [inferRaw, leftType, rightType, Option.some.injEq] at inferred
              cases inferred
              exact .pair (inferRaw_sound leftType) (inferRaw_sound rightType)
  | fst pair =>
      cases pairType : inferRaw declarations signatures Γ pair with
      | none => simp [inferRaw, pairType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, pairType] at inferred
          all_goals try cases inferred
          exact .fst (inferRaw_sound pairType)
  | snd pair =>
      cases pairType : inferRaw declarations signatures Γ pair with
      | none => simp [inferRaw, pairType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, pairType] at inferred
          all_goals try cases inferred
          exact .snd (inferRaw_sound pairType)
  | split pair body =>
      cases pairType : inferRaw declarations signatures Γ pair with
      | none => simp [inferRaw, pairType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, pairType] at inferred
          all_goals try cases inferred
          exact .split (inferRaw_sound pairType) (inferRaw_sound inferred)
  | unitCase scrutinee body =>
      simp only [inferRaw] at inferred
      split at inferred
      next scrutineeType => exact .unitCase (inferRaw_sound scrutineeType) (inferRaw_sound inferred)
      next => cases inferred
  | inl other payload =>
      simp only [inferRaw] at inferred
      split at inferred
      next formed =>
        cases payloadType : inferRaw declarations signatures Γ payload with
        | none => simp [payloadType] at inferred
        | some α =>
            simp only [payloadType, Option.some.injEq] at inferred
            cases inferred
            exact .inl (inferRaw_sound payloadType) (tyWellFormed_iff.mp formed)
      next => cases inferred
  | inr other payload =>
      simp only [inferRaw] at inferred
      split at inferred
      next formed =>
        cases payloadType : inferRaw declarations signatures Γ payload with
        | none => simp [payloadType] at inferred
        | some β =>
            simp only [payloadType, Option.some.injEq] at inferred
            cases inferred
            exact .inr (inferRaw_sound payloadType) (tyWellFormed_iff.mp formed)
      next => cases inferred
  | sumCase scrutinee left right =>
      cases scrutineeType : inferRaw declarations signatures Γ scrutinee with
      | none => simp [inferRaw, scrutineeType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, scrutineeType] at inferred
          all_goals try cases inferred
          case sum α β =>
            cases leftType : inferRaw declarations signatures (α :: Γ) left with
            | none => simp [leftType] at inferred
            | some result =>
                simp only [leftType] at inferred
                split at inferred
                next rightType =>
                  cases inferred
                  exact .sumCase (inferRaw_sound scrutineeType) (inferRaw_sound leftType)
                    (inferRaw_sound rightType)
                next => cases inferred
  | natCase scrutinee zeroBody succBody =>
      simp only [inferRaw] at inferred
      split at inferred
      next scrutineeType =>
        cases zeroType : inferRaw declarations signatures Γ zeroBody with
        | none => simp [zeroType] at inferred
        | some result =>
            simp only [zeroType] at inferred
            split at inferred
            next succType =>
              cases inferred
              exact .natCase (inferRaw_sound scrutineeType) (inferRaw_sound zeroType)
                (inferRaw_sound succType)
            next => cases inferred
      next => cases inferred
  | natBin operation left right =>
      simp only [inferRaw] at inferred
      split at inferred
      next leftType =>
        split at inferred
        next rightType =>
          cases inferred
          exact .natBin operation (inferRaw_sound leftType) (inferRaw_sound rightType)
        next => cases inferred
      next => cases inferred
  | natCmp operation left right =>
      simp only [inferRaw] at inferred
      split at inferred
      next leftType =>
        split at inferred
        next rightType =>
          cases inferred
          exact .natCmp operation (inferRaw_sound leftType) (inferRaw_sound rightType)
        next => cases inferred
      next => cases inferred
  | wordBin width operation left right =>
      simp only [inferRaw] at inferred
      split at inferred
      next leftType =>
        split at inferred
        next rightType =>
          cases inferred
          exact .wordBin width operation (inferRaw_sound leftType) (inferRaw_sound rightType)
        next => cases inferred
      next => cases inferred
  | wordCmp width operation left right =>
      simp only [inferRaw] at inferred
      split at inferred
      next leftType =>
        split at inferred
        next rightType =>
          cases inferred
          exact .wordCmp width operation (inferRaw_sound leftType) (inferRaw_sound rightType)
        next => cases inferred
      next => cases inferred
  | wordOfNat target value =>
      simp only [inferRaw] at inferred
      split at inferred
      next valueType =>
        cases inferred
        exact .wordOfNat target (inferRaw_sound valueType)
      next => cases inferred
  | wordToNat source value =>
      simp only [inferRaw] at inferred
      split at inferred
      next valueType =>
        cases inferred
        exact .wordToNat source (inferRaw_sound valueType)
      next => cases inferred
  | wordCast source target value =>
      simp only [inferRaw] at inferred
      split at inferred
      next valueType =>
        cases inferred
        exact .wordCast source target (inferRaw_sound valueType)
      next => cases inferred
  | call function arguments =>
      cases found : lookup signatures function with
      | none => simp [inferRaw, found] at inferred
      | some signature =>
          simp only [inferRaw, found] at inferred
          split at inferred
          next argumentsChecked =>
            cases inferred
            exact .call found (checkArgsRaw_sound argumentsChecked)
          next => cases inferred
  | arrayEmpty item =>
      simp only [inferRaw] at inferred
      split at inferred
      next formed => cases inferred; exact .arrayEmpty (tyWellFormed_iff.mp formed)
      next => cases inferred
  | arraySize array =>
      cases arrayType : inferRaw declarations signatures Γ array with
      | none => simp [inferRaw, arrayType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, arrayType] at inferred
          all_goals try cases inferred
          exact .arraySize (inferRaw_sound arrayType)
  | arrayGet? array index =>
      cases arrayType : inferRaw declarations signatures Γ array with
      | none => simp [inferRaw, arrayType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, arrayType] at inferred
          all_goals try cases inferred
          split at inferred
          next indexType =>
            cases inferred
            exact .arrayGet? (inferRaw_sound arrayType) (inferRaw_sound indexType)
          next => cases inferred
  | arraySet? array index replacement =>
      cases arrayType : inferRaw declarations signatures Γ array with
      | none => simp [inferRaw, arrayType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, arrayType] at inferred
          all_goals try cases inferred
          split at inferred
          next indexType =>
            split at inferred
            next replacementType =>
              cases inferred
              exact .arraySet? (inferRaw_sound arrayType) (inferRaw_sound indexType)
                (inferRaw_sound replacementType)
            next => cases inferred
          next => cases inferred
  | arrayPush? array value =>
      cases arrayType : inferRaw declarations signatures Γ array with
      | none => simp [inferRaw, arrayType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, arrayType] at inferred
          all_goals try cases inferred
          split at inferred
          next valueType =>
            cases inferred
            exact .arrayPush? (inferRaw_sound arrayType) (inferRaw_sound valueType)
          next => cases inferred
  | arrayAppend? left right =>
      cases leftType : inferRaw declarations signatures Γ left with
      | none => simp [inferRaw, leftType] at inferred
      | some shape =>
          cases shape <;> simp only [inferRaw, leftType] at inferred
          all_goals try cases inferred
          split at inferred
          next rightType =>
            cases inferred
            exact .arrayAppend? (inferRaw_sound leftType) (inferRaw_sound rightType)
          next => cases inferred
  | dataCtor dataId constructor fields =>
      cases foundData : lookup declarations dataId with
      | none => simp [inferRaw, foundData] at inferred
      | some constructors =>
          cases foundCtor : lookup constructors constructor with
          | none => simp [inferRaw, foundData, foundCtor] at inferred
          | some fieldTypes =>
              simp only [inferRaw, foundData, foundCtor] at inferred
              split at inferred
              next fieldsChecked =>
                cases inferred
                exact .dataCtor foundData foundCtor (checkArgsRaw_sound fieldsChecked)
              next => cases inferred
  | dataCase dataId result scrutinee branches =>
      simp only [inferRaw] at inferred
      split at inferred
      next resultFormed =>
        split at inferred
        next scrutineeType =>
          cases foundData : lookup declarations dataId with
          | none => simp [foundData] at inferred
          | some constructors =>
              simp only [foundData] at inferred
              split at inferred
              next branchesChecked =>
                cases inferred
                exact .dataCase foundData (tyWellFormed_iff.mp resultFormed)
                  (inferRaw_sound scrutineeType) (checkBranchesRaw_sound branchesChecked)
              next => cases inferred
        next => cases inferred
      next => cases inferred

theorem checkArgsRaw_sound
    (checked : checkArgsRaw declarations signatures Γ arguments types = true) :
    ArgsTyped declarations signatures Γ arguments types := by
  cases arguments with
  | nil =>
      cases types with
      | nil => exact .nil
      | cons _ _ => cases checked
  | cons argument rest =>
      cases types with
      | nil => cases checked
      | cons α types =>
          obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp checked
          exact .cons (inferRaw_sound (of_decide_eq_true head)) (checkArgsRaw_sound tail)

theorem checkBranchesRaw_sound
    (checked : checkBranchesRaw declarations signatures Γ branches constructors result = true) :
    BranchesTyped declarations signatures Γ branches constructors result := by
  cases branches with
  | nil =>
      cases constructors with
      | nil => exact .nil
      | cons _ _ => cases checked
  | cons branch rest =>
      obtain ⟨arity, body⟩ := branch
      cases constructors with
      | nil => cases checked
      | cons fields constructors =>
          obtain ⟨arityChecked, tail⟩ := Bool.and_eq_true_iff.mp checked
          obtain ⟨bodyChecked, restChecked⟩ := Bool.and_eq_true_iff.mp tail
          exact .cons (of_decide_eq_true arityChecked)
            (inferRaw_sound (of_decide_eq_true bodyChecked)) (checkBranchesRaw_sound restChecked)
end

theorem inferRaw_iff : inferRaw declarations signatures Γ expr = some τ ↔
    ExprTyped declarations signatures Γ expr τ :=
  ⟨inferRaw_sound, inferRaw_complete⟩

theorem checkArgsRaw_iff : checkArgsRaw declarations signatures Γ arguments types = true ↔
    ArgsTyped declarations signatures Γ arguments types :=
  ⟨checkArgsRaw_sound, checkArgsRaw_complete⟩

theorem checkBranchesRaw_iff :
    checkBranchesRaw declarations signatures Γ branches constructors result = true ↔
      BranchesTyped declarations signatures Γ branches constructors result :=
  ⟨checkBranchesRaw_sound, checkBranchesRaw_complete⟩

/-- Explicit sum annotations make the expression judgment type-unique. -/
theorem ExprTyped.unique (left : ExprTyped declarations signatures Γ expr α)
    (right : ExprTyped declarations signatures Γ expr β) : α = β :=
  Option.some.inj ((inferRaw_complete left).symm.trans (inferRaw_complete right))

/-- Public inference validates every ambient declaration, signature, and context entry. -/
def infer (declarations : DataDecls) (signatures : Signatures) (Γ : Context) (expr : Expr) :
    Option Ty :=
  if declarationsWellFormed declarations &&
      (signaturesWellFormed declarations signatures && typesWellFormed declarations Γ) then
    inferRaw declarations signatures Γ expr
  else none

theorem infer_eq_some_iff : infer declarations signatures Γ expr = some τ ↔
    DeclarationsWF declarations ∧ SignaturesWF declarations signatures ∧
      TypesWF declarations Γ ∧ ExprTyped declarations signatures Γ expr τ := by
  constructor
  · intro inferred
    unfold infer at inferred
    split at inferred
    next formed =>
      obtain ⟨declarationsChecked, rest⟩ := Bool.and_eq_true_iff.mp formed
      obtain ⟨signaturesChecked, contextChecked⟩ := Bool.and_eq_true_iff.mp rest
      exact ⟨declarationsWellFormed_iff.mp declarationsChecked,
        signaturesWellFormed_iff.mp signaturesChecked, typesWellFormed_iff.mp contextChecked,
        inferRaw_sound inferred⟩
    next => cases inferred
  · rintro ⟨declarationsFormed, signaturesFormed, contextFormed, typed⟩
    simp only [infer, declarationsWellFormed_iff.mpr declarationsFormed,
      signaturesWellFormed_iff.mpr signaturesFormed, typesWellFormed_iff.mpr contextFormed,
      Bool.true_and, ite_true]
    exact inferRaw_complete typed

theorem inferRaw_add : inferRaw declarations signatures Γ (.add left right) =
    if inferRaw declarations signatures Γ left = some .nat64 then
      if inferRaw declarations signatures Γ right = some .nat64 then some .nat64 else none
    else none := rfl

theorem inferRaw_succ : inferRaw declarations signatures Γ (.succ value) =
    if inferRaw declarations signatures Γ value = some .nat64 then some .nat64 else none := by
  simp [inferRaw, show 1 < nat64Limit from by decide]

theorem inferRaw_pred : inferRaw declarations signatures Γ (.pred value) =
    if inferRaw declarations signatures Γ value = some .nat64 then some .nat64 else none := by
  simp [inferRaw, show 1 < nat64Limit from by decide]

theorem inferRaw_boolToNat : inferRaw declarations signatures Γ (.boolToNat value) =
    if inferRaw declarations signatures Γ value = some .bool then some .nat64 else none := by
  simp [inferRaw, show 1 < nat64Limit from by decide,
    show 0 < nat64Limit from by decide]

theorem inferRaw_wordNot : inferRaw declarations signatures Γ (.wordNot width value) =
    if inferRaw declarations signatures Γ value = some (.word width)
    then some (.word width) else none := by
  simp [inferRaw, wordMask_bounded]

/-- Check each body against its signature in the shared global signature table. -/
def bodiesWellTyped (declarations : DataDecls) (signatures : Signatures) :
    Program → Signatures → Bool
  | [], [] => true
  | body :: bodies, signature :: rest =>
      decide (inferRaw declarations signatures signature.params body = some signature.result) &&
        bodiesWellTyped declarations signatures bodies rest
  | _, _ => false

/-- Ordinary program admission, including unused declarations and exact body alignment. -/
def programWellTyped (declarations : DataDecls) (program : Program) (signatures : Signatures) :
    Bool :=
  declarationsWellFormed declarations &&
    (signaturesWellFormed declarations signatures &&
      bodiesWellTyped declarations signatures program signatures)

theorem bodiesWellTyped_iff : bodiesWellTyped declarations signatures program bodySignatures = true ↔
    BodiesTyped declarations signatures program bodySignatures := by
  induction program generalizing bodySignatures with
  | nil =>
      cases bodySignatures with
      | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
      | cons signature rest =>
          constructor
          · intro impossible; cases impossible
          · intro impossible; cases impossible
  | cons body bodies ih =>
      cases bodySignatures with
      | nil =>
          constructor
          · intro impossible; cases impossible
          · intro impossible; cases impossible
      | cons signature rest =>
          constructor
          · intro checked
            obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp checked
            exact .cons (inferRaw_sound (of_decide_eq_true head)) (ih.mp tail)
          · intro typed
            cases typed with
            | cons head tail =>
                exact Bool.and_eq_true_iff.mpr
                  ⟨decide_eq_true (inferRaw_complete head), ih.mpr tail⟩

theorem programWellTyped_iff : programWellTyped declarations program signatures = true ↔
    ProgramTyped declarations program signatures := by
  constructor
  · intro checked
    obtain ⟨declarationsChecked, rest⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨signaturesChecked, bodiesChecked⟩ := Bool.and_eq_true_iff.mp rest
    exact ⟨declarationsWellFormed_iff.mp declarationsChecked,
      signaturesWellFormed_iff.mp signaturesChecked, bodiesWellTyped_iff.mp bodiesChecked⟩
  · intro typed
    exact Bool.and_eq_true_iff.mpr
      ⟨declarationsWellFormed_iff.mpr typed.declarationsWF,
        Bool.and_eq_true_iff.mpr ⟨signaturesWellFormed_iff.mpr typed.signaturesWF,
          bodiesWellTyped_iff.mpr typed.bodies⟩⟩

/-- Expression admission combines complete ordinary typing with syntactic relevance. -/
def profileExpressionWellTyped (declarations : DataDecls) (signatures : Signatures)
    (Γ : Context) (expr : Expr) (τ : Ty) : Bool :=
  decide (infer declarations signatures Γ expr = some τ) && admissible expr

/-- Program admission combines complete ordinary typing with syntactic relevance. -/
def profileProgramWellTyped (declarations : DataDecls) (program : Program)
    (signatures : Signatures) : Bool :=
  programWellTyped declarations program signatures && programAdmissible program signatures

theorem profileExpressionWellTyped_iff :
    profileExpressionWellTyped declarations signatures Γ expr τ = true ↔
      DeclarationsWF declarations ∧ SignaturesWF declarations signatures ∧
        TypesWF declarations Γ ∧ ProfileTyped declarations signatures Γ expr τ := by
  constructor
  · intro checked
    obtain ⟨typeChecked, admitted⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨declarationsFormed, signaturesFormed, contextFormed, typed⟩ :=
      infer_eq_some_iff.mp (of_decide_eq_true typeChecked)
    exact ⟨declarationsFormed, signaturesFormed, contextFormed, typed, admitted⟩
  · rintro ⟨declarationsFormed, signaturesFormed, contextFormed, typed, admitted⟩
    exact Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true (infer_eq_some_iff.mpr
        ⟨declarationsFormed, signaturesFormed, contextFormed, typed⟩), admitted⟩

theorem profileProgramWellTyped_iff :
    profileProgramWellTyped declarations program signatures = true ↔
      ProfileProgramTyped declarations program signatures := by
  constructor
  · intro checked
    obtain ⟨typed, admitted⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨programWellTyped_iff.mp typed, admitted⟩
  · intro typed
    exact Bool.and_eq_true_iff.mpr ⟨programWellTyped_iff.mpr typed.1, typed.2⟩

/-- Checked ordinary programs and expressions inherit safety for every finite execution. -/
theorem checked_type_safety
    (programChecked : programWellTyped declarations program signatures = true)
    (expressionChecked : infer declarations signatures [] expr = some τ)
    (execution : Steps program (initial expr) final) :
    StateTyped declarations signatures final τ ∧ ¬ Stuck program final :=
  closed_type_safety (programWellTyped_iff.mp programChecked)
    (infer_eq_some_iff.mp expressionChecked).2.2.2 execution

/-- Executable profile admission is sufficient for the proved language safety theorem. -/
theorem profile_checked_type_safety
    (programChecked : profileProgramWellTyped declarations program signatures = true)
    (expressionChecked : profileExpressionWellTyped declarations signatures [] expr τ = true)
    (execution : Steps program (initial expr) final) :
    StateTyped declarations signatures final τ ∧ ¬ Stuck program final :=
  profile_type_safety (profileProgramWellTyped_iff.mp programChecked)
    (profileExpressionWellTyped_iff.mp expressionChecked).2.2.2 execution

end LeanExe.TypeSafety
