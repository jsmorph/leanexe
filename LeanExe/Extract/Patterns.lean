import Lean
import Init.Data.ByteArray.Extra
import LeanExe.Extract.Storage
import LeanExe.IR.Core

open Lean

namespace LeanExe.Extract.Core

def replaceAt? {α : Type} (index : Nat) (value : α) : List α → Option (List α)
  | [] => none
  | head :: rest =>
      if index == 0 then
        some (value :: rest)
      else
        replaceAt? (index - 1) value rest |>.map fun updated => head :: updated

def optionConstructorType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | ty :: _ => typeAtom? env ty
  | [] => none

def exceptConstructorTypes? (env : Environment) (args : List Expr) : Option (Ty × Ty) :=
  match args with
  | errorTy :: okTy :: _ =>
      match typeAtom? env errorTy, typeAtom? env okTy with
      | some errorTy, some okTy => some (errorTy, okTy)
      | _, _ => none
  | _ => none

def exceptMapTypes? (env : Environment) (args : List Expr) : Option (Ty × Ty) :=
  match args with
  | errorTy :: _sourceTy :: resultTy :: _ =>
      match typeAtom? env errorTy, typeAtom? env resultTy with
      | some errorTy, some resultTy => some (errorTy, resultTy)
      | _, _ => none
  | _ => none

def exceptMapErrorTypes? (env : Environment) (args : List Expr) : Option (Ty × Ty) :=
  match args with
  | sourceErrorTy :: resultErrorTy :: _okTy :: _ =>
      match typeAtom? env sourceErrorTy, typeAtom? env resultErrorTy with
      | some sourceErrorTy, some resultErrorTy => some (sourceErrorTy, resultErrorTy)
      | _, _ => none
  | _ => none

def exceptPayloadType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | errorTy :: okTy :: _ =>
      match typeAtom? env errorTy, typeAtom? env okTy with
      | some _, some okTy => some okTy
      | _, _ => none
  | _ => none

def optionMapResultType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | _sourceTy :: resultTy :: _ => typeAtom? env resultTy
  | _ => none

def optionOrElseArgs? (env : Environment) (fn : Expr) (args : List Expr) : Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Option.orElse then
        match args.reverse with
        | fallback :: optionValue :: _ => some (optionValue, fallback)
        | _ => none
      else if name == ``HOrElse.hOrElse then
        match primitiveResultType? env args, args.reverse with
        | some resultTy, fallback :: optionValue :: _ =>
            optionPayloadType? resultTy |>.map (fun _ => (optionValue, fallback))
        | _, _ => none
      else
        none
  | _ => none

def exceptOrElseArgs? (env : Environment) (fn : Expr) (args : List Expr) : Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``HOrElse.hOrElse then
        match primitiveResultType? env args, args.reverse with
        | some (.variant typeName _ _), fallback :: exceptValue :: _ =>
            if typeName == ``Except then some (exceptValue, fallback) else none
        | _, _ => none
      else
        none
  | _ => none

def idBindArgs? (fn : Expr) (args : List Expr) : Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Bind.bind then
        match args, args.reverse with
        | monadTy :: _, bindFn :: value :: _ =>
            if isIdType monadTy then some (value, bindFn) else none
        | _, _ => none
      else
        none
  | _ => none

inductive SupportedMonad where
  | id
  | option
  | except (errorTy : Ty)

def exceptMonadErrorType? (env : Environment) (expr : Expr) : Option Ty :=
  match appFnArgs expr with
  | (.const ``Except _, [errorTy]) => typeAtom? env errorTy
  | _ => none

def supportedMonadType? (env : Environment) (expr : Expr) : Option SupportedMonad :=
  if isIdType expr then
    some .id
  else if isOptionMonadType expr then
    some .option
  else
    match exceptMonadErrorType? env expr with
    | some errorTy => some (.except errorTy)
    | none => none

def monadMapResultType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | _monadTy :: _inst :: _sourceTy :: resultTy :: _ => typeAtom? env resultTy
  | _ => none

structure ForInArgs where
  collectionTy : Ty
  itemTy : Ty
  resultTy : Ty
  collection : Expr
  init : Expr
  body : Expr

def isLegacyRangeType : Ty → Bool
  | .struct name _ [.nat, .nat, .nat] => name == ``Std.Legacy.Range
  | _ => false

def isLeanLoopType : Ty → Bool
  | .struct name _ [] => name == ``Lean.Loop
  | .variant name _ [[]] => name == ``Lean.Loop
  | _ => false

def legacyRangeParts (value : ExtractedValue) : Except String (IRExpr × IRExpr × IRExpr) := do
  let start ← scalarValue (← structField ``Std.Legacy.Range 0 value)
  let stop ← scalarValue (← structField ``Std.Legacy.Range 1 value)
  let step ← scalarValue (← structField ``Std.Legacy.Range 2 value)
  .ok (start, stop, step)

def arrayAttachValue? (env : Environment) (expr : Expr) : Option (Ty × Expr) :=
  match appFnArgs expr with
  | (.const ``Array.attach _, args) =>
      match args.reverse with
      | array :: itemTyExpr :: _ =>
          typeAtom? env itemTyExpr |>.map fun itemTy => (itemTy, array)
      | _ => none
  | _ => none

def arrayAttachSize? (env : Environment) (expr : Expr) : Option Expr :=
  match appFnArgs expr with
  | (.const ``Array.size _, args) =>
      match args.reverse with
      | array :: _ => arrayAttachValue? env array |>.map Prod.snd
      | _ => none
  | _ => none

def arrayMapUnattachBody? (expr : Expr) : Option Expr :=
  match appFnArgs expr with
  | (.const ``Array.map_unattach.match_1 _, args) =>
      match args.reverse with
      | arm :: _scrutinee :: _ => collectLambdas arm 2
      | _ => none
  | _ => none

def isArrayAttachGeneratedMatcherName (candidate : Name) : Bool :=
  match candidate with
  | .str _ component => component.startsWith "match_"
  | _ => false

def isSubtypeTypeExpr (expr : Expr) : Bool :=
  match appFnArgs expr with
  | (.const name _, _) => name == ``Subtype
  | _ => false

def arrayAttachSubtypeMatcherBody? (env : Environment) (name : Name) (args : List Expr) :
    Option Expr :=
  if !isArrayAttachGeneratedMatcherName name then
    none
  else
    match env.find? name with
    | some info =>
        let domains := (peelForall info.type).fst
        let rec loop (index : Nat) : List Expr → Option Nat
          | [] => none
          | domain :: rest =>
              let instantiated := domain.instantiateRev (args.take index).toArray
              if isSubtypeTypeExpr instantiated then
                some index
              else
                loop (index + 1) rest
        match loop 0 domains with
        | some scrutineeIndex =>
            match args[scrutineeIndex]?, args.drop (scrutineeIndex + 1) with
            | some scrutinee, [arm] =>
                if isBVar 0 scrutinee then
                  collectLambdas arm 2
                else
                  none
            | _, _ => none
        | none => none
    | none => none

def arrayAttachUnwrapBody? (env : Environment) (expr : Expr) : Option Expr :=
  match arrayMapUnattachBody? expr with
  | some body => some body
  | none =>
      match appFnArgs expr with
      | (.const name _, args) =>
          arrayAttachSubtypeMatcherBody? env name args
      | _ => none

def idPureArg? (fn : Expr) (args : List Expr) : Option Expr :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Pure.pure then
        match args, args.reverse with
        | monadTy :: _, value :: _ =>
            if isIdType monadTy then some value else none
        | _, _ => none
      else
        none
  | _ => none

def idForInArgs? (env : Environment) (fn : Expr) (args : List Expr) : Option ForInArgs :=
  match fn.consumeMData, args with
  | .const name _, [monadTy, collectionTyExpr, itemTyExpr, _inst, resultTyExpr, collection, init, body] =>
      if name == ``ForIn.forIn && isIdType monadTy then
        match typeAtom? env collectionTyExpr, typeAtom? env itemTyExpr, typeAtom? env resultTyExpr with
        | some collectionTy, some itemTy, some resultTy =>
            some {
              collectionTy := collectionTy,
              itemTy := itemTy,
              resultTy := resultTy,
              collection := collection,
              init := init,
              body := body
            }
        | _, _, _ => none
      else
        none
  | _, _ => none

structure ForInStepBody where
  done : Expr
  value : Expr

def boolLiteralExpr (value : Bool) : Expr :=
  if value then .const ``Bool.true [] else .const ``Bool.false []

def mkIteExpr (ty cond inst thenExpr elseExpr : Expr) : Expr :=
  .app
    (.app
      (.app
        (.app
          (.app (.const ``ite []) ty)
          cond)
        inst)
      thenExpr)
    elseExpr

def wrapForInStepLet
    (name : Name)
    (type value : Expr)
    (nondep : Bool)
    (step : ForInStepBody) :
    ForInStepBody :=
  {
    done := .letE name type value step.done nondep
    value := .letE name type value step.value nondep
  }

partial def betaReduceLocalExpr (fuel : Nat) (expr : Expr) : Expr :=
  match fuel with
  | 0 => expr
  | fuel + 1 =>
      let reduce := betaReduceLocalExpr fuel
      match expr.consumeMData with
      | .app _ _ =>
          let (fn, args) := appFnArgs expr
          let reducedFn := reduce fn
          let reducedArgs := args.map reduce
          let rec applyReduced (fn : Expr) : List Expr → Expr
            | [] => fn
            | arg :: rest =>
                match fn.consumeMData with
                | .lam _ _ body _ => applyReduced (reduce (body.instantiate1 arg)) rest
                | _ => rebuildApp fn (arg :: rest)
          applyReduced reducedFn reducedArgs
      | .lam name type body bi => .lam name (reduce type) (reduce body) bi
      | .forallE name type body bi => .forallE name (reduce type) (reduce body) bi
      | .letE name type value body nondep =>
          .letE name (reduce type) (reduce value) (reduce body) nondep
      | .mdata data body => .mdata data (reduce body)
      | .proj typeName index body => .proj typeName index (reduce body)
      | other => other

partial def forInStepBody? (resultTy : Ty) (expr : Expr) : Except String ForInStepBody := do
  match expr.consumeMData with
  | .letE name type value body nondep => do
      match value.consumeMData with
      | .lam _ _ _ _ =>
          forInStepBody? resultTy (betaReduceLocalExpr 32 (body.instantiateRev #[value]))
      | _ =>
          .ok (wrapForInStepLet name type value nondep (← forInStepBody? resultTy body))
  | expr =>
      match appFnArgs expr with
      | (.const ``ForInStep.yield _, args) =>
          match args.reverse with
          | value :: _ => .ok { done := boolLiteralExpr false, value := value }
          | _ => .error "unsupported ForInStep.yield application"
      | (.const ``ForInStep.done _, args) =>
          match args.reverse with
          | value :: _ => .ok { done := boolLiteralExpr true, value := value }
          | _ => .error "unsupported ForInStep.done application"
      | (.const ``Pure.pure _, args) =>
          match idPureArg? (.const ``Pure.pure []) args with
          | some value => forInStepBody? resultTy value
          | none => .error "unsupported for-in pure step"
      | (.const ``Bind.bind _, args) =>
          match idBindArgs? (.const ``Bind.bind []) args with
          | some (value, bindFn) =>
              match bindFn.consumeMData with
              | .lam name type body _ =>
                  forInStepBody? resultTy (.letE name type value body true)
              | _ => .error "unsupported for-in body bind function"
          | none => .error "unsupported for-in body bind"
      | (.const ``ite _, [_ty, condExpr, inst, thenExpr, elseExpr]) =>
          match tyExpr? resultTy with
          | some resultTyExpr => do
              let thenStep ← forInStepBody? resultTy thenExpr
              let elseStep ← forInStepBody? resultTy elseExpr
              .ok {
                done :=
                  mkIteExpr (.const ``Bool []) condExpr inst thenStep.done elseStep.done
                value :=
                  mkIteExpr resultTyExpr condExpr inst thenStep.value elseStep.value
              }
          | none => .error s!"unsupported conditional for-in accumulator type: {reprStr resultTy}"
      | _ => .error s!"unsupported for-in body: {expr}"

partial def listLiteralItems? (env : Environment) (expr : Expr) : Option (Ty × List Expr) :=
  match appFnArgs expr with
  | (.const ``List.nil _, [itemTy]) =>
      typeAtom? env itemTy |>.map (fun ty => (ty, []))
  | (.const ``List.cons _, [itemTy, head, tail]) =>
      match typeAtom? env itemTy, listLiteralItems? env tail with
      | some ty, some (tailTy, items) =>
          if ty == tailTy then
            some (ty, head :: items)
          else
            none
      | _, _ => none
  | _ => none

def isMatcherName (candidate : Name) : Bool :=
  match candidate with
  | .str _ component => component.startsWith "match_"
  | _ => false

def generatedMatcherScrutineeArg? (env : Environment) (name : Name) (args : List Expr) :
    Option (Nat × Ty) :=
  if !isMatcherName name then
    none
  else
    match env.find? name with
    | some info =>
        let domains := (peelForall info.type).fst
        let rec loop (index : Nat) : List Expr → Option (Nat × Ty)
          | [] => none
          | domain :: rest =>
              let instantiated := domain.instantiateRev (args.take index).toArray
              match typeAtom? env instantiated with
              | some ty => some (index, ty)
              | none => loop (index + 1) rest
        loop 0 domains
    | none => none

def generatedMatcherVariantScrutineeArg?
    (env : Environment)
    (name : Name)
    (args : List Expr)
    (targetName? : Option Name) :
    Option (Nat × Ty) :=
  if !isMatcherName name then
    none
  else
    match env.find? name with
    | some info =>
        let domains := (peelForall info.type).fst
        let rec loop (index : Nat) : List Expr → Option (Nat × Ty)
          | [] => none
          | domain :: rest =>
              let instantiated := domain.instantiateRev (args.take index).toArray
              match typeAtom? env instantiated with
              | some ty =>
                  let matchesTarget :=
                    match targetName?, ty with
                    | some targetName, .variant typeName _ _ => targetName == typeName
                    | some targetName, .recVariant typeName _ => targetName == typeName
                    | none, .variant _ _ _ => true
                    | none, .recVariant _ _ => true
                    | _, _ => false
                  if matchesTarget then
                    some (index, ty)
                  else
                    loop (index + 1) rest
              | none => loop (index + 1) rest
        loop 0 domains
    | none => none

def takeLast? {α : Type} (count : Nat) (items : List α) : Option (List α) :=
  if items.length < count then
    none
  else
    some (items.drop (items.length - count))

def optionMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  let optionArmKind? (optionTy payloadTy : Ty) (arm : Expr) : Option Bool :=
    match arm.consumeMData with
    | .lam _ domain _ _ =>
        match typeAtom? env domain with
        | some .unit => some false
        | some ty =>
            if ty == payloadTy then
              some true
            else if ty == optionTy then
              some false
            else
              none
        | none => none
    | _ => none
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Option.casesOn || name == ``Option.rec then
        match args.reverse with
        | someArm :: noneArm :: scrutinee :: _ => some (scrutinee, noneArm, someArm)
        | _ => none
      else
        match generatedMatcherScrutineeArg? env name args with
        | some (scrutineeIndex, optionTy) =>
            match optionPayloadType? optionTy, args[scrutineeIndex]?,
                args.drop (scrutineeIndex + 1) with
            | some payloadTy, some scrutinee, [firstArm, secondArm] =>
                match optionArmKind? optionTy payloadTy firstArm,
                    optionArmKind? optionTy payloadTy secondArm with
                | some false, some true => some (scrutinee, firstArm, secondArm)
                | some true, some false => some (scrutinee, secondArm, firstArm)
                | _, _ => none
            | _, _, _ => none
        | _ => none
  | _ => none

partial def exceptArmTarget? (expr : Expr) : Option Bool :=
  match expr.consumeMData with
  | .forallE _ _ body _ => exceptArmTarget? body
  | .app _ value =>
      match appFnArgs value with
      | (.const ``Except.error _, _) => some false
      | (.const ``Except.ok _, _) => some true
      | _ => none
  | _ => none

def exceptMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  let generatedExceptArgs? (name : Name) : Option (Expr × Expr × Expr) :=
    match env.find? name, args with
    | some info, [_motive, scrutinee, firstArm, secondArm] =>
        match (peelForall info.type).fst with
        | _motiveTy :: _scrutineeTy :: firstArmTy :: secondArmTy :: _ =>
            match exceptArmTarget? firstArmTy, exceptArmTarget? secondArmTy with
            | some false, some true => some (scrutinee, firstArm, secondArm)
            | some true, some false => some (scrutinee, secondArm, firstArm)
            | _, _ => none
        | _ => none
    | _, _ => none
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Except.casesOn then
        match args.reverse with
        | okArm :: errorArm :: scrutinee :: _ => some (scrutinee, errorArm, okArm)
        | _ => none
      else if name == ``Except.rec then
        match args.reverse with
        | scrutinee :: okArm :: errorArm :: _ => some (scrutinee, errorArm, okArm)
        | _ => none
      else
        generatedExceptArgs? name
  | _ => none

partial def boolArmTarget? (expr : Expr) : Option Bool :=
  match expr.consumeMData with
  | .forallE _ _ body _ => boolArmTarget? body
  | .app _ value =>
      if isConst ``Bool.false value then
        some false
      else if isConst ``Bool.true value then
        some true
      else
        none
  | _ => none

def boolMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Bool.casesOn then
        match args with
        | [_motive, scrutinee, falseArm, trueArm] => some (scrutinee, falseArm, trueArm)
        | _ => none
      else
        match generatedMatcherScrutineeArg? env name args with
        | some (scrutineeIndex, .bool) =>
            match env.find? name, args[scrutineeIndex]?, args.drop (scrutineeIndex + 1) with
            | some info, some scrutinee, [firstArm, secondArm] =>
                match (peelForall info.type).fst.drop (scrutineeIndex + 1) with
                | firstArmTy :: secondArmTy :: _ =>
                    match boolArmTarget? firstArmTy, boolArmTarget? secondArmTy with
                    | some false, some true => some (scrutinee, firstArm, secondArm)
                    | some true, some false => some (scrutinee, secondArm, firstArm)
                    | _, _ => none
                | _ => none
            | _, _, _ => none
        | _ => none
  | _ => none

def natMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr × Expr) :=
  let natArmKind? (arm : Expr) : Option Bool :=
    match arm.consumeMData with
    | .lam _ domain _ _ =>
        match typeAtom? env domain with
        | some .unit => some false
        | some .nat => some true
        | _ => none
    | _ => none
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Nat.casesOn then
        match args with
        | [_motive, scrutinee, zeroArm, succArm] => some (scrutinee, zeroArm, succArm)
        | _ => none
      else
        match generatedMatcherScrutineeArg? env name args with
        | some (scrutineeIndex, .nat) =>
            match args[scrutineeIndex]?, args.drop (scrutineeIndex + 1) with
            | some scrutinee, [firstArm, secondArm] =>
                match natArmKind? firstArm, natArmKind? secondArm with
                | some false, some true => some (scrutinee, firstArm, secondArm)
                | some true, some false => some (scrutinee, secondArm, firstArm)
                | _, _ => none
            | _, _ => none
        | _ => none
  | _ => none

def productMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``Prod.casesOn then
        match args.reverse with
        | arm :: scrutinee :: _ => some (scrutinee, arm)
        | _ => none
      else if name == ``Prod.rec then
        match args.reverse with
        | scrutinee :: arm :: _ => some (scrutinee, arm)
        | _ => none
      else
        match generatedMatcherScrutineeArg? env name args with
        | some (scrutineeIndex, .product _ _) =>
            match args[scrutineeIndex]?, args.drop (scrutineeIndex + 1) with
            | some scrutinee, [arm] => some (scrutinee, arm)
            | _, _ => none
        | _ => none
  | _ => none

def psumMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Ty × Ty × Expr × Expr × Expr) :=
  match fn.consumeMData with
  | .const name _ =>
      if name == ``PSum.casesOn then
        match args with
        | leftTyExpr :: rightTyExpr :: _motive :: scrutinee :: leftArm :: rightArm :: [] => do
            let leftTy ← typeAtom? env leftTyExpr
            let rightTy ← typeAtom? env rightTyExpr
            some (leftTy, rightTy, scrutinee, leftArm, rightArm)
        | _ => none
      else
        none
  | _ => none

def structureMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (Name × List (Option Ty) × Expr × Expr) :=
  let directMatcher? (name : Name) : Option (Name × List (Option Ty) × Expr × Expr) :=
    match env.find? name with
    | some (.recInfo recInfo) =>
        match recInfo.all with
        | structName :: [] =>
            match structureCtorInfo? env structName with
            | some ctorInfo =>
                let params? := (args.take ctorInfo.numParams).mapM (typeAtom? env)
                let rest := args.drop ctorInfo.numParams
                match params?.bind (structureFieldKindsWithParams? env structName) with
                | some fieldKinds =>
                    if name == .str structName "casesOn" ||
                        name == .str structName "recOn" then
                      match rest.reverse with
                      | arm :: scrutinee :: _ => some (structName, fieldKinds, scrutinee, arm)
                      | _ => none
                    else if name == .str structName "rec" then
                      match rest.reverse with
                      | scrutinee :: arm :: _ => some (structName, fieldKinds, scrutinee, arm)
                      | _ => none
                    else
                      none
                | none => none
            | none => none
        | _ => none
    | _ => none
  let generatedMatcher? (name : Name) : Option (Name × List (Option Ty) × Expr × Expr) :=
    match generatedMatcherScrutineeArg? env name args with
    | some (scrutineeIndex, .struct _ _ _) =>
        match env.find? name with
        | some info =>
            let domains := (peelForall info.type).fst
            match domains[scrutineeIndex]?, args[scrutineeIndex]?, args.drop (scrutineeIndex + 1) with
            | some domain, some scrutinee, [arm] =>
                let instantiated := domain.instantiateRev (args.take scrutineeIndex).toArray
                match structureTypeLayout? env instantiated with
                | some (structName, fieldKinds) => some (structName, fieldKinds, scrutinee, arm)
                | none => none
            | _, _, _ => none
        | none => none
    | _ => none
  match fn.consumeMData with
  | .const name _ =>
      match directMatcher? name with
      | some result => some result
      | none => generatedMatcher? name
  | _ => none

partial def variantArmCtorName? (env : Environment) (expr : Expr) : Option Name :=
  match expr.consumeMData with
  | .const ctorName _ =>
      match anyVariantConstructor? env ctorName with
      | some _ => some ctorName
      | none =>
          match env.find? ctorName with
          | some (.ctorInfo _) => some ctorName
          | _ => none
  | .forallE _ _ body _ => variantArmCtorName? env body
  | .mdata _ body => variantArmCtorName? env body
  | .app _ value =>
      match appFnArgs expr with
      | (.const ctorName _, _) =>
          match anyVariantConstructor? env ctorName with
          | some _ => some ctorName
          | none =>
              match env.find? ctorName with
              | some (.ctorInfo _) => some ctorName
              | _ => none
      | _ =>
          match variantArmCtorName? env value with
          | some ctorName => some ctorName
          | none =>
              match expr.consumeMData with
              | .app fn _ => variantArmCtorName? env fn
              | _ => none
  | _ => none

def reorderVariantArms?
    (ctorNames : List Name)
    (typedArms : List (Name × Expr)) :
    Option (List Expr) :=
  ctorNames.mapM fun ctorName =>
    typedArms.find? (fun item => item.fst == ctorName) |>.map Prod.snd

structure VariantMatch where
  layout : VariantLayout
  scrutinee : Expr
  arms : List Expr
  fallbackArms : List Bool := []
  prePostArgCount : Nat := 0

def variantMatcherInfo?
    (env : Environment)
    (fn : Expr)
    (args : List Expr)
    (targetName? : Option Name := none)
    (postArgCount? : Option Nat := none) :
    Option VariantMatch :=
  let directMatcher? (name : Name) : Option VariantMatch :=
    match env.find? name with
    | some (.recInfo recInfo) =>
        match recInfo.all with
        | typeName :: [] =>
            let targetMatches :=
              match targetName? with
              | some targetName => targetName == typeName
              | none => true
            if targetMatches then
              let params? :=
                match env.find? typeName with
                | some (.inductInfo info) => (args.take info.numParams).mapM (typeAtom? env)
                | _ => none
              let rest :=
                match env.find? typeName with
                | some (.inductInfo info) => args.drop info.numParams
                | _ => args
              match params?.bind (fun params =>
                  match variantLayoutWithParams? env typeName params with
                  | some layout => some layout
                  | none => recursiveVariantLayout? env typeName params) with
              | some layout =>
                  let ctorCount := layout.ctors.length
                  if name == .str typeName "casesOn" || name == .str typeName "recOn" then
                    match rest with
                    | _motive :: scrutinee :: rest =>
                        if rest.length == ctorCount then
                          some { layout := layout, scrutinee := scrutinee, arms := rest }
                        else
                          none
                    | _ => none
                  else if name == .str typeName "rec" then
                    match rest with
                    | _motive :: rest =>
                        let arms := rest.take ctorCount
                        match rest.drop ctorCount with
                        | scrutinee :: [] =>
                            if arms.length == ctorCount then
                              some { layout := layout, scrutinee := scrutinee, arms := arms }
                            else
                              none
                        | _ => none
                    | _ => none
                  else
                    none
              | none => none
            else
              none
        | _ => none
    | _ => none
  let generatedMatcher? (name : Name) : Option VariantMatch :=
    let fallbackArm? (layout : VariantLayout) (armType : Expr) : Option Bool :=
      match armType.consumeMData with
      | .forallE _ domain _ _ =>
          match typeAtom? env domain with
          | some (.variant typeName params _) =>
              some (typeName == layout.name && params == layout.params)
          | some (.recVariant typeName params) =>
              some (typeName == layout.name && params == layout.params)
          | _ => none
      | _ => none
    let orderSparseArms (layout : VariantLayout) (arms armTypes : List Expr) :
        Option (List Expr × List Bool) :=
      let entries? :=
        (armTypes.zip arms).mapM fun item =>
          match variantArmCtorName? env item.fst with
          | some ctorName => some (some ctorName, item.snd)
          | none =>
              match fallbackArm? layout item.fst with
              | some true => some (none, item.snd)
              | _ => none
      match entries? with
      | some entries =>
          let fallbackArms := entries.filterMap fun item =>
            match item.fst with
            | none => some item.snd
            | some _ => none
          match fallbackArms with
          | [fallbackArm] =>
              let ctorArms := entries.filterMap fun item =>
                match item.fst with
                | some ctorName => some (ctorName, item.snd)
                | none => none
              let ordered :=
                layout.ctors.map fun ctor =>
                  match ctorArms.find? (fun item => item.fst == ctor.name) with
                  | some item => (item.snd, false)
                  | none => (fallbackArm, true)
              some (ordered.map Prod.fst, ordered.map Prod.snd)
          | _ => none
      | none => none
    let orderArms (info : ConstantInfo) (scrutineeIndex : Nat) (layout : VariantLayout)
        (scrutinee : Expr) (afterScrutinee : List Expr) : Option VariantMatch :=
      let ctorCount := layout.ctors.length
      let sparseResult? : Option VariantMatch :=
        if postArgCount?.isSome then
          none
        else
          match orderSparseArms layout afterScrutinee
              ((peelForall info.type).fst.drop (scrutineeIndex + 1)) with
          | some (orderedArms, fallbackArms) =>
              some {
                layout := layout,
                scrutinee := scrutinee,
                arms := orderedArms,
                fallbackArms := fallbackArms
              }
          | none => none
      match takeLast? ctorCount afterScrutinee,
          takeLast? ctorCount ((peelForall info.type).fst.drop (scrutineeIndex + 1)) with
      | some arms, some armTypes =>
          let typedArms? :=
            (armTypes.zip arms).mapM fun item =>
              variantArmCtorName? env item.fst |>.map fun ctorName =>
                (ctorName, item.snd)
          match typedArms? with
          | some typedArms =>
              match reorderVariantArms? (layout.ctors.map (fun ctor => ctor.name)) typedArms with
              | some orderedArms =>
                  let postAfterCount := afterScrutinee.length - ctorCount
                  match postArgCount? with
                  | some postArgCount =>
                      if postAfterCount <= postArgCount then
                        some {
                          layout := layout,
                          scrutinee := scrutinee,
                          arms := orderedArms,
                          fallbackArms := List.replicate orderedArms.length false,
                          prePostArgCount := postArgCount - postAfterCount
                        }
                      else
                        none
                  | none =>
                      some {
                        layout := layout,
                        scrutinee := scrutinee,
                        arms := orderedArms,
                        fallbackArms := List.replicate orderedArms.length false
                      }
              | none => sparseResult?
          | none => sparseResult?
      | _, _ => sparseResult?
    match generatedMatcherVariantScrutineeArg? env name args targetName?, env.find? name with
    | some (scrutineeIndex, .variant _ _ _), some info =>
        let domains := (peelForall info.type).fst
        match domains[scrutineeIndex]?, args[scrutineeIndex]? with
        | some domain, some scrutinee =>
            let instantiated := domain.instantiateRev (args.take scrutineeIndex).toArray
            match variantTypeLayout? env instantiated with
            | some layout =>
                orderArms info scrutineeIndex layout scrutinee (args.drop (scrutineeIndex + 1))
            | none => none
        | _, _ => none
    | some (scrutineeIndex, .recVariant typeName typeParams), some info =>
        match recursiveVariantLayout? env typeName typeParams, args[scrutineeIndex]? with
        | some layout, some scrutinee =>
            orderArms info scrutineeIndex layout scrutinee (args.drop (scrutineeIndex + 1))
        | _, _ => none
    | _, _ => none
  match fn.consumeMData with
  | .const name _ =>
      match directMatcher? name with
      | some result => some result
      | none => generatedMatcher? name
  | _ => none

def variantMatcherArgs? (env : Environment) (fn : Expr) (args : List Expr) :
    Option (VariantLayout × Expr × List Expr × List Bool) :=
  variantMatcherInfo? env fn args |>.map fun info =>
    (info.layout, info.scrutinee, info.arms, info.fallbackArms)

end LeanExe.Extract.Core
