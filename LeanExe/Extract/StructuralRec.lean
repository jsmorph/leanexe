import Lean
import Init.Data.ByteArray.Extra
import LeanExe.Extract.Demand
import LeanExe.IR.Core

open Lean

namespace LeanExe.Extract.Core

def brecOnName (typeName : Name) : Name :=
  .str typeName "brecOn"

def brecOnTypeName? : Name → Option Name
  | .str typeName "brecOn" => some typeName
  | _ => none

structure StructuralRecApplication where
  fn : Expr
  typeName : Name
  typeParams : List Ty
  typeArgExprs : List Expr
  motive : Expr
  scrutinee : Expr
  step : Expr
  postArgs : List Expr

structure StructuralExpressionRecShape where
  fn : Expr
  typeName : Name
  typeParams : List Ty
  typeArgExprs : List Expr
  dynamicPostArgTypes : List Ty
  captureIndices : List Nat
  captureTypes : List Ty
  motive : Expr
  scrutinee : Expr
  step : Expr
  postArgs : List Expr
  resultTy : Ty

def rawStructuralRecApplication? (env : Environment) (expr : Expr) :
    Option StructuralRecApplication :=
  match appFnArgs expr with
  | (fn@(.const candidate _), args) => do
      let typeName ← brecOnTypeName? candidate
      let info ← userRecursiveInductiveInfo? env typeName
      let typeArgExprs := args.take info.numParams
      let typeParams ← typeArgExprs.mapM (typeAtom? env)
      match args.drop info.numParams with
      | motive :: scrutinee :: step :: postArgs =>
          some {
            fn := fn,
            typeName := typeName,
            typeParams := typeParams,
            typeArgExprs := typeArgExprs,
            motive := motive,
            scrutinee := scrutinee,
            step := step,
            postArgs := postArgs
          }
      | _ => none
  | _ => none

partial def containsSupportedBrecOn (env : Environment) (expr : Expr) : Bool :=
  expr.getUsedConstants.any fun name =>
    match brecOnTypeName? name with
    | some typeName => (userRecursiveInductiveInfo? env typeName).isSome
    | none => false

partial def peelLambdaBody (expr : Expr) : Expr :=
  match expr.consumeMData with
  | .lam _ _ body _ => peelLambdaBody body
  | body => body

partial def transparentStructuralAdapterAt? (env : Environment) (fuel : Nat) (expr : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      let body := peelLambdaBody expr
      match body.consumeMData with
      | .proj _ _ _ => true
      | _ =>
          match appFnArgs body with
          | (.const name _, _) =>
              match env.find? name with
              | some (.ctorInfo _) => true
              | some info =>
                  match info.value? with
                  | some value =>
                      containsSupportedBrecOn env value ||
                        transparentStructuralAdapterAt? env fuel value
                  | none => false
              | none => false
          | _ => false

def transparentStructuralAdapter? (env : Environment) (expr : Expr) : Bool :=
  transparentStructuralAdapterAt? env 8 expr

def structuralUnfoldCandidate? (env : Environment) (root name : Name) (value : Expr) : Bool :=
  name.getRoot != root &&
    !blocksTransparentSpecialization name &&
    (containsSupportedBrecOn env value || transparentStructuralAdapter? env value)

def ctorProjection? (env : Environment) (typeName : Name) (index : Nat) (expr : Expr) :
    Option Expr :=
  match appFnArgs expr with
  | (.const ctorName _, args) =>
      match env.find? ctorName with
      | some (.ctorInfo info) =>
          if info.induct == typeName then
            args[info.numParams + index]?
          else
            none
      | _ => none
  | _ => none

partial def forallBinderInfos (expr : Expr) : List BinderInfo :=
  match expr.consumeMData with
  | .forallE _ _ body info => info :: forallBinderInfos body
  | _ => []

def shouldNormalizeStructuralArg : BinderInfo → Bool
  | .default => false
  | _ => true

partial def structuralNormalizeExpr
    (env : Environment)
    (root : Name)
    (fuel : Nat)
    (expr : Expr) : Expr :=
  match fuel with
  | 0 => expr
  | fuel + 1 =>
      let normalize := structuralNormalizeExpr env root fuel
      let reduceApp (fn : Expr) (args : List Expr) : Expr :=
        let rec applyNormalized (fn : Expr) : List Expr → Expr
          | [] => fn
          | arg :: rest =>
              match fn.consumeMData with
              | .lam _ _ body _ => applyNormalized (normalize (body.instantiate1 arg)) rest
              | _ => rebuildApp fn (arg :: rest)
        let applied := applyNormalized fn args
        match appFnArgs applied with
        | (.const name _, appliedArgs) =>
            match env.find? name with
            | some info =>
                match info.value? with
                | some value =>
                    if structuralUnfoldCandidate? env root name value then
                      normalize (rebuildApp value appliedArgs)
                    else
                      applied
                | none => applied
            | none => applied
        | _ => applied
      match expr.consumeMData with
      | .app _ _ =>
          match appFnArgs expr with
          | (.const candidate _, _) =>
              if (brecOnTypeName? candidate).any (fun typeName =>
                  (userRecursiveInductiveInfo? env typeName).isSome) then
                expr
              else
                let (fn, args) := appFnArgs expr
                let normalizedArgs :=
                  match fn.consumeMData with
                  | .const name _ =>
                      match env.find? name with
                      | some info =>
                          let binders := forallBinderInfos info.type
                          args.zipIdx.map fun item =>
                            match binders[item.snd]? with
                            | some binder =>
                                if shouldNormalizeStructuralArg binder then
                                  normalize item.fst
                                else
                                  item.fst
                            | none => item.fst
                      | none => args
                  | _ => args.map normalize
                reduceApp (normalize fn) normalizedArgs
          | _ =>
              let (fn, args) := appFnArgs expr
              reduceApp (normalize fn) (args.map normalize)
      | .lam name type body bi => .lam name (normalize type) (normalize body) bi
      | .forallE name type body bi => .forallE name (normalize type) (normalize body) bi
      | .letE name type value body nondep =>
          .letE name (normalize type) (normalize value) (normalize body) nondep
      | .mdata data body => .mdata data (normalize body)
      | .proj typeName index body =>
          let normalizedBody := normalize body
          match ctorProjection? env typeName index normalizedBody with
          | some projected => normalize projected
          | none => .proj typeName index normalizedBody
      | other => other

def structuralRecApplication?
    (env : Environment)
    (root : Name)
    (expr : Expr) :
    Option StructuralRecApplication :=
  rawStructuralRecApplication? env (structuralNormalizeExpr env root 32 expr)

def structuralPostArgTypesAndResult?
    (env : Environment)
    (root : Name)
    (motive scrutinee : Expr)
    (postArgs : List Expr) :
    Option (List Ty × Ty) := do
  let motiveResult :=
    structuralNormalizeExpr env root 16 (rebuildApp motive [scrutinee])
  let rec loop :
      List Expr → Expr → List Ty → Option (List Ty × Expr)
    | [], resultExpr, acc => some (acc.reverse, resultExpr)
    | arg :: restArgs, resultExpr, acc =>
        match resultExpr.consumeMData with
        | .forallE _ domain body _ =>
            let nextResult := structuralNormalizeExpr env root 16 (body.instantiate1 arg)
            if isDirectLambda arg then
              if containsBVar 0 arg then
                none
              else
                loop restArgs nextResult acc
            else
              match typeAtom? env domain with
              | some ty =>
                  if supportedInternalParamType ty then
                    loop restArgs nextResult (ty :: acc)
                  else
                    none
              | none => none
        | _ => none
  let (dynamicTypes, resultExpr) ← loop postArgs motiveResult []
  let resultExpr := structuralNormalizeExpr env root 16 resultExpr
  let resultTy ← typeAtom? env resultExpr
  some (dynamicTypes, resultTy)

def insertSortedNat (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: rest =>
      if value == head then
        head :: rest
      else if value < head then
        value :: head :: rest
      else
        head :: insertSortedNat value rest

partial def looseBVarIndicesAt (depth : Nat) (expr : Expr) (acc : List Nat) : List Nat :=
  match expr.consumeMData with
  | .bvar index =>
      if index < depth then
        acc
      else
        insertSortedNat (index - depth) acc
  | .app fn arg =>
      looseBVarIndicesAt depth arg (looseBVarIndicesAt depth fn acc)
  | .lam _ type body _ =>
      looseBVarIndicesAt (depth + 1) body (looseBVarIndicesAt depth type acc)
  | .forallE _ type body _ =>
      looseBVarIndicesAt (depth + 1) body (looseBVarIndicesAt depth type acc)
  | .letE _ type value body _ =>
      looseBVarIndicesAt (depth + 1) body
        (looseBVarIndicesAt depth value (looseBVarIndicesAt depth type acc))
  | .mdata _ body => looseBVarIndicesAt depth body acc
  | .proj _ _ body => looseBVarIndicesAt depth body acc
  | _ => acc

def looseBVarIndices (expr : Expr) : List Nat :=
  looseBVarIndicesAt 0 expr []

def structuralRecCaptureIndices? (app : StructuralRecApplication) : Option (List Nat) :=
  let relevantPostArgs := app.postArgs.filter isDirectLambda
  let indices :=
    relevantPostArgs.foldl
      (fun acc arg => looseBVarIndicesAt 0 arg acc)
      (looseBVarIndicesAt 0 app.step (looseBVarIndices app.motive))
  match app.scrutinee.consumeMData with
  | .bvar scrutineeIndex =>
      if indices.contains scrutineeIndex then none else some indices
  | _ => some indices

def captureTypes? (localTypes : List (Option Ty)) (captureIndices : List Nat) :
    Option (List Ty) :=
  captureIndices.mapM fun index => do
    let ty ← localTypes[index]? |>.join
    if supportedInternalParamType ty then some ty else none

def expressionStructuralRecShapeWithLocalTypes?
    (env : Environment)
    (root : Name)
    (localTypes : List (Option Ty))
    (expr : Expr) :
    Option StructuralExpressionRecShape :=
  match structuralRecApplication? env root expr with
  | some app => do
      let captureIndices ← structuralRecCaptureIndices? app
      let captureTypes ← captureTypes? localTypes captureIndices
      let (dynamicPostArgTypes, resultTy) ←
        structuralPostArgTypesAndResult? env root app.motive app.scrutinee app.postArgs
      if supportedInternalResultType resultTy then
        some {
          fn := app.fn,
          typeName := app.typeName,
          typeParams := app.typeParams,
          typeArgExprs := app.typeArgExprs,
          dynamicPostArgTypes := dynamicPostArgTypes,
          captureIndices := captureIndices,
          captureTypes := captureTypes,
          motive := app.motive,
          scrutinee := app.scrutinee,
          step := app.step,
          postArgs := app.postArgs,
          resultTy := resultTy
        }
      else
        none
  | none => none

def expressionStructuralRecShape?
    (env : Environment)
    (root : Name)
    (expr : Expr) :
    Option StructuralExpressionRecShape :=
  match structuralRecApplication? env root expr with
  | some app => do
      let captureIndices ← structuralRecCaptureIndices? app
      let (dynamicPostArgTypes, resultTy) ←
        structuralPostArgTypesAndResult? env root app.motive app.scrutinee app.postArgs
      if supportedInternalResultType resultTy then
        some {
          fn := app.fn,
          typeName := app.typeName,
          typeParams := app.typeParams,
          typeArgExprs := app.typeArgExprs,
          dynamicPostArgTypes := dynamicPostArgTypes,
          captureIndices := captureIndices,
          captureTypes := [],
          motive := app.motive,
          scrutinee := app.scrutinee,
          step := app.step,
          postArgs := app.postArgs,
          resultTy := resultTy
        }
      else
        none
  | none => none

def syntheticMatchesShape (synth : SyntheticFunction) (shape : StructuralExpressionRecShape) :
    Bool :=
  synth.typeName == shape.typeName &&
    synth.typeParams == shape.typeParams &&
    synth.sig.result == shape.resultTy &&
    synth.dynamicPostArgTypes == shape.dynamicPostArgTypes &&
    synth.captureIndices == shape.captureIndices &&
    (shape.captureTypes.isEmpty || synth.captureTypes == shape.captureTypes) &&
    synth.sig.params ==
      (.recVariant shape.typeName shape.typeParams ::
        (shape.dynamicPostArgTypes ++ synth.captureTypes)) &&
    synth.motive == shape.motive &&
    synth.step == shape.step &&
    synth.postArgs == shape.postArgs

def syntheticForShape? (ctx : Context) (shape : StructuralExpressionRecShape) :
    Option SyntheticFunction :=
  ctx.synthetics.toList.find? (fun synth => syntheticMatchesShape synth shape)

def captureParamIndex? (captureIndices : List Nat) (index : Nat) : Option Nat :=
  let rec loop (position : Nat) : List Nat → Option Nat
    | [] => none
    | head :: rest =>
        if head == index then some position else loop (position + 1) rest
  loop 0 captureIndices

partial def rebaseCapturedBVarsAt
    (captureIndices : List Nat)
    (captureCount : Nat)
    (depth : Nat)
    (expr : Expr) :
    Option Expr :=
  match expr.consumeMData with
  | .bvar index =>
      if index < depth then
        some (.bvar index)
      else
        let sourceIndex := index - depth
        match captureParamIndex? captureIndices sourceIndex with
        | some position => some (.bvar (depth + captureCount - 1 - position))
        | none => none
  | .app fn arg => do
      let fn ← rebaseCapturedBVarsAt captureIndices captureCount depth fn
      let arg ← rebaseCapturedBVarsAt captureIndices captureCount depth arg
      some (.app fn arg)
  | .lam name type body info => do
      let type ← rebaseCapturedBVarsAt captureIndices captureCount depth type
      let body ← rebaseCapturedBVarsAt captureIndices captureCount (depth + 1) body
      some (.lam name type body info)
  | .forallE name type body info => do
      let type ← rebaseCapturedBVarsAt captureIndices captureCount depth type
      let body ← rebaseCapturedBVarsAt captureIndices captureCount (depth + 1) body
      some (.forallE name type body info)
  | .letE name type value body nondep => do
      let type ← rebaseCapturedBVarsAt captureIndices captureCount depth type
      let value ← rebaseCapturedBVarsAt captureIndices captureCount depth value
      let body ← rebaseCapturedBVarsAt captureIndices captureCount (depth + 1) body
      some (.letE name type value body nondep)
  | .mdata data body => do
      let body ← rebaseCapturedBVarsAt captureIndices captureCount depth body
      some (.mdata data body)
  | .proj typeName index body => do
      let body ← rebaseCapturedBVarsAt captureIndices captureCount depth body
      some (.proj typeName index body)
  | other => some other

def rebaseCapturedBVars (captureIndices : List Nat) (expr : Expr) : Option Expr :=
  rebaseCapturedBVarsAt captureIndices captureIndices.length 0 expr

def structuralExpressionSyntheticPostArgs
    (captureIndices : List Nat)
    (captureCount : Nat)
    (postArgs : List Expr) :
    Option (List Expr) :=
  let rec loop (remaining : Nat) : List Expr → Option (List Expr)
    | [] => some []
    | arg :: rest => do
        let nextRemaining := if isDirectLambda arg then remaining else remaining - 1
        let rest ← loop nextRemaining rest
        if isDirectLambda arg then
          let rebased ← rebaseCapturedBVarsAt captureIndices captureCount 0 arg
          some (rebased :: rest)
        else
          some (.bvar (captureCount + remaining - 1) :: rest)
  loop (postArgs.filter (fun arg => !isDirectLambda arg)).length postArgs

def structuralExpressionSyntheticValue? (shape : StructuralExpressionRecShape) : Option Expr := do
  if shape.captureIndices.length != shape.captureTypes.length then
    none
  else
  let domain := rebuildApp (.const shape.typeName []) shape.typeArgExprs
  let dynamicDomains ← (shape.dynamicPostArgTypes ++ shape.captureTypes).mapM tyExpr?
  let captureCount := shape.captureTypes.length
  let scrutineeIndex := shape.dynamicPostArgTypes.length + captureCount
  let motive ← rebaseCapturedBVars shape.captureIndices shape.motive
  let step ← rebaseCapturedBVars shape.captureIndices shape.step
  let postArgs ←
    structuralExpressionSyntheticPostArgs shape.captureIndices captureCount shape.postArgs
  let body :=
    rebuildApp shape.fn
      (shape.typeArgExprs ++
        [motive, .bvar scrutineeIndex, step] ++
        postArgs)
  let withDynamicArgs :=
    dynamicDomains.foldr (fun argType body => .lam `arg argType body .default) body
  some (.lam `xs domain withDynamicArgs .default)

def structuralExpressionCallExtraArgs (shape : StructuralExpressionRecShape) : List Expr :=
  shape.postArgs ++ shape.captureIndices.map Expr.bvar

structure StructuralStep where
  layout : VariantLayout
  arms : List Expr
  prePostArgCount : Nat

def structuralRecStepMatcher?
    (env : Environment)
    (typeName : Name)
    (_typeParams : List Ty)
    (postArgCount : Nat)
    (step : Expr) :
    Except String StructuralStep := do
  let stepBody ←
    match collectLambdas step (2 + postArgCount) with
    | some body => .ok body
    | none => .error s!"unsupported structural recursion step: {typeName}"
  match stepBody.consumeMData with
  | .app matcherExpr belowArg =>
      if !isBVar postArgCount belowArg then
        .error s!"unsupported structural recursion below argument: {typeName}"
      else
        let (matcherFn, matcherArgs) := appFnArgs matcherExpr
        match variantMatcherInfo? env matcherFn matcherArgs (some typeName) (some postArgCount) with
        | some info =>
            let layout := info.layout
            let scrutinee := info.scrutinee
            if info.fallbackArms.any id then
              .error s!"unsupported sparse structural recursion matcher: {typeName}"
            else if layout.name == typeName then
              if isBVar (postArgCount + 1) scrutinee then
                .ok {
                  layout := layout,
                  arms := info.arms,
                  prePostArgCount := info.prePostArgCount
                }
              else
                .error s!"unsupported structural recursion matcher scrutinee: {typeName}"
            else
              .error s!"structural recursion matcher type mismatch: {typeName}"
        | none => .error s!"unsupported structural recursion matcher: {typeName}"
  | _ => .error s!"unsupported structural recursion step body: {typeName}"

def structuralBelowForFields
    (functionName : Name)
    (capturedArgs : List ExtractedValue)
    (fields : List ExtractedValue) :
    StructuralBelow :=
  let fieldBelow (value : ExtractedValue) : StructuralBelow :=
    .pair (.call functionName value capturedArgs) .unit
  let rec loop : List ExtractedValue → StructuralBelow
    | [] => .unit
    | [value] => fieldBelow value
    | value :: rest => .pair (fieldBelow value) (loop rest)
  loop fields

def structuralBelowBinding
    (functionName : Name)
    (capturedArgs : List ExtractedValue)
    (typeName : Name)
    (typeParams : List Ty)
    (ctor : Name)
    (fieldKinds : List (Option Ty))
    (runtimeFields : List ExtractedValue) :
    Except String Binding := do
  let typedFields ← typedFieldsFromKinds ctor fieldKinds runtimeFields
  let recursiveFields :=
    typedFields.filter fun item =>
      match item.fst with
      | .recVariant candidate params => candidate == typeName && params == typeParams
      | _ => false
  match recursiveFields with
  | [] => .ok (.value (.scalar (.u64 0)))
  | fields =>
      .ok (.structuralBelow (structuralBelowForFields functionName capturedArgs (fields.map Prod.snd)))

inductive StructuralPostArg where
  | dynamic (ty : Ty) (binding : Binding)
  | staticLambda (expr : Expr)

def structuralPostArgIsDynamic : StructuralPostArg -> Bool
  | .dynamic _ _ => true
  | .staticLambda _ => false

def bindingValue? : Binding -> Option ExtractedValue
  | .value value => some value
  | _ => none

def structuralCapturedArgs
    (params : List Ty)
    (postPlans : List StructuralPostArg) :
    Except String (List ExtractedValue) :=
  if postPlans.any structuralPostArgIsDynamic then
    .ok []
  else
    (internalParamBindings params).drop 1 |>.mapM fun binding =>
      match bindingValue? binding with
      | some value => .ok value
      | none => .error "unsupported structural recursion captured argument"

def structuralPostArgs
    (params : List Ty)
    (postArgs : List Expr) :
    Except String (List StructuralPostArg) := do
  let paramTypes := params.reverse
  let paramBindings := (internalParamBindings params).reverse
  let rec loop :
      List Expr → List StructuralPostArg →
        Except String (List StructuralPostArg)
    | [], acc => .ok acc.reverse
    | arg :: restArgs, acc =>
        if isDirectLambda arg then
          loop restArgs (.staticLambda arg :: acc)
        else
          match arg.consumeMData with
          | .bvar index =>
              match paramTypes[index]?, paramBindings[index]? with
              | some ty, some binding =>
                  loop restArgs (.dynamic ty binding :: acc)
              | _, _ => .error "unsupported structural recursion carried argument initializer"
          | _ => .error "unsupported structural recursion carried argument initializer"
  loop postArgs []

inductive StructuralArmBinder where
  | runtime (expected : Option Ty) (binding : Binding)
  | staticLambda (expr : Expr)
  | below (binding : Binding)

def checkStructuralArmBinder
    (env : Environment)
    (typeName : Name)
    (binder : StructuralArmBinder)
    (domain : Expr) :
    Except String Unit := do
  match binder with
  | .runtime (some expected) _ =>
      match typeAtom? env domain with
      | some actual =>
          if actual == expected then
            .ok ()
          else
            .error
              s!"structural recursion arm binder type mismatch: {typeName}: expected {reprStr expected}, got {reprStr actual}"
      | none =>
          .error
            s!"unsupported structural recursion arm binder type: {typeName}: {reprStr domain}"
  | .runtime none _ =>
      if isProofType? env domain then
        .ok ()
      else
        .error s!"structural recursion arm proof binder mismatch: {typeName}"
  | .staticLambda _ => .ok ()
  | .below _ => .ok ()

partial def consumeStructuralArmBinders
    (ctx : Context)
    (typeName : Name)
    (binders : List StructuralArmBinder)
    (arm : Expr) :
    Except String (Expr × List Binding) := do
  let rec loop :
      List StructuralArmBinder → Expr → List Binding → Except String (Expr × List Binding)
    | [], body, bindings => .ok (betaSpecializeExpr ctx.env ctx.root 16 body, bindings)
    | binder :: rest, expr, bindings =>
        match expr.consumeMData with
        | .lam _ domain body _ => do
            checkStructuralArmBinder ctx.env typeName binder domain
            match binder with
            | .runtime _ binding => loop rest body (binding :: bindings)
            | .below binding => loop rest body (binding :: bindings)
            | .staticLambda staticExpr => loop rest (body.instantiate1 staticExpr) bindings
        | _ => .error s!"unsupported structural recursion arm: {typeName}"
  loop binders arm []

def structuralCtorArmBinders
    (prePostArgCount : Nat)
    (postBinders fieldBinders : List StructuralArmBinder)
    (belowBinding : Binding) :
    List StructuralArmBinder :=
  postBinders.take prePostArgCount ++
    fieldBinders ++
    postBinders.drop prePostArgCount ++
    [StructuralArmBinder.below belowBinding]

def consumeStructuralCtorArm
    (ctx : Context)
    (typeName : Name)
    (prePostArgCount : Nat)
    (postBinders fieldBinders : List StructuralArmBinder)
    (ctor : VariantCtorLayout)
    (belowBinding : Binding)
    (arm : Expr) :
    Except String (Expr × List Binding) := do
  let armBinders := structuralCtorArmBinders prePostArgCount postBinders fieldBinders belowBinding
  if ctor.fields.isEmpty then
    let unitBinder :=
      StructuralArmBinder.runtime (some .unit) (.value (.scalar (.u64 0)))
    match consumeStructuralArmBinders ctx typeName (unitBinder :: armBinders) arm with
    | .ok parsedArm => .ok parsedArm
    | .error _ => consumeStructuralArmBinders ctx typeName armBinders arm
  else
    consumeStructuralArmBinders ctx typeName armBinders arm

structure ClosedFoldCtorInfo where
  index : Nat
  ctor : VariantCtorLayout
  recursiveOffsets : List Nat

def runtimeFieldSlotCount (fields : List (Option Ty)) : Nat :=
  fields.foldl
    (fun total field =>
      match field with
      | some ty => total + internalSlots ty
      | none => total)
    0

def directRecursiveFieldOffsets
    (typeName : Name)
    (typeParams : List Ty)
    (fields : List (Option Ty)) :
    List Nat :=
  let rec loop (offset : Nat) (fields : List (Option Ty)) (acc : List Nat) : List Nat :=
    match fields with
    | [] => acc.reverse
    | none :: rest => loop offset rest acc
    | some ty :: rest =>
        let nextOffset := offset + internalSlots ty
        match ty with
        | .recVariant candidate params =>
            if candidate == typeName && params == typeParams then
              loop nextOffset rest (offset :: acc)
            else
              loop nextOffset rest acc
        | _ => loop nextOffset rest acc
  loop 0 fields []

def localRuntimeFieldsFromKinds
    (fields : List (Option Ty))
    (fieldStart : Nat) :
    List ExtractedValue :=
  let rec loop
      (offset : Nat)
      (fields : List (Option Ty))
      (acc : List ExtractedValue) :
      List ExtractedValue :=
    match fields with
    | [] => acc.reverse
    | none :: rest => loop offset rest acc
    | some ty :: rest =>
        let value := valueFromInternalSlots ty fun slotOffset =>
          .local (fieldStart + offset + slotOffset)
        loop (offset + internalSlots ty) rest (value :: acc)
  loop 0 fields []

def structuralRecCallTarget?
    (locals : List Binding)
    (body : Expr) :
    Except String (Option (Name × ExtractedValue × List ExtractedValue × List Expr)) := do
  match appFnArgs body with
  | (fn, extraArgs) =>
      match fn.consumeMData with
      | .proj ``PProd _ _ =>
          match ← structuralRecProjection? locals fn with
          | some (functionName, arg, capturedArgs) =>
              .ok (some (functionName, arg, capturedArgs, extraArgs))
          | none => .ok none
      | _ => .ok none

structure ClosedStructuralPredicateShape where
  typeName : Name
  typeParams : List Ty
  scrutinee : Expr
  step : Expr
  predicate : Expr

partial def materializeCapturedStructuralArgs
    (tys : List Ty)
    (values : List ExtractedValue)
    (nextLocal : Nat) :
    Except String StrictArgs := do
  match tys, values with
  | [], [] => .ok { lets := [], args := [], nextLocal := nextLocal }
  | ty :: restTys, value :: restValues =>
      let head ← materializeStrictInternalSlots ty value nextLocal
      let bound := bindStrictSlots head.slots head.nextLocal
      let rest ← materializeCapturedStructuralArgs restTys restValues bound.nextLocal
      .ok {
        lets := head.lets ++ bound.lets ++ rest.lets,
        args := bound.slots ++ rest.args,
        nextLocal := rest.nextLocal
      }
  | _, _ => .error "structural recursion captured argument arity mismatch"

def closedStructuralPredicateShape? (env : Environment) (body : Expr) :
    Option ClosedStructuralPredicateShape :=
  match rawStructuralRecApplication? env body with
  | some app =>
      match app.postArgs with
      | [predicate] =>
          if isDirectLambda predicate then
            some {
              typeName := app.typeName,
              typeParams := app.typeParams,
              scrutinee := app.scrutinee,
              step := app.step,
              predicate := predicate
            }
          else
            none
      | _ => none
  | none => none

partial def natRecursorProjection? (locals : List Binding) (expr : Expr) :
    Except String (Option Name) := do
  match expr.consumeMData with
  | .bvar index =>
      match ← lookupBinding locals index with
      | .natRecursor functionName => .ok (some functionName)
      | _ => .ok none
  | .proj ``PProd 0 body =>
      natRecursorProjection? locals body
  | _ => .ok none

end LeanExe.Extract.Core
