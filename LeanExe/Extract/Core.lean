import Lean
import Init.Data.ByteArray.Extra
import LeanExe.Extract.Env
import LeanExe.Extract.StructuralRec
import LeanExe.IR.Core
import LeanExe.Runtime

open Lean

namespace LeanExe.Extract.Core

mutual
  partial def extractStructuralRecCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (functionName : Name)
      (arg : ExtractedValue)
      (capturedArgs : List ExtractedValue)
      (extraArgs : List Expr) :
      Except String (ExtractedValue × Nat) := do
    let index ←
      match functionIndex? ctx functionName with
      | some index => .ok index
      | none => .error s!"structural recursive function is not compiled: {functionName}"
    let sig ←
      match functionSignature? ctx functionName with
      | some sig => .ok sig
      | none => .error s!"unsupported function type or declaration: {functionName}"
    let paramTy ←
      match sig.params with
      | paramTy :: _ => .ok paramTy
      | _ => .error s!"unsupported structural recursion arity: {functionName}"
    let argSlots ← materializeStrictInternalSlots paramTy arg nextLocal
    let bound := bindStrictSlots argSlots.slots argSlots.nextLocal
    let expectedExtra := sig.params.drop 1
    let extraResult ←
      if extraArgs.isEmpty && !capturedArgs.isEmpty then
        materializeCapturedStructuralArgs expectedExtra capturedArgs bound.nextLocal
      else
        let dynamicExtraArgs ← dynamicStructuralExtraArgs expectedExtra extraArgs
        extractCallArgsFrom ctx locals bound.nextLocal expectedExtra dynamicExtraArgs
    let slotCount := internalSlots sig.result
    let slotStart := extraResult.nextLocal
    let slots := (List.range slotCount).map (fun offset => slotStart + offset)
    let value := valueFromInternalSlots sig.result fun offset => .local (slotStart + offset)
    .ok
      (wrapValueLets (argSlots.lets ++ bound.lets ++ extraResult.lets)
        (.letCall slots index (bound.slots ++ extraResult.args) value),
        slotStart + slotCount)

  partial def extractWfRecursorCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (functionName : Name)
      (args : List Expr) :
      Except String (ExtractedValue × Nat) := do
    match args with
    | arg :: _proof :: extraArgs =>
        let argResult ← extractValueFrom ctx locals nextLocal arg
        extractStructuralRecCallValueFrom ctx locals argResult.snd functionName argResult.fst []
          extraArgs
    | _ => .error s!"unsupported well-founded recursive call: {functionName}"

  partial def extractNatRecursorCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (functionName : Name)
      (args : List Expr) :
      Except String (ExtractedValue × Nat) := do
    let index ←
      match functionIndex? ctx functionName with
      | some index => .ok index
      | none => .error s!"Nat recursive function is not compiled: {functionName}"
    let sig ←
      match functionSignature? ctx functionName with
      | some sig => .ok sig
      | none => .error s!"unsupported function type or declaration: {functionName}"
    let carriedParams ←
      match sig.params with
      | .nat :: carried => .ok carried
      | _ => .error s!"unsupported Nat recursive function arity: {functionName}"
    if args.length != carriedParams.length then
      .error s!"Nat recursive call arity mismatch: {functionName}"
    else
      strictCallMaterializationCheck ctx functionName carriedParams args
      let argsResult ← extractCallArgsFrom ctx locals nextLocal carriedParams args
      let slotCount := internalSlots sig.result
      let slotStart := argsResult.nextLocal
      let slots := (List.range slotCount).map (fun offset => slotStart + offset)
      let value := valueFromInternalSlots sig.result fun offset => .local (slotStart + offset)
      let fuelArg : IRExpr := .u64Bin .sub (.local 0) (.u64 1)
      .ok
        (wrapValueLets argsResult.lets
          (.letCall slots index (fuelArg :: argsResult.args) value),
          slotStart + slotCount)

  partial def extractClosedStructuralPredicateExprFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String (Option (IRExpr × Nat)) := do
    match closedStructuralPredicateShape? ctx.env expr with
    | none => .ok none
    | some shape =>
        let layout ←
          match recursiveVariantLayout? ctx.env shape.typeName shape.typeParams with
          | some layout => .ok layout
          | none => .error s!"unsupported closed structural predicate type: {shape.typeName}"
        let stepInfo ←
          structuralRecStepMatcher? ctx.env shape.typeName shape.typeParams 1 shape.step
        if stepInfo.layout != layout then
          .error s!"closed structural predicate matcher type mismatch: {shape.typeName}"
        else if stepInfo.arms.length != layout.ctors.length then
          .error s!"inductive matcher arity mismatch: {layout.name}"
        else if stepInfo.prePostArgCount > 1 then
          .error s!"unsupported closed structural predicate arguments: {shape.typeName}"
        else
          let ctorInfos :=
            enumerate layout.ctors |>.map fun item =>
              ({
                index := item.fst,
                ctor := item.snd,
                recursiveOffsets :=
                  directRecursiveFieldOffsets shape.typeName shape.typeParams item.snd.fields
              } : ClosedFoldCtorInfo)
          let continueInfos := ctorInfos.filter fun info => info.recursiveOffsets.length == 1
          let terminalInfos := ctorInfos.filter fun info => info.recursiveOffsets.isEmpty
          let continueInfo ←
            match continueInfos with
            | [info] => .ok info
            | _ => .error s!"closed structural predicate requires one recursive constructor: {shape.typeName}"
          if terminalInfos.length + 1 != ctorInfos.length then
            .error s!"closed structural predicate requires list-shaped recursive constructors: {shape.typeName}"
          else
            let recursiveFieldOffset ←
              match continueInfo.recursiveOffsets with
              | [offset] => .ok offset
              | _ => .error s!"closed structural predicate requires one recursive field: {shape.typeName}"
            let scrutineeResult ← extractValueFrom ctx locals nextLocal shape.scrutinee
            let parts ← heapVariantPtrWithLets layout.name scrutineeResult.fst
            let ptrExpr := wrapExprLets parts.fst parts.snd
            let fieldSlotCount := runtimeFieldSlotCount continueInfo.ctor.fields
            let fieldStart := scrutineeResult.snd
            let runtimeFields := localRuntimeFieldsFromKinds continueInfo.ctor.fields fieldStart
            let sourceBindings ←
              sourceFieldBindingsFromKinds layout.name continueInfo.ctor.fields runtimeFields
            let fieldBinders :=
              (continueInfo.ctor.fields.zip sourceBindings).map fun item =>
                StructuralArmBinder.runtime item.fst item.snd
            let postBinders := [StructuralArmBinder.staticLambda shape.predicate]
            let belowBinding ←
              structuralBelowBinding layout.name [] layout.name shape.typeParams
                continueInfo.ctor.name continueInfo.ctor.fields runtimeFields
            let continueArm ←
              match stepInfo.arms[continueInfo.index]? with
              | some arm => .ok arm
              | none => .error s!"inductive matcher arity mismatch: {layout.name}"
            let parsedContinue ←
              consumeStructuralCtorArm ctx layout.name stepInfo.prePostArgCount postBinders fieldBinders
                continueInfo.ctor belowBinding continueArm
            let (predicateExpr, recExpr, stopWhenTrue, terminalValue) ←
              match appFnArgs parsedContinue.fst with
              | (.const ``Bool.or _, [predicateExpr, recExpr]) =>
                  .ok (predicateExpr, recExpr, true, false)
              | (.const ``Bool.and _, [predicateExpr, recExpr]) =>
                  .ok (predicateExpr, recExpr, false, true)
              | _ =>
                  .error s!"unsupported closed structural predicate step: {shape.typeName}"
            let recCall ←
              match ← structuralRecCallTarget? parsedContinue.snd recExpr with
              | some recCall => .ok recCall
              | none =>
                  .error
                    s!"closed structural predicate step must call the recursive field: {shape.typeName}"
            if recCall.fst != layout.name then
              .error s!"closed structural predicate recursive target mismatch: {shape.typeName}"
            else
              let recArg := recCall.snd.fst
              let recCapturedArgs := recCall.snd.snd.fst
              let recExtraArgs := recCall.snd.snd.snd
              let recursiveFieldValue := valueFromInternalSlots
                (.recVariant shape.typeName shape.typeParams)
                (fun _ => .local (fieldStart + recursiveFieldOffset))
              if recArg != recursiveFieldValue then
                .error s!"closed structural predicate recursive field mismatch: {shape.typeName}"
              else if !recCapturedArgs.isEmpty || !(recExtraArgs.all isDirectLambda) then
                .error s!"closed structural predicate recursive argument mismatch: {shape.typeName}"
              else
                let predicateResult ←
                  extractExprFrom ctx (parsedContinue.snd ++ locals)
                    (fieldStart + fieldSlotCount) predicateExpr
                let rec parseTerminalArms : List ClosedFoldCtorInfo → Except String Unit
                  | [] => .ok ()
                  | info :: rest => do
                      let arm ←
                        match stepInfo.arms[info.index]? with
                        | some arm => .ok arm
                        | none => .error s!"inductive matcher arity mismatch: {layout.name}"
                      let runtimeFields ← runtimeTypesFromKinds info.ctor.fields |>.mapM defaultValue
                      let sourceBindings ←
                        sourceFieldBindingsFromKinds layout.name info.ctor.fields runtimeFields
                      let fieldBinders :=
                        (info.ctor.fields.zip sourceBindings).map fun item =>
                          StructuralArmBinder.runtime item.fst item.snd
                      let belowBinding ←
                        structuralBelowBinding layout.name [] layout.name shape.typeParams
                          info.ctor.name info.ctor.fields runtimeFields
                      let parsedArm ←
                        consumeStructuralCtorArm ctx layout.name stepInfo.prePostArgCount postBinders
                          fieldBinders info.ctor belowBinding arm
                      let armResult ←
                        extractExprFrom ctx (parsedArm.snd ++ locals) predicateResult.snd parsedArm.fst
                      let expected := if terminalValue then .u64 1 else .u64 0
                      if armResult.fst == expected then
                        parseTerminalArms rest
                      else
                        .error
                          s!"closed structural predicate terminal arm mismatch: {shape.typeName}"
                parseTerminalArms terminalInfos
                .ok (some
                  (.heapLinearPredicate ptrExpr continueInfo.index fieldSlotCount recursiveFieldOffset
                    fieldStart predicateResult.fst stopWhenTrue terminalValue,
                    predicateResult.snd))

  partial def extractValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String (ExtractedValue × Nat) := do
    match expr.consumeMData with
    | .bvar index =>
        match ← lookupBinding locals index with
        | .slot slot => .ok (.scalar (.local slot), nextLocal)
        | .value value => .ok (value, nextLocal)
        | .thunk savedLocals value => extractValueFrom ctx savedLocals nextLocal value
        | .structuralRec _ _ => .error "structural recursion handle used as a value"
        | .structuralBelow _ => .error "structural recursion below value used as a value"
        | .wfRecursor _ => .error "well-founded recursion handle used as a value"
        | .natRecursor _ => .error "Nat recursion handle used as a value"
        | .recursor => .error "recursive handle used as a value"
    | .letE _ type value body _ =>
        if !containsBVar 0 body then
          extractValueFrom ctx (.recursor :: locals) nextLocal body
        else if isStringType type then
          extractValueFrom ctx (.thunk locals value :: locals) nextLocal body
        else
          match typeAtom? ctx.env type with
          | some ty =>
              if supportedLocalType ty then
                let valueResult ← extractValueFrom ctx locals nextLocal value
                let width := internalSlots ty
                let targets := (List.range width).map fun offset => valueResult.snd + offset
                let lets ← materializeInternalValueLets ty valueResult.fst targets
                let localValue :=
                  valueFromInternalSlots ty (fun offset => .local (valueResult.snd + offset))
                let bodyResult ←
                  extractValueFrom ctx (.value localValue :: locals) (valueResult.snd + width) body
                .ok (wrapValueLocalLets lets bodyResult.fst, bodyResult.snd)
              else
                .error s!"unsupported let-bound type: {type}"
          | none => .error s!"unsupported let-bound type: {type}"
    | .proj ``PProd index body =>
        match ← natRecursorProjection? locals (.proj ``PProd index body) with
        | some _functionName => .error "Nat recursion handle used as a value"
        | none =>
            match ← structuralRecProjection? locals (.proj ``PProd index body) with
            | some (functionName, arg, capturedArgs) =>
                extractStructuralRecCallValueFrom ctx locals nextLocal functionName arg capturedArgs []
            | none => .error "unsupported structural recursion projection"
    | .proj ``Prod index body =>
        let valueResult ← extractValueFrom ctx locals nextLocal body
        .ok (← productField index valueResult.fst, valueResult.snd)
    | .proj typeName index body =>
        match structureFieldKinds? ctx.env typeName with
        | some kinds =>
            match runtimeFieldIndexFromKinds index kinds with
            | some (some runtimeIndex) =>
                let valueResult ← extractValueFrom ctx locals nextLocal body
                .ok (← structField typeName runtimeIndex valueResult.fst, valueResult.snd)
            | some none => .ok (.scalar (.u64 0), nextLocal)
            | none => .error s!"unsupported structure projection index: {typeName}.{index}"
        | none => .error s!"unsupported projection: {typeName}"
    | .const ``Unit.unit _ => .ok (.scalar (.u64 0), nextLocal)
    | .const ``ByteArray.empty _ => .ok (.byteArray (.u64 0) (.u64 0) (.u64 0), nextLocal)
    | _ =>
        match expressionStructuralRecShape? ctx.env ctx.root expr with
        | some shape =>
            match syntheticForShape? ctx shape with
            | some synth =>
                let scrutineeResult ← extractValueFrom ctx locals nextLocal shape.scrutinee
                extractStructuralRecCallValueFrom ctx locals scrutineeResult.snd synth.name
                  scrutineeResult.fst [] (structuralExpressionCallExtraArgs shape)
            | none => .error s!"unsupported expression-level structural recursion: {shape.typeName}"
        | none =>
        match appFnArgs expr with
        | (.bvar index, args) =>
            match ← lookupBinding locals index with
            | .wfRecursor functionName =>
                extractWfRecursorCallValueFrom ctx locals nextLocal functionName args
            | .natRecursor functionName =>
                extractNatRecursorCallValueFrom ctx locals nextLocal functionName args
            | _ => .error s!"unsupported expression: {expr}"
        | (.proj ``PProd index body, extraArgs) =>
            match ← natRecursorProjection? locals (.proj ``PProd index body) with
            | some functionName =>
                extractNatRecursorCallValueFrom ctx locals nextLocal functionName extraArgs
            | none =>
                match ← structuralRecProjection? locals (.proj ``PProd index body) with
                | some (functionName, arg, capturedArgs) =>
                    extractStructuralRecCallValueFrom ctx locals nextLocal functionName arg capturedArgs
                      extraArgs
                | none => .error "unsupported structural recursion projection"
        | (.const ``Prod.mk _, args) =>
            match args.reverse with
            | right :: left :: _ =>
                let leftResult ← extractValueFrom ctx locals nextLocal left
                let rightResult ← extractValueFrom ctx locals leftResult.snd right
                .ok (.product leftResult.fst rightResult.fst, rightResult.snd)
            | _ => .error "unsupported product constructor"
        | (.const ``Prod.fst _, args) =>
            match args.reverse with
            | product :: _ =>
                let valueResult ← extractValueFrom ctx locals nextLocal product
                .ok (← productField 0 valueResult.fst, valueResult.snd)
            | _ => .error "unsupported Prod.fst application"
        | (.const ``Prod.snd _, args) =>
            match args.reverse with
            | product :: _ =>
                let valueResult ← extractValueFrom ctx locals nextLocal product
                .ok (← productField 1 valueResult.fst, valueResult.snd)
            | _ => .error "unsupported Prod.snd application"
        | (.const ``Array.swapAt _, args) =>
            match args, args.reverse with
            | itemTy :: _, _proof :: value :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                  match arrayElementSlots? itemTy with
                  | some width =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                    let valueSlots ← flattenArrayElementValue itemTy valueResult.fst
                    let childMask := arrayElementChildMask itemTy
                    let ownedMask := ownedChildMaskForSlots childMask valueSlots
                    let oldValue ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                    let updatedArray :=
                      ownedArrayValue valueResult.snd
                        (.arraySetSlots
                          width childMask ownedMask (.local arraySlot) (.local indexSlot) valueSlots)
                    .ok
                      (.letE arraySlot arrayResult.fst
                        (.letE indexSlot indexResult.fst
                          (.product oldValue updatedArray)),
                        valueResult.snd + 1)
                  | none => .error s!"unsupported Array.swapAt item type: {reprStr itemTy}"
                | none => .error "unsupported Array.swapAt item type"
            | _, _ => .error "unsupported Array.swapAt application"
        | (.const ``List.toArray _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.replicate _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.push _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.append _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.extract _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.map _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.filter _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.empty _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.mkEmpty _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.emptyWithCapacity _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.singleton _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.set _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.set! _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.insertIdx _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.insertIdx! _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.eraseIdx! _, _) =>
            let ptrResult ← extractExprFrom ctx locals nextLocal expr
            .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
        | (.const ``Array.pop _, args) =>
            match args, args.reverse with
            | itemTy :: _, array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.pop" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let arraySlot := arrayResult.snd
                    let resultSlot := arraySlot + 1
                    let isEmpty := .eqU64 (.arraySize (.local arraySlot)) (.u64 0)
                    let resultPtr := .arrayPopSlots width childMask (.local arraySlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (conditionalArrayOwnerValue resultSlot resultPtr (.not isEmpty)
                            parts.snd.owner)),
                        resultSlot + 1)
                | none => .error "unsupported Array.pop item type"
            | _, _ => .error "unsupported Array.pop application"
        | (.const ``Array.eraseIdxIfInBounds _, args) =>
            match args, args.reverse with
            | itemTy :: _, index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.eraseIdxIfInBounds" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let resultSlot := arraySlot + 2
                    let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                    let resultPtr :=
                      .arrayEraseIfInBoundsSlots width childMask (.local arraySlot)
                        (.local indexSlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (.letE indexSlot indexResult.fst
                            (conditionalArrayOwnerValue resultSlot resultPtr inBounds
                              parts.snd.owner))),
                        resultSlot + 1)
                | none => .error "unsupported Array.eraseIdxIfInBounds item type"
            | _, _ => .error "unsupported Array.eraseIdxIfInBounds application"
        | (.const ``Array.eraseIdx _, args) =>
            match args, args.reverse with
            | itemTy :: _, _proof :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.eraseIdx" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let resultSlot := arraySlot + 2
                    let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                    let resultPtr :=
                      .arrayEraseIfInBoundsSlots width childMask (.local arraySlot)
                        (.local indexSlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (.letE indexSlot indexResult.fst
                            (conditionalArrayOwnerValue resultSlot resultPtr inBounds
                              parts.snd.owner))),
                        resultSlot + 1)
                | none => .error "unsupported Array.eraseIdx item type"
            | _, _ => .error "unsupported Array.eraseIdx application"
        | (.const ``Array.swapIfInBounds _, args) =>
            match args, args.reverse with
            | itemTy :: _, right :: left :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.swapIfInBounds" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let leftResult ← extractExprFrom ctx locals arrayResult.snd left
                    let rightResult ← extractExprFrom ctx locals leftResult.snd right
                    let arraySlot := rightResult.snd
                    let leftSlot := arraySlot + 1
                    let rightSlot := arraySlot + 2
                    let resultSlot := arraySlot + 3
                    let len := .arraySize (.local arraySlot)
                    let inBounds :=
                      .and (.ltU64 (.local leftSlot) len) (.ltU64 (.local rightSlot) len)
                    let resultPtr :=
                      .arraySwapIfInBoundsSlots width childMask (.local arraySlot)
                        (.local leftSlot) (.local rightSlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (.letE leftSlot leftResult.fst
                            (.letE rightSlot rightResult.fst
                              (conditionalArrayOwnerValue resultSlot resultPtr inBounds
                                parts.snd.owner)))),
                        resultSlot + 1)
                | none => .error "unsupported Array.swapIfInBounds item type"
            | _, _ => .error "unsupported Array.swapIfInBounds application"
        | (.const ``Array.swap _, args) =>
            match args, args.reverse with
            | itemTy :: _, _rightProof :: _leftProof :: right :: left :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.swap" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let leftResult ← extractExprFrom ctx locals arrayResult.snd left
                    let rightResult ← extractExprFrom ctx locals leftResult.snd right
                    let arraySlot := rightResult.snd
                    let leftSlot := arraySlot + 1
                    let rightSlot := arraySlot + 2
                    let resultSlot := arraySlot + 3
                    let len := .arraySize (.local arraySlot)
                    let inBounds :=
                      .and (.ltU64 (.local leftSlot) len) (.ltU64 (.local rightSlot) len)
                    let resultPtr :=
                      .arraySwapIfInBoundsSlots width childMask (.local arraySlot)
                        (.local leftSlot) (.local rightSlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (.letE leftSlot leftResult.fst
                            (.letE rightSlot rightResult.fst
                              (conditionalArrayOwnerValue resultSlot resultPtr inBounds
                                parts.snd.owner)))),
                        resultSlot + 1)
                | none => .error "unsupported Array.swap item type"
            | _, _ => .error "unsupported Array.swap application"
        | (.const ``Array.reverse _, args) =>
            match args, args.reverse with
            | itemTy :: _, array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.reverse" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let arraySlot := arrayResult.snd
                    let resultSlot := arraySlot + 1
                    let takesOwnership := .not (.leU64 (.arraySize (.local arraySlot)) (.u64 1))
                    let resultPtr := .arrayReverseSlots width childMask (.local arraySlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (conditionalArrayOwnerValue resultSlot resultPtr takesOwnership
                            parts.snd.owner)),
                        resultSlot + 1)
                | none => .error "unsupported Array.reverse item type"
            | _, _ => .error "unsupported Array.reverse application"
        | (.const ``Array.insertIdxIfInBounds _, args) =>
            match args, args.reverse with
            | itemTy :: _, value :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.insertIdxIfInBounds" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                    let slots ← flattenArrayElementValue itemTy valueResult.fst
                    let ownedMask := ownedChildMaskForSlots childMask slots
                    let resultSlot := valueResult.snd
                    let inBounds := .leU64 (.local indexSlot) (.arraySize (.local arraySlot))
                    let resultPtr :=
                      .arrayInsertIfInBoundsSlots width childMask ownedMask (.local arraySlot)
                        (.local indexSlot) slots
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (.letE indexSlot indexResult.fst
                            (conditionalArrayOwnerValue resultSlot resultPtr inBounds
                              parts.snd.owner))),
                        resultSlot + 1)
                | none => .error "unsupported Array.insertIdxIfInBounds item type"
            | _, _ => .error "unsupported Array.insertIdxIfInBounds application"
        | (.const ``Array.modify _, args) =>
            match args, args.reverse with
            | itemTy :: _, modifyFn :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let width ← arrayElementWidth "Array.modify" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let oldValue ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                    let modifyBody ←
                      match collectLambdas modifyFn 1 with
                      | some body => .ok body
                      | none => .error "unsupported Array.modify function"
                    let modifiedResult ←
                      extractValueFrom ctx (.value oldValue :: locals) (indexSlot + 1) modifyBody
                    let slots ← flattenArrayElementValue itemTy modifiedResult.fst
                    let ownedMask := ownedChildMaskForSlots childMask slots
                    let resultSlot := modifiedResult.snd
                    let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                    let resultPtr :=
                      .ite inBounds
                        (.arraySetSlots width childMask ownedMask (.local arraySlot)
                          (.local indexSlot) slots)
                        (.local arraySlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (.letE indexSlot indexResult.fst
                            (conditionalArrayOwnerValue resultSlot resultPtr inBounds
                              parts.snd.owner))),
                        resultSlot + 1)
                | none => .error "unsupported Array.modify item type"
            | _, _ => .error "unsupported Array.modify application"
        | (.const ``Array.setIfInBounds _, args) =>
            match args, args.reverse with
            | itemTy :: _, value :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                  match arrayElementSlots? itemTy with
                  | some width =>
                    let childMask := arrayElementChildMask itemTy
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← arrayFullPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                    let slots ← flattenArrayElementValue itemTy valueResult.fst
                    let ownedMask := ownedChildMaskForSlots childMask slots
                    let resultSlot := valueResult.snd
                    let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                    let resultPtr :=
                      .ite inBounds
                        (.arraySetSlots width childMask ownedMask (.local arraySlot)
                          (.local indexSlot) slots)
                        (.local arraySlot)
                    .ok
                      (wrapValueLets parts.fst
                        (.letE arraySlot parts.snd.ptr
                          (.letE indexSlot indexResult.fst
                            (conditionalArrayOwnerValue resultSlot resultPtr inBounds
                              parts.snd.owner))),
                        resultSlot + 1)
                  | none => .error s!"unsupported Array.setIfInBounds item type: {reprStr itemTy}"
                | none => .error "unsupported Array.setIfInBounds item type"
            | _, _ => .error "unsupported Array.setIfInBounds application"
        | (.const ``id _, args) =>
            match args.reverse with
            | value :: _ => extractValueFrom ctx locals nextLocal value
            | _ => .error "unsupported id application"
        | (.const ``ForIn.forIn _, args) =>
            match idForInArgs? ctx.env (.const ``ForIn.forIn []) args with
            | some forIn =>
                if !supportedLoopAccumulatorType forIn.resultTy then
                  .error s!"unsupported for-in accumulator type: {reprStr forIn.resultTy}"
                else
                  let stepBody ←
                    match collectLambdas forIn.body 2 with
                    | some body => forInStepBody? forIn.resultTy body
                    | none => .error "unsupported for-in body"
                  let resultWidth := internalSlots forIn.resultTy
                  match forIn.collectionTy with
                  | .byteArray =>
                      if forIn.itemTy == .u8 then
                        let collectionResult ← extractValueFrom ctx locals nextLocal forIn.collection
                        let parts ← byteArrayPartsWithLets collectionResult.fst
                        let ptr := wrapExprLets parts.fst parts.snd.fst
                        let len := wrapExprLets parts.fst parts.snd.snd
                        let initResult ← extractValueFrom ctx locals collectionResult.snd forIn.init
                        let initSlots ← flattenInternalValue forIn.resultTy initResult.fst
                        if initSlots.length != resultWidth then
                          .error "for-in accumulator initial value shape mismatch"
                        else
                        let accStart := initResult.snd
                        let byteSlot := accStart + resultWidth
                        let accValue :=
                          valueFromInternalSlots forIn.resultTy
                            (fun offset => .local (accStart + offset))
                        let bodyResult ←
                          extractValueFrom ctx
                            (.value accValue ::
                              .value (.scalar (.local byteSlot)) :: locals)
                            (byteSlot + 1)
                            stepBody.value
                        let bodyTargets :=
                          (List.range resultWidth).map fun offset => bodyResult.snd + offset
                        let bodyLets ←
                          materializeInternalValueLets forIn.resultTy bodyResult.fst bodyTargets
                        let doneResult ←
                          extractExprFrom ctx
                            (.value accValue ::
                              .value (.scalar (.local byteSlot)) :: locals)
                            (bodyResult.snd + resultWidth)
                            stepBody.done
                        if bodyTargets.length != resultWidth then
                          .error "for-in accumulator body value shape mismatch"
                        else
                        let resultValue :=
                          valueFromInternalSlots forIn.resultTy
                            (fun offset =>
                              .byteArrayFoldMultiSlot
                                resultWidth
                                ptr
                                len
                                (.u64 0)
                                len
                                initSlots
                                accStart
                                byteSlot
                                (bodyTargets.map fun slot => (.local slot : IRExpr))
                                bodyLets
                                doneResult.fst
                                offset)
                        .ok
                          (resultValue, doneResult.snd)
                      else
                        .error s!"unsupported ByteArray for-in item type: {reprStr forIn.itemTy}"
                  | .array itemTy =>
                      if itemTy == forIn.itemTy then
                        match arrayElementSlots? itemTy with
                        | some width =>
                            let collectionResult ← extractExprFrom ctx locals nextLocal forIn.collection
                            let initResult ← extractValueFrom ctx locals collectionResult.snd forIn.init
                            let initSlots ← flattenInternalValue forIn.resultTy initResult.fst
                            if initSlots.length != resultWidth then
                              .error "for-in accumulator initial value shape mismatch"
                            else
                            let accStart := initResult.snd
                            let itemStart := accStart + resultWidth
                            let itemValue ← arrayLocalValue itemTy itemStart
                            let accValue :=
                              valueFromInternalSlots forIn.resultTy
                                (fun offset => .local (accStart + offset))
                            let bodyResult ←
                              extractValueFrom ctx
                                (.value accValue ::
                                  .value itemValue :: locals)
                                (itemStart + width)
                                stepBody.value
                            let bodyTargets :=
                              (List.range resultWidth).map fun offset => bodyResult.snd + offset
                            let bodyLets ←
                              materializeInternalValueLets forIn.resultTy bodyResult.fst bodyTargets
                            let doneResult ←
                              extractExprFrom ctx
                                (.value accValue ::
                                  .value itemValue :: locals)
                                (bodyResult.snd + resultWidth)
                                stepBody.done
                            if bodyTargets.length != resultWidth then
                              .error "for-in accumulator body value shape mismatch"
                            else
                            let resultValue :=
                              valueFromInternalSlots forIn.resultTy
                                (fun offset =>
                                  .arrayFoldMultiSlot
                                    width
                                    resultWidth
                                    collectionResult.fst
                                    (.u64 0)
                                    (.arraySize collectionResult.fst)
                                    initSlots
                                    accStart
                                    itemStart
                                    (bodyTargets.map fun slot => (.local slot : IRExpr))
                                    bodyLets
                                    doneResult.fst
                                    offset)
                            .ok
                              (resultValue, doneResult.snd)
                        | none => .error s!"unsupported Array for-in item type: {reprStr itemTy}"
                      else
                        .error "Array for-in item type mismatch"
                  | rangeTy =>
                      if isLegacyRangeType rangeTy && forIn.itemTy == .nat then
                        let collectionResult ← extractValueFrom ctx locals nextLocal forIn.collection
                        let rangeParts ← legacyRangeParts collectionResult.fst
                        let initResult ← extractValueFrom ctx locals collectionResult.snd forIn.init
                        let initSlots ← flattenInternalValue forIn.resultTy initResult.fst
                        if initSlots.length != resultWidth then
                          .error "for-in accumulator initial value shape mismatch"
                        else
                        let accStart := initResult.snd
                        let itemSlot := accStart + resultWidth
                        let accValue :=
                          valueFromInternalSlots forIn.resultTy
                            (fun offset => .local (accStart + offset))
                        let bodyResult ←
                          extractValueFrom ctx
                            (.value accValue ::
                              .value (.scalar (.local itemSlot)) :: locals)
                            (itemSlot + 1)
                            stepBody.value
                        let bodyTargets :=
                          (List.range resultWidth).map fun offset => bodyResult.snd + offset
                        let bodyLets ←
                          materializeInternalValueLets forIn.resultTy bodyResult.fst bodyTargets
                        let doneResult ←
                          extractExprFrom ctx
                            (.value accValue ::
                              .value (.scalar (.local itemSlot)) :: locals)
                            (bodyResult.snd + resultWidth)
                            stepBody.done
                        if bodyTargets.length != resultWidth then
                          .error "for-in accumulator body value shape mismatch"
                        else
                        let resultValue :=
                          valueFromInternalSlots forIn.resultTy
                            (fun offset =>
                              .rangeFoldMultiSlot
                                resultWidth
                                rangeParts.fst
                                rangeParts.snd.fst
                                rangeParts.snd.snd
                                initSlots
                                accStart
                                itemSlot
                                (bodyTargets.map fun slot => (.local slot : IRExpr))
                                bodyLets
                                doneResult.fst
                                offset)
                        .ok (resultValue, doneResult.snd)
                      else
                        .error s!"unsupported for-in collection type: {reprStr forIn.collectionTy}"
            | none => .error "unsupported ForIn.forIn application"
        | (.const ``Array.foldl _, args) =>
            match args with
            | sourceTyExpr :: resultTyExpr :: foldFn :: init :: array :: rest =>
                let attached? := arrayAttachValue? ctx.env array
                let sourceTy? :=
                  match attached? with
                  | some item => some item.fst
                  | none => typeAtom? ctx.env sourceTyExpr
                match sourceTy?, typeAtom? ctx.env resultTyExpr with
                | some sourceTy, some resultTy =>
                    if !supportedLoopAccumulatorType resultTy then
                      .error s!"unsupported Array.foldl accumulator type: {reprStr resultTy}"
                    else
                      match arrayElementSlots? sourceTy with
                      | some sourceWidth =>
                          let arrayExpr :=
                            match attached? with
                            | some item => item.snd
                            | none => array
                          let arrayResult ← extractExprFrom ctx locals nextLocal arrayExpr
                          let initResult ← extractValueFrom ctx locals arrayResult.snd init
                          let startStop ←
                            match rest with
                            | [] => .ok ((.u64 0, .arraySize arrayResult.fst), initResult.snd)
                            | [start] =>
                                let startResult ← extractExprFrom ctx locals initResult.snd start
                                .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                            | [start, stop] =>
                                let startResult ← extractExprFrom ctx locals initResult.snd start
                                match attached?, arrayAttachSize? ctx.env stop with
                                | some _, some _ =>
                                    .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                                | _, _ =>
                                    let stopResult ← extractExprFrom ctx locals startResult.snd stop
                                    .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                            | _ => .error "unsupported Array.foldl application"
                          let resultWidth := internalSlots resultTy
                          let initSlots ← flattenInternalValue resultTy initResult.fst
                          if initSlots.length != resultWidth then
                            .error "Array.foldl accumulator initial value shape mismatch"
                          else
                          let accStart := startStop.snd
                          let itemStart := accStart + resultWidth
                          let foldBody ←
                            match collectLambdas foldFn 2 with
                            | some body => .ok body
                            | none => .error "unsupported Array.foldl function"
                          let itemValue ← arrayLocalValue sourceTy itemStart
                          let accValue :=
                            valueFromInternalSlots resultTy
                              (fun offset => .local (accStart + offset))
                          let bodyExpr ←
                            match attached? with
                            | some _ =>
                                match arrayAttachUnwrapBody? ctx.env foldBody with
                                | some body => .ok body
                                | none => .error "unsupported Array.attach fold body"
                            | none => .ok foldBody
                          let bodyLocals :=
                            match attached? with
                            | some _ =>
                                .recursor :: .value itemValue :: .recursor ::
                                  .value accValue :: locals
                            | none =>
                                .value itemValue :: .value accValue :: locals
                          let bodyResult ←
                            extractValueFrom ctx
                              bodyLocals
                              (itemStart + sourceWidth)
                              bodyExpr
                          let bodyTargets :=
                            (List.range resultWidth).map fun offset => bodyResult.snd + offset
                          let bodyLets ← materializeInternalValueLets resultTy bodyResult.fst bodyTargets
                          if bodyTargets.length != resultWidth then
                            .error "Array.foldl accumulator body value shape mismatch"
                          else
                          let resultValue :=
                            valueFromInternalSlots resultTy
                              (fun offset =>
                                .arrayFoldMultiSlot
                                  sourceWidth
                                  resultWidth
                                  arrayResult.fst
                                  startStop.fst.fst
                                  startStop.fst.snd
                                  initSlots
                                  accStart
                                  itemStart
                                  (bodyTargets.map fun slot => (.local slot : IRExpr))
                                  bodyLets
                                  (.u64 0)
                                  offset)
                          .ok (resultValue, bodyResult.snd + resultWidth)
                      | none => .error s!"unsupported Array.foldl item type: {reprStr sourceTy}"
                | _, _ => .error "unsupported Array.foldl application"
            | _ => .error "unsupported Array.foldl application"
        | (.const ``ByteArray.foldl _, args) =>
            match args with
            | resultTyExpr :: foldFn :: init :: array :: rest =>
                match typeAtom? ctx.env resultTyExpr with
                | some resultTy =>
                    if !supportedLoopAccumulatorType resultTy then
                      .error s!"unsupported ByteArray.foldl accumulator type: {reprStr resultTy}"
                    else
                      let arrayResult ← extractValueFrom ctx locals nextLocal array
                      let parts ← byteArrayPartsWithLets arrayResult.fst
                      let ptr := wrapExprLets parts.fst parts.snd.fst
                      let len := wrapExprLets parts.fst parts.snd.snd
                      let initResult ← extractValueFrom ctx locals arrayResult.snd init
                      let startStop ←
                        match rest with
                        | [] => .ok ((.u64 0, len), initResult.snd)
                        | [start] =>
                            let startResult ← extractExprFrom ctx locals initResult.snd start
                            .ok ((startResult.fst, len), startResult.snd)
                        | [start, stop] =>
                            let startResult ← extractExprFrom ctx locals initResult.snd start
                            let stopResult ← extractExprFrom ctx locals startResult.snd stop
                            .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                        | _ => .error "unsupported ByteArray.foldl application"
                      let resultWidth := internalSlots resultTy
                      let initSlots ← flattenInternalValue resultTy initResult.fst
                      if initSlots.length != resultWidth then
                        .error "ByteArray.foldl accumulator initial value shape mismatch"
                      else
                      let accStart := startStop.snd
                      let byteSlot := accStart + resultWidth
                      let body ←
                        match collectLambdas foldFn 2 with
                        | some body => .ok body
                        | none => .error "unsupported ByteArray.foldl function"
                      let accValue :=
                        valueFromInternalSlots resultTy
                          (fun offset => .local (accStart + offset))
                      let bodyResult ←
                        extractValueFrom ctx
                          (.value (.scalar (.local byteSlot)) ::
                            .value accValue :: locals)
                          (byteSlot + 1)
                          body
                      let bodyTargets :=
                        (List.range resultWidth).map fun offset => bodyResult.snd + offset
                      let bodyLets ← materializeInternalValueLets resultTy bodyResult.fst bodyTargets
                      if bodyTargets.length != resultWidth then
                        .error "ByteArray.foldl accumulator body value shape mismatch"
                      else
                      let resultValue :=
                        valueFromInternalSlots resultTy
                          (fun offset =>
                            .byteArrayFoldMultiSlot
                              resultWidth
                              ptr
                              len
                              startStop.fst.fst
                              startStop.fst.snd
                              initSlots
                              accStart
                              byteSlot
                              (bodyTargets.map fun slot => (.local slot : IRExpr))
                              bodyLets
                              (.u64 0)
                              offset)
                      .ok (resultValue, bodyResult.snd + resultWidth)
                | none => .error "unsupported ByteArray.foldl result type"
            | _ => .error "unsupported ByteArray.foldl application"
        | (.const ``Id.run _, args) =>
            match args.reverse with
            | value :: _ => extractValueFrom ctx locals nextLocal value
            | _ => .error "unsupported Id.run application"
        | (.const ``Pure.pure _, args) =>
            match args, args.reverse with
            | monadTy :: _, value :: _ =>
                match supportedMonadType? ctx.env monadTy with
                | some .id =>
                    extractValueFrom ctx locals nextLocal value
                | some .option =>
                    let valueResult ← extractValueFrom ctx locals nextLocal value
                    .ok (mkOptionValue (.u64 1) valueResult.fst, valueResult.snd)
                | some (.except errorTy) =>
                    let valueResult ← extractValueFrom ctx locals nextLocal value
                    .ok (mkExceptValue (.u64 1) (← defaultValue errorTy) valueResult.fst,
                      valueResult.snd)
                | none =>
                    .error "unsupported Pure.pure application"
            | _, _ => .error "unsupported Pure.pure application"
        | (.const ``Bind.bind _, args) =>
            match args, args.reverse, monadMapResultType? ctx.env args with
            | monadTy :: _, bindFn :: value :: _, resultTy? =>
                match supportedMonadType? ctx.env monadTy with
                | some .id =>
                    let valueResult ← extractValueFrom ctx locals nextLocal value
                    let body ←
                      match collectLambdas bindFn 1 with
                      | some body => .ok body
                      | none => .error "unsupported Id bind function"
                    extractValueFrom ctx (.value valueResult.fst :: locals) valueResult.snd body
                | some .option =>
                    match resultTy? with
                    | some resultTy =>
                        let optionResult ← extractValueFrom ctx locals nextLocal value
                        let parts ← optionPartsWithLets optionResult.fst
                        let lets := parts.fst
                        let tag := parts.snd.fst
                        let payload := parts.snd.snd
                        let bindBody ←
                          match collectLambdas bindFn 1 with
                          | some body => .ok body
                          | none => .error "unsupported Option bind function"
                        let bindResult ←
                          extractValueFrom ctx (.value payload :: locals) optionResult.snd bindBody
                        let bindParts ← optionPartsWithLets bindResult.fst
                        let bindLets := bindParts.fst
                        let bindTag := wrapExprLets bindLets bindParts.snd.fst
                        let bindPayload := wrapValueLets bindLets bindParts.snd.snd
                        let nonePayload ← defaultValue resultTy
                        .ok
                          (wrapValueLets lets
                            (mkOptionValue
                              (.ite (.eqU64 tag (.u64 0)) (.u64 0) bindTag)
                              (← valueIte (.eqU64 tag (.u64 0)) nonePayload bindPayload)),
                            bindResult.snd)
                    | none => .error "unsupported Option bind application"
                | some (.except _errorTy) =>
                    match resultTy? with
                    | some resultTy =>
                        let exceptResult ← extractValueFrom ctx locals nextLocal value
                        let parts ← exceptPartsWithLets exceptResult.fst
                        let lets := parts.fst
                        let tag := parts.snd.fst
                        let errorPayload := parts.snd.snd.fst
                        let okPayload := parts.snd.snd.snd
                        let bindBody ←
                          match collectLambdas bindFn 1 with
                          | some body => .ok body
                          | none => .error "unsupported Except bind function"
                        let bindResult ←
                          extractValueFrom ctx (.value okPayload :: locals) exceptResult.snd bindBody
                        let bindParts ← exceptPartsWithLets bindResult.fst
                        let bindLets := bindParts.fst
                        let bindTag := wrapExprLets bindLets bindParts.snd.fst
                        let bindError := wrapValueLets bindLets bindParts.snd.snd.fst
                        let bindOk := wrapValueLets bindLets bindParts.snd.snd.snd
                        let defaultOk ← defaultValue resultTy
                        let isError := .eqU64 tag (.u64 0)
                        .ok
                          (wrapValueLets lets
                            (mkExceptValue
                              (.ite isError (.u64 0) bindTag)
                              (← valueIte isError errorPayload bindError)
                              (← valueIte isError defaultOk bindOk)),
                            bindResult.snd)
                    | none => .error "unsupported Except bind application"
                | none => .error "unsupported Bind.bind application"
            | _, _, _ => .error "unsupported Bind.bind application"
        | (.const ``Functor.map _, args) =>
            match args, args.reverse, monadMapResultType? ctx.env args with
            | monadTy :: _, value :: mapFn :: _, some resultTy =>
                match supportedMonadType? ctx.env monadTy with
                | some .option =>
                    let optionResult ← extractValueFrom ctx locals nextLocal value
                    let parts ← optionPartsWithLets optionResult.fst
                    let lets := parts.fst
                    let tag := parts.snd.fst
                    let payload := parts.snd.snd
                    let mapBody ←
                      match collectLambdas mapFn 1 with
                      | some body => .ok body
                      | none => .error "unsupported Option Functor.map function"
                    let mapResult ←
                      extractValueFrom ctx (.value payload :: locals) optionResult.snd mapBody
                    let nonePayload ← defaultValue resultTy
                    .ok
                      (wrapValueLets lets
                        (mkOptionValue tag
                          (← valueIte (.eqU64 tag (.u64 0)) nonePayload mapResult.fst)),
                        mapResult.snd)
                | some (.except _errorTy) =>
                    let exceptResult ← extractValueFrom ctx locals nextLocal value
                    let parts ← exceptPartsWithLets exceptResult.fst
                    let lets := parts.fst
                    let tag := parts.snd.fst
                    let errorPayload := parts.snd.snd.fst
                    let okPayload := parts.snd.snd.snd
                    let mapBody ←
                      match collectLambdas mapFn 1 with
                      | some body => .ok body
                      | none => .error "unsupported Except Functor.map function"
                    let mapResult ←
                      extractValueFrom ctx (.value okPayload :: locals) exceptResult.snd mapBody
                    let defaultOk ← defaultValue resultTy
                    .ok
                      (wrapValueLets lets
                        (mkExceptValue tag errorPayload
                          (← valueIte (.eqU64 tag (.u64 0)) defaultOk mapResult.fst)),
                        mapResult.snd)
                | _ => .error "unsupported Functor.map application"
            | _, _, _ => .error "unsupported Functor.map application"
        | (.const ``Option.none _, args) =>
            match optionConstructorType? ctx.env args with
            | some payloadTy =>
                .ok (mkOptionValue (.u64 0) (← defaultValue payloadTy), nextLocal)
            | none => .error "unsupported Option.none application"
        | (.const ``Option.some _, args) =>
            match args.reverse, optionConstructorType? ctx.env args with
            | value :: _, some _ =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                .ok (mkOptionValue (.u64 1) valueResult.fst, valueResult.snd)
            | _, _ => .error "unsupported Option.some application"
        | (.const ``Except.error _, args) =>
            match args.reverse, exceptConstructorTypes? ctx.env args with
            | value :: _, some (_errorTy, okTy) =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                .ok (mkExceptValue (.u64 0) valueResult.fst (← defaultValue okTy),
                  valueResult.snd)
            | _, _ => .error "unsupported Except.error application"
        | (.const ``Except.ok _, args) =>
            match args.reverse, exceptConstructorTypes? ctx.env args with
            | value :: _, some (errorTy, _okTy) =>
                let valueResult ← extractValueFrom ctx locals nextLocal value
                .ok (mkExceptValue (.u64 1) (← defaultValue errorTy) valueResult.fst,
                  valueResult.snd)
            | _, _ => .error "unsupported Except.ok application"
        | (.const ``Except.map _, args) =>
            match args.reverse, exceptMapTypes? ctx.env args with
            | exceptValue :: mapFn :: _, some (_errorTy, resultTy) =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let errorPayload := parts.snd.snd.fst
                let okPayload := parts.snd.snd.snd
                let mapBody ←
                  match collectLambdas mapFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Except.map function"
                let mapResult ←
                  extractValueFrom ctx (.value okPayload :: locals) exceptResult.snd mapBody
                let defaultOk ← defaultValue resultTy
                .ok
                  (wrapValueLets lets
                    (mkExceptValue tag errorPayload
                      (← valueIte (.eqU64 tag (.u64 0)) defaultOk mapResult.fst)),
                    mapResult.snd)
            | _, _ => .error "unsupported Except.map application"
        | (.const ``Except.mapError _, args) =>
            match args.reverse, exceptMapErrorTypes? ctx.env args with
            | exceptValue :: mapFn :: _, some (_sourceErrorTy, resultErrorTy) =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let errorPayload := parts.snd.snd.fst
                let okPayload := parts.snd.snd.snd
                let mapBody ←
                  match collectLambdas mapFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Except.mapError function"
                let mapResult ←
                  extractValueFrom ctx (.value errorPayload :: locals) exceptResult.snd mapBody
                let defaultError ← defaultValue resultErrorTy
                .ok
                  (wrapValueLets lets
                    (mkExceptValue tag
                      (← valueIte (.eqU64 tag (.u64 0)) mapResult.fst defaultError)
                      okPayload),
                    mapResult.snd)
            | _, _ => .error "unsupported Except.mapError application"
        | (.const ``Except.bind _, args) =>
            match args.reverse, exceptMapTypes? ctx.env args with
            | bindFn :: exceptValue :: _, some (_errorTy, resultTy) =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let errorPayload := parts.snd.snd.fst
                let okPayload := parts.snd.snd.snd
                let bindBody ←
                  match collectLambdas bindFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Except.bind function"
                let bindResult ←
                  extractValueFrom ctx (.value okPayload :: locals) exceptResult.snd bindBody
                let bindParts ← exceptPartsWithLets bindResult.fst
                let bindLets := bindParts.fst
                let bindTag := wrapExprLets bindLets bindParts.snd.fst
                let bindError := wrapValueLets bindLets bindParts.snd.snd.fst
                let bindOk := wrapValueLets bindLets bindParts.snd.snd.snd
                let defaultOk ← defaultValue resultTy
                let isError := .eqU64 tag (.u64 0)
                .ok
                  (wrapValueLets lets
                    (mkExceptValue
                      (.ite isError (.u64 0) bindTag)
                      (← valueIte isError errorPayload bindError)
                      (← valueIte isError defaultOk bindOk)),
                    bindResult.snd)
            | _, _ => .error "unsupported Except.bind application"
        | (.const ``Except.toOption _, args) =>
            match args.reverse, exceptPayloadType? ctx.env args with
            | exceptValue :: _, some _payloadTy =>
                let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
                let parts ← exceptPartsWithLets exceptResult.fst
                .ok
                  (wrapValueLets parts.fst
                    (mkOptionValue parts.snd.fst parts.snd.snd.snd),
                    exceptResult.snd)
            | _, _ => .error "unsupported Except.toOption application"
        | (.const ``Except.isOk _, args) =>
            match args.reverse, exceptPayloadType? ctx.env args with
            | exceptValue :: _, some _payloadTy =>
                let tagResult ← extractExceptTagExprFrom ctx locals nextLocal exceptValue
                .ok (.scalar (boolExpr (.not (.eqU64 tagResult.fst (.u64 0)))), tagResult.snd)
            | _, _ => .error "unsupported Except.isOk application"
        | (.const ``Option.getD _, args) =>
            match args.reverse with
            | defaultValue :: optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let defaultResult ← extractValueFrom ctx locals optionResult.snd defaultValue
                .ok
                  (wrapValueLets lets
                    (← valueIte (.eqU64 tag (.u64 0)) defaultResult.fst payload),
                    defaultResult.snd)
            | _ => .error "unsupported Option.getD application"
        | (.const ``Option.get! _, args) =>
            match args.reverse, optionConstructorType? ctx.env args with
            | optionValue :: _, some payloadTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                .ok
                  (wrapValueLets lets
                    (← valueIte (.eqU64 tag (.u64 0)) (← trapValue payloadTy) payload),
                    optionResult.snd)
            | _, _ => .error "unsupported Option.get! application"
        | (.const ``Option.orElse _, args) =>
            match optionOrElseArgs? ctx.env (.const ``Option.orElse []) args with
            | some (optionValue, fallback) =>
                extractOptionOrElseValueFrom ctx locals nextLocal optionValue fallback
            | none => .error "unsupported Option.orElse application"
        | (.const ``HOrElse.hOrElse _, args) =>
            match optionOrElseArgs? ctx.env (.const ``HOrElse.hOrElse []) args with
            | some (optionValue, fallback) =>
                extractOptionOrElseValueFrom ctx locals nextLocal optionValue fallback
            | none =>
                match exceptOrElseArgs? ctx.env (.const ``HOrElse.hOrElse []) args with
                | some (exceptValue, fallback) =>
                    extractExceptOrElseValueFrom ctx locals nextLocal exceptValue fallback
                | none => .error "unsupported HOrElse.hOrElse application"
        | (.const ``Option.elim _, args) =>
            match args.reverse with
            | someArm :: defaultValue :: optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let defaultResult ← extractValueFrom ctx locals optionResult.snd defaultValue
                let someBody ←
                  match collectLambdas someArm 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.elim some arm"
                let someResult ←
                  extractValueFrom ctx (.value payload :: locals) defaultResult.snd someBody
                .ok
                  (wrapValueLets lets
                    (← valueIte (.eqU64 tag (.u64 0)) defaultResult.fst someResult.fst),
                    someResult.snd)
            | _ => .error "unsupported Option.elim application"
        | (.const ``Option.map _, args) =>
            match args.reverse, optionMapResultType? ctx.env args with
            | optionValue :: mapFn :: _, some resultTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let mapBody ←
                  match collectLambdas mapFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.map function"
                let mapResult ←
                  extractValueFrom ctx (.value payload :: locals) optionResult.snd mapBody
                let nonePayload ← defaultValue resultTy
                .ok
                  (wrapValueLets lets
                    (mkOptionValue tag
                      (← valueIte (.eqU64 tag (.u64 0)) nonePayload mapResult.fst)),
                    mapResult.snd)
            | _, _ => .error "unsupported Option.map application"
        | (.const ``Option.filter _, args) =>
            match args.reverse, optionConstructorType? ctx.env args with
            | optionValue :: predicate :: _, some payloadTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let predicateBody ←
                  match collectLambdas predicate 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.filter predicate"
                let predicateResult ←
                  extractCondFrom ctx (.value payload :: locals) optionResult.snd predicateBody
                let nonePayload ← defaultValue payloadTy
                let keep :=
                  .and (.not (.eqU64 tag (.u64 0))) predicateResult.fst
                .ok
                  (wrapValueLets lets
                    (mkOptionValue (.ite keep (.u64 1) (.u64 0))
                      (← valueIte keep payload nonePayload)),
                    predicateResult.snd)
            | _, _ => .error "unsupported Option.filter application"
        | (.const ``Option.bind _, args) =>
            match args.reverse, optionMapResultType? ctx.env args with
            | bindFn :: optionValue :: _, some resultTy =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let lets := parts.fst
                let tag := parts.snd.fst
                let payload := parts.snd.snd
                let bindBody ←
                  match collectLambdas bindFn 1 with
                  | some body => .ok body
                  | none => .error "unsupported Option.bind function"
                let bindResult ←
                  extractValueFrom ctx (.value payload :: locals) optionResult.snd bindBody
                let bindParts ← optionPartsWithLets bindResult.fst
                let bindLets := bindParts.fst
                let bindTag := wrapExprLets bindLets bindParts.snd.fst
                let bindPayload := wrapValueLets bindLets bindParts.snd.snd
                let nonePayload ← defaultValue resultTy
                .ok
                  (wrapValueLets lets
                    (mkOptionValue
                      (.ite (.eqU64 tag (.u64 0)) (.u64 0) bindTag)
                      (← valueIte (.eqU64 tag (.u64 0)) nonePayload bindPayload)),
                    bindResult.snd)
            | _, _ => .error "unsupported Option.bind application"
        | (.const ``GetElem?.getElem? _, args) =>
            match args.reverse with
            | index :: array :: _ =>
                match primitiveReceiverType? ctx.env args with
                | some (.array itemTy) =>
                  match arrayElementSlots? itemTy with
                  | some _width =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let arraySlot := indexResult.snd
                    let indexSlot := arraySlot + 1
                    let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                    let tag := boolExpr inBounds
                    let payload ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                    let defaultPayload ← defaultValue itemTy
                    .ok
                      (.letE arraySlot arrayResult.fst
                        (.letE indexSlot indexResult.fst
                          (mkOptionValue tag (← valueIte inBounds payload defaultPayload))),
                        indexSlot + 1)
                  | none =>
                    .error s!"unsupported GetElem?.getElem? receiver type: {reprStr ((.array itemTy : Ty))}"
                | some .byteArray =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let ptrSlot := indexResult.snd
                    let lenSlot := ptrSlot + 1
                    let indexSlot := ptrSlot + 2
                    let inBounds := .ltU64 (.local indexSlot) (.local lenSlot)
                    let tag := boolExpr inBounds
                    let payload :=
                      .scalar
                        (.byteArrayGet (.local ptrSlot) (.local lenSlot) (.local indexSlot))
                    let defaultPayload ← defaultValue .u8
                    .ok
                      (wrapValueLets parts.fst
                        (.letE ptrSlot parts.snd.fst
                          (.letE lenSlot parts.snd.snd
                            (.letE indexSlot indexResult.fst
                              (mkOptionValue tag (← valueIte inBounds payload defaultPayload))))),
                        indexSlot + 1)
                | some other =>
                    .error s!"unsupported GetElem?.getElem? receiver type: {reprStr other}"
                | none => .error "unsupported GetElem?.getElem? receiver type"
            | _ => .error "unsupported GetElem?.getElem? application"
        | (.const ``Array.findIdx? _, args) =>
            match args, args.reverse with
            | itemTyExpr :: _, array :: predicate :: _ =>
                match typeAtom? ctx.env itemTyExpr with
                | some itemTy =>
                  match arrayElementSlots? itemTy with
                  | some sourceWidth =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let itemStart := arrayResult.snd
                    let predicateBody ←
                      match collectLambdas predicate 1 with
                      | some body => .ok body
                      | none => .error "unsupported Array.findIdx? predicate"
                    let itemValue ← arrayLocalValue itemTy itemStart
                    let predicateResult ←
                      extractExprFrom ctx
                        (.value itemValue :: locals)
                        (itemStart + sourceWidth)
                        predicateBody
                    let tag :=
                      .arrayFindIdxSlots
                        sourceWidth arrayResult.fst itemStart predicateResult.fst false
                    let payload :=
                      .arrayFindIdxSlots
                        sourceWidth arrayResult.fst itemStart predicateResult.fst true
                    .ok (mkOptionValue tag (.scalar payload), predicateResult.snd)
                  | none => .error s!"unsupported Array.findIdx? item type: {reprStr itemTy}"
                | none => .error "unsupported Array.findIdx? item type"
            | _, _ => .error "unsupported Array.findIdx? application"
        | (.const ``Array.find? _, args) =>
            match args, args.reverse with
            | itemTyExpr :: _, array :: predicate :: _ =>
                match typeAtom? ctx.env itemTyExpr with
                | some itemTy =>
                  match arrayElementSlots? itemTy with
                  | some sourceWidth =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let itemStart := arrayResult.snd
                    let predicateBody ←
                      match collectLambdas predicate 1 with
                      | some body => .ok body
                      | none => .error "unsupported Array.find? predicate"
                    let itemValue ← arrayLocalValue itemTy itemStart
                    let predicateResult ←
                      extractExprFrom ctx
                        (.value itemValue :: locals)
                        (itemStart + sourceWidth)
                        predicateBody
                    let tag :=
                      .arrayFindIdxSlots
                        sourceWidth arrayResult.fst itemStart predicateResult.fst false
                    let payload ←
                      arrayFindValue
                        itemTy
                        sourceWidth
                        arrayResult.fst
                        itemStart
                        predicateResult.fst
                    .ok (mkOptionValue tag payload, predicateResult.snd)
                  | none => .error s!"unsupported Array.find? item type: {reprStr itemTy}"
                | none => .error "unsupported Array.find? item type"
            | _, _ => .error "unsupported Array.find? application"
        | (.const ``Array.get!Internal _, args) =>
            match args, args.reverse with
            | itemTy :: _, index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let value ← arrayLoadValue itemTy arrayResult.fst indexResult.fst
                    .ok (value, indexResult.snd)
                | none => .error "unsupported Array.get!Internal item type"
            | _, _ => .error "unsupported Array.get!Internal application"
        | (.const ``GetElem?.getElem! _, args) =>
            match args.reverse with
            | index :: array :: _ =>
                match primitiveReceiverType? ctx.env args with
                | some (.array itemTy) =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let value ← arrayLoadValue itemTy arrayResult.fst indexResult.fst
                    .ok (value, indexResult.snd)
                | some .byteArray =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok
                      (.scalar
                        (wrapExprLets parts.fst
                          (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst)),
                        indexResult.snd)
                | some other =>
                    .error s!"unsupported GetElem?.getElem! receiver type: {reprStr other}"
                | none => .error "unsupported GetElem?.getElem! receiver type"
            | _ => .error "unsupported GetElem?.getElem! application"
        | (.const ``GetElem.getElem _, args) =>
            match args.reverse with
            | _proof :: index :: array :: _ =>
                match primitiveReceiverType? ctx.env args with
                | some (.array itemTy) =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    let value ← arrayLoadValue itemTy arrayResult.fst indexResult.fst
                    .ok (value, indexResult.snd)
                | some .byteArray =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok
                      (.scalar
                        (wrapExprLets parts.fst
                          (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst)),
                        indexResult.snd)
                | some other =>
                    .error s!"unsupported GetElem.getElem receiver type: {reprStr other}"
                | none => .error "unsupported GetElem.getElem receiver type"
            | _ => .error "unsupported GetElem.getElem application"
        | (.const ``Array.back? _, args) =>
            match args, args.reverse with
            | itemTy :: _, array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    match arrayElementSlots? itemTy with
                    | some _width =>
                      let arrayResult ← extractExprFrom ctx locals nextLocal array
                      let arraySlot := arrayResult.snd
                      let hasItem := .not (.eqU64 (.arraySize (.local arraySlot)) (.u64 0))
                      let tag := boolExpr hasItem
                      let index := .u64Bin .sub (.arraySize (.local arraySlot)) (.u64 1)
                      let payload ← arrayLoadValue itemTy (.local arraySlot) index
                      let defaultPayload ← defaultValue itemTy
                      .ok
                        (.letE arraySlot arrayResult.fst
                          (mkOptionValue tag (← valueIte hasItem payload defaultPayload)),
                          arraySlot + 1)
                    | none => .error s!"unsupported Array.back? item type: {reprStr itemTy}"
                | none => .error "unsupported Array.back? item type"
            | _, _ => .error "unsupported Array.back? application"
        | (.const ``Array.back! _, args) =>
            match args, args.reverse with
            | itemTy :: _, array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let index := .u64Bin .sub (.arraySize arrayResult.fst) (.u64 1)
                    let value ← arrayLoadValue itemTy arrayResult.fst index
                    .ok (value, arrayResult.snd)
                | none => .error "unsupported Array.back! item type"
            | _, _ => .error "unsupported Array.back! application"
        | (.const ``Array.back _, args) =>
            match args, args.reverse with
            | itemTy :: _, _proof :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let index := .u64Bin .sub (.arraySize arrayResult.fst) (.u64 1)
                    let value ← arrayLoadValue itemTy arrayResult.fst index
                    .ok (value, arrayResult.snd)
                | none => .error "unsupported Array.back item type"
            | _, _ => .error "unsupported Array.back application"
        | (.const ``Array.getD _, args) =>
            match args, args.reverse with
            | itemTy :: _, defaultValue :: index :: array :: _ =>
                match typeAtom? ctx.env itemTy with
                | some itemTy =>
                    match arrayElementSlots? itemTy with
                    | some _width =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let defaultResult ← extractValueFrom ctx locals (indexSlot + 1) defaultValue
                        let loaded ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                        let selected ←
                          valueIte
                            (.ltU64 (.local indexSlot) (.arraySize (.local arraySlot)))
                            loaded
                            defaultResult.fst
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst selected),
                            defaultResult.snd)
                    | none => .error s!"unsupported Array.getD item type: {reprStr itemTy}"
                | none => .error "unsupported Array.getD item type"
            | _, _ => .error "unsupported Array.getD application"
        | (.const ``ByteArray.extract _, args) =>
            match args with
            | [array, start, stop] =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayFullPartsWithLets arrayResult.fst
                let startResult ← extractExprFrom ctx locals arrayResult.snd start
                let stopResult ← extractExprFrom ctx locals startResult.snd stop
                let ownerSlot := stopResult.snd
                let ptrSlot := ownerSlot + 1
                let lenSlot := ownerSlot + 2
                let startSlot := ownerSlot + 3
                let stopSlot := ownerSlot + 4
                let effectiveStop :=
                  .ite
                    (.ltU64 (.local stopSlot) (.local lenSlot))
                    (.local stopSlot)
                    (.local lenSlot)
                let nonempty :=
                  .and
                    (.ltU64 (.local startSlot) (.local lenSlot))
                    (.ltU64 (.local startSlot) effectiveStop)
                let slicePtr := .u64Bin .add (.local ptrSlot) (.local startSlot)
                let sliceLen :=
                  .ite nonempty (.u64Bin .sub effectiveStop (.local startSlot)) (.u64 0)
                .ok
                  (wrapValueLets parts.fst
                    (.letE ownerSlot parts.snd.owner
                      (.letE ptrSlot parts.snd.ptr
                        (.letE lenSlot parts.snd.len
                          (.letE startSlot startResult.fst
                            (.letE stopSlot stopResult.fst
                              (.byteArray (.local ownerSlot) slicePtr sliceLen)))))),
                    stopSlot + 1)
            | _ => .error "unsupported ByteArray.extract application"
        | (.const ``ByteArray.push _, args) =>
            match args.reverse with
            | value :: array :: _ =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let valueResult ← extractExprFrom ctx locals arrayResult.snd value
                let valueSlot := valueResult.snd
                let ptrSlot := valueSlot + 1
                let lenSlot := valueSlot + 2
                let resultPtrSlot := valueSlot + 3
                .ok
                  (wrapValueLets parts.fst
                    (.letE valueSlot valueResult.fst
                      (.letE ptrSlot parts.snd.fst
                        (.letE lenSlot parts.snd.snd
                          (.letE resultPtrSlot
                            (.byteArrayPushPtr
                              (.local ptrSlot)
                              (.local lenSlot)
                              (.local valueSlot))
                            (.byteArray
                              (.local resultPtrSlot)
                              (.local resultPtrSlot)
                              (.u64Bin .add (.local lenSlot) (.u64 1))))))),
                    resultPtrSlot + 1)
            | _ => .error "unsupported ByteArray.push application"
        | (.const ``ByteArray.append _, args) =>
            match args with
            | [left, right] =>
                let leftResult ← extractValueFrom ctx locals nextLocal left
                let leftParts ← byteArrayPartsWithLets leftResult.fst
                let rightResult ← extractValueFrom ctx locals leftResult.snd right
                let rightParts ← byteArrayPartsWithLets rightResult.fst
                let leftPtrSlot := rightResult.snd
                let leftLenSlot := leftPtrSlot + 1
                let rightPtrSlot := leftPtrSlot + 2
                let rightLenSlot := leftPtrSlot + 3
                let resultPtrSlot := leftPtrSlot + 4
                .ok
                  (wrapValueLets (leftParts.fst ++ rightParts.fst)
                    (.letE leftPtrSlot leftParts.snd.fst
                      (.letE leftLenSlot leftParts.snd.snd
                        (.letE rightPtrSlot rightParts.snd.fst
                          (.letE rightLenSlot rightParts.snd.snd
                            (.letE resultPtrSlot
                              (.byteArrayAppendPtr
                                (.local leftPtrSlot)
                                (.local leftLenSlot)
                                (.local rightPtrSlot)
                                (.local rightLenSlot))
                              (.byteArray
                                (.local resultPtrSlot)
                                (.local resultPtrSlot)
                                (.u64Bin .add (.local leftLenSlot) (.local rightLenSlot)))))))),
                    resultPtrSlot + 1)
            | _ => .error "unsupported ByteArray.append application"
        | (.const ``HAppend.hAppend _, args) =>
            match args.reverse, primitiveResultType? ctx.env args with
            | _right :: _left :: _, some (.array _) =>
                let ptrResult ← extractExprFrom ctx locals nextLocal expr
                .ok (ownedArrayValue ptrResult.snd ptrResult.fst, ptrResult.snd + 1)
            | right :: left :: _, some .byteArray =>
                let leftResult ← extractValueFrom ctx locals nextLocal left
                let leftParts ← byteArrayPartsWithLets leftResult.fst
                let rightResult ← extractValueFrom ctx locals leftResult.snd right
                let rightParts ← byteArrayPartsWithLets rightResult.fst
                let leftPtrSlot := rightResult.snd
                let leftLenSlot := leftPtrSlot + 1
                let rightPtrSlot := leftPtrSlot + 2
                let rightLenSlot := leftPtrSlot + 3
                let resultPtrSlot := leftPtrSlot + 4
                .ok
                  (wrapValueLets (leftParts.fst ++ rightParts.fst)
                    (.letE leftPtrSlot leftParts.snd.fst
                      (.letE leftLenSlot leftParts.snd.snd
                        (.letE rightPtrSlot rightParts.snd.fst
                          (.letE rightLenSlot rightParts.snd.snd
                            (.letE resultPtrSlot
                              (.byteArrayAppendPtr
                                (.local leftPtrSlot)
                                (.local leftLenSlot)
                                (.local rightPtrSlot)
                                (.local rightLenSlot))
                              (.byteArray
                                (.local resultPtrSlot)
                                (.local resultPtrSlot)
                                (.u64Bin .add (.local leftLenSlot) (.local rightLenSlot)))))))),
                    resultPtrSlot + 1)
            | _, _ =>
                let scalarResult ← extractExprFrom ctx locals nextLocal expr
                .ok (.scalar scalarResult.fst, scalarResult.snd)
        | (.const ``ByteArray.set! _, args) =>
            match args.reverse with
            | value :: index :: array :: _ =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                let valueResult ← extractExprFrom ctx locals indexResult.snd value
                let indexSlot := valueResult.snd
                let valueSlot := indexSlot + 1
                let ptrSlot := indexSlot + 2
                let lenSlot := indexSlot + 3
                let resultPtrSlot := indexSlot + 4
                .ok
                  (wrapValueLets parts.fst
                    (.letE indexSlot indexResult.fst
                      (.letE valueSlot valueResult.fst
                        (.letE ptrSlot parts.snd.fst
                          (.letE lenSlot parts.snd.snd
                            (.letE resultPtrSlot
                              (.byteArraySetPtr
                                (.local ptrSlot)
                                (.local lenSlot)
                                (.local indexSlot)
                                (.local valueSlot))
                              (.byteArray
                                (.local resultPtrSlot)
                                (.local resultPtrSlot)
                                (.local lenSlot))))))),
                    resultPtrSlot + 1)
            | _ => .error "unsupported ByteArray.set! application"
        | (.const ``ByteArray.set _, args) =>
            match args.reverse with
            | _proof :: value :: index :: array :: _ =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                let valueResult ← extractExprFrom ctx locals indexResult.snd value
                let indexSlot := valueResult.snd
                let valueSlot := indexSlot + 1
                let ptrSlot := indexSlot + 2
                let lenSlot := indexSlot + 3
                let resultPtrSlot := indexSlot + 4
                .ok
                  (wrapValueLets parts.fst
                    (.letE indexSlot indexResult.fst
                      (.letE valueSlot valueResult.fst
                        (.letE ptrSlot parts.snd.fst
                          (.letE lenSlot parts.snd.snd
                            (.letE resultPtrSlot
                              (.byteArraySetPtr
                                (.local ptrSlot)
                                (.local lenSlot)
                                (.local indexSlot)
                                (.local valueSlot))
                              (.byteArray
                                (.local resultPtrSlot)
                                (.local resultPtrSlot)
                                (.local lenSlot))))))),
                    resultPtrSlot + 1)
            | _ => .error "unsupported ByteArray.set application"
        | (.const ``ByteArray.copySlice _, args) =>
            let copyArgs? :=
              match args.reverse with
              | _exact :: copyLen :: destOff :: dest :: srcOff :: src :: _ =>
                  some (src, srcOff, dest, destOff, copyLen)
              | copyLen :: destOff :: dest :: srcOff :: src :: [] =>
                  some (src, srcOff, dest, destOff, copyLen)
              | _ => none
            match copyArgs? with
            | some (src, srcOff, dest, destOff, copyLen) =>
                let srcResult ← extractValueFrom ctx locals nextLocal src
                let srcParts ← byteArrayPartsWithLets srcResult.fst
                let srcOffResult ← extractExprFrom ctx locals srcResult.snd srcOff
                let destResult ← extractValueFrom ctx locals srcOffResult.snd dest
                let destParts ← byteArrayPartsWithLets destResult.fst
                let destOffResult ← extractExprFrom ctx locals destResult.snd destOff
                let copyLenResult ← extractExprFrom ctx locals destOffResult.snd copyLen
                let srcPtrSlot := copyLenResult.snd
                let srcLenSlot := srcPtrSlot + 1
                let srcOffSlot := srcPtrSlot + 2
                let destPtrSlot := srcPtrSlot + 3
                let destLenSlot := srcPtrSlot + 4
                let destOffSlot := srcPtrSlot + 5
                let copyLenSlot := srcPtrSlot + 6
                let resultLenSlot := srcPtrSlot + 7
                let resultPtrSlot := srcPtrSlot + 8
                .ok
                  (wrapValueLets (srcParts.fst ++ destParts.fst)
                    (.letE srcPtrSlot srcParts.snd.fst
                      (.letE srcLenSlot srcParts.snd.snd
                        (.letE srcOffSlot srcOffResult.fst
                          (.letE destPtrSlot destParts.snd.fst
                            (.letE destLenSlot destParts.snd.snd
                              (.letE destOffSlot destOffResult.fst
                                (.letE copyLenSlot copyLenResult.fst
                                  (.letE resultLenSlot
                                    (byteArrayCopySliceResultLen
                                      (.local srcLenSlot)
                                      (.local srcOffSlot)
                                      (.local destLenSlot)
                                      (.local destOffSlot)
                                      (.local copyLenSlot))
                                    (.letE resultPtrSlot
                                      (.byteArrayCopySlicePtr
                                        (.local srcPtrSlot)
                                        (.local srcLenSlot)
                                        (.local srcOffSlot)
                                        (.local destPtrSlot)
                                        (.local destLenSlot)
                                        (.local destOffSlot)
                                        (.local copyLenSlot))
                                      (.byteArray
                                        (.local resultPtrSlot)
                                        (.local resultPtrSlot)
                                        (.local resultLenSlot))))))))))),
                    resultPtrSlot + 1)
            | none => .error "unsupported ByteArray.copySlice application"
        | (.const ``ByteArray.findIdx? _, args) =>
            let findArgs? :=
              match args.reverse with
              | start :: predicate :: array :: _ => some (array, predicate, some start)
              | predicate :: array :: [] => some (array, predicate, none)
              | _ => none
            match findArgs? with
            | some (array, predicate, start?) =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let startResult ←
                  match start? with
                  | some start => extractExprFrom ctx locals arrayResult.snd start
                  | none => .ok (.u64 0, arrayResult.snd)
                let byteSlot := startResult.snd
                let predicateBody ←
                  match collectLambdas predicate 1 with
                  | some body => .ok body
                  | none => .error "unsupported ByteArray.findIdx? predicate"
                let predicateResult ←
                  extractExprFrom ctx
                    (.value (.scalar (.local byteSlot)) :: locals)
                    (byteSlot + 1)
                    predicateBody
                let ptr := wrapExprLets parts.fst parts.snd.fst
                let len := wrapExprLets parts.fst parts.snd.snd
                let tag :=
                  .byteArrayFindIdx ptr len startResult.fst byteSlot predicateResult.fst false
                let payload :=
                  .byteArrayFindIdx ptr len startResult.fst byteSlot predicateResult.fst true
                .ok (mkOptionValue tag (.scalar payload), predicateResult.snd)
            | none => .error "unsupported ByteArray.findIdx? application"
        | (.const ``ByteArray.mk _, args) =>
            match args with
            | [array] =>
                let arrayResult ← extractExprFrom ctx locals nextLocal array
                let arraySlot := arrayResult.snd
                let ptrSlot := arraySlot + 1
                .ok
                  (.letE arraySlot arrayResult.fst
                    (.letE ptrSlot (.byteArrayFromArrayPtr (.local arraySlot))
                      (.byteArray
                        (.local ptrSlot)
                        (.local ptrSlot)
                        (.arraySize (.local arraySlot)))),
                    ptrSlot + 1)
            | _ => .error "unsupported ByteArray.mk application"
        | (.const ``String.toUTF8 _, args) =>
            match args with
            | [value] =>
                let bytes ←
                  asciiStringExprBytesFrom ctx locals value
                    "unsupported String.toUTF8 argument: expected compile-time string expression"
                    "unsupported String.toUTF8 string: expected ASCII"
                .ok (byteArrayLiteralValue nextLocal bytes)
            | _ => .error "unsupported String.toUTF8 application"
        | (.const ``Bool.casesOn _, args) =>
            match boolMatcherArgs? ctx.env (.const ``Bool.casesOn []) args with
            | some (scrutinee, falseArm, trueArm) =>
                let condResult ← extractCondFrom ctx locals nextLocal scrutinee
                let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
                let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
                .ok (← valueIte condResult.fst trueResult.fst falseResult.fst, trueResult.snd)
            | none => .error "unsupported Bool.casesOn application"
        | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
            match typeAtom? ctx.env ty with
            | some resultTy =>
                if supportedLocalType resultTy then
                  let condResult ← extractCondFrom ctx locals nextLocal condExpr
                  let thenResult ← extractValueFrom ctx locals condResult.snd thenExpr
                  let elseResult ← extractValueFrom ctx locals thenResult.snd elseExpr
                  .ok (← valueIte condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
                else
                  let exprResult ← extractExprFrom ctx locals nextLocal expr
                  .ok (.scalar exprResult.fst, exprResult.snd)
            | none =>
                let exprResult ← extractExprFrom ctx locals nextLocal expr
                .ok (.scalar exprResult.fst, exprResult.snd)
        | (.const ``dite _, [ty, condExpr, _, thenArm, elseArm]) =>
            match typeAtom? ctx.env ty with
            | some resultTy =>
                if supportedLocalType resultTy then
                  let condResult ← extractCondFrom ctx locals nextLocal condExpr
                  let thenResult ← extractUnitArmValueFrom ctx locals condResult.snd thenArm
                  let elseResult ← extractUnitArmValueFrom ctx locals thenResult.snd elseArm
                  .ok (← valueIte condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
                else
                  .error "unsupported dependent-if result type"
            | none => .error "unsupported dependent-if result type"
        | (fn, args) =>
            match fn.consumeMData with
            | .const name _ =>
                if name == ``PSum.inl then
                  match args with
                  | [_leftTyExpr, rightTyExpr, payload] =>
                      let rightTy ←
                        match typeAtom? ctx.env rightTyExpr with
                        | some ty => .ok ty
                        | none => .error "unsupported PSum.inl right type"
                      let payloadResult ← extractValueFrom ctx locals nextLocal payload
                      let rightDefault ← defaultValue rightTy
                      .ok (.sum (.u64 0) payloadResult.fst rightDefault, payloadResult.snd)
                  | _ => .error "unsupported PSum.inl application"
                else if name == ``PSum.inr then
                  match args with
                  | [leftTyExpr, _rightTyExpr, payload] =>
                      let leftTy ←
                        match typeAtom? ctx.env leftTyExpr with
                        | some ty => .ok ty
                        | none => .error "unsupported PSum.inr left type"
                      let leftDefault ← defaultValue leftTy
                      let payloadResult ← extractValueFrom ctx locals nextLocal payload
                      .ok (.sum (.u64 1) leftDefault payloadResult.fst, payloadResult.snd)
                  | _ => .error "unsupported PSum.inr application"
                else
                match structureConstructorForArgs? ctx.env name args with
                | some (structName, fieldKinds, runtimeArgs) =>
                    if runtimeArgs.length == fieldKinds.length then
                      let rec loop :
                          List Expr → List (Option Ty) → Nat →
                            Except String (List ExtractedValue × Nat)
                        | [], [], next => .ok ([], next)
                        | arg :: restArgs, some _ :: restKinds, next => do
                            let fieldResult ← extractValueFrom ctx locals next arg
                            let restResult ← loop restArgs restKinds fieldResult.snd
                            .ok (fieldResult.fst :: restResult.fst, restResult.snd)
                        | _arg :: restArgs, none :: restKinds, next =>
                            loop restArgs restKinds next
                        | _, _, _ => .error s!"structure constructor arity mismatch: {name}"
                      let result ← loop runtimeArgs fieldKinds nextLocal
                      .ok (.struct structName result.fst, result.snd)
                    else
                      .error s!"structure constructor arity mismatch: {name}"
                | none =>
                    match recursiveVariantConstructorForArgs? ctx.env name args with
                    | some (layout, ctorIndex, ctor, runtimeArgs) =>
                        if runtimeArgs.length == ctor.fields.length then
                          let rec recursiveVariantCtorLoop :
                              List Expr → List (Option Ty) → Nat →
                                Except String (List ExtractedValue × Nat)
                            | [], [], next => .ok ([], next)
                            | arg :: restArgs, some _ :: restKinds, next => do
                                let fieldResult ← extractValueFrom ctx locals next arg
                                let restResult ←
                                  recursiveVariantCtorLoop restArgs restKinds fieldResult.snd
                                .ok (fieldResult.fst :: restResult.fst, restResult.snd)
                            | _arg :: restArgs, none :: restKinds, next =>
                                recursiveVariantCtorLoop restArgs restKinds next
                            | _, _, _ => .error s!"inductive constructor arity mismatch: {name}"
                          let runtimeFields ← recursiveVariantCtorLoop runtimeArgs ctor.fields nextLocal
                          let defaults ← defaultCtorTypedValues layout.ctors
                          let activeFields ← typedFieldsFromKinds ctor.name ctor.fields runtimeFields.fst
                          let ctors ←
                            match replaceAt? ctorIndex activeFields defaults with
                            | some ctors => .ok ctors
                            | none => .error s!"inductive constructor index mismatch: {name}"
                          .ok
                            (.recursiveVariant layout.name (.u64 ctorIndex) ctors,
                              runtimeFields.snd)
                        else
                          .error s!"inductive constructor arity mismatch: {name}"
                    | none =>
                        match variantConstructorForArgs? ctx.env name args with
                        | some (layout, ctorIndex, ctor, runtimeArgs) =>
                            if runtimeArgs.length == ctor.fields.length then
                              let rec variantCtorLoop :
                                  List Expr → List (Option Ty) → Nat →
                                    Except String (List ExtractedValue × Nat)
                                | [], [], next => .ok ([], next)
                                | arg :: restArgs, some _ :: restKinds, next => do
                                    let fieldResult ← extractValueFrom ctx locals next arg
                                    let restResult ← variantCtorLoop restArgs restKinds fieldResult.snd
                                    .ok (fieldResult.fst :: restResult.fst, restResult.snd)
                                | _arg :: restArgs, none :: restKinds, next =>
                                    variantCtorLoop restArgs restKinds next
                                | _, _, _ => .error s!"inductive constructor arity mismatch: {name}"
                              let runtimeFields ← variantCtorLoop runtimeArgs ctor.fields nextLocal
                              let defaults ← defaultCtorValues layout.ctors
                              let ctors ←
                                match replaceAt? ctorIndex runtimeFields.fst defaults with
                                | some ctors => .ok ctors
                                | none => .error s!"inductive constructor index mismatch: {name}"
                              .ok (.variant layout.name (.u64 ctorIndex) ctors, runtimeFields.snd)
                            else
                              .error s!"inductive constructor arity mismatch: {name}"
                        | none =>
                            match structureProjectionForArgs? ctx.env name args with
                            | some (structName, some index, target) =>
                                let valueResult ← extractValueFrom ctx locals nextLocal target
                                .ok (← structField structName index valueResult.fst, valueResult.snd)
                            | some (_structName, none, _target) =>
                                .ok (.scalar (.u64 0), nextLocal)
                            | none =>
                                extractNonStructureValueFrom ctx locals nextLocal expr fn args
            | _ => extractNonStructureValueFrom ctx locals nextLocal expr fn args

  partial def extractNonStructureValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr fn : Expr)
      (args : List Expr) :
      Except String (ExtractedValue × Nat) := do
    match boolMatcherArgs? ctx.env fn args with
    | some (scrutinee, falseArm, trueArm) =>
        let condResult ← extractCondFrom ctx locals nextLocal scrutinee
        let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
        let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
        .ok (← valueIte condResult.fst trueResult.fst falseResult.fst, trueResult.snd)
    | none =>
        match exceptMatcherArgs? ctx.env fn args with
        | some (scrutinee, errorArm, okArm) =>
            extractExceptMatchValueFrom ctx locals nextLocal scrutinee errorArm okArm
        | none =>
            match optionMatcherArgs? ctx.env fn args with
            | some (scrutinee, noneArm, someArm) =>
                extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
            | none =>
                match natMatcherArgs? ctx.env fn args with
                | some (scrutinee, zeroArm, succArm) =>
                    extractNatMatchValueFrom ctx locals nextLocal scrutinee zeroArm succArm
                | none =>
                    match psumMatcherArgs? ctx.env fn args with
                    | some (_leftTy, _rightTy, scrutinee, leftArm, rightArm) =>
                        extractPsumMatchValueFrom ctx locals nextLocal scrutinee leftArm rightArm
                    | none =>
                            match productMatcherArgs? ctx.env fn args with
                            | some (scrutinee, arm) =>
                                extractProductMatchValueFrom ctx locals nextLocal scrutinee arm
                            | none =>
                                match structureMatcherArgs? ctx.env fn args with
                                | some (structName, fieldKinds, scrutinee, arm) =>
                                    extractStructureMatchValueFrom ctx locals nextLocal
                                      structName fieldKinds scrutinee arm
                                | none =>
                                    match variantMatcherArgs? ctx.env fn args with
                                    | some (layout, scrutinee, arms) =>
                                        extractVariantMatchValueFrom ctx locals nextLocal layout scrutinee arms
                                    | none =>
                                        match fn.consumeMData with
                                        | .const name _ =>
                                            if name == ``LeanExe.Runtime.release ||
                                                (args.isEmpty && (runtimeStatPrimitive? name).isSome) then
                                              let exprResult ←
                                                extractPrimitiveApplicationFrom ctx locals nextLocal name args
                                              .ok (.scalar exprResult.fst, exprResult.snd)
                                            else
                                              match ← extractInlineCallValueFrom ctx locals nextLocal name args with
                                              | some valueResult => .ok valueResult
                                              | none =>
                                                  match ← extractFunctionCallValueFrom ctx locals nextLocal name args with
                                                  | some valueResult => .ok valueResult
                                                  | none =>
                                                      let exprResult ← extractExprFrom ctx locals nextLocal expr
                                                      .ok (.scalar exprResult.fst, exprResult.snd)
                                        | _ =>
                                            let exprResult ← extractExprFrom ctx locals nextLocal expr
                                            .ok (.scalar exprResult.fst, exprResult.snd)

  partial def extractUnitArmValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (arm : Expr) :
      Except String (ExtractedValue × Nat) := do
    match collectLambdas arm 1 with
    | some body => extractValueFrom ctx (.value (.scalar (.u64 0)) :: locals) nextLocal body
    | none => extractValueFrom ctx locals nextLocal arm

  partial def extractOptionMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee noneArm someArm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let parts ← optionPartsWithLets scrutineeResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let payload := parts.snd.snd
    let noneArmResult ←
      match collectLambdas noneArm 1 with
      | some body => .ok (body, .value (.scalar (.u64 0)) :: locals)
      | none => .ok (noneArm, locals)
    let noneResult ←
      extractValueFrom ctx noneArmResult.snd scrutineeResult.snd noneArmResult.fst
    let someBody ←
      match collectLambdas someArm 1 with
      | some body => .ok body
      | none => .error "unsupported Option.some matcher arm"
    let someResult ←
      extractValueFrom ctx (.value payload :: locals) noneResult.snd someBody
    .ok
      (wrapValueLets lets
        (← valueIte (.eqU64 tag (.u64 0)) noneResult.fst someResult.fst),
        someResult.snd)

  partial def extractExceptMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee errorArm okArm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let parts ← exceptPartsWithLets scrutineeResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let errorPayload := parts.snd.snd.fst
    let okPayload := parts.snd.snd.snd
    let errorBody ←
      match collectLambdas errorArm 1 with
      | some body => .ok body
      | none => .error "unsupported Except.error matcher arm"
    let errorResult ←
      extractValueFrom ctx (.value errorPayload :: locals) scrutineeResult.snd errorBody
    let okBody ←
      match collectLambdas okArm 1 with
      | some body => .ok body
      | none => .error "unsupported Except.ok matcher arm"
    let okResult ←
      extractValueFrom ctx (.value okPayload :: locals) errorResult.snd okBody
    .ok
      (wrapValueLets lets
        (← valueIte (.eqU64 tag (.u64 0)) errorResult.fst okResult.fst),
        okResult.snd)

  partial def extractExceptOrElseValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (exceptValue fallback : Expr) :
      Except String (ExtractedValue × Nat) := do
    let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
    let parts ← exceptPartsWithLets exceptResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let errorPayload := parts.snd.snd.fst
    let okPayload := parts.snd.snd.snd
    let fallbackBody ←
      match collectLambdas fallback 1 with
      | some body => .ok body
      | none => .error "unsupported Except fallback"
    let fallbackResult ←
      extractValueFrom ctx (.value (.scalar (.u64 0)) :: locals) exceptResult.snd fallbackBody
    let fallbackParts ← exceptPartsWithLets fallbackResult.fst
    let fallbackLets := fallbackParts.fst
    let fallbackTag := wrapExprLets fallbackLets fallbackParts.snd.fst
    let fallbackError := wrapValueLets fallbackLets fallbackParts.snd.snd.fst
    let fallbackOk := wrapValueLets fallbackLets fallbackParts.snd.snd.snd
    let isError := .eqU64 tag (.u64 0)
    .ok
      (wrapValueLets lets
        (mkExceptValue
          (.ite isError fallbackTag tag)
          (← valueIte isError fallbackError errorPayload)
          (← valueIte isError fallbackOk okPayload)),
        fallbackResult.snd)

  partial def extractExceptTagExprFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (exceptValue : Expr) :
      Except String (IRExpr × Nat) := do
    let exceptResult ← extractValueFrom ctx locals nextLocal exceptValue
    let parts ← exceptPartsWithLets exceptResult.fst
    .ok (wrapExprLets parts.fst parts.snd.fst, exceptResult.snd)

  partial def extractOptionOrElseValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (optionValue fallback : Expr) :
      Except String (ExtractedValue × Nat) := do
    let optionResult ← extractValueFrom ctx locals nextLocal optionValue
    let parts ← optionPartsWithLets optionResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let payload := parts.snd.snd
    let fallbackBody ←
      match collectLambdas fallback 1 with
      | some body => .ok body
      | none => .error "unsupported Option.orElse fallback"
    let fallbackResult ←
      extractValueFrom ctx (.value (.scalar (.u64 0)) :: locals) optionResult.snd fallbackBody
    .ok
      (wrapValueLets lets
        (← valueIte (.eqU64 tag (.u64 0)) fallbackResult.fst (mkOptionValue tag payload)),
        fallbackResult.snd)

  partial def extractOptionPredicateCondFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr)
      (noneValue : Bool) :
      Except String (IRCond × Nat) := do
    match appFnArgs expr with
    | (.const name _, args) =>
        if name == ``Option.any || name == ``Option.all then
          match args.reverse with
          | optionValue :: predicate :: _ =>
              let optionResult ← extractValueFrom ctx locals nextLocal optionValue
              let parts ← optionPartsWithLets optionResult.fst
              let tag := parts.snd.fst
              let payload := parts.snd.snd
              let predicateBody ←
                match collectLambdas predicate 1 with
                | some body => .ok body
                | none => .error s!"unsupported {name} predicate"
              let predicateResult ←
                extractCondFrom ctx (.value payload :: locals) optionResult.snd predicateBody
              let cond :=
                if noneValue then
                  .or (.eqU64 tag (.u64 0)) predicateResult.fst
                else
                  .and (.not (.eqU64 tag (.u64 0))) predicateResult.fst
              .ok (boolCond (wrapExprLets parts.fst (boolExpr cond)), predicateResult.snd)
          | _ => .error s!"unsupported {name} application"
        else
          .error s!"unsupported option predicate application: {expr}"
    | _ => .error s!"unsupported option predicate application: {expr}"

  partial def extractNatMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee zeroArm succArm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractExprFrom ctx locals nextLocal scrutinee
    let scrutineeSlot := scrutineeResult.snd
    let predValue :=
      .scalar (.u64Bin .natSub (.local scrutineeSlot) (.u64 1))
    let zeroResult ←
      extractUnitArmValueFrom ctx locals (scrutineeSlot + 1) zeroArm
    let succBody ←
      match collectLambdas succArm 1 with
      | some body => .ok body
      | none => .error "unsupported Nat successor matcher arm"
    let succResult ←
      extractValueFrom ctx (.value predValue :: locals) zeroResult.snd succBody
    .ok
      (.letE scrutineeSlot scrutineeResult.fst
        (← valueIte (.eqU64 (.local scrutineeSlot) (.u64 0)) zeroResult.fst succResult.fst),
        succResult.snd)

  partial def extractProductMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee arm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let leftValue ← productField 0 scrutineeResult.fst
    let rightValue ← productField 1 scrutineeResult.fst
    let body ←
      match collectLambdas arm 2 with
      | some body => .ok body
      | none => .error "unsupported product matcher arm"
    extractValueFrom ctx (.value rightValue :: .value leftValue :: locals) scrutineeResult.snd body

  partial def extractStructureMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (structName : Name)
      (fieldKinds : List (Option Ty))
      (scrutinee arm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let rec fieldsFromKinds :
        Nat → List (Option Ty) → Except String (List ExtractedValue)
      | _, [] => .ok []
      | runtimeIndex, some _ :: rest => do
          let field ← structField structName runtimeIndex scrutineeResult.fst
          let restFields ← fieldsFromKinds (runtimeIndex + 1) rest
          .ok (field :: restFields)
      | runtimeIndex, none :: rest => do
          let restFields ← fieldsFromKinds runtimeIndex rest
          .ok (.scalar (.u64 0) :: restFields)
    let fieldValues ← fieldsFromKinds 0 fieldKinds
    let body ←
      match collectLambdas arm fieldKinds.length with
      | some body => .ok body
      | none => .error s!"unsupported structure matcher arm: {structName}"
    let fieldBindings := fieldValues.reverse.map Binding.value
    extractValueFrom ctx (fieldBindings ++ locals) scrutineeResult.snd body

  partial def extractPsumMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (scrutinee leftArm rightArm : Expr) :
      Except String (ExtractedValue × Nat) := do
    let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
    let parts ← sumPartsWithLets scrutineeResult.fst
    let lets := parts.fst
    let tag := parts.snd.fst
    let leftPayload := parts.snd.snd.fst
    let rightPayload := parts.snd.snd.snd
    let leftBody ←
      match collectLambdas leftArm 1 with
      | some body => .ok body
      | none => .error "unsupported PSum.inl matcher arm"
    let leftResult ←
      extractValueFrom ctx (.value leftPayload :: locals) scrutineeResult.snd leftBody
    let rightBody ←
      match collectLambdas rightArm 1 with
      | some body => .ok body
      | none => .error "unsupported PSum.inr matcher arm"
    let rightResult ←
      extractValueFrom ctx (.value rightPayload :: locals) leftResult.snd rightBody
    .ok
      (wrapValueLets lets
        (← valueIte (.eqU64 tag (.u64 0)) leftResult.fst rightResult.fst),
        rightResult.snd)

  partial def extractVariantMatchValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (layout : VariantLayout)
      (scrutinee : Expr)
      (arms : List Expr) :
      Except String (ExtractedValue × Nat) := do
    if arms.length != layout.ctors.length then
      .error s!"inductive matcher arity mismatch: {layout.name}"
    else
      let scrutineeResult ← extractValueFrom ctx locals nextLocal scrutinee
      if (recursiveVariantLayout? ctx.env layout.name layout.params).isSome then
        match heapVariantPtrWithLets? layout.name scrutineeResult.fst with
        | some parts =>
            let ptrSlot := scrutineeResult.snd
            let ptrExpr := wrapExprLets parts.fst parts.snd
            let ptrLocal : IRExpr := .local ptrSlot
            let tag := .heapLoadSlot ptrLocal 0
            let rec heapExtractArms :
                List VariantCtorLayout → List Expr → Nat → Nat →
                  Except String (List ExtractedValue × Nat)
              | [], [], _, next => .ok ([], next)
              | ctor :: restCtors, arm :: restArms, payloadSlot, next => do
                  let runtimeFields ← heapRuntimeFieldsFromKinds ptrLocal ctor.fields payloadSlot
                  let sourceBindings ←
                    sourceFieldBindingsFromKinds layout.name ctor.fields runtimeFields.fst
                  let armResult ←
                    if ctor.fields.isEmpty then
                      extractUnitArmValueFrom ctx locals next arm
                    else
                      let body ←
                        match collectLambdas arm ctor.fields.length with
                        | some body => .ok body
                        | none => .error s!"unsupported inductive matcher arm: {ctor.name}"
                      extractValueFrom ctx (sourceBindings.reverse ++ locals) next body
                  let restResult ←
                    heapExtractArms restCtors restArms runtimeFields.snd armResult.snd
                  .ok (armResult.fst :: restResult.fst, restResult.snd)
              | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
            let armResults ← heapExtractArms layout.ctors arms 1 (ptrSlot + 1)
            let rec heapCombine : List (Nat × ExtractedValue) → Except String ExtractedValue
              | [] => .error s!"inductive matcher has no arms: {layout.name}"
              | [(_index, value)] => .ok value
              | (index, value) :: rest => do
                  let elseValue ← heapCombine rest
                  valueIte (.eqU64 tag (.u64 index)) value elseValue
            .ok (.letE ptrSlot ptrExpr (← heapCombine (enumerate armResults.fst)),
              armResults.snd)
        | none =>
            let parts ← recursiveVariantPartsWithLets layout.name scrutineeResult.fst
            let lets := parts.fst
            let tag := parts.snd.fst
            let ctorValues := parts.snd.snd
            if ctorValues.length != layout.ctors.length then
              .error s!"inductive matcher value shape mismatch: {layout.name}"
            else
              let rec recursiveExtractArms :
                  List VariantCtorLayout → List (List ExtractedValue) → List Expr → Nat →
                    Except String (List ExtractedValue × Nat)
                | [], [], [], next => .ok ([], next)
                | ctor :: restCtors, fields :: restFields, arm :: restArms, next => do
                    let sourceBindings ← sourceFieldBindingsFromKinds layout.name ctor.fields fields
                    let armResult ←
                      if ctor.fields.isEmpty then
                        extractUnitArmValueFrom ctx locals next arm
                      else
                        let body ←
                          match collectLambdas arm ctor.fields.length with
                          | some body => .ok body
                          | none => .error s!"unsupported inductive matcher arm: {ctor.name}"
                        extractValueFrom ctx (sourceBindings.reverse ++ locals) next body
                    let restResult ←
                      recursiveExtractArms restCtors restFields restArms armResult.snd
                    .ok (armResult.fst :: restResult.fst, restResult.snd)
                | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
              let armResults ←
                recursiveExtractArms layout.ctors ctorValues arms scrutineeResult.snd
              let rec recursiveCombine : List (Nat × ExtractedValue) → Except String ExtractedValue
                | [] => .error s!"inductive matcher has no arms: {layout.name}"
                | [(_index, value)] => .ok value
                | (index, value) :: rest => do
                    let elseValue ← recursiveCombine rest
                    valueIte (.eqU64 tag (.u64 index)) value elseValue
              .ok (wrapValueLets lets (← recursiveCombine (enumerate armResults.fst)),
                armResults.snd)
      else
        let parts ← variantPartsWithLets layout.name scrutineeResult.fst
        let lets := parts.fst
        let tag := parts.snd.fst
        let ctorValues := parts.snd.snd
        if ctorValues.length != layout.ctors.length then
          .error s!"inductive matcher value shape mismatch: {layout.name}"
        else
          let rec variantExtractArms :
              List VariantCtorLayout → List (List ExtractedValue) → List Expr → Nat →
                Except String (List ExtractedValue × Nat)
            | [], [], [], next => .ok ([], next)
            | ctor :: restCtors, fields :: restFields, arm :: restArms, next => do
                let sourceBindings ← sourceFieldBindingsFromKinds layout.name ctor.fields fields
                let armResult ←
                  if ctor.fields.isEmpty then
                    extractUnitArmValueFrom ctx locals next arm
                  else
                    let body ←
                      match collectLambdas arm ctor.fields.length with
                      | some body => .ok body
                      | none => .error s!"unsupported inductive matcher arm: {ctor.name}"
                    extractValueFrom ctx (sourceBindings.reverse ++ locals) next body
                let restResult ← variantExtractArms restCtors restFields restArms armResult.snd
                .ok (armResult.fst :: restResult.fst, restResult.snd)
            | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
          let armResults ← variantExtractArms layout.ctors ctorValues arms scrutineeResult.snd
          let rec variantCombine : List (Nat × ExtractedValue) → Except String ExtractedValue
            | [] => .error s!"inductive matcher has no arms: {layout.name}"
            | [(_index, value)] => .ok value
            | (index, value) :: rest => do
                let elseValue ← variantCombine rest
                valueIte (.eqU64 tag (.u64 index)) value elseValue
          .ok (wrapValueLets lets (← variantCombine (enumerate armResults.fst)), armResults.snd)

  partial def extractInlineCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (name : Name)
      (args : List Expr) :
      Except String (Option (ExtractedValue × Nat)) := do
    if name.getRoot != ctx.root then
      return none
    if ctx.inlineStack.contains name then
      return none
    let info ←
      match ctx.env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during extraction: {name}"
    if containsConstant ``Nat.brecOn info || containsConstant name info then
      return none
    let specialization ←
      match supportedInlineFunction? ctx.env info with
      | some sig => .ok ({ sig := sig, staticArgs := [], runtimeArgs := args } : InlineSpecialization)
      | none =>
          match specializedInlineCall? ctx.env info args with
          | some specialization => .ok specialization
          | none => .error s!"unsupported function type or declaration: {name}"
    if specialization.runtimeArgs.length != specialization.sig.params.length then
      .error s!"inline call arity mismatch: {name}"
    else
      if (functionIndex? ctx name).isSome &&
          strictCallSafe ctx name args &&
          strictCallMaterializationSafe ctx specialization.sig.params specialization.runtimeArgs then
        return none
      let value ←
        match info.value? with
        | some value => .ok (betaSpecializeExpr ctx.env ctx.root 32 value)
        | none => .error s!"declaration has no executable value: {name}"
      let value ←
        match instantiateLeadingLambdas value specialization.staticArgs with
        | some value => .ok (betaSpecializeExpr ctx.env ctx.root 32 value)
        | none => .error s!"definition body does not match static function arity: {name}"
      let body ←
        match collectLambdas value specialization.sig.params.length with
        | some body => .ok body
        | none => .error s!"definition body does not match function arity: {name}"
      let argBindings := specialization.runtimeArgs.reverse.map (fun arg => Binding.thunk locals arg)
      let inlineCtx := { ctx with inlineStack := name :: ctx.inlineStack }
      let result ← extractValueFrom inlineCtx argBindings nextLocal body
      .ok (some result)

  partial def extractFunctionCallValueFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (name : Name)
      (args : List Expr) :
      Except String (Option (ExtractedValue × Nat)) := do
    match functionIndex? ctx name with
    | none => .ok none
    | some index =>
        strictRecursiveCallCheck ctx name args
        let sig ←
          match ctx.env.find? name with
          | some info =>
              match supportedFunction? ctx.env info with
              | some sig => .ok sig
              | none => .error s!"unsupported function type or declaration: {name}"
          | none => .error s!"declaration disappeared during extraction: {name}"
        strictCallMaterializationCheck ctx name sig.params args
        let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
        let slotCount := internalSlots sig.result
        let slotStart := argsResult.nextLocal
        let slots := (List.range slotCount).map (fun offset => slotStart + offset)
        let value := valueFromInternalSlots sig.result fun offset => .local (slotStart + offset)
        .ok
          (some
            (wrapValueLets argsResult.lets (.letCall slots index argsResult.args value),
              slotStart + slotCount))

  partial def extractExprFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String (IRExpr × Nat) := do
    match expr.consumeMData with
    | .bvar index =>
        match ← lookupBinding locals index with
        | .slot slot => .ok (.local slot, nextLocal)
        | .value value =>
            match scalarValue value with
            | .ok expr => .ok (expr, nextLocal)
            | .error message => .error s!"{message} while extracting bvar {index}"
        | .thunk savedLocals value =>
            let valueResult ← extractValueFrom ctx savedLocals nextLocal value
            .ok (← scalarValue valueResult.fst, valueResult.snd)
        | .structuralRec _ _ => .error "structural recursion handle used as a value"
        | .structuralBelow _ => .error "structural recursion below value used as a value"
        | .wfRecursor _ => .error "well-founded recursion handle used as a value"
        | .natRecursor _ => .error "Nat recursion handle used as a value"
        | .recursor => .error "recursive handle used as a value"
    | .letE _ type value body _ =>
        if !containsBVar 0 body then
          extractExprFrom ctx (.recursor :: locals) nextLocal body
        else if isStringType type then
          extractExprFrom ctx (.thunk locals value :: locals) nextLocal body
        else
          match typeAtom? ctx.env type with
          | some ty =>
              if supportedLocalType ty then
                extractExprFrom ctx (.thunk locals value :: locals) nextLocal body
              else
                .error s!"unsupported let-bound type: {type}"
          | none => .error s!"unsupported let-bound type: {type}"
    | .proj ``PProd index body =>
        let valueResult ← extractValueFrom ctx locals nextLocal (.proj ``PProd index body)
        .ok (← scalarValue valueResult.fst, valueResult.snd)
    | .proj ``Prod index body =>
        let valueResult ← extractValueFrom ctx locals nextLocal body
        .ok (← scalarValue (← productField index valueResult.fst), valueResult.snd)
    | .proj typeName index body =>
        match structureFieldKinds? ctx.env typeName with
        | some kinds =>
            match runtimeFieldIndexFromKinds index kinds with
            | some (some runtimeIndex) =>
                let valueResult ← extractValueFrom ctx locals nextLocal body
                .ok (← scalarValue (← structField typeName runtimeIndex valueResult.fst),
                  valueResult.snd)
            | some none => .ok (.u64 0, nextLocal)
            | none => .error s!"unsupported structure projection index: {typeName}.{index}"
        | none => .error s!"unsupported projection: {typeName}"
    | .const ``Unit.unit _ => .ok (.u64 0, nextLocal)
    | .const ``Bool.true _ => .ok (.u64 1, nextLocal)
    | .const ``Bool.false _ => .ok (.u64 0, nextLocal)
    | .const name _ =>
        match runtimeStatPrimitive? name with
        | some stat => .ok (.runtimeStat stat, nextLocal)
        | none =>
            match constNatValue? ctx.env name with
            | some value => .ok (← boundedNatExpr value, nextLocal)
            | none =>
                match functionIndex? ctx name with
                | some index => .ok (.call index [], nextLocal)
                | none => .error s!"unsupported constant in expression: {name}"
    | _ =>
        match scalarLiteralExpr? expr with
        | some result => .ok (← result, nextLocal)
        | none =>
          match appFnArgs expr with
            | (.bvar index, args) =>
                match ← lookupBinding locals index with
                | .wfRecursor functionName =>
                    let valueResult ←
                      extractWfRecursorCallValueFrom ctx locals nextLocal functionName args
                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                | .natRecursor functionName =>
                    let valueResult ←
                      extractNatRecursorCallValueFrom ctx locals nextLocal functionName args
                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                | _ => .error s!"unsupported expression: {expr}"
            | (.proj ``PProd index body, extraArgs) =>
                match ← natRecursorProjection? locals (.proj ``PProd index body) with
                | some functionName =>
                    let valueResult ←
                      extractNatRecursorCallValueFrom ctx locals nextLocal functionName extraArgs
                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                | none =>
                    match ← structuralRecProjection? locals (.proj ``PProd index body) with
                    | some (functionName, arg, capturedArgs) =>
                        let valueResult ←
                          extractStructuralRecCallValueFrom ctx locals nextLocal
                            functionName arg capturedArgs extraArgs
                        .ok (← scalarValue valueResult.fst, valueResult.snd)
                    | none => .error "unsupported structural recursion projection"
            | (.const ``Bool.casesOn _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Option.getD _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Option.get! _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Option.elim _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Option.isSome _, args) =>
                match args.reverse with
                | optionValue :: _ =>
                    let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                    let parts ← optionPartsWithLets optionResult.fst
                    let tag := wrapExprLets parts.fst parts.snd.fst
                    .ok (boolExpr (.not (.eqU64 tag (.u64 0))), optionResult.snd)
                | _ => .error "unsupported Option.isSome application"
            | (.const ``Option.isNone _, args) =>
                match args.reverse with
                | optionValue :: _ =>
                    let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                    let parts ← optionPartsWithLets optionResult.fst
                    let tag := wrapExprLets parts.fst parts.snd.fst
                    .ok (boolExpr (.eqU64 tag (.u64 0)), optionResult.snd)
                | _ => .error "unsupported Option.isNone application"
            | (.const ``Option.any _, _) =>
                let condResult ← extractOptionPredicateCondFrom ctx locals nextLocal expr false
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Option.all _, _) =>
                let condResult ← extractOptionPredicateCondFrom ctx locals nextLocal expr true
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``id _, args) =>
                match args.reverse with
                | value :: _ =>
                    let valueResult ← extractValueFrom ctx locals nextLocal value
                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                | _ => .error "unsupported id application"
            | (.const ``Nat.blt _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Nat.ble _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Nat.beq _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``String.length _, args) =>
                match args with
                | [value] =>
                    let bytes ←
                      asciiStringExprBytesFrom ctx locals value
                        "unsupported String.length argument: expected compile-time string expression"
                        "unsupported String.length string: expected ASCII"
                    .ok (.u64 bytes.length, nextLocal)
                | _ => .error "unsupported String.length application"
            | (.const ``String.isEmpty _, args) =>
                match args with
                | [value] =>
                    let bytes ←
                      asciiStringExprBytesFrom ctx locals value
                        "unsupported String.isEmpty argument: expected compile-time string expression"
                        "unsupported String.isEmpty string: expected ASCII"
                    .ok (boolExpr (if bytes.isEmpty then .true else .false), nextLocal)
                | _ => .error "unsupported String.isEmpty application"
            | (.const ``Except.isOk _, args) =>
                match args.reverse, exceptPayloadType? ctx.env args with
                | exceptValue :: _, some _payloadTy =>
                    let tagResult ← extractExceptTagExprFrom ctx locals nextLocal exceptValue
                    .ok (boolExpr (.not (.eqU64 tagResult.fst (.u64 0))), tagResult.snd)
                | _, _ => .error "unsupported Except.isOk application"
            | (.const ``Decidable.decide _, [prop, _inst]) =>
                let condResult ← extractCondFrom ctx locals nextLocal prop
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Id.run _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Pure.pure _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Bind.bind _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
                if typeAtom? ctx.env ty |>.isSome then
                  let condResult ← extractCondFrom ctx locals nextLocal condExpr
                  let thenResult ← extractExprFrom ctx locals condResult.snd thenExpr
                  let elseResult ← extractExprFrom ctx locals thenResult.snd elseExpr
                  .ok (.ite condResult.fst thenResult.fst elseResult.fst, elseResult.snd)
                else
                  .error "unsupported if-result type"
            | (.const ``dite _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Bool.or _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.and _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.not _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``Bool.xor _, _) =>
                let condResult ← extractCondFrom ctx locals nextLocal expr
                .ok (boolExpr condResult.fst, condResult.snd)
            | (.const ``List.toArray _, args) =>
                match args with
                | [_itemTy, listExpr] =>
                    match listLiteralItems? ctx.env listExpr with
                    | some (itemTy, items) =>
                      match arrayElementSlots? itemTy with
                      | some width =>
                        let childMask := arrayElementChildMask itemTy
                        let rec build
                            (index next : Nat)
                            (arrayExpr : IRExpr)
                            (remaining : List Expr) :
                            Except String (IRExpr × Nat) := do
                          match remaining with
                          | [] => .ok (arrayExpr, next)
                          | item :: rest =>
                              let itemResult ← extractValueFrom ctx locals next item
                              let itemSlots ←
                                materializeStrictArrayElementSlots itemTy itemResult.fst itemResult.snd
                              let arraySlot := itemSlots.nextLocal
                              let updatedArray :=
                                wrapExprLets itemSlots.lets
                                  (.arraySetSlots
                                    width
                                    childMask
                                    (ownedChildMaskForStrictSlots childMask itemSlots)
                                    (.local arraySlot)
                                    (.u64 index)
                                    itemSlots.slots)
                              build (index + 1) (arraySlot + 1)
                                (.letE arraySlot arrayExpr updatedArray)
                                rest
                        build 0 nextLocal (.arrayAllocSlots width childMask (.u64 items.length)) items
                      | none => .error s!"unsupported List.toArray item type: {reprStr itemTy}"
                    | none => .error "unsupported List.toArray argument"
                | _ => .error "unsupported List.toArray application"
            | (.const ``Array.replicate _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: cells :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.replicate" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let cellsResult ← extractExprFrom ctx locals nextLocal cells
                        let valueResult ← extractValueFrom ctx locals cellsResult.snd value
                        let slots ←
                          materializeStrictArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let cellsSlot := slots.nextLocal
                        .ok
                          (.letE cellsSlot cellsResult.fst
                            (wrapExprLets slots.lets
                              (.arrayReplicateSlots
                                width childMask (ownedChildMaskForStrictSlots childMask slots)
                                (.local cellsSlot) slots.slots)),
                            cellsSlot + 1)
                    | none => .error "unsupported Array.replicate item type"
                | _, _ => .error "unsupported Array.replicate application"
            | (.const ``Array.size _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    .ok (.arraySize arrayResult.fst, arrayResult.snd)
                | _ => .error "unsupported Array.size application"
            | (.const ``Array.isEmpty _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    .ok (boolExpr (.eqU64 (.arraySize arrayResult.fst) (.u64 0)), arrayResult.snd)
                | _ => .error "unsupported Array.isEmpty application"
            | (.const ``Array.push _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.push" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let valueResult ← extractValueFrom ctx locals arrayResult.snd value
                        let slots ←
                          materializeStrictArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (wrapExprLets slots.lets
                              (.arrayPushSlots
                                width childMask (ownedChildMaskForStrictSlots childMask slots)
                                (.local arraySlot) slots.slots)),
                            arraySlot + 1)
                    | none => .error "unsupported Array.push item type"
                | _, _ => .error "unsupported Array.push application"
            | (.const ``Array.pop _, args) =>
                match args, args.reverse with
                | itemTy :: _, array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.pop" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        .ok (.arrayPopSlots width childMask arrayResult.fst, arrayResult.snd)
                    | none => .error "unsupported Array.pop item type"
                | _, _ => .error "unsupported Array.pop application"
            | (.const ``Array.eraseIdxIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.eraseIdxIfInBounds" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayEraseIfInBoundsSlots width childMask arrayResult.fst indexResult.fst,
                          indexResult.snd)
                    | none => .error "unsupported Array.eraseIdxIfInBounds item type"
                | _, _ => .error "unsupported Array.eraseIdxIfInBounds application"
            | (.const ``Array.eraseIdx _, args) =>
                match args, args.reverse with
                | itemTy :: _, _proof :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.eraseIdx" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayEraseIfInBoundsSlots width childMask arrayResult.fst indexResult.fst,
                          indexResult.snd)
                    | none => .error "unsupported Array.eraseIdx item type"
                | _, _ => .error "unsupported Array.eraseIdx application"
            | (.const ``Array.swapIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, right :: left :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.swapIfInBounds" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let leftResult ← extractExprFrom ctx locals arrayResult.snd left
                        let rightResult ← extractExprFrom ctx locals leftResult.snd right
                        .ok
                          (.arraySwapIfInBoundsSlots
                            width
                            childMask
                            arrayResult.fst
                            leftResult.fst
                            rightResult.fst,
                            rightResult.snd)
                    | none => .error "unsupported Array.swapIfInBounds item type"
                | _, _ => .error "unsupported Array.swapIfInBounds application"
            | (.const ``Array.swap _, args) =>
                match args, args.reverse with
                | itemTy :: _, _rightProof :: _leftProof :: right :: left :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.swap" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let leftResult ← extractExprFrom ctx locals arrayResult.snd left
                        let rightResult ← extractExprFrom ctx locals leftResult.snd right
                        .ok
                          (.arraySwapIfInBoundsSlots
                            width
                            childMask
                            arrayResult.fst
                            leftResult.fst
                            rightResult.fst,
                            rightResult.snd)
                    | none => .error "unsupported Array.swap item type"
                | _, _ => .error "unsupported Array.swap application"
            | (.const ``Array.reverse _, args) =>
                match args, args.reverse with
                | itemTy :: _, array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.reverse" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        .ok (.arrayReverseSlots width childMask arrayResult.fst, arrayResult.snd)
                    | none => .error "unsupported Array.reverse item type"
                | _, _ => .error "unsupported Array.reverse application"
            | (.const ``Array.insertIdx _, args) =>
                match args, args.reverse with
                | itemTy :: _, _proof :: value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.insertIdx" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ←
                          materializeStrictArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        let indexSlot := arraySlot + 1
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (wrapExprLets slots.lets
                                (.arrayInsertIfInBoundsSlots
                                  width
                                  childMask
                                  (ownedChildMaskForStrictSlots childMask slots)
                                  (.local arraySlot)
                                  (.local indexSlot)
                                  slots.slots))),
                            indexSlot + 1)
                    | none => .error "unsupported Array.insertIdx item type"
                | _, _ => .error "unsupported Array.insertIdx application"
            | (.const ``Array.insertIdx! _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.insertIdx!" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                        let slots ←
                          materializeStrictArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let inserted :=
                          wrapExprLets slots.lets
                            (.arrayInsertIfInBoundsSlots
                              width
                              childMask
                              (ownedChildMaskForStrictSlots childMask slots)
                              (.local arraySlot)
                              (.local indexSlot)
                              slots.slots)
                        let inBounds := .leU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds inserted .trap)),
                            slots.nextLocal)
                    | none => .error "unsupported Array.insertIdx! item type"
                | _, _ => .error "unsupported Array.insertIdx! application"
            | (.const ``Array.append _, args) =>
                match args, args.reverse with
                | itemTy :: _, right :: left :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.append" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let leftResult ← extractExprFrom ctx locals nextLocal left
                        let rightResult ← extractExprFrom ctx locals leftResult.snd right
                        .ok (.arrayAppendSlots width childMask leftResult.fst rightResult.fst,
                          rightResult.snd)
                    | none => .error "unsupported Array.append item type"
                | _, _ => .error "unsupported Array.append application"
            | (.const ``Array.insertIdxIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.insertIdxIfInBounds" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ← flattenArrayElementValue itemTy valueResult.fst
                        .ok
                          (.arrayInsertIfInBoundsSlots
                            width
                            childMask
                            (ownedChildMaskForSlots childMask slots)
                            arrayResult.fst
                            indexResult.fst
                            slots,
                            valueResult.snd)
                    | none => .error "unsupported Array.insertIdxIfInBounds item type"
                | _, _ => .error "unsupported Array.insertIdxIfInBounds application"
            | (.const ``HAppend.hAppend _, args) =>
                match args.reverse, primitiveResultType? ctx.env args with
                | right :: left :: _, some (.array itemTy) =>
                    let width ← arrayElementWidth "HAppend.hAppend" itemTy
                    let childMask := arrayElementChildMask itemTy
                    let leftResult ← extractExprFrom ctx locals nextLocal left
                    let rightResult ← extractExprFrom ctx locals leftResult.snd right
                    .ok (.arrayAppendSlots width childMask leftResult.fst rightResult.fst,
                      rightResult.snd)
                | _, _ => .error "unsupported HAppend.hAppend application"
            | (.const ``Array.modify _, args) =>
                match args, args.reverse with
                | itemTy :: _, modifyFn :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.modify" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let oldValue ← arrayLoadValue itemTy (.local arraySlot) (.local indexSlot)
                        let modifyBody ←
                          match collectLambdas modifyFn 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.modify function"
                        let modifiedResult ←
                          extractValueFrom ctx (.value oldValue :: locals) (indexSlot + 1) modifyBody
                        let slots ← flattenArrayElementValue itemTy modifiedResult.fst
                        let ownedMask := ownedChildMaskForSlots childMask slots
                        let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        let modifiedArray :=
                          .arraySetSlots width childMask ownedMask (.local arraySlot) (.local indexSlot)
                            slots
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds modifiedArray (.local arraySlot))),
                            modifiedResult.snd)
                    | none => .error "unsupported Array.modify item type"
                | _, _ => .error "unsupported Array.modify application"
            | (.const ``Array.extract _, args) =>
                match args, args.reverse with
                | itemTy :: _, stop :: start :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.extract" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startResult ← extractExprFrom ctx locals arrayResult.snd start
                        let stopResult ← extractExprFrom ctx locals startResult.snd stop
                        .ok
                          (.arrayExtractSlots
                            width childMask arrayResult.fst startResult.fst stopResult.fst,
                            stopResult.snd)
                    | none => .error "unsupported Array.extract item type"
                | _, _ => .error "unsupported Array.extract application"
            | (.const ``Array.map _, args) =>
                match args, args.reverse with
                | sourceTy :: resultTy :: _, array :: mapFn :: _ =>
                    match typeAtom? ctx.env sourceTy, typeAtom? ctx.env resultTy with
                    | some source, some result =>
                      match arrayElementSlots? source, arrayElementSlots? result with
                      | some sourceWidth, some resultWidth =>
                        let resultChildMask := arrayElementChildMask result
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let itemStart := arrayResult.snd
                        let mapBody ←
                          match collectLambdas mapFn 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.map function"
                        let itemValue ← arrayLocalValue source itemStart
                        let bodyResult ←
                          extractValueFrom ctx (.value itemValue :: locals)
                            (itemStart + sourceWidth) mapBody
                        let bodySlots ← flattenArrayElementValue result bodyResult.fst
                        let bodyOwnedMask := ownedChildMaskForSlots resultChildMask bodySlots
                        .ok
                          (.arrayMapSlots
                            sourceWidth
                            resultWidth
                            resultChildMask
                            bodyOwnedMask
                            arrayResult.fst
                            itemStart
                            bodySlots,
                            bodyResult.snd)
                      | _, _ =>
                        .error s!"unsupported Array.map item types: {reprStr source}, {reprStr result}"
                    | _, _ => .error "unsupported Array.map item types"
                | _, _ => .error "unsupported Array.map application"
            | (.const ``Array.any _, args) =>
                match args with
                | itemTyExpr :: array :: predicate :: rest =>
                    match typeAtom? ctx.env itemTyExpr with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some sourceWidth =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startStop ←
                          match rest with
                          | [] => .ok ((.u64 0, .arraySize arrayResult.fst), arrayResult.snd)
                          | [start] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                          | [start, stop] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              let stopResult ← extractExprFrom ctx locals startResult.snd stop
                              .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                          | _ => .error "unsupported Array.any application"
                        let itemStart := startStop.snd
                        let predicateBody ←
                          match collectLambdas predicate 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.any predicate"
                        let itemValue ← arrayLocalValue itemTy itemStart
                        let predicateResult ←
                          extractExprFrom ctx
                            (.value itemValue :: locals)
                            (itemStart + sourceWidth)
                            predicateBody
                        .ok
                          (.arrayAnySlots
                            sourceWidth
                            arrayResult.fst
                            startStop.fst.fst
                            startStop.fst.snd
                            itemStart
                            predicateResult.fst
                            false,
                            predicateResult.snd)
                      | none => .error s!"unsupported Array.any item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.any item type"
                | _ => .error "unsupported Array.any application"
            | (.const ``Array.all _, args) =>
                match args with
                | itemTyExpr :: array :: predicate :: rest =>
                    match typeAtom? ctx.env itemTyExpr with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some sourceWidth =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startStop ←
                          match rest with
                          | [] => .ok ((.u64 0, .arraySize arrayResult.fst), arrayResult.snd)
                          | [start] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                          | [start, stop] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              let stopResult ← extractExprFrom ctx locals startResult.snd stop
                              .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                          | _ => .error "unsupported Array.all application"
                        let itemStart := startStop.snd
                        let predicateBody ←
                          match collectLambdas predicate 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.all predicate"
                        let itemValue ← arrayLocalValue itemTy itemStart
                        let predicateResult ←
                          extractExprFrom ctx
                            (.value itemValue :: locals)
                            (itemStart + sourceWidth)
                            predicateBody
                        .ok
                          (.arrayAnySlots
                            sourceWidth
                            arrayResult.fst
                            startStop.fst.fst
                            startStop.fst.snd
                            itemStart
                            predicateResult.fst
                            true,
                            predicateResult.snd)
                      | none => .error s!"unsupported Array.all item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.all item type"
                | _ => .error "unsupported Array.all application"
            | (.const ``Array.filter _, args) =>
                match args with
                | itemTyExpr :: predicate :: array :: rest =>
                    match typeAtom? ctx.env itemTyExpr with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some sourceWidth =>
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let startStop ←
                          match rest with
                          | [] => .ok ((.u64 0, .arraySize arrayResult.fst), arrayResult.snd)
                          | [start] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              .ok ((startResult.fst, .arraySize arrayResult.fst), startResult.snd)
                          | [start, stop] =>
                              let startResult ← extractExprFrom ctx locals arrayResult.snd start
                              let stopResult ← extractExprFrom ctx locals startResult.snd stop
                              .ok ((startResult.fst, stopResult.fst), stopResult.snd)
                          | _ => .error "unsupported Array.filter application"
                        let itemStart := startStop.snd
                        let predicateBody ←
                          match collectLambdas predicate 1 with
                          | some body => .ok body
                          | none => .error "unsupported Array.filter predicate"
                        let itemValue ← arrayLocalValue itemTy itemStart
                        let predicateResult ←
                          extractExprFrom ctx
                            (.value itemValue :: locals)
                            (itemStart + sourceWidth)
                            predicateBody
                        .ok
                          (.arrayFilterSlots
                            sourceWidth
                            childMask
                            arrayResult.fst
                            startStop.fst.fst
                            startStop.fst.snd
                            itemStart
                            predicateResult.fst,
                            predicateResult.snd)
                      | none => .error s!"unsupported Array.filter item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.filter item type"
                | _ => .error "unsupported Array.filter application"
            | (.const ``Array.foldl _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``Array.empty _, args) =>
                match args with
                | [itemTy] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.empty" itemTy
                        let childMask := arrayElementChildMask itemTy
                        .ok (.arrayAllocSlots width childMask (.u64 0), nextLocal)
                    | none => .error "unsupported Array.empty item type"
                | _ => .error "unsupported Array.empty application"
            | (.const ``Array.mkEmpty _, args) =>
                match args with
                | [itemTy, _capacity] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.mkEmpty" itemTy
                        let childMask := arrayElementChildMask itemTy
                        .ok (.arrayAllocSlots width childMask (.u64 0), nextLocal)
                    | none => .error "unsupported Array.mkEmpty item type"
                | _ => .error "unsupported Array.mkEmpty application"
            | (.const ``Array.emptyWithCapacity _, args) =>
                match args with
                | [itemTy, _capacity] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.emptyWithCapacity" itemTy
                        let childMask := arrayElementChildMask itemTy
                        .ok (.arrayAllocSlots width childMask (.u64 0), nextLocal)
                    | none => .error "unsupported Array.emptyWithCapacity item type"
                | _ => .error "unsupported Array.emptyWithCapacity application"
            | (.const ``Array.singleton _, args) =>
                match args with
                | [itemTy, value] =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.singleton" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let valueResult ← extractValueFrom ctx locals nextLocal value
                        let slots ←
                          materializeStrictArrayElementSlots itemTy valueResult.fst valueResult.snd
                        .ok
                          (wrapExprLets slots.lets
                            (.arraySetSlots
                              width
                              childMask
                              (ownedChildMaskForStrictSlots childMask slots)
                              (.arrayAllocSlots width childMask (.u64 1))
                              (.u64 0)
                              slots.slots),
                            slots.nextLocal)
                    | none => .error "unsupported Array.singleton item type"
                | _ => .error "unsupported Array.singleton application"
            | (.const ``Array.get!Internal _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok (.arrayGetSlot 1 0 arrayResult.fst indexResult.fst, indexResult.snd)
                | _ => .error "unsupported Array.get!Internal application"
            | (.const ``GetElem?.getElem! _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    match primitiveReceiverType? ctx.env args with
                    | some .byteArray =>
                        let arrayResult ← extractValueFrom ctx locals nextLocal array
                        let parts ← byteArrayPartsWithLets arrayResult.fst
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok
                          (wrapExprLets parts.fst
                            (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst),
                            indexResult.snd)
                    | _ =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayGetSlot 1 0 arrayResult.fst indexResult.fst, indexResult.snd)
                | _ => .error "unsupported GetElem?.getElem! application"
            | (.const ``GetElem.getElem _, args) =>
                match args.reverse with
                | _proof :: index :: array :: _ =>
                    match primitiveReceiverType? ctx.env args with
                    | some .byteArray =>
                        let arrayResult ← extractValueFrom ctx locals nextLocal array
                        let parts ← byteArrayPartsWithLets arrayResult.fst
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok
                          (wrapExprLets parts.fst
                            (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst),
                            indexResult.snd)
                    | _ =>
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        .ok (.arrayGetSlot 1 0 arrayResult.fst indexResult.fst, indexResult.snd)
                | _ => .error "unsupported GetElem.getElem application"
            | (.const ``Array.back! _, args) =>
                match args.reverse with
                | array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let slot := arrayResult.snd
                    let value :=
                      .arrayGetSlot 1 0 (.local slot) (.u64Bin .sub (.arraySize (.local slot)) (.u64 1))
                    .ok (.letE slot arrayResult.fst value, slot + 1)
                | _ => .error "unsupported Array.back! application"
            | (.const ``Array.back _, args) =>
                match args.reverse with
                | _proof :: array :: _ =>
                    let arrayResult ← extractExprFrom ctx locals nextLocal array
                    let slot := arrayResult.snd
                    let value :=
                      .arrayGetSlot 1 0 (.local slot) (.u64Bin .sub (.arraySize (.local slot)) (.u64 1))
                    .ok (.letE slot arrayResult.fst value, slot + 1)
                | _ => .error "unsupported Array.back application"
            | (.const ``Array.getD _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                let scalar ← scalarValue valueResult.fst
                .ok (scalar, valueResult.snd)
            | (.const ``Array.set _, args) =>
                match args, args.reverse with
                | itemTy :: _, _proof :: value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some width =>
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ←
                          materializeStrictArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        let indexSlot := arraySlot + 1
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (wrapExprLets slots.lets
                                (.arraySetSlots
                                  width
                                  childMask
                                  (ownedChildMaskForStrictSlots childMask slots)
                                  (.local arraySlot)
                                  (.local indexSlot)
                                  slots.slots))),
                            indexSlot + 1)
                      | none => .error s!"unsupported Array.set item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.set item type"
                | _, _ => .error "unsupported Array.set application"
            | (.const ``Array.setIfInBounds _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                      match arrayElementSlots? itemTy with
                      | some width =>
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let valueResult ← extractValueFrom ctx locals (indexSlot + 1) value
                        let slots ← flattenArrayElementValue itemTy valueResult.fst
                        let ownedMask := ownedChildMaskForSlots childMask slots
                        let updated :=
                          .arraySetSlots width childMask ownedMask (.local arraySlot) (.local indexSlot)
                            slots
                        let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds updated (.local arraySlot))),
                            valueResult.snd)
                      | none => .error s!"unsupported Array.setIfInBounds item type: {reprStr itemTy}"
                    | none => .error "unsupported Array.setIfInBounds item type"
                | _, _ => .error "unsupported Array.setIfInBounds application"
            | (.const ``Array.set! _, args) =>
                match args, args.reverse with
                | itemTy :: _, value :: index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.set!" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let valueResult ← extractValueFrom ctx locals indexResult.snd value
                        let slots ←
                          materializeStrictArrayElementSlots itemTy valueResult.fst valueResult.snd
                        let arraySlot := slots.nextLocal
                        let indexSlot := arraySlot + 1
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (wrapExprLets slots.lets
                                (.arraySetSlots
                                  width
                                  childMask
                                  (ownedChildMaskForStrictSlots childMask slots)
                                  (.local arraySlot)
                                  (.local indexSlot)
                                  slots.slots))),
                            indexSlot + 1)
                    | none => .error "unsupported Array.set! item type"
                | _, _ => .error "unsupported Array.set! application"
            | (.const ``Array.eraseIdx! _, args) =>
                match args, args.reverse with
                | itemTy :: _, index :: array :: _ =>
                    match typeAtom? ctx.env itemTy with
                    | some itemTy =>
                        let width ← arrayElementWidth "Array.eraseIdx!" itemTy
                        let childMask := arrayElementChildMask itemTy
                        let arrayResult ← extractExprFrom ctx locals nextLocal array
                        let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                        let arraySlot := indexResult.snd
                        let indexSlot := arraySlot + 1
                        let erased :=
                          .arrayEraseIfInBoundsSlots width childMask (.local arraySlot)
                            (.local indexSlot)
                        let inBounds := .ltU64 (.local indexSlot) (.arraySize (.local arraySlot))
                        .ok
                          (.letE arraySlot arrayResult.fst
                            (.letE indexSlot indexResult.fst
                              (.ite inBounds erased .trap)),
                            indexSlot + 1)
                    | none => .error "unsupported Array.eraseIdx! item type"
                | _, _ => .error "unsupported Array.eraseIdx! application"
            | (.const ``ByteArray.foldl _, _) =>
                let valueResult ← extractValueFrom ctx locals nextLocal expr
                .ok (← scalarValue valueResult.fst, valueResult.snd)
            | (.const ``ByteArray.size _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    .ok (wrapExprLets parts.fst parts.snd.snd, arrayResult.snd)
                | _ => .error "unsupported ByteArray.size application"
            | (.const ``ByteArray.isEmpty _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let len := wrapExprLets parts.fst parts.snd.snd
                    .ok (boolExpr (.eqU64 len (.u64 0)), arrayResult.snd)
                | _ => .error "unsupported ByteArray.isEmpty application"
            | (.const ``ByteArray.toUInt64LE! _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let ptrSlot := arrayResult.snd
                    let lenSlot := ptrSlot + 1
                    let ptr := wrapExprLets parts.fst parts.snd.fst
                    let len := wrapExprLets parts.fst parts.snd.snd
                    .ok
                      (.letE ptrSlot ptr
                        (.letE lenSlot len
                          (byteArrayLoadUInt64Checked
                            (.local ptrSlot)
                            (.local lenSlot)
                            [(0, 0), (1, 8), (2, 16), (3, 24),
                              (4, 32), (5, 40), (6, 48), (7, 56)])),
                        lenSlot + 1)
                | _ => .error "unsupported ByteArray.toUInt64LE! application"
            | (.const ``ByteArray.toUInt64BE! _, args) =>
                match args with
                | [array] =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let ptrSlot := arrayResult.snd
                    let lenSlot := ptrSlot + 1
                    let ptr := wrapExprLets parts.fst parts.snd.fst
                    let len := wrapExprLets parts.fst parts.snd.snd
                    .ok
                      (.letE ptrSlot ptr
                        (.letE lenSlot len
                          (byteArrayLoadUInt64Checked
                            (.local ptrSlot)
                            (.local lenSlot)
                            [(7, 0), (6, 8), (5, 16), (4, 24),
                              (3, 32), (2, 40), (1, 48), (0, 56)])),
                        lenSlot + 1)
                | _ => .error "unsupported ByteArray.toUInt64BE! application"
            | (.const ``ByteArray.get! _, args) =>
                match args.reverse with
                | index :: array :: _ =>
                    let arrayResult ← extractValueFrom ctx locals nextLocal array
                    let parts ← byteArrayPartsWithLets arrayResult.fst
                    let indexResult ← extractExprFrom ctx locals arrayResult.snd index
                    .ok
                      (wrapExprLets parts.fst
                        (.byteArrayGet parts.snd.fst parts.snd.snd indexResult.fst),
                        indexResult.snd)
                | _ => .error "unsupported ByteArray.get! application"
            | (.const ``Bool.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt64.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 value, nextLocal)
                | none => extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt64.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt64.toUInt8 _, [arg]) =>
                let argResult ← extractExprFrom ctx locals nextLocal arg
                .ok (.u64Bin .bitAnd argResult.fst (.u64 255), argResult.snd)
            | (.const ``UInt64.toUInt32 _, [arg]) =>
                let argResult ← extractExprFrom ctx locals nextLocal arg
                .ok (.u64Bin .bitAnd argResult.fst (.u64 (2 ^ 32 - 1)), argResult.snd)
            | (.const ``Nat.toUInt64 _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 value, nextLocal)
                | none => extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt32.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 (value % (2 ^ 32)), nextLocal)
                | none =>
                    let argResult ← extractExprFrom ctx locals nextLocal arg
                    .ok (.u64Bin .bitAnd argResult.fst (.u64 (2 ^ 32 - 1)), argResult.snd)
            | (.const ``UInt32.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt32.toUInt64 _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt32.toUInt8 _, [arg]) =>
                let argResult ← extractExprFrom ctx locals nextLocal arg
                .ok (.u64Bin .bitAnd argResult.fst (.u64 255), argResult.snd)
            | (.const ``UInt8.ofNat _, [arg]) =>
                match ofNat? ``Nat arg with
                | some value => .ok (.u64 (value % 256), nextLocal)
                | none =>
                    let argResult ← extractExprFrom ctx locals nextLocal arg
                    .ok (.u64Bin .bitAnd argResult.fst (.u64 255), argResult.snd)
            | (.const ``UInt8.toNat _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt8.toUInt64 _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``UInt8.toUInt32 _, [arg]) =>
                extractExprFrom ctx locals nextLocal arg
            | (.const ``Prod.fst _, args) =>
                match args.reverse with
                | product :: _ =>
                    let valueResult ← extractValueFrom ctx locals nextLocal product
                    .ok (← scalarValue (← productField 0 valueResult.fst), valueResult.snd)
                | _ => .error "unsupported Prod.fst application"
            | (.const ``Prod.snd _, args) =>
                match args.reverse with
                | product :: _ =>
                    let valueResult ← extractValueFrom ctx locals nextLocal product
                    .ok (← scalarValue (← productField 1 valueResult.fst), valueResult.snd)
                | _ => .error "unsupported Prod.snd application"
            | (.const ``Option.none _, _) =>
                .error "option value used where scalar value is required"
            | (.const ``Option.some _, _) =>
                .error "option value used where scalar value is required"
            | (.const ``Prod.mk _, _) =>
                .error "product value used where scalar value is required"
            | (.const primitive _, args) =>
                match expressionStructuralRecShape? ctx.env ctx.root expr with
                | some shape =>
                    match syntheticForShape? ctx shape with
                    | some synth =>
                        let scrutineeResult ← extractValueFrom ctx locals nextLocal shape.scrutinee
                        let valueResult ←
                          extractStructuralRecCallValueFrom ctx locals scrutineeResult.snd synth.name
                            scrutineeResult.fst [] (structuralExpressionCallExtraArgs shape)
                        .ok (← scalarValue valueResult.fst, valueResult.snd)
                    | none =>
                        .error s!"unsupported expression-level structural recursion: {shape.typeName}"
                | none =>
                match ← extractClosedStructuralPredicateExprFrom ctx locals nextLocal expr with
                | some result => .ok result
                | none =>
                    match structureProjectionForArgs? ctx.env primitive args with
                    | some (structName, some index, target) =>
                        let valueResult ← extractValueFrom ctx locals nextLocal target
                        .ok (← scalarValue (← structField structName index valueResult.fst),
                          valueResult.snd)
                    | some (_structName, none, _target) =>
                        .ok (.u64 0, nextLocal)
                    | none =>
                        match boolMatcherArgs? ctx.env (.const primitive []) args with
                        | some (scrutinee, falseArm, trueArm) =>
                            let condResult ← extractCondFrom ctx locals nextLocal scrutinee
                            let falseResult ← extractUnitArmValueFrom ctx locals condResult.snd falseArm
                            let trueResult ← extractUnitArmValueFrom ctx locals falseResult.snd trueArm
                            .ok
                              (← scalarValue
                                (← valueIte condResult.fst trueResult.fst falseResult.fst),
                                trueResult.snd)
                        | none =>
                            match exceptMatcherArgs? ctx.env (.const primitive []) args with
                            | some (scrutinee, errorArm, okArm) =>
                                let valueResult ←
                                  extractExceptMatchValueFrom ctx locals nextLocal scrutinee errorArm okArm
                                .ok (← scalarValue valueResult.fst, valueResult.snd)
                            | none =>
                                match optionMatcherArgs? ctx.env (.const primitive []) args with
                                | some (scrutinee, noneArm, someArm) =>
                                    let valueResult ←
                                      extractOptionMatchValueFrom ctx locals nextLocal scrutinee noneArm someArm
                                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                                | none =>
                                    match natMatcherArgs? ctx.env (.const primitive []) args with
                                    | some (scrutinee, zeroArm, succArm) =>
                                        let valueResult ←
                                          extractNatMatchValueFrom ctx locals nextLocal scrutinee zeroArm succArm
                                        .ok (← scalarValue valueResult.fst, valueResult.snd)
                                    | none =>
                                        match productMatcherArgs? ctx.env (.const primitive []) args with
                                        | some (scrutinee, arm) =>
                                            let valueResult ←
                                              extractProductMatchValueFrom ctx locals nextLocal scrutinee arm
                                            .ok (← scalarValue valueResult.fst, valueResult.snd)
                                        | none =>
                                            match structureMatcherArgs? ctx.env (.const primitive []) args with
                                            | some (structName, fieldKinds, scrutinee, arm) =>
                                                let valueResult ←
                                                  extractStructureMatchValueFrom ctx locals nextLocal
                                                    structName fieldKinds scrutinee arm
                                                .ok (← scalarValue valueResult.fst, valueResult.snd)
                                            | none =>
                                                match variantMatcherArgs? ctx.env (.const primitive []) args with
                                                | some (layout, scrutinee, arms) =>
                                                    let valueResult ←
                                                      extractVariantMatchValueFrom ctx locals nextLocal
                                                        layout scrutinee arms
                                                    .ok (← scalarValue valueResult.fst, valueResult.snd)
                                                | none =>
                                                    extractPrimitiveApplicationFrom ctx locals nextLocal
                                                      primitive args
            | (fn, _) => .error s!"unsupported expression: {fn}"

  partial def extractPrimitiveApplicationFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (primitive : Name)
      (args : List Expr) :
      Except String (IRExpr × Nat) := do
    if primitive == ``LeanExe.Runtime.release then
      match args.reverse with
      | value :: typeExpr :: _ =>
          let ty ←
            match typeAtom? ctx.env typeExpr with
            | some ty => .ok ty
            | none => .error "unsupported Runtime.release type"
          let valueResult ← extractValueFrom ctx locals nextLocal value
          match ty with
          | .recVariant name _ =>
              let parts ← heapVariantPtrWithLets name valueResult.fst
              .ok (.release (wrapExprLets parts.fst parts.snd), valueResult.snd)
          | .array _ =>
              let parts ← arrayFullPartsWithLets valueResult.fst
              .ok (.release (wrapExprLets parts.fst parts.snd.owner), valueResult.snd)
          | _ => .error s!"unsupported Runtime.release type: {reprStr ty}"
      | _ => .error "unsupported Runtime.release application"
    else
      match runtimeStatPrimitive? primitive, args with
      | some stat, [] => .ok (.runtimeStat stat, nextLocal)
      | some _, _ => .error s!"unsupported runtime stat application: {primitive}"
      | none, _ =>
        match ← extractInlineCallValueFrom ctx locals nextLocal primitive args with
        | some valueResult => .ok (← scalarValue valueResult.fst, valueResult.snd)
        | none =>
            match functionIndex? ctx primitive with
            | some index =>
                strictRecursiveCallCheck ctx primitive args
                let sig ←
                  match ctx.env.find? primitive with
                  | some info =>
                      match supportedFunction? ctx.env info with
                      | some sig => .ok sig
                      | none => .error s!"unsupported function type or declaration: {primitive}"
                  | none => .error s!"declaration disappeared during extraction: {primitive}"
                strictCallMaterializationCheck ctx primitive sig.params args
                let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
                .ok (wrapExprLets argsResult.lets (.call index argsResult.args), argsResult.nextLocal)
            | none =>
                if primitive == ``BEq.beq && primitiveStringReceiver? args then
                  match primitiveArgPair? args with
                  | some (left, right) =>
                      let leftBytes ←
                        asciiStringExprBytesFrom ctx locals left
                          "unsupported String equality argument: expected compile-time string expression"
                          "unsupported String equality string: expected ASCII"
                      let rightBytes ←
                        asciiStringExprBytesFrom ctx locals right
                          "unsupported String equality argument: expected compile-time string expression"
                          "unsupported String equality string: expected ASCII"
                      .ok (boolExpr (if leftBytes == rightBytes then .true else .false), nextLocal)
                  | none => .error "unsupported String equality application"
                else if primitive == ``bne && primitiveStringReceiver? args then
                  match primitiveArgPair? args with
                  | some (left, right) =>
                      let leftBytes ←
                        asciiStringExprBytesFrom ctx locals left
                          "unsupported String inequality argument: expected compile-time string expression"
                          "unsupported String inequality string: expected ASCII"
                      let rightBytes ←
                        asciiStringExprBytesFrom ctx locals right
                          "unsupported String inequality argument: expected compile-time string expression"
                          "unsupported String inequality string: expected ASCII"
                      .ok (boolExpr (if leftBytes == rightBytes then .false else .true), nextLocal)
                  | none => .error "unsupported String inequality application"
                else if primitive == ``BEq.beq || primitive == ``bne then
                  match primitiveArgPair? args, primitiveReceiverType? ctx.env args with
                  | some (left, right), some ty =>
                      if supportedEqType ty then
                        let eqResult ← extractStructuralEqExprFrom ctx locals nextLocal ty left right
                        if primitive == ``BEq.beq then
                          .ok eqResult
                        else
                          .ok (boolExpr (.not (boolCond eqResult.fst)), eqResult.snd)
                      else
                        .error s!"unsupported equality type: {reprStr ty}"
                  | _, _ => .error s!"unsupported equality application: {primitive}"
                else if primitive == ``Complement.complement then
                  match args.reverse with
                  | value :: _ =>
                      let valueResult ← extractExprFrom ctx locals nextLocal value
                      match primitiveReceiverType? ctx.env args with
                      | some .u8 =>
                          .ok (.u64Bin .bitXor valueResult.fst (.u64 255), valueResult.snd)
                      | some .u32 =>
                          .ok (.u64Bin .bitXor valueResult.fst (.u64 (2 ^ 32 - 1)),
                            valueResult.snd)
                      | some .u64 =>
                          .ok (.u64Bin .bitXor valueResult.fst (.u64 (runtimeNatLimit - 1)),
                            valueResult.snd)
                      | _ => .error s!"unsupported complement expression: {primitive}"
                  | _ => .error s!"unsupported complement expression: {primitive}"
                else if primitive == ``Nat.succ then
                  match args.reverse with
                  | value :: _ =>
                      let valueResult ← extractExprFrom ctx locals nextLocal value
                      .ok (.u64Bin .natAdd valueResult.fst (.u64 1), valueResult.snd)
                  | _ => .error "unsupported Nat.succ application"
                else if primitive == ``Nat.pred then
                  match args.reverse with
                  | value :: _ =>
                      let valueResult ← extractExprFrom ctx locals nextLocal value
                      .ok (.u64Bin .natSub valueResult.fst (.u64 1), valueResult.snd)
                  | _ => .error "unsupported Nat.pred application"
                else
                  match primitiveArgPair? args with
                  | some (left, right) =>
                      extractPrimitivePairFrom ctx locals nextLocal primitive args left right
                  | none => .error s!"unsupported application: {primitive}"

  partial def extractStructuralEqExprFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (ty : Ty)
      (left right : Expr) :
      Except String (IRExpr × Nat) := do
    let leftResult ← extractValueFrom ctx locals nextLocal left
    let rightResult ← extractValueFrom ctx locals leftResult.snd right
    structuralEqValueExpr rightResult.snd ty leftResult.fst rightResult.fst

  partial def extractPrimitivePairFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (primitive : Name)
      (args : List Expr)
      (left right : Expr) :
      Except String (IRExpr × Nat) := do
    let leftResult ← extractExprFrom ctx locals nextLocal left
    let rightResult ← extractExprFrom ctx locals leftResult.snd right
    let leftIR := leftResult.fst
    let rightIR := rightResult.fst
    if primitive == ``HAdd.hAdd then
      match primitiveResultType? ctx.env args with
      | some .nat =>
          .ok (.u64Bin .natAdd leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .add leftIR rightIR), rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .add leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .add leftIR rightIR, rightResult.snd)
    else if primitive == ``HSub.hSub then
      match primitiveResultType? ctx.env args with
      | some .nat =>
          .ok (.u64Bin .natSub leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .sub leftIR rightIR), rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .sub leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .sub leftIR rightIR, rightResult.snd)
    else if primitive == ``HMul.hMul then
      match primitiveResultType? ctx.env args with
      | some .nat =>
          .ok (.u64Bin .natMul leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .mul leftIR rightIR), rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .mul leftIR rightIR), rightResult.snd)
      | _ => .ok (.u64Bin .mul leftIR rightIR, rightResult.snd)
    else if primitive == ``HDiv.hDiv then
      .ok (.u64Bin .divU leftIR rightIR, rightResult.snd)
    else if primitive == ``HMod.hMod then
      .ok (.u64Bin .modU leftIR rightIR, rightResult.snd)
    else if primitive == ``HAnd.hAnd then
      match primitiveResultType? ctx.env args with
      | some .u8 | some .u32 | some .u64 =>
          .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise and expression: {primitive}"
    else if primitive == ``HOr.hOr then
      match primitiveResultType? ctx.env args with
      | some .u8 | some .u32 | some .u64 =>
          .ok (.u64Bin .bitOr leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise or expression: {primitive}"
    else if primitive == ``HXor.hXor then
      match primitiveResultType? ctx.env args with
      | some .u8 | some .u32 | some .u64 =>
          .ok (.u64Bin .bitXor leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported bitwise xor expression: {primitive}"
    else if primitive == ``HShiftLeft.hShiftLeft then
      match primitiveReceiverType? ctx.env args with
      | some .u64 =>
          .ok (.u64Bin .shiftLeft leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (u8WrapExpr (.u64Bin .shiftLeft leftIR (u8ShiftAmountExpr rightIR)),
            rightResult.snd)
      | some .u32 =>
          .ok (u32WrapExpr (.u64Bin .shiftLeft leftIR (u32ShiftAmountExpr rightIR)),
            rightResult.snd)
      | _ => .error s!"unsupported shift-left expression: {primitive}"
    else if primitive == ``HShiftRight.hShiftRight then
      match primitiveReceiverType? ctx.env args with
      | some .u64 =>
          .ok (.u64Bin .shiftRight leftIR rightIR, rightResult.snd)
      | some .u8 =>
          .ok (.u64Bin .shiftRight leftIR (u8ShiftAmountExpr rightIR), rightResult.snd)
      | some .u32 =>
          .ok (.u64Bin .shiftRight leftIR (u32ShiftAmountExpr rightIR), rightResult.snd)
      | _ => .error s!"unsupported shift-right expression: {primitive}"
    else if primitive == ``UInt64.land then
      .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.lor then
      .ok (.u64Bin .bitOr leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.xor then
      .ok (.u64Bin .bitXor leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.shiftLeft then
      .ok (.u64Bin .shiftLeft leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt64.shiftRight then
      .ok (.u64Bin .shiftRight leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt32.land then
      .ok (.u64Bin .bitAnd leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt32.lor then
      .ok (.u64Bin .bitOr leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt32.xor then
      .ok (.u64Bin .bitXor leftIR rightIR, rightResult.snd)
    else if primitive == ``UInt32.shiftLeft then
      .ok (u32WrapExpr (.u64Bin .shiftLeft leftIR (u32ShiftAmountExpr rightIR)),
        rightResult.snd)
    else if primitive == ``UInt32.shiftRight then
      .ok (.u64Bin .shiftRight leftIR (u32ShiftAmountExpr rightIR), rightResult.snd)
    else if primitive == ``UInt8.shiftLeft then
      .ok (u8WrapExpr (.u64Bin .shiftLeft leftIR (u8ShiftAmountExpr rightIR)),
        rightResult.snd)
    else if primitive == ``UInt8.shiftRight then
      .ok (.u64Bin .shiftRight leftIR (u8ShiftAmountExpr rightIR), rightResult.snd)
    else if primitive == ``BEq.beq then
      .ok (boolExpr (.eqU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``bne then
      .ok (boolExpr (.not (.eqU64 leftIR rightIR)), rightResult.snd)
    else if primitive == ``LT.lt then
      .ok (boolExpr (.ltU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``LE.le then
      .ok (boolExpr (.leU64 leftIR rightIR), rightResult.snd)
    else if primitive == ``GT.gt then
      .ok (boolExpr (.ltU64 rightIR leftIR), rightResult.snd)
    else if primitive == ``GE.ge then
      .ok (boolExpr (.leU64 rightIR leftIR), rightResult.snd)
    else if primitive == ``Min.min then
      match primitiveReceiverType? ctx.env args with
      | some .nat | some .u8 | some .u32 | some .u64 =>
          .ok (.ite (.leU64 leftIR rightIR) leftIR rightIR, rightResult.snd)
      | _ => .error s!"unsupported min expression: {primitive}"
    else if primitive == ``Max.max then
      match primitiveReceiverType? ctx.env args with
      | some .nat | some .u8 | some .u32 | some .u64 =>
          .ok (.ite (.leU64 leftIR rightIR) rightIR leftIR, rightResult.snd)
      | _ => .error s!"unsupported max expression: {primitive}"
    else
      .error s!"unsupported primitive expression: {primitive}"

  partial def extractCondFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String (IRCond × Nat) := do
    match expr.consumeMData with
    | .bvar index =>
        match ← lookupBinding locals index with
        | .slot slot => .ok (boolCond (.local slot), nextLocal)
        | .value value => .ok (boolCond (← scalarValue value), nextLocal)
        | .thunk savedLocals value =>
            let valueResult ← extractValueFrom ctx savedLocals nextLocal value
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | .structuralRec _ _ => .error "structural recursion handle used as a condition"
        | .structuralBelow _ => .error "structural recursion below value used as a condition"
        | .wfRecursor _ => .error "well-founded recursion handle used as a condition"
        | .natRecursor _ => .error "Nat recursion handle used as a condition"
        | .recursor => .error "recursive handle used as a condition"
    | .letE _ type value body _ =>
        if !containsBVar 0 body then
          extractCondFrom ctx (.recursor :: locals) nextLocal body
        else if isStringType type then
          extractCondFrom ctx (.thunk locals value :: locals) nextLocal body
        else
          match typeAtom? ctx.env type with
          | some ty =>
              if supportedLocalType ty then
                extractCondFrom ctx (.thunk locals value :: locals) nextLocal body
              else
                .error s!"unsupported let-bound type: {type}"
          | none => .error s!"unsupported let-bound type: {type}"
    | .const ``Bool.true _ => .ok (.true, nextLocal)
    | .const ``Bool.false _ => .ok (.false, nextLocal)
    | .const ``True _ => .ok (.true, nextLocal)
    | .const ``False _ => .ok (.false, nextLocal)
    | _ =>
        match appFnArgs expr with
        | (.bvar index, args) =>
            match ← lookupBinding locals index with
            | .wfRecursor functionName =>
                let valueResult ←
                  extractWfRecursorCallValueFrom ctx locals nextLocal functionName args
                .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
            | .natRecursor functionName =>
                let valueResult ←
                  extractNatRecursorCallValueFrom ctx locals nextLocal functionName args
                .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
            | _ => .error s!"unsupported condition: {expr}"
        | (.proj ``PProd index body, extraArgs) =>
            match ← natRecursorProjection? locals (.proj ``PProd index body) with
            | some functionName =>
                let valueResult ←
                  extractNatRecursorCallValueFrom ctx locals nextLocal functionName extraArgs
                .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
            | none =>
                match ← structuralRecProjection? locals (.proj ``PProd index body) with
                | some (functionName, arg, capturedArgs) =>
                    let valueResult ←
                      extractStructuralRecCallValueFrom ctx locals nextLocal
                        functionName arg capturedArgs extraArgs
                    .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
                | none => .error "unsupported structural recursion projection"
        | (.const ``String.isEmpty _, args) =>
            match args with
            | [value] =>
                let bytes ←
                  asciiStringExprBytesFrom ctx locals value
                    "unsupported String.isEmpty argument: expected compile-time string expression"
                    "unsupported String.isEmpty string: expected ASCII"
                .ok (if bytes.isEmpty then .true else .false, nextLocal)
            | _ => .error "unsupported String.isEmpty application"
        | (.const ``Eq _, [ty, left, right]) =>
            if isStringType ty then
              let leftBytes ←
                asciiStringExprBytesFrom ctx locals left
                  "unsupported String equality argument: expected compile-time string expression"
                  "unsupported String equality string: expected ASCII"
              let rightBytes ←
                asciiStringExprBytesFrom ctx locals right
                  "unsupported String equality argument: expected compile-time string expression"
                  "unsupported String equality string: expected ASCII"
              .ok (if leftBytes == rightBytes then .true else .false, nextLocal)
            else
              match typeAtom? ctx.env ty with
              | some eqTy =>
                  if supportedEqType eqTy then
                    let eqResult ← extractStructuralEqExprFrom ctx locals nextLocal eqTy left right
                    .ok (boolCond eqResult.fst, eqResult.snd)
                  else
                    .error "unsupported equality proposition in condition"
              | none => .error "unsupported equality proposition in condition"
        | (.const ``Decidable.decide _, [prop, _inst]) =>
            extractCondFrom ctx locals nextLocal prop
        | (.const ``Id.run _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``Pure.pure _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``Bind.bind _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``dite _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``And _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.and leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Or _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.or leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Not _, [arg]) =>
            let result ← extractCondFrom ctx locals nextLocal arg
            .ok (.not result.fst, result.snd)
        | (.const ``Bool.casesOn _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``BEq.beq _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                if primitiveStringReceiver? args then
                  let leftBytes ←
                    asciiStringExprBytesFrom ctx locals left
                      "unsupported String equality argument: expected compile-time string expression"
                      "unsupported String equality string: expected ASCII"
                  let rightBytes ←
                    asciiStringExprBytesFrom ctx locals right
                      "unsupported String equality argument: expected compile-time string expression"
                      "unsupported String equality string: expected ASCII"
                  .ok (if leftBytes == rightBytes then .true else .false, nextLocal)
                else
                  match primitiveReceiverType? ctx.env args with
                  | some ty =>
                      if supportedEqType ty then
                        let eqResult ← extractStructuralEqExprFrom ctx locals nextLocal ty left right
                        .ok (boolCond eqResult.fst, eqResult.snd)
                      else
                        .error s!"unsupported equality type: {reprStr ty}"
                  | none => .error "unsupported BEq application"
            | none => .error "unsupported BEq application"
        | (.const ``bne _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                if primitiveStringReceiver? args then
                  let leftBytes ←
                    asciiStringExprBytesFrom ctx locals left
                      "unsupported String inequality argument: expected compile-time string expression"
                      "unsupported String inequality string: expected ASCII"
                  let rightBytes ←
                    asciiStringExprBytesFrom ctx locals right
                      "unsupported String inequality argument: expected compile-time string expression"
                      "unsupported String inequality string: expected ASCII"
                  .ok (if leftBytes == rightBytes then .false else .true, nextLocal)
                else
                  match primitiveReceiverType? ctx.env args with
                  | some ty =>
                      if supportedEqType ty then
                        let eqResult ← extractStructuralEqExprFrom ctx locals nextLocal ty left right
                        .ok (.not (boolCond eqResult.fst), eqResult.snd)
                      else
                        .error s!"unsupported equality type: {reprStr ty}"
                  | none => .error "unsupported bne application"
            | none => .error "unsupported bne application"
        | (.const ``LT.lt _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.ltU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported LT.lt application"
        | (.const ``LE.le _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.leU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported LE.le application"
        | (.const ``GT.gt _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.ltU64 rightResult.fst leftResult.fst, rightResult.snd)
            | none => .error "unsupported GT.gt application"
        | (.const ``GE.ge _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.leU64 rightResult.fst leftResult.fst, rightResult.snd)
            | none => .error "unsupported GE.ge application"
        | (.const ``Bool.not _, [arg]) =>
            let result ← extractCondFrom ctx locals nextLocal arg
            .ok (.not result.fst, result.snd)
        | (.const ``Option.get! _, _) =>
            let valueResult ← extractValueFrom ctx locals nextLocal expr
            .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
        | (.const ``Array.get!Internal _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``GetElem?.getElem! _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``GetElem.getElem _, _) =>
            let exprResult ← extractExprFrom ctx locals nextLocal expr
            .ok (boolCond exprResult.fst, exprResult.snd)
        | (.const ``Option.isSome _, args) =>
            match args.reverse with
            | optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let tag := wrapExprLets parts.fst parts.snd.fst
                .ok (.not (.eqU64 tag (.u64 0)), optionResult.snd)
            | _ => .error "unsupported Option.isSome condition"
        | (.const ``Option.isNone _, args) =>
            match args.reverse with
            | optionValue :: _ =>
                let optionResult ← extractValueFrom ctx locals nextLocal optionValue
                let parts ← optionPartsWithLets optionResult.fst
                let tag := wrapExprLets parts.fst parts.snd.fst
                .ok (.eqU64 tag (.u64 0), optionResult.snd)
            | _ => .error "unsupported Option.isNone condition"
        | (.const ``Option.any _, _) =>
            extractOptionPredicateCondFrom ctx locals nextLocal expr false
        | (.const ``Option.all _, _) =>
            extractOptionPredicateCondFrom ctx locals nextLocal expr true
        | (.const ``Except.isOk _, args) =>
            match args.reverse, exceptPayloadType? ctx.env args with
            | exceptValue :: _, some _payloadTy =>
                let tagResult ← extractExceptTagExprFrom ctx locals nextLocal exceptValue
                .ok (.not (.eqU64 tagResult.fst (.u64 0)), tagResult.snd)
            | _, _ => .error "unsupported Except.isOk condition"
        | (.const ``Bool.or _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.or leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Bool.and _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok (.and leftResult.fst rightResult.fst, rightResult.snd)
        | (.const ``Bool.xor _, [left, right]) =>
            let leftResult ← extractCondFrom ctx locals nextLocal left
            let rightResult ← extractCondFrom ctx locals leftResult.snd right
            .ok
              (.or
                (.and leftResult.fst (.not rightResult.fst))
                (.and (.not leftResult.fst) rightResult.fst),
                rightResult.snd)
        | (.const ``Nat.blt _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.ltU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported Nat.blt application"
        | (.const ``Nat.ble _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.leU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported Nat.ble application"
        | (.const ``Nat.beq _, args) =>
            match primitiveArgPair? args with
            | some (left, right) =>
                let leftResult ← extractExprFrom ctx locals nextLocal left
                let rightResult ← extractExprFrom ctx locals leftResult.snd right
                .ok (.eqU64 leftResult.fst rightResult.fst, rightResult.snd)
            | none => .error "unsupported Nat.beq application"
        | (.const ``Array.isEmpty _, args) =>
            match args.reverse with
            | array :: _ =>
                let arrayResult ← extractExprFrom ctx locals nextLocal array
                .ok (.eqU64 (.arraySize arrayResult.fst) (.u64 0), arrayResult.snd)
            | _ => .error "unsupported Array.isEmpty condition"
        | (.const ``ByteArray.isEmpty _, args) =>
            match args with
            | [array] =>
                let arrayResult ← extractValueFrom ctx locals nextLocal array
                let parts ← byteArrayPartsWithLets arrayResult.fst
                let len := wrapExprLets parts.fst parts.snd.snd
                .ok (.eqU64 len (.u64 0), arrayResult.snd)
            | _ => .error "unsupported ByteArray.isEmpty condition"
        | (.const name _, args) =>
            match boolMatcherArgs? ctx.env (.const name []) args with
            | some _ =>
                let exprResult ← extractExprFrom ctx locals nextLocal expr
                .ok (boolCond exprResult.fst, exprResult.snd)
            | none =>
                match exceptMatcherArgs? ctx.env (.const name []) args with
                | some _ =>
                    let exprResult ← extractExprFrom ctx locals nextLocal expr
                    .ok (boolCond exprResult.fst, exprResult.snd)
                | none =>
                    match natMatcherArgs? ctx.env (.const name []) args with
                    | some _ =>
                        let exprResult ← extractExprFrom ctx locals nextLocal expr
                        .ok (boolCond exprResult.fst, exprResult.snd)
                    | none =>
                        match productMatcherArgs? ctx.env (.const name []) args with
                        | some _ =>
                            let exprResult ← extractExprFrom ctx locals nextLocal expr
                            .ok (boolCond exprResult.fst, exprResult.snd)
                        | none =>
                            match structureMatcherArgs? ctx.env (.const name []) args with
                            | some _ =>
                                let exprResult ← extractExprFrom ctx locals nextLocal expr
                                .ok (boolCond exprResult.fst, exprResult.snd)
                            | none =>
                                match variantMatcherArgs? ctx.env (.const name []) args with
                                | some _ =>
                                    let exprResult ← extractExprFrom ctx locals nextLocal expr
                                    .ok (boolCond exprResult.fst, exprResult.snd)
                                | none =>
                                    match ← extractInlineCallValueFrom ctx locals nextLocal name args with
                                    | some valueResult =>
                                        .ok (boolCond (← scalarValue valueResult.fst), valueResult.snd)
                                    | none =>
                                        match functionIndex? ctx name with
                                        | some index =>
                                            strictRecursiveCallCheck ctx name args
                                            let sig ←
                                              match ctx.env.find? name with
                                              | some info =>
                                                  match supportedFunction? ctx.env info with
                                                  | some sig => .ok sig
                                                  | none =>
                                                      .error
                                                        s!"unsupported function type or declaration: {name}"
                                              | none =>
                                                  .error s!"declaration disappeared during extraction: {name}"
                                            strictCallMaterializationCheck ctx name sig.params args
                                            let argsResult ← extractCallArgsFrom ctx locals nextLocal sig.params args
                                            .ok
                                              (boolCond
                                                (wrapExprLets argsResult.lets
                                                  (.call index argsResult.args)),
                                                argsResult.nextLocal)
                                        | none => .error s!"unsupported condition: {expr}"
        | _ => .error s!"unsupported condition: {expr}"

  partial def extractExprListFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat) :
      List Expr → Except String (List IRExpr × Nat)
    | [] => .ok ([], nextLocal)
    | expr :: rest => do
        let headResult ← extractExprFrom ctx locals nextLocal expr
        let restResult ← extractExprListFrom ctx locals headResult.snd rest
        .ok (headResult.fst :: restResult.fst, restResult.snd)

  partial def extractCallArgsFrom
      (ctx : Context)
      (locals : List Binding)
      (nextLocal : Nat) :
      List Ty → List Expr → Except String StrictArgs
    | [], [] => .ok { lets := [], args := [], nextLocal := nextLocal }
    | ty :: restTys, expr :: restExprs => do
        let valueResult ← extractValueFrom ctx locals nextLocal expr
        let head ← materializeStrictInternalSlots ty valueResult.fst valueResult.snd
        let bound := bindStrictSlots head.slots head.nextLocal
        let rest ← extractCallArgsFrom ctx locals bound.nextLocal restTys restExprs
        .ok {
          lets := head.lets ++ bound.lets ++ rest.lets,
          args := bound.slots ++ rest.args,
          nextLocal := rest.nextLocal
        }
    | _, _ => .error "function call arity mismatch"
end

def extractExpr (ctx : Context) (locals : List Binding) (nextLocal : Nat) (expr : Expr) :
    Except String (IRExpr × Nat) :=
  extractExprFrom ctx locals nextLocal expr

def extractCond (ctx : Context) (locals : List Binding) (nextLocal : Nat) (expr : Expr) :
    Except String (IRCond × Nat) :=
  extractCondFrom ctx locals nextLocal expr

def localBindingsForParams (useAbi : Bool) (params : List Ty) : List Binding :=
  (functionParamBindings useAbi params).reverse

def baseBindingsForParams (useAbi : Bool) (name : Name) (params : List Ty) : List Binding :=
  .natRecursor name :: ((functionParamBindings useAbi params).drop 1).reverse

def stepBindingsForParams (useAbi : Bool) (name : Name) (params : List Ty) : List Binding :=
  let carried := ((functionParamBindings useAbi params).drop 1).reverse
  (.natRecursor name :: carried) ++ [.value (.scalar (.u64Bin .sub (.local 0) (.u64 1)))]

def extractStructuralRecFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (typeName : Name)
    (typeParams : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let useAbi := exportName.isSome
  let wasmParamCount := functionParamCount useAbi params
  let paramLocals := localBindingsForParams useAbi params
  let body ←
    match collectLambdas value params.length with
    | some body => .ok body
    | none => .error s!"definition body does not match function arity: {name}"
  let (scrutinee, step, postArgs) ←
    match rawStructuralRecApplication? ctx.env body with
    | some app =>
        if app.typeName == typeName && app.typeParams == typeParams then
          .ok (app.scrutinee, app.step, app.postArgs)
        else
          .error s!"structural recursion type mismatch: {name}"
    | none => .error s!"unsupported structural recursion shape: {name}"
  let postPlans ← structuralPostArgs params postArgs
  let capturedArgs ← structuralCapturedArgs params postPlans
  if !isBVar (params.length - 1) scrutinee then
    .error s!"unsupported structural recursion scrutinee: {name}"
  else
    let stepLambdaBindings := List.replicate (2 + postArgs.length) Binding.recursor
    let stepInfo ← structuralRecStepMatcher? ctx.env typeName typeParams postArgs.length step
    if stepInfo.prePostArgCount > postPlans.length then
      .error s!"unsupported structural recursion carried arguments: {name}"
    else
      let layout := stepInfo.layout
      let arms := stepInfo.arms
      if arms.length != layout.ctors.length then
        .error s!"inductive matcher arity mismatch: {layout.name}"
      else
        let scrutineeResult ← extractValueFrom ctx paramLocals wasmParamCount scrutinee
        let parts ← heapVariantPtrWithLets layout.name scrutineeResult.fst
        let ptrSlot := scrutineeResult.snd
        let ptrExpr := wrapExprLets parts.fst parts.snd
        let ptrLocal : IRExpr := .local ptrSlot
        let tag := .heapLoadSlot ptrLocal 0
        let rec extractArms :
            List VariantCtorLayout → List Expr → Nat → Nat →
              Except String (List ExtractedValue × Nat)
          | [], [], _, next => .ok ([], next)
          | ctor :: restCtors, arm :: restArms, payloadSlot, next => do
              let runtimeFields ← heapRuntimeFieldsFromKinds ptrLocal ctor.fields payloadSlot
              let sourceBindings ←
                sourceFieldBindingsFromKinds layout.name ctor.fields runtimeFields.fst
              let belowBinding ←
                structuralBelowBinding name capturedArgs layout.name typeParams ctor.name ctor.fields
                  runtimeFields.fst
              let postBinders :=
                postPlans.map fun plan =>
                  match plan with
                  | .dynamic ty binding => StructuralArmBinder.runtime (some ty) binding
                  | .staticLambda expr => StructuralArmBinder.staticLambda expr
              let fieldBinders :=
                (ctor.fields.zip sourceBindings).map fun item =>
                  StructuralArmBinder.runtime item.fst item.snd
              let armBinders :=
                postBinders.take stepInfo.prePostArgCount ++
                  fieldBinders ++
                  postBinders.drop stepInfo.prePostArgCount ++
                  [StructuralArmBinder.below belowBinding]
              let parsedArm ←
                if ctor.fields.isEmpty then
                  let unitBinder :=
                    StructuralArmBinder.runtime (some .unit) (.value (.scalar (.u64 0)))
                  match consumeStructuralArmBinders ctx layout.name (unitBinder :: armBinders) arm with
                  | .ok parsedArm => .ok parsedArm
                  | .error _ => consumeStructuralArmBinders ctx layout.name armBinders arm
                else
                  consumeStructuralArmBinders ctx layout.name armBinders arm
              let armResult ←
                extractValueFrom ctx (parsedArm.snd ++ stepLambdaBindings ++ paramLocals)
                  next parsedArm.fst
              let restResult ← extractArms restCtors restArms runtimeFields.snd armResult.snd
              .ok (armResult.fst :: restResult.fst, restResult.snd)
          | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
        let armResults ← extractArms layout.ctors arms 1 (ptrSlot + 1)
        let rec combine : List (Nat × ExtractedValue) → Except String ExtractedValue
          | [] => .error s!"inductive matcher has no arms: {layout.name}"
          | [(_index, value)] => .ok value
          | (index, value) :: rest => do
              let elseValue ← combine rest
              valueIte (.eqU64 tag (.u64 index)) value elseValue
        let resultValue := .letE ptrSlot ptrExpr (← combine (enumerate armResults.fst))
        let resultCount := resultSlotCount useAbi resultTy
        let resultTargets := (List.range resultCount).map (fun offset => armResults.snd + offset)
        let resultBody ← materializeResultValue ctx useAbi resultTy resultTargets resultValue
        .ok {
          sourceName := name,
          exportName := exportName,
          params := wasmParamCount,
          locals := armResults.snd + resultCount,
          body := resultBody,
          results := resultTargets.map LeanExe.IR.Expr.local
        }

structure ClosedStructuralFoldShape where
  typeName : Name
  typeParams : List Ty
  scrutinee : Expr
  step : Expr
  init : Expr

def closedStructuralFoldShape? (env : Environment) (body : Expr) :
    Option ClosedStructuralFoldShape :=
  match rawStructuralRecApplication? env body with
  | some app =>
      match app.postArgs with
      | [init] =>
          if isDirectLambda init then
            none
          else
            some {
              typeName := app.typeName,
              typeParams := app.typeParams,
              scrutinee := app.scrutinee,
              step := app.step,
              init := init
            }
      | _ => none
  | none => none

def closedStructuralFoldCandidate? (env : Environment) (value : Expr) (paramCount : Nat) :
    Bool :=
  match collectLambdas value paramCount with
  | some body => (closedStructuralFoldShape? env body).isSome
  | none => false

def wellFoundedFixStep? (expr : Expr) : Option Expr :=
  match appFnArgs expr with
  | (.const ``WellFounded.fix _, args) =>
      match args.reverse with
      | step :: _wf :: _rel :: _motive :: _type :: _ => some step
      | _ => none
  | _ => none

def wellFoundedNatFixStep? (expr : Expr) : Option Expr :=
  match appFnArgs expr with
  | (.const ``WellFounded.Nat.fix _, args) =>
      match args with
      | [_type, _motive, _measure, step] => some step
      | _ => none
  | _ => none

def wellFoundedMatcherInfo?
    (env : Environment)
    (fn : Expr)
    (args : List Expr)
    (typeName : Name)
    (typeParams : List Ty) :
    Option VariantMatch :=
  match fn.consumeMData with
  | .const name _ =>
      match generatedMatcherVariantScrutineeArg? env name args (some typeName) with
      | some (scrutineeIndex, .recVariant actual params) =>
          if actual == typeName && params == typeParams then
            match recursiveVariantLayout? env typeName typeParams, args[scrutineeIndex]?, env.find? name with
            | some layout, some scrutinee, some info =>
              let ctorCount := layout.ctors.length
              let afterScrutinee := args.drop (scrutineeIndex + 1)
              let armArgs := afterScrutinee.take ctorCount
              let armDomains := (peelForall info.type).fst.drop (scrutineeIndex + 1) |>.take ctorCount
              if afterScrutinee.length == ctorCount + 1 then
                let typedArms? :=
                  (armDomains.zip armArgs).mapM fun item =>
                    variantArmCtorName? env item.fst |>.map fun ctorName => (ctorName, item.snd)
                match typedArms? with
                | some typedArms =>
                    match reorderVariantArms? (layout.ctors.map (fun ctor => ctor.name)) typedArms with
                    | some orderedArms =>
                        some {
                          layout := layout,
                          scrutinee := scrutinee,
                          arms := orderedArms,
                          prePostArgCount := 0
                        }
                    | none => none
                | none => none
              else
                none
            | _, _, _ => none
          else
            none
      | _ => none
  | _ => none

def extractWellFoundedRecFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (typeName : Name)
    (typeParams : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  if params.length != 1 then
    .error s!"unsupported well-founded recursion arity: {name}"
  else
  let step ←
    match wellFoundedFixStep? value with
    | some step => .ok step
    | none => .error s!"unsupported well-founded recursion shape: {name}"
  let stepBody ←
    match collectLambdas step 2 with
    | some body => .ok body
    | none => .error s!"unsupported well-founded recursion step: {name}"
  let (matcherFn, matcherArgs) := appFnArgs stepBody
  let info ←
    match wellFoundedMatcherInfo? ctx.env matcherFn matcherArgs typeName typeParams with
    | some info => .ok info
    | none => .error s!"unsupported well-founded recursion matcher: {name}"
  if !isBVar 1 info.scrutinee then
    .error s!"unsupported well-founded recursion scrutinee: {name}"
  else
  let layout := info.layout
  if layout.name != typeName then
    .error s!"well-founded recursion matcher type mismatch: {name}"
  else if info.arms.length != layout.ctors.length then
    .error s!"inductive matcher arity mismatch: {layout.name}"
  else
  let useAbi := exportName.isSome
  let wasmParamCount := functionParamCount useAbi params
  let stepLocals := .wfRecursor name :: localBindingsForParams useAbi params
  let scrutineeResult ←
    match extractValueFrom ctx stepLocals wasmParamCount info.scrutinee with
    | .ok result => .ok result
    | .error error => .error s!"while extracting well-founded scrutinee for {name}: {error}"
  let parts ← heapVariantPtrWithLets layout.name scrutineeResult.fst
  let ptrSlot := scrutineeResult.snd
  let ptrExpr := wrapExprLets parts.fst parts.snd
  let ptrLocal : IRExpr := .local ptrSlot
  let tag := .heapLoadSlot ptrLocal 0
  let postBinders := [StructuralArmBinder.below (.wfRecursor name)]
  let rec extractArms :
      List VariantCtorLayout → List Expr → Nat → Nat →
        Except String (List ExtractedValue × Nat)
    | [], [], _, next => .ok ([], next)
    | ctor :: restCtors, arm :: restArms, payloadSlot, next => do
        let runtimeFields ← heapRuntimeFieldsFromKinds ptrLocal ctor.fields payloadSlot
        let sourceBindings ←
          sourceFieldBindingsFromKinds layout.name ctor.fields runtimeFields.fst
        let fieldBinders :=
          (ctor.fields.zip sourceBindings).map fun item =>
            StructuralArmBinder.runtime item.fst item.snd
        let armBinders :=
          postBinders.take info.prePostArgCount ++
            fieldBinders ++
            postBinders.drop info.prePostArgCount
        let parsedArm ←
          if ctor.fields.isEmpty then
            let unitBinder :=
              StructuralArmBinder.runtime (some .unit) (.value (.scalar (.u64 0)))
            match consumeStructuralArmBinders ctx layout.name (unitBinder :: armBinders) arm with
            | .ok parsedArm => .ok parsedArm
            | .error _ => consumeStructuralArmBinders ctx layout.name armBinders arm
          else
            consumeStructuralArmBinders ctx layout.name armBinders arm
        let armResult ←
          match extractValueFrom ctx (parsedArm.snd ++ stepLocals) next parsedArm.fst with
          | .ok result => .ok result
          | .error error => .error s!"while extracting well-founded arm {ctor.name} for {name}: {error}"
        let restResult ← extractArms restCtors restArms runtimeFields.snd armResult.snd
        .ok (armResult.fst :: restResult.fst, restResult.snd)
    | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
  let armResults ← extractArms layout.ctors info.arms 1 (ptrSlot + 1)
  let rec combine : List (Nat × ExtractedValue) → Except String ExtractedValue
    | [] => .error s!"inductive matcher has no arms: {layout.name}"
    | [(_index, value)] => .ok value
    | (index, value) :: rest => do
        let elseValue ← combine rest
        valueIte (.eqU64 tag (.u64 index)) value elseValue
  let resultValue := .letE ptrSlot ptrExpr (← combine (enumerate armResults.fst))
  let resultCount := resultSlotCount useAbi resultTy
  let resultTargets := (List.range resultCount).map (fun offset => armResults.snd + offset)
  let resultBody ← materializeResultValue ctx useAbi resultTy resultTargets resultValue
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := armResults.snd + resultCount,
    body := resultBody,
    results := resultTargets.map LeanExe.IR.Expr.local
  }

def extractWellFoundedNatMemberBranch
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (typeName : Name)
    (typeParams : List Ty)
    (payload : ExtractedValue)
    (nextLocal : Nat)
    (body : Expr) :
    Except String (ExtractedValue × Nat) := do
  let (matcherFn, matcherArgs) := appFnArgs body
  let info ←
    match wellFoundedMatcherInfo? ctx.env matcherFn matcherArgs typeName typeParams with
    | some info => .ok info
    | none => .error s!"unsupported well-founded Nat member matcher: {name}"
  if !isBVar 1 info.scrutinee then
    .error s!"unsupported well-founded Nat member scrutinee: {name}"
  else
  let layout := info.layout
  if layout.name != typeName then
    .error s!"well-founded Nat member matcher type mismatch: {name}"
  else if info.arms.length != layout.ctors.length then
    .error s!"inductive matcher arity mismatch: {layout.name}"
  else
  let parts ← heapVariantPtrWithLets layout.name payload
  let ptrSlot := nextLocal
  let ptrExpr := wrapExprLets parts.fst parts.snd
  let ptrLocal : IRExpr := .local ptrSlot
  let tag := .heapLoadSlot ptrLocal 0
  let stepLocals := .wfRecursor name :: .value payload :: localBindingsForParams false params
  let postBinders := [StructuralArmBinder.below (.wfRecursor name)]
  let rec extractArms :
      List VariantCtorLayout → List Expr → Nat → Nat →
        Except String (List ExtractedValue × Nat)
    | [], [], _, next => .ok ([], next)
    | ctor :: restCtors, arm :: restArms, payloadSlot, next => do
        let runtimeFields ← heapRuntimeFieldsFromKinds ptrLocal ctor.fields payloadSlot
        let sourceBindings ←
          sourceFieldBindingsFromKinds layout.name ctor.fields runtimeFields.fst
        let fieldBinders :=
          (ctor.fields.zip sourceBindings).map fun item =>
            StructuralArmBinder.runtime item.fst item.snd
        let armBinders :=
          postBinders.take info.prePostArgCount ++
            fieldBinders ++
            postBinders.drop info.prePostArgCount
        let parsedArm ←
          if ctor.fields.isEmpty then
            let unitBinder :=
              StructuralArmBinder.runtime (some .unit) (.value (.scalar (.u64 0)))
            match consumeStructuralArmBinders ctx layout.name (unitBinder :: armBinders) arm with
            | .ok parsedArm => .ok parsedArm
            | .error _ => consumeStructuralArmBinders ctx layout.name armBinders arm
          else
            consumeStructuralArmBinders ctx layout.name armBinders arm
        let armResult ←
          match extractValueFrom ctx (parsedArm.snd ++ stepLocals) next parsedArm.fst with
          | .ok result => .ok result
          | .error error => .error s!"while extracting well-founded Nat member arm {ctor.name} for {name}: {error}"
        let restResult ← extractArms restCtors restArms runtimeFields.snd armResult.snd
        .ok (armResult.fst :: restResult.fst, restResult.snd)
    | _, _, _, _ => .error s!"inductive matcher arity mismatch: {layout.name}"
  let armResults ← extractArms layout.ctors info.arms 1 (ptrSlot + 1)
  let rec combine : List (Nat × ExtractedValue) → Except String ExtractedValue
    | [] => .error s!"inductive matcher has no arms: {layout.name}"
    | [(_index, value)] => .ok value
    | (index, value) :: rest => do
        let elseValue ← combine rest
        valueIte (.eqU64 tag (.u64 index)) value elseValue
  .ok (.letE ptrSlot ptrExpr (← combine (enumerate armResults.fst)), armResults.snd)

partial def extractWellFoundedNatSumTree
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (expectedTy : Ty)
    (payload : ExtractedValue)
    (nextLocal : Nat)
    (body : Expr) :
    Except String (ExtractedValue × Nat) := do
  match expectedTy with
  | .recVariant typeName typeParams =>
      extractWellFoundedNatMemberBranch ctx name params typeName typeParams payload nextLocal body
  | .sum expectedLeft expectedRight =>
      let (matcherFn, stepArgs) := appFnArgs body
      let (matcherArgs, recursorArg) ←
        match stepArgs.reverse with
        | recursorArg :: reversedMatcherArgs => .ok (reversedMatcherArgs.reverse, recursorArg)
        | _ => .error s!"unsupported well-founded Nat recursion sum branch: {name}"
      if !isBVar 0 recursorArg then
        .error s!"unsupported well-founded Nat recursion recursor argument: {name}"
      else
      let (leftTy, rightTy, scrutinee, leftArm, rightArm) ←
        match psumMatcherArgs? ctx.env matcherFn matcherArgs with
        | some result => .ok result
        | none => .error s!"unsupported well-founded Nat recursion PSum matcher: {name}"
      if (.sum expectedLeft expectedRight : Ty) != (.sum leftTy rightTy : Ty) then
        .error s!"well-founded Nat recursion sum type mismatch: {name}"
      else if !isBVar 1 scrutinee then
        .error s!"unsupported well-founded Nat recursion scrutinee: {name}"
      else
      let parts ← sumPartsWithLets payload
      let lets := parts.fst
      let tag := parts.snd.fst
      let leftPayload := parts.snd.snd.fst
      let rightPayload := parts.snd.snd.snd
      let leftBody ←
        match collectLambdas leftArm 2 with
        | some body => .ok body
        | none => .error s!"unsupported well-founded Nat recursion left sum arm: {name}"
      let leftResult ←
        match extractWellFoundedNatSumTree ctx name params leftTy leftPayload nextLocal leftBody with
        | .ok result => .ok result
        | .error error => .error s!"while extracting well-founded Nat left sum arm for {name}: {error}"
      let rightBody ←
        match collectLambdas rightArm 2 with
        | some body => .ok body
        | none => .error s!"unsupported well-founded Nat recursion right sum arm: {name}"
      let rightResult ←
        match extractWellFoundedNatSumTree ctx name params rightTy rightPayload leftResult.snd rightBody with
        | .ok result => .ok result
        | .error error => .error s!"while extracting well-founded Nat right sum arm for {name}: {error}"
      let resultValue ← valueIte (.eqU64 tag (.u64 0)) leftResult.fst rightResult.fst
      .ok (wrapValueLets lets resultValue, rightResult.snd)
  | _ => .error s!"unsupported well-founded Nat recursion member type: {name}"

def extractWellFoundedNatSumFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let sumTy ←
    match params with
    | [sumTy] =>
        match sumTy with
        | .sum _ _ => .ok sumTy
        | _ => .error s!"unsupported well-founded Nat recursion parameter type: {name}"
    | _ => .error s!"unsupported well-founded Nat recursion arity: {name}"
  let useAbi := exportName.isSome
  let wasmParamCount := functionParamCount useAbi params
  let paramLocals := localBindingsForParams useAbi params
  let step ←
    match wellFoundedNatFixStep? value with
    | some step => .ok step
    | none => .error s!"unsupported well-founded Nat recursion shape: {name}"
  let stepBody ←
    match collectLambdas step 2 with
    | some body => .ok body
    | none => .error s!"unsupported well-founded Nat recursion step: {name}"
  let scrutineeResult ← extractValueFrom ctx paramLocals wasmParamCount (.bvar 0)
  let result ←
    extractWellFoundedNatSumTree ctx name params sumTy scrutineeResult.fst scrutineeResult.snd stepBody
  let resultCount := resultSlotCount useAbi resultTy
  let resultTargets := (List.range resultCount).map (fun offset => result.snd + offset)
  let resultBody ← materializeResultValue ctx useAbi resultTy resultTargets result.fst
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := result.snd + resultCount,
    body := resultBody,
    results := resultTargets.map LeanExe.IR.Expr.local
  }

def extractWellFoundedNatRecFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (typeName : Name)
    (typeParams : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  match params with
  | [.recVariant actual actualParams] =>
      if actual != typeName || actualParams != typeParams then
        .error s!"well-founded Nat recursion parameter type mismatch: {name}"
      else
      let useAbi := exportName.isSome
      let wasmParamCount := functionParamCount useAbi params
      let paramLocals := localBindingsForParams useAbi params
      let step ←
        match wellFoundedNatFixStep? value with
        | some step => .ok step
        | none => .error s!"unsupported well-founded Nat recursion shape: {name}"
      let stepBody ←
        match collectLambdas step 2 with
        | some body => .ok body
        | none => .error s!"unsupported well-founded Nat recursion step: {name}"
      let scrutineeResult ← extractValueFrom ctx paramLocals wasmParamCount (.bvar 0)
      let result ←
        extractWellFoundedNatMemberBranch ctx name params typeName typeParams
          scrutineeResult.fst scrutineeResult.snd stepBody
      let resultCount := resultSlotCount useAbi resultTy
      let resultTargets := (List.range resultCount).map (fun offset => result.snd + offset)
      let resultBody ← materializeResultValue ctx useAbi resultTy resultTargets result.fst
      .ok {
        sourceName := name,
        exportName := exportName,
        params := wasmParamCount,
        locals := result.snd + resultCount,
        body := resultBody,
        results := resultTargets.map LeanExe.IR.Expr.local
      }
  | _ => .error s!"unsupported well-founded Nat recursion arity: {name}"

def recCallArgsAt? (recursorIndex expected : Nat) (expr : Expr) : Option (List Expr) :=
  match appFnArgs expr with
  | (fn, args) =>
      if args.length == expected && containsBVar recursorIndex fn then
        some args
      else
        none

structure RecSpec where
  base : Expr
  continueCond? : Option Expr
  continueWhenTrue : Bool
  exitValue? : Option Expr
  recArgs : List Expr

structure NatRecShape where
  base : Expr
  step : Expr

structure TailStepResult where
  stmt : IRStmt
  nextLocal : Nat

def wrapRecStepLet
    (name : Name)
    (type value : Expr)
    (nondep : Bool)
    (parsed : Option (Expr × Bool) × Option Expr × List Expr) :
    Option (Expr × Bool) × Option Expr × List Expr :=
  let wrap (expr : Expr) := .letE name type value expr nondep
  let cond? := parsed.fst.map fun item => (wrap item.fst, item.snd)
  let exit? := parsed.snd.fst.map wrap
  let recArgs := parsed.snd.snd.map wrap
  (cond?, exit?, recArgs)

partial def parseStepBodyAt? (env : Environment) (paramCount recursorIndex : Nat) (body : Expr) :
    Except String (Option (Expr × Bool) × Option Expr × List Expr) := do
  match body.consumeMData with
  | .letE name type value letBody nondep => do
      .ok
        (wrapRecStepLet name type value nondep
          (← parseStepBodyAt? env paramCount (recursorIndex + 1) letBody))
  | body =>
      let expectedArgs := paramCount - 1
      match appFnArgs body with
      | (.const ``ite _, [ty, condExpr, _, thenExpr, elseExpr]) =>
          if typeAtom? env ty |>.isSome then
            match recCallArgsAt? recursorIndex expectedArgs thenExpr with
            | some args => .ok (some (condExpr, true), some elseExpr, args)
            | none =>
                match recCallArgsAt? recursorIndex expectedArgs elseExpr with
                | some args => .ok (some (condExpr, false), some thenExpr, args)
                | none => .error "recursive branch is not a tail call"
          else
            .error "recursive branch has unsupported if-result type"
      | _ =>
          match recCallArgsAt? recursorIndex expectedArgs body with
          | some args => .ok (none, none, args)
          | none => .error "recursive branch is not a supported tail call"

def parseStepBody? (env : Environment) (paramCount : Nat) (body : Expr) :
    Except String (Option (Expr × Bool) × Option Expr × List Expr) :=
  parseStepBodyAt? env paramCount 0 body

def parseRecMatcher? (env : Environment) (name : Name) (paramCount : Nat) (expr : Expr) :
    Except String (Option RecSpec) := do
  match appFnArgs expr with
  | (.const candidate _, args) =>
      if !isMatcherName candidate then
        return none
      let carriedCount := paramCount - 1
      if args.length != paramCount + 4 then
        .error s!"unsupported Nat recursion matcher arity: {name}"
      else
        match args.drop (carriedCount + 2) with
        | baseArm :: succArm :: _below :: [] =>
            let baseBody ←
              match collectLambdas baseArm (carriedCount + 1) with
              | some body => .ok body
              | none => .error s!"unsupported Nat recursion base arm: {name}"
            let stepBody ←
              match collectLambdas succArm (carriedCount + 2) with
              | some body => .ok body
              | none => .error s!"unsupported Nat recursion successor arm: {name}"
            let parsedStep ← parseStepBody? env paramCount stepBody
            let continueCond? := parsedStep.fst.map Prod.fst
            let continueWhenTrue := parsedStep.fst.map Prod.snd |>.getD true
            .ok (some {
              base := baseBody,
              continueCond? := continueCond?,
              continueWhenTrue := continueWhenTrue,
              exitValue? := parsedStep.snd.fst,
              recArgs := parsedStep.snd.snd
            })
        | _ => .error s!"unsupported Nat recursion matcher arguments: {name}"
  | _ => return none

def parseNatRecShapeMatcher? (_env : Environment) (name : Name) (paramCount : Nat) (expr : Expr) :
    Except String (Option NatRecShape) := do
  match appFnArgs expr with
  | (.const candidate _, args) =>
      if !isMatcherName candidate then
        return none
      let carriedCount := paramCount - 1
      if args.length != paramCount + 4 then
        .error s!"unsupported Nat recursion matcher arity: {name}"
      else
        match args.drop (carriedCount + 2) with
        | baseArm :: succArm :: _below :: [] =>
            let baseBody ←
              match collectLambdas baseArm (carriedCount + 1) with
              | some body => .ok body
              | none => .error s!"unsupported Nat recursion base arm: {name}"
            let stepBody ←
              match collectLambdas succArm (carriedCount + 2) with
              | some body => .ok body
              | none => .error s!"unsupported Nat recursion successor arm: {name}"
            .ok (some { base := baseBody, step := stepBody })
        | _ => .error s!"unsupported Nat recursion matcher arguments: {name}"
  | _ => return none

mutual
  partial def findRecSpec? (env : Environment) (name : Name) (paramCount : Nat) (expr : Expr) :
      Except String (Option RecSpec) := do
    match ← parseRecMatcher? env name paramCount expr with
    | some spec => .ok (some spec)
    | none => findRecSpecInChildren? env name paramCount expr

  partial def findRecSpecInChildren? (env : Environment) (name : Name) (paramCount : Nat) (expr : Expr) :
      Except String (Option RecSpec) := do
    match expr.consumeMData with
    | .app fn arg =>
        match ← findRecSpec? env name paramCount fn with
        | some spec => .ok (some spec)
        | none => findRecSpec? env name paramCount arg
    | .lam _ type body _ =>
        match ← findRecSpec? env name paramCount type with
        | some spec => .ok (some spec)
        | none => findRecSpec? env name paramCount body
    | .forallE _ type body _ =>
        match ← findRecSpec? env name paramCount type with
        | some spec => .ok (some spec)
        | none => findRecSpec? env name paramCount body
    | .letE _ type value body _ =>
        match ← findRecSpec? env name paramCount type with
        | some spec => .ok (some spec)
        | none =>
            match ← findRecSpec? env name paramCount value with
            | some spec => .ok (some spec)
            | none => findRecSpec? env name paramCount body
    | .mdata _ body => findRecSpec? env name paramCount body
    | .proj _ _ body => findRecSpec? env name paramCount body
    | _ => .ok none
end

mutual
  partial def findNatRecShape? (env : Environment) (name : Name) (paramCount : Nat)
      (expr : Expr) :
      Except String (Option NatRecShape) := do
    match ← parseNatRecShapeMatcher? env name paramCount expr with
    | some shape => .ok (some shape)
    | none => findNatRecShapeInChildren? env name paramCount expr

  partial def findNatRecShapeInChildren? (env : Environment) (name : Name)
      (paramCount : Nat) (expr : Expr) :
      Except String (Option NatRecShape) := do
    match expr.consumeMData with
    | .app fn arg =>
        match ← findNatRecShape? env name paramCount fn with
        | some shape => .ok (some shape)
        | none => findNatRecShape? env name paramCount arg
    | .lam _ type body _ =>
        match ← findNatRecShape? env name paramCount type with
        | some shape => .ok (some shape)
        | none => findNatRecShape? env name paramCount body
    | .forallE _ type body _ =>
        match ← findNatRecShape? env name paramCount type with
        | some shape => .ok (some shape)
        | none => findNatRecShape? env name paramCount body
    | .letE _ type value body _ =>
        match ← findNatRecShape? env name paramCount type with
        | some shape => .ok (some shape)
        | none =>
            match ← findNatRecShape? env name paramCount value with
            | some shape => .ok (some shape)
            | none => findNatRecShape? env name paramCount body
    | .mdata _ body => findNatRecShape? env name paramCount body
    | .proj _ _ body => findNatRecShape? env name paramCount body
    | _ => .ok none
end

def assignMany (targets : List Nat) (values : List IRExpr) (tempStart : Nat) : IRStmt :=
  let tempAssignments :=
    enumerate values |>.map (fun item => LeanExe.IR.Stmt.assign (tempStart + item.fst) item.snd)
  let targetAssignments :=
    enumerate targets |>.map (fun item => LeanExe.IR.Stmt.assign item.snd (.local (tempStart + item.fst)))
  LeanExe.IR.seqList (tempAssignments ++ targetAssignments)

def seqWithPrefix (prefixStmts : List IRStmt) (body : IRStmt) : IRStmt :=
  LeanExe.IR.seqList (prefixStmts ++ [body])

def addDoneAfter (doneSlot : Nat) (stmt : IRStmt) : IRStmt :=
  LeanExe.IR.seqList [stmt, .assign doneSlot (.u64 1)]

structure NatTailContext where
  extractCtx : Context
  useAbi : Bool
  params : List Ty
  resultTy : Ty
  resultTargets : List Nat
  doneSlot : Nat

partial def combineTailMatchArms (tag : IRExpr) : List (Nat × IRStmt) → Except String IRStmt
  | [] => .error "inductive matcher has no arms"
  | [(_index, stmt)] => .ok stmt
  | (index, stmt) :: rest => do
      let elseStmt ← combineTailMatchArms tag rest
      .ok (.ite (.eqU64 tag (.u64 index)) stmt elseStmt)

def extractClosedStructuralFoldFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  if !supportedInternalResultType resultTy then
    .error s!"unsupported closed structural fold result type: {reprStr resultTy}"
  let useAbi := exportName.isSome
  let wasmParamCount := functionParamCount useAbi params
  let paramLocals := localBindingsForParams useAbi params
  let body ←
    match collectLambdas value params.length with
    | some body => .ok body
    | none => .error s!"definition body does not match function arity: {name}"
  let shape ←
    match closedStructuralFoldShape? ctx.env body with
    | some shape => .ok shape
    | none => .error s!"unsupported closed structural fold shape: {name}"
  let layout ←
    match recursiveVariantLayout? ctx.env shape.typeName shape.typeParams with
    | some layout => .ok layout
    | none => .error s!"unsupported closed structural fold type: {shape.typeName}"
  let stepInfo ←
    structuralRecStepMatcher? ctx.env shape.typeName shape.typeParams 1 shape.step
  if stepInfo.layout != layout then
    .error s!"closed structural fold matcher type mismatch: {shape.typeName}"
  else if stepInfo.arms.length != layout.ctors.length then
    .error s!"inductive matcher arity mismatch: {layout.name}"
  else if stepInfo.prePostArgCount > 1 then
    .error s!"unsupported closed structural fold carried arguments: {name}"
  else
    let ctorInfos :=
      enumerate layout.ctors |>.map fun item =>
        ({
          index := item.fst,
          ctor := item.snd,
          recursiveOffsets :=
            directRecursiveFieldOffsets shape.typeName shape.typeParams item.snd.fields
        } : ClosedFoldCtorInfo)
    let continueInfos := ctorInfos.filter fun info => info.recursiveOffsets.length == 1
    let terminalInfos := ctorInfos.filter fun info => info.recursiveOffsets.isEmpty
    let continueInfo ←
      match continueInfos with
      | [info] => .ok info
      | _ => .error s!"closed structural fold requires one recursive constructor: {name}"
    if terminalInfos.length + 1 != ctorInfos.length then
      .error s!"closed structural fold requires list-shaped recursive constructors: {name}"
    else
      let recursiveFieldOffset ←
        match continueInfo.recursiveOffsets with
        | [offset] => .ok offset
        | _ => .error s!"closed structural fold requires one recursive field: {name}"
      let resultWidth := internalSlots resultTy
      let scrutineeResult ←
        extractValueFrom ctx paramLocals wasmParamCount shape.scrutinee
      let parts ← heapVariantPtrWithLets layout.name scrutineeResult.fst
      let ptrSlot := scrutineeResult.snd
      let ptrExpr := wrapExprLets parts.fst parts.snd
      let initResult ←
        extractValueFrom ctx paramLocals (ptrSlot + 1) shape.init
      let initSlots ← flattenInternalValue resultTy initResult.fst
      if initSlots.length != resultWidth then
        .error s!"closed structural fold initializer shape mismatch: {name}"
      else
      let accStart := initResult.snd
      let fieldSlotCount := runtimeFieldSlotCount continueInfo.ctor.fields
      let fieldStart := accStart + resultWidth
      let accValue :=
        valueFromInternalSlots resultTy fun offset => .local (accStart + offset)
      let postBinders :=
        [StructuralArmBinder.runtime (some resultTy) (.value accValue)]
      let rec parseTerminalArms : List ClosedFoldCtorInfo → Except String Unit
        | [] => .ok ()
        | info :: rest => do
            let arm ←
              match stepInfo.arms[info.index]? with
              | some arm => .ok arm
              | none => .error s!"inductive matcher arity mismatch: {layout.name}"
            let runtimeFields ← runtimeTypesFromKinds info.ctor.fields |>.mapM defaultValue
            let sourceBindings ←
              sourceFieldBindingsFromKinds layout.name info.ctor.fields runtimeFields
            let fieldBinders :=
              (info.ctor.fields.zip sourceBindings).map fun item =>
                StructuralArmBinder.runtime item.fst item.snd
            let belowBinding ←
              structuralBelowBinding name [] layout.name shape.typeParams info.ctor.name info.ctor.fields
                runtimeFields
            let parsedArm ←
              consumeStructuralCtorArm ctx layout.name stepInfo.prePostArgCount postBinders fieldBinders
                info.ctor belowBinding arm
            let armResult ←
              extractValueFrom ctx (parsedArm.snd ++ paramLocals)
                fieldStart parsedArm.fst
            let armSlots ← flattenInternalValue resultTy armResult.fst
            let expected := (List.range resultWidth).map fun offset => .local (accStart + offset)
            if armSlots == expected then
              parseTerminalArms rest
            else
              .error s!"closed structural fold terminal arm must return the accumulator: {name}"
      parseTerminalArms terminalInfos
      let runtimeFields := localRuntimeFieldsFromKinds continueInfo.ctor.fields fieldStart
      let sourceBindings ←
        sourceFieldBindingsFromKinds layout.name continueInfo.ctor.fields runtimeFields
      let fieldBinders :=
        (continueInfo.ctor.fields.zip sourceBindings).map fun item =>
          StructuralArmBinder.runtime item.fst item.snd
      let belowBinding ←
        structuralBelowBinding layout.name [] layout.name shape.typeParams
          continueInfo.ctor.name continueInfo.ctor.fields runtimeFields
      let continueArm ←
        match stepInfo.arms[continueInfo.index]? with
        | some arm => .ok arm
        | none => .error s!"inductive matcher arity mismatch: {layout.name}"
      let parsedContinue ←
        consumeStructuralCtorArm ctx layout.name stepInfo.prePostArgCount postBinders fieldBinders
          continueInfo.ctor belowBinding continueArm
      let recCall ←
        match ← structuralRecCallTarget? parsedContinue.snd parsedContinue.fst with
        | some recCall => .ok recCall
        | none => .error s!"closed structural fold step must tail-call the recursive field: {name}"
      if recCall.fst != layout.name then
        .error s!"closed structural fold recursive target mismatch: {name}"
      else
      let recursiveFieldValue := valueFromInternalSlots
        (.recVariant shape.typeName shape.typeParams)
        (fun _ => .local (fieldStart + recursiveFieldOffset))
      if recCall.snd.fst != recursiveFieldValue then
        .error s!"closed structural fold recursive field mismatch: {name}"
      else
      let recCapturedArgs := recCall.snd.snd.fst
      let recExtraArgs := recCall.snd.snd.snd
      if !recCapturedArgs.isEmpty then
        .error s!"closed structural fold recursive argument mismatch: {name}"
      else
      let nextAccExpr ←
        match recExtraArgs with
        | [arg] => .ok arg
        | _ => .error s!"closed structural fold step must update one carried argument: {name}"
      let nextAccResult ←
        extractValueFrom ctx (parsedContinue.snd ++ paramLocals)
          (fieldStart + fieldSlotCount) nextAccExpr
      let nextAccSlots ← flattenInternalValue resultTy nextAccResult.fst
      if nextAccSlots.length != resultWidth then
        .error s!"closed structural fold step result shape mismatch: {name}"
      else
      let fieldLoads :=
        (List.range fieldSlotCount).map fun offset =>
          LeanExe.IR.Stmt.assign (fieldStart + offset)
            (.heapLoadSlot (.local ptrSlot) (1 + offset))
      let initStores :=
        (enumerate initSlots).map fun item =>
          LeanExe.IR.Stmt.assign (accStart + item.fst) item.snd
      let accTargets := (List.range resultWidth).map fun offset => accStart + offset
      let tempStart := nextAccResult.snd
      let loopBody :=
        LeanExe.IR.seqList
          (fieldLoads ++
            [assignMany accTargets nextAccSlots tempStart,
              LeanExe.IR.Stmt.assign ptrSlot (.local (fieldStart + recursiveFieldOffset))])
      let loopCond : IRCond :=
        .eqU64 (.heapLoadSlot (.local ptrSlot) 0) (.u64 continueInfo.index)
      let resultCount := resultSlotCount useAbi resultTy
      let resultTargets :=
        (List.range resultCount).map (fun offset => tempStart + resultWidth + offset)
      let resultValue :=
        valueFromInternalSlots resultTy fun offset => .local (accStart + offset)
      let resultBody ← materializeResultValue ctx useAbi resultTy resultTargets resultValue
      .ok {
        sourceName := name,
        exportName := exportName,
        params := wasmParamCount,
        locals := tempStart + resultWidth + resultCount,
        body :=
          LeanExe.IR.seqList
            ([LeanExe.IR.Stmt.assign ptrSlot ptrExpr] ++
              initStores ++
              [LeanExe.IR.Stmt.while loopCond loopBody, resultBody]),
        results := resultTargets.map LeanExe.IR.Expr.local
      }

mutual
  partial def extractNatTailExitStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String TailStepResult := do
    let valueResult ← extractValueFrom lower.extractCtx locals nextLocal expr
    let stmt ←
      materializeResultValue lower.extractCtx lower.useAbi lower.resultTy lower.resultTargets valueResult.fst
    .ok {
      stmt := addDoneAfter lower.doneSlot stmt,
      nextLocal := valueResult.snd
    }

  partial def extractNatTailContinueStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (nextLocal : Nat)
      (recArgs : List Expr) :
      Except String TailStepResult := do
    let carriedParams := lower.params.drop 1
    let targets := (functionParamTargets lower.useAbi lower.params |>.drop 1).flatMap Prod.snd
    let argsResult ←
      extractCallArgsFrom lower.extractCtx locals nextLocal carriedParams recArgs
    let tempStart := argsResult.nextLocal
    let updateArgs :=
      LeanExe.IR.seqList
        (argsResult.lets.map valueLetStmt ++ [assignMany targets argsResult.args tempStart])
    let decFuel : IRStmt := .assign 0 (.u64Bin .sub (.local 0) (.u64 1))
    .ok {
      stmt := LeanExe.IR.seqList [updateArgs, decFuel],
      nextLocal := tempStart + targets.length
    }

  partial def extractNatTailUnitArmStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (nextLocal : Nat)
      (arm : Expr) :
      Except String TailStepResult := do
    match collectLambdas arm 1 with
    | some body =>
        extractNatTailStepStmt lower
          (.value (.scalar (.u64 0)) :: locals)
          (recursorIndex + 1)
          nextLocal
          body
    | none => extractNatTailStepStmt lower locals recursorIndex nextLocal arm

  partial def extractNatTailVariantArmResults
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (ctors : List VariantCtorLayout)
      (ctorValues : List (List ExtractedValue))
      (arms : List Expr)
      (nextLocal index : Nat) :
      Except String (List (Nat × IRStmt) × Nat) := do
    match ctors, ctorValues, arms with
    | [], [], [] => .ok ([], nextLocal)
    | ctor :: restCtors, values :: restValues, arm :: restArms =>
        let armResult ←
          if ctor.fields.isEmpty then
            extractNatTailUnitArmStmt lower locals recursorIndex nextLocal arm
          else
            let sourceBindings ← sourceFieldBindingsFromKinds ctor.name ctor.fields values
            let body ←
              match collectLambdas arm ctor.fields.length with
              | some body => .ok body
              | none => .error s!"unsupported inductive matcher arm: {ctor.name}"
            extractNatTailStepStmt lower
              (sourceBindings.reverse ++ locals)
              (recursorIndex + ctor.fields.length)
              nextLocal
              body
        let restResult ←
          extractNatTailVariantArmResults lower locals recursorIndex
            restCtors restValues restArms armResult.nextLocal (index + 1)
        .ok ((index, armResult.stmt) :: restResult.fst, restResult.snd)
    | _, _, _ => .error "inductive matcher arity mismatch"

  partial def extractNatTailVariantMatchStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (nextLocal : Nat)
      (layout : VariantLayout)
      (scrutinee : Expr)
      (arms : List Expr) :
      Except String TailStepResult := do
    if containsBVar recursorIndex scrutinee then
      .error "recursive call is not in tail position"
    else if arms.length != layout.ctors.length then
      .error s!"inductive matcher arity mismatch: {layout.name}"
    else if (recursiveVariantLayout? lower.extractCtx.env layout.name layout.params).isSome then
      .error s!"tail-recursive matcher over recursive inductive is unsupported: {layout.name}"
    else
      let scrutineeResult ← extractValueFrom lower.extractCtx locals nextLocal scrutinee
      let parts ← variantPartsWithLets layout.name scrutineeResult.fst
      let tag := parts.snd.fst
      let ctorValues := parts.snd.snd
      if ctorValues.length != layout.ctors.length then
        .error s!"inductive matcher value shape mismatch: {layout.name}"
      else
        let armResults ←
          extractNatTailVariantArmResults lower locals recursorIndex
            layout.ctors ctorValues arms scrutineeResult.snd 0
        let body ← combineTailMatchArms tag armResults.fst
        .ok {
          stmt := seqWithPrefix (parts.fst.map valueLetStmt) body,
          nextLocal := armResults.snd
        }

  partial def extractNatTailOptionMatchStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (nextLocal : Nat)
      (scrutinee noneArm someArm : Expr) :
      Except String TailStepResult := do
    if containsBVar recursorIndex scrutinee then
      .error "recursive call is not in tail position"
    else
      let scrutineeResult ← extractValueFrom lower.extractCtx locals nextLocal scrutinee
      let parts ← optionPartsWithLets scrutineeResult.fst
      let tag := parts.snd.fst
      let payload := parts.snd.snd
      let noneResult ←
        match collectLambdas noneArm 1 with
        | some body =>
            extractNatTailStepStmt lower
              (.value (.scalar (.u64 0)) :: locals)
              (recursorIndex + 1)
              scrutineeResult.snd
              body
        | none =>
            extractNatTailStepStmt lower locals recursorIndex scrutineeResult.snd noneArm
      let someBody ←
        match collectLambdas someArm 1 with
        | some body => .ok body
        | none => .error "unsupported Option.some matcher arm"
      let someResult ←
        extractNatTailStepStmt lower
          (.value payload :: locals)
          (recursorIndex + 1)
          noneResult.nextLocal
          someBody
      .ok {
        stmt :=
          seqWithPrefix (parts.fst.map valueLetStmt)
            (.ite (.eqU64 tag (.u64 0)) noneResult.stmt someResult.stmt),
        nextLocal := someResult.nextLocal
      }

  partial def extractNatTailBoolMatchStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (nextLocal : Nat)
      (scrutinee falseArm trueArm : Expr) :
      Except String TailStepResult := do
    if containsBVar recursorIndex scrutinee then
      .error "recursive call is not in tail position"
    else
      let condResult ← extractCond lower.extractCtx locals nextLocal scrutinee
      let falseResult ←
        extractNatTailUnitArmStmt lower locals recursorIndex condResult.snd falseArm
      let trueResult ←
        extractNatTailUnitArmStmt lower locals recursorIndex falseResult.nextLocal trueArm
      .ok {
        stmt := .ite condResult.fst trueResult.stmt falseResult.stmt,
        nextLocal := trueResult.nextLocal
      }

  partial def extractNatTailIfStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (nextLocal : Nat)
      (condExpr thenExpr elseExpr : Expr) :
      Except String TailStepResult := do
    if containsBVar recursorIndex condExpr then
      .error "recursive call is not in tail position"
    else
      let condResult ← extractCond lower.extractCtx locals nextLocal condExpr
      let thenResult ←
        extractNatTailStepStmt lower locals recursorIndex condResult.snd thenExpr
      let elseResult ←
        extractNatTailStepStmt lower locals recursorIndex thenResult.nextLocal elseExpr
      .ok {
        stmt := .ite condResult.fst thenResult.stmt elseResult.stmt,
        nextLocal := elseResult.nextLocal
      }

  partial def extractNatTailDiteStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (nextLocal : Nat)
      (condExpr thenArm elseArm : Expr) :
      Except String TailStepResult := do
    if containsBVar recursorIndex condExpr then
      .error "recursive call is not in tail position"
    else
      let condResult ← extractCond lower.extractCtx locals nextLocal condExpr
      let thenBody ←
        match collectLambdas thenArm 1 with
        | some body => .ok body
        | none => .error "unsupported dependent-if then arm"
      let elseBody ←
        match collectLambdas elseArm 1 with
        | some body => .ok body
        | none => .error "unsupported dependent-if else arm"
      let proofBinding := .value (.scalar (.u64 0))
      let thenResult ←
        extractNatTailStepStmt lower
          (proofBinding :: locals)
          (recursorIndex + 1)
          condResult.snd
          thenBody
      let elseResult ←
        extractNatTailStepStmt lower
          (proofBinding :: locals)
          (recursorIndex + 1)
          thenResult.nextLocal
          elseBody
      .ok {
        stmt := .ite condResult.fst thenResult.stmt elseResult.stmt,
        nextLocal := elseResult.nextLocal
      }

  partial def extractNatTailStepStmt
      (lower : NatTailContext)
      (locals : List Binding)
      (recursorIndex : Nat)
      (nextLocal : Nat)
      (expr : Expr) :
      Except String TailStepResult := do
    match expr.consumeMData with
    | .mdata _ body => extractNatTailStepStmt lower locals recursorIndex nextLocal body
    | .letE _ type value body _ =>
        if containsBVar recursorIndex value then
          .error "recursive call is not in tail position"
        else if !containsBVar 0 body then
          extractNatTailStepStmt lower (.recursor :: locals) (recursorIndex + 1) nextLocal body
        else if isStringType type then
          extractNatTailStepStmt lower
            (.thunk locals value :: locals)
            (recursorIndex + 1)
            nextLocal
            body
        else
          match typeAtom? lower.extractCtx.env type with
          | some ty =>
              if supportedLocalType ty then
                extractNatTailStepStmt lower
                  (.thunk locals value :: locals)
                  (recursorIndex + 1)
                  nextLocal
                  body
              else
                .error s!"unsupported let-bound type in tail recursion: {type}"
          | none => .error s!"unsupported let-bound type in tail recursion: {type}"
    | body =>
        let expectedArgs := lower.params.length - 1
        match recCallArgsAt? recursorIndex expectedArgs body with
        | some recArgs => extractNatTailContinueStmt lower locals nextLocal recArgs
        | none =>
            if !containsBVar recursorIndex body then
              extractNatTailExitStmt lower locals nextLocal body
            else
              match appFnArgs body with
              | (.const ``ite _, [_ty, condExpr, _, thenExpr, elseExpr]) =>
                  if containsBVar recursorIndex condExpr then
                    extractNatTailExitStmt lower locals nextLocal body
                  else
                    extractNatTailIfStmt lower locals recursorIndex nextLocal
                      condExpr thenExpr elseExpr
              | (.const ``dite _, [_ty, condExpr, _, thenArm, elseArm]) =>
                  if containsBVar recursorIndex condExpr then
                    extractNatTailExitStmt lower locals nextLocal body
                  else
                    extractNatTailDiteStmt lower locals recursorIndex nextLocal
                      condExpr thenArm elseArm
              | (fn, args) =>
                  match boolMatcherArgs? lower.extractCtx.env fn args with
                  | some (scrutinee, falseArm, trueArm) =>
                      if containsBVar recursorIndex scrutinee then
                        extractNatTailExitStmt lower locals nextLocal body
                      else
                        extractNatTailBoolMatchStmt lower locals recursorIndex nextLocal
                          scrutinee falseArm trueArm
                  | none =>
                      match optionMatcherArgs? lower.extractCtx.env fn args with
                      | some (scrutinee, noneArm, someArm) =>
                          if containsBVar recursorIndex scrutinee then
                            extractNatTailExitStmt lower locals nextLocal body
                          else
                            extractNatTailOptionMatchStmt lower locals recursorIndex nextLocal
                              scrutinee noneArm someArm
                      | none =>
                          match variantMatcherInfo? lower.extractCtx.env fn args with
                          | some info =>
                              if containsBVar recursorIndex info.scrutinee then
                                extractNatTailExitStmt lower locals nextLocal body
                              else if (recursiveVariantLayout? lower.extractCtx.env
                                  info.layout.name info.layout.params).isSome then
                                extractNatTailExitStmt lower locals nextLocal body
                              else
                                extractNatTailVariantMatchStmt lower locals recursorIndex nextLocal
                                  info.layout info.scrutinee info.arms
                          | none =>
                              extractNatTailExitStmt lower locals nextLocal body
end

def extractNatRecFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let sourceParamCount := params.length
  let useAbi := exportName.isSome
  let wasmParamCount := functionParamCount useAbi params
  let shape ←
    match ← findNatRecShape? ctx.env name sourceParamCount value with
    | some shape => .ok shape
    | none => .error s!"unsupported Nat recursion shape: {name}"
  let stepLocals := stepBindingsForParams useAbi name params
  let baseLocals := baseBindingsForParams useAbi name params
  let fuelLive : IRCond := .not (.eqU64 (.local 0) (.u64 0))
  let resultCount := resultSlotCount useAbi resultTy
  let resultStart := wasmParamCount
  let resultTargets := (List.range resultCount).map (fun offset => resultStart + offset)
  let doneSlot := resultStart + resultCount
  let tempStart := doneSlot + 1
  let lower : NatTailContext := {
    extractCtx := ctx,
    useAbi := useAbi,
    params := params,
    resultTy := resultTy,
    resultTargets := resultTargets,
    doneSlot := doneSlot
  }
  let stepResult ← extractNatTailStepStmt lower stepLocals 0 tempStart shape.step
  let baseResult ← extractValueFrom ctx baseLocals stepResult.nextLocal shape.base
  let baseBody ← materializeResultValue ctx useAbi resultTy resultTargets baseResult.fst
  let loopCond : IRCond := .and fuelLive (.eqU64 (.local doneSlot) (.u64 0))
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := baseResult.snd,
    body :=
      LeanExe.IR.seqList
        [.assign doneSlot (.u64 0),
          .while loopCond stepResult.stmt,
          .ite (.eqU64 (.local doneSlot) (.u64 0)) baseBody .skip],
    results := resultTargets.map LeanExe.IR.Expr.local
  }

def extractPlainFunc
    (ctx : Context)
    (name : Name)
    (params : List Ty)
    (resultTy : Ty)
    (value : Expr)
    (exportName : Option String) : Except String IRFunc := do
  let sourceParamCount := params.length
  let useAbi := exportName.isSome
  let wasmParamCount := functionParamCount useAbi params
  let paramLocals := localBindingsForParams useAbi params
  let body ←
    match collectLambdas value sourceParamCount with
    | some body => .ok body
    | none => .error s!"definition body does not match function arity: {name}"
  let result ← extractValueFrom ctx paramLocals wasmParamCount body
  let resultCount := resultSlotCount useAbi resultTy
  let resultTargets := (List.range resultCount).map (fun offset => result.snd + offset)
  let resultBody ← materializeResultValue ctx useAbi resultTy resultTargets result.fst
  .ok {
    sourceName := name,
    exportName := exportName,
    params := wasmParamCount,
    locals := result.snd + resultCount,
    body := resultBody,
    results := resultTargets.map LeanExe.IR.Expr.local
  }

def shortExportName (name : Name) : String :=
  match (LeanExe.Extract.Env.displayName name).splitOn "." |>.reverse with
  | part :: _ => part
  | [] => LeanExe.Extract.Env.displayName name

def reservedExportNames : List String :=
  ["memory", "alloc", "reset"]

def extractFunction
    (exportEntry : Bool)
    (ctx : Context)
    (entry name : Name)
    (info : ConstantInfo)
    (sig : Signature) : Except String IRFunc := do
  let value ←
    match info.value? with
    | some value => .ok (betaSpecializeExpr ctx.env ctx.root 32 value)
    | none => .error s!"declaration has no executable value: {name}"
  let exportName ←
    if exportEntry && name == entry then
      let candidate := shortExportName name
      if reservedExportNames.contains candidate then
        .error s!"entry export name is reserved by the runtime ABI: {candidate}"
      else
        .ok (some candidate)
    else
      .ok none
  match sig.params with
  | .nat :: _ =>
      if containsConstantInExpr ``Nat.brecOn value then
        extractNatRecFunc ctx name sig.params sig.result value exportName
      else
        extractPlainFunc ctx name sig.params sig.result value exportName
  | .sum _ _ :: _ =>
      if containsConstantInExpr ``WellFounded.Nat.fix value then
        match extractWellFoundedNatSumFunc ctx name sig.params sig.result value exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting well-founded Nat recursion: {error}"
      else
        match extractPlainFunc ctx name sig.params sig.result value exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting plain function: {error}"
  | .recVariant typeName typeParams :: _ =>
      if containsConstantInExpr (brecOnName typeName) value then
        match extractStructuralRecFunc ctx name sig.params typeName typeParams sig.result value exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting structural recursion: {error}"
      else if containsConstantInExpr ``WellFounded.Nat.fix value then
        match extractWellFoundedNatRecFunc ctx name sig.params typeName typeParams sig.result value
            exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting well-founded Nat recursion: {error}"
      else if containsConstantInExpr ``WellFounded.fix value then
        match extractWellFoundedRecFunc ctx name sig.params typeName typeParams sig.result value exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting well-founded recursion: {error}"
      else
        match extractPlainFunc ctx name sig.params sig.result value exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting plain function: {error}"
  | _ =>
      if closedStructuralFoldCandidate? ctx.env value sig.params.length then
        match extractClosedStructuralFoldFunc ctx name sig.params sig.result value exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting closed structural fold: {error}"
      else
        match extractPlainFunc ctx name sig.params sig.result value exportName with
        | .ok func => .ok func
        | .error error => .error s!"while extracting plain function: {error}"

def structuralExpressionSyntheticName (root : Name) (index : Nat) : Name :=
  .str (.str root "_leanexe_expr_rec") (toString index)

partial def freshStructuralExpressionSyntheticName
    (env : Environment)
    (root : Name)
    (reserved : List Name)
    (index : Nat) :
    Name :=
  let candidate := structuralExpressionSyntheticName root index
  if reserved.contains candidate || (env.find? candidate).isSome then
    freshStructuralExpressionSyntheticName env root reserved (index + 1)
  else
    candidate

def topLevelStructuralRecCandidate? (env : Environment) (value : Expr) (params : List Ty) : Bool :=
  match params with
  | .recVariant typeName typeParams :: _ =>
      match collectLambdas value params.length with
      | some body =>
          match rawStructuralRecApplication? env body with
          | some app =>
              app.typeName == typeName &&
                app.typeParams == typeParams &&
                isBVar (params.length - 1) app.scrutinee
          | none => false
      | none => false
  | _ => false

partial def collectExpressionStructuralSynthetics
    (env : Environment)
    (root : Name)
    (reserved : List Name)
    (localTypes : List (Option Ty))
    (expr : Expr)
    (synthetics : Array SyntheticFunction) :
    Array SyntheticFunction :=
  let synthetics :=
    match expressionStructuralRecShapeWithLocalTypes? env root localTypes expr with
    | some shape =>
        if synthetics.toList.any (fun synth => syntheticMatchesShape synth shape) then
          synthetics
        else
            let reserved := reserved ++ synthetics.toList.map (fun synth => synth.name)
            let name := freshStructuralExpressionSyntheticName env root reserved synthetics.size
            match structuralExpressionSyntheticValue? shape with
            | some value =>
                synthetics.push {
                  name := name,
                  sig := {
                    params := .recVariant shape.typeName shape.typeParams ::
                      (shape.dynamicPostArgTypes ++ shape.captureTypes),
                    result := shape.resultTy
                  },
                  value := value,
                  typeName := shape.typeName,
                  typeParams := shape.typeParams,
                  dynamicPostArgTypes := shape.dynamicPostArgTypes,
                  captureIndices := shape.captureIndices,
                  captureTypes := shape.captureTypes,
                  motive := shape.motive,
                  step := shape.step,
                  postArgs := shape.postArgs
                }
            | none => synthetics
    | none => synthetics
  match expr.consumeMData with
  | .app fn arg =>
      let synthetics := collectExpressionStructuralSynthetics env root reserved localTypes fn synthetics
      collectExpressionStructuralSynthetics env root reserved localTypes arg synthetics
  | .lam _ type body _ =>
      let synthetics := collectExpressionStructuralSynthetics env root reserved localTypes type synthetics
      let localType := typeAtom? env type
      collectExpressionStructuralSynthetics env root reserved (localType :: localTypes) body synthetics
  | .forallE _ type body _ =>
      let synthetics := collectExpressionStructuralSynthetics env root reserved localTypes type synthetics
      let localType := typeAtom? env type
      collectExpressionStructuralSynthetics env root reserved (localType :: localTypes) body synthetics
  | .letE _ type value body _ =>
      let synthetics := collectExpressionStructuralSynthetics env root reserved localTypes type synthetics
      let synthetics := collectExpressionStructuralSynthetics env root reserved localTypes value synthetics
      let localType := typeAtom? env type
      collectExpressionStructuralSynthetics env root reserved (localType :: localTypes) body synthetics
  | .mdata _ body => collectExpressionStructuralSynthetics env root reserved localTypes body synthetics
  | .proj _ _ body => collectExpressionStructuralSynthetics env root reserved localTypes body synthetics
  | _ => synthetics

def collectFunctionExpressionStructuralSynthetics
    (env : Environment)
    (root : Name)
    (reserved : List Name)
    (sig : Signature)
    (value : Expr)
    (synthetics : Array SyntheticFunction) :
    Array SyntheticFunction :=
  if topLevelStructuralRecCandidate? env value sig.params then
    synthetics
  else
    collectExpressionStructuralSynthetics env root reserved [] value synthetics

def entryModeSignature?
    (exportEntry : Bool)
    (env : Environment)
    (entry name : Name)
    (info : ConstantInfo) :
    Option Signature :=
  if exportEntry && name == entry then
    supportedEntryFunction? env info
  else
    supportedFunction? env info

def compileEnvironmentWithEntryMode
    (exportEntry : Bool)
    (env : Environment)
    (moduleName entry : Name) :
    Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let _entrySig ←
    match entryModeSignature? exportEntry env entry entry entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  let (_, namesList) ← collectReachable env moduleName.getRoot entry [] []
  let root := moduleName.getRoot
  let mut synthetics := #[]
  for name in namesList do
    let info ←
      match env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during extraction: {name}"
    let sig ←
      match entryModeSignature? exportEntry env entry name info with
      | some sig => .ok sig
      | none => .error s!"unsupported function type or declaration: {name}"
    let value ←
      match info.value? with
      | some value => .ok (betaSpecializeExpr env root 32 value)
      | none => .error s!"declaration has no executable value: {name}"
    synthetics := collectFunctionExpressionStructuralSynthetics env root namesList sig value synthetics
  let names := (namesList ++ synthetics.toList.map (fun synth => synth.name)).toArray
  let ctx : Context :=
    { env := env, root := root, names := names, synthetics := synthetics, inlineStack := [] }
  let mut funcs := #[]
  for name in namesList do
    let info ←
      match env.find? name with
      | some info => .ok info
      | none => .error s!"declaration disappeared during extraction: {name}"
    let sig ←
      match entryModeSignature? exportEntry ctx.env entry name info with
      | some sig => .ok sig
      | none => .error s!"unsupported function type or declaration: {name}"
    let func ←
      match extractFunction exportEntry ctx entry name info sig with
      | .ok func => .ok func
      | .error error => .error s!"while extracting {name}: {error}"
    funcs := funcs.push func
  for synth in synthetics do
    let func ←
      match extractStructuralRecFunc ctx synth.name synth.sig.params synth.typeName synth.typeParams
          synth.sig.result synth.value none with
      | .ok func => .ok func
      | .error error => .error s!"while extracting {synth.name}: {error}"
    funcs := funcs.push func
  .ok { funcs := funcs }

def compileEnvironment (env : Environment) (moduleName entry : Name) : Except String IRModule :=
  compileEnvironmentWithEntryMode true env moduleName entry

def compileInternalEntryEnvironment (env : Environment) (moduleName entry : Name) :
    Except String IRModule :=
  compileEnvironmentWithEntryMode false env moduleName entry

def compile (moduleText entryText : String) : IO IRModule := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileEnvironment env moduleName entryName with
  | .ok module_ => pure module_
  | .error error => throw <| IO.userError error

def compileProgramEnvironment (env : Environment) (moduleName entry : Name) :
    Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let entrySig ←
    match supportedEntryFunction? env entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  if !entrySig.params.isEmpty then
    .error s!"program entry must take no parameters: {entry}"
  else if entrySig.result != .byteArray then
    .error s!"program entry must return ByteArray: {entry}"
  else
    compileEnvironment env moduleName entry

def compileStdinProgramEnvironment (env : Environment) (moduleName entry : Name) :
    Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let entrySig ←
    match supportedEntryFunction? env entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  if entrySig.params != [.byteArray] || entrySig.result != .byteArray then
    .error s!"program stdin entry must have type ByteArray -> ByteArray: {entry}"
  else
    compileEnvironment env moduleName entry

def stdinExceptResultTy : Ty :=
  .variant ``Except [.byteArray, .byteArray] [[.byteArray], [.byteArray]]

def argvExceptParamTy : Ty :=
  .array .byteArray

def compileStdinExceptProgramEnvironment (env : Environment) (moduleName entry : Name) :
    Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let entrySig ←
    match supportedEntryFunction? env entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  if entrySig.params != [.byteArray] || entrySig.result != stdinExceptResultTy then
    .error s!"program stdin-except entry must have type ByteArray -> Except ByteArray ByteArray: {entry}"
  else
    compileEnvironment env moduleName entry

def compileArgvExceptProgramEnvironment (env : Environment) (moduleName entry : Name) :
    Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let entrySig ←
    match supportedFunction? env entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  if entrySig.params != [argvExceptParamTy] || entrySig.result != stdinExceptResultTy then
    .error s!"program argv-except entry must have type Array ByteArray -> Except ByteArray ByteArray: {entry}"
  else
    compileInternalEntryEnvironment env moduleName entry

def compileStdinArgvExceptProgramEnvironment (env : Environment) (moduleName entry : Name) :
    Except String IRModule := do
  let entryInfo ←
    match env.find? entry with
    | some info => .ok info
    | none => .error s!"entry not found: {entry}"
  let entrySig ←
    match supportedFunction? env entryInfo with
    | some sig => .ok sig
    | none => .error s!"unsupported function type or declaration: {entry}"
  if entrySig.params != [.byteArray, argvExceptParamTy] || entrySig.result != stdinExceptResultTy then
    .error s!"program stdin-argv-except entry must have type ByteArray -> Array ByteArray -> Except ByteArray ByteArray: {entry}"
  else
    compileInternalEntryEnvironment env moduleName entry

def compileProgram (moduleText entryText : String) : IO IRModule := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileProgramEnvironment env moduleName entryName with
  | .ok module_ => pure module_
  | .error error => throw <| IO.userError error

def compileStdinProgram (moduleText entryText : String) : IO IRModule := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileStdinProgramEnvironment env moduleName entryName with
  | .ok module_ => pure module_
  | .error error => throw <| IO.userError error

def compileStdinExceptProgram (moduleText entryText : String) : IO IRModule := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileStdinExceptProgramEnvironment env moduleName entryName with
  | .ok module_ => pure module_
  | .error error => throw <| IO.userError error

def compileArgvExceptProgram (moduleText entryText : String) : IO IRModule := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileArgvExceptProgramEnvironment env moduleName entryName with
  | .ok module_ => pure module_
  | .error error => throw <| IO.userError error

def compileStdinArgvExceptProgram (moduleText entryText : String) : IO IRModule := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match compileStdinArgvExceptProgramEnvironment env moduleName entryName with
  | .ok module_ => pure module_
  | .error error => throw <| IO.userError error

end LeanExe.Extract.Core
