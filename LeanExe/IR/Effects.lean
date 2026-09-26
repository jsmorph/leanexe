import LeanExe.IR.Core

namespace LeanExe.IR

mutual
  partial def Expr.hasEffects : Expr → Bool
    | .local _ => false
    | .trap => false
    | .u64 _ => false
    | .f64SqrtBits value => Expr.hasEffects value
    | .scalarUnary _ value => Expr.hasEffects value
    | .u64Bin _ left right => Expr.hasEffects left || Expr.hasEffects right
    | .ite cond thenValue elseValue =>
        Cond.hasEffects cond ||
        Expr.hasEffects thenValue ||
        Expr.hasEffects elseValue
    | .letE _ value body => Expr.hasEffects value || Expr.hasEffects body
    | .letCall _ _ args body => args.any Expr.hasEffects || Expr.hasEffects body
    | .letLets lets body => lets.any LocalLet.hasEffects || Expr.hasEffects body
    | .runtimeStat _ => false
    | .release _ => true
    | .arrayAllocSlots _ _ cells => Expr.hasEffects cells
    | .heapAllocSlots _ _ values => values.any Expr.hasEffects
    | .heapLoadSlot ptr _ => Expr.hasEffects ptr
    | .arrayReplicateSlots _ _ _ cells values => Expr.hasEffects cells || values.any Expr.hasEffects
    | .arrayLiteralSlots _ _ elements => elements.any (fun item => item.2.any Expr.hasEffects)
    | .arraySize array => Expr.hasEffects array
    | .arrayGetSlot _ _ array index => Expr.hasEffects array || Expr.hasEffects index
    | .arraySetSlots _ _ _ array index values =>
        Expr.hasEffects array ||
        Expr.hasEffects index ||
        values.any Expr.hasEffects
    | .arrayPushSlots _ _ _ array values => Expr.hasEffects array || values.any Expr.hasEffects
    | .arrayPopSlots _ _ array => Expr.hasEffects array
    | .arrayAppendSlots _ _ left right => Expr.hasEffects left || Expr.hasEffects right
    | .arrayExtractSlots _ _ array start stop =>
        Expr.hasEffects array ||
        Expr.hasEffects start ||
        Expr.hasEffects stop
    | .arrayMapSlots _ _ _ _ array _ bodyValues bodyLets =>
        Expr.hasEffects array ||
        bodyValues.any Expr.hasEffects ||
        bodyLets.any LocalLet.hasEffects
    | .arrayFoldMultiSlot _ _ _ array start stop initValues _ _ bodyValues bodyLets bodyDone _ _ =>
        Expr.hasEffects array ||
        Expr.hasEffects start ||
        Expr.hasEffects stop ||
        initValues.any Expr.hasEffects ||
        bodyValues.any Expr.hasEffects ||
        bodyLets.any LocalLet.hasEffects ||
        Expr.hasEffects bodyDone
    | .arrayFindIdxSlots _ array _ predicate _ => Expr.hasEffects array || Expr.hasEffects predicate
    | .arrayFindSlot _ array _ predicate _ => Expr.hasEffects array || Expr.hasEffects predicate
    | .arrayEqSlots _ left right _ _ predicate =>
        Expr.hasEffects left ||
        Expr.hasEffects right ||
        Expr.hasEffects predicate
    | .arrayAnySlots _ array start stop _ predicate _ =>
        Expr.hasEffects array ||
        Expr.hasEffects start ||
        Expr.hasEffects stop ||
        Expr.hasEffects predicate
    | .arrayFilterSlots _ _ array start stop _ predicate =>
        Expr.hasEffects array ||
        Expr.hasEffects start ||
        Expr.hasEffects stop ||
        Expr.hasEffects predicate
    | .arrayInsertIfInBoundsSlots _ _ _ array index values =>
        Expr.hasEffects array ||
        Expr.hasEffects index ||
        values.any Expr.hasEffects
    | .arrayEraseIfInBoundsSlots _ _ array index => Expr.hasEffects array || Expr.hasEffects index
    | .arraySwapIfInBoundsSlots _ _ array left right =>
        Expr.hasEffects array ||
        Expr.hasEffects left ||
        Expr.hasEffects right
    | .arrayReverseSlots _ _ array => Expr.hasEffects array
    | .byteArrayGet ptr len index => Expr.hasEffects ptr || Expr.hasEffects len || Expr.hasEffects index
    | .byteArrayLoad32 ptr len offset =>
        Expr.hasEffects ptr ||
        Expr.hasEffects len ||
        Expr.hasEffects offset
    | .byteArrayGeneratePtr _ byteLen _ body => Expr.hasEffects byteLen || Expr.hasEffects body
    | .byteArrayPushPtr ptr len value => Expr.hasEffects ptr || Expr.hasEffects len || Expr.hasEffects value
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        Expr.hasEffects leftPtr ||
        Expr.hasEffects leftLen ||
        Expr.hasEffects rightPtr ||
        Expr.hasEffects rightLen
    | .byteArraySetPtr ptr len index value =>
        Expr.hasEffects ptr ||
        Expr.hasEffects len ||
        Expr.hasEffects index ||
        Expr.hasEffects value
    | .byteArrayFromArrayPtr array => Expr.hasEffects array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        Expr.hasEffects srcPtr ||
        Expr.hasEffects srcLen ||
        Expr.hasEffects srcOff ||
        Expr.hasEffects destPtr ||
        Expr.hasEffects destLen ||
        Expr.hasEffects destOff ||
        Expr.hasEffects copyLen
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        Expr.hasEffects leftPtr ||
        Expr.hasEffects leftLen ||
        Expr.hasEffects rightPtr ||
        Expr.hasEffects rightLen
    | .byteArrayFindIdx ptr len start _ predicate _ =>
        Expr.hasEffects ptr ||
        Expr.hasEffects len ||
        Expr.hasEffects start ||
        Expr.hasEffects predicate
    | .byteArrayFoldMultiSlot _ ptr len start stop initValues _ _ bodyValues bodyLets bodyDone _ _ =>
        Expr.hasEffects ptr ||
        Expr.hasEffects len ||
        Expr.hasEffects start ||
        Expr.hasEffects stop ||
        initValues.any Expr.hasEffects ||
        bodyValues.any Expr.hasEffects ||
        bodyLets.any LocalLet.hasEffects ||
        Expr.hasEffects bodyDone
    | .rangeFoldMultiSlot _ start stop step initValues _ _ bodyValues bodyLets bodyDone _ _ =>
        Expr.hasEffects start ||
        Expr.hasEffects stop ||
        Expr.hasEffects step ||
        initValues.any Expr.hasEffects ||
        bodyValues.any Expr.hasEffects ||
        bodyLets.any LocalLet.hasEffects ||
        Expr.hasEffects bodyDone
    | .loopFoldMultiSlot _ initValues _ bodyValues bodyLets bodyDone _ _ =>
        initValues.any Expr.hasEffects ||
        bodyValues.any Expr.hasEffects ||
        bodyLets.any LocalLet.hasEffects ||
        Expr.hasEffects bodyDone
    | .heapLinearPredicate ptr _ _ _ _ predicate _ _ => Expr.hasEffects ptr || Expr.hasEffects predicate
    | .call _ args => args.any Expr.hasEffects

  partial def Cond.hasEffects : Cond → Bool
    | .true => false
    | .false => false
    | .eqU64 left right => Expr.hasEffects left || Expr.hasEffects right
    | .ltU64 left right => Expr.hasEffects left || Expr.hasEffects right
    | .leU64 left right => Expr.hasEffects left || Expr.hasEffects right
    | .not cond => Cond.hasEffects cond
    | .and left right => Cond.hasEffects left || Cond.hasEffects right
    | .or left right => Cond.hasEffects left || Cond.hasEffects right

  partial def LocalLet.hasEffects : LocalLet → Bool
    | .effectCall _ _ _ => true
    | .expr _ value => Expr.hasEffects value
    | .call _ _ args => args.any Expr.hasEffects
    | .slots _ values => values.any Expr.hasEffects
    | .branch cond thenLets elseLets =>
        Cond.hasEffects cond ||
        thenLets.any LocalLet.hasEffects ||
        elseLets.any LocalLet.hasEffects

end

end LeanExe.IR
