import Lean
import LeanExe.Extract.Types
import LeanExe.IR.Core
import LeanExe.Runtime

open Lean

namespace LeanExe.Extract.Core

def lookupBinding (locals : List Binding) (index : Nat) : Except String Binding :=
  match locals[index]? with
  | some binding => .ok binding
  | none => .error s!"unbound de Bruijn variable: {index}"

def structuralBelowProjection (below : StructuralBelow) (index : Nat) :
    Except String StructuralBelow :=
  match below, index with
  | .pair left _, 0 => .ok left
  | .pair _ right, 1 => .ok right
  | _, _ => .error "unsupported structural recursion below projection"

partial def structuralBelowFromExpr?
    (locals : List Binding)
    (expr : Expr) :
    Except String (Option StructuralBelow) := do
  match expr.consumeMData with
  | .bvar index =>
      match ← lookupBinding locals index with
      | .structuralRec functionName arg => .ok (some (.call functionName arg []))
      | .structuralBelow below => .ok (some below)
      | _ => .ok none
  | .proj ``PProd index body =>
      match ← structuralBelowFromExpr? locals body with
      | some below => .ok (some (← structuralBelowProjection below index))
      | none => .ok none
  | _ => .ok none

def structuralRecProjection?
    (locals : List Binding)
    (expr : Expr) :
    Except String (Option (Name × ExtractedValue × List ExtractedValue)) := do
  match ← structuralBelowFromExpr? locals expr with
  | some (.call functionName arg capturedArgs) => .ok (some (functionName, arg, capturedArgs))
  | some _ => .error "unsupported structural recursion projection"
  | none => .ok none

def primitiveArgPair? (args : List Expr) : Option (Expr × Expr) :=
  match args.reverse with
  | right :: left :: _ => some (left, right)
  | _ => none

def primitiveResultType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | _leftType :: _rightType :: resultType :: _ => typeAtom? env resultType
  | _ => none

def primitiveReceiverType? (env : Environment) (args : List Expr) : Option Ty :=
  match args with
  | ty :: _ => typeAtom? env ty
  | _ => none

def primitiveStringReceiver? (args : List Expr) : Bool :=
  match args with
  | ty :: _ => isStringType ty
  | _ => false

def primitiveStringResult? (args : List Expr) : Bool :=
  match args with
  | _leftTy :: _rightTy :: resultTy :: _ => isStringType resultTy
  | _ => false

def runtimeStatPrimitive? (name : Name) : Option LeanExe.IR.RuntimeStat :=
  if name == ``LeanExe.Runtime.allocCount then
    some .allocs
  else if name == ``LeanExe.Runtime.retainCount then
    some .retains
  else if name == ``LeanExe.Runtime.releaseCount then
    some .releases
  else if name == ``LeanExe.Runtime.freeCount then
    some .frees
  else
    none

partial def compileTimeString?
    (ctx : Context)
    (locals : List Binding)
    (fuel : Nat)
    (expr : Expr) : Option String :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match expr.consumeMData with
      | .lit (.strVal value) => some value
      | .bvar index =>
          match lookupBinding locals index with
          | .ok (.thunk savedLocals value) => compileTimeString? ctx savedLocals fuel value
          | _ => none
      | .letE _ type value body _ =>
          if containsBVar 0 body then
            if isStringType type then
              compileTimeString? ctx (.thunk locals value :: locals) fuel body
            else
              none
          else
            compileTimeString? ctx (.recursor :: locals) fuel body
      | .mdata _ body => compileTimeString? ctx locals fuel body
      | .const name _ =>
          match ctx.env.find? name with
          | some info =>
              if isStringType info.type then
                match info.value? with
                | some value => compileTimeString? ctx [] fuel value
                | none => none
              else
                none
          | none => none
      | _ =>
          match appFnArgs expr with
          | (.const ``String.append _, [left, right]) =>
              match compileTimeString? ctx locals fuel left,
                  compileTimeString? ctx locals fuel right with
              | some leftValue, some rightValue => some (leftValue ++ rightValue)
              | _, _ => none
          | (.const ``HAppend.hAppend _, args) =>
              if primitiveStringResult? args then
                match primitiveArgPair? args with
                | some (left, right) =>
                    match compileTimeString? ctx locals fuel left,
                        compileTimeString? ctx locals fuel right with
                    | some leftValue, some rightValue => some (leftValue ++ rightValue)
                    | _, _ => none
                | none => none
              else
                none
          | (.const ``Append.append _, args) =>
              if primitiveStringReceiver? args then
                match primitiveArgPair? args with
                | some (left, right) =>
                    match compileTimeString? ctx locals fuel left,
                        compileTimeString? ctx locals fuel right with
                    | some leftValue, some rightValue => some (leftValue ++ rightValue)
                    | _, _ => none
                | none => none
              else
                none
          | (.const ``id _, args) =>
              match args.reverse with
              | value :: _ => compileTimeString? ctx locals fuel value
              | _ => none
          | _ => none

def asciiStringExprBytesFrom
    (ctx : Context)
    (locals : List Binding)
    (expr : Expr)
    (unsupportedMessage nonAsciiMessage : String) :
    Except String (List UInt8) :=
  match compileTimeString? ctx locals 256 expr with
  | some value =>
      match asciiStringBytes? value with
      | some bytes => .ok bytes
      | none => .error nonAsciiMessage
  | none => .error unsupportedMessage

def boolExpr (cond : IRCond) : IRExpr :=
  .ite cond (.u64 1) (.u64 0)

def boolCond (expr : IRExpr) : IRCond :=
  .not (.eqU64 expr (.u64 0))

def irConstNat? : IRExpr → Option Nat
  | .u64 value => some value
  | _ => none

def u8WrapExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 255)

def u8ShiftAmountExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 7)

def u32WrapExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 (2 ^ 32 - 1))

def u32ShiftAmountExpr (expr : IRExpr) : IRExpr :=
  .u64Bin .bitAnd expr (.u64 31)

partial def supportedEqType : Ty → Bool
  | .unit => true
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | .byteArray => true
  | .array item => supportedEqType item && (arrayElementSlots? item |>.isSome)
  | .product left right => supportedEqType left && supportedEqType right
  | .sum left right => supportedEqType left && supportedEqType right
  | .struct _ _ fields => fields.all supportedEqType
  | .variant _ _ ctors => ctors.all (fun fields => fields.all supportedEqType)
  | _ => false

def addLiveSlot (live : List Nat) (slot : Nat) : List Nat :=
  if live.contains slot then live else slot :: live

def addLiveSlots (live slots : List Nat) : List Nat :=
  slots.foldl addLiveSlot live

def removeLiveSlot (live : List Nat) (slot : Nat) : List Nat :=
  live.filter fun candidate => candidate != slot

def removeLiveSlots (live slots : List Nat) : List Nat :=
  slots.foldl removeLiveSlot live

def anyLiveSlot (live slots : List Nat) : Bool :=
  slots.any fun slot => live.contains slot

def slotsFrom (start width : Nat) : List Nat :=
  (List.range width).map fun offset => start + offset

mutual
  partial def tyReleaseOwnerSlotOffsetsAt (base : Nat) : Ty → List Nat
    | .array item =>
        if supportedArrayElementType item then [base] else []
    | .byteArray => [base]
    | .product left right =>
        addLiveSlots
          (tyReleaseOwnerSlotOffsetsAt base left)
          (tyReleaseOwnerSlotOffsetsAt (base + internalSlots left) right)
    | .struct _ _ fields => tyListReleaseOwnerSlotOffsetsAt base fields
    | _ => []

  partial def tyListReleaseOwnerSlotOffsetsAt (base : Nat) : List Ty → List Nat
    | [] => []
    | ty :: rest =>
        addLiveSlots
          (tyReleaseOwnerSlotOffsetsAt base ty)
          (tyListReleaseOwnerSlotOffsetsAt (base + internalSlots ty) rest)
end

def tyReleaseOwnerSlotOffsets (ty : Ty) : List Nat :=
  tyReleaseOwnerSlotOffsetsAt 0 ty

partial def tyContainsHeapPointer : Ty → Bool
  | .byteArray => true
  | .array _ => true
  | .recVariant _ _ => true
  | .product left right => tyContainsHeapPointer left || tyContainsHeapPointer right
  | .sum left right => tyContainsHeapPointer left || tyContainsHeapPointer right
  | .struct _ _ fields => fields.any tyContainsHeapPointer
  | .variant _ _ ctors => ctors.any fun ctor => ctor.any tyContainsHeapPointer
  | .unit => false
  | .bool => false
  | .u8 => false
  | .u32 => false
  | .u64 => false
  | .nat => false

def slotsAtOffsets (slots offsets : List Nat) : List Nat :=
  offsets.filterMap fun offset => slots[offset]?

def functionNameAtIndex? (ctx : Context) (index : Nat) : Option Name :=
  if h : index < ctx.names.size then
    some ctx.names[index]
  else
    none

def callResultReleaseOwnerSlots (ctx : Context) (index : Nat) (slots : List Nat) : List Nat :=
  match functionNameAtIndex? ctx index with
  | some name =>
      match functionSignature? ctx name with
      | some sig =>
          if sig.params.any tyContainsHeapPointer then
            []
          else
            slotsAtOffsets slots (tyReleaseOwnerSlotOffsets sig.result)
      | none => []
  | none => []

mutual
  partial def exprUsedSlots : IRExpr → List Nat
    | .local index => [index]
    | .trap => []
    | .u64 _ => []
    | .u64Bin _ left right =>
        addLiveSlots (exprUsedSlots left) (exprUsedSlots right)
    | .ite cond thenValue elseValue =>
        addLiveSlots (addLiveSlots (condUsedSlots cond) (exprUsedSlots thenValue))
          (exprUsedSlots elseValue)
    | .letE slot value body =>
        let bodyLive := exprUsedSlots body
        if bodyLive.contains slot then
          addLiveSlots (removeLiveSlot bodyLive slot) (exprUsedSlots value)
        else
          bodyLive
    | .letCall slots _ args body =>
        let bodyLive := exprUsedSlots body
        if anyLiveSlot bodyLive slots then
          addLiveSlots (removeLiveSlots bodyLive slots) (exprListUsedSlots args)
        else
          bodyLive
    | .letLets lets body =>
        (pruneLocalLetsWithLive lets (exprUsedSlots body)).snd
    | .runtimeStat _ => []
    | .release ptr => exprUsedSlots ptr
    | .arrayAllocSlots _ _ cells => exprUsedSlots cells
    | .heapAllocSlots _ values => exprListUsedSlots values
    | .heapLoadSlot ptr _ => exprUsedSlots ptr
    | .arrayReplicateSlots _ _ _ cells values =>
        addLiveSlots (exprUsedSlots cells) (exprListUsedSlots values)
    | .arraySize array => exprUsedSlots array
    | .arrayGetSlot _ _ array index =>
        addLiveSlots (exprUsedSlots array) (exprUsedSlots index)
    | .arraySetSlots _ _ _ array index values =>
        addLiveSlots (addLiveSlots (exprUsedSlots array) (exprUsedSlots index))
          (exprListUsedSlots values)
    | .arrayPushSlots _ _ _ array values =>
        addLiveSlots (exprUsedSlots array) (exprListUsedSlots values)
    | .arrayPopSlots _ _ array => exprUsedSlots array
    | .arrayAppendSlots _ _ left right =>
        addLiveSlots (exprUsedSlots left) (exprUsedSlots right)
    | .arrayExtractSlots _ _ array start stop =>
        addLiveSlots (addLiveSlots (exprUsedSlots array) (exprUsedSlots start))
          (exprUsedSlots stop)
    | .arrayMapSlots sourceWidth _ _ _ array itemStart bodyValues =>
        let bodyLive := removeLiveSlots (exprListUsedSlots bodyValues)
          (slotsFrom itemStart sourceWidth)
        addLiveSlots (exprUsedSlots array) bodyLive
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyLets bodyDone _ =>
        let bodyLive := addLiveSlots (exprListUsedSlots bodyValues) (exprUsedSlots bodyDone)
        let bodyFree := removeLiveSlots
          (removeLiveSlots (pruneLocalLetsWithLive bodyLets bodyLive).snd
            (slotsFrom accStart resultWidth))
          (slotsFrom itemStart sourceWidth)
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprUsedSlots array) (exprUsedSlots start))
            (exprUsedSlots stop))
          (addLiveSlots (exprListUsedSlots initValues) bodyFree)
    | .arrayFindIdxSlots sourceWidth array itemStart predicate _ =>
        let predicateFree := removeLiveSlots (exprUsedSlots predicate)
          (slotsFrom itemStart sourceWidth)
        addLiveSlots (exprUsedSlots array) predicateFree
    | .arrayFindSlot sourceWidth array itemStart predicate _ =>
        let predicateFree := removeLiveSlots (exprUsedSlots predicate)
          (slotsFrom itemStart sourceWidth)
        addLiveSlots (exprUsedSlots array) predicateFree
    | .arrayEqSlots width left right leftStart rightStart predicate =>
        let predicateFree :=
          removeLiveSlots
            (removeLiveSlots (exprUsedSlots predicate) (slotsFrom leftStart width))
            (slotsFrom rightStart width)
        addLiveSlots (addLiveSlots (exprUsedSlots left) (exprUsedSlots right))
          predicateFree
    | .arrayAnySlots sourceWidth array start stop itemStart predicate _ =>
        let predicateFree := removeLiveSlots (exprUsedSlots predicate)
          (slotsFrom itemStart sourceWidth)
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprUsedSlots array) (exprUsedSlots start))
            (exprUsedSlots stop))
          predicateFree
    | .arrayFilterSlots sourceWidth _ array start stop itemStart predicate =>
        let predicateFree := removeLiveSlots (exprUsedSlots predicate)
          (slotsFrom itemStart sourceWidth)
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprUsedSlots array) (exprUsedSlots start))
            (exprUsedSlots stop))
          predicateFree
    | .arrayInsertIfInBoundsSlots _ _ _ array index values =>
        addLiveSlots (addLiveSlots (exprUsedSlots array) (exprUsedSlots index))
          (exprListUsedSlots values)
    | .arrayEraseIfInBoundsSlots _ _ array index =>
        addLiveSlots (exprUsedSlots array) (exprUsedSlots index)
    | .arraySwapIfInBoundsSlots _ _ array left right =>
        addLiveSlots (addLiveSlots (exprUsedSlots array) (exprUsedSlots left))
          (exprUsedSlots right)
    | .arrayReverseSlots _ _ array => exprUsedSlots array
    | .byteArrayGet ptr len index =>
        addLiveSlots (addLiveSlots (exprUsedSlots ptr) (exprUsedSlots len))
          (exprUsedSlots index)
    | .byteArrayPushPtr ptr len value =>
        addLiveSlots (addLiveSlots (exprUsedSlots ptr) (exprUsedSlots len))
          (exprUsedSlots value)
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        addLiveSlots
          (addLiveSlots (addLiveSlots (exprUsedSlots leftPtr) (exprUsedSlots leftLen))
            (exprUsedSlots rightPtr))
          (exprUsedSlots rightLen)
    | .byteArraySetPtr ptr len index value =>
        addLiveSlots
          (addLiveSlots (addLiveSlots (exprUsedSlots ptr) (exprUsedSlots len))
            (exprUsedSlots index))
          (exprUsedSlots value)
    | .byteArrayFromArrayPtr array => exprUsedSlots array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots
              (addLiveSlots
                (addLiveSlots
                  (addLiveSlots (exprUsedSlots srcPtr) (exprUsedSlots srcLen))
                  (exprUsedSlots srcOff))
                (exprUsedSlots destPtr))
              (exprUsedSlots destLen))
            (exprUsedSlots destOff))
          (exprUsedSlots copyLen)
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        addLiveSlots
          (addLiveSlots (addLiveSlots (exprUsedSlots leftPtr) (exprUsedSlots leftLen))
            (exprUsedSlots rightPtr))
          (exprUsedSlots rightLen)
    | .byteArrayFindIdx ptr len start byteSlot predicate _ =>
        addLiveSlots
          (addLiveSlots (addLiveSlots (exprUsedSlots ptr) (exprUsedSlots len))
            (exprUsedSlots start))
          (removeLiveSlot (exprUsedSlots predicate) byteSlot)
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone _ =>
        let bodyLive := addLiveSlots (exprListUsedSlots bodyValues) (exprUsedSlots bodyDone)
        let bodyFree := removeLiveSlot
          (removeLiveSlots (pruneLocalLetsWithLive bodyLets bodyLive).snd
            (slotsFrom accStart resultWidth))
          byteSlot
        addLiveSlots
          (addLiveSlots
            (addLiveSlots
              (addLiveSlots (exprUsedSlots ptr) (exprUsedSlots len))
              (exprUsedSlots start))
            (exprUsedSlots stop))
          (addLiveSlots (exprListUsedSlots initValues) bodyFree)
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyLets bodyDone _ =>
        let bodyLive := addLiveSlots (exprListUsedSlots bodyValues) (exprUsedSlots bodyDone)
        let bodyFree := removeLiveSlot
          (removeLiveSlots (pruneLocalLetsWithLive bodyLets bodyLive).snd
            (slotsFrom accStart resultWidth))
          itemSlot
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprUsedSlots start) (exprUsedSlots stop))
            (exprUsedSlots step))
          (addLiveSlots (exprListUsedSlots initValues) bodyFree)
    | .heapLinearPredicate ptr _ fieldSlotCount _ fieldStart predicate _ _ =>
        addLiveSlots (exprUsedSlots ptr)
          (removeLiveSlots (exprUsedSlots predicate) (slotsFrom fieldStart fieldSlotCount))
    | .call _ args => exprListUsedSlots args

  partial def condUsedSlots : IRCond → List Nat
    | .true => []
    | .false => []
    | .eqU64 left right =>
        addLiveSlots (exprUsedSlots left) (exprUsedSlots right)
    | .ltU64 left right =>
        addLiveSlots (exprUsedSlots left) (exprUsedSlots right)
    | .leU64 left right =>
        addLiveSlots (exprUsedSlots left) (exprUsedSlots right)
    | .not cond => condUsedSlots cond
    | .and left right =>
        addLiveSlots (condUsedSlots left) (condUsedSlots right)
    | .or left right =>
        addLiveSlots (condUsedSlots left) (condUsedSlots right)

  partial def exprListUsedSlots (exprs : List IRExpr) : List Nat :=
    exprs.foldl (fun live expr => addLiveSlots live (exprUsedSlots expr)) []

  partial def valueUsedSlots : ExtractedValue → List Nat
    | .scalar expr => exprUsedSlots expr
    | .array owner ptr => addLiveSlots (exprUsedSlots owner) (exprUsedSlots ptr)
    | .byteArray owner ptr len =>
        addLiveSlots (exprUsedSlots owner) (addLiveSlots (exprUsedSlots ptr) (exprUsedSlots len))
    | .product left right =>
        addLiveSlots (valueUsedSlots left) (valueUsedSlots right)
    | .sum tag left right =>
        addLiveSlots (addLiveSlots (exprUsedSlots tag) (valueUsedSlots left))
          (valueUsedSlots right)
    | .struct _ fields =>
        fields.foldl (fun live field => addLiveSlots live (valueUsedSlots field)) []
    | .variant _ tag ctors =>
        ctors.foldl
          (fun live fields =>
            fields.foldl (fun acc field => addLiveSlots acc (valueUsedSlots field)) live)
          (exprUsedSlots tag)
    | .recursiveVariant _ tag ctors =>
        ctors.foldl
          (fun live fields =>
            fields.foldl (fun acc field => addLiveSlots acc (valueUsedSlots field.snd)) live)
          (exprUsedSlots tag)
    | .heapVariant _ ptr => exprUsedSlots ptr
    | .ite cond thenValue elseValue =>
        addLiveSlots (addLiveSlots (condUsedSlots cond) (valueUsedSlots thenValue))
          (valueUsedSlots elseValue)
    | .letE slot value body =>
        let bodyLive := valueUsedSlots body
        if bodyLive.contains slot then
          addLiveSlots (removeLiveSlot bodyLive slot) (exprUsedSlots value)
        else
          bodyLive
    | .letCall slots _ args body =>
        let bodyLive := valueUsedSlots body
        if anyLiveSlot bodyLive slots then
          addLiveSlots (removeLiveSlots bodyLive slots) (exprListUsedSlots args)
        else
          bodyLive
    | .letLocal lets body =>
        (pruneLocalLetsWithLive lets (valueUsedSlots body)).snd

  partial def pruneLocalLetWithLive (localLet : LeanExe.IR.LocalLet) (liveAfter : List Nat) :
      Option LeanExe.IR.LocalLet × List Nat :=
    match localLet with
    | .expr slot value =>
        if liveAfter.contains slot then
          (some (.expr slot value), addLiveSlots (removeLiveSlot liveAfter slot)
            (exprUsedSlots value))
        else
          (none, liveAfter)
    | .call slots index args =>
        if anyLiveSlot liveAfter slots then
          (some (.call slots index args), addLiveSlots (removeLiveSlots liveAfter slots)
            (exprListUsedSlots args))
        else
          (none, liveAfter)
    | .slots slots values =>
        let kept := (slots.zip values).filter fun item => liveAfter.contains item.fst
        if kept.isEmpty then
          (none, liveAfter)
        else
          let keptSlots := kept.map Prod.fst
          let keptValues := kept.map Prod.snd
          (some (.slots keptSlots keptValues),
            addLiveSlots (removeLiveSlots liveAfter keptSlots) (exprListUsedSlots keptValues))
    | .branch cond thenLets elseLets =>
        let thenResult := pruneLocalLetsWithLive thenLets liveAfter
        let elseResult := pruneLocalLetsWithLive elseLets liveAfter
        if thenResult.fst.isEmpty && elseResult.fst.isEmpty then
          (none, liveAfter)
        else
          let branchLive := addLiveSlots (addLiveSlots thenResult.snd elseResult.snd)
            (condUsedSlots cond)
          (some (.branch cond thenResult.fst elseResult.fst), branchLive)

  partial def pruneLocalLetsWithLive : List LeanExe.IR.LocalLet → List Nat →
      List LeanExe.IR.LocalLet × List Nat
    | [], liveAfter => ([], liveAfter)
    | localLet :: rest, liveAfter =>
        let restResult := pruneLocalLetsWithLive rest liveAfter
        let itemResult := pruneLocalLetWithLive localLet restResult.snd
        match itemResult.fst with
        | some kept => (kept :: restResult.fst, itemResult.snd)
        | none => (restResult.fst, itemResult.snd)
end

def pruneLocalLets (lets : List LeanExe.IR.LocalLet) (liveAfter : List Nat) :
    List LeanExe.IR.LocalLet :=
  (pruneLocalLetsWithLive lets liveAfter).fst

def wrapValueLocalLets (lets : List LeanExe.IR.LocalLet) (value : ExtractedValue) :
    ExtractedValue :=
  let kept := pruneLocalLets lets (valueUsedSlots value)
  if kept.isEmpty then
    value
  else
    .letLocal kept value

def wrapExprLocalLets (lets : List LeanExe.IR.LocalLet) (expr : IRExpr) : IRExpr :=
  let kept := pruneLocalLets lets (exprUsedSlots expr)
  if kept.isEmpty then
    expr
  else
    .letLets kept expr

def scalarValue (value : ExtractedValue) : Except String IRExpr :=
  match value with
  | .scalar expr => .ok expr
  | .array _ ptr => .ok ptr
  | .byteArray _ _ _ => .error "ByteArray value used where scalar value is required"
  | .product _ _ => .error "product value used where scalar value is required"
  | .sum _ _ _ => .error "sum value used where scalar value is required"
  | .struct name _ => .error s!"structure value used where scalar value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where scalar value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where scalar value is required: {name}"
  | .heapVariant name _ => .error s!"recursive inductive value used where scalar value is required: {name}"
  | .ite cond thenValue elseValue => do
      .ok (.ite cond (← scalarValue thenValue) (← scalarValue elseValue))
  | .letE slot value body => do
      .ok (.letE slot value (← scalarValue body))
  | .letCall slots index args body => do
      .ok (.letCall slots index args (← scalarValue body))
  | .letLocal lets body => do
      .ok (wrapExprLocalLets lets (← scalarValue body))

structure ByteArraySlots where
  owner : IRExpr
  ptr : IRExpr
  len : IRExpr
  deriving BEq, Repr

partial def byteArrayFullParts (value : ExtractedValue) :
    Except String ByteArraySlots :=
  match value with
  | .byteArray owner ptr len => .ok { owner, ptr, len }
  | .scalar _ => .error "scalar value used where ByteArray value is required"
  | .array _ _ => .error "array value used where ByteArray value is required"
  | .product _ _ => .error "product value used where ByteArray value is required"
  | .sum _ _ _ => .error "sum value used where ByteArray value is required"
  | .struct name _ => .error s!"structure value used where ByteArray value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where ByteArray value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← byteArrayFullParts thenValue
      let elseParts ← byteArrayFullParts elseValue
      .ok {
        owner := .ite cond thenParts.owner elseParts.owner,
        ptr := .ite cond thenParts.ptr elseParts.ptr,
        len := .ite cond thenParts.len elseParts.len
      }
  | .letE slot value body => do
      let parts ← byteArrayFullParts body
      .ok {
        owner := .letE slot value parts.owner,
        ptr := .letE slot value parts.ptr,
        len := .letE slot value parts.len
      }
  | .letCall slots index args body => do
      let parts ← byteArrayFullParts body
      .ok {
        owner := .letCall slots index args parts.owner,
        ptr := .letCall slots index args parts.ptr,
        len := .letCall slots index args parts.len
      }
  | .letLocal lets body => do
      let parts ← byteArrayFullParts body
      .ok {
        owner := wrapExprLocalLets lets parts.owner,
        ptr := wrapExprLocalLets lets parts.ptr,
        len := wrapExprLocalLets lets parts.len
      }

def byteArrayParts (value : ExtractedValue) : Except String (IRExpr × IRExpr) := do
  let parts ← byteArrayFullParts value
  .ok (parts.ptr, parts.len)

partial def byteArrayFullPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × ByteArraySlots) :=
  match value with
  | .byteArray owner ptr len => .ok ([], { owner, ptr, len })
  | .scalar _ => .error "scalar value used where ByteArray value is required"
  | .array _ _ => .error "array value used where ByteArray value is required"
  | .product _ _ => .error "product value used where ByteArray value is required"
  | .sum _ _ _ => .error "sum value used where ByteArray value is required"
  | .struct name _ => .error s!"structure value used where ByteArray value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where ByteArray value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where ByteArray value is required: {name}"
  | .ite cond thenValue elseValue => do
      let parts ← byteArrayFullParts (.ite cond thenValue elseValue)
      .ok ([], parts)
  | .letE slot value body => do
      let parts ← byteArrayFullPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd)
  | .letCall slots index args body => do
      let parts ← byteArrayFullPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd)
  | .letLocal lets body => do
      let parts ← byteArrayFullParts body
      .ok ([], {
        owner := wrapExprLocalLets lets parts.owner,
        ptr := wrapExprLocalLets lets parts.ptr,
        len := wrapExprLocalLets lets parts.len
      })

partial def byteArrayPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × IRExpr) := do
  let parts ← byteArrayFullPartsWithLets value
  .ok (parts.fst, parts.snd.ptr, parts.snd.len)

structure ArraySlots where
  owner : IRExpr
  ptr : IRExpr
  deriving BEq, Repr

partial def arrayFullParts (value : ExtractedValue) :
    Except String ArraySlots :=
  match value with
  | .array owner ptr => .ok { owner, ptr }
  | .scalar _ => .error "scalar value used where array value is required"
  | .byteArray _ _ _ => .error "ByteArray value used where array value is required"
  | .product _ _ => .error "product value used where array value is required"
  | .sum _ _ _ => .error "sum value used where array value is required"
  | .struct name _ => .error s!"structure value used where array value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where array value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where array value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where array value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← arrayFullParts thenValue
      let elseParts ← arrayFullParts elseValue
      .ok {
        owner := .ite cond thenParts.owner elseParts.owner,
        ptr := .ite cond thenParts.ptr elseParts.ptr
      }
  | .letE slot value body => do
      let parts ← arrayFullParts body
      .ok {
        owner := .letE slot value parts.owner,
        ptr := .letE slot value parts.ptr
      }
  | .letCall slots index args body => do
      let parts ← arrayFullParts body
      .ok {
        owner := .letCall slots index args parts.owner,
        ptr := .letCall slots index args parts.ptr
      }
  | .letLocal lets body => do
      let parts ← arrayFullParts body
      .ok {
        owner := wrapExprLocalLets lets parts.owner,
        ptr := wrapExprLocalLets lets parts.ptr
      }

partial def arrayFullPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × ArraySlots) :=
  match value with
  | .array owner ptr => .ok ([], { owner, ptr })
  | .scalar _ => .error "scalar value used where array value is required"
  | .byteArray _ _ _ => .error "ByteArray value used where array value is required"
  | .product _ _ => .error "product value used where array value is required"
  | .sum _ _ _ => .error "sum value used where array value is required"
  | .struct name _ => .error s!"structure value used where array value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where array value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where array value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where array value is required: {name}"
  | .ite cond thenValue elseValue => do
      let parts ← arrayFullParts (.ite cond thenValue elseValue)
      .ok ([], parts)
  | .letE slot value body => do
      let parts ← arrayFullPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd)
  | .letCall slots index args body => do
      let parts ← arrayFullPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd)
  | .letLocal lets body => do
      let parts ← arrayFullParts body
      .ok ([], {
        owner := wrapExprLocalLets lets parts.owner,
        ptr := wrapExprLocalLets lets parts.ptr
      })

def arrayPtr (value : ExtractedValue) : Except String IRExpr := do
  let parts ← arrayFullParts value
  .ok parts.ptr

def ownedArrayValue (slot : Nat) (ptr : IRExpr) : ExtractedValue :=
  .letE slot ptr (.array (.local slot) (.local slot))

def conditionalArrayOwnerValue
    (slot : Nat)
    (ptr : IRExpr)
    (takesOwnership : IRCond)
    (borrowedOwner : IRExpr) :
    ExtractedValue :=
  .letE slot ptr (.array (.ite takesOwnership (.local slot) borrowedOwner) (.local slot))

def productField (index : Nat) (value : ExtractedValue) : Except String ExtractedValue :=
  match value with
  | .product left right =>
      if index == 0 then
        .ok left
      else if index == 1 then
        .ok right
      else
        .error s!"unsupported product projection index: {index}"
  | .scalar _ => .error "scalar value used where product value is required"
  | .array _ _ => .error "array value used where product value is required"
  | .byteArray _ _ _ => .error "ByteArray value used where product value is required"
  | .sum _ _ _ => .error "sum value used where product value is required"
  | .struct name _ => .error s!"structure value used where product value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where product value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where product value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where product value is required: {name}"
  | .ite cond thenValue elseValue => do
      .ok (.ite cond (← productField index thenValue) (← productField index elseValue))
  | .letE slot value body => do
      .ok (.letE slot value (← productField index body))
  | .letCall slots callIndex args body => do
      .ok (.letCall slots callIndex args (← productField index body))
  | .letLocal lets body => do
      .ok (wrapValueLocalLets lets (← productField index body))

def structField (name : Name) (index : Nat) (value : ExtractedValue) : Except String ExtractedValue :=
  match value with
  | .struct actual fields =>
      if actual == name then
        match fields[index]? with
        | some field => .ok field
        | none => .error s!"unsupported structure projection index: {name}.{index}"
      else
        .error s!"structure projection type mismatch: expected {name}, got {actual}"
  | .scalar _ => .error s!"scalar value used where structure value is required: {name}"
  | .array _ _ => .error s!"array value used where structure value is required: {name}"
  | .byteArray _ _ _ => .error s!"ByteArray value used where structure value is required: {name}"
  | .product _ _ => .error s!"product value used where structure value is required: {name}"
  | .sum _ _ _ => .error s!"sum value used where structure value is required: {name}"
  | .variant actual _ _ =>
      .error s!"inductive value used where structure value is required: {name}; got {actual}"
  | .recursiveVariant actual _ _ =>
      .error s!"recursive inductive value used where structure value is required: {name}; got {actual}"
  | .heapVariant actual _ =>
      .error s!"recursive inductive value used where structure value is required: {name}; got {actual}"
  | .ite cond thenValue elseValue => do
      .ok (.ite cond (← structField name index thenValue) (← structField name index elseValue))
  | .letE slot value body => do
      .ok (.letE slot value (← structField name index body))
  | .letCall slots callIndex args body => do
      .ok (.letCall slots callIndex args (← structField name index body))
  | .letLocal lets body => do
      .ok (wrapValueLocalLets lets (← structField name index body))

def mkOptionValue (tag : IRExpr) (payload : ExtractedValue) : ExtractedValue :=
  .variant ``Option tag [[], [payload]]

def optionPayloadType? : Ty → Option Ty
  | .variant name _ [[], [payloadTy]] => if name == ``Option then some payloadTy else none
  | _ => none

partial def wrapValueLets (lets : List ValueLet) (value : ExtractedValue) :
    ExtractedValue :=
  lets.foldr
    (fun item acc =>
      match item with
      | .expr slot expr => .letE slot expr acc
      | .call slots index args => .letCall slots index args acc)
    value

def wrapExprLets (lets : List ValueLet) (expr : IRExpr) : IRExpr :=
  lets.foldr
    (fun item acc =>
      match item with
      | .expr slot value => .letE slot value acc
      | .call slots index args => .letCall slots index args acc)
    expr

def valueLetStmt : ValueLet → IRStmt
  | .expr slot expr => .assign slot expr
  | .call slots index args => .call slots index args

partial def optionPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × ExtractedValue) :=
  match value with
  | .variant name tag [[], [payload]] =>
      if name == ``Option then
        .ok ([], tag, payload)
      else
        .error s!"inductive value used where Option value is required: {name}"
  | .scalar _ => .error "scalar value used where option value is required"
  | .array _ _ => .error "array value used where option value is required"
  | .byteArray _ _ _ => .error "ByteArray value used where option value is required"
  | .product _ _ => .error "product value used where option value is required"
  | .sum _ _ _ => .error "sum value used where option value is required"
  | .struct name _ => .error s!"structure value used where option value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where Option value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where Option value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where Option value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← optionPartsWithLets thenValue
      let elseParts ← optionPartsWithLets elseValue
      let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
      let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
      let payload :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd)
          (wrapValueLets elseParts.fst elseParts.snd.snd)
      .ok ([], .ite cond thenTag elseTag, payload)
  | .letE slot value body => do
      let parts ← optionPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letCall slots index args body => do
      let parts ← optionPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letLocal lets body => do
      let parts ← optionPartsWithLets body
      .ok ([],
        wrapExprLocalLets lets (wrapExprLets parts.fst parts.snd.fst),
        wrapValueLocalLets lets (wrapValueLets parts.fst parts.snd.snd))

partial def sumPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × ExtractedValue × ExtractedValue) :=
  match value with
  | .sum tag left right => .ok ([], tag, left, right)
  | .scalar _ => .error "scalar value used where sum value is required"
  | .array _ _ => .error "array value used where sum value is required"
  | .byteArray _ _ _ => .error "ByteArray value used where sum value is required"
  | .product _ _ => .error "product value used where sum value is required"
  | .struct name _ => .error s!"structure value used where sum value is required: {name}"
  | .variant name _ _ => .error s!"inductive value used where sum value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where sum value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where sum value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← sumPartsWithLets thenValue
      let elseParts ← sumPartsWithLets elseValue
      let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
      let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
      let left :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.fst)
          (wrapValueLets elseParts.fst elseParts.snd.snd.fst)
      let right :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.snd)
          (wrapValueLets elseParts.fst elseParts.snd.snd.snd)
      .ok ([], .ite cond thenTag elseTag, left, right)
  | .letE slot value body => do
      let parts ← sumPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)
  | .letCall slots index args body => do
      let parts ← sumPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)
  | .letLocal lets body => do
      let parts ← sumPartsWithLets body
      .ok ([],
        wrapExprLocalLets lets (wrapExprLets parts.fst parts.snd.fst),
        wrapValueLocalLets lets (wrapValueLets parts.fst parts.snd.snd.fst),
        wrapValueLocalLets lets (wrapValueLets parts.fst parts.snd.snd.snd))

partial def variantPartsWithLets (expectedName : Name) (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × List (List ExtractedValue)) :=
  match value with
  | .variant name tag ctors =>
      if name == expectedName then
        .ok ([], tag, ctors)
      else
        .error s!"inductive value type mismatch: expected {expectedName}, got {name}"
  | .scalar _ => .error s!"scalar value used where inductive value is required: {expectedName}"
  | .array _ _ => .error s!"array value used where inductive value is required: {expectedName}"
  | .byteArray _ _ _ =>
      .error s!"ByteArray value used where inductive value is required: {expectedName}"
  | .product _ _ => .error s!"product value used where inductive value is required: {expectedName}"
  | .sum _ _ _ => .error s!"sum value used where inductive value is required: {expectedName}"
  | .struct name _ =>
      .error s!"structure value used where inductive value is required: {expectedName}; got {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where nonrecursive inductive value is required: {expectedName}; got {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where nonrecursive inductive value is required: {expectedName}; got {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← variantPartsWithLets expectedName thenValue
      let elseParts ← variantPartsWithLets expectedName elseValue
      if thenParts.snd.snd.length == elseParts.snd.snd.length then do
        let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
        let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
        let ctors ← (thenParts.snd.snd.zip elseParts.snd.snd).mapM fun ctorPair =>
          if ctorPair.fst.length == ctorPair.snd.length then
            .ok <| ctorPair.fst.zip ctorPair.snd |>.map fun fieldPair =>
              .ite cond
                (wrapValueLets thenParts.fst fieldPair.fst)
                (wrapValueLets elseParts.fst fieldPair.snd)
          else
            .error s!"conditional inductive constructor payload shape mismatch: {expectedName}"
        .ok ([], .ite cond thenTag elseTag, ctors)
      else
        .error s!"conditional inductive value shape mismatch: {expectedName}"
  | .letE slot value body => do
      let parts ← variantPartsWithLets expectedName body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letCall slots index args body => do
      let parts ← variantPartsWithLets expectedName body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letLocal lets body => do
      let parts ← variantPartsWithLets expectedName body
      .ok ([],
        wrapExprLocalLets lets (wrapExprLets parts.fst parts.snd.fst),
        parts.snd.snd.map fun fields =>
          fields.map fun field => wrapValueLocalLets lets (wrapValueLets parts.fst field))

partial def heapVariantPtrWithLets (expectedName : Name) (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr) :=
  match value with
  | .heapVariant name ptr =>
      if name == expectedName then
        .ok ([], ptr)
      else
        .error s!"recursive inductive value type mismatch: expected {expectedName}, got {name}"
  | .scalar _ =>
      .error s!"scalar value used where recursive inductive value is required: {expectedName}"
  | .array _ _ =>
      .error s!"array value used where recursive inductive value is required: {expectedName}"
  | .byteArray _ _ _ =>
      .error s!"ByteArray value used where recursive inductive value is required: {expectedName}"
  | .product _ _ =>
      .error s!"product value used where recursive inductive value is required: {expectedName}"
  | .sum _ _ _ =>
      .error s!"sum value used where recursive inductive value is required: {expectedName}"
  | .struct name _ =>
      .error s!"structure value used where recursive inductive value is required: {expectedName}; got {name}"
  | .variant name _ _ =>
      .error s!"nonrecursive inductive value used where recursive inductive value is required: {expectedName}; got {name}"
  | .recursiveVariant name _ _ =>
      .error s!"lazy recursive inductive value used where heap recursive value is required: {expectedName}; got {name}"
  | .ite _ _ _ =>
      .error s!"conditional recursive heap value is unsupported: {expectedName}"
  | .letE slot value body => do
      let parts ← heapVariantPtrWithLets expectedName body
      .ok (.expr slot value :: parts.fst, parts.snd)
  | .letCall slots index args body => do
      let parts ← heapVariantPtrWithLets expectedName body
      .ok (.call slots index args :: parts.fst, parts.snd)
  | .letLocal lets body => do
      let parts ← heapVariantPtrWithLets expectedName body
      .ok ([], wrapExprLocalLets lets (wrapExprLets parts.fst parts.snd))

partial def heapVariantPtrWithLets? (expectedName : Name) (value : ExtractedValue) :
    Option (List ValueLet × IRExpr) :=
  match value with
  | .heapVariant name ptr =>
      if name == expectedName then some ([], ptr) else none
  | .letE slot value body =>
      heapVariantPtrWithLets? expectedName body |>.map fun parts =>
        (.expr slot value :: parts.fst, parts.snd)
  | .letCall slots index args body =>
      heapVariantPtrWithLets? expectedName body |>.map fun parts =>
        (.call slots index args :: parts.fst, parts.snd)
  | .letLocal lets body =>
      heapVariantPtrWithLets? expectedName body |>.map fun parts =>
        ([], wrapExprLocalLets lets (wrapExprLets parts.fst parts.snd))
  | _ => none

partial def recursiveVariantPartsWithLets (expectedName : Name) (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × List (List ExtractedValue)) :=
  match value with
  | .recursiveVariant name tag ctors =>
      if name == expectedName then
        .ok ([], tag, ctors.map (fun fields => fields.map Prod.snd))
      else
        .error s!"recursive inductive value type mismatch: expected {expectedName}, got {name}"
  | .scalar _ =>
      .error s!"scalar value used where recursive inductive value is required: {expectedName}"
  | .array _ _ =>
      .error s!"array value used where recursive inductive value is required: {expectedName}"
  | .byteArray _ _ _ =>
      .error s!"ByteArray value used where recursive inductive value is required: {expectedName}"
  | .product _ _ =>
      .error s!"product value used where recursive inductive value is required: {expectedName}"
  | .sum _ _ _ =>
      .error s!"sum value used where recursive inductive value is required: {expectedName}"
  | .struct name _ =>
      .error s!"structure value used where recursive inductive value is required: {expectedName}; got {name}"
  | .variant name _ _ =>
      .error s!"nonrecursive inductive value used where recursive inductive value is required: {expectedName}; got {name}"
  | .heapVariant name _ =>
      .error s!"heap recursive inductive value used where lazy recursive value is required: {expectedName}; got {name}"
  | .ite _ _ _ =>
      .error s!"conditional recursive inductive value is unsupported: {expectedName}"
  | .letE slot value body => do
      let parts ← recursiveVariantPartsWithLets expectedName body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letCall slots index args body => do
      let parts ← recursiveVariantPartsWithLets expectedName body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd)
  | .letLocal lets body => do
      let parts ← recursiveVariantPartsWithLets expectedName body
      .ok ([],
        wrapExprLocalLets lets (wrapExprLets parts.fst parts.snd.fst),
        parts.snd.snd.map fun fields =>
          fields.map fun field => wrapValueLocalLets lets (wrapValueLets parts.fst field))

def mkExceptValue (tag : IRExpr) (errorPayload okPayload : ExtractedValue) : ExtractedValue :=
  .variant ``Except tag [[errorPayload], [okPayload]]

partial def exceptPartsWithLets (value : ExtractedValue) :
    Except String (List ValueLet × IRExpr × ExtractedValue × ExtractedValue) :=
  match value with
  | .variant name tag [[errorPayload], [okPayload]] =>
      if name == ``Except then
        .ok ([], tag, errorPayload, okPayload)
      else
        .error s!"inductive value used where Except value is required: {name}"
  | .scalar _ => .error "scalar value used where Except value is required"
  | .array _ _ => .error "array value used where Except value is required"
  | .byteArray _ _ _ => .error "ByteArray value used where Except value is required"
  | .product _ _ => .error "product value used where Except value is required"
  | .sum _ _ _ => .error "sum value used where Except value is required"
  | .struct name _ => .error s!"structure value used where Except value is required: {name}"
  | .variant name _ _ =>
      .error s!"inductive value used where Except value is required: {name}"
  | .recursiveVariant name _ _ =>
      .error s!"recursive inductive value used where Except value is required: {name}"
  | .heapVariant name _ =>
      .error s!"recursive inductive value used where Except value is required: {name}"
  | .ite cond thenValue elseValue => do
      let thenParts ← exceptPartsWithLets thenValue
      let elseParts ← exceptPartsWithLets elseValue
      let thenTag := wrapExprLets thenParts.fst thenParts.snd.fst
      let elseTag := wrapExprLets elseParts.fst elseParts.snd.fst
      let errorPayload :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.fst)
          (wrapValueLets elseParts.fst elseParts.snd.snd.fst)
      let okPayload :=
        .ite cond
          (wrapValueLets thenParts.fst thenParts.snd.snd.snd)
          (wrapValueLets elseParts.fst elseParts.snd.snd.snd)
      .ok ([], .ite cond thenTag elseTag, errorPayload, okPayload)
  | .letE slot value body => do
      let parts ← exceptPartsWithLets body
      .ok (.expr slot value :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)
  | .letCall slots index args body => do
      let parts ← exceptPartsWithLets body
      .ok (.call slots index args :: parts.fst, parts.snd.fst, parts.snd.snd.fst, parts.snd.snd.snd)
  | .letLocal lets body => do
      let parts ← exceptPartsWithLets body
      .ok ([],
        wrapExprLocalLets lets (wrapExprLets parts.fst parts.snd.fst),
        wrapValueLocalLets lets (wrapValueLets parts.fst parts.snd.snd.fst),
        wrapValueLocalLets lets (wrapValueLets parts.fst parts.snd.snd.snd))

partial def defaultValue : Ty → Except String ExtractedValue
  | .unit => .ok (.scalar (.u64 0))
  | .bool => .ok (.scalar (.u64 0))
  | .u8 => .ok (.scalar (.u64 0))
  | .u32 => .ok (.scalar (.u64 0))
  | .u64 => .ok (.scalar (.u64 0))
  | .nat => .ok (.scalar (.u64 0))
  | .byteArray => .ok (.byteArray (.u64 0) (.u64 0) (.u64 0))
  | .array item =>
      if supportedArrayElementType item then
        .ok (.array (.u64 0) (.u64 0))
      else
        .error s!"unsupported default value type: {reprStr ((.array item : Ty))}"
  | .product left right => do
      .ok (.product (← defaultValue left) (← defaultValue right))
  | .struct name _ fields => do
      .ok (.struct name (← fields.mapM defaultValue))
  | .variant name _ ctors => do
      .ok (.variant name (.u64 0) (← ctors.mapM (fun fields => fields.mapM defaultValue)))
  | .recVariant name _ => .ok (.heapVariant name (.u64 0))
  | .sum left right => do
      .ok (.sum (.u64 0) (← defaultValue left) (← defaultValue right))

partial def trapValue : Ty → Except String ExtractedValue
  | .unit => .ok (.scalar .trap)
  | .bool => .ok (.scalar .trap)
  | .u8 => .ok (.scalar .trap)
  | .u32 => .ok (.scalar .trap)
  | .u64 => .ok (.scalar .trap)
  | .nat => .ok (.scalar .trap)
  | .byteArray => .ok (.byteArray .trap .trap .trap)
  | .array item =>
      if supportedArrayElementType item then
        .ok (.array .trap .trap)
      else
        .error s!"unsupported trap value type: {reprStr ((.array item : Ty))}"
  | .product left right => do
      .ok (.product (← trapValue left) (← trapValue right))
  | .struct name _ fields => do
      .ok (.struct name (← fields.mapM trapValue))
  | .variant name _ ctors => do
      .ok (.variant name .trap (← ctors.mapM (fun fields => fields.mapM trapValue)))
  | .recVariant name _ => .ok (.heapVariant name .trap)
  | .sum left right => do
      .ok (.sum .trap (← trapValue left) (← trapValue right))

def byteArrayCopySliceCopiedLen
    (srcLen srcOff copyLen : IRExpr) : IRExpr :=
  let available :=
    .ite
      (.ltU64 srcOff srcLen)
      (.u64Bin .sub srcLen srcOff)
      (.u64 0)
  .ite (.ltU64 copyLen available) copyLen available

def byteArrayCopySliceResultLen
    (srcLen srcOff destLen destOff copyLen : IRExpr) : IRExpr :=
  let copiedLen := byteArrayCopySliceCopiedLen srcLen srcOff copyLen
  let prefixLen := .ite (.ltU64 destOff destLen) destOff destLen
  let suffixStart := .u64Bin .add destOff copiedLen
  let suffixLen :=
    .ite
      (.ltU64 suffixStart destLen)
      (.u64Bin .sub destLen suffixStart)
      (.u64 0)
  .u64Bin .add (.u64Bin .add prefixLen copiedLen) suffixLen

def byteArrayLoadUInt64 (ptr len : IRExpr) (items : List (Nat × Nat)) : IRExpr :=
  items.foldl
    (fun acc item =>
      .u64Bin .bitOr acc
        (.u64Bin .shiftLeft (.byteArrayGet ptr len (.u64 item.fst)) (.u64 item.snd)))
    (.u64 0)

def byteArrayLoadUInt64Checked (ptr len : IRExpr) (items : List (Nat × Nat)) : IRExpr :=
  .ite
    (.eqU64 len (.u64 8))
    (byteArrayLoadUInt64 ptr len items)
    .trap

partial def valueIte
    (cond : IRCond)
    (thenValue elseValue : ExtractedValue) :
    Except String ExtractedValue :=
  match thenValue, elseValue with
  | .letE _ _ _, _ => .ok (.ite cond thenValue elseValue)
  | _, .letE _ _ _ => .ok (.ite cond thenValue elseValue)
  | .letCall _ _ _ _, _ => .ok (.ite cond thenValue elseValue)
  | _, .letCall _ _ _ _ => .ok (.ite cond thenValue elseValue)
  | .letLocal _ _, _ => .ok (.ite cond thenValue elseValue)
  | _, .letLocal _ _ => .ok (.ite cond thenValue elseValue)
  | .ite _ _ _, _ => .ok (.ite cond thenValue elseValue)
  | _, .ite _ _ _ => .ok (.ite cond thenValue elseValue)
  | .scalar thenExpr, .scalar elseExpr => .ok (.scalar (.ite cond thenExpr elseExpr))
  | .array thenOwner thenPtr, .array elseOwner elsePtr =>
      .ok (.array (.ite cond thenOwner elseOwner) (.ite cond thenPtr elsePtr))
  | .byteArray thenOwner thenPtr thenLen, .byteArray elseOwner elsePtr elseLen =>
      .ok (.byteArray
        (.ite cond thenOwner elseOwner)
        (.ite cond thenPtr elsePtr)
        (.ite cond thenLen elseLen))
  | .product thenLeft thenRight, .product elseLeft elseRight => do
      .ok (.product
        (← valueIte cond thenLeft elseLeft)
        (← valueIte cond thenRight elseRight))
  | .sum thenTag thenLeft thenRight, .sum elseTag elseLeft elseRight => do
      .ok (.sum
        (.ite cond thenTag elseTag)
        (← valueIte cond thenLeft elseLeft)
        (← valueIte cond thenRight elseRight))
  | .struct thenName thenFields, .struct elseName elseFields =>
      if thenName == elseName && thenFields.length == elseFields.length then do
        let fields ← (thenFields.zip elseFields).mapM fun item =>
          valueIte cond item.fst item.snd
        .ok (.struct thenName fields)
      else
        .error "if branches have incompatible structure value shapes"
  | .variant thenName thenTag thenCtors, .variant elseName elseTag elseCtors =>
      if thenName == elseName && thenCtors.length == elseCtors.length then do
        let ctors ← (thenCtors.zip elseCtors).mapM fun ctorPair =>
          if ctorPair.fst.length == ctorPair.snd.length then
            ctorPair.fst.zip ctorPair.snd |>.mapM fun fieldPair =>
              valueIte cond fieldPair.fst fieldPair.snd
          else
            .error "if branches have incompatible inductive constructor payload shapes"
        .ok (.variant thenName (.ite cond thenTag elseTag) ctors)
      else
        .error "if branches have incompatible inductive value shapes"
  | .heapVariant thenName thenPtr, .heapVariant elseName elsePtr =>
      if thenName == elseName then
        .ok (.heapVariant thenName (.ite cond thenPtr elsePtr))
      else
        .error "if branches have incompatible recursive inductive value shapes"
  | .heapVariant heapName _, .recursiveVariant recursiveName _ _ =>
      if heapName == recursiveName then
        .ok (.ite cond thenValue elseValue)
      else
        .error "if branches have incompatible recursive inductive value shapes"
  | .recursiveVariant recursiveName _ _, .heapVariant heapName _ =>
      if recursiveName == heapName then
        .ok (.ite cond thenValue elseValue)
      else
        .error "if branches have incompatible recursive inductive value shapes"
  | .recursiveVariant thenName _thenTag thenCtors,
      .recursiveVariant elseName _elseTag elseCtors =>
      if thenName == elseName && thenCtors.length == elseCtors.length then
        .ok (.ite cond thenValue elseValue)
      else
        .error "if branches have incompatible recursive inductive value shapes"
  | _, _ => .error "if branches have incompatible structured value shapes"

def combineIteSlots (cond : IRCond) (thenSlots elseSlots : List IRExpr) :
    Except String (List IRExpr) :=
  if thenSlots.length == elseSlots.length then
    .ok <| thenSlots.zip elseSlots |>.map fun item => .ite cond item.fst item.snd
  else
    .error "conditional flattened value shape mismatch"

mutual
  partial def heapChildMaskFromType (slot : Nat) : Ty → Nat × Nat
    | .recVariant _ _ => (2 ^ slot, slot + 1)
    | .product left right =>
        let leftResult := heapChildMaskFromType slot left
        let rightResult := heapChildMaskFromType leftResult.snd right
        (leftResult.fst + rightResult.fst, rightResult.snd)
    | .sum left right =>
        let leftResult := heapChildMaskFromType (slot + 1) left
        let rightResult := heapChildMaskFromType leftResult.snd right
        (leftResult.fst + rightResult.fst, rightResult.snd)
    | .struct _ _ fields => heapChildMaskFromTypes slot fields
    | .variant _ _ ctors => heapChildMaskFromTypes (slot + 1) ctors.flatten
    | .byteArray => (2 ^ slot, slot + 3)
    | .array _ => (2 ^ slot, slot + 2)
    | .unit => (0, slot + 1)
    | .bool => (0, slot + 1)
    | .u8 => (0, slot + 1)
    | .u32 => (0, slot + 1)
    | .u64 => (0, slot + 1)
    | .nat => (0, slot + 1)

  partial def heapChildMaskFromTypes : Nat → List Ty → Nat × Nat
    | slot, [] => (0, slot)
    | slot, ty :: rest =>
        let head := heapChildMaskFromType slot ty
        let tail := heapChildMaskFromTypes head.snd rest
        (head.fst + tail.fst, tail.snd)
end

def heapChildMaskForCtors (ctors : List (List (Ty × ExtractedValue))) : Nat :=
  (heapChildMaskFromTypes 1 (ctors.flatten.map Prod.fst)).fst

def maskBitSet (mask slot : Nat) : Bool :=
  (mask / (2 ^ slot)) % 2 == 1

def arrayElementChildMask (ty : Ty) : Nat :=
  (heapChildMaskFromType 0 ty).fst

partial def flattenInternalValue (ty : Ty) (value : ExtractedValue) :
    Except String (List IRExpr) :=
  match ty with
  | .unit => scalarValue value |>.map (fun expr => [expr])
  | .bool => scalarValue value |>.map (fun expr => [expr])
  | .u8 => scalarValue value |>.map (fun expr => [expr])
  | .u32 => scalarValue value |>.map (fun expr => [expr])
  | .u64 => scalarValue value |>.map (fun expr => [expr])
  | .nat => scalarValue value |>.map (fun expr => [expr])
  | .byteArray => do
      let parts ← byteArrayFullParts value
      .ok [parts.owner, parts.ptr, parts.len]
  | .array item =>
      if supportedArrayElementType item then do
        let parts ← arrayFullParts value
        .ok [parts.owner, parts.ptr]
      else
        .error s!"unsupported internal value type: {reprStr ((.array item : Ty))}"
  | .product left right =>
      match value with
      | .product leftValue rightValue => do
          let leftSlots ← flattenInternalValue left leftValue
          let rightSlots ← flattenInternalValue right rightValue
          .ok (leftSlots ++ rightSlots)
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error "non-product value used where product internal value is required"
  | .sum left right =>
      match value with
      | .sum tag leftValue rightValue => do
          let leftSlots ← flattenInternalValue left leftValue
          let rightSlots ← flattenInternalValue right rightValue
          .ok (tag :: leftSlots ++ rightSlots)
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error "non-sum value used where sum internal value is required"
  | .struct name _ fields =>
      match value with
      | .struct actual values =>
          if actual == name && values.length == fields.length then do
            let flattened ← (fields.zip values).mapM fun item =>
              flattenInternalValue item.fst item.snd
            .ok flattened.flatten
          else
            .error s!"structure internal value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error s!"non-structure value used where structure internal value is required: {name}"
  | .variant name _ ctors =>
      match value with
      | .variant actual tag values =>
          if actual == name && values.length == ctors.length then do
            let flattened ← (ctors.zip values).mapM fun ctorPair =>
              if ctorPair.fst.length == ctorPair.snd.length then do
                let fields ← ctorPair.fst.zip ctorPair.snd |>.mapM fun fieldPair =>
                  flattenInternalValue fieldPair.fst fieldPair.snd
                .ok fields.flatten
              else
                .error s!"inductive internal constructor payload shape mismatch: {name}"
            .ok (tag :: flattened.flatten)
          else
            .error s!"inductive internal value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ => .error s!"non-inductive value used where inductive internal value is required: {name}"
  | .recVariant name _ =>
      match value with
      | .heapVariant actual ptr =>
          if actual == name then
            .ok [ptr]
          else
            .error s!"recursive inductive internal value shape mismatch: {name}"
      | .recursiveVariant actual tag ctors =>
          if actual == name then do
            let flattened ← ctors.mapM fun fields =>
              fields.mapM (fun field => flattenInternalValue field.fst field.snd)
            .ok [(.heapAllocSlots (heapChildMaskForCtors ctors) (tag :: flattened.flatten.flatten))]
          else
            .error s!"recursive inductive internal value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenInternalValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenInternalValue ty thenValue) (← flattenInternalValue ty elseValue)
      | _ =>
          .error s!"non-recursive value used where recursive inductive internal value is required: {name}"

partial def flattenAbiValue (ty : Ty) (value : ExtractedValue) : Except String (List IRExpr) :=
  match ty with
  | .unit => scalarValue value |>.map (fun expr => [expr])
  | .bool => scalarValue value |>.map (fun expr => [expr])
  | .u8 => scalarValue value |>.map (fun expr => [u8WrapExpr expr])
  | .u32 => scalarValue value |>.map (fun expr => [u32WrapExpr expr])
  | .u64 => scalarValue value |>.map (fun expr => [expr])
  | .nat => scalarValue value |>.map (fun expr => [expr])
  | .array item =>
      if supportedAbiArrayElementType item then
        arrayPtr value |>.map (fun expr => [expr])
      else
        .error s!"unsupported ABI value type: {reprStr ((.array item : Ty))}"
  | .byteArray => do
      let parts ← byteArrayParts value
      .ok [parts.fst, parts.snd]
  | .struct name _ fields => do
      match value with
      | .struct actual values =>
          if actual == name && values.length == fields.length then
            let flattened ← (fields.zip values).mapM fun item =>
              flattenAbiValue item.fst item.snd
            .ok flattened.flatten
          else
            .error s!"structure ABI value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenAbiValue ty thenValue) (← flattenAbiValue ty elseValue)
      | _ => .error s!"non-structure value used where structure ABI value is required: {name}"
  | .variant name _ ctors => do
      match value with
      | .variant actual tag values =>
          if actual == name && values.length == ctors.length then do
            let flattened ← (ctors.zip values).mapM fun ctorPair =>
              if ctorPair.fst.length == ctorPair.snd.length then do
                let fields ← ctorPair.fst.zip ctorPair.snd |>.mapM fun fieldPair =>
                  flattenAbiValue fieldPair.fst fieldPair.snd
                .ok fields.flatten
              else
                .error s!"inductive ABI constructor payload shape mismatch: {name}"
            .ok (tag :: flattened.flatten)
          else
            .error s!"inductive ABI value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenAbiValue ty thenValue) (← flattenAbiValue ty elseValue)
      | _ => .error s!"non-inductive value used where inductive ABI value is required: {name}"
  | .recVariant name _ =>
      match value with
      | .heapVariant actual ptr =>
          if actual == name then
            .ok [ptr]
          else
            .error s!"recursive inductive ABI value shape mismatch: {name}"
      | .recursiveVariant actual tag ctors =>
          if actual == name then do
            let flattened ← ctors.mapM fun fields =>
              fields.mapM (fun field => flattenInternalValue field.fst field.snd)
            .ok [(.heapAllocSlots (heapChildMaskForCtors ctors) (tag :: flattened.flatten.flatten))]
          else
            .error s!"recursive inductive ABI value shape mismatch: {name}"
      | .letE slot value body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letE slot value expr))
      | .letCall slots index args body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (fun expr => .letCall slots index args expr))
      | .letLocal lets body => do
          let flattened ← flattenAbiValue ty body
          .ok (flattened.map (wrapExprLocalLets lets))
      | .ite cond thenValue elseValue => do
          combineIteSlots cond (← flattenAbiValue ty thenValue) (← flattenAbiValue ty elseValue)
      | _ => .error s!"non-recursive value used where recursive inductive ABI value is required: {name}"
  | other => .error s!"unsupported ABI value type: {reprStr other}"

def resultSlotCount (useAbi : Bool) (ty : Ty) : Nat :=
  if useAbi then abiSlots ty else internalSlots ty

def flattenResultValue (useAbi : Bool) (ty : Ty) (value : ExtractedValue) :
    Except String (List IRExpr) :=
  if useAbi then flattenAbiValue ty value else flattenInternalValue ty value

def assignResultSlots (targets : List Nat) (values : List IRExpr) : IRStmt :=
  LeanExe.IR.seqList <|
    (targets.zip values).map fun item =>
      LeanExe.IR.Stmt.assign item.fst item.snd

def arrayFoldMultiSlotAssign? (targets : List Nat) (values : List IRExpr) :
    Option IRStmt :=
  match values with
  | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
      bodyValues bodyLets bodyDone _ :: _ =>
      if values.length == resultWidth && targets.length == resultWidth then
        let expected : List IRExpr :=
          (List.range resultWidth).map fun offset =>
            .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart
              itemStart bodyValues bodyLets bodyDone offset
        if values == expected then
          some <|
            .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart
              itemStart bodyValues bodyLets bodyDone targets
        else
          none
      else
        none
  | _ => none

def byteArrayFoldMultiSlotAssign? (targets : List Nat) (values : List IRExpr) :
    Option IRStmt :=
  match values with
  | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyLets bodyDone _ :: _ =>
      if values.length == resultWidth && targets.length == resultWidth then
        let expected : List IRExpr :=
          (List.range resultWidth).map fun offset =>
            .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart
              byteSlot bodyValues bodyLets bodyDone offset
        if values == expected then
          some <|
            .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart
              byteSlot bodyValues bodyLets bodyDone targets
        else
          none
      else
        none
  | _ => none

def rangeFoldMultiSlotAssign? (targets : List Nat) (values : List IRExpr) :
    Option IRStmt :=
  match values with
  | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot
      bodyValues bodyLets bodyDone _ :: _ =>
      if values.length == resultWidth && targets.length == resultWidth then
        let expected : List IRExpr :=
          (List.range resultWidth).map fun offset =>
            .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
              bodyLets bodyDone offset
        if values == expected then
          some <|
            .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot
              bodyValues bodyLets bodyDone targets
        else
          none
      else
        none
  | _ => none

def foldMultiSlotAssign? (targets : List Nat) (values : List IRExpr) : Option IRStmt :=
  match arrayFoldMultiSlotAssign? targets values with
  | some stmt => some stmt
  | none =>
      match byteArrayFoldMultiSlotAssign? targets values with
      | some stmt => some stmt
      | none => rangeFoldMultiSlotAssign? targets values

mutual
  def localLetStmtOptimized : LeanExe.IR.LocalLet → IRStmt
    | .expr slot expr => .assign slot expr
    | .call slots index args => .call slots index args
    | .slots slots values =>
        match foldMultiSlotAssign? slots values with
        | some stmt => stmt
        | none =>
            LeanExe.IR.seqList <|
              (slots.zip values).map fun item => LeanExe.IR.Stmt.assign item.fst item.snd
    | .branch cond thenLets elseLets =>
        .ite cond (localLetStmtListOptimized thenLets) (localLetStmtListOptimized elseLets)

  def localLetStmtListOptimized : List LeanExe.IR.LocalLet → IRStmt
    | [] => .skip
    | item :: rest => .seq (localLetStmtOptimized item) (localLetStmtListOptimized rest)
end

def exprReturnsLocalSlot (slot : Nat) : IRExpr → Bool
  | .local candidate => candidate == slot
  | .letE _ _ body => exprReturnsLocalSlot slot body
  | .letCall _ _ _ body => exprReturnsLocalSlot slot body
  | .letLets _ body => exprReturnsLocalSlot slot body
  | .ite _ thenValue elseValue =>
      exprReturnsLocalSlot slot thenValue && exprReturnsLocalSlot slot elseValue
  | _ => false

mutual
  partial def exprReturnsOwnedHeapObjectFrom (ownedLocals : List Nat) : IRExpr → Bool
    | .local slot => ownedLocals.contains slot
    | .letE slot value body =>
        let valueOwned := exprReturnsOwnedHeapObjectFrom ownedLocals value
        let nextOwned := if valueOwned then slot :: ownedLocals else ownedLocals
        exprReturnsOwnedHeapObjectFrom nextOwned body
    | .letCall _ _ _ body => exprReturnsOwnedHeapObjectFrom ownedLocals body
    | .letLets lets body =>
        exprReturnsOwnedHeapObjectFrom (ownedHeapLocalsFromLocalLets ownedLocals lets) body
    | .ite _ thenValue elseValue =>
        exprReturnsOwnedHeapObjectFrom ownedLocals thenValue &&
          exprReturnsOwnedHeapObjectFrom ownedLocals elseValue
    | .arrayAllocSlots .. => true
    | .heapAllocSlots .. => true
    | .arrayReplicateSlots .. => true
    | .arraySetSlots .. => true
    | .arrayPushSlots .. => true
    | .arrayAppendSlots .. => true
    | .arrayExtractSlots .. => true
    | .arrayMapSlots .. => true
    | .arrayFilterSlots .. => true
    | .byteArrayPushPtr .. => true
    | .byteArrayAppendPtr .. => true
    | .byteArraySetPtr .. => true
    | .byteArrayFromArrayPtr .. => true
    | .byteArrayCopySlicePtr .. => true
    | _ => false

  partial def localLetOwnedHeapSlotsFrom
      (ownedLocals : List Nat) :
      LeanExe.IR.LocalLet → List Nat
    | .expr slot expr =>
        if exprReturnsOwnedHeapObjectFrom ownedLocals expr then [slot] else []
    | .slots slots values =>
        (slots.zip values).filterMap fun item =>
          if exprReturnsOwnedHeapObjectFrom ownedLocals item.snd then some item.fst else none
    | .call _ _ _ => []
    | .branch _ _ _ => []

  partial def ownedHeapLocalsFromLocalLets
      (ownedLocals : List Nat)
      (lets : List LeanExe.IR.LocalLet) :
      List Nat :=
    lets.foldl
      (fun owned localLet => owned ++ localLetOwnedHeapSlotsFrom owned localLet)
      ownedLocals
end

def exprReturnsOwnedHeapObject (expr : IRExpr) : Bool :=
  exprReturnsOwnedHeapObjectFrom [] expr

def ownedChildMaskForSlots (childMask : Nat) (slots : List IRExpr) : Nat :=
  let rec loop : Nat → List IRExpr → Nat → Nat
    | _, [], acc => acc
    | slot, expr :: rest, acc =>
        let nextAcc :=
          if maskBitSet childMask slot && exprReturnsOwnedHeapObject expr then
            acc + 2 ^ slot
          else
            acc
        loop (slot + 1) rest nextAcc
  loop 0 slots 0

def valueLetOwnedHeapSlots : ValueLet → List Nat
  | .expr slot expr => if exprReturnsOwnedHeapObject expr then [slot] else []
  | .call _ _ _ => []

def valueLetOwnedHeapSlotsFrom (ownedLocals : List Nat) : ValueLet → List Nat
  | .expr slot expr =>
      let localAliasOwned :=
        match expr with
        | .local sourceSlot => ownedLocals.contains sourceSlot
        | _ => false
      if exprReturnsOwnedHeapObject expr || localAliasOwned then [slot] else []
  | .call _ _ _ => []

def ownedHeapLocalsFromValueLets (lets : List ValueLet) : List Nat :=
  lets.foldl
    (fun owned letValue =>
      owned ++ valueLetOwnedHeapSlotsFrom owned letValue)
    []

def ownedChildMaskForSlotsWithLets
    (childMask : Nat)
    (lets : List ValueLet)
    (slots : List IRExpr) :
    Nat :=
  let ownedLocals := ownedHeapLocalsFromValueLets lets
  let rec loop : Nat → List IRExpr → Nat → Nat
    | _, [], acc => acc
    | slot, expr :: rest, acc =>
        let localOwned :=
          match expr with
          | .local localSlot => ownedLocals.contains localSlot
          | _ => false
        let nextAcc :=
          if maskBitSet childMask slot && (exprReturnsOwnedHeapObject expr || localOwned) then
            acc + 2 ^ slot
          else
            acc
        loop (slot + 1) rest nextAcc
  loop 0 slots 0

def ownedChildMaskForStrictSlots (childMask : Nat) (slots : StrictSlots) : Nat :=
  ownedChildMaskForSlotsWithLets childMask slots.lets slots.slots

def localLetOwnedHeapSlots : LeanExe.IR.LocalLet → List Nat
  | .expr slot expr => if exprReturnsOwnedHeapObject expr then [slot] else []
  | .slots slots values =>
      (slots.zip values).filterMap fun item =>
        if exprReturnsOwnedHeapObject item.snd then some item.fst else none
  | .call _ _ _ => []
  | .branch _ _ _ => []

def localLetCallReleaseOwnerSlots (ctx : Context) : LeanExe.IR.LocalLet → List Nat
  | .call slots index _ => callResultReleaseOwnerSlots ctx index slots
  | _ => []

mutual
  partial def exprReleasedSlots : IRExpr → List Nat
    | .release ptr => exprUsedSlots ptr
    | .u64Bin _ left right => addLiveSlots (exprReleasedSlots left) (exprReleasedSlots right)
    | .ite cond thenValue elseValue =>
        addLiveSlots (condReleasedSlots cond)
          (addLiveSlots (exprReleasedSlots thenValue) (exprReleasedSlots elseValue))
    | .letE _ value body => addLiveSlots (exprReleasedSlots value) (exprReleasedSlots body)
    | .letCall _ _ args body =>
        addLiveSlots (exprListReleasedSlots args) (exprReleasedSlots body)
    | .letLets lets body =>
        addLiveSlots (localLetsReleasedSlots lets) (exprReleasedSlots body)
    | .heapAllocSlots _ values => exprListReleasedSlots values
    | .heapLoadSlot ptr _ => exprReleasedSlots ptr
    | .arrayAllocSlots _ _ cells => exprReleasedSlots cells
    | .arrayReplicateSlots _ _ _ cells values =>
        addLiveSlots (exprReleasedSlots cells) (exprListReleasedSlots values)
    | .arraySize array => exprReleasedSlots array
    | .arrayGetSlot _ _ array index =>
        addLiveSlots (exprReleasedSlots array) (exprReleasedSlots index)
    | .arraySetSlots _ _ _ array index values =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots array) (exprReleasedSlots index))
          (exprListReleasedSlots values)
    | .arrayPushSlots _ _ _ array values =>
        addLiveSlots (exprReleasedSlots array) (exprListReleasedSlots values)
    | .arrayPopSlots _ _ array => exprReleasedSlots array
    | .arrayAppendSlots _ _ left right =>
        addLiveSlots (exprReleasedSlots left) (exprReleasedSlots right)
    | .arrayExtractSlots _ _ array start stop =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots array) (exprReleasedSlots start))
          (exprReleasedSlots stop)
    | .arrayMapSlots _ _ _ _ array _ bodyValues =>
        addLiveSlots (exprReleasedSlots array) (exprListReleasedSlots bodyValues)
    | .arrayFoldMultiSlot _ _ array start stop initValues _ _ bodyValues _ bodyDone _ =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots array) (exprReleasedSlots start))
            (exprReleasedSlots stop))
          (addLiveSlots (exprListReleasedSlots initValues)
            (addLiveSlots (exprListReleasedSlots bodyValues) (exprReleasedSlots bodyDone)))
    | .arrayFindIdxSlots _ array _ predicate _ =>
        addLiveSlots (exprReleasedSlots array) (exprReleasedSlots predicate)
    | .arrayFindSlot _ array _ predicate _ =>
        addLiveSlots (exprReleasedSlots array) (exprReleasedSlots predicate)
    | .arrayEqSlots _ left right _ _ predicate =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots left) (exprReleasedSlots right))
          (exprReleasedSlots predicate)
    | .arrayAnySlots _ array start stop _ predicate _ =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots array) (exprReleasedSlots start))
            (exprReleasedSlots stop))
          (exprReleasedSlots predicate)
    | .arrayFilterSlots _ _ array start stop _ predicate =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots array) (exprReleasedSlots start))
            (exprReleasedSlots stop))
          (exprReleasedSlots predicate)
    | .arrayInsertIfInBoundsSlots _ _ _ array index values =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots array) (exprReleasedSlots index))
          (exprListReleasedSlots values)
    | .arrayEraseIfInBoundsSlots _ _ array index =>
        addLiveSlots (exprReleasedSlots array) (exprReleasedSlots index)
    | .arraySwapIfInBoundsSlots _ _ array left right =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots array) (exprReleasedSlots left))
          (exprReleasedSlots right)
    | .arrayReverseSlots _ _ array => exprReleasedSlots array
    | .byteArrayGet ptr len index =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots ptr) (exprReleasedSlots len))
          (exprReleasedSlots index)
    | .byteArrayPushPtr ptr len value =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots ptr) (exprReleasedSlots len))
          (exprReleasedSlots value)
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots leftPtr) (exprReleasedSlots leftLen))
          (addLiveSlots (exprReleasedSlots rightPtr) (exprReleasedSlots rightLen))
    | .byteArraySetPtr ptr len index value =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots ptr) (exprReleasedSlots len))
            (exprReleasedSlots index))
          (exprReleasedSlots value)
    | .byteArrayFromArrayPtr array => exprReleasedSlots array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots srcPtr) (exprReleasedSlots srcLen))
            (exprReleasedSlots srcOff))
          (addLiveSlots
            (addLiveSlots
              (addLiveSlots (exprReleasedSlots destPtr) (exprReleasedSlots destLen))
              (exprReleasedSlots destOff))
            (exprReleasedSlots copyLen))
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        addLiveSlots
          (addLiveSlots (exprReleasedSlots leftPtr) (exprReleasedSlots leftLen))
          (addLiveSlots (exprReleasedSlots rightPtr) (exprReleasedSlots rightLen))
    | .byteArrayFindIdx ptr len start _ predicate _ =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots ptr) (exprReleasedSlots len))
            (exprReleasedSlots start))
          (exprReleasedSlots predicate)
    | .byteArrayFoldMultiSlot _ ptr len start stop initValues _ _ bodyValues _ bodyDone _ =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots ptr) (exprReleasedSlots len))
            (addLiveSlots (exprReleasedSlots start) (exprReleasedSlots stop)))
          (addLiveSlots (exprListReleasedSlots initValues)
            (addLiveSlots (exprListReleasedSlots bodyValues) (exprReleasedSlots bodyDone)))
    | .rangeFoldMultiSlot _ start stop step initValues _ _ bodyValues _ bodyDone _ =>
        addLiveSlots
          (addLiveSlots
            (addLiveSlots (exprReleasedSlots start) (exprReleasedSlots stop))
            (exprReleasedSlots step))
          (addLiveSlots (exprListReleasedSlots initValues)
            (addLiveSlots (exprListReleasedSlots bodyValues) (exprReleasedSlots bodyDone)))
    | .heapLinearPredicate ptr _ _ _ _ predicate _ _ =>
        addLiveSlots (exprReleasedSlots ptr) (exprReleasedSlots predicate)
    | .call _ args => exprListReleasedSlots args
    | .local _ | .trap | .u64 _ | .runtimeStat _ => []

  partial def exprListReleasedSlots (exprs : List IRExpr) : List Nat :=
    exprs.foldl (fun acc expr => addLiveSlots acc (exprReleasedSlots expr)) []

  partial def condReleasedSlots : IRCond → List Nat
    | .true => []
    | .false => []
    | .eqU64 left right => addLiveSlots (exprReleasedSlots left) (exprReleasedSlots right)
    | .ltU64 left right => addLiveSlots (exprReleasedSlots left) (exprReleasedSlots right)
    | .leU64 left right => addLiveSlots (exprReleasedSlots left) (exprReleasedSlots right)
    | .not cond => condReleasedSlots cond
    | .and left right => addLiveSlots (condReleasedSlots left) (condReleasedSlots right)
    | .or left right => addLiveSlots (condReleasedSlots left) (condReleasedSlots right)

  partial def localLetReleasedSlots : LeanExe.IR.LocalLet → List Nat
    | .expr _ value => exprReleasedSlots value
    | .call _ _ args => exprListReleasedSlots args
    | .slots _ values => exprListReleasedSlots values
    | .branch cond thenLets elseLets =>
        addLiveSlots (condReleasedSlots cond)
          (addLiveSlots (localLetsReleasedSlots thenLets) (localLetsReleasedSlots elseLets))

  partial def localLetsReleasedSlots (lets : List LeanExe.IR.LocalLet) : List Nat :=
    lets.foldl (fun acc letValue => addLiveSlots acc (localLetReleasedSlots letValue)) []
end

mutual
  partial def valueReleasedSlots : ExtractedValue → List Nat
    | .scalar expr => exprReleasedSlots expr
    | .array owner ptr =>
        addLiveSlots (exprReleasedSlots owner) (exprReleasedSlots ptr)
    | .byteArray owner ptr len =>
        addLiveSlots (exprReleasedSlots owner)
          (addLiveSlots (exprReleasedSlots ptr) (exprReleasedSlots len))
    | .product left right =>
        addLiveSlots (valueReleasedSlots left) (valueReleasedSlots right)
    | .sum tag left right =>
        addLiveSlots (exprReleasedSlots tag)
          (addLiveSlots (valueReleasedSlots left) (valueReleasedSlots right))
    | .struct _ fields => valueListReleasedSlots fields
    | .variant _ tag ctors =>
        addLiveSlots (exprReleasedSlots tag) (valueListReleasedSlots ctors.flatten)
    | .recursiveVariant _ tag ctors =>
        addLiveSlots (exprReleasedSlots tag) (valueListReleasedSlots (ctors.flatten.map Prod.snd))
    | .heapVariant _ ptr => exprReleasedSlots ptr
    | .ite _ thenValue elseValue =>
        addLiveSlots (valueReleasedSlots thenValue) (valueReleasedSlots elseValue)
    | .letE _ value body =>
        addLiveSlots (exprReleasedSlots value) (valueReleasedSlots body)
    | .letCall _ _ args body =>
        addLiveSlots (exprListReleasedSlots args) (valueReleasedSlots body)
    | .letLocal lets body =>
        addLiveSlots (localLetsReleasedSlots lets) (valueReleasedSlots body)

  partial def valueListReleasedSlots (values : List ExtractedValue) : List Nat :=
    values.foldl (fun acc value => addLiveSlots acc (valueReleasedSlots value)) []
end

def slotReleasedByValue (slot : Nat) (value : ExtractedValue) : Bool :=
  (valueReleasedSlots value).contains slot

def slotReleasedByExpr (slot : Nat) (expr : IRExpr) : Bool :=
  (exprReleasedSlots expr).contains slot

def appendReleases (stmt : IRStmt) (slots : List Nat) : IRStmt :=
  slots.foldl (fun current slot => .seq current (.release (.local slot))) stmt

def releaseIfDistinctStmt (released : List Nat) (slot : Nat) : IRStmt :=
  let nonzero : IRCond := .not (.eqU64 (.local slot) (.u64 0))
  let distinct :=
    released.foldl
      (fun cond prior => .and cond (.not (.eqU64 (.local slot) (.local prior))))
      nonzero
  .ite distinct (.release (.local slot)) .skip

def appendDistinctReleases (stmt : IRStmt) (slots : List Nat) : IRStmt :=
  let rec loop (released : List Nat) (current : IRStmt) : List Nat → IRStmt
    | [] => current
    | slot :: rest =>
        loop (slot :: released) (.seq current (releaseIfDistinctStmt released slot)) rest
  loop [] stmt slots

mutual
  partial def valueReleaseOwnerLocalSlots : ExtractedValue → List Nat
    | .byteArray owner _ _ =>
        match owner with
        | .local slot => [slot]
        | _ => []
    | .array owner _ =>
        match owner with
        | .local slot => [slot]
        | _ => []
    | .product left right =>
        addLiveSlots (valueReleaseOwnerLocalSlots left) (valueReleaseOwnerLocalSlots right)
    | .sum _ left right =>
        addLiveSlots (valueReleaseOwnerLocalSlots left) (valueReleaseOwnerLocalSlots right)
    | .struct _ fields => valueListReleaseOwnerLocalSlots fields
    | .variant _ _ ctors => valueListReleaseOwnerLocalSlots ctors.flatten
    | .recursiveVariant _ _ ctors =>
        valueListReleaseOwnerLocalSlots (ctors.flatten.map Prod.snd)
    | .ite _ thenValue elseValue =>
        addLiveSlots (valueReleaseOwnerLocalSlots thenValue)
          (valueReleaseOwnerLocalSlots elseValue)
    | .letE _ _ body => valueReleaseOwnerLocalSlots body
    | .letCall _ _ _ body => valueReleaseOwnerLocalSlots body
    | .letLocal _ body => valueReleaseOwnerLocalSlots body
    | .scalar _ | .heapVariant _ _ => []

  partial def valueListReleaseOwnerLocalSlots (values : List ExtractedValue) : List Nat :=
    values.foldl (fun acc value => addLiveSlots acc (valueReleaseOwnerLocalSlots value)) []
end

mutual
  partial def materializeInternalValueLets
      (ty : Ty)
      (value : ExtractedValue)
      (targets : List Nat) :
      Except String (List LeanExe.IR.LocalLet) := do
    match value with
    | .letE slot expr (.array (.local ownerSlot) (.local ptrSlot)) =>
        match ty, targets with
        | .array item, [ownerTarget, ptrTarget] =>
            if supportedArrayElementType item && ownerSlot == slot && ptrSlot == slot then
              .ok [.expr ownerTarget expr, .slots [ptrTarget] [.local ownerTarget]]
            else
              let rest ←
                materializeInternalValueLets ty (.array (.local ownerSlot) (.local ptrSlot))
                  targets
              .ok (.expr slot expr :: rest)
        | _, _ =>
            let rest ← materializeInternalValueLets ty (.array (.local ownerSlot) (.local ptrSlot))
              targets
            .ok (.expr slot expr :: rest)
    | .letE slot expr (.byteArray (.local ownerSlot) (.local ptrSlot) len) =>
        match ty, targets with
        | .byteArray, [ownerTarget, ptrTarget, lenTarget] =>
            if ownerSlot == slot && ptrSlot == slot then
              .ok [.expr ownerTarget expr, .slots [ptrTarget, lenTarget] [.local ownerTarget, len]]
            else
              let rest ←
                materializeInternalValueLets ty
                  (.byteArray (.local ownerSlot) (.local ptrSlot) len)
                  targets
              .ok (.expr slot expr :: rest)
        | _, _ =>
            let rest ←
              materializeInternalValueLets ty (.byteArray (.local ownerSlot) (.local ptrSlot) len)
                targets
            .ok (.expr slot expr :: rest)
    | .letE slot expr body =>
        let rest ← materializeInternalValueLets ty body targets
        .ok (.expr slot expr :: rest)
    | .letCall slots index args body =>
        let rest ← materializeInternalValueLets ty body targets
        .ok (.call slots index args :: rest)
    | .letLocal lets body =>
        let rest ← materializeInternalValueLets ty body targets
        let restResult := pruneLocalLetsWithLive rest targets
        .ok (pruneLocalLets lets restResult.snd ++ restResult.fst)
    | .ite cond thenValue elseValue => do
        let thenLets ← materializeInternalValueLets ty thenValue targets
        let elseLets ← materializeInternalValueLets ty elseValue targets
        .ok [.branch cond thenLets elseLets]
    | _ =>
        match flattenInternalValue ty value with
        | .ok slots =>
            if (foldMultiSlotAssign? targets slots).isSome then
              return [.slots targets slots]
        | .error _ => pure ()
        match ty, value with
        | .product leftTy rightTy, .product leftValue rightValue =>
            let leftWidth := internalSlots leftTy
            let leftTargets := targets.take leftWidth
            let rightTargets := targets.drop leftWidth
            if leftTargets.length != leftWidth then
              .error "product materialization target shape mismatch"
            else
              let leftLets ← materializeInternalValueLets leftTy leftValue leftTargets
              let rightLets ← materializeInternalValueLets rightTy rightValue rightTargets
              .ok (leftLets ++ rightLets)
        | .sum leftTy rightTy, .sum tag leftValue rightValue =>
            match targets with
            | tagTarget :: payloadTargets =>
                let leftWidth := internalSlots leftTy
                let leftTargets := payloadTargets.take leftWidth
                let rightTargets := payloadTargets.drop leftWidth
                if leftTargets.length != leftWidth then
                  .error "sum materialization target shape mismatch"
                else
                  let leftLets ← materializeInternalValueLets leftTy leftValue leftTargets
                  let rightLets ← materializeInternalValueLets rightTy rightValue rightTargets
                  .ok (.slots [tagTarget] [tag] :: leftLets ++ rightLets)
            | [] => .error "sum materialization target shape mismatch"
        | .struct expected _ fieldTys, .struct actual fieldValues =>
            if expected == actual && fieldTys.length == fieldValues.length then
              materializeInternalFieldLets fieldTys fieldValues targets
            else
              .error s!"structure materialization shape mismatch: {expected}"
        | .variant expected _ ctorTys, .variant actual tag ctorValues =>
            if expected == actual && ctorTys.length == ctorValues.length then
              match targets with
              | tagTarget :: payloadTargets => do
                  let payloadLets ← materializeInternalCtorLets ctorTys ctorValues payloadTargets
                  .ok (.slots [tagTarget] [tag] :: payloadLets)
              | [] => .error s!"inductive materialization target shape mismatch: {expected}"
            else
              .error s!"inductive materialization shape mismatch: {expected}"
        | _, _ => do
            let slots ← flattenInternalValue ty value
            if slots.length == targets.length then
              .ok [.slots targets slots]
            else
              .error "materialization target shape mismatch"

  partial def materializeInternalFieldLets
      (fieldTys : List Ty)
      (fieldValues : List ExtractedValue)
      (targets : List Nat) :
      Except String (List LeanExe.IR.LocalLet) := do
    match fieldTys, fieldValues with
    | [], [] =>
        if targets.isEmpty then .ok [] else .error "field materialization target shape mismatch"
    | fieldTy :: restTys, fieldValue :: restValues =>
        let width := internalSlots fieldTy
        let fieldTargets := targets.take width
        let restTargets := targets.drop width
        if fieldTargets.length != width then
          .error "field materialization target shape mismatch"
        else
          let head ← materializeInternalValueLets fieldTy fieldValue fieldTargets
          let tail ← materializeInternalFieldLets restTys restValues restTargets
          .ok (head ++ tail)
    | _, _ => .error "field materialization shape mismatch"

  partial def materializeInternalCtorLets
      (ctorTys : List (List Ty))
      (ctorValues : List (List ExtractedValue))
      (targets : List Nat) :
      Except String (List LeanExe.IR.LocalLet) := do
    match ctorTys, ctorValues with
    | [], [] =>
        if targets.isEmpty then .ok [] else .error "constructor materialization target shape mismatch"
    | fieldTys :: restTys, fieldValues :: restValues =>
        let width := fieldTys.foldl (fun total ty => total + internalSlots ty) 0
        let ctorTargets := targets.take width
        let restTargets := targets.drop width
        if ctorTargets.length != width then
          .error "constructor materialization target shape mismatch"
        else
          let head ← materializeInternalFieldLets fieldTys fieldValues ctorTargets
          let tail ← materializeInternalCtorLets restTys restValues restTargets
          .ok (head ++ tail)
    | _, _ => .error "constructor materialization shape mismatch"
end

def assignResultExprWithOwnedReleases
    (ctx : Context)
    (canReleaseOwnedTemps : Bool)
    (target : Nat)
    (expr : IRExpr) :
    IRStmt :=
  match expr with
  | .letE slot value body =>
      let bodyStmt := assignResultExprWithOwnedReleases ctx canReleaseOwnedTemps target body
      let stmt := .seq (.assign slot value) bodyStmt
      if canReleaseOwnedTemps &&
          exprReturnsOwnedHeapObject value &&
          !slotReleasedByExpr slot body &&
          !exprReturnsLocalSlot slot body then
        .seq stmt (.release (.local slot))
      else
        stmt
  | .letCall slots index args body =>
      let bodyStmt := assignResultExprWithOwnedReleases ctx canReleaseOwnedTemps target body
      let stmt := .seq (.call slots index args) bodyStmt
      if canReleaseOwnedTemps then
        let released := exprReleasedSlots body
        let ownerSlots :=
          (callResultReleaseOwnerSlots ctx index slots).filter fun slot =>
            !released.contains slot
        appendDistinctReleases stmt ownerSlots
      else
        stmt
  | .letLets lets body =>
      let bodyStmt := assignResultExprWithOwnedReleases ctx canReleaseOwnedTemps target body
      let stmt := .seq (localLetStmtListOptimized lets) bodyStmt
      if canReleaseOwnedTemps then
        let released := addLiveSlots (localLetsReleasedSlots lets) (exprReleasedSlots body)
        let ownerSlots :=
          addLiveSlots
            (lets.flatMap localLetOwnedHeapSlots)
            (lets.flatMap (localLetCallReleaseOwnerSlots ctx))
        appendDistinctReleases stmt
          (ownerSlots.filter fun slot => !released.contains slot)
      else
        stmt
  | _ => .assign target expr

def assignResultSlotsWithOwnedReleases
    (ctx : Context)
    (canReleaseOwnedTemps : Bool)
    (targets : List Nat)
    (values : List IRExpr) :
    IRStmt :=
  LeanExe.IR.seqList <|
    (targets.zip values).map fun item =>
      assignResultExprWithOwnedReleases ctx canReleaseOwnedTemps item.fst item.snd

partial def materializeResultValue
    (ctx : Context)
    (useAbi : Bool)
    (ty : Ty)
    (targets : List Nat)
    (value : ExtractedValue) :
    Except String IRStmt := do
  let canReleaseOwnedTemps := !tyContainsHeapPointer ty
  match value with
  | .letE slot expr body => do
      let bodyStmt ← materializeResultValue ctx useAbi ty targets body
      let stmt := .seq (.assign slot expr) bodyStmt
      if canReleaseOwnedTemps &&
          exprReturnsOwnedHeapObject expr &&
          !slotReleasedByValue slot body then
        .ok (.seq stmt (.release (.local slot)))
      else
        .ok stmt
  | .letCall slots index args body => do
      let bodyStmt ← materializeResultValue ctx useAbi ty targets body
      let stmt := .seq (.call slots index args) bodyStmt
      if canReleaseOwnedTemps then
        let released := valueReleasedSlots body
        let bodyOwnerSlots :=
          (valueReleaseOwnerLocalSlots body).filter fun slot =>
            slots.contains slot && !released.contains slot
        let resultOwnerSlots :=
          (callResultReleaseOwnerSlots ctx index slots).filter fun slot =>
            !released.contains slot
        let ownerSlots := addLiveSlots bodyOwnerSlots resultOwnerSlots
        .ok (appendDistinctReleases stmt ownerSlots)
      else
        .ok stmt
  | .letLocal lets body => do
      let values ← flattenResultValue useAbi ty body
      let kept := pruneLocalLets lets (exprListUsedSlots values)
      let bodyStmt ← materializeResultValue ctx useAbi ty targets body
      let stmt := .seq (localLetStmtListOptimized kept) bodyStmt
      if canReleaseOwnedTemps then
        let released := addLiveSlots (localLetsReleasedSlots kept) (valueReleasedSlots body)
        let ownerSlots :=
          addLiveSlots
            (kept.flatMap localLetOwnedHeapSlots)
            (kept.flatMap (localLetCallReleaseOwnerSlots ctx))
        .ok (appendDistinctReleases stmt
          (ownerSlots.filter fun slot => !released.contains slot))
      else
        .ok stmt
  | .ite cond thenValue elseValue => do
      let thenStmt ← materializeResultValue ctx useAbi ty targets thenValue
      let elseStmt ← materializeResultValue ctx useAbi ty targets elseValue
      .ok (.ite cond thenStmt elseStmt)
  | _ =>
      if !useAbi then
        let lets ← materializeInternalValueLets ty value targets
        let stmt := localLetStmtListOptimized lets
        if canReleaseOwnedTemps then
          let released := localLetsReleasedSlots lets
          let ownerSlots :=
            addLiveSlots
              (lets.flatMap localLetOwnedHeapSlots)
              (lets.flatMap (localLetCallReleaseOwnerSlots ctx))
          .ok (appendDistinctReleases stmt
            (ownerSlots.filter fun slot => !released.contains slot))
        else
          .ok stmt
      else
        let values ← flattenResultValue useAbi ty value
        match foldMultiSlotAssign? targets values with
        | some stmt => .ok stmt
        | none =>
            if targets.length == values.length then
              .ok (assignResultSlotsWithOwnedReleases ctx canReleaseOwnedTemps targets values)
            else
              .error "result slot count mismatch"

end LeanExe.Extract.Core
