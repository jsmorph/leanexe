import LeanExe.Core
import LeanExe.IR.Core

namespace LeanExe.Wasm.Binary

def byte (n : Nat) : UInt8 :=
  UInt8.ofNat n

def ofNats (bytes : List Nat) : List UInt8 :=
  bytes.map byte

partial def u32leb (n : Nat) : List UInt8 :=
  let low := n % 128
  let rest := n / 128
  if rest = 0 then
    [byte low]
  else
    byte (low + 128) :: u32leb rest

partial def s64lebInt (n : Int) : List UInt8 :=
  let lowInt := n % 128
  let low := lowInt.toNat
  let rest := (n - lowInt) / 128
  if (rest == 0 && low < 64) || (rest == -1 && 64 <= low) then
    [byte low]
  else
    byte (low + 128) :: s64lebInt rest

def byteVec (bytes : List UInt8) : List UInt8 :=
  u32leb bytes.length ++ bytes

def concatBytes : List (List UInt8) → List UInt8
  | [] => []
  | item :: rest => item ++ concatBytes rest

def u32Vec (values : List Nat) : List UInt8 :=
  u32leb values.length ++ concatBytes (values.map u32leb)

def vec (items : List (List UInt8)) : List UInt8 :=
  u32leb items.length ++ concatBytes items

def name (s : String) : List UInt8 :=
  byteVec s.toUTF8.data.toList

def wasmSection (id : Nat) (payload : List UInt8) : List UInt8 :=
  byte id :: u32leb payload.length ++ payload

def funcType (params results : List UInt8) : List UInt8 :=
  byte 96 :: byteVec params ++ byteVec results

def i32 : UInt8 :=
  byte 127

def i64 : UInt8 :=
  byte 126

def typeSection : List UInt8 :=
  wasmSection 1 <| vec [
    funcType [i32] [i32],
    funcType [] [],
    funcType [i32, i32] [i32]
  ]

def functionSection : List UInt8 :=
  wasmSection 3 <| byteVec (ofNats [0, 1, 2])

def memorySection : List UInt8 :=
  wasmSection 5 <| vec [
    ofNats [0] ++ u32leb 1
  ]

def globalSection : List UInt8 :=
  wasmSection 6 <| vec [
    ofNats [127, 1, 65] ++ u32leb 4096 ++ ofNats [11]
  ]

def exportEntry (entryName : String) (kind index : Nat) : List UInt8 :=
  name entryName ++ ofNats [kind] ++ u32leb index

def exportSection : List UInt8 :=
  wasmSection 7 <| vec [
    exportEntry "memory" 2 0,
    exportEntry "alloc" 0 0,
    exportEntry "reset" 0 1,
    exportEntry "validate" 0 2
  ]

def body (locals code : List UInt8) : List UInt8 :=
  byteVec (locals ++ code ++ ofNats [11])

def allocBody : List UInt8 :=
  body
    (ofNats [0])
    (ofNats [
      35, 0,
      35, 0,
      32, 0,
      106,
      36, 0
    ])

def resetBody : List UInt8 :=
  body
    (ofNats [0])
    (ofNats [65] ++ u32leb 4096 ++ ofNats [36, 0])

def validateBody (validator : LeanExe.Core.LoweredValidator) : List UInt8 :=
  body
    (ofNats [1, 2, 127])
    (ofNats [
      65, 0,
      33, 2,
      2, 64,
      2, 64,
      3, 64,
      32, 2,
      32, 1,
      79,
      13, 1,
      32, 0,
      32, 2,
      106,
      45, 0, 0,
      33, 3,
      32, 3,
      65
    ] ++ u32leb validator.min ++ ofNats [
      73,
      13, 2,
      32, 3,
      65
    ] ++ u32leb validator.max ++ ofNats [
      75,
      13, 2,
      32, 2,
      65, 1,
      106,
      33, 2,
      12, 0,
      11,
      11,
      65, 1,
      15,
      11,
      65, 0
    ])

def codeSection (validator : LeanExe.Core.LoweredValidator) : List UInt8 :=
  wasmSection 10 <| vec [
    allocBody,
    resetBody,
    validateBody validator
  ]

def moduleBytes
    (validator : LeanExe.Core.LoweredValidator :=
      LeanExe.Core.lower LeanExe.Core.asciiDigits) : ByteArray :=
  ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
    ++ typeSection
    ++ functionSection
    ++ memorySection
    ++ globalSection
    ++ exportSection
    ++ codeSection validator).toArray

def i64Const (n : Nat) : List UInt8 :=
  let bits := n % (2 ^ 64)
  let signed :=
    if bits < 2 ^ 63 then
      Int.ofNat bits
    else
      Int.ofNat bits - Int.ofNat (2 ^ 64)
  byte 66 :: s64lebInt signed

def i32Const (n : Nat) : List UInt8 :=
  byte 65 :: u32leb n

def localGet (index : Nat) : List UInt8 :=
  ofNats [32] ++ u32leb index

def localSet (index : Nat) : List UInt8 :=
  ofNats [33] ++ u32leb index

def localTee (index : Nat) : List UInt8 :=
  ofNats [34] ++ u32leb index

def call (index : Nat) : List UInt8 :=
  ofNats [16] ++ u32leb index

def globalGet (index : Nat) : List UInt8 :=
  ofNats [35] ++ u32leb index

def globalSet (index : Nat) : List UInt8 :=
  ofNats [36] ++ u32leb index

namespace CoreWasm

abbrev Expr := LeanExe.IR.Expr
abbrev Cond := LeanExe.IR.Cond
abbrev LocalLet := LeanExe.IR.LocalLet
abbrev Stmt := LeanExe.IR.Stmt
abbrev Func := LeanExe.IR.Func
abbrev Module := LeanExe.IR.Module

mutual
  partial def shiftExprCalls (offset : Nat) : Expr → Expr
    | .local index => .local index
    | .trap => .trap
    | .u64 value => .u64 value
    | .u64Bin op left right =>
        .u64Bin op (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .ite cond thenValue elseValue =>
        .ite (shiftCondCalls offset cond)
          (shiftExprCalls offset thenValue)
          (shiftExprCalls offset elseValue)
    | .letE slot value body =>
        .letE slot (shiftExprCalls offset value) (shiftExprCalls offset body)
    | .letCall slots index args body =>
        .letCall slots (index + offset) (args.map (shiftExprCalls offset))
          (shiftExprCalls offset body)
    | .letLets lets body =>
        .letLets (lets.map (shiftLocalLetCalls offset)) (shiftExprCalls offset body)
    | .runtimeStat stat => .runtimeStat stat
    | .release ptr => .release (shiftExprCalls offset ptr)
    | .arrayAllocSlots width childMask cells =>
        .arrayAllocSlots width childMask (shiftExprCalls offset cells)
    | .heapAllocSlots childMask values =>
        .heapAllocSlots childMask (values.map (shiftExprCalls offset))
    | .heapLoadSlot ptr slot =>
        .heapLoadSlot (shiftExprCalls offset ptr) slot
    | .arrayReplicateSlots width childMask ownedMask cells values =>
        .arrayReplicateSlots width childMask ownedMask (shiftExprCalls offset cells)
          (values.map (shiftExprCalls offset))
    | .arraySize array =>
        .arraySize (shiftExprCalls offset array)
    | .arrayGetSlot width slot array index =>
        .arrayGetSlot width slot (shiftExprCalls offset array) (shiftExprCalls offset index)
    | .arraySetSlots width childMask ownedMask array index values =>
        .arraySetSlots width childMask ownedMask (shiftExprCalls offset array)
          (shiftExprCalls offset index)
          (values.map (shiftExprCalls offset))
    | .arrayPushSlots width childMask ownedMask array values =>
        .arrayPushSlots width childMask ownedMask (shiftExprCalls offset array)
          (values.map (shiftExprCalls offset))
    | .arrayPopSlots width childMask array =>
        .arrayPopSlots width childMask (shiftExprCalls offset array)
    | .arrayAppendSlots width childMask left right =>
        .arrayAppendSlots width childMask (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .arrayExtractSlots width childMask array start stop =>
        .arrayExtractSlots width childMask (shiftExprCalls offset array) (shiftExprCalls offset start)
          (shiftExprCalls offset stop)
    | .arrayMapSlots sourceWidth resultWidth childMask ownedMask array itemStart bodyValues =>
        .arrayMapSlots sourceWidth resultWidth childMask ownedMask (shiftExprCalls offset array) itemStart
          (bodyValues.map (shiftExprCalls offset))
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyLets bodyDone resultSlot =>
        .arrayFoldMultiSlot sourceWidth resultWidth (shiftExprCalls offset array)
          (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart itemStart
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) resultSlot
    | .arrayFindIdxSlots sourceWidth array itemStart predicate returnPayload =>
        .arrayFindIdxSlots sourceWidth (shiftExprCalls offset array) itemStart
          (shiftExprCalls offset predicate) returnPayload
    | .arrayFindSlot sourceWidth array itemStart predicate slot =>
        .arrayFindSlot sourceWidth (shiftExprCalls offset array) itemStart
          (shiftExprCalls offset predicate) slot
    | .arrayEqSlots width left right leftStart rightStart predicate =>
        .arrayEqSlots width (shiftExprCalls offset left) (shiftExprCalls offset right)
          leftStart rightStart (shiftExprCalls offset predicate)
    | .arrayAnySlots sourceWidth array start stop itemStart predicate forAll =>
        .arrayAnySlots sourceWidth (shiftExprCalls offset array) (shiftExprCalls offset start)
          (shiftExprCalls offset stop) itemStart (shiftExprCalls offset predicate) forAll
    | .arrayFilterSlots sourceWidth childMask array start stop itemStart predicate =>
        .arrayFilterSlots sourceWidth childMask (shiftExprCalls offset array) (shiftExprCalls offset start)
          (shiftExprCalls offset stop) itemStart (shiftExprCalls offset predicate)
    | .arrayInsertIfInBoundsSlots width childMask ownedMask array index values =>
        .arrayInsertIfInBoundsSlots width childMask ownedMask (shiftExprCalls offset array)
          (shiftExprCalls offset index) (values.map (shiftExprCalls offset))
    | .arrayEraseIfInBoundsSlots width childMask array index =>
        .arrayEraseIfInBoundsSlots width childMask (shiftExprCalls offset array) (shiftExprCalls offset index)
    | .arraySwapIfInBoundsSlots width childMask array left right =>
        .arraySwapIfInBoundsSlots width childMask (shiftExprCalls offset array)
          (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .arrayReverseSlots width childMask array =>
        .arrayReverseSlots width childMask (shiftExprCalls offset array)
    | .byteArrayGet ptr len index =>
        .byteArrayGet (shiftExprCalls offset ptr) (shiftExprCalls offset len)
          (shiftExprCalls offset index)
    | .byteArrayPushPtr ptr len value =>
        .byteArrayPushPtr (shiftExprCalls offset ptr) (shiftExprCalls offset len)
          (shiftExprCalls offset value)
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        .byteArrayAppendPtr (shiftExprCalls offset leftPtr) (shiftExprCalls offset leftLen)
          (shiftExprCalls offset rightPtr) (shiftExprCalls offset rightLen)
    | .byteArraySetPtr ptr len index value =>
        .byteArraySetPtr (shiftExprCalls offset ptr) (shiftExprCalls offset len)
          (shiftExprCalls offset index) (shiftExprCalls offset value)
    | .byteArrayFromArrayPtr array =>
        .byteArrayFromArrayPtr (shiftExprCalls offset array)
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        .byteArrayCopySlicePtr (shiftExprCalls offset srcPtr) (shiftExprCalls offset srcLen)
          (shiftExprCalls offset srcOff) (shiftExprCalls offset destPtr)
          (shiftExprCalls offset destLen) (shiftExprCalls offset destOff)
          (shiftExprCalls offset copyLen)
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        .byteArrayEq (shiftExprCalls offset leftPtr) (shiftExprCalls offset leftLen)
          (shiftExprCalls offset rightPtr) (shiftExprCalls offset rightLen)
    | .byteArrayFindIdx ptr len start byteSlot predicate returnPayload =>
        .byteArrayFindIdx (shiftExprCalls offset ptr) (shiftExprCalls offset len)
          (shiftExprCalls offset start) byteSlot (shiftExprCalls offset predicate) returnPayload
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone resultSlot =>
        .byteArrayFoldMultiSlot resultWidth (shiftExprCalls offset ptr)
          (shiftExprCalls offset len) (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart byteSlot
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone resultSlot =>
        .rangeFoldMultiSlot resultWidth (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (shiftExprCalls offset step) (initValues.map (shiftExprCalls offset)) accStart
          itemSlot (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) resultSlot
    | .heapLinearPredicate ptr continueTag fieldSlotCount recursiveFieldOffset fieldStart
        predicate stopWhenTrue terminalValue =>
        .heapLinearPredicate (shiftExprCalls offset ptr) continueTag fieldSlotCount
          recursiveFieldOffset fieldStart (shiftExprCalls offset predicate) stopWhenTrue
          terminalValue
    | .call index args =>
        .call (index + offset) (args.map (shiftExprCalls offset))

  partial def shiftCondCalls (offset : Nat) : Cond → Cond
    | .true => .true
    | .false => .false
    | .eqU64 left right =>
        .eqU64 (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .ltU64 left right =>
        .ltU64 (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .leU64 left right =>
        .leU64 (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .not cond => .not (shiftCondCalls offset cond)
    | .and left right => .and (shiftCondCalls offset left) (shiftCondCalls offset right)
    | .or left right => .or (shiftCondCalls offset left) (shiftCondCalls offset right)

  partial def shiftLocalLetCalls (offset : Nat) : LocalLet → LocalLet
    | .expr slot value => .expr slot (shiftExprCalls offset value)
    | .call slots index args => .call slots (index + offset) (args.map (shiftExprCalls offset))
    | .slots slots values => .slots slots (values.map (shiftExprCalls offset))
    | .branch cond thenLets elseLets =>
        .branch (shiftCondCalls offset cond)
          (thenLets.map (shiftLocalLetCalls offset))
          (elseLets.map (shiftLocalLetCalls offset))

  partial def shiftStmtCalls (offset : Nat) : Stmt → Stmt
    | .skip => .skip
    | .assign index value => .assign index (shiftExprCalls offset value)
    | .call slots index args => .call slots (index + offset) (args.map (shiftExprCalls offset))
    | .release ptr => .release (shiftExprCalls offset ptr)
    | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyLets bodyDone targets =>
        .arrayFoldMultiSlotAssign sourceWidth resultWidth (shiftExprCalls offset array)
          (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart itemStart
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) targets
    | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart
        byteSlot bodyValues bodyLets bodyDone targets =>
        .byteArrayFoldMultiSlotAssign resultWidth (shiftExprCalls offset ptr)
          (shiftExprCalls offset len) (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart byteSlot
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) targets
    | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyLets bodyDone targets =>
        .rangeFoldMultiSlotAssign resultWidth (shiftExprCalls offset start)
          (shiftExprCalls offset stop) (shiftExprCalls offset step)
          (initValues.map (shiftExprCalls offset)) accStart itemSlot
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) targets
    | .ite cond thenStmt elseStmt =>
        .ite (shiftCondCalls offset cond) (shiftStmtCalls offset thenStmt)
          (shiftStmtCalls offset elseStmt)
    | .seq first second => .seq (shiftStmtCalls offset first) (shiftStmtCalls offset second)
    | .while cond body => .while (shiftCondCalls offset cond) (shiftStmtCalls offset body)
end

def shiftFuncCalls (offset : Nat) (func : Func) : Func :=
  { func with
    body := shiftStmtCalls offset func.body,
    results := func.results.map (shiftExprCalls offset) }

def shiftModuleCalls (offset : Nat) (module_ : Module) : Module :=
  { funcs := module_.funcs.map (shiftFuncCalls offset) }

def emitU64Op : LeanExe.IR.U64Op → List UInt8
  | .add => ofNats [124]
  | .natAdd => ofNats [124]
  | .sub => ofNats [125]
  | .natSub => ofNats [125]
  | .mul => ofNats [126]
  | .natMul => ofNats [126]
  | .divU => ofNats [128]
  | .modU => ofNats [130]
  | .bitAnd => ofNats [131]
  | .bitOr => ofNats [132]
  | .bitXor => ofNats [133]
  | .shiftLeft => ofNats [134]
  | .shiftRight => ofNats [136]

def coreGlobalSection : List UInt8 :=
  wasmSection 6 <| vec [
    ofNats [126, 1] ++ i64Const 4096 ++ ofNats [11],
    ofNats [126, 1] ++ i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ i64Const 0 ++ ofNats [11]
  ]

def coreMemorySection : List UInt8 :=
  wasmSection 5 <| vec [
    ofNats [0] ++ u32leb 16
  ]

def i32WrapI64 : List UInt8 :=
  ofNats [167]

def i64Load : List UInt8 :=
  ofNats [41, 3, 0]

def i32Load : List UInt8 :=
  ofNats [40, 2, 0]

def i64Eq : List UInt8 :=
  ofNats [81]

def i64Store : List UInt8 :=
  ofNats [55, 3, 0]

def i32Store : List UInt8 :=
  ofNats [54, 2, 0]

def i32Load8U : List UInt8 :=
  ofNats [45, 0, 0]

def i32Store8 : List UInt8 :=
  ofNats [58, 0, 0]

def i32Eq : List UInt8 :=
  ofNats [70]

def i32ConstNegOne : List UInt8 :=
  ofNats [65, 127]

def i64ExtendI32U : List UInt8 :=
  ofNats [173]

def i64LtU : List UInt8 :=
  ofNats [84]

def i64Ne : List UInt8 :=
  ofNats [82]

def i64LeU : List UInt8 :=
  ofNats [88]

def i64GeU : List UInt8 :=
  ofNats [90]

def i64And : List UInt8 :=
  ofNats [131]

def i64ShrU : List UInt8 :=
  ofNats [136]

def i64Eqz : List UInt8 :=
  ofNats [80]

def unreachable : List UInt8 :=
  ofNats [0]

def returnOp : List UInt8 :=
  ofNats [15]

def memorySize : List UInt8 :=
  ofNats [63, 0]

def memoryGrow : List UInt8 :=
  ofNats [64, 0]

def i64Align8 (value : List UInt8) : List UInt8 :=
  value ++ i64Const 7 ++ ofNats [124] ++ i64Const 8 ++ ofNats [128] ++
    i64Const 8 ++ ofNats [126]

def rcHeaderBytes : Nat :=
  48

def rcMagic : Nat :=
  5501223100278326855

def rcKindRaw : Nat :=
  0

def rcKindSlots : Nat :=
  1

def rcKindArray : Nat :=
  2

def runtimeStatGlobal : LeanExe.IR.RuntimeStat → Nat
  | .allocs => 2
  | .retains => 3
  | .releases => 4
  | .frees => 5

def incGlobal (index : Nat) : List UInt8 :=
  globalGet index ++ i64Const 1 ++ ofNats [124] ++ globalSet index

def rcHeaderAddress (ptr : List UInt8) (offset : Nat) : List UInt8 :=
  ptr ++ i64Const offset ++ ofNats [125] ++ i32WrapI64

def rcHeaderLoad (ptr : List UInt8) (offset : Nat) : List UInt8 :=
  rcHeaderAddress ptr offset ++ i64Load

def rcHeaderStore (ptr : List UInt8) (offset : Nat) (value : List UInt8) : List UInt8 :=
  rcHeaderAddress ptr offset ++ value ++ i64Store

def rcInitHeader
    (ptr capacity kind aux1 aux2 : List UInt8) :
    List UInt8 :=
  rcHeaderStore ptr 48 (i64Const rcMagic) ++
    rcHeaderStore ptr 40 (i64Const 1) ++
    rcHeaderStore ptr 32 capacity ++
    rcHeaderStore ptr 24 kind ++
    rcHeaderStore ptr 16 aux1 ++
    rcHeaderStore ptr 8 aux2

def rcAllocPayload
    (scratch : Nat)
    (payloadBytes kind aux1 aux2 : List UInt8) :
    List UInt8 :=
  let alignedLocal := scratch
  let prevLocal := scratch + 1
  let currLocal := scratch + 2
  let sizeLocal := scratch + 3
  let nextLocal := scratch + 4
  let ptrLocal := scratch + 5
  let endLocal := sizeLocal
  let requiredPagesLocal := nextLocal
  let unlinkCurrent :=
    localGet prevLocal ++ i64Const 0 ++ i64Eq ++
      ofNats [4, 64] ++
        localGet nextLocal ++ globalSet 1 ++
      ofNats [5] ++
        rcHeaderStore (localGet prevLocal) 8 (localGet nextLocal) ++
      ofNats [11]
  let takeCurrent :=
    unlinkCurrent ++
      rcInitHeader (localGet currLocal) (localGet sizeLocal) kind aux1 aux2 ++
      localGet currLocal ++ localSet ptrLocal
  let searchLoop :=
    ofNats [2, 64, 3, 64] ++
      localGet currLocal ++ i64Const 0 ++ i64Eq ++ ofNats [13] ++ u32leb 1 ++
      localGet ptrLocal ++ i64Const 0 ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
      rcHeaderLoad (localGet currLocal) 32 ++ localSet sizeLocal ++
      rcHeaderLoad (localGet currLocal) 8 ++ localSet nextLocal ++
      localGet sizeLocal ++ localGet alignedLocal ++ i64GeU ++
        ofNats [4, 64] ++
          takeCurrent ++
        ofNats [5] ++
          localGet currLocal ++ localSet prevLocal ++
          localGet nextLocal ++ localSet currLocal ++
        ofNats [11] ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]
  let bumpAllocate :=
    globalGet 0 ++ i64Const rcHeaderBytes ++ ofNats [124] ++ localGet alignedLocal ++
      ofNats [124] ++ localTee endLocal ++
      globalGet 0 ++ i64LtU ++
      ofNats [4, 64] ++
        unreachable ++
      ofNats [11] ++
      localGet endLocal ++ i64Const 1 ++ ofNats [125] ++ i64Const 65536 ++
        ofNats [128] ++ i64Const 1 ++ ofNats [124] ++ localSet requiredPagesLocal ++
      memorySize ++ i64ExtendI32U ++ localGet requiredPagesLocal ++ i64LtU ++
      ofNats [4, 64] ++
        localGet requiredPagesLocal ++ memorySize ++ i64ExtendI32U ++ ofNats [125] ++
          i32WrapI64 ++ memoryGrow ++ i32ConstNegOne ++ i32Eq ++
          ofNats [4, 64] ++
            unreachable ++
          ofNats [11] ++
      ofNats [11] ++
      globalGet 0 ++ i64Const rcHeaderBytes ++ ofNats [124] ++ localSet ptrLocal ++
      localGet endLocal ++ globalSet 0 ++
      rcInitHeader (localGet ptrLocal) (localGet alignedLocal) kind aux1 aux2
  i64Align8 payloadBytes ++ localSet alignedLocal ++
    localGet alignedLocal ++ i64Const 8 ++ i64LtU ++
      ofNats [4, 64] ++
        i64Const 8 ++ localSet alignedLocal ++
      ofNats [11] ++
    i64Const 0 ++ localSet ptrLocal ++
    i64Const 0 ++ localSet prevLocal ++
    globalGet 1 ++ localSet currLocal ++
    searchLoop ++
    localGet ptrLocal ++ i64Const 0 ++ i64Eq ++
      ofNats [4, 64] ++
        bumpAllocate ++
      ofNats [11] ++
    incGlobal (runtimeStatGlobal .allocs) ++
    localGet ptrLocal

def rcArrayPayloadBytes (width : Nat) (len : List UInt8) : List UInt8 :=
  i64Const 8 ++ len ++ i64Const width ++ ofNats [126] ++ i64Const 8 ++ ofNats [126, 124]

def rcAllocArrayObject (scratch width childMask : Nat) (len : List UInt8) : List UInt8 :=
  rcAllocPayload scratch
    (rcArrayPayloadBytes width len)
    (i64Const rcKindArray)
    (i64Const width)
    (i64Const childMask)

def rcAllocSlotObject (scratch slots childMask : Nat) : List UInt8 :=
  rcAllocPayload scratch
    (i64Const (slots * 8))
    (i64Const rcKindSlots)
    (i64Const slots)
    (i64Const childMask)

def rcAllocRawObject (scratch : Nat) (len : List UInt8) : List UInt8 :=
  rcAllocPayload scratch (len) (i64Const rcKindRaw) (i64Const 0) (i64Const 0)

def arrayCellAddress (base index : List UInt8) : List UInt8 :=
  base ++ index ++ i64Const 1 ++ ofNats [124] ++ i64Const 8 ++ ofNats [126, 124] ++
    i32WrapI64

def arraySlotAddress (width slot : Nat) (base index : List UInt8) : List UInt8 :=
  base ++ index ++ i64Const width ++ ofNats [126] ++ i64Const (slot + 1) ++
    ofNats [124] ++ i64Const 8 ++ ofNats [126, 124] ++ i32WrapI64

def enumerateAux {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | item :: rest, index => (index, item) :: enumerateAux rest (index + 1)

def enumerate {α : Type} (items : List α) : List (Nat × α) :=
  enumerateAux items 0

def maskBitSet (mask slot : Nat) : Bool :=
  (mask / (2 ^ slot)) % 2 == 1

def emitRetainLocal (ptrLocal rcLocal : Nat) : List UInt8 :=
  localGet ptrLocal ++ i64Const 0 ++ i64Ne ++
    ofNats [4, 64] ++
      rcHeaderLoad (localGet ptrLocal) 48 ++ i64Const rcMagic ++ i64Ne ++
        ofNats [4, 64] ++ unreachable ++ ofNats [11] ++
      rcHeaderLoad (localGet ptrLocal) 40 ++ localSet rcLocal ++
      localGet rcLocal ++ i64Const 0 ++ i64Eq ++
        ofNats [4, 64] ++ unreachable ++ ofNats [11] ++
      incGlobal (runtimeStatGlobal .retains) ++
      rcHeaderStore (localGet ptrLocal) 40 (localGet rcLocal ++ i64Const 1 ++ ofNats [124]) ++
    ofNats [11]

def emitRetainArraySlotsAtIndex
    (width childMask skipMask childLocal rcLocal : Nat)
    (base index : List UInt8) :
    List UInt8 :=
  (List.range width).flatMap fun slot =>
    if maskBitSet childMask slot && !maskBitSet skipMask slot then
      arraySlotAddress width slot base index ++ i64Load ++ localSet childLocal ++
        emitRetainLocal childLocal rcLocal
    else
      []

def emitRetainArrayRange
    (width childMask loopLocal childLocal rcLocal : Nat)
    (base start len : List UInt8) :
    List UInt8 :=
  if childMask == 0 then
    []
  else
    let index := start ++ localGet loopLocal ++ ofNats [124]
    i64Const 0 ++ localSet loopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet loopLocal ++ len ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        emitRetainArraySlotsAtIndex width childMask 0 childLocal rcLocal base index ++
        localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11]

def emitRetainArrayRangeWithSpecial
    (width childMask skipMask loopLocal childLocal rcLocal : Nat)
    (base start len specialIndex : List UInt8) :
    List UInt8 :=
  if childMask == 0 then
    []
  else
    let index := start ++ localGet loopLocal ++ ofNats [124]
    i64Const 0 ++ localSet loopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet loopLocal ++ len ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        index ++ specialIndex ++ i64Eq ++
          ofNats [4, 64] ++
            emitRetainArraySlotsAtIndex width childMask skipMask childLocal rcLocal base index ++
          ofNats [5] ++
            emitRetainArraySlotsAtIndex width childMask 0 childLocal rcLocal base index ++
          ofNats [11] ++
        localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11]

mutual
  partial def exprScratch : Expr → Nat
    | .local _ => 0
    | .trap => 0
    | .u64 _ => 0
    | .u64Bin .natAdd left right => 3 + max (exprScratch left) (exprScratch right)
    | .u64Bin .natSub left right => 2 + max (exprScratch left) (exprScratch right)
    | .u64Bin .natMul left right => 2 + max (exprScratch left) (exprScratch right)
    | .u64Bin .divU left right => 2 + max (exprScratch left) (exprScratch right)
    | .u64Bin .modU left right => 2 + max (exprScratch left) (exprScratch right)
    | .u64Bin _ left right => max (exprScratch left) (exprScratch right)
    | .ite cond thenValue elseValue =>
        max (condScratch cond) (max (exprScratch thenValue) (exprScratch elseValue))
    | .letE _ value body => max (exprScratch value) (exprScratch body)
    | .runtimeStat _ => 0
    | .release ptr => exprScratch ptr
    | .arrayAllocSlots _ _ cells => 8 + exprScratch cells
    | .heapAllocSlots _ values =>
        1 + values.length +
          max 6 (values.foldl (fun n value => max n (exprScratch value)) 0)
    | .heapLoadSlot ptr _ => 1 + exprScratch ptr
    | .arrayReplicateSlots _ _ _ cells values =>
        5 + values.length +
          max 6
            (max (exprScratch cells) (values.foldl (fun n value => max n (exprScratch value)) 0))
    | .arraySize array => 1 + exprScratch array
    | .arrayGetSlot _ _ array index => 2 + max (exprScratch array) (exprScratch index)
    | .arraySetSlots _ _ _ array index values =>
        8 + values.length +
          max 6
            (max (exprScratch array)
              (max (exprScratch index)
                (values.foldl (fun n value => max n (exprScratch value)) 0)))
    | .arrayPushSlots _ _ _ array values =>
        8 + values.length +
          max 6
            (max (exprScratch array) (values.foldl (fun n value => max n (exprScratch value)) 0))
    | .arrayPopSlots _ _ array => 8 + max 6 (exprScratch array)
    | .arrayAppendSlots _ _ left right => 11 + max 6 (max (exprScratch left) (exprScratch right))
    | .arrayExtractSlots _ _ array start stop =>
        12 + max 6 (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
    | .arrayMapSlots _ _ _ _ array _ bodyValues =>
        6 + max 6
          (max (exprScratch array)
            (bodyValues.foldl (fun n value => max n (exprScratch value)) 0))
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues _ _ bodyValues
        bodyLets bodyDone _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
        let bodyScratch :=
          max letScratch <|
            max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        5 + sourceWidth + resultWidth + 1 +
          max
            (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
            (max initScratch bodyScratch)
    | .arrayFindIdxSlots sourceWidth array _ predicate _ =>
        4 + sourceWidth + max (exprScratch array) (exprScratch predicate)
    | .arrayFindSlot sourceWidth array _ predicate _ =>
        4 + sourceWidth + max (exprScratch array) (exprScratch predicate)
    | .arrayEqSlots width left right _ _ predicate =>
        5 + max
          (max (exprScratch left) (exprScratch right))
          (max (exprScratch predicate) width)
    | .arrayAnySlots sourceWidth array start stop _ predicate _ =>
        6 + sourceWidth +
          max
            (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
            (exprScratch predicate)
    | .arrayFilterSlots sourceWidth _ array start stop _ predicate =>
        10 + sourceWidth +
          max 6
            (max
              (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
              (exprScratch predicate))
    | .arrayInsertIfInBoundsSlots _ _ _ array index values =>
        10 + values.length +
          max 6
            (max (exprScratch array)
              (max (exprScratch index)
                (values.foldl (fun n value => max n (exprScratch value)) 0)))
    | .arrayEraseIfInBoundsSlots _ _ array index =>
        10 + max 6 (max (exprScratch array) (exprScratch index))
    | .arraySwapIfInBoundsSlots _ _ array left right =>
        9 + max 6 (max (exprScratch array) (max (exprScratch left) (exprScratch right)))
    | .arrayReverseSlots _ _ array => 6 + max 6 (exprScratch array)
    | .byteArrayGet ptr len index =>
        3 + max (exprScratch ptr) (max (exprScratch len) (exprScratch index))
    | .byteArrayPushPtr ptr len value =>
        6 + max 6 (max (exprScratch ptr) (max (exprScratch len) (exprScratch value)))
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        7 + max 6
          (max
            (max (exprScratch leftPtr) (exprScratch leftLen))
            (max (exprScratch rightPtr) (exprScratch rightLen)))
    | .byteArraySetPtr ptr len index value =>
        6 + max 6
          (max
            (max (exprScratch ptr) (exprScratch len))
            (max (exprScratch index) (exprScratch value)))
    | .byteArrayFromArrayPtr array => 4 + max 6 (exprScratch array)
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        15 + max 6
          (max
            (max (exprScratch srcPtr) (max (exprScratch srcLen) (exprScratch srcOff)))
            (max
              (max (exprScratch destPtr) (max (exprScratch destLen) (exprScratch destOff)))
              (exprScratch copyLen)))
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        6 + max
          (max (exprScratch leftPtr) (exprScratch leftLen))
          (max (exprScratch rightPtr) (exprScratch rightLen))
    | .byteArrayFindIdx ptr len start _ predicate _ =>
        4 + max
          (max (exprScratch ptr) (max (exprScratch len) (exprScratch start)))
          (exprScratch predicate)
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues _ _ bodyValues
        bodyLets bodyDone _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
        let bodyScratch :=
          max letScratch <|
            max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        5 + resultWidth + 1 +
          max
            (max (exprScratch ptr) (exprScratch len))
            (max (max (exprScratch start) (exprScratch stop))
              (max initScratch bodyScratch))
    | .rangeFoldMultiSlot resultWidth start stop step initValues _ _ bodyValues bodyLets bodyDone _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
        let bodyScratch :=
          max letScratch <|
            max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        3 +
          max
            (max (exprScratch start) (max (exprScratch stop) (exprScratch step)))
            (max (max initScratch bodyScratch) (max (bodyScratch + resultWidth + 1) 3))
    | .heapLinearPredicate ptr _ _ _ _ predicate _ _ =>
        2 + max (exprScratch ptr) (exprScratch predicate)
    | .call _ args => args.foldl (fun count arg => max count (exprScratch arg)) 0
    | .letCall _ _ args body =>
        max (args.foldl (fun count arg => max count (exprScratch arg)) 0) (exprScratch body)
    | .letLets lets body =>
        max
          (lets.foldl (fun count item => max count (localLetScratch item)) 0)
          (exprScratch body)

  partial def localLetScratch : LocalLet → Nat
    | .expr _ value => exprScratch value
    | .call _ _ args => args.foldl (fun count arg => max count (exprScratch arg)) 0
    | .slots _ values => values.foldl (fun count value => max count (exprScratch value)) 0
    | .branch cond thenLets elseLets =>
        max (condScratch cond)
          (max
            (thenLets.foldl (fun count item => max count (localLetScratch item)) 0)
            (elseLets.foldl (fun count item => max count (localLetScratch item)) 0))

  partial def condScratch : Cond → Nat
    | .true => 0
    | .false => 0
    | .eqU64 left right => max (exprScratch left) (exprScratch right)
    | .ltU64 left right => max (exprScratch left) (exprScratch right)
    | .leU64 left right => max (exprScratch left) (exprScratch right)
    | .not cond => condScratch cond
    | .and left right => max (condScratch left) (condScratch right)
    | .or left right => max (condScratch left) (condScratch right)
end

partial def stmtScratch : Stmt → Nat
  | .skip => 0
  | .assign _ value => exprScratch value
  | .call _ _ args => args.foldl (fun count arg => max count (exprScratch arg)) 0
  | .release ptr => exprScratch ptr
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues _ _ bodyValues
      bodyLets bodyDone _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
      let bodyScratch :=
        max letScratch <|
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      5 + sourceWidth + resultWidth + 1 +
        max
          (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
          (max initScratch bodyScratch)
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues _ _ bodyValues
      bodyLets bodyDone _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
      let bodyScratch :=
        max letScratch <|
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      5 + resultWidth + 1 +
        max
          (max (exprScratch ptr) (exprScratch len))
          (max (max (exprScratch start) (exprScratch stop))
            (max initScratch bodyScratch))
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues _ _ bodyValues bodyLets bodyDone _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
      let bodyScratch :=
        max letScratch <|
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      3 +
        max
          (max (exprScratch start) (max (exprScratch stop) (exprScratch step)))
          (max (max initScratch bodyScratch) (max (bodyScratch + resultWidth + 1) 3))
  | .ite cond thenStmt elseStmt =>
      max (condScratch cond) (max (stmtScratch thenStmt) (stmtScratch elseStmt))
  | .seq first second => max (stmtScratch first) (stmtScratch second)
  | .while cond body => max (condScratch cond) (stmtScratch body)

def funcScratch (func : Func) : Nat :=
  max (stmtScratch func.body) (func.results.foldl (fun acc result => max acc (exprScratch result)) 0)

def emitCopyLoop (arrayLocal newLocal lenLocal loopLocal : Nat) : List UInt8 :=
  i64Const 0 ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
      arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

def emitCopyLoopAt
    (arrayLocal newLocal destOffsetLocal lenLocal loopLocal : Nat) : List UInt8 :=
  i64Const 0 ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress
        (localGet newLocal)
        (localGet destOffsetLocal ++ localGet loopLocal ++ ofNats [124]) ++
      arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

def emitExtractCopyLoop
    (arrayLocal newLocal startLocal lenLocal loopLocal : Nat) : List UInt8 :=
  i64Const 0 ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
      arrayCellAddress
        (localGet arrayLocal)
        (localGet startLocal ++ localGet loopLocal ++ ofNats [124]) ++
      i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

def emitRangeCopyLoop
    (arrayLocal newLocal : Nat)
    (sourceOffset destOffset : List UInt8)
    (lenLocal loopLocal : Nat) : List UInt8 :=
  i64Const 0 ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress
        (localGet newLocal)
        (destOffset ++ localGet loopLocal ++ ofNats [124]) ++
      arrayCellAddress
        (localGet arrayLocal)
        (sourceOffset ++ localGet loopLocal ++ ofNats [124]) ++
      i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

def emitByteRangeCopyLoop
    (sourcePtrLocal destPtrLocal : Nat)
    (sourceOffset destOffset len : List UInt8)
    (loopLocal : Nat) : List UInt8 :=
  i64Const 0 ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ len ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      localGet destPtrLocal ++ destOffset ++ ofNats [124] ++
        localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
      localGet sourcePtrLocal ++ sourceOffset ++ ofNats [124] ++
        localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
      i32Load8U ++ i32Store8 ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

mutual
  partial def emitArrayAllocSlots (scratch width childMask : Nat) (cells : Expr) : List UInt8 :=
    let len := scratch
    let ptr := scratch + 1
    let loopLocal := scratch + 2
    let cellCountLocal := scratch + 3
    let zeroLoop :=
      localGet len ++ i64Const width ++ ofNats [126] ++ localSet cellCountLocal ++
        i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet cellCountLocal ++ i64GeU ++
            ofNats [13] ++ u32leb 1 ++
          localGet ptr ++ i64Const 8 ++ ofNats [124] ++
            localGet loopLocal ++ i64Const 8 ++ ofNats [126, 124] ++
            i32WrapI64 ++ i64Const 0 ++ i64Store ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    emitExpr (scratch + 2) cells ++ localSet len ++
      rcAllocArrayObject (scratch + 2) width childMask (localGet len) ++ localSet ptr ++
      localGet ptr ++ i32WrapI64 ++ localGet len ++ i64Store ++
      zeroLoop ++
      localGet ptr

  partial def emitHeapAllocSlots (scratch childMask : Nat) (values : List Expr) : List UInt8 :=
    let ptrLocal := scratch
    let valueStart := scratch + 1
    let childScratch := scratch + 1 + values.length
    let rec emitValueStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, _) :: rest =>
          localGet ptrLocal ++ i64Const (offset * 8) ++ ofNats [124] ++ i32WrapI64 ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    emitValueStores (enumerate values) ++
      rcAllocSlotObject childScratch values.length childMask ++ localSet ptrLocal ++
      emitSlotStores (enumerate values) ++
      localGet ptrLocal

  partial def emitHeapLoadSlot (scratch : Nat) (ptr : Expr) (slot : Nat) : List UInt8 :=
    let ptrLocal := scratch
    emitExpr (scratch + 1) ptr ++ localSet ptrLocal ++
      localGet ptrLocal ++ i64Const (slot * 8) ++ ofNats [124] ++ i32WrapI64 ++ i64Load

  partial def emitArrayReplicateSlots
      (scratch width childMask ownedMask : Nat)
      (cells : Expr)
      (values : List Expr) : List UInt8 :=
    let lenLocal := scratch
    let ptrLocal := scratch + 1
    let loopLocal := scratch + 2
    let valueStart := scratch + 3
    let retainChildLocal := scratch + 3 + values.length
    let retainRcLocal := retainChildLocal + 1
    let childScratch := retainRcLocal + 1
    let rec emitValueStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet ptrLocal) (localGet loopLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    let fillLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
          emitSlotStores (enumerate values) ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    emitExpr childScratch cells ++ localSet lenLocal ++
      emitValueStores (enumerate values) ++
      rcAllocArrayObject childScratch width childMask (localGet lenLocal) ++ localSet ptrLocal ++
      localGet ptrLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
      fillLoop ++
      emitRetainArrayRangeWithSpecial width childMask ownedMask loopLocal retainChildLocal
        retainRcLocal (localGet ptrLocal) (i64Const 0) (localGet lenLocal) (i64Const 0) ++
      localGet ptrLocal

  partial def emitArrayGetSlot
      (scratch width slot : Nat)
      (array index : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let childScratch := scratch + 2
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet indexLocal ++ localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ i64LtU ++
      ofNats [4, 126] ++
        arraySlotAddress width slot (localGet arrayLocal) (localGet indexLocal) ++ i64Load ++
      ofNats [5] ++
        ofNats [0] ++
      ofNats [11]

  partial def emitArraySize (scratch : Nat) (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    emitExpr (scratch + 1) array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load

  partial def emitArraySetSlots
      (scratch width childMask ownedMask : Nat)
      (array index : Expr)
      (values : List Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let cellsLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let valueStart := scratch + 6
    let retainChildLocal := scratch + 6 + values.length
    let retainRcLocal := retainChildLocal + 1
    let childScratch := retainRcLocal + 1
    let rec emitValueStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet indexLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      emitValueStores (enumerate values) ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet lenLocal ++ i64Const width ++ ofNats [126] ++ localSet cellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet lenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        emitSlotStores (enumerate values) ++
        emitRetainArrayRangeWithSpecial width childMask ownedMask loopLocal retainChildLocal
          retainRcLocal (localGet newLocal) (i64Const 0) (localGet lenLocal) (localGet indexLocal) ++
        localGet newLocal ++
      ofNats [5] ++
        ofNats [0] ++
      ofNats [11]

  partial def emitArrayPushSlots
      (scratch width childMask ownedMask : Nat)
      (array : Expr)
      (values : List Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let cellsLocal := scratch + 2
    let newLenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let valueStart := scratch + 6
    let retainChildLocal := scratch + 6 + values.length
    let retainRcLocal := retainChildLocal + 1
    let childScratch := retainRcLocal + 1
    let rec emitValueStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet lenLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitValueStores (enumerate values) ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const width ++ ofNats [126] ++ localSet cellsLocal ++
      localGet lenLocal ++ i64Const 1 ++ ofNats [124] ++ localSet newLenLocal ++
      rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
      emitSlotStores (enumerate values) ++
      emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
        (localGet newLocal) (i64Const 0) (localGet lenLocal) ++
      emitRetainArraySlotsAtIndex width childMask ownedMask retainChildLocal retainRcLocal
        (localGet newLocal) (localGet lenLocal) ++
      localGet newLocal

  partial def emitArrayPopSlots (scratch width childMask : Nat) (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLenLocal := scratch + 2
    let cellsLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let retainChildLocal := scratch + 6
    let retainRcLocal := scratch + 7
    let childScratch := scratch + 8
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const 0 ++ ofNats [81] ++
      ofNats [4, 126] ++
        localGet arrayLocal ++
      ofNats [5] ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [125] ++ localSet newLenLocal ++
        localGet newLenLocal ++ i64Const width ++ ofNats [126] ++ localSet cellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet newLenLocal) ++
        localGet newLocal ++
      ofNats [11]

  partial def emitArrayAppendSlots
      (scratch width childMask : Nat)
      (left right : Expr) : List UInt8 :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let leftLenLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let newLenLocal := scratch + 4
    let leftCellsLocal := scratch + 5
    let rightCellsLocal := scratch + 6
    let newLocal := scratch + 7
    let loopLocal := scratch + 8
    let retainChildLocal := scratch + 9
    let retainRcLocal := scratch + 10
    let childScratch := scratch + 11
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ i32WrapI64 ++ i64Load ++ localSet leftLenLocal ++
      localGet rightLocal ++ i32WrapI64 ++ i64Load ++ localSet rightLenLocal ++
      localGet leftLenLocal ++ localGet rightLenLocal ++ ofNats [124] ++
        localSet newLenLocal ++
      localGet leftLenLocal ++ i64Const width ++ ofNats [126] ++ localSet leftCellsLocal ++
      localGet rightLenLocal ++ i64Const width ++ ofNats [126] ++ localSet rightCellsLocal ++
      rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      emitCopyLoop leftLocal newLocal leftCellsLocal loopLocal ++
      emitCopyLoopAt rightLocal newLocal leftCellsLocal rightCellsLocal loopLocal ++
      emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
        (localGet newLocal) (i64Const 0) (localGet leftLenLocal) ++
      emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
        (localGet newLocal) (localGet leftLenLocal) (localGet rightLenLocal) ++
      localGet newLocal

  partial def emitArrayExtractSlots
      (scratch width childMask : Nat)
      (array start stop : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let startLocal := scratch + 1
    let stopLocal := scratch + 2
    let sourceLenLocal := scratch + 3
    let stopBoundLocal := scratch + 4
    let newLenLocal := scratch + 5
    let startCellLocal := scratch + 6
    let cellsLocal := scratch + 7
    let newLocal := scratch + 8
    let loopLocal := scratch + 9
    let retainChildLocal := scratch + 10
    let retainRcLocal := scratch + 11
    let childScratch := scratch + 12
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch start ++ localSet startLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet sourceLenLocal ++
      localGet stopLocal ++ localGet sourceLenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopLocal ++
      ofNats [5] ++
        localGet sourceLenLocal ++
      ofNats [11] ++ localSet stopBoundLocal ++
      localGet startLocal ++ localGet stopBoundLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopBoundLocal ++ localGet startLocal ++ ofNats [125] ++
      ofNats [5] ++
        i64Const 0 ++
      ofNats [11] ++ localSet newLenLocal ++
      localGet startLocal ++ i64Const width ++ ofNats [126] ++ localSet startCellLocal ++
      localGet newLenLocal ++ i64Const width ++ ofNats [126] ++ localSet cellsLocal ++
      rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      emitExtractCopyLoop arrayLocal newLocal startCellLocal cellsLocal loopLocal ++
      emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
        (localGet newLocal) (i64Const 0) (localGet newLenLocal) ++
      localGet newLocal

  partial def emitArrayMapSlots
      (scratch sourceWidth resultWidth childMask ownedMask : Nat)
      (array : Expr)
      (itemStart : Nat)
      (bodyValues : List Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let retainChildLocal := scratch + 4
    let retainRcLocal := scratch + 5
    let childScratch := scratch + 6
    let rec emitSourceLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet loopLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitResultStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          arraySlotAddress resultWidth offset (localGet newLocal) (localGet loopLocal) ++
            emitExpr childScratch value ++ i64Store ++ emitResultStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      rcAllocArrayObject childScratch resultWidth childMask (localGet lenLocal) ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
      i64Const 0 ++ localSet loopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        emitResultStores (enumerate bodyValues) ++
        emitRetainArraySlotsAtIndex resultWidth childMask ownedMask retainChildLocal retainRcLocal
          (localGet newLocal) (localGet loopLocal) ++
        localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet newLocal

  partial def emitArrayFoldMultiSlot
      (scratch sourceWidth resultWidth : Nat)
      (array start stop : Expr)
      (initValues : List Expr)
      (accStart itemStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (resultSlot : Nat) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec emitSourceLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitInitStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopLocal ++
      ofNats [5] ++
        localGet lenLocal ++
      ofNats [11] ++ localSet effectiveStopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitTempCopies (List.range resultWidth) ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet (accStart + resultSlot)

  partial def emitArrayFoldMultiSlotAssign
      (scratch sourceWidth resultWidth : Nat)
      (array start stop : Expr)
      (initValues : List Expr)
      (accStart itemStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (targets : List Nat) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec emitSourceLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitInitStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let rec emitTargetCopies : List (Nat × Nat) → List UInt8
      | [] => []
      | (offset, target) :: rest =>
          localGet (accStart + offset) ++ localSet target ++ emitTargetCopies rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopLocal ++
      ofNats [5] ++
        localGet lenLocal ++
      ofNats [11] ++ localSet effectiveStopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitTempCopies (List.range resultWidth) ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      emitTargetCopies (enumerate targets)

  partial def emitArrayFindIdxSlots
      (scratch sourceWidth : Nat)
      (array : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (returnPayload : Bool) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let foundValue := if returnPayload then localGet indexLocal else i64Const 1
    let rec emitSourceLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      i64Const 0 ++ localSet indexLocal ++
      i64Const 0 ++ localSet resultLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ofNats [4, 64] ++
          foundValue ++ localSet resultLocal ++
          ofNats [12] ++ u32leb 2 ++
        ofNats [11] ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet resultLocal

  partial def emitArrayFindSlot
      (scratch sourceWidth : Nat)
      (array : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (slot : Nat) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let rec emitSourceLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      i64Const 0 ++ localSet indexLocal ++
      i64Const 0 ++ localSet resultLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ofNats [4, 64] ++
          localGet (itemStart + slot) ++ localSet resultLocal ++
          ofNats [12] ++ u32leb 2 ++
        ofNats [11] ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet resultLocal

  partial def emitArrayEqSlots
      (scratch width : Nat)
      (left right : Expr)
      (leftStart rightStart : Nat)
      (predicate : Expr) : List UInt8 :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let lenLocal := scratch + 2
    let indexLocal := scratch + 3
    let resultLocal := scratch + 4
    let childScratch := scratch + 5
    let rec emitElementLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress width offset (localGet leftLocal) (localGet indexLocal) ++
            i64Load ++ localSet (leftStart + offset) ++
          arraySlotAddress width offset (localGet rightLocal) (localGet indexLocal) ++
            i64Load ++ localSet (rightStart + offset) ++
          emitElementLoads rest
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ localGet rightLocal ++ i32WrapI64 ++ i64Load ++ i64Ne ++
      ofNats [4, 126] ++
        i64Const 0 ++
      ofNats [5] ++
        i64Const 0 ++ localSet indexLocal ++
        i64Const 1 ++ localSet resultLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
            ofNats [13] ++ u32leb 1 ++
          emitElementLoads (List.range width) ++
          emitExpr childScratch predicate ++ i64Const 0 ++ i64Eq ++
          ofNats [4, 64] ++
            i64Const 0 ++ localSet resultLocal ++
            ofNats [12] ++ u32leb 2 ++
          ofNats [11] ++
          localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11] ++
        localGet resultLocal ++
      ofNats [11]

  partial def emitArrayAnySlots
      (scratch sourceWidth : Nat)
      (array start stop : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (forAll : Bool) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let resultLocal := scratch + 5
    let childScratch := scratch + 6
    let initialResult := if forAll then i64Const 1 else i64Const 0
    let foundResult := if forAll then i64Const 0 else i64Const 1
    let predicateCondition :=
      if forAll then
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++ ofNats [69]
      else
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne
    let rec emitSourceLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      initialResult ++ localSet resultLocal ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopLocal ++
      ofNats [5] ++
        localGet lenLocal ++
      ofNats [11] ++ localSet effectiveStopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        predicateCondition ++
        ofNats [4, 64] ++
          foundResult ++ localSet resultLocal ++
          ofNats [12] ++ u32leb 2 ++
        ofNats [11] ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet resultLocal

  partial def emitArrayFilterSlots
      (scratch sourceWidth childMask : Nat)
      (array start stop : Expr)
      (itemStart : Nat)
      (predicate : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let newLocal := scratch + 5
    let writeIndexLocal := scratch + 6
    let cellsLocal := scratch + 7
    let retainChildLocal := scratch + 8
    let retainRcLocal := scratch + 9
    let childScratch := scratch + 10
    let rec emitSourceLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitResultStores : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet newLocal) (localGet writeIndexLocal) ++
            localGet (itemStart + offset) ++ i64Store ++ emitResultStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      localGet lenLocal ++ i64Const sourceWidth ++ ofNats [126] ++ localSet cellsLocal ++
      rcAllocArrayObject childScratch sourceWidth childMask (localGet lenLocal) ++ localSet newLocal ++
      i64Const 0 ++ localSet writeIndexLocal ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopLocal ++
      ofNats [5] ++
        localGet lenLocal ++
      ofNats [11] ++ localSet effectiveStopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ofNats [4, 64] ++
          emitResultStores (List.range sourceWidth) ++
          emitRetainArraySlotsAtIndex sourceWidth childMask 0 retainChildLocal retainRcLocal
            (localGet newLocal) (localGet writeIndexLocal) ++
          localGet writeIndexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet writeIndexLocal ++
        ofNats [11] ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet newLocal ++ i32WrapI64 ++ localGet writeIndexLocal ++ i64Store ++
      localGet newLocal

  partial def emitArrayInsertIfInBoundsSlots
      (scratch width childMask ownedMask : Nat)
      (array index : Expr)
      (values : List Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let prefixCellsLocal := scratch + 3
    let suffixCellsLocal := scratch + 4
    let newLenLocal := scratch + 5
    let newLocal := scratch + 6
    let loopLocal := scratch + 7
    let valueStart := scratch + 8
    let retainChildLocal := scratch + 8 + values.length
    let retainRcLocal := retainChildLocal + 1
    let childScratch := retainRcLocal + 1
    let rec emitValueStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet indexLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LeU ++
      ofNats [4, 126] ++
        emitValueStores (enumerate values) ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [124] ++ localSet newLenLocal ++
        localGet indexLocal ++ i64Const width ++ ofNats [126] ++ localSet prefixCellsLocal ++
        localGet lenLocal ++ localGet indexLocal ++ ofNats [125] ++
          i64Const width ++ ofNats [126] ++ localSet suffixCellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal prefixCellsLocal loopLocal ++
        emitSlotStores (enumerate values) ++
        emitRangeCopyLoop
          arrayLocal
          newLocal
          (localGet prefixCellsLocal)
          (localGet prefixCellsLocal ++ i64Const width ++ ofNats [124])
          suffixCellsLocal
          loopLocal ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet indexLocal) ++
        emitRetainArraySlotsAtIndex width childMask ownedMask retainChildLocal retainRcLocal
          (localGet newLocal) (localGet indexLocal) ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (localGet indexLocal ++ i64Const 1 ++ ofNats [124])
          (localGet lenLocal ++ localGet indexLocal ++ ofNats [125]) ++
        localGet newLocal ++
      ofNats [5] ++
        localGet arrayLocal ++
      ofNats [11]

  partial def emitArrayEraseIfInBoundsSlots
      (scratch width childMask : Nat)
      (array index : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let prefixCellsLocal := scratch + 3
    let suffixCellsLocal := scratch + 4
    let newLenLocal := scratch + 5
    let newLocal := scratch + 6
    let loopLocal := scratch + 7
    let retainChildLocal := scratch + 8
    let retainRcLocal := scratch + 9
    let childScratch := scratch + 10
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [125] ++ localSet newLenLocal ++
        localGet indexLocal ++ i64Const width ++ ofNats [126] ++ localSet prefixCellsLocal ++
        localGet newLenLocal ++ localGet indexLocal ++ ofNats [125] ++
          i64Const width ++ ofNats [126] ++ localSet suffixCellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal prefixCellsLocal loopLocal ++
        emitRangeCopyLoop
          arrayLocal
          newLocal
          (localGet prefixCellsLocal ++ i64Const width ++ ofNats [124])
          (localGet prefixCellsLocal)
          suffixCellsLocal
          loopLocal ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet indexLocal) ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (localGet indexLocal)
          (localGet newLenLocal ++ localGet indexLocal ++ ofNats [125]) ++
        localGet newLocal ++
      ofNats [5] ++
        localGet arrayLocal ++
      ofNats [11]

  partial def emitArraySwapIfInBoundsSlots
      (scratch width childMask : Nat)
      (array left right : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let leftLocal := scratch + 1
    let rightLocal := scratch + 2
    let lenLocal := scratch + 3
    let cellsLocal := scratch + 4
    let newLocal := scratch + 5
    let loopLocal := scratch + 6
    let retainChildLocal := scratch + 7
    let retainRcLocal := scratch + 8
    let childScratch := scratch + 9
    let rec emitSlotCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet leftLocal) ++
            arraySlotAddress width offset (localGet arrayLocal) (localGet rightLocal) ++
            i64Load ++ i64Store ++
          arraySlotAddress width offset (localGet newLocal) (localGet rightLocal) ++
            arraySlotAddress width offset (localGet arrayLocal) (localGet leftLocal) ++
            i64Load ++ i64Store ++
          emitSlotCopies rest
    let swapBody :=
      localGet lenLocal ++ i64Const width ++ ofNats [126] ++ localSet cellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet lenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        emitSlotCopies (List.range width) ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet lenLocal) ++
        localGet newLocal
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet leftLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet rightLocal ++ localGet lenLocal ++ i64LtU ++
        ofNats [4, 126] ++
          swapBody ++
        ofNats [5] ++
          localGet arrayLocal ++
        ofNats [11] ++
      ofNats [5] ++
        localGet arrayLocal ++
      ofNats [11]

  partial def emitArrayReverseSlots
      (scratch width childMask : Nat)
      (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let retainChildLocal := scratch + 4
    let retainRcLocal := scratch + 5
    let childScratch := scratch + 6
    let sourceIndex :=
      localGet lenLocal ++ localGet loopLocal ++ ofNats [125] ++ i64Const 1 ++ ofNats [125]
    let rec emitSlotCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet loopLocal) ++
            arraySlotAddress width offset (localGet arrayLocal) sourceIndex ++
            i64Load ++ i64Store ++ emitSlotCopies rest
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
          emitSlotCopies (List.range width) ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const 1 ++ i64LeU ++
      ofNats [4, 126] ++
        localGet arrayLocal ++
      ofNats [5] ++
        rcAllocArrayObject childScratch width childMask (localGet lenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        copyLoop ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet lenLocal) ++
        localGet newLocal ++
      ofNats [11]

  partial def emitByteArrayGet (scratch : Nat) (ptr len index : Expr) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let childScratch := scratch + 3
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet ptrLocal ++ localGet indexLocal ++ ofNats [124] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U ++
      ofNats [5] ++
        ofNats [0] ++
      ofNats [11]

  partial def emitByteArrayPushPtr (scratch : Nat) (ptr len value : Expr) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let valueLocal := scratch + 2
    let newPtrLocal := scratch + 3
    let newLenLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
          localGet newPtrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            localGet ptrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch value ++ localSet valueLocal ++
      localGet lenLocal ++ i64Const 1 ++ ofNats [124] ++ localSet newLenLocal ++
      rcAllocRawObject childScratch (localGet newLenLocal) ++ localSet newPtrLocal ++
      copyLoop ++
      localGet newPtrLocal ++ localGet lenLocal ++ ofNats [124] ++ i32WrapI64 ++
        localGet valueLocal ++ i32WrapI64 ++ i32Store8 ++
      localGet newPtrLocal

  partial def emitByteArrayAppendPtr
      (scratch : Nat)
      (leftPtr leftLen rightPtr rightLen : Expr) : List UInt8 :=
    let leftPtrLocal := scratch
    let leftLenLocal := scratch + 1
    let rightPtrLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let newPtrLocal := scratch + 4
    let newLenLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
    let copyLeftLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet leftLenLocal ++ i64GeU ++
            ofNats [13] ++ u32leb 1 ++
          localGet newPtrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            localGet leftPtrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    let copyRightLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet rightLenLocal ++ i64GeU ++
            ofNats [13] ++ u32leb 1 ++
          localGet newPtrLocal ++ localGet leftLenLocal ++ ofNats [124] ++
            localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            localGet rightPtrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    emitExpr childScratch leftPtr ++ localSet leftPtrLocal ++
      emitExpr childScratch leftLen ++ localSet leftLenLocal ++
      emitExpr childScratch rightPtr ++ localSet rightPtrLocal ++
      emitExpr childScratch rightLen ++ localSet rightLenLocal ++
      localGet leftLenLocal ++ localGet rightLenLocal ++ ofNats [124] ++ localSet newLenLocal ++
      rcAllocRawObject childScratch (localGet newLenLocal) ++ localSet newPtrLocal ++
      copyLeftLoop ++
      copyRightLoop ++
      localGet newPtrLocal

  partial def emitByteArraySetPtr
      (scratch : Nat)
      (ptr len index value : Expr) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let valueLocal := scratch + 3
    let newPtrLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
          localGet newPtrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            localGet ptrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      emitExpr childScratch value ++ localSet valueLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        rcAllocRawObject childScratch (localGet lenLocal) ++ localSet newPtrLocal ++
        copyLoop ++
        localGet newPtrLocal ++ localGet indexLocal ++ ofNats [124] ++ i32WrapI64 ++
          localGet valueLocal ++ i32WrapI64 ++ i32Store8 ++
        localGet newPtrLocal ++
      ofNats [5] ++
        ofNats [0] ++
      ofNats [11]

  partial def emitByteArrayFromArrayPtr (scratch : Nat) (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newPtrLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
          localGet newPtrLocal ++ localGet loopLocal ++ ofNats [124] ++ i32WrapI64 ++
            arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++
            i32WrapI64 ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11]
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      rcAllocRawObject childScratch (localGet lenLocal) ++ localSet newPtrLocal ++
      copyLoop ++
      localGet newPtrLocal

  partial def emitByteArrayCopySlicePtr
      (scratch : Nat)
      (srcPtr srcLen srcOff destPtr destLen destOff copyLen : Expr) : List UInt8 :=
    let srcPtrLocal := scratch
    let srcLenLocal := scratch + 1
    let srcOffLocal := scratch + 2
    let destPtrLocal := scratch + 3
    let destLenLocal := scratch + 4
    let destOffLocal := scratch + 5
    let requestedLenLocal := scratch + 6
    let availableLocal := scratch + 7
    let copiedLenLocal := scratch + 8
    let prefixLenLocal := scratch + 9
    let suffixStartLocal := scratch + 10
    let suffixLenLocal := scratch + 11
    let newLenLocal := scratch + 12
    let newPtrLocal := scratch + 13
    let loopLocal := scratch + 14
    let childScratch := scratch + 15
    emitExpr childScratch srcPtr ++ localSet srcPtrLocal ++
      emitExpr childScratch srcLen ++ localSet srcLenLocal ++
      emitExpr childScratch srcOff ++ localSet srcOffLocal ++
      emitExpr childScratch destPtr ++ localSet destPtrLocal ++
      emitExpr childScratch destLen ++ localSet destLenLocal ++
      emitExpr childScratch destOff ++ localSet destOffLocal ++
      emitExpr childScratch copyLen ++ localSet requestedLenLocal ++
      localGet srcOffLocal ++ localGet srcLenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet srcLenLocal ++ localGet srcOffLocal ++ ofNats [125] ++
      ofNats [5] ++
        i64Const 0 ++
      ofNats [11] ++ localSet availableLocal ++
      localGet requestedLenLocal ++ localGet availableLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet requestedLenLocal ++
      ofNats [5] ++
        localGet availableLocal ++
      ofNats [11] ++ localSet copiedLenLocal ++
      localGet destOffLocal ++ localGet destLenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet destOffLocal ++
      ofNats [5] ++
        localGet destLenLocal ++
      ofNats [11] ++ localSet prefixLenLocal ++
      localGet destOffLocal ++ localGet copiedLenLocal ++ ofNats [124] ++ localSet suffixStartLocal ++
      localGet suffixStartLocal ++ localGet destLenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet destLenLocal ++ localGet suffixStartLocal ++ ofNats [125] ++
      ofNats [5] ++
        i64Const 0 ++
      ofNats [11] ++ localSet suffixLenLocal ++
      localGet prefixLenLocal ++ localGet copiedLenLocal ++ ofNats [124] ++
        localGet suffixLenLocal ++ ofNats [124] ++ localSet newLenLocal ++
      rcAllocRawObject childScratch (localGet newLenLocal) ++ localSet newPtrLocal ++
      emitByteRangeCopyLoop
        destPtrLocal
        newPtrLocal
        (i64Const 0)
        (i64Const 0)
        (localGet prefixLenLocal)
        loopLocal ++
      emitByteRangeCopyLoop
        srcPtrLocal
        newPtrLocal
        (localGet srcOffLocal)
        (localGet prefixLenLocal)
        (localGet copiedLenLocal)
        loopLocal ++
      emitByteRangeCopyLoop
        destPtrLocal
        newPtrLocal
        (localGet suffixStartLocal)
        (localGet prefixLenLocal ++ localGet copiedLenLocal ++ ofNats [124])
        (localGet suffixLenLocal)
        loopLocal ++
      localGet newPtrLocal

  partial def emitByteArrayEq
      (scratch : Nat)
      (leftPtr leftLen rightPtr rightLen : Expr) : List UInt8 :=
    let leftPtrLocal := scratch
    let leftLenLocal := scratch + 1
    let rightPtrLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let indexLocal := scratch + 4
    let resultLocal := scratch + 5
    let childScratch := scratch + 6
    emitExpr childScratch leftPtr ++ localSet leftPtrLocal ++
      emitExpr childScratch leftLen ++ localSet leftLenLocal ++
      emitExpr childScratch rightPtr ++ localSet rightPtrLocal ++
      emitExpr childScratch rightLen ++ localSet rightLenLocal ++
      localGet leftLenLocal ++ localGet rightLenLocal ++ i64Ne ++
      ofNats [4, 126] ++
        i64Const 0 ++
      ofNats [5] ++
        i64Const 0 ++ localSet indexLocal ++
        i64Const 1 ++ localSet resultLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet indexLocal ++ localGet leftLenLocal ++ i64GeU ++
            ofNats [13] ++ u32leb 1 ++
          localGet leftPtrLocal ++ localGet indexLocal ++ ofNats [124] ++ i32WrapI64 ++
            i32Load8U ++ i64ExtendI32U ++
          localGet rightPtrLocal ++ localGet indexLocal ++ ofNats [124] ++ i32WrapI64 ++
            i32Load8U ++ i64ExtendI32U ++
          i64Ne ++
          ofNats [4, 64] ++
            i64Const 0 ++ localSet resultLocal ++
            ofNats [12] ++ u32leb 2 ++
          ofNats [11] ++
          localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11] ++
        localGet resultLocal ++
      ofNats [11]

  partial def emitByteArrayFindIdx
      (scratch : Nat)
      (ptr len start : Expr)
      (byteSlot : Nat)
      (predicate : Expr)
      (returnPayload : Bool) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let foundValue := if returnPayload then localGet indexLocal else i64Const 1
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      i64Const 0 ++ localSet resultLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        localGet ptrLocal ++ localGet indexLocal ++ ofNats [124] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U ++ localSet byteSlot ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ofNats [4, 64] ++
          foundValue ++ localSet resultLocal ++
          ofNats [12] ++ u32leb 2 ++
        ofNats [11] ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet resultLocal

  partial def emitByteArrayFoldMultiSlot
      (scratch resultWidth : Nat)
      (ptr len start stop : Expr)
      (initValues : List Expr)
      (accStart byteSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (resultSlot : Nat) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec emitInitStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopLocal ++
      ofNats [5] ++
        localGet lenLocal ++
      ofNats [11] ++ localSet effectiveStopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        localGet ptrLocal ++ localGet indexLocal ++ ofNats [124] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U ++ localSet byteSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitTempCopies (List.range resultWidth) ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet (accStart + resultSlot)

  partial def emitByteArrayFoldMultiSlotAssign
      (scratch resultWidth : Nat)
      (ptr len start stop : Expr)
      (initValues : List Expr)
      (accStart byteSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (targets : List Nat) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec emitInitStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let rec emitTargetCopies : List (Nat × Nat) → List UInt8
      | [] => []
      | (offset, target) :: rest =>
          localGet (accStart + offset) ++ localSet target ++ emitTargetCopies rest
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet stopLocal ++
      ofNats [5] ++
        localGet lenLocal ++
      ofNats [11] ++ localSet effectiveStopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        localGet ptrLocal ++ localGet indexLocal ++ ofNats [124] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U ++ localSet byteSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitTempCopies (List.range resultWidth) ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      emitTargetCopies (enumerate targets)

  partial def emitCheckedDivMod
      (scratch : Nat)
      (op : LeanExe.IR.U64Op)
      (left right : Expr) : List UInt8 :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    let zeroValue :=
      match op with
      | .divU => i64Const 0
      | .modU => localGet leftLocal
      | _ => i64Const 0
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet rightLocal ++ i64Const 0 ++ ofNats [81] ++
      ofNats [4, 126] ++
        zeroValue ++
      ofNats [5] ++
        localGet leftLocal ++ localGet rightLocal ++ emitU64Op op ++
      ofNats [11]

  partial def emitNatAdd
      (scratch : Nat)
      (left right : Expr) : List UInt8 :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let resultLocal := scratch + 2
    let childScratch := scratch + 3
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ localGet rightLocal ++ ofNats [124] ++ localTee resultLocal ++
      localGet leftLocal ++ i64LtU ++
      ofNats [4, 126] ++
        ofNats [0] ++
      ofNats [5] ++
        localGet resultLocal ++
      ofNats [11]

  partial def emitNatMul
      (scratch : Nat)
      (left right : Expr) : List UInt8 :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet rightLocal ++ i64Const 0 ++ ofNats [81] ++
      ofNats [4, 126] ++
        i64Const 0 ++
      ofNats [5] ++
        i64Const (2 ^ 64 - 1) ++ localGet rightLocal ++ ofNats [128] ++
          localGet leftLocal ++ i64LtU ++
        ofNats [4, 126] ++
          ofNats [0] ++
        ofNats [5] ++
          localGet leftLocal ++ localGet rightLocal ++ ofNats [126] ++
        ofNats [11] ++
      ofNats [11]

  partial def emitNatSub
      (scratch : Nat)
      (left right : Expr) : List UInt8 :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ localGet rightLocal ++ i64LtU ++
      ofNats [4, 126] ++
        i64Const 0 ++
      ofNats [5] ++
        localGet leftLocal ++ localGet rightLocal ++ ofNats [125] ++
      ofNats [11]

  partial def emitRangeFoldMultiSlot
      (scratch resultWidth : Nat)
      (start stop step : Expr)
      (initValues : List Expr)
      (accStart itemSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (resultSlot : Nat) : List UInt8 :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec emitInitStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitExpr childScratch step ++ localSet stepLocal ++
      emitInitStores (enumerate initValues) ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet stopLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        localGet indexLocal ++ localSet itemSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitTempCopies (List.range resultWidth) ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
        emitExpr childScratch (.u64Bin .natAdd (.local indexLocal) (.local stepLocal)) ++
          localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet (accStart + resultSlot)

  partial def emitRangeFoldMultiSlotAssign
      (scratch resultWidth : Nat)
      (start stop step : Expr)
      (initValues : List Expr)
      (accStart itemSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (targets : List Nat) : List UInt8 :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec emitInitStores : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List UInt8
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let rec emitTargetCopies : List (Nat × Nat) → List UInt8
      | [] => []
      | (offset, target) :: rest =>
          localGet (accStart + offset) ++ localSet target ++ emitTargetCopies rest
    emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitExpr childScratch step ++ localSet stepLocal ++
      emitInitStores (enumerate initValues) ++
      ofNats [2, 64, 3, 64] ++
        localGet indexLocal ++ localGet stopLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        localGet indexLocal ++ localSet itemSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitTempCopies (List.range resultWidth) ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
        emitExpr childScratch (.u64Bin .natAdd (.local indexLocal) (.local stepLocal)) ++
          localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      emitTargetCopies (enumerate targets)

  partial def emitHeapLinearPredicate
      (scratch : Nat)
      (ptr : Expr)
      (continueTag fieldSlotCount recursiveFieldOffset fieldStart : Nat)
      (predicate : Expr)
      (stopWhenTrue terminalValue : Bool) : List UInt8 :=
    let ptrLocal := scratch
    let resultLocal := scratch + 1
    let childScratch := scratch + 2
    let rec emitFieldLoads : List Nat → List UInt8
      | [] => []
      | offset :: rest =>
          localGet ptrLocal ++ i64Const ((1 + offset) * 8) ++ ofNats [124] ++
            i32WrapI64 ++ i64Load ++ localSet (fieldStart + offset) ++
            emitFieldLoads rest
    let stopCond :=
      emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        (if stopWhenTrue then [] else ofNats [69])
    let stopValue := if stopWhenTrue then 1 else 0
    let terminal := if terminalValue then 1 else 0
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      i64Const terminal ++ localSet resultLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet ptrLocal ++ i64Const 0 ++ ofNats [124] ++ i32WrapI64 ++ i64Load ++
          i64Const continueTag ++ i64Ne ++ ofNats [13] ++ u32leb 1 ++
        emitFieldLoads (List.range fieldSlotCount) ++
        stopCond ++ ofNats [4, 64] ++
          i64Const stopValue ++ localSet resultLocal ++ ofNats [12] ++ u32leb 2 ++
        ofNats [11] ++
        localGet (fieldStart + recursiveFieldOffset) ++ localSet ptrLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet resultLocal

  partial def emitExpr (scratch : Nat) : Expr → List UInt8
    | .local index => localGet index
    | .trap => ofNats [0]
    | .u64 value => i64Const value
    | .u64Bin .natAdd left right => emitNatAdd scratch left right
    | .u64Bin .natSub left right => emitNatSub scratch left right
    | .u64Bin .natMul left right => emitNatMul scratch left right
    | .u64Bin .divU left right => emitCheckedDivMod scratch .divU left right
    | .u64Bin .modU left right => emitCheckedDivMod scratch .modU left right
    | .u64Bin op left right => emitExpr scratch left ++ emitExpr scratch right ++ emitU64Op op
    | .ite cond thenValue elseValue =>
        emitCond scratch cond ++ ofNats [4, 126] ++ emitExpr scratch thenValue ++ ofNats [5] ++
          emitExpr scratch elseValue ++ ofNats [11]
    | .letE slot value body => emitExpr scratch value ++ localSet slot ++ emitExpr scratch body
    | .arrayAllocSlots width childMask cells => emitArrayAllocSlots scratch width childMask cells
    | .runtimeStat stat => globalGet (runtimeStatGlobal stat)
    | .release ptr => emitExpr scratch ptr ++ unreachable
    | .heapAllocSlots childMask values => emitHeapAllocSlots scratch childMask values
    | .heapLoadSlot ptr slot => emitHeapLoadSlot scratch ptr slot
    | .arrayReplicateSlots width childMask ownedMask cells values =>
        emitArrayReplicateSlots scratch width childMask ownedMask cells values
    | .arraySize array => emitArraySize scratch array
    | .arrayGetSlot width slot array index => emitArrayGetSlot scratch width slot array index
    | .arraySetSlots width childMask ownedMask array index values =>
        emitArraySetSlots scratch width childMask ownedMask array index values
    | .arrayPushSlots width childMask ownedMask array values =>
        emitArrayPushSlots scratch width childMask ownedMask array values
    | .arrayPopSlots width childMask array => emitArrayPopSlots scratch width childMask array
    | .arrayAppendSlots width childMask left right =>
        emitArrayAppendSlots scratch width childMask left right
    | .arrayExtractSlots width childMask array start stop =>
        emitArrayExtractSlots scratch width childMask array start stop
    | .arrayMapSlots sourceWidth resultWidth childMask ownedMask array itemStart bodyValues =>
        emitArrayMapSlots scratch sourceWidth resultWidth childMask ownedMask array itemStart bodyValues
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
        bodyValues bodyLets bodyDone resultSlot =>
        emitArrayFoldMultiSlot scratch sourceWidth resultWidth array start stop initValues accStart
          itemStart bodyValues bodyLets bodyDone resultSlot
    | .arrayFindIdxSlots sourceWidth array itemStart predicate returnPayload =>
        emitArrayFindIdxSlots scratch sourceWidth array itemStart predicate returnPayload
    | .arrayFindSlot sourceWidth array itemStart predicate slot =>
        emitArrayFindSlot scratch sourceWidth array itemStart predicate slot
    | .arrayEqSlots width left right leftStart rightStart predicate =>
        emitArrayEqSlots scratch width left right leftStart rightStart predicate
    | .arrayAnySlots sourceWidth array start stop itemStart predicate forAll =>
        emitArrayAnySlots scratch sourceWidth array start stop itemStart predicate forAll
    | .arrayFilterSlots sourceWidth childMask array start stop itemStart predicate =>
        emitArrayFilterSlots scratch sourceWidth childMask array start stop itemStart predicate
    | .arrayInsertIfInBoundsSlots width childMask ownedMask array index values =>
        emitArrayInsertIfInBoundsSlots scratch width childMask ownedMask array index values
    | .arrayEraseIfInBoundsSlots width childMask array index =>
        emitArrayEraseIfInBoundsSlots scratch width childMask array index
    | .arraySwapIfInBoundsSlots width childMask array left right =>
        emitArraySwapIfInBoundsSlots scratch width childMask array left right
    | .arrayReverseSlots width childMask array => emitArrayReverseSlots scratch width childMask array
    | .byteArrayGet ptr len index => emitByteArrayGet scratch ptr len index
    | .byteArrayPushPtr ptr len value => emitByteArrayPushPtr scratch ptr len value
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        emitByteArrayAppendPtr scratch leftPtr leftLen rightPtr rightLen
    | .byteArraySetPtr ptr len index value =>
        emitByteArraySetPtr scratch ptr len index value
    | .byteArrayFromArrayPtr array => emitByteArrayFromArrayPtr scratch array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        emitByteArrayCopySlicePtr scratch srcPtr srcLen srcOff destPtr destLen destOff copyLen
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        emitByteArrayEq scratch leftPtr leftLen rightPtr rightLen
    | .byteArrayFindIdx ptr len start byteSlot predicate returnPayload =>
        emitByteArrayFindIdx scratch ptr len start byteSlot predicate returnPayload
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone resultSlot =>
        emitByteArrayFoldMultiSlot scratch resultWidth ptr len start stop initValues accStart
          byteSlot bodyValues bodyLets bodyDone resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone resultSlot =>
        emitRangeFoldMultiSlot scratch resultWidth start stop step initValues accStart itemSlot
          bodyValues bodyLets bodyDone resultSlot
    | .heapLinearPredicate ptr continueTag fieldSlotCount recursiveFieldOffset fieldStart predicate
        stopWhenTrue terminalValue =>
        emitHeapLinearPredicate scratch ptr continueTag fieldSlotCount recursiveFieldOffset fieldStart
          predicate stopWhenTrue terminalValue
    | .call index args => args.flatMap (emitExpr scratch) ++ call index
    | .letCall slots index args body =>
        args.flatMap (emitExpr scratch) ++ call index ++
          slots.reverse.flatMap localSet ++ emitExpr scratch body
    | .letLets lets body =>
        lets.flatMap (emitLocalLet scratch) ++ emitExpr scratch body

  partial def emitSlotsAssign (scratch : Nat) (slots : List Nat) (values : List Expr) :
      List UInt8 :=
    match values with
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
        bodyValues bodyLets bodyDone _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart
                itemStart bodyValues bodyLets bodyDone offset
                : Expr)
          if values == expected then
            emitArrayFoldMultiSlotAssign scratch sourceWidth resultWidth array start stop initValues
              accStart itemStart bodyValues bodyLets bodyDone slots
          else
            (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
        else
          (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart
                byteSlot bodyValues bodyLets bodyDone offset
                : Expr)
          if values == expected then
            emitByteArrayFoldMultiSlotAssign scratch resultWidth ptr len start stop initValues
              accStart byteSlot bodyValues bodyLets bodyDone slots
          else
            (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
        else
          (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot
                bodyValues bodyLets bodyDone offset
                : Expr)
          if values == expected then
            emitRangeFoldMultiSlotAssign scratch resultWidth start stop step initValues accStart
              itemSlot bodyValues bodyLets bodyDone slots
          else
            (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
        else
          (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
    | _ =>
        (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst

  partial def emitLocalLet (scratch : Nat) : LocalLet → List UInt8
    | .expr slot value => emitExpr scratch value ++ localSet slot
    | .call slots index args =>
        args.flatMap (emitExpr scratch) ++ call index ++ slots.reverse.flatMap localSet
    | .slots slots values => emitSlotsAssign scratch slots values
    | .branch cond thenLets elseLets =>
        emitCond scratch cond ++ ofNats [4, 64] ++
          thenLets.flatMap (emitLocalLet scratch) ++
          ofNats [5] ++
          elseLets.flatMap (emitLocalLet scratch) ++
          ofNats [11]

  partial def emitCond (scratch : Nat) : Cond → List UInt8
    | .true => ofNats [65, 1]
    | .false => ofNats [65, 0]
    | .eqU64 left right => emitExpr scratch left ++ emitExpr scratch right ++ ofNats [81]
    | .ltU64 left right => emitExpr scratch left ++ emitExpr scratch right ++ i64LtU
    | .leU64 left right => emitExpr scratch left ++ emitExpr scratch right ++ i64LeU
    | .not cond => emitCond scratch cond ++ ofNats [69]
    | .and left right =>
        emitCond scratch left ++ ofNats [4, 127] ++
          emitCond scratch right ++
        ofNats [5, 65, 0, 11]
    | .or left right =>
        emitCond scratch left ++ ofNats [4, 127, 65, 1, 5] ++
          emitCond scratch right ++
        ofNats [11]
end

mutual
partial def emitExprWithRelease (releaseIndex scratch : Nat) : Expr → List UInt8
  | .local index => localGet index
  | .trap => unreachable
  | .u64 value => i64Const value
  | .u64Bin .natAdd left right =>
      emitNatAddWithRelease releaseIndex scratch left right
  | .u64Bin .natSub left right =>
      emitNatSubWithRelease releaseIndex scratch left right
  | .u64Bin .natMul left right =>
      emitNatMulWithRelease releaseIndex scratch left right
  | .u64Bin .divU left right =>
      emitCheckedDivModWithRelease releaseIndex scratch .divU left right
  | .u64Bin .modU left right =>
      emitCheckedDivModWithRelease releaseIndex scratch .modU left right
  | .u64Bin op left right =>
      emitExprWithRelease releaseIndex scratch left ++
        emitExprWithRelease releaseIndex scratch right ++ emitU64Op op
  | .ite cond thenValue elseValue =>
      emitCondWithRelease releaseIndex scratch cond ++ ofNats [4, 126] ++
        emitExprWithRelease releaseIndex scratch thenValue ++ ofNats [5] ++
        emitExprWithRelease releaseIndex scratch elseValue ++ ofNats [11]
  | .letE slot value body =>
      emitExprWithRelease releaseIndex scratch value ++ localSet slot ++
        emitExprWithRelease releaseIndex scratch body
  | .letCall slots index args body =>
      args.flatMap (emitExprWithRelease releaseIndex scratch) ++ call index ++
        slots.reverse.flatMap localSet ++ emitExprWithRelease releaseIndex scratch body
  | .runtimeStat stat => globalGet (runtimeStatGlobal stat)
  | .release ptr =>
      emitExprWithRelease releaseIndex scratch ptr ++ call releaseIndex ++
        globalGet (runtimeStatGlobal .frees)
  | expr => emitExpr scratch expr

partial def emitCondWithRelease (releaseIndex scratch : Nat) : Cond → List UInt8
  | .true => ofNats [65, 1]
  | .false => ofNats [65, 0]
  | .eqU64 left right =>
      emitExprWithRelease releaseIndex scratch left ++
        emitExprWithRelease releaseIndex scratch right ++ ofNats [81]
  | .ltU64 left right =>
      emitExprWithRelease releaseIndex scratch left ++
        emitExprWithRelease releaseIndex scratch right ++ i64LtU
  | .leU64 left right =>
      emitExprWithRelease releaseIndex scratch left ++
        emitExprWithRelease releaseIndex scratch right ++ i64LeU
  | .not cond => emitCondWithRelease releaseIndex scratch cond ++ ofNats [69]
  | .and left right =>
      emitCondWithRelease releaseIndex scratch left ++ ofNats [4, 127] ++
        emitCondWithRelease releaseIndex scratch right ++
      ofNats [5, 65, 0, 11]
  | .or left right =>
      emitCondWithRelease releaseIndex scratch left ++ ofNats [4, 127, 65, 1, 5] ++
        emitCondWithRelease releaseIndex scratch right ++
      ofNats [11]

partial def emitCheckedDivModWithRelease
    (releaseIndex scratch : Nat)
    (op : LeanExe.IR.U64Op)
    (left right : Expr) : List UInt8 :=
  let leftLocal := scratch
  let rightLocal := scratch + 1
  let childScratch := scratch + 2
  let zeroValue :=
    match op with
    | .divU => i64Const 0
    | .modU => localGet leftLocal
    | _ => i64Const 0
  emitExprWithRelease releaseIndex childScratch left ++ localSet leftLocal ++
    emitExprWithRelease releaseIndex childScratch right ++ localSet rightLocal ++
    localGet rightLocal ++ i64Const 0 ++ ofNats [81] ++
    ofNats [4, 126] ++
      zeroValue ++
    ofNats [5] ++
      localGet leftLocal ++ localGet rightLocal ++ emitU64Op op ++
    ofNats [11]

partial def emitNatAddWithRelease
    (releaseIndex scratch : Nat)
    (left right : Expr) : List UInt8 :=
  let leftLocal := scratch
  let rightLocal := scratch + 1
  let resultLocal := scratch + 2
  let childScratch := scratch + 3
  emitExprWithRelease releaseIndex childScratch left ++ localSet leftLocal ++
    emitExprWithRelease releaseIndex childScratch right ++ localSet rightLocal ++
    localGet leftLocal ++ localGet rightLocal ++ ofNats [124] ++ localTee resultLocal ++
    localGet leftLocal ++ i64LtU ++
    ofNats [4, 126] ++
      ofNats [0] ++
    ofNats [5] ++
      localGet resultLocal ++
    ofNats [11]

partial def emitNatMulWithRelease
    (releaseIndex scratch : Nat)
    (left right : Expr) : List UInt8 :=
  let leftLocal := scratch
  let rightLocal := scratch + 1
  let childScratch := scratch + 2
  emitExprWithRelease releaseIndex childScratch left ++ localSet leftLocal ++
    emitExprWithRelease releaseIndex childScratch right ++ localSet rightLocal ++
    localGet rightLocal ++ i64Const 0 ++ ofNats [81] ++
    ofNats [4, 126] ++
      i64Const 0 ++
    ofNats [5] ++
      i64Const (2 ^ 64 - 1) ++ localGet rightLocal ++ ofNats [128] ++
        localGet leftLocal ++ i64LtU ++
      ofNats [4, 126] ++
        ofNats [0] ++
      ofNats [5] ++
        localGet leftLocal ++ localGet rightLocal ++ ofNats [126] ++
      ofNats [11] ++
    ofNats [11]

partial def emitNatSubWithRelease
    (releaseIndex scratch : Nat)
    (left right : Expr) : List UInt8 :=
  let leftLocal := scratch
  let rightLocal := scratch + 1
  let childScratch := scratch + 2
  emitExprWithRelease releaseIndex childScratch left ++ localSet leftLocal ++
    emitExprWithRelease releaseIndex childScratch right ++ localSet rightLocal ++
    localGet leftLocal ++ localGet rightLocal ++ i64LtU ++
    ofNats [4, 126] ++
      i64Const 0 ++
    ofNats [5] ++
      localGet leftLocal ++ localGet rightLocal ++ ofNats [125] ++
    ofNats [11]
end

partial def emitStmt (releaseIndex scratch : Nat) : Stmt → List UInt8
  | .skip => []
  | .assign index value => emitExprWithRelease releaseIndex scratch value ++ localSet index
  | .call slots index args =>
      args.flatMap (emitExprWithRelease releaseIndex scratch) ++ call index ++
        slots.reverse.flatMap localSet
  | .release ptr => emitExprWithRelease releaseIndex scratch ptr ++ call releaseIndex
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart itemStart
      bodyValues bodyLets bodyDone targets =>
      emitArrayFoldMultiSlotAssign scratch sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyLets bodyDone targets
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyLets bodyDone targets =>
      emitByteArrayFoldMultiSlotAssign scratch resultWidth ptr len start stop initValues accStart
        byteSlot bodyValues bodyLets bodyDone targets
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot bodyValues
      bodyLets bodyDone targets =>
      emitRangeFoldMultiSlotAssign scratch resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyLets bodyDone targets
  | .ite cond thenStmt elseStmt =>
      emitCondWithRelease releaseIndex scratch cond ++ ofNats [4, 64] ++
        emitStmt releaseIndex scratch thenStmt ++
        ofNats [5] ++
        emitStmt releaseIndex scratch elseStmt ++
        ofNats [11]
  | .seq first second => emitStmt releaseIndex scratch first ++ emitStmt releaseIndex scratch second
  | .while cond loopBody =>
      ofNats [2, 64, 3, 64] ++
      emitCond scratch cond ++ ofNats [69, 13, 1] ++
      emitStmt releaseIndex scratch loopBody ++
      ofNats [12, 0, 11, 11]

def localDecls (func : Func) : List UInt8 :=
  let extra := func.locals - func.params + funcScratch func
  if extra == 0 then
    ofNats [0]
  else
    u32leb 1 ++ u32leb extra ++ ofNats [126]

def emitFuncBody (releaseIndex : Nat) (func : Func) : List UInt8 :=
  let scratch := func.locals
  body (localDecls func)
    (emitStmt releaseIndex scratch func.body ++ func.results.flatMap (emitExpr scratch))

def typeForFunc (func : Func) : List UInt8 :=
  funcType (List.replicate func.params i64) (List.replicate func.results.length i64)

def typeSection (module_ : Module) : List UInt8 :=
  wasmSection 1 <| vec (
    module_.funcs.toList.map typeForFunc ++
      [funcType [i64] [i64], funcType [] [], funcType [i64] [i64], funcType [i64] []])

def functionSection (module_ : Module) : List UInt8 :=
  wasmSection 3 <| u32Vec (List.range (module_.funcs.size + 4))

def exportSection (module_ : Module) : List UInt8 :=
  wasmSection 7 <| vec <|
    [exportEntry "memory" 2 0] ++
      (enumerate module_.funcs.toList |>.filterMap fun item =>
        item.snd.exportName.map (fun exportName => exportEntry exportName 0 item.fst)) ++
      [exportEntry "alloc" 0 module_.funcs.size,
        exportEntry "reset" 0 (module_.funcs.size + 1),
        exportEntry "retain" 0 (module_.funcs.size + 2),
        exportEntry "release" 0 (module_.funcs.size + 3),
        exportEntry "free" 0 (module_.funcs.size + 3)]

def coreAllocBody : List UInt8 :=
  body
    (ofNats [1, 6, 126])
    (rcAllocRawObject 1 (localGet 0))

def coreResetBody : List UInt8 :=
  body
    (ofNats [0])
    (i64Const 4096 ++ globalSet 0 ++
      i64Const 0 ++ globalSet 1 ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .allocs) ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .retains) ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .releases) ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .frees))

def coreRetainBody : List UInt8 :=
  let rcLocal := 1
  body
    (ofNats [1, 1, 126])
    (localGet 0 ++ i64Const 0 ++ i64Ne ++
      ofNats [4, 64] ++
        rcHeaderLoad (localGet 0) 48 ++ i64Const rcMagic ++ i64Ne ++
          ofNats [4, 64] ++ unreachable ++ ofNats [11] ++
      rcHeaderLoad (localGet 0) 40 ++ localSet rcLocal ++
      localGet rcLocal ++ i64Const 0 ++ i64Eq ++
        ofNats [4, 64] ++ unreachable ++ ofNats [11] ++
        incGlobal (runtimeStatGlobal .retains) ++
        rcHeaderStore (localGet 0) 40 (localGet rcLocal ++ i64Const 1 ++ ofNats [124]) ++
      ofNats [11] ++
      localGet 0)

def coreReleaseBody (releaseIndex : Nat) : List UInt8 :=
  let rcLocal := 1
  let kindLocal := 2
  let limitLocal := 3
  let widthLocal := 4
  let maskLocal := 5
  let slotLocal := 6
  let itemLocal := 7
  let childLocal := 8
  let callReleaseChild := localGet childLocal ++ call releaseIndex
  let slotReleaseLoop :=
    i64Const 0 ++ localSet slotLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet slotLocal ++ localGet limitLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        localGet maskLocal ++ localGet slotLocal ++ i64ShrU ++ i64Const 1 ++ i64And ++
          i64Const 0 ++ i64Ne ++
          ofNats [4, 64] ++
            localGet 0 ++ localGet slotLocal ++ i64Const 8 ++ ofNats [126, 124] ++
              i32WrapI64 ++ i64Load ++ localSet childLocal ++
            callReleaseChild ++
          ofNats [11] ++
        localGet slotLocal ++ i64Const 1 ++ ofNats [124] ++ localSet slotLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11]
  let arrayReleaseLoop :=
    localGet 0 ++ i32WrapI64 ++ i64Load ++ localSet limitLocal ++
      rcHeaderLoad (localGet 0) 16 ++ localSet widthLocal ++
      rcHeaderLoad (localGet 0) 8 ++ localSet maskLocal ++
      i64Const 0 ++ localSet itemLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet itemLocal ++ localGet limitLocal ++ i64GeU ++
          ofNats [13] ++ u32leb 1 ++
        i64Const 0 ++ localSet slotLocal ++
        ofNats [2, 64, 3, 64] ++
          localGet slotLocal ++ localGet widthLocal ++ i64GeU ++
            ofNats [13] ++ u32leb 1 ++
          localGet maskLocal ++ localGet slotLocal ++ i64ShrU ++ i64Const 1 ++ i64And ++
            i64Const 0 ++ i64Ne ++
            ofNats [4, 64] ++
              localGet 0 ++ i64Const 8 ++ ofNats [124] ++
                localGet itemLocal ++ localGet widthLocal ++ ofNats [126] ++
                localGet slotLocal ++ ofNats [124] ++ i64Const 8 ++ ofNats [126, 124] ++
                i32WrapI64 ++ i64Load ++ localSet childLocal ++
              callReleaseChild ++
            ofNats [11] ++
          localGet slotLocal ++ i64Const 1 ++ ofNats [124] ++ localSet slotLocal ++
          ofNats [12] ++ u32leb 0 ++
        ofNats [11, 11] ++
        localGet itemLocal ++ i64Const 1 ++ ofNats [124] ++ localSet itemLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11]
  let freeCurrent :=
    incGlobal (runtimeStatGlobal .frees) ++
      rcHeaderStore (localGet 0) 40 (i64Const 0) ++
      rcHeaderStore (localGet 0) 8 (globalGet 1) ++
      localGet 0 ++ globalSet 1
  body
    (ofNats [1, 8, 126])
    (localGet 0 ++ i64Const 0 ++ i64Eq ++
      ofNats [4, 64] ++ returnOp ++ ofNats [11] ++
      rcHeaderLoad (localGet 0) 48 ++ i64Const rcMagic ++ i64Ne ++
        ofNats [4, 64] ++ unreachable ++ ofNats [11] ++
      rcHeaderLoad (localGet 0) 40 ++ localSet rcLocal ++
      localGet rcLocal ++ i64Const 0 ++ i64Eq ++
        ofNats [4, 64] ++ unreachable ++ ofNats [11] ++
      incGlobal (runtimeStatGlobal .releases) ++
      i64Const 1 ++ localGet rcLocal ++ i64LtU ++
        ofNats [4, 64] ++
          rcHeaderStore (localGet 0) 40 (localGet rcLocal ++ i64Const 1 ++ ofNats [125]) ++
          returnOp ++
        ofNats [11] ++
      rcHeaderLoad (localGet 0) 24 ++ localSet kindLocal ++
      localGet kindLocal ++ i64Const rcKindSlots ++ i64Eq ++
        ofNats [4, 64] ++
          rcHeaderLoad (localGet 0) 16 ++ localSet limitLocal ++
          rcHeaderLoad (localGet 0) 8 ++ localSet maskLocal ++
          slotReleaseLoop ++
        ofNats [11] ++
      localGet kindLocal ++ i64Const rcKindArray ++ i64Eq ++
        ofNats [4, 64] ++
          arrayReleaseLoop ++
        ofNats [11] ++
      freeCurrent)

def codeSection (module_ : Module) : List UInt8 :=
  let releaseIndex := module_.funcs.size + 3
  wasmSection 10 <| vec (
    module_.funcs.toList.map (emitFuncBody releaseIndex) ++
      [coreAllocBody, coreResetBody, coreRetainBody, coreReleaseBody releaseIndex])

def moduleBytes (module_ : Module) : ByteArray :=
  ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
    ++ typeSection module_
    ++ functionSection module_
    ++ coreMemorySection
    ++ coreGlobalSection
    ++ exportSection module_
    ++ codeSection module_).toArray

def importEntry (moduleName fieldName : String) (typeIndex : Nat) : List UInt8 :=
  name moduleName ++ name fieldName ++ ofNats [0] ++ u32leb typeIndex

def wasiImportSection : List UInt8 :=
  wasmSection 2 <| vec [
    importEntry "wasi_snapshot_preview1" "fd_write" 0
  ]

def wasiStdinImportSection : List UInt8 :=
  wasmSection 2 <| vec [
    importEntry "wasi_snapshot_preview1" "fd_write" 0,
    importEntry "wasi_snapshot_preview1" "fd_read" 0
  ]

def wasiStdinExceptImportSection : List UInt8 :=
  wasmSection 2 <| vec [
    importEntry "wasi_snapshot_preview1" "fd_write" 0,
    importEntry "wasi_snapshot_preview1" "fd_read" 0,
    importEntry "wasi_snapshot_preview1" "proc_exit" 1
  ]

def wasiArgvExceptImportSection : List UInt8 :=
  wasmSection 2 <| vec [
    importEntry "wasi_snapshot_preview1" "fd_write" 0,
    importEntry "wasi_snapshot_preview1" "args_sizes_get" 1,
    importEntry "wasi_snapshot_preview1" "args_get" 1,
    importEntry "wasi_snapshot_preview1" "proc_exit" 2
  ]

def wasiStdinArgvExceptImportSection : List UInt8 :=
  wasmSection 2 <| vec [
    importEntry "wasi_snapshot_preview1" "fd_write" 0,
    importEntry "wasi_snapshot_preview1" "fd_read" 0,
    importEntry "wasi_snapshot_preview1" "args_sizes_get" 1,
    importEntry "wasi_snapshot_preview1" "args_get" 1,
    importEntry "wasi_snapshot_preview1" "proc_exit" 2
  ]

def wasiFdIoType : List UInt8 :=
  funcType [i32, i32, i32, i32] [i32]

def wasiArgsType : List UInt8 :=
  funcType [i32, i32] [i32]

def wasiProcExitType : List UInt8 :=
  funcType [i32] []

def wasiStartType : List UInt8 :=
  funcType [] []

def wasiTypeSectionWithImportTypes (importTypes : List (List UInt8)) (module_ : Module) :
    List UInt8 :=
  wasmSection 1 <| vec (
    importTypes ++
      module_.funcs.toList.map typeForFunc ++
      [wasiStartType, funcType [i64] []])

def wasiTypeSection (module_ : Module) : List UInt8 :=
  wasiTypeSectionWithImportTypes [wasiFdIoType] module_

def wasiFunctionSectionWithImportTypes (importTypeCount : Nat) (module_ : Module) : List UInt8 :=
  wasmSection 3 <|
    u32Vec ((List.range (module_.funcs.size + 2)).map (fun index => index + importTypeCount))

def wasiFunctionSection (module_ : Module) : List UInt8 :=
  wasiFunctionSectionWithImportTypes 1 module_

def wasiExportSection (module_ : Module) (importCount : Nat) : List UInt8 :=
  wasmSection 7 <| vec [
    exportEntry "memory" 2 0,
    exportEntry "_start" 0 (module_.funcs.size + importCount)
  ]

def entryFuncIndex? (module_ : Module) : Option Nat :=
  let rec loop (index : Nat) : Option Nat :=
    if h : index < module_.funcs.size then
      if module_.funcs[index].exportName.isSome then
        some index
      else
        loop (index + 1)
    else
      none
  loop 0

def funcIndexBySourceName? (module_ : Module) (sourceName : Lean.Name) : Option Nat :=
  let rec loop (index : Nat) : Option Nat :=
    if h : index < module_.funcs.size then
      if module_.funcs[index].sourceName == sourceName then
        some index
      else
        loop (index + 1)
    else
      none
  loop 0

def wasiWriteFd (fd ptrLocal lenLocal fdWriteIndex : Nat) : List UInt8 :=
  i32Const 0 ++ localGet ptrLocal ++ i32WrapI64 ++ i32Store ++
    i32Const 4 ++ localGet lenLocal ++ i32WrapI64 ++ i32Store ++
    i32Const 8 ++ i32Const 0 ++ i32Store ++
    i32Const fd ++ i32Const 0 ++ i32Const 1 ++ i32Const 8 ++ call fdWriteIndex ++
    ofNats [69, 4, 64] ++
      i32Const 8 ++ i32Load ++ localGet lenLocal ++ i32WrapI64 ++ i32Eq ++
      ofNats [4, 64, 5, 0, 11, 5, 0, 11]

def wasiWriteStdout (ptrLocal lenLocal fdWriteIndex : Nat) : List UInt8 :=
  wasiWriteFd 1 ptrLocal lenLocal fdWriteIndex

def wasiStdoutStartBody (entryIndex : Nat) : List UInt8 :=
  body
    (ofNats [1, 2, 126])
    (call entryIndex ++
      localSet 1 ++
      localSet 0 ++
      wasiWriteStdout 0 1 0)

def wasiCodeSection (module_ : Module) (entryIndex : Nat) : List UInt8 :=
  let shifted := shiftModuleCalls 1 module_
  let releaseIndex := module_.funcs.size + 2
  wasmSection 10 <| vec (
    shifted.funcs.toList.map (emitFuncBody releaseIndex) ++
      [wasiStdoutStartBody (entryIndex + 1), coreReleaseBody releaseIndex])

def wasiMemoryBytes : Nat :=
  16 * 65536

def wasiInputStart : Nat :=
  4096

def wasiMaxInputBytes : Nat :=
  wasiMemoryBytes - wasiInputStart - 1

def wasiMaxReservedBytes : Nat :=
  wasiMemoryBytes - wasiInputStart

def wasiArgvReservedBytes (maxArgs maxArgBytes : Nat) : Nat :=
  8 + maxArgs * 24 + (maxArgs + 1) * 4 + maxArgBytes

def wasiReadStdinLoop (maxInput : Nat) : List UInt8 :=
  ofNats [2, 64, 3, 64] ++
    i64Const (maxInput + 1) ++ localGet 1 ++ ofNats [125] ++ localSet 2 ++
    i32Const 0 ++ localGet 0 ++ localGet 1 ++ ofNats [124] ++ i32WrapI64 ++ i32Store ++
    i32Const 4 ++ localGet 2 ++ i32WrapI64 ++ i32Store ++
    i32Const 8 ++ i32Const 0 ++ i32Store ++
    i32Const 0 ++ i32Const 0 ++ i32Const 1 ++ i32Const 8 ++ call 1 ++
    ofNats [69, 4, 64, 5, 0, 11] ++
    i32Const 8 ++ i32Load ++ i64ExtendI32U ++ localSet 3 ++
    localGet 3 ++ i64Const 0 ++ i64Eq ++ ofNats [13] ++ u32leb 1 ++
    localGet 1 ++ localGet 3 ++ ofNats [124] ++ localSet 1 ++
    i64Const maxInput ++ localGet 1 ++ i64LtU ++ ofNats [4, 64, 0, 11] ++
    ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11]

def wasiReadArgvArrayWithImports
    (argsSizesGetIndex argsGetIndex maxArgs maxArgBytes : Nat) :
    List UInt8 :=
  let arrayBytes := 8 + maxArgs * 24
  let tableBytes := (maxArgs + 1) * 4
  let reservedBytes := wasiArgvReservedBytes maxArgs maxArgBytes
  i64Align8 (globalGet 0) ++ localSet 0 ++
    localGet 0 ++ i64Const arrayBytes ++ ofNats [124] ++ localSet 1 ++
    localGet 1 ++ i64Const tableBytes ++ ofNats [124] ++ localSet 2 ++
    localGet 0 ++ i64Const reservedBytes ++ ofNats [124] ++ globalSet 0 ++
    i32Const 16 ++ i32Const 20 ++ call argsSizesGetIndex ++
    ofNats [69, 4, 64, 5, 0, 11] ++
    i32Const 16 ++ i32Load ++ i64ExtendI32U ++ localSet 3 ++
    i32Const 20 ++ i32Load ++ i64ExtendI32U ++ localSet 4 ++
    i64Const (maxArgs + 1) ++ localGet 3 ++ i64LtU ++ ofNats [4, 64, 0, 11] ++
    i64Const maxArgBytes ++ localGet 4 ++ i64LtU ++ ofNats [4, 64, 0, 11] ++
    localGet 3 ++ i64Const 0 ++ i64Eq ++ ofNats [4, 64] ++
      i64Const 0 ++ localSet 5 ++
    ofNats [5] ++
      localGet 3 ++ i64Const 1 ++ ofNats [125] ++ localSet 5 ++
    ofNats [11] ++
    localGet 0 ++ i32WrapI64 ++ localGet 5 ++ i64Store ++
    localGet 1 ++ i32WrapI64 ++ localGet 2 ++ i32WrapI64 ++ call argsGetIndex ++
    ofNats [69, 4, 64, 5, 0, 11] ++
    i64Const 0 ++ localSet 6 ++
    ofNats [2, 64, 3, 64] ++
      localGet 6 ++ localGet 5 ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      localGet 1 ++ localGet 6 ++ i64Const 1 ++ ofNats [124] ++ i64Const 4 ++ ofNats [126, 124] ++
        i32WrapI64 ++ i32Load ++ i64ExtendI32U ++ localSet 7 ++
      i64Const 0 ++ localSet 8 ++
      ofNats [2, 64, 3, 64] ++
        localGet 7 ++ localGet 8 ++ ofNats [124] ++ i32WrapI64 ++ i32Load8U ++
          ofNats [69, 13] ++ u32leb 1 ++
        localGet 8 ++ i64Const 1 ++ ofNats [124] ++ localSet 8 ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      arraySlotAddress 3 0 (localGet 0) (localGet 6) ++ i64Const 0 ++ i64Store ++
      arraySlotAddress 3 1 (localGet 0) (localGet 6) ++ localGet 7 ++ i64Store ++
      arraySlotAddress 3 2 (localGet 0) (localGet 6) ++ localGet 8 ++ i64Store ++
      localGet 6 ++ i64Const 1 ++ ofNats [124] ++ localSet 6 ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

def wasiReadArgvArray (maxArgs maxArgBytes : Nat) : List UInt8 :=
  wasiReadArgvArrayWithImports 1 2 maxArgs maxArgBytes

def wasiStdinStartBody (maxInput entryIndex : Nat) : List UInt8 :=
  body
    (ofNats [1, 4, 126])
    (globalGet 0 ++ localSet 0 ++
      i64Align8 (localGet 0 ++ i64Const (maxInput + 1) ++ ofNats [124]) ++ globalSet 0 ++
      i64Const 0 ++ localSet 1 ++
      wasiReadStdinLoop maxInput ++
      localGet 0 ++ localGet 1 ++ call entryIndex ++
      localSet 1 ++
      localSet 0 ++
      wasiWriteStdout 0 1 0)

def wasiStdinExceptStartBody (maxInput entryIndex : Nat) : List UInt8 :=
  body
    (ofNats [1, 9, 126])
    (globalGet 0 ++ localSet 0 ++
      i64Align8 (localGet 0 ++ i64Const (maxInput + 1) ++ ofNats [124]) ++ globalSet 0 ++
      i64Const 0 ++ localSet 1 ++
      wasiReadStdinLoop maxInput ++
      localGet 0 ++ localGet 1 ++ call entryIndex ++
      localSet 8 ++
      localSet 7 ++
      localSet 6 ++
      localSet 5 ++
      localSet 4 ++
      localGet 4 ++ i64Const 0 ++ i64Eq ++ ofNats [4, 64] ++
        wasiWriteFd 2 5 6 0 ++
        i32Const 1 ++ call 2 ++
      ofNats [5] ++
        localGet 4 ++ i64Const 1 ++ i64Eq ++ ofNats [4, 64] ++
          wasiWriteStdout 7 8 0 ++
        ofNats [5, 0, 11] ++
      ofNats [11])

def wasiArgvExceptStartBody (maxArgs maxArgBytes entryIndex : Nat) : List UInt8 :=
  body
    (ofNats [1, 16, 126])
    (wasiReadArgvArray maxArgs maxArgBytes ++
      localGet 0 ++ call entryIndex ++
      localSet 15 ++
      localSet 14 ++
      localSet 13 ++
      localSet 12 ++
      localSet 11 ++
      localSet 10 ++
      localSet 9 ++
      localGet 9 ++ i64Const 0 ++ i64Eq ++ ofNats [4, 64] ++
        wasiWriteFd 2 11 12 0 ++
        i32Const 1 ++ call 3 ++
      ofNats [5] ++
        localGet 9 ++ i64Const 1 ++ i64Eq ++ ofNats [4, 64] ++
          wasiWriteStdout 14 15 0 ++
        ofNats [5, 0, 11] ++
      ofNats [11])

def wasiStdinArgvExceptStartBody
    (maxInput maxArgs maxArgBytes entryIndex : Nat) :
    List UInt8 :=
  body
    (ofNats [1, 16, 126])
    (globalGet 0 ++ localSet 0 ++
      i64Align8 (localGet 0 ++ i64Const (maxInput + 1) ++ ofNats [124]) ++ globalSet 0 ++
      i64Const 0 ++ localSet 1 ++
      wasiReadStdinLoop maxInput ++
      localGet 0 ++ localSet 14 ++
      localGet 1 ++ localSet 15 ++
      wasiReadArgvArrayWithImports 2 3 maxArgs maxArgBytes ++
      i64Const 0 ++ localGet 14 ++ localGet 15 ++ localGet 0 ++ call entryIndex ++
      localSet 15 ++
      localSet 14 ++
      localSet 13 ++
      localSet 12 ++
      localSet 11 ++
      localSet 10 ++
      localSet 9 ++
      localGet 9 ++ i64Const 0 ++ i64Eq ++ ofNats [4, 64] ++
        wasiWriteFd 2 11 12 0 ++
        i32Const 1 ++ call 4 ++
      ofNats [5] ++
        localGet 9 ++ i64Const 1 ++ i64Eq ++ ofNats [4, 64] ++
          wasiWriteStdout 14 15 0 ++
        ofNats [5, 0, 11] ++
      ofNats [11])

def wasiStdinCodeSection (maxInput : Nat) (module_ : Module) (entryIndex : Nat) : List UInt8 :=
  let shifted := shiftModuleCalls 2 module_
  let releaseIndex := module_.funcs.size + 3
  wasmSection 10 <| vec (
    shifted.funcs.toList.map (emitFuncBody releaseIndex) ++
      [wasiStdinStartBody maxInput (entryIndex + 2), coreReleaseBody releaseIndex])

def wasiStdinExceptCodeSection (maxInput : Nat) (module_ : Module) (entryIndex : Nat) :
    List UInt8 :=
  let shifted := shiftModuleCalls 3 module_
  let releaseIndex := module_.funcs.size + 4
  wasmSection 10 <| vec (
    shifted.funcs.toList.map (emitFuncBody releaseIndex) ++
      [wasiStdinExceptStartBody maxInput (entryIndex + 3), coreReleaseBody releaseIndex])

def wasiArgvExceptCodeSection
    (maxArgs maxArgBytes : Nat)
    (module_ : Module)
    (entryIndex : Nat) :
    List UInt8 :=
  let shifted := shiftModuleCalls 4 module_
  let releaseIndex := module_.funcs.size + 5
  wasmSection 10 <| vec (
    shifted.funcs.toList.map (emitFuncBody releaseIndex) ++
      [wasiArgvExceptStartBody maxArgs maxArgBytes (entryIndex + 4), coreReleaseBody releaseIndex])

def wasiStdinArgvExceptCodeSection
    (maxInput maxArgs maxArgBytes : Nat)
    (module_ : Module)
    (entryIndex : Nat) :
    List UInt8 :=
  let shifted := shiftModuleCalls 5 module_
  let releaseIndex := module_.funcs.size + 6
  wasmSection 10 <| vec (
    shifted.funcs.toList.map (emitFuncBody releaseIndex) ++
      [wasiStdinArgvExceptStartBody maxInput maxArgs maxArgBytes (entryIndex + 5),
        coreReleaseBody releaseIndex])

def wasiModuleBytes (module_ : Module) : Except String ByteArray := do
  let entryIndex ←
    match entryFuncIndex? module_ with
    | some index => .ok index
    | none => .error "program module has no exported entry function"
  .ok <| ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
    ++ wasiTypeSection module_
    ++ wasiImportSection
    ++ wasiFunctionSection module_
    ++ coreMemorySection
    ++ coreGlobalSection
    ++ wasiExportSection module_ 1
    ++ wasiCodeSection module_ entryIndex).toArray

def wasiStdinModuleBytes (maxInput : Nat) (module_ : Module) : Except String ByteArray := do
  if maxInput > wasiMaxInputBytes then
    .error s!"max input bytes exceeds WASM memory capacity: {maxInput}"
  else
    let entryIndex ←
      match entryFuncIndex? module_ with
      | some index => .ok index
      | none => .error "program module has no exported entry function"
    .ok <| ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
      ++ wasiTypeSection module_
      ++ wasiStdinImportSection
      ++ wasiFunctionSection module_
      ++ coreMemorySection
      ++ coreGlobalSection
      ++ wasiExportSection module_ 2
      ++ wasiStdinCodeSection maxInput module_ entryIndex).toArray

def wasiStdinExceptModuleBytes (maxInput : Nat) (module_ : Module) : Except String ByteArray := do
  if maxInput > wasiMaxInputBytes then
    .error s!"max input bytes exceeds WASM memory capacity: {maxInput}"
  else
    let entryIndex ←
      match entryFuncIndex? module_ with
      | some index => .ok index
      | none => .error "program module has no exported entry function"
    .ok <| ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
      ++ wasiTypeSectionWithImportTypes [wasiFdIoType, wasiProcExitType] module_
      ++ wasiStdinExceptImportSection
      ++ wasiFunctionSectionWithImportTypes 2 module_
      ++ coreMemorySection
      ++ coreGlobalSection
      ++ wasiExportSection module_ 3
      ++ wasiStdinExceptCodeSection maxInput module_ entryIndex).toArray

def wasiArgvExceptModuleBytes
    (maxArgs maxArgBytes : Nat)
    (entryName : Lean.Name)
    (module_ : Module) :
    Except String ByteArray := do
  let reservedBytes := wasiArgvReservedBytes maxArgs maxArgBytes
  if reservedBytes > wasiMaxReservedBytes then
    .error s!"max argv storage exceeds WASM memory capacity: {reservedBytes}"
  else
    let entryIndex ←
      match funcIndexBySourceName? module_ entryName with
      | some index => .ok index
      | none => .error "program module has no selected entry function"
    .ok <| ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
      ++ wasiTypeSectionWithImportTypes [wasiFdIoType, wasiArgsType, wasiProcExitType] module_
      ++ wasiArgvExceptImportSection
      ++ wasiFunctionSectionWithImportTypes 3 module_
      ++ coreMemorySection
      ++ coreGlobalSection
      ++ wasiExportSection module_ 4
      ++ wasiArgvExceptCodeSection maxArgs maxArgBytes module_ entryIndex).toArray

def wasiStdinArgvExceptModuleBytes
    (maxInput maxArgs maxArgBytes : Nat)
    (entryName : Lean.Name)
    (module_ : Module) :
    Except String ByteArray := do
  let reservedBytes := wasiArgvReservedBytes maxArgs maxArgBytes
  if maxInput > wasiMaxInputBytes then
    .error s!"max input bytes exceeds WASM memory capacity: {maxInput}"
  else if maxInput + 8 + reservedBytes > wasiMaxReservedBytes then
    .error s!"max stdin and argv storage exceeds WASM memory capacity: {maxInput + 8 + reservedBytes}"
  else
    let entryIndex ←
      match funcIndexBySourceName? module_ entryName with
      | some index => .ok index
      | none => .error "program module has no selected entry function"
    .ok <| ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
      ++ wasiTypeSectionWithImportTypes [wasiFdIoType, wasiArgsType, wasiProcExitType] module_
      ++ wasiStdinArgvExceptImportSection
      ++ wasiFunctionSectionWithImportTypes 3 module_
      ++ coreMemorySection
      ++ coreGlobalSection
      ++ wasiExportSection module_ 5
      ++ wasiStdinArgvExceptCodeSection maxInput maxArgs maxArgBytes module_ entryIndex).toArray

def indent (spaces : Nat) (lines : List String) : List String :=
  let pad := String.ofList (List.replicate spaces ' ')
  lines.map (fun line => pad ++ line)

def arrayCellAddressWat (base index : List String) : List String :=
  base ++ index ++ ["i64.const 1", "i64.add", "i64.const 8", "i64.mul", "i64.add", "i32.wrap_i64"]

def arraySlotAddressWat (width slot : Nat) (base index : List String) : List String :=
  base ++ index ++ [s!"i64.const {width}", "i64.mul", s!"i64.const {slot + 1}",
    "i64.add", "i64.const 8", "i64.mul", "i64.add", "i32.wrap_i64"]

def copyLoopWat (arrayLocal newLocal lenLocal loopLocal : Nat) : List String :=
  [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
      arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {loopLocal}"] ++
      ["i64.load align=8", "i64.store align=8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

def copyLoopAtWat
    (arrayLocal newLocal destOffsetLocal lenLocal loopLocal : Nat) : List String :=
  [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat
        [s!"local.get {newLocal}"]
        [s!"local.get {destOffsetLocal}", s!"local.get {loopLocal}", "i64.add"] ++
      arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {loopLocal}"] ++
      ["i64.load align=8", "i64.store align=8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

def extractCopyLoopWat
    (arrayLocal newLocal startLocal lenLocal loopLocal : Nat) : List String :=
  [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
      arrayCellAddressWat
        [s!"local.get {arrayLocal}"]
        [s!"local.get {startLocal}", s!"local.get {loopLocal}", "i64.add"] ++
      ["i64.load align=8", "i64.store align=8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

def rangeCopyLoopWat
    (arrayLocal newLocal : Nat)
    (sourceOffset destOffset : List String)
    (lenLocal loopLocal : Nat) : List String :=
  [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat
        [s!"local.get {newLocal}"]
        (destOffset ++ [s!"local.get {loopLocal}", "i64.add"]) ++
      arrayCellAddressWat
        [s!"local.get {arrayLocal}"]
        (sourceOffset ++ [s!"local.get {loopLocal}", "i64.add"]) ++
      ["i64.load align=8", "i64.store align=8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

def byteRangeCopyLoopWat
    (sourcePtrLocal destPtrLocal : Nat)
    (sourceOffset destOffset len : List String)
    (loopLocal : Nat) : List String :=
  [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}"] ++ len ++ ["i64.ge_u", "br_if 1",
        s!"local.get {destPtrLocal}"] ++ destOffset ++ ["i64.add",
        s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        s!"local.get {sourcePtrLocal}"] ++ sourceOffset ++ ["i64.add",
        s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i32.store8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

mutual
  partial def arrayAllocSlotsWatLines (scratch width _childMask : Nat) (cells : Expr) : List String :=
    let len := scratch
    let ptr := scratch + 1
    let loopLocal := scratch + 2
    let cellCountLocal := scratch + 3
    let zeroLoop :=
      [s!"local.get {len}", s!"i64.const {width}", "i64.mul", s!"local.set {cellCountLocal}",
        "i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
        indent 4
          [s!"local.get {loopLocal}", s!"local.get {cellCountLocal}", "i64.ge_u", "br_if 1",
            s!"local.get {ptr}", "i64.const 8", "i64.add",
            s!"local.get {loopLocal}", "i64.const 8", "i64.mul", "i64.add",
            "i32.wrap_i64", "i64.const 0", "i64.store align=8",
            s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
            "br 0"] ++
        ["  end", "end"]
    exprWatLines (scratch + 2) cells ++
      [s!"local.set {len}", "global.get 0", s!"local.set {ptr}",
        s!"local.get {ptr}", "i32.wrap_i64", s!"local.get {len}", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {len}", s!"i64.const {width}",
        "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      zeroLoop ++
      [s!"local.get {ptr}"]

  partial def heapAllocSlotsWatLines (scratch _childMask : Nat) (values : List Expr) : List String :=
    let ptrLocal := scratch
    let valueStart := scratch + 1
    let childScratch := scratch + 1 + values.length
    let rec valueStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++ [s!"local.set {valueStart + offset}"] ++
            valueStores rest
    let rec slotStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, _) :: rest =>
          [s!"local.get {ptrLocal}", s!"i64.const {offset * 8}", "i64.add", "i32.wrap_i64",
            s!"local.get {valueStart + offset}", "i64.store align=8"] ++
            slotStores rest
    valueStores (enumerate values) ++
      ["global.get 0", s!"local.set {ptrLocal}"] ++
      slotStores (enumerate values) ++
      ["global.get 0", s!"i64.const {values.length * 8}", "i64.add", "global.set 0",
        s!"local.get {ptrLocal}"]

  partial def heapLoadSlotWatLines (scratch : Nat) (ptr : Expr) (slot : Nat) : List String :=
    let ptrLocal := scratch
    exprWatLines (scratch + 1) ptr ++ [s!"local.set {ptrLocal}",
      s!"local.get {ptrLocal}", s!"i64.const {slot * 8}", "i64.add", "i32.wrap_i64",
      "i64.load align=8"]

  partial def arrayReplicateSlotsWatLines
      (scratch width _childMask _ownedMask : Nat)
      (cells : Expr)
      (values : List Expr) : List String :=
    let lenLocal := scratch
    let ptrLocal := scratch + 1
    let loopLocal := scratch + 2
    let valueStart := scratch + 3
    let childScratch := scratch + 3 + values.length
    let rec valueStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++ [s!"local.set {valueStart + offset}"] ++
            valueStores rest
    let rec slotStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddressWat width offset [s!"local.get {ptrLocal}"] [s!"local.get {loopLocal}"] ++
            [s!"local.get {valueStart + offset}", "i64.store align=8"] ++
            slotStores rest
    let fillLoop :=
      [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
        indent 4 (
          [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
          slotStores (enumerate values) ++
          [s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
            "br 0"]) ++
        ["  end", "end"]
    exprWatLines childScratch cells ++ [s!"local.set {lenLocal}"] ++
      valueStores (enumerate values) ++
      ["global.get 0", s!"local.set {ptrLocal}",
        s!"local.get {ptrLocal}", "i32.wrap_i64", s!"local.get {lenLocal}", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {lenLocal}", s!"i64.const {width}",
        "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      fillLoop ++
      [s!"local.get {ptrLocal}"]

  partial def arrayGetSlotWatLines
      (scratch width slot : Nat)
      (array index : Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let childScratch := scratch + 2
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}",
        s!"local.get {indexLocal}", s!"local.get {arrayLocal}", "i32.wrap_i64",
        "i64.load align=8", "i64.lt_u", "if (result i64)"] ++
      indent 2 (arraySlotAddressWat width slot
        [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
        ["i64.load align=8"]) ++
      ["else", "  unreachable", "end"]

  partial def arraySizeWatLines (scratch : Nat) (array : Expr) : List String :=
    let arrayLocal := scratch
    exprWatLines (scratch + 1) array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8"]

  partial def arraySetSlotsWatLines
      (scratch width _childMask _ownedMask : Nat)
      (array index : Expr)
      (values : List Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let cellsLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let valueStart := scratch + 6
    let childScratch := scratch + 6 + values.length
    let rec valueStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {valueStart + offset}"] ++ valueStores rest
    let rec slotStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddressWat width offset
            [s!"local.get {newLocal}"] [s!"local.get {indexLocal}"] ++
          [s!"local.get {valueStart + offset}", "i64.store align=8"] ++
          slotStores rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}"] ++
      valueStores (enumerate values) ++
      [s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {lenLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)"] ++
      indent 2 (
        [s!"local.get {lenLocal}", s!"i64.const {width}", "i64.mul",
          s!"local.set {cellsLocal}",
          "global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {cellsLocal}", "i64.const 8",
          "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        copyLoopWat arrayLocal newLocal cellsLocal loopLocal ++
        slotStores (enumerate values) ++
        [s!"local.get {newLocal}"]) ++
      ["else", "  unreachable", "end"]

  partial def arrayPushSlotsWatLines
      (scratch width _childMask _ownedMask : Nat)
      (array : Expr)
      (values : List Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let cellsLocal := scratch + 2
    let newLenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let valueStart := scratch + 6
    let childScratch := scratch + 6 + values.length
    let rec valueStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {valueStart + offset}"] ++ valueStores rest
    let rec slotStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddressWat width offset
            [s!"local.get {newLocal}"] [s!"local.get {lenLocal}"] ++
          [s!"local.get {valueStart + offset}", "i64.store align=8"] ++
          slotStores rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      valueStores (enumerate values) ++
      [s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {lenLocal}",
        s!"local.get {lenLocal}", s!"i64.const {width}", "i64.mul",
        s!"local.set {cellsLocal}",
        s!"local.get {lenLocal}", "i64.const 1", "i64.add", s!"local.set {newLenLocal}",
        "global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
        "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", s!"i64.const {width}",
        "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      copyLoopWat arrayLocal newLocal cellsLocal loopLocal ++
      slotStores (enumerate values) ++
      [s!"local.get {newLocal}"]

  partial def arrayPopSlotsWatLines (scratch width _childMask : Nat) (array : Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLenLocal := scratch + 2
    let cellsLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8", s!"local.set {lenLocal}",
      s!"local.get {lenLocal}", "i64.const 0", "i64.eq", "if (result i64)"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["else"] ++
      indent 2 (
        [s!"local.get {lenLocal}", "i64.const 1", "i64.sub", s!"local.set {newLenLocal}",
          s!"local.get {newLenLocal}", s!"i64.const {width}", "i64.mul",
          s!"local.set {cellsLocal}",
          "global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {cellsLocal}", "i64.const 8",
          "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        copyLoopWat arrayLocal newLocal cellsLocal loopLocal ++
        [s!"local.get {newLocal}"]) ++
      ["end"]

  partial def arrayAppendSlotsWatLines
      (scratch width _childMask : Nat)
      (left right : Expr) : List String :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let leftLenLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let newLenLocal := scratch + 4
    let leftCellsLocal := scratch + 5
    let rightCellsLocal := scratch + 6
    let newLocal := scratch + 7
    let loopLocal := scratch + 8
    let childScratch := scratch + 9
    exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
        s!"local.get {leftLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {leftLenLocal}",
        s!"local.get {rightLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {rightLenLocal}",
        s!"local.get {leftLenLocal}", s!"local.get {rightLenLocal}", "i64.add",
        s!"local.set {newLenLocal}",
        s!"local.get {leftLenLocal}", s!"i64.const {width}", "i64.mul",
        s!"local.set {leftCellsLocal}",
        s!"local.get {rightLenLocal}", s!"i64.const {width}", "i64.mul",
        s!"local.set {rightCellsLocal}",
        "global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
        "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", s!"i64.const {width}",
        "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      copyLoopWat leftLocal newLocal leftCellsLocal loopLocal ++
      copyLoopAtWat rightLocal newLocal leftCellsLocal rightCellsLocal loopLocal ++
      [s!"local.get {newLocal}"]

  partial def arrayExtractSlotsWatLines
      (scratch width _childMask : Nat)
      (array start stop : Expr) : List String :=
    let arrayLocal := scratch
    let startLocal := scratch + 1
    let stopLocal := scratch + 2
    let sourceLenLocal := scratch + 3
    let stopBoundLocal := scratch + 4
    let newLenLocal := scratch + 5
    let startCellLocal := scratch + 6
    let cellsLocal := scratch + 7
    let newLocal := scratch + 8
    let loopLocal := scratch + 9
    let childScratch := scratch + 10
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {startLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {sourceLenLocal}",
        s!"local.get {stopLocal}", s!"local.get {sourceLenLocal}", "i64.lt_u",
        "if (result i64)",
        s!"  local.get {stopLocal}",
        "else",
        s!"  local.get {sourceLenLocal}",
        "end",
        s!"local.set {stopBoundLocal}",
        s!"local.get {startLocal}", s!"local.get {stopBoundLocal}", "i64.lt_u",
        "if (result i64)",
        s!"  local.get {stopBoundLocal}", s!"  local.get {startLocal}", "  i64.sub",
        "else",
        "  i64.const 0",
        "end",
        s!"local.set {newLenLocal}",
        s!"local.get {startLocal}", s!"i64.const {width}", "i64.mul",
        s!"local.set {startCellLocal}",
        s!"local.get {newLenLocal}", s!"i64.const {width}", "i64.mul",
        s!"local.set {cellsLocal}",
        "global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
        "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {cellsLocal}", "i64.const 8",
        "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      extractCopyLoopWat arrayLocal newLocal startCellLocal cellsLocal loopLocal ++
      [s!"local.get {newLocal}"]

  partial def arrayMapSlotsWatLines
      (scratch sourceWidth resultWidth _childMask _ownedMask : Nat)
      (array : Expr)
      (itemStart : Nat)
      (bodyValues : List Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    let rec sourceLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {arrayLocal}"] [s!"local.get {loopLocal}"] ++
            ["i64.load align=8", s!"local.set {itemStart + offset}"] ++ sourceLoads rest
    let rec resultStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          arraySlotAddressWat resultWidth offset [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
            exprWatLines childScratch value ++ ["i64.store align=8"] ++ resultStores rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}",
      "global.get 0", s!"local.set {newLocal}",
      s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}",
      "i64.store align=8",
      "global.get 0", "i64.const 8", s!"local.get {lenLocal}", s!"i64.const {resultWidth}",
      "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0",
      "i64.const 0", s!"local.set {loopLocal}",
      "block", "  loop",
      s!"    local.get {loopLocal}", s!"    local.get {lenLocal}", "    i64.ge_u",
      "    br_if 1"] ++
      indent 4 (
        sourceLoads (List.range sourceWidth) ++
        resultStores (enumerate bodyValues) ++
        [s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {newLocal}"]

  partial def arrayFoldMultiSlotWatLines
      (scratch sourceWidth resultWidth : Nat)
      (array start stop : Expr)
      (initValues : List Expr)
      (accStart itemStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (resultSlot : Nat) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec sourceLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {itemStart + offset}"] ++ sourceLoads rest
    let rec initStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {accStart + offset}"] ++ initStores rest
    let rec bodyStages : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {tempStart + offset}"] ++ bodyStages rest
    let rec tempCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          [s!"local.get {tempStart + offset}", s!"local.set {accStart + offset}"] ++
            tempCopies rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}"] ++
      initStores (enumerate initValues) ++
      [s!"local.get {stopLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {stopLocal}", "else",
        s!"  local.get {lenLocal}", "end", s!"local.set {effectiveStopLocal}",
        "block", "  loop",
        s!"    local.get {indexLocal}", s!"    local.get {effectiveStopLocal}", "    i64.ge_u",
        "    br_if 1"] ++
      indent 4 (
        sourceLoads (List.range sourceWidth) ++
        bodyLets.flatMap (localLetWatLines childScratch) ++
        bodyStages (enumerate bodyValues) ++
        exprWatLines childScratch bodyDone ++
        [s!"local.set {doneSlot}"] ++
        tempCopies (List.range resultWidth) ++
        [s!"local.get {doneSlot}", "i64.const 0", "i64.ne", "br_if 1"] ++
        [s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {accStart + resultSlot}"]

  partial def arrayFoldMultiSlotAssignWatLines
      (scratch sourceWidth resultWidth : Nat)
      (array start stop : Expr)
      (initValues : List Expr)
      (accStart itemStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (targets : List Nat) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec sourceLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {itemStart + offset}"] ++ sourceLoads rest
    let rec initStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {accStart + offset}"] ++ initStores rest
    let rec bodyStages : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {tempStart + offset}"] ++ bodyStages rest
    let rec tempCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          [s!"local.get {tempStart + offset}", s!"local.set {accStart + offset}"] ++
            tempCopies rest
    let rec targetCopies : List (Nat × Nat) → List String
      | [] => []
      | (offset, target) :: rest =>
          [s!"local.get {accStart + offset}", s!"local.set {target}"] ++ targetCopies rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}"] ++
      initStores (enumerate initValues) ++
      [s!"local.get {stopLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {stopLocal}", "else",
        s!"  local.get {lenLocal}", "end", s!"local.set {effectiveStopLocal}",
        "block", "  loop",
        s!"    local.get {indexLocal}", s!"    local.get {effectiveStopLocal}", "    i64.ge_u",
        "    br_if 1"] ++
      indent 4 (
        sourceLoads (List.range sourceWidth) ++
        bodyLets.flatMap (localLetWatLines childScratch) ++
        bodyStages (enumerate bodyValues) ++
        exprWatLines childScratch bodyDone ++
        [s!"local.set {doneSlot}"] ++
        tempCopies (List.range resultWidth) ++
        [s!"local.get {doneSlot}", "i64.const 0", "i64.ne", "br_if 1"] ++
        [s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["  end", "end"] ++
      targetCopies (enumerate targets)

  partial def arrayFindIdxSlotsWatLines
      (scratch sourceWidth : Nat)
      (array : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (returnPayload : Bool) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let foundValue := if returnPayload then [s!"local.get {indexLocal}"] else ["i64.const 1"]
    let rec sourceLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {itemStart + offset}"] ++ sourceLoads rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}",
      "i64.const 0", s!"local.set {indexLocal}",
      "i64.const 0", s!"local.set {resultLocal}",
      "block", "  loop",
      s!"    local.get {indexLocal}", s!"    local.get {lenLocal}", "    i64.ge_u",
      "    br_if 1"] ++
      indent 4 (
        sourceLoads (List.range sourceWidth) ++
        exprWatLines childScratch predicate ++ ["i64.const 0", "i64.ne", "if"] ++
        indent 2 (foundValue ++ [s!"local.set {resultLocal}", "br 2"]) ++
        ["end",
          s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {resultLocal}"]

  partial def arrayFindSlotWatLines
      (scratch sourceWidth : Nat)
      (array : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (slot : Nat) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let rec sourceLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {itemStart + offset}"] ++ sourceLoads rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}",
      "i64.const 0", s!"local.set {indexLocal}",
      "i64.const 0", s!"local.set {resultLocal}",
      "block", "  loop",
      s!"    local.get {indexLocal}", s!"    local.get {lenLocal}", "    i64.ge_u",
      "    br_if 1"] ++
      indent 4 (
        sourceLoads (List.range sourceWidth) ++
        exprWatLines childScratch predicate ++ ["i64.const 0", "i64.ne", "if"] ++
        indent 2 ([s!"local.get {itemStart + slot}", s!"local.set {resultLocal}", "br 2"]) ++
        ["end",
          s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {resultLocal}"]

  partial def arrayEqSlotsWatLines
      (scratch width : Nat)
      (left right : Expr)
      (leftStart rightStart : Nat)
      (predicate : Expr) : List String :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let lenLocal := scratch + 2
    let indexLocal := scratch + 3
    let resultLocal := scratch + 4
    let childScratch := scratch + 5
    let rec elementLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat width offset [s!"local.get {leftLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {leftStart + offset}"] ++
          arraySlotAddressWat width offset [s!"local.get {rightLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {rightStart + offset}"] ++
          elementLoads rest
    exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
      s!"local.get {leftLocal}", "i32.wrap_i64", "i64.load align=8", s!"local.set {lenLocal}",
      s!"local.get {lenLocal}", s!"local.get {rightLocal}", "i32.wrap_i64", "i64.load align=8",
      "i64.ne",
      "if (result i64)", "  i64.const 0", "else",
      s!"  i64.const 0", s!"  local.set {indexLocal}",
      s!"  i64.const 1", s!"  local.set {resultLocal}",
      "  block", "    loop",
      s!"      local.get {indexLocal}", s!"      local.get {lenLocal}", "      i64.ge_u",
      "      br_if 1"] ++
      indent 6 (
        elementLoads (List.range width) ++
        exprWatLines childScratch predicate ++ ["i64.const 0", "i64.eq", "if"] ++
        indent 2 (["i64.const 0", s!"local.set {resultLocal}", "br 2"]) ++
        ["end",
          s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["    end", "  end", s!"  local.get {resultLocal}", "end"]

  partial def arrayAnySlotsWatLines
      (scratch sourceWidth : Nat)
      (array start stop : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (forAll : Bool) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let resultLocal := scratch + 5
    let childScratch := scratch + 6
    let initialResult := if forAll then "i64.const 1" else "i64.const 0"
    let foundResult := if forAll then "i64.const 0" else "i64.const 1"
    let predicateCondition :=
      if forAll then
        exprWatLines childScratch predicate ++ ["i64.const 0", "i64.ne", "i32.eqz"]
      else
        exprWatLines childScratch predicate ++ ["i64.const 0", "i64.ne"]
    let rec sourceLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {itemStart + offset}"] ++ sourceLoads rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}",
        initialResult, s!"local.set {resultLocal}",
        s!"local.get {stopLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {stopLocal}", "else",
        s!"  local.get {lenLocal}", "end", s!"local.set {effectiveStopLocal}",
        "block", "  loop",
        s!"    local.get {indexLocal}", s!"    local.get {effectiveStopLocal}", "    i64.ge_u",
        "    br_if 1"] ++
      indent 4 (
        sourceLoads (List.range sourceWidth) ++
        predicateCondition ++ ["if"] ++
        indent 2 ([foundResult, s!"local.set {resultLocal}", "br 2"]) ++
        ["end",
          s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {resultLocal}"]

  partial def arrayFilterSlotsWatLines
      (scratch sourceWidth _childMask : Nat)
      (array start stop : Expr)
      (itemStart : Nat)
      (predicate : Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let newLocal := scratch + 5
    let writeIndexLocal := scratch + 6
    let cellsLocal := scratch + 7
    let childScratch := scratch + 8
    let rec sourceLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
            ["i64.load align=8", s!"local.set {itemStart + offset}"] ++ sourceLoads rest
    let rec resultStores : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat sourceWidth offset [s!"local.get {newLocal}"] [s!"local.get {writeIndexLocal}"] ++
            [s!"local.get {itemStart + offset}", "i64.store align=8"] ++ resultStores rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}",
        s!"local.get {lenLocal}", s!"i64.const {sourceWidth}", "i64.mul",
        s!"local.set {cellsLocal}",
        "global.get 0", s!"local.set {newLocal}",
        "global.get 0", "i64.const 8", s!"local.get {cellsLocal}", "i64.const 8",
        "i64.mul", "i64.add", "i64.add", "global.set 0",
        "i64.const 0", s!"local.set {writeIndexLocal}",
        s!"local.get {stopLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {stopLocal}", "else",
        s!"  local.get {lenLocal}", "end", s!"local.set {effectiveStopLocal}",
        "block", "  loop",
        s!"    local.get {indexLocal}", s!"    local.get {effectiveStopLocal}", "    i64.ge_u",
        "    br_if 1"] ++
      indent 4 (
        sourceLoads (List.range sourceWidth) ++
        exprWatLines childScratch predicate ++ ["i64.const 0", "i64.ne", "if"] ++
        indent 2 (
          resultStores (List.range sourceWidth) ++
          [s!"local.get {writeIndexLocal}", "i64.const 1", "i64.add",
            s!"local.set {writeIndexLocal}"]) ++
        ["end",
          s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["  end", "end",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {writeIndexLocal}",
        "i64.store align=8",
        s!"local.get {newLocal}"]

  partial def arrayInsertIfInBoundsSlotsWatLines
      (scratch width _childMask _ownedMask : Nat)
      (array index : Expr)
      (values : List Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let prefixCellsLocal := scratch + 3
    let suffixCellsLocal := scratch + 4
    let newLenLocal := scratch + 5
    let newLocal := scratch + 6
    let loopLocal := scratch + 7
    let valueStart := scratch + 8
    let childScratch := scratch + 8 + values.length
    let rec valueStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++ [s!"local.set {valueStart + offset}"] ++
            valueStores rest
    let rec slotStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddressWat width offset [s!"local.get {newLocal}"] [s!"local.get {indexLocal}"] ++
            [s!"local.get {valueStart + offset}", "i64.store align=8"] ++
            slotStores rest
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {lenLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.le_u",
        "if (result i64)"] ++
      indent 2 (
        valueStores (enumerate values) ++
        [s!"local.get {lenLocal}", "i64.const 1", "i64.add", s!"local.set {newLenLocal}",
          s!"local.get {indexLocal}", s!"i64.const {width}", "i64.mul",
          s!"local.set {prefixCellsLocal}",
          s!"local.get {lenLocal}", s!"local.get {indexLocal}", "i64.sub",
          s!"i64.const {width}", "i64.mul", s!"local.set {suffixCellsLocal}",
          "global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", s!"i64.const {width}",
          "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        copyLoopWat arrayLocal newLocal prefixCellsLocal loopLocal ++
        slotStores (enumerate values) ++
        rangeCopyLoopWat
          arrayLocal
          newLocal
          [s!"local.get {prefixCellsLocal}"]
          [s!"local.get {prefixCellsLocal}", s!"i64.const {width}", "i64.add"]
          suffixCellsLocal
          loopLocal ++
        [s!"local.get {newLocal}"]) ++
      ["else"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["end"]

  partial def arrayEraseIfInBoundsSlotsWatLines
      (scratch width _childMask : Nat)
      (array index : Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let prefixCellsLocal := scratch + 3
    let suffixCellsLocal := scratch + 4
    let newLenLocal := scratch + 5
    let newLocal := scratch + 6
    let loopLocal := scratch + 7
    let childScratch := scratch + 8
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {lenLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)"] ++
      indent 2 (
        [s!"local.get {lenLocal}", "i64.const 1", "i64.sub", s!"local.set {newLenLocal}",
          s!"local.get {indexLocal}", s!"i64.const {width}", "i64.mul",
          s!"local.set {prefixCellsLocal}",
          s!"local.get {newLenLocal}", s!"local.get {indexLocal}", "i64.sub",
          s!"i64.const {width}", "i64.mul", s!"local.set {suffixCellsLocal}",
          "global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", s!"i64.const {width}",
          "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        copyLoopWat arrayLocal newLocal prefixCellsLocal loopLocal ++
        rangeCopyLoopWat
          arrayLocal
          newLocal
          [s!"local.get {prefixCellsLocal}", s!"i64.const {width}", "i64.add"]
          [s!"local.get {prefixCellsLocal}"]
          suffixCellsLocal
          loopLocal ++
        [s!"local.get {newLocal}"]) ++
      ["else"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["end"]

  partial def arraySwapIfInBoundsSlotsWatLines
      (scratch width _childMask : Nat)
      (array left right : Expr) : List String :=
    let arrayLocal := scratch
    let leftLocal := scratch + 1
    let rightLocal := scratch + 2
    let lenLocal := scratch + 3
    let cellsLocal := scratch + 4
    let newLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
    let rec slotCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat width offset [s!"local.get {newLocal}"] [s!"local.get {leftLocal}"] ++
          arraySlotAddressWat width offset [s!"local.get {arrayLocal}"] [s!"local.get {rightLocal}"] ++
          ["i64.load align=8", "i64.store align=8"] ++
          arraySlotAddressWat width offset [s!"local.get {newLocal}"] [s!"local.get {rightLocal}"] ++
          arraySlotAddressWat width offset [s!"local.get {arrayLocal}"] [s!"local.get {leftLocal}"] ++
          ["i64.load align=8", "i64.store align=8"] ++ slotCopies rest
    let swapBody :=
      [s!"local.get {lenLocal}", s!"i64.const {width}", "i64.mul", s!"local.set {cellsLocal}",
        "global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}",
        "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {cellsLocal}", "i64.const 8",
        "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      copyLoopWat arrayLocal newLocal cellsLocal loopLocal ++
      slotCopies (List.range width) ++
      [s!"local.get {newLocal}"]
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {lenLocal}",
        s!"local.get {leftLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)"] ++
      indent 2 (
        [s!"local.get {rightLocal}", s!"local.get {lenLocal}", "i64.lt_u",
          "if (result i64)"] ++
        indent 2 swapBody ++
        ["else"] ++
        indent 2 [s!"local.get {arrayLocal}"] ++
        ["end"]) ++
      ["else"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["end"]

  partial def arrayReverseSlotsWatLines
      (scratch width _childMask : Nat)
      (array : Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    let sourceIndex :=
      [s!"local.get {lenLocal}", s!"local.get {loopLocal}", "i64.sub", "i64.const 1", "i64.sub"]
    let rec slotCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          arraySlotAddressWat width offset [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
          arraySlotAddressWat width offset [s!"local.get {arrayLocal}"] sourceIndex ++
          ["i64.load align=8", "i64.store align=8"] ++ slotCopies rest
    let copyLoop :=
      [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
        indent 4 (
          [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
          slotCopies (List.range width) ++
          [s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
            "br 0"]) ++
        ["  end", "end"]
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}",
      s!"local.get {lenLocal}", "i64.const 1", "i64.le_u",
      "if (result i64)"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["else"] ++
      indent 2 (
        ["global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {lenLocal}", s!"i64.const {width}",
          "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        copyLoop ++
        [s!"local.get {newLocal}"]) ++
      ["end"]

  partial def byteArrayGetWatLines (scratch : Nat) (ptr len index : Expr) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let childScratch := scratch + 3
    exprWatLines childScratch ptr ++ [s!"local.set {ptrLocal}"] ++
      exprWatLines childScratch len ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)"] ++
      indent 2 [s!"local.get {ptrLocal}", s!"local.get {indexLocal}", "i64.add",
        "i32.wrap_i64", "i32.load8_u", "i64.extend_i32_u"] ++
      ["else", "  unreachable", "end"]

  partial def byteArrayPushPtrWatLines (scratch : Nat) (ptr len value : Expr) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let valueLocal := scratch + 2
    let newPtrLocal := scratch + 3
    let newLenLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let copyLoop :=
      [s!"i64.const 0", s!"local.set {loopLocal}", "block", "loop",
        s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1",
        s!"local.get {newPtrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        s!"local.get {ptrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i32.store8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0", "end", "end"]
    exprWatLines childScratch ptr ++ [s!"local.set {ptrLocal}"] ++
      exprWatLines childScratch len ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch value ++ [s!"local.set {valueLocal}",
        s!"local.get {lenLocal}", "i64.const 1", "i64.add", s!"local.set {newLenLocal}",
        "global.get 0", s!"local.set {newPtrLocal}",
        "global.get 0", s!"local.get {newLenLocal}", "i64.add", "global.set 0"] ++
      copyLoop ++
      [s!"local.get {newPtrLocal}", s!"local.get {lenLocal}", "i64.add", "i32.wrap_i64",
        s!"local.get {valueLocal}", "i32.wrap_i64", "i32.store8",
        s!"local.get {newPtrLocal}"]

  partial def byteArrayAppendPtrWatLines
      (scratch : Nat)
      (leftPtr leftLen rightPtr rightLen : Expr) : List String :=
    let leftPtrLocal := scratch
    let leftLenLocal := scratch + 1
    let rightPtrLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let newPtrLocal := scratch + 4
    let newLenLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
    let copyLeftLoop :=
      ["i64.const 0", s!"local.set {loopLocal}", "block", "loop",
        s!"local.get {loopLocal}", s!"local.get {leftLenLocal}", "i64.ge_u", "br_if 1",
        s!"local.get {newPtrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        s!"local.get {leftPtrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i32.store8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0", "end", "end"]
    let copyRightLoop :=
      ["i64.const 0", s!"local.set {loopLocal}", "block", "loop",
        s!"local.get {loopLocal}", s!"local.get {rightLenLocal}", "i64.ge_u", "br_if 1",
        s!"local.get {newPtrLocal}", s!"local.get {leftLenLocal}", "i64.add",
        s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        s!"local.get {rightPtrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i32.store8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0", "end", "end"]
    exprWatLines childScratch leftPtr ++ [s!"local.set {leftPtrLocal}"] ++
      exprWatLines childScratch leftLen ++ [s!"local.set {leftLenLocal}"] ++
      exprWatLines childScratch rightPtr ++ [s!"local.set {rightPtrLocal}"] ++
      exprWatLines childScratch rightLen ++ [s!"local.set {rightLenLocal}",
        s!"local.get {leftLenLocal}", s!"local.get {rightLenLocal}", "i64.add",
        s!"local.set {newLenLocal}",
        "global.get 0", s!"local.set {newPtrLocal}",
        "global.get 0", s!"local.get {newLenLocal}", "i64.add", "global.set 0"] ++
      copyLeftLoop ++
      copyRightLoop ++
      [s!"local.get {newPtrLocal}"]

  partial def byteArraySetPtrWatLines
      (scratch : Nat)
      (ptr len index value : Expr) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let valueLocal := scratch + 3
    let newPtrLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let copyLoop :=
      ["i64.const 0", s!"local.set {loopLocal}", "block", "loop",
        s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1",
        s!"local.get {newPtrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        s!"local.get {ptrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i32.store8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0", "end", "end"]
    exprWatLines childScratch ptr ++ [s!"local.set {ptrLocal}"] ++
      exprWatLines childScratch len ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch value ++ [s!"local.set {valueLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)"] ++
      indent 2 (
        ["global.get 0", s!"local.set {newPtrLocal}",
          "global.get 0", s!"local.get {lenLocal}", "i64.add", "global.set 0"] ++
        copyLoop ++
        [s!"local.get {newPtrLocal}", s!"local.get {indexLocal}", "i64.add",
          "i32.wrap_i64", s!"local.get {valueLocal}", "i32.wrap_i64", "i32.store8",
          s!"local.get {newPtrLocal}"]) ++
      ["else", "  unreachable", "end"]

  partial def byteArrayFromArrayPtrWatLines (scratch : Nat) (array : Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newPtrLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    let copyLoop :=
      ["i64.const 0", s!"local.set {loopLocal}", "block", "loop",
        s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1",
        s!"local.get {newPtrLocal}", s!"local.get {loopLocal}", "i64.add", "i32.wrap_i64"] ++
      arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {loopLocal}"] ++
      ["i64.load align=8", "i32.wrap_i64", "i32.store8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0", "end", "end"]
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8", s!"local.set {lenLocal}",
      "global.get 0", s!"local.set {newPtrLocal}",
      "global.get 0", s!"local.get {lenLocal}", "i64.add", "global.set 0"] ++
      copyLoop ++
      [s!"local.get {newPtrLocal}"]

  partial def byteArrayCopySlicePtrWatLines
      (scratch : Nat)
      (srcPtr srcLen srcOff destPtr destLen destOff copyLen : Expr) : List String :=
    let srcPtrLocal := scratch
    let srcLenLocal := scratch + 1
    let srcOffLocal := scratch + 2
    let destPtrLocal := scratch + 3
    let destLenLocal := scratch + 4
    let destOffLocal := scratch + 5
    let requestedLenLocal := scratch + 6
    let availableLocal := scratch + 7
    let copiedLenLocal := scratch + 8
    let prefixLenLocal := scratch + 9
    let suffixStartLocal := scratch + 10
    let suffixLenLocal := scratch + 11
    let newLenLocal := scratch + 12
    let newPtrLocal := scratch + 13
    let loopLocal := scratch + 14
    let childScratch := scratch + 15
    exprWatLines childScratch srcPtr ++ [s!"local.set {srcPtrLocal}"] ++
      exprWatLines childScratch srcLen ++ [s!"local.set {srcLenLocal}"] ++
      exprWatLines childScratch srcOff ++ [s!"local.set {srcOffLocal}"] ++
      exprWatLines childScratch destPtr ++ [s!"local.set {destPtrLocal}"] ++
      exprWatLines childScratch destLen ++ [s!"local.set {destLenLocal}"] ++
      exprWatLines childScratch destOff ++ [s!"local.set {destOffLocal}"] ++
      exprWatLines childScratch copyLen ++ [s!"local.set {requestedLenLocal}",
        s!"local.get {srcOffLocal}", s!"local.get {srcLenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {srcLenLocal}", s!"  local.get {srcOffLocal}",
        "  i64.sub", "else", "  i64.const 0", "end", s!"local.set {availableLocal}",
        s!"local.get {requestedLenLocal}", s!"local.get {availableLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {requestedLenLocal}", "else",
        s!"  local.get {availableLocal}", "end", s!"local.set {copiedLenLocal}",
        s!"local.get {destOffLocal}", s!"local.get {destLenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {destOffLocal}", "else",
        s!"  local.get {destLenLocal}", "end", s!"local.set {prefixLenLocal}",
        s!"local.get {destOffLocal}", s!"local.get {copiedLenLocal}", "i64.add",
        s!"local.set {suffixStartLocal}",
        s!"local.get {suffixStartLocal}", s!"local.get {destLenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {destLenLocal}", s!"  local.get {suffixStartLocal}",
        "  i64.sub", "else", "  i64.const 0", "end", s!"local.set {suffixLenLocal}",
        s!"local.get {prefixLenLocal}", s!"local.get {copiedLenLocal}", "i64.add",
        s!"local.get {suffixLenLocal}", "i64.add", s!"local.set {newLenLocal}",
        "global.get 0", s!"local.set {newPtrLocal}",
        "global.get 0", s!"local.get {newLenLocal}", "i64.add", "global.set 0"] ++
      byteRangeCopyLoopWat
        destPtrLocal
        newPtrLocal
        ["i64.const 0"]
        ["i64.const 0"]
        [s!"local.get {prefixLenLocal}"]
        loopLocal ++
      byteRangeCopyLoopWat
        srcPtrLocal
        newPtrLocal
        [s!"local.get {srcOffLocal}"]
        [s!"local.get {prefixLenLocal}"]
        [s!"local.get {copiedLenLocal}"]
        loopLocal ++
      byteRangeCopyLoopWat
        destPtrLocal
        newPtrLocal
        [s!"local.get {suffixStartLocal}"]
        [s!"local.get {prefixLenLocal}", s!"local.get {copiedLenLocal}", "i64.add"]
        [s!"local.get {suffixLenLocal}"]
        loopLocal ++
      [s!"local.get {newPtrLocal}"]

  partial def byteArrayFindIdxWatLines
      (scratch : Nat)
      (ptr len start : Expr)
      (byteSlot : Nat)
      (predicate : Expr)
      (returnPayload : Bool) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let foundValue := if returnPayload then [s!"local.get {indexLocal}"] else ["i64.const 1"]
    exprWatLines childScratch ptr ++ [s!"local.set {ptrLocal}"] ++
      exprWatLines childScratch len ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}",
        "i64.const 0", s!"local.set {resultLocal}",
        "block", "  loop",
        s!"    local.get {indexLocal}", s!"    local.get {lenLocal}", "    i64.ge_u",
        "    br_if 1",
        s!"    local.get {ptrLocal}", s!"    local.get {indexLocal}", "    i64.add",
        "    i32.wrap_i64", "    i32.load8_u", "    i64.extend_i32_u",
        s!"    local.set {byteSlot}"] ++
      indent 4 (
        exprWatLines childScratch predicate ++ ["i64.const 0", "i64.ne", "if"] ++
        indent 2 (foundValue ++ [s!"local.set {resultLocal}", "br 2"]) ++
        ["end",
          s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {resultLocal}"]

  partial def byteArrayEqWatLines
      (scratch : Nat)
      (leftPtr leftLen rightPtr rightLen : Expr) : List String :=
    let leftPtrLocal := scratch
    let leftLenLocal := scratch + 1
    let rightPtrLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let indexLocal := scratch + 4
    let resultLocal := scratch + 5
    let childScratch := scratch + 6
    exprWatLines childScratch leftPtr ++ [s!"local.set {leftPtrLocal}"] ++
      exprWatLines childScratch leftLen ++ [s!"local.set {leftLenLocal}"] ++
      exprWatLines childScratch rightPtr ++ [s!"local.set {rightPtrLocal}"] ++
      exprWatLines childScratch rightLen ++ [s!"local.set {rightLenLocal}",
      s!"local.get {leftLenLocal}", s!"local.get {rightLenLocal}", "i64.ne",
      "if (result i64)", "  i64.const 0", "else",
      s!"  i64.const 0", s!"  local.set {indexLocal}",
      s!"  i64.const 1", s!"  local.set {resultLocal}",
      "  block", "    loop",
      s!"      local.get {indexLocal}", s!"      local.get {leftLenLocal}", "      i64.ge_u",
      "      br_if 1",
      s!"      local.get {leftPtrLocal}", s!"      local.get {indexLocal}", "      i64.add",
      "      i32.wrap_i64", "      i32.load8_u", "      i64.extend_i32_u",
      s!"      local.get {rightPtrLocal}", s!"      local.get {indexLocal}", "      i64.add",
      "      i32.wrap_i64", "      i32.load8_u", "      i64.extend_i32_u",
      "      i64.ne", "      if"] ++
      indent 8 (["i64.const 0", s!"local.set {resultLocal}", "br 2"]) ++
      ["      end",
      s!"      local.get {indexLocal}", "      i64.const 1", "      i64.add",
      s!"      local.set {indexLocal}", "      br 0",
      "    end", "  end", s!"  local.get {resultLocal}", "end"]

  partial def byteArrayFoldMultiSlotWatLines
      (scratch resultWidth : Nat)
      (ptr len start stop : Expr)
      (initValues : List Expr)
      (accStart byteSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (resultSlot : Nat) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec initStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {accStart + offset}"] ++ initStores rest
    let rec bodyStages : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {tempStart + offset}"] ++ bodyStages rest
    let rec tempCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          [s!"local.get {tempStart + offset}", s!"local.set {accStart + offset}"] ++
            tempCopies rest
    exprWatLines childScratch ptr ++ [s!"local.set {ptrLocal}"] ++
      exprWatLines childScratch len ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}"] ++
      initStores (enumerate initValues) ++
      [s!"local.get {stopLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {stopLocal}", "else",
        s!"  local.get {lenLocal}", "end", s!"local.set {effectiveStopLocal}",
        "block", "loop",
        s!"local.get {indexLocal}", s!"local.get {effectiveStopLocal}", "i64.ge_u",
        "br_if 1",
        s!"local.get {ptrLocal}", s!"local.get {indexLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i64.extend_i32_u", s!"local.set {byteSlot}"] ++
      bodyLets.flatMap (localLetWatLines childScratch) ++
      bodyStages (enumerate bodyValues) ++
      exprWatLines childScratch bodyDone ++
      [s!"local.set {doneSlot}"] ++
      tempCopies (List.range resultWidth) ++
      [s!"local.get {doneSlot}", "i64.const 0", "i64.ne", "br_if 1"] ++
      [s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
        "br 0", "end", "end", s!"local.get {accStart + resultSlot}"]

  partial def byteArrayFoldMultiSlotAssignWatLines
      (scratch resultWidth : Nat)
      (ptr len start stop : Expr)
      (initValues : List Expr)
      (accStart byteSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (targets : List Nat) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec initStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {accStart + offset}"] ++ initStores rest
    let rec bodyStages : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {tempStart + offset}"] ++ bodyStages rest
    let rec tempCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          [s!"local.get {tempStart + offset}", s!"local.set {accStart + offset}"] ++
            tempCopies rest
    let rec targetCopies : List (Nat × Nat) → List String
      | [] => []
      | (offset, target) :: rest =>
          [s!"local.get {accStart + offset}", s!"local.set {target}"] ++ targetCopies rest
    exprWatLines childScratch ptr ++ [s!"local.set {ptrLocal}"] ++
      exprWatLines childScratch len ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}"] ++
      initStores (enumerate initValues) ++
      [s!"local.get {stopLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {stopLocal}", "else",
        s!"  local.get {lenLocal}", "end", s!"local.set {effectiveStopLocal}",
        "block", "loop",
        s!"local.get {indexLocal}", s!"local.get {effectiveStopLocal}", "i64.ge_u",
        "br_if 1",
        s!"local.get {ptrLocal}", s!"local.get {indexLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i64.extend_i32_u", s!"local.set {byteSlot}"] ++
      bodyLets.flatMap (localLetWatLines childScratch) ++
      bodyStages (enumerate bodyValues) ++
      exprWatLines childScratch bodyDone ++
      [s!"local.set {doneSlot}"] ++
      tempCopies (List.range resultWidth) ++
      [s!"local.get {doneSlot}", "i64.const 0", "i64.ne", "br_if 1"] ++
      [s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
        "br 0", "end", "end"] ++
      targetCopies (enumerate targets)

  partial def checkedDivModWatLines
      (scratch : Nat)
      (op : LeanExe.IR.U64Op)
      (left right : Expr) : List String :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    let zeroLines :=
      match op with
      | .divU => ["i64.const 0"]
      | .modU => [s!"local.get {leftLocal}"]
      | _ => ["i64.const 0"]
    let opLine :=
      match op with
      | .divU => "i64.div_u"
      | .modU => "i64.rem_u"
      | _ => "i64.add"
    exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
        s!"local.get {rightLocal}", "i64.const 0", "i64.eq", "if (result i64)"] ++
      indent 2 zeroLines ++
      ["else", s!"  local.get {leftLocal}", s!"  local.get {rightLocal}", s!"  {opLine}", "end"]

  partial def natAddWatLines (scratch : Nat) (left right : Expr) : List String :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let resultLocal := scratch + 2
    let childScratch := scratch + 3
    exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
        s!"local.get {leftLocal}", s!"local.get {rightLocal}", "i64.add",
        s!"local.tee {resultLocal}", s!"local.get {leftLocal}", "i64.lt_u",
        "if (result i64)", "  unreachable", "else", s!"  local.get {resultLocal}", "end"]

  partial def natMulWatLines (scratch : Nat) (left right : Expr) : List String :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
        s!"local.get {rightLocal}", "i64.const 0", "i64.eq", "if (result i64)",
        "  i64.const 0", "else",
        "  i64.const 18446744073709551615",
        s!"  local.get {rightLocal}", "i64.div_u", s!"  local.get {leftLocal}", "i64.lt_u",
        "  if (result i64)", "    unreachable", "  else",
        s!"    local.get {leftLocal}", s!"    local.get {rightLocal}", "    i64.mul",
        "  end", "end"]

  partial def natSubWatLines (scratch : Nat) (left right : Expr) : List String :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
        s!"local.get {leftLocal}", s!"local.get {rightLocal}", "i64.lt_u",
        "if (result i64)", "  i64.const 0", "else",
        s!"  local.get {leftLocal}", s!"  local.get {rightLocal}", "  i64.sub", "end"]

  partial def rangeFoldMultiSlotWatLines
      (scratch resultWidth : Nat)
      (start stop step : Expr)
      (initValues : List Expr)
      (accStart itemSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (resultSlot : Nat) : List String :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec initStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {accStart + offset}"] ++ initStores rest
    let rec bodyStages : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {tempStart + offset}"] ++ bodyStages rest
    let rec tempCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          [s!"local.get {tempStart + offset}", s!"local.set {accStart + offset}"] ++
            tempCopies rest
    exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}"] ++
      exprWatLines childScratch step ++ [s!"local.set {stepLocal}"] ++
      initStores (enumerate initValues) ++
      ["block", "loop",
        s!"local.get {indexLocal}", s!"local.get {stopLocal}", "i64.ge_u",
        "br_if 1",
        s!"local.get {indexLocal}", s!"local.set {itemSlot}"] ++
      bodyLets.flatMap (localLetWatLines childScratch) ++
      bodyStages (enumerate bodyValues) ++
      exprWatLines childScratch bodyDone ++
      [s!"local.set {doneSlot}"] ++
      tempCopies (List.range resultWidth) ++
      [s!"local.get {doneSlot}", "i64.const 0", "i64.ne", "br_if 1"] ++
      exprWatLines childScratch (.u64Bin .natAdd (.local indexLocal) (.local stepLocal)) ++
      [s!"local.set {indexLocal}", "br 0", "end", "end",
        s!"local.get {accStart + resultSlot}"]

  partial def rangeFoldMultiSlotAssignWatLines
      (scratch resultWidth : Nat)
      (start stop step : Expr)
      (initValues : List Expr)
      (accStart itemSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (targets : List Nat) : List String :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let rec initStores : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {accStart + offset}"] ++ initStores rest
    let rec bodyStages : List (Nat × Expr) → List String
      | [] => []
      | (offset, value) :: rest =>
          exprWatLines childScratch value ++
            [s!"local.set {tempStart + offset}"] ++ bodyStages rest
    let rec tempCopies : List Nat → List String
      | [] => []
      | offset :: rest =>
          [s!"local.get {tempStart + offset}", s!"local.set {accStart + offset}"] ++
            tempCopies rest
    let rec targetCopies : List (Nat × Nat) → List String
      | [] => []
      | (offset, target) :: rest =>
          [s!"local.get {accStart + offset}", s!"local.set {target}"] ++ targetCopies rest
    exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}"] ++
      exprWatLines childScratch step ++ [s!"local.set {stepLocal}"] ++
      initStores (enumerate initValues) ++
      ["block", "loop",
        s!"local.get {indexLocal}", s!"local.get {stopLocal}", "i64.ge_u",
        "br_if 1",
        s!"local.get {indexLocal}", s!"local.set {itemSlot}"] ++
      bodyLets.flatMap (localLetWatLines childScratch) ++
      bodyStages (enumerate bodyValues) ++
      exprWatLines childScratch bodyDone ++
      [s!"local.set {doneSlot}"] ++
      tempCopies (List.range resultWidth) ++
      [s!"local.get {doneSlot}", "i64.const 0", "i64.ne", "br_if 1"] ++
      exprWatLines childScratch (.u64Bin .natAdd (.local indexLocal) (.local stepLocal)) ++
      [s!"local.set {indexLocal}", "br 0", "end", "end"] ++
      targetCopies (enumerate targets)

  partial def heapLinearPredicateWatLines
      (scratch : Nat)
      (ptr : Expr)
      (continueTag fieldSlotCount recursiveFieldOffset fieldStart : Nat)
      (predicate : Expr)
      (stopWhenTrue terminalValue : Bool) : List String :=
    let ptrLocal := scratch
    let resultLocal := scratch + 1
    let childScratch := scratch + 2
    let rec fieldLoads : List Nat → List String
      | [] => []
      | offset :: rest =>
          [s!"local.get {ptrLocal}", s!"i64.const {(1 + offset) * 8}", "i64.add",
            "i32.wrap_i64", "i64.load align=8", s!"local.set {fieldStart + offset}"] ++
            fieldLoads rest
    let stopCond :=
      exprWatLines childScratch predicate ++ ["i64.const 0", "i64.ne"] ++
        (if stopWhenTrue then [] else ["i32.eqz"])
    let stopValue := if stopWhenTrue then 1 else 0
    let terminal := if terminalValue then 1 else 0
    exprWatLines childScratch ptr ++
      [s!"local.set {ptrLocal}", s!"i64.const {terminal}", s!"local.set {resultLocal}",
        "block", "  loop"] ++
      indent 4 (
        [s!"local.get {ptrLocal}", "i64.const 0", "i64.add", "i32.wrap_i64",
          "i64.load align=8", s!"i64.const {continueTag}", "i64.ne", "br_if 1"] ++
        fieldLoads (List.range fieldSlotCount) ++
        stopCond ++
        ["if",
          s!"  i64.const {stopValue}",
          s!"  local.set {resultLocal}",
          "  br 2",
          "end",
          s!"local.get {fieldStart + recursiveFieldOffset}",
          s!"local.set {ptrLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {resultLocal}"]

  partial def exprWatLines (scratch : Nat) : Expr → List String
    | .local index => [s!"local.get {index}"]
    | .trap => ["unreachable"]
    | .u64 value => [s!"i64.const {value}"]
    | .u64Bin .add left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.add"]
    | .u64Bin .natAdd left right => natAddWatLines scratch left right
    | .u64Bin .sub left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.sub"]
    | .u64Bin .natSub left right => natSubWatLines scratch left right
    | .u64Bin .mul left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.mul"]
    | .u64Bin .natMul left right => natMulWatLines scratch left right
    | .u64Bin .divU left right => checkedDivModWatLines scratch .divU left right
    | .u64Bin .modU left right => checkedDivModWatLines scratch .modU left right
    | .u64Bin .bitAnd left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.and"]
    | .u64Bin .bitOr left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.or"]
    | .u64Bin .bitXor left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.xor"]
    | .u64Bin .shiftLeft left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.shl"]
    | .u64Bin .shiftRight left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.shr_u"]
    | .ite cond thenValue elseValue =>
        condWatLines scratch cond ++
          ["if (result i64)"] ++
          indent 2 (exprWatLines scratch thenValue) ++
          ["else"] ++
          indent 2 (exprWatLines scratch elseValue) ++
          ["end"]
    | .letE slot value body =>
        exprWatLines scratch value ++ [s!"local.set {slot}"] ++ exprWatLines scratch body
    | .arrayAllocSlots width childMask cells =>
        arrayAllocSlotsWatLines scratch width childMask cells
    | .runtimeStat stat => [s!"global.get {runtimeStatGlobal stat}"]
    | .release ptr => exprWatLines scratch ptr ++ ["unreachable"]
    | .heapAllocSlots childMask values => heapAllocSlotsWatLines scratch childMask values
    | .heapLoadSlot ptr slot => heapLoadSlotWatLines scratch ptr slot
    | .arrayReplicateSlots width childMask ownedMask cells values =>
        arrayReplicateSlotsWatLines scratch width childMask ownedMask cells values
    | .arraySize array => arraySizeWatLines scratch array
    | .arrayGetSlot width slot array index =>
        arrayGetSlotWatLines scratch width slot array index
    | .arraySetSlots width childMask ownedMask array index values =>
        arraySetSlotsWatLines scratch width childMask ownedMask array index values
    | .arrayPushSlots width childMask ownedMask array values =>
        arrayPushSlotsWatLines scratch width childMask ownedMask array values
    | .arrayPopSlots width childMask array => arrayPopSlotsWatLines scratch width childMask array
    | .arrayAppendSlots width childMask left right =>
        arrayAppendSlotsWatLines scratch width childMask left right
    | .arrayExtractSlots width childMask array start stop =>
        arrayExtractSlotsWatLines scratch width childMask array start stop
    | .arrayMapSlots sourceWidth resultWidth childMask ownedMask array itemStart bodyValues =>
        arrayMapSlotsWatLines scratch sourceWidth resultWidth childMask ownedMask array itemStart
          bodyValues
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
        bodyValues bodyLets bodyDone resultSlot =>
        arrayFoldMultiSlotWatLines scratch sourceWidth resultWidth array start stop initValues accStart
          itemStart bodyValues bodyLets bodyDone resultSlot
    | .arrayFindIdxSlots sourceWidth array itemStart predicate returnPayload =>
        arrayFindIdxSlotsWatLines scratch sourceWidth array itemStart predicate returnPayload
    | .arrayFindSlot sourceWidth array itemStart predicate slot =>
        arrayFindSlotWatLines scratch sourceWidth array itemStart predicate slot
    | .arrayEqSlots width left right leftStart rightStart predicate =>
        arrayEqSlotsWatLines scratch width left right leftStart rightStart predicate
    | .arrayAnySlots sourceWidth array start stop itemStart predicate forAll =>
        arrayAnySlotsWatLines scratch sourceWidth array start stop itemStart predicate forAll
    | .arrayFilterSlots sourceWidth childMask array start stop itemStart predicate =>
        arrayFilterSlotsWatLines scratch sourceWidth childMask array start stop itemStart predicate
    | .arrayInsertIfInBoundsSlots width childMask ownedMask array index values =>
        arrayInsertIfInBoundsSlotsWatLines scratch width childMask ownedMask array index values
    | .arrayEraseIfInBoundsSlots width childMask array index =>
        arrayEraseIfInBoundsSlotsWatLines scratch width childMask array index
    | .arraySwapIfInBoundsSlots width childMask array left right =>
        arraySwapIfInBoundsSlotsWatLines scratch width childMask array left right
    | .arrayReverseSlots width childMask array =>
        arrayReverseSlotsWatLines scratch width childMask array
    | .byteArrayGet ptr len index => byteArrayGetWatLines scratch ptr len index
    | .byteArrayPushPtr ptr len value => byteArrayPushPtrWatLines scratch ptr len value
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        byteArrayAppendPtrWatLines scratch leftPtr leftLen rightPtr rightLen
    | .byteArraySetPtr ptr len index value => byteArraySetPtrWatLines scratch ptr len index value
    | .byteArrayFromArrayPtr array => byteArrayFromArrayPtrWatLines scratch array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        byteArrayCopySlicePtrWatLines scratch srcPtr srcLen srcOff destPtr destLen destOff copyLen
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        byteArrayEqWatLines scratch leftPtr leftLen rightPtr rightLen
    | .byteArrayFindIdx ptr len start byteSlot predicate returnPayload =>
        byteArrayFindIdxWatLines scratch ptr len start byteSlot predicate returnPayload
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone resultSlot =>
        byteArrayFoldMultiSlotWatLines scratch resultWidth ptr len start stop initValues accStart
          byteSlot bodyValues bodyLets bodyDone resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone resultSlot =>
        rangeFoldMultiSlotWatLines scratch resultWidth start stop step initValues accStart itemSlot
          bodyValues bodyLets bodyDone resultSlot
    | .heapLinearPredicate ptr continueTag fieldSlotCount recursiveFieldOffset fieldStart predicate
        stopWhenTrue terminalValue =>
        heapLinearPredicateWatLines scratch ptr continueTag fieldSlotCount recursiveFieldOffset
          fieldStart predicate stopWhenTrue terminalValue
    | .call index args => args.flatMap (exprWatLines scratch) ++ [s!"call {index}"]
    | .letCall slots index args body =>
        args.flatMap (exprWatLines scratch) ++ [s!"call {index}"] ++
          slots.reverse.map (fun slot => s!"local.set {slot}") ++ exprWatLines scratch body
    | .letLets lets body =>
        lets.flatMap (localLetWatLines scratch) ++ exprWatLines scratch body

  partial def slotsAssignWatLines (scratch : Nat) (slots : List Nat) (values : List Expr) :
      List String :=
    let direct :=
      (slots.zip values).flatMap fun item =>
        exprWatLines scratch item.snd ++ [s!"local.set {item.fst}"]
    match values with
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
        bodyValues bodyLets bodyDone _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart
                itemStart bodyValues bodyLets bodyDone offset
                : Expr)
          if values == expected then
            arrayFoldMultiSlotAssignWatLines scratch sourceWidth resultWidth array start stop
              initValues accStart itemStart bodyValues bodyLets bodyDone slots
          else
            direct
        else
          direct
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart
                byteSlot bodyValues bodyLets bodyDone offset
                : Expr)
          if values == expected then
            byteArrayFoldMultiSlotAssignWatLines scratch resultWidth ptr len start stop initValues
              accStart byteSlot bodyValues bodyLets bodyDone slots
          else
            direct
        else
          direct
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot
                bodyValues bodyLets bodyDone offset
                : Expr)
          if values == expected then
            rangeFoldMultiSlotAssignWatLines scratch resultWidth start stop step initValues accStart
              itemSlot bodyValues bodyLets bodyDone slots
          else
            direct
        else
          direct
    | _ => direct

  partial def localLetWatLines (scratch : Nat) : LocalLet → List String
    | .expr slot value => exprWatLines scratch value ++ [s!"local.set {slot}"]
    | .call slots index args =>
        args.flatMap (exprWatLines scratch) ++ [s!"call {index}"] ++
          slots.reverse.map (fun slot => s!"local.set {slot}")
    | .slots slots values => slotsAssignWatLines scratch slots values
    | .branch cond thenLets elseLets =>
        condWatLines scratch cond ++ ["if"] ++
          indent 2 (thenLets.flatMap (localLetWatLines scratch)) ++
          ["else"] ++
          indent 2 (elseLets.flatMap (localLetWatLines scratch)) ++
          ["end"]

  partial def condWatLines (scratch : Nat) : Cond → List String
    | .true => ["i32.const 1"]
    | .false => ["i32.const 0"]
    | .eqU64 left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.eq"]
    | .ltU64 left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.lt_u"]
    | .leU64 left right => exprWatLines scratch left ++ exprWatLines scratch right ++ ["i64.le_u"]
    | .not cond => condWatLines scratch cond ++ ["i32.eqz"]
    | .and left right =>
        condWatLines scratch left ++
          ["if (result i32)"] ++
          indent 2 (condWatLines scratch right) ++
          ["else", "  i32.const 0", "end"]
    | .or left right =>
        condWatLines scratch left ++
          ["if (result i32)", "  i32.const 1", "else"] ++
          indent 2 (condWatLines scratch right) ++
          ["end"]
end

mutual
  partial def exprWatLinesWithRelease (releaseIndex scratch : Nat) : Expr → List String
    | .local index => [s!"local.get {index}"]
    | .trap => ["unreachable"]
    | .u64 value => [s!"i64.const {value}"]
    | .u64Bin .add left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.add"]
    | .u64Bin .natAdd left right => natAddWatLines scratch left right
    | .u64Bin .sub left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.sub"]
    | .u64Bin .natSub left right => natSubWatLines scratch left right
    | .u64Bin .mul left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.mul"]
    | .u64Bin .natMul left right => natMulWatLines scratch left right
    | .u64Bin .divU left right => checkedDivModWatLines scratch .divU left right
    | .u64Bin .modU left right => checkedDivModWatLines scratch .modU left right
    | .u64Bin .bitAnd left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.and"]
    | .u64Bin .bitOr left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.or"]
    | .u64Bin .bitXor left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.xor"]
    | .u64Bin .shiftLeft left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.shl"]
    | .u64Bin .shiftRight left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.shr_u"]
    | .ite cond thenValue elseValue =>
        condWatLinesWithRelease releaseIndex scratch cond ++
          ["if (result i64)"] ++
          indent 2 (exprWatLinesWithRelease releaseIndex scratch thenValue) ++
          ["else"] ++
          indent 2 (exprWatLinesWithRelease releaseIndex scratch elseValue) ++
          ["end"]
    | .letE slot value body =>
        exprWatLinesWithRelease releaseIndex scratch value ++ [s!"local.set {slot}"] ++
          exprWatLinesWithRelease releaseIndex scratch body
    | .letCall slots index args body =>
        args.flatMap (exprWatLinesWithRelease releaseIndex scratch) ++ [s!"call {index}"] ++
          slots.reverse.map (fun slot => s!"local.set {slot}") ++
          exprWatLinesWithRelease releaseIndex scratch body
    | .letLets lets body =>
        lets.flatMap (localLetWatLinesWithRelease releaseIndex scratch) ++
          exprWatLinesWithRelease releaseIndex scratch body
    | .runtimeStat stat => [s!"global.get {runtimeStatGlobal stat}"]
    | .release ptr =>
        exprWatLinesWithRelease releaseIndex scratch ptr ++ [s!"call {releaseIndex}"] ++
          [s!"global.get {runtimeStatGlobal .frees}"]
    | expr => exprWatLines scratch expr

  partial def condWatLinesWithRelease (releaseIndex scratch : Nat) : Cond → List String
    | .true => ["i32.const 1"]
    | .false => ["i32.const 0"]
    | .eqU64 left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.eq"]
    | .ltU64 left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.lt_u"]
    | .leU64 left right =>
        exprWatLinesWithRelease releaseIndex scratch left ++
          exprWatLinesWithRelease releaseIndex scratch right ++ ["i64.le_u"]
    | .not cond => condWatLinesWithRelease releaseIndex scratch cond ++ ["i32.eqz"]
    | .and left right =>
        condWatLinesWithRelease releaseIndex scratch left ++
          ["if (result i32)"] ++
          indent 2 (condWatLinesWithRelease releaseIndex scratch right) ++
          ["else", "  i32.const 0", "end"]
    | .or left right =>
        condWatLinesWithRelease releaseIndex scratch left ++
          ["if (result i32)", "  i32.const 1", "else"] ++
          indent 2 (condWatLinesWithRelease releaseIndex scratch right) ++
          ["end"]

  partial def localLetWatLinesWithRelease (releaseIndex scratch : Nat) :
      LocalLet → List String
    | .expr slot value =>
        exprWatLinesWithRelease releaseIndex scratch value ++ [s!"local.set {slot}"]
    | .call slots index args =>
        args.flatMap (exprWatLinesWithRelease releaseIndex scratch) ++ [s!"call {index}"] ++
          slots.reverse.map (fun slot => s!"local.set {slot}")
    | .slots slots values =>
        (slots.zip values).flatMap fun item =>
          exprWatLinesWithRelease releaseIndex scratch item.snd ++ [s!"local.set {item.fst}"]
    | .branch cond thenLets elseLets =>
        condWatLinesWithRelease releaseIndex scratch cond ++ ["if"] ++
          indent 2 (thenLets.flatMap (localLetWatLinesWithRelease releaseIndex scratch)) ++
          ["else"] ++
          indent 2 (elseLets.flatMap (localLetWatLinesWithRelease releaseIndex scratch)) ++
          ["end"]
end

partial def stmtWatLines (releaseIndex scratch : Nat) : Stmt → List String
  | .skip => []
  | .assign index value =>
      exprWatLinesWithRelease releaseIndex scratch value ++ [s!"local.set {index}"]
  | .call slots index args =>
      args.flatMap (exprWatLinesWithRelease releaseIndex scratch) ++ [s!"call {index}"] ++
        slots.reverse.map (fun slot => s!"local.set {slot}")
  | .release ptr => exprWatLinesWithRelease releaseIndex scratch ptr ++ [s!"call {releaseIndex}"]
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart itemStart
      bodyValues bodyLets bodyDone targets =>
      arrayFoldMultiSlotAssignWatLines scratch sourceWidth resultWidth array start stop initValues
        accStart itemStart bodyValues bodyLets bodyDone targets
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyLets bodyDone targets =>
      byteArrayFoldMultiSlotAssignWatLines scratch resultWidth ptr len start stop initValues accStart
        byteSlot bodyValues bodyLets bodyDone targets
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot bodyValues
      bodyLets bodyDone targets =>
      rangeFoldMultiSlotAssignWatLines scratch resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyLets bodyDone targets
  | .ite cond thenStmt elseStmt =>
      condWatLinesWithRelease releaseIndex scratch cond ++ ["if"] ++
        indent 2 (stmtWatLines releaseIndex scratch thenStmt) ++
        ["else"] ++
        indent 2 (stmtWatLines releaseIndex scratch elseStmt) ++
        ["end"]
  | .seq first second =>
      stmtWatLines releaseIndex scratch first ++ stmtWatLines releaseIndex scratch second
  | .while cond loopBody =>
      ["block", "  loop"] ++
        indent 4 (condWatLinesWithRelease releaseIndex scratch cond ++ ["i32.eqz", "br_if 1"] ++
          stmtWatLines releaseIndex scratch loopBody ++ ["br 0"]) ++
        ["  end", "end"]

def paramWat (count : Nat) : String :=
  if count == 0 then
    ""
  else
    " (param " ++ String.intercalate " " (List.replicate count "i64") ++ ")"

def localWat (count : Nat) : List String :=
  if count == 0 then
    []
  else
    ["(local " ++ String.intercalate " " (List.replicate count "i64") ++ ")"]

def resultWat (count : Nat) : String :=
  if count == 0 then
    ""
  else
    " (result " ++ String.intercalate " " (List.replicate count "i64") ++ ")"

def funcWatLines (releaseIndex : Nat) (func : Func) : List String :=
  let extra := func.locals - func.params + funcScratch func
  let scratch := func.locals
  let exportText :=
    match func.exportName with
    | some exportName => s!" (export \"{exportName}\")"
    | none => ""
  [s!"(func{exportText}{paramWat func.params}{resultWat func.results.length}"] ++
    indent 2
      (localWat extra ++ stmtWatLines releaseIndex scratch func.body ++
        func.results.flatMap (exprWatLinesWithRelease releaseIndex scratch)) ++
    [")"]

def moduleWat (module_ : Module) : String :=
  let releaseIndex := module_.funcs.size + 3
  String.intercalate "\n" <|
    ["(module", "  (memory (export \"memory\") 16)",
      "  (global (mut i64) (i64.const 4096))",
      "  (global (mut i64) (i64.const 0))",
      "  (global (mut i64) (i64.const 0))",
      "  (global (mut i64) (i64.const 0))",
      "  (global (mut i64) (i64.const 0))",
      "  (global (mut i64) (i64.const 0))"] ++
      (module_.funcs.toList.flatMap (fun func => indent 2 (funcWatLines releaseIndex func))) ++
      indent 2 [
        "(func (export \"alloc\") (param i64) (result i64)",
        "  (local i64 i64)",
        "  global.get 0",
        "  local.set 1",
        "  global.get 0",
        "  local.get 0",
        "  i64.add",
        "  local.tee 2",
        "  global.get 0",
        "  i64.lt_u",
        "  if",
        "    unreachable",
        "  end",
        "  local.get 2",
        "  i64.const 1",
        "  i64.sub",
        "  i64.const 65536",
        "  i64.div_u",
        "  i64.const 1",
        "  i64.add",
        "  memory.size",
        "  i64.extend_i32_u",
        "  i64.gt_u",
        "  if",
        "    local.get 2",
        "    i64.const 1",
        "    i64.sub",
        "    i64.const 65536",
        "    i64.div_u",
        "    i64.const 1",
        "    i64.add",
        "    memory.size",
        "    i64.extend_i32_u",
        "    i64.sub",
        "    i32.wrap_i64",
        "    memory.grow",
        "    i32.const -1",
        "    i32.eq",
        "    if",
        "      unreachable",
        "    end",
        "  end",
        "  local.get 2",
        "  global.set 0",
        "  global.get 2",
        "  i64.const 1",
        "  i64.add",
        "  global.set 2",
        "  local.get 1",
        ")",
        "(func (export \"reset\")",
        "  i64.const 4096",
        "  global.set 0",
        "  i64.const 0",
        "  global.set 1",
        "  i64.const 0",
        "  global.set 2",
        "  i64.const 0",
        "  global.set 3",
        "  i64.const 0",
        "  global.set 4",
        "  i64.const 0",
        "  global.set 5",
        ")",
        "(func (export \"retain\") (param i64) (result i64)",
        "  local.get 0",
        "  i64.eqz",
        "  if",
        "    local.get 0",
        "    return",
        "  end",
        "  global.get 3",
        "  i64.const 1",
        "  i64.add",
        "  global.set 3",
        "  local.get 0",
        ")",
        "(func (export \"release\") (param i64)",
        "  local.get 0",
        "  i64.eqz",
        "  if",
        "    return",
        "  end",
        "  global.get 4",
        "  i64.const 1",
        "  i64.add",
        "  global.set 4",
        "  global.get 5",
        "  i64.const 1",
        "  i64.add",
        "  global.set 5",
        "  local.get 0",
        "  drop",
        ")",
        "(func (export \"free\") (param i64)",
        "  local.get 0",
        "  drop",
        ")"] ++
      [")", ""]

end CoreWasm

def wat
    (validator : LeanExe.Core.LoweredValidator :=
      LeanExe.Core.lower LeanExe.Core.asciiDigits) : String :=
  String.intercalate "\n" [
    "(module",
    "  (memory (export \"memory\") 1)",
    "  (global $heap (mut i32) (i32.const 4096))",
    "  (func (export \"alloc\") (param $len i32) (result i32)",
    "    global.get $heap",
    "    global.get $heap",
    "    local.get $len",
    "    i32.add",
    "    global.set $heap)",
    "  (func (export \"reset\")",
    "    i32.const 4096",
    "    global.set $heap)",
    "  (func (export \"validate\") (param $ptr i32) (param $len i32) (result i32)",
    "    (local $i i32)",
    "    (local $b i32)",
    "    i32.const 0",
    "    local.set $i",
    "    block $fail",
    "      block $done",
    "        loop $loop",
    "          local.get $i",
    "          local.get $len",
    "          i32.ge_u",
    "          br_if $done",
    "          local.get $ptr",
    "          local.get $i",
    "          i32.add",
    "          i32.load8_u",
    "          local.set $b",
    "          local.get $b",
    s!"          i32.const {validator.min}",
    "          i32.lt_u",
    "          br_if $fail",
    "          local.get $b",
    s!"          i32.const {validator.max}",
    "          i32.gt_u",
    "          br_if $fail",
    "          local.get $i",
    "          i32.const 1",
    "          i32.add",
    "          local.set $i",
    "          br $loop",
    "        end",
    "      end",
    "      i32.const 1",
    "      return",
    "    end",
    "    i32.const 0)",
    ")",
    ""
  ]

end LeanExe.Wasm.Binary
