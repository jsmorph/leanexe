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
    | .arrayAllocSlots width cells =>
        .arrayAllocSlots width (shiftExprCalls offset cells)
    | .heapAllocSlots values =>
        .heapAllocSlots (values.map (shiftExprCalls offset))
    | .heapLoadSlot ptr slot =>
        .heapLoadSlot (shiftExprCalls offset ptr) slot
    | .arrayReplicateSlots width cells values =>
        .arrayReplicateSlots width (shiftExprCalls offset cells)
          (values.map (shiftExprCalls offset))
    | .arraySize array =>
        .arraySize (shiftExprCalls offset array)
    | .arrayGetSlot width slot array index =>
        .arrayGetSlot width slot (shiftExprCalls offset array) (shiftExprCalls offset index)
    | .arraySetSlots width array index values =>
        .arraySetSlots width (shiftExprCalls offset array) (shiftExprCalls offset index)
          (values.map (shiftExprCalls offset))
    | .arrayPushSlots width array values =>
        .arrayPushSlots width (shiftExprCalls offset array) (values.map (shiftExprCalls offset))
    | .arrayPopSlots width array =>
        .arrayPopSlots width (shiftExprCalls offset array)
    | .arrayAppendSlots width left right =>
        .arrayAppendSlots width (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .arrayExtractSlots width array start stop =>
        .arrayExtractSlots width (shiftExprCalls offset array) (shiftExprCalls offset start)
          (shiftExprCalls offset stop)
    | .arrayMapSlots sourceWidth resultWidth array itemStart bodyValues =>
        .arrayMapSlots sourceWidth resultWidth (shiftExprCalls offset array) itemStart
          (bodyValues.map (shiftExprCalls offset))
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyDone resultSlot =>
        .arrayFoldMultiSlot sourceWidth resultWidth (shiftExprCalls offset array)
          (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart itemStart
          (bodyValues.map (shiftExprCalls offset)) (shiftExprCalls offset bodyDone) resultSlot
    | .arrayFindIdxSlots sourceWidth array itemStart predicate returnPayload =>
        .arrayFindIdxSlots sourceWidth (shiftExprCalls offset array) itemStart
          (shiftExprCalls offset predicate) returnPayload
    | .arrayFindSlot sourceWidth array itemStart predicate slot =>
        .arrayFindSlot sourceWidth (shiftExprCalls offset array) itemStart
          (shiftExprCalls offset predicate) slot
    | .arrayAnySlots sourceWidth array start stop itemStart predicate forAll =>
        .arrayAnySlots sourceWidth (shiftExprCalls offset array) (shiftExprCalls offset start)
          (shiftExprCalls offset stop) itemStart (shiftExprCalls offset predicate) forAll
    | .arrayFilterSlots sourceWidth array start stop itemStart predicate =>
        .arrayFilterSlots sourceWidth (shiftExprCalls offset array) (shiftExprCalls offset start)
          (shiftExprCalls offset stop) itemStart (shiftExprCalls offset predicate)
    | .arrayInsertIfInBoundsSlots width array index values =>
        .arrayInsertIfInBoundsSlots width (shiftExprCalls offset array)
          (shiftExprCalls offset index) (values.map (shiftExprCalls offset))
    | .arrayEraseIfInBoundsSlots width array index =>
        .arrayEraseIfInBoundsSlots width (shiftExprCalls offset array) (shiftExprCalls offset index)
    | .arraySwapIfInBoundsSlots width array left right =>
        .arraySwapIfInBoundsSlots width (shiftExprCalls offset array)
          (shiftExprCalls offset left) (shiftExprCalls offset right)
    | .arrayReverseSlots width array =>
        .arrayReverseSlots width (shiftExprCalls offset array)
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
    | .byteArrayFindIdx ptr len start byteSlot predicate returnPayload =>
        .byteArrayFindIdx (shiftExprCalls offset ptr) (shiftExprCalls offset len)
          (shiftExprCalls offset start) byteSlot (shiftExprCalls offset predicate) returnPayload
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyDone resultSlot =>
        .byteArrayFoldMultiSlot resultWidth (shiftExprCalls offset ptr)
          (shiftExprCalls offset len) (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart byteSlot
          (bodyValues.map (shiftExprCalls offset)) (shiftExprCalls offset bodyDone) resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyDone resultSlot =>
        .rangeFoldMultiSlot resultWidth (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (shiftExprCalls offset step) (initValues.map (shiftExprCalls offset)) accStart
          itemSlot (bodyValues.map (shiftExprCalls offset)) (shiftExprCalls offset bodyDone)
          resultSlot
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

  partial def shiftStmtCalls (offset : Nat) : Stmt → Stmt
    | .skip => .skip
    | .assign index value => .assign index (shiftExprCalls offset value)
    | .call slots index args => .call slots (index + offset) (args.map (shiftExprCalls offset))
    | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyDone targets =>
        .arrayFoldMultiSlotAssign sourceWidth resultWidth (shiftExprCalls offset array)
          (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart itemStart
          (bodyValues.map (shiftExprCalls offset)) (shiftExprCalls offset bodyDone) targets
    | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart
        byteSlot bodyValues bodyDone targets =>
        .byteArrayFoldMultiSlotAssign resultWidth (shiftExprCalls offset ptr)
          (shiftExprCalls offset len) (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart byteSlot
          (bodyValues.map (shiftExprCalls offset)) (shiftExprCalls offset bodyDone) targets
    | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyDone targets =>
        .rangeFoldMultiSlotAssign resultWidth (shiftExprCalls offset start)
          (shiftExprCalls offset stop) (shiftExprCalls offset step)
          (initValues.map (shiftExprCalls offset)) accStart itemSlot
          (bodyValues.map (shiftExprCalls offset)) (shiftExprCalls offset bodyDone) targets
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
    ofNats [126, 1] ++ i64Const 4096 ++ ofNats [11]
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

def i64Store : List UInt8 :=
  ofNats [55, 3, 0]

def i32Store : List UInt8 :=
  ofNats [54, 2, 0]

def i32Load8U : List UInt8 :=
  ofNats [45, 0, 0]

def i32Store8 : List UInt8 :=
  ofNats [58, 0, 0]

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
    | .arrayAllocSlots _ cells => 2 + exprScratch cells
    | .heapAllocSlots values =>
        1 + values.length + values.foldl (fun n value => max n (exprScratch value)) 0
    | .heapLoadSlot ptr _ => 1 + exprScratch ptr
    | .arrayReplicateSlots _ cells values =>
        3 + values.length +
          max (exprScratch cells) (values.foldl (fun n value => max n (exprScratch value)) 0)
    | .arraySize array => 1 + exprScratch array
    | .arrayGetSlot _ _ array index => 2 + max (exprScratch array) (exprScratch index)
    | .arraySetSlots _ array index values =>
        6 + values.length +
          max (exprScratch array)
            (max (exprScratch index) (values.foldl (fun n value => max n (exprScratch value)) 0))
    | .arrayPushSlots _ array values =>
        6 + values.length +
          max (exprScratch array) (values.foldl (fun n value => max n (exprScratch value)) 0)
    | .arrayPopSlots _ array => 6 + exprScratch array
    | .arrayAppendSlots _ left right => 9 + max (exprScratch left) (exprScratch right)
    | .arrayExtractSlots _ array start stop =>
        10 + max (exprScratch array) (max (exprScratch start) (exprScratch stop))
    | .arrayMapSlots _ _ array _ bodyValues =>
        4 + max (exprScratch array)
          (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues _ _ bodyValues bodyDone _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let bodyScratch :=
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        5 + sourceWidth + resultWidth + 1 +
          max
            (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
            (max initScratch bodyScratch)
    | .arrayFindIdxSlots sourceWidth array _ predicate _ =>
        4 + sourceWidth + max (exprScratch array) (exprScratch predicate)
    | .arrayFindSlot sourceWidth array _ predicate _ =>
        4 + sourceWidth + max (exprScratch array) (exprScratch predicate)
    | .arrayAnySlots sourceWidth array start stop _ predicate _ =>
        6 + sourceWidth +
          max
            (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
            (exprScratch predicate)
    | .arrayFilterSlots sourceWidth array start stop _ predicate =>
        8 + sourceWidth +
          max
            (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
            (exprScratch predicate)
    | .arrayInsertIfInBoundsSlots _ array index values =>
        8 + values.length +
          max (exprScratch array)
            (max (exprScratch index) (values.foldl (fun n value => max n (exprScratch value)) 0))
    | .arrayEraseIfInBoundsSlots _ array index =>
        8 + max (exprScratch array) (exprScratch index)
    | .arraySwapIfInBoundsSlots _ array left right =>
        7 + max (exprScratch array) (max (exprScratch left) (exprScratch right))
    | .arrayReverseSlots _ array => 4 + exprScratch array
    | .byteArrayGet ptr len index =>
        3 + max (exprScratch ptr) (max (exprScratch len) (exprScratch index))
    | .byteArrayPushPtr ptr len value =>
        6 + max (exprScratch ptr) (max (exprScratch len) (exprScratch value))
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        7 + max
          (max (exprScratch leftPtr) (exprScratch leftLen))
          (max (exprScratch rightPtr) (exprScratch rightLen))
    | .byteArraySetPtr ptr len index value =>
        6 + max
          (max (exprScratch ptr) (exprScratch len))
          (max (exprScratch index) (exprScratch value))
    | .byteArrayFromArrayPtr array => 4 + exprScratch array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        15 + max
          (max (exprScratch srcPtr) (max (exprScratch srcLen) (exprScratch srcOff)))
          (max
            (max (exprScratch destPtr) (max (exprScratch destLen) (exprScratch destOff)))
            (exprScratch copyLen))
    | .byteArrayFindIdx ptr len start _ predicate _ =>
        4 + max
          (max (exprScratch ptr) (max (exprScratch len) (exprScratch start)))
          (exprScratch predicate)
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues _ _ bodyValues bodyDone _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let bodyScratch :=
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        5 + resultWidth + 1 +
          max
            (max (exprScratch ptr) (exprScratch len))
            (max (max (exprScratch start) (exprScratch stop))
              (max initScratch bodyScratch))
    | .rangeFoldMultiSlot resultWidth start stop step initValues _ _ bodyValues bodyDone _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let bodyScratch :=
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
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues _ _ bodyValues bodyDone _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let bodyScratch :=
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      5 + sourceWidth + resultWidth + 1 +
        max
          (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
          (max initScratch bodyScratch)
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues _ _ bodyValues bodyDone _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let bodyScratch :=
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      5 + resultWidth + 1 +
        max
          (max (exprScratch ptr) (exprScratch len))
          (max (max (exprScratch start) (exprScratch stop))
            (max initScratch bodyScratch))
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues _ _ bodyValues bodyDone _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let bodyScratch :=
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
  partial def emitArrayAllocSlots (scratch width : Nat) (cells : Expr) : List UInt8 :=
    let len := scratch
    let ptr := scratch + 1
    emitExpr (scratch + 2) cells ++ localSet len ++
      globalGet 0 ++ localSet ptr ++
      localGet ptr ++ i32WrapI64 ++ localGet len ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet len ++ i64Const width ++ ofNats [126] ++
        i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
      localGet ptr

  partial def emitHeapAllocSlots (scratch : Nat) (values : List Expr) : List UInt8 :=
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
      globalGet 0 ++ localSet ptrLocal ++
      emitSlotStores (enumerate values) ++
      globalGet 0 ++ i64Const (values.length * 8) ++ ofNats [124] ++ globalSet 0 ++
      localGet ptrLocal

  partial def emitHeapLoadSlot (scratch : Nat) (ptr : Expr) (slot : Nat) : List UInt8 :=
    let ptrLocal := scratch
    emitExpr (scratch + 1) ptr ++ localSet ptrLocal ++
      localGet ptrLocal ++ i64Const (slot * 8) ++ ofNats [124] ++ i32WrapI64 ++ i64Load

  partial def emitArrayReplicateSlots
      (scratch width : Nat)
      (cells : Expr)
      (values : List Expr) : List UInt8 :=
    let lenLocal := scratch
    let ptrLocal := scratch + 1
    let loopLocal := scratch + 2
    let valueStart := scratch + 3
    let childScratch := scratch + 3 + values.length
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
      globalGet 0 ++ localSet ptrLocal ++
      localGet ptrLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const width ++
        ofNats [126] ++ i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
      fillLoop ++
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
      (scratch width : Nat)
      (array index : Expr)
      (values : List Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let cellsLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let valueStart := scratch + 6
    let childScratch := scratch + 6 + values.length
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
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet cellsLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        emitSlotStores (enumerate values) ++
        localGet newLocal ++
      ofNats [5] ++
        ofNats [0] ++
      ofNats [11]

  partial def emitArrayPushSlots
      (scratch width : Nat)
      (array : Expr)
      (values : List Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let cellsLocal := scratch + 2
    let newLenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let valueStart := scratch + 6
    let childScratch := scratch + 6 + values.length
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
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const width ++
        ofNats [126] ++ i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
      emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
      emitSlotStores (enumerate values) ++
      localGet newLocal

  partial def emitArrayPopSlots (scratch width : Nat) (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLenLocal := scratch + 2
    let cellsLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const 0 ++ ofNats [81] ++
      ofNats [4, 126] ++
        localGet arrayLocal ++
      ofNats [5] ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [125] ++ localSet newLenLocal ++
        localGet newLenLocal ++ i64Const width ++ ofNats [126] ++ localSet cellsLocal ++
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet cellsLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        localGet newLocal ++
      ofNats [11]

  partial def emitArrayAppendSlots (scratch width : Nat) (left right : Expr) : List UInt8 :=
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
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ i32WrapI64 ++ i64Load ++ localSet leftLenLocal ++
      localGet rightLocal ++ i32WrapI64 ++ i64Load ++ localSet rightLenLocal ++
      localGet leftLenLocal ++ localGet rightLenLocal ++ ofNats [124] ++
        localSet newLenLocal ++
      localGet leftLenLocal ++ i64Const width ++ ofNats [126] ++ localSet leftCellsLocal ++
      localGet rightLenLocal ++ i64Const width ++ ofNats [126] ++ localSet rightCellsLocal ++
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const width ++
        ofNats [126] ++ i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
      emitCopyLoop leftLocal newLocal leftCellsLocal loopLocal ++
      emitCopyLoopAt rightLocal newLocal leftCellsLocal rightCellsLocal loopLocal ++
      localGet newLocal

  partial def emitArrayExtractSlots
      (scratch width : Nat)
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
    let childScratch := scratch + 10
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
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet cellsLocal ++ i64Const 8 ++
        ofNats [126, 124, 124] ++ globalSet 0 ++
      emitExtractCopyLoop arrayLocal newLocal startCellLocal cellsLocal loopLocal ++
      localGet newLocal

  partial def emitArrayMapSlots
      (scratch sourceWidth resultWidth : Nat)
      (array : Expr)
      (itemStart : Nat)
      (bodyValues : List Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
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
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const resultWidth ++
        ofNats [126] ++ i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
      i64Const 0 ++ localSet loopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        emitSourceLoads (List.range sourceWidth) ++
        emitResultStores (enumerate bodyValues) ++
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
      (bodyDone : Expr)
      (resultSlot : Nat) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (bodyDone : Expr)
      (targets : List Nat) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (scratch sourceWidth : Nat)
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
    let childScratch := scratch + 8
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
      globalGet 0 ++ localSet newLocal ++
      globalGet 0 ++ i64Const 8 ++ localGet cellsLocal ++ i64Const 8 ++
        ofNats [126, 124, 124] ++ globalSet 0 ++
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
          localGet writeIndexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet writeIndexLocal ++
        ofNats [11] ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet newLocal ++ i32WrapI64 ++ localGet writeIndexLocal ++ i64Store ++
      localGet newLocal

  partial def emitArrayInsertIfInBoundsSlots
      (scratch width : Nat)
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
    let childScratch := scratch + 8 + values.length
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
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const width ++
          ofNats [126] ++ i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal prefixCellsLocal loopLocal ++
        emitSlotStores (enumerate values) ++
        emitRangeCopyLoop
          arrayLocal
          newLocal
          (localGet prefixCellsLocal)
          (localGet prefixCellsLocal ++ i64Const width ++ ofNats [124])
          suffixCellsLocal
          loopLocal ++
        localGet newLocal ++
      ofNats [5] ++
        localGet arrayLocal ++
      ofNats [11]

  partial def emitArrayEraseIfInBoundsSlots
      (scratch width : Nat)
      (array index : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let prefixCellsLocal := scratch + 3
    let suffixCellsLocal := scratch + 4
    let newLenLocal := scratch + 5
    let newLocal := scratch + 6
    let loopLocal := scratch + 7
    let childScratch := scratch + 8
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [125] ++ localSet newLenLocal ++
        localGet indexLocal ++ i64Const width ++ ofNats [126] ++ localSet prefixCellsLocal ++
        localGet newLenLocal ++ localGet indexLocal ++ ofNats [125] ++
          i64Const width ++ ofNats [126] ++ localSet suffixCellsLocal ++
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const width ++
          ofNats [126] ++ i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal prefixCellsLocal loopLocal ++
        emitRangeCopyLoop
          arrayLocal
          newLocal
          (localGet prefixCellsLocal ++ i64Const width ++ ofNats [124])
          (localGet prefixCellsLocal)
          suffixCellsLocal
          loopLocal ++
        localGet newLocal ++
      ofNats [5] ++
        localGet arrayLocal ++
      ofNats [11]

  partial def emitArraySwapIfInBoundsSlots
      (scratch width : Nat)
      (array left right : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let leftLocal := scratch + 1
    let rightLocal := scratch + 2
    let lenLocal := scratch + 3
    let cellsLocal := scratch + 4
    let newLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
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
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet cellsLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        emitSlotCopies (List.range width) ++
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
      (scratch width : Nat)
      (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
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
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const width ++
          ofNats [126] ++ i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
        copyLoop ++
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
      globalGet 0 ++ localSet newPtrLocal ++
      globalGet 0 ++ localGet newLenLocal ++ ofNats [124] ++ globalSet 0 ++
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
      globalGet 0 ++ localSet newPtrLocal ++
      globalGet 0 ++ localGet newLenLocal ++ ofNats [124] ++ globalSet 0 ++
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
        globalGet 0 ++ localSet newPtrLocal ++
        globalGet 0 ++ localGet lenLocal ++ ofNats [124] ++ globalSet 0 ++
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
      globalGet 0 ++ localSet newPtrLocal ++
      globalGet 0 ++ localGet lenLocal ++ ofNats [124] ++ globalSet 0 ++
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
      globalGet 0 ++ localSet newPtrLocal ++
      globalGet 0 ++ localGet newLenLocal ++ ofNats [124] ++ globalSet 0 ++
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
      (bodyDone : Expr)
      (resultSlot : Nat) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (bodyDone : Expr)
      (targets : List Nat) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (bodyDone : Expr)
      (resultSlot : Nat) : List UInt8 :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let bodyScratch :=
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
      (bodyDone : Expr)
      (targets : List Nat) : List UInt8 :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let bodyScratch :=
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
    | .arrayAllocSlots width cells => emitArrayAllocSlots scratch width cells
    | .heapAllocSlots values => emitHeapAllocSlots scratch values
    | .heapLoadSlot ptr slot => emitHeapLoadSlot scratch ptr slot
    | .arrayReplicateSlots width cells values =>
        emitArrayReplicateSlots scratch width cells values
    | .arraySize array => emitArraySize scratch array
    | .arrayGetSlot width slot array index => emitArrayGetSlot scratch width slot array index
    | .arraySetSlots width array index values =>
        emitArraySetSlots scratch width array index values
    | .arrayPushSlots width array values => emitArrayPushSlots scratch width array values
    | .arrayPopSlots width array => emitArrayPopSlots scratch width array
    | .arrayAppendSlots width left right => emitArrayAppendSlots scratch width left right
    | .arrayExtractSlots width array start stop =>
        emitArrayExtractSlots scratch width array start stop
    | .arrayMapSlots sourceWidth resultWidth array itemStart bodyValues =>
        emitArrayMapSlots scratch sourceWidth resultWidth array itemStart bodyValues
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
        bodyValues bodyDone resultSlot =>
        emitArrayFoldMultiSlot scratch sourceWidth resultWidth array start stop initValues accStart
          itemStart bodyValues bodyDone resultSlot
    | .arrayFindIdxSlots sourceWidth array itemStart predicate returnPayload =>
        emitArrayFindIdxSlots scratch sourceWidth array itemStart predicate returnPayload
    | .arrayFindSlot sourceWidth array itemStart predicate slot =>
        emitArrayFindSlot scratch sourceWidth array itemStart predicate slot
    | .arrayAnySlots sourceWidth array start stop itemStart predicate forAll =>
        emitArrayAnySlots scratch sourceWidth array start stop itemStart predicate forAll
    | .arrayFilterSlots sourceWidth array start stop itemStart predicate =>
        emitArrayFilterSlots scratch sourceWidth array start stop itemStart predicate
    | .arrayInsertIfInBoundsSlots width array index values =>
        emitArrayInsertIfInBoundsSlots scratch width array index values
    | .arrayEraseIfInBoundsSlots width array index =>
        emitArrayEraseIfInBoundsSlots scratch width array index
    | .arraySwapIfInBoundsSlots width array left right =>
        emitArraySwapIfInBoundsSlots scratch width array left right
    | .arrayReverseSlots width array => emitArrayReverseSlots scratch width array
    | .byteArrayGet ptr len index => emitByteArrayGet scratch ptr len index
    | .byteArrayPushPtr ptr len value => emitByteArrayPushPtr scratch ptr len value
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        emitByteArrayAppendPtr scratch leftPtr leftLen rightPtr rightLen
    | .byteArraySetPtr ptr len index value =>
        emitByteArraySetPtr scratch ptr len index value
    | .byteArrayFromArrayPtr array => emitByteArrayFromArrayPtr scratch array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        emitByteArrayCopySlicePtr scratch srcPtr srcLen srcOff destPtr destLen destOff copyLen
    | .byteArrayFindIdx ptr len start byteSlot predicate returnPayload =>
        emitByteArrayFindIdx scratch ptr len start byteSlot predicate returnPayload
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyDone resultSlot =>
        emitByteArrayFoldMultiSlot scratch resultWidth ptr len start stop initValues accStart
          byteSlot bodyValues bodyDone resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyDone resultSlot =>
        emitRangeFoldMultiSlot scratch resultWidth start stop step initValues accStart itemSlot
          bodyValues bodyDone resultSlot
    | .heapLinearPredicate ptr continueTag fieldSlotCount recursiveFieldOffset fieldStart predicate
        stopWhenTrue terminalValue =>
        emitHeapLinearPredicate scratch ptr continueTag fieldSlotCount recursiveFieldOffset fieldStart
          predicate stopWhenTrue terminalValue
    | .call index args => args.flatMap (emitExpr scratch) ++ call index
    | .letCall slots index args body =>
        args.flatMap (emitExpr scratch) ++ call index ++
          slots.reverse.flatMap localSet ++ emitExpr scratch body

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

partial def emitStmt (scratch : Nat) : Stmt → List UInt8
  | .skip => []
  | .assign index value => emitExpr scratch value ++ localSet index
  | .call slots index args => args.flatMap (emitExpr scratch) ++ call index ++ slots.reverse.flatMap localSet
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart itemStart
      bodyValues bodyDone targets =>
      emitArrayFoldMultiSlotAssign scratch sourceWidth resultWidth array start stop initValues accStart
        itemStart bodyValues bodyDone targets
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyDone targets =>
      emitByteArrayFoldMultiSlotAssign scratch resultWidth ptr len start stop initValues accStart
        byteSlot bodyValues bodyDone targets
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot bodyValues
      bodyDone targets =>
      emitRangeFoldMultiSlotAssign scratch resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyDone targets
  | .ite cond thenStmt elseStmt =>
      emitCond scratch cond ++ ofNats [4, 64] ++
        emitStmt scratch thenStmt ++
        ofNats [5] ++
        emitStmt scratch elseStmt ++
        ofNats [11]
  | .seq first second => emitStmt scratch first ++ emitStmt scratch second
  | .while cond loopBody =>
      ofNats [2, 64, 3, 64] ++
      emitCond scratch cond ++ ofNats [69, 13, 1] ++
      emitStmt scratch loopBody ++
      ofNats [12, 0, 11, 11]

def localDecls (func : Func) : List UInt8 :=
  let extra := func.locals - func.params + funcScratch func
  if extra == 0 then
    ofNats [0]
  else
    u32leb 1 ++ u32leb extra ++ ofNats [126]

def emitFuncBody (func : Func) : List UInt8 :=
  let scratch := func.locals
  body (localDecls func) (emitStmt scratch func.body ++ func.results.flatMap (emitExpr scratch))

def typeForFunc (func : Func) : List UInt8 :=
  funcType (List.replicate func.params i64) (List.replicate func.results.length i64)

def typeSection (module_ : Module) : List UInt8 :=
  wasmSection 1 <| vec (
    module_.funcs.toList.map typeForFunc ++
      [funcType [i64] [i64], funcType [] []])

def functionSection (module_ : Module) : List UInt8 :=
  wasmSection 3 <| u32Vec (List.range (module_.funcs.size + 2))

def exportSection (module_ : Module) : List UInt8 :=
  wasmSection 7 <| vec <|
    [exportEntry "memory" 2 0] ++
      (enumerate module_.funcs.toList |>.filterMap fun item =>
        item.snd.exportName.map (fun exportName => exportEntry exportName 0 item.fst)) ++
      [exportEntry "alloc" 0 module_.funcs.size,
        exportEntry "reset" 0 (module_.funcs.size + 1)]

def coreAllocBody : List UInt8 :=
  body
    (ofNats [0])
    (globalGet 0 ++ globalGet 0 ++ localGet 0 ++ ofNats [124] ++ globalSet 0)

def coreResetBody : List UInt8 :=
  body
    (ofNats [0])
    (i64Const 4096 ++ globalSet 0)

def codeSection (module_ : Module) : List UInt8 :=
  wasmSection 10 <| vec (module_.funcs.toList.map emitFuncBody ++ [coreAllocBody, coreResetBody])

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

def wasiTypeSection (module_ : Module) : List UInt8 :=
  wasmSection 1 <| vec (
    [funcType [i32, i32, i32, i32] [i32]] ++
      module_.funcs.toList.map typeForFunc ++
      [funcType [] []])

def wasiFunctionSection (module_ : Module) : List UInt8 :=
  wasmSection 3 <| u32Vec ((List.range (module_.funcs.size + 1)).map (fun index => index + 1))

def wasiExportSection (module_ : Module) : List UInt8 :=
  wasmSection 7 <| vec [
    exportEntry "memory" 2 0,
    exportEntry "_start" 0 (module_.funcs.size + 1)
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

def wasiStartBody (entryIndex : Nat) : List UInt8 :=
  body
    (ofNats [1, 2, 126])
    (call entryIndex ++
      localSet 1 ++
      localSet 0 ++
      i32Const 0 ++ localGet 0 ++ i32WrapI64 ++ i32Store ++
      i32Const 4 ++ localGet 1 ++ i32WrapI64 ++ i32Store ++
      i32Const 8 ++ i32Const 0 ++ i32Store ++
      i32Const 1 ++ i32Const 0 ++ i32Const 1 ++ i32Const 8 ++ call 0 ++
      ofNats [69, 4, 64] ++
        i32Const 8 ++ i32Load ++ localGet 1 ++ i32WrapI64 ++
        ofNats [70, 4, 64, 5, 0, 11, 5, 0, 11])

def wasiCodeSection (module_ : Module) (entryIndex : Nat) : List UInt8 :=
  let shifted := shiftModuleCalls 1 module_
  wasmSection 10 <| vec (
    shifted.funcs.toList.map emitFuncBody ++
      [wasiStartBody (entryIndex + 1)])

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
    ++ wasiExportSection module_
    ++ wasiCodeSection module_ entryIndex).toArray

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
  partial def arrayAllocSlotsWatLines (scratch width : Nat) (cells : Expr) : List String :=
    let len := scratch
    let ptr := scratch + 1
    exprWatLines (scratch + 2) cells ++
      [s!"local.set {len}", "global.get 0", s!"local.set {ptr}",
        s!"local.get {ptr}", "i32.wrap_i64", s!"local.get {len}", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {len}", s!"i64.const {width}",
        "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0",
        s!"local.get {ptr}"]

  partial def heapAllocSlotsWatLines (scratch : Nat) (values : List Expr) : List String :=
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
      (scratch width : Nat)
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
      (scratch width : Nat)
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
      (scratch width : Nat)
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

  partial def arrayPopSlotsWatLines (scratch width : Nat) (array : Expr) : List String :=
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

  partial def arrayAppendSlotsWatLines (scratch width : Nat) (left right : Expr) : List String :=
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
      (scratch width : Nat)
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
      (scratch sourceWidth resultWidth : Nat)
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
      (bodyDone : Expr)
      (resultSlot : Nat) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (bodyDone : Expr)
      (targets : List Nat) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (scratch sourceWidth : Nat)
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
      (scratch width : Nat)
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
      (scratch width : Nat)
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
      (scratch width : Nat)
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
      (scratch width : Nat)
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

  partial def byteArrayFoldMultiSlotWatLines
      (scratch resultWidth : Nat)
      (ptr len start stop : Expr)
      (initValues : List Expr)
      (accStart byteSlot : Nat)
      (bodyValues : List Expr)
      (bodyDone : Expr)
      (resultSlot : Nat) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (bodyDone : Expr)
      (targets : List Nat) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    let bodyScratch :=
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
      (bodyDone : Expr)
      (resultSlot : Nat) : List String :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let bodyScratch :=
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
      (bodyDone : Expr)
      (targets : List Nat) : List String :=
    let indexLocal := scratch
    let stopLocal := scratch + 1
    let stepLocal := scratch + 2
    let childScratch := scratch + 3
    let bodyScratch :=
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
    | .arrayAllocSlots width cells => arrayAllocSlotsWatLines scratch width cells
    | .heapAllocSlots values => heapAllocSlotsWatLines scratch values
    | .heapLoadSlot ptr slot => heapLoadSlotWatLines scratch ptr slot
    | .arrayReplicateSlots width cells values =>
        arrayReplicateSlotsWatLines scratch width cells values
    | .arraySize array => arraySizeWatLines scratch array
    | .arrayGetSlot width slot array index =>
        arrayGetSlotWatLines scratch width slot array index
    | .arraySetSlots width array index values =>
        arraySetSlotsWatLines scratch width array index values
    | .arrayPushSlots width array values => arrayPushSlotsWatLines scratch width array values
    | .arrayPopSlots width array => arrayPopSlotsWatLines scratch width array
    | .arrayAppendSlots width left right => arrayAppendSlotsWatLines scratch width left right
    | .arrayExtractSlots width array start stop =>
        arrayExtractSlotsWatLines scratch width array start stop
    | .arrayMapSlots sourceWidth resultWidth array itemStart bodyValues =>
        arrayMapSlotsWatLines scratch sourceWidth resultWidth array itemStart bodyValues
    | .arrayFoldMultiSlot sourceWidth resultWidth array start stop initValues accStart itemStart
        bodyValues bodyDone resultSlot =>
        arrayFoldMultiSlotWatLines scratch sourceWidth resultWidth array start stop initValues accStart
          itemStart bodyValues bodyDone resultSlot
    | .arrayFindIdxSlots sourceWidth array itemStart predicate returnPayload =>
        arrayFindIdxSlotsWatLines scratch sourceWidth array itemStart predicate returnPayload
    | .arrayFindSlot sourceWidth array itemStart predicate slot =>
        arrayFindSlotWatLines scratch sourceWidth array itemStart predicate slot
    | .arrayAnySlots sourceWidth array start stop itemStart predicate forAll =>
        arrayAnySlotsWatLines scratch sourceWidth array start stop itemStart predicate forAll
    | .arrayFilterSlots sourceWidth array start stop itemStart predicate =>
        arrayFilterSlotsWatLines scratch sourceWidth array start stop itemStart predicate
    | .arrayInsertIfInBoundsSlots width array index values =>
        arrayInsertIfInBoundsSlotsWatLines scratch width array index values
    | .arrayEraseIfInBoundsSlots width array index =>
        arrayEraseIfInBoundsSlotsWatLines scratch width array index
    | .arraySwapIfInBoundsSlots width array left right =>
        arraySwapIfInBoundsSlotsWatLines scratch width array left right
    | .arrayReverseSlots width array => arrayReverseSlotsWatLines scratch width array
    | .byteArrayGet ptr len index => byteArrayGetWatLines scratch ptr len index
    | .byteArrayPushPtr ptr len value => byteArrayPushPtrWatLines scratch ptr len value
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        byteArrayAppendPtrWatLines scratch leftPtr leftLen rightPtr rightLen
    | .byteArraySetPtr ptr len index value => byteArraySetPtrWatLines scratch ptr len index value
    | .byteArrayFromArrayPtr array => byteArrayFromArrayPtrWatLines scratch array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        byteArrayCopySlicePtrWatLines scratch srcPtr srcLen srcOff destPtr destLen destOff copyLen
    | .byteArrayFindIdx ptr len start byteSlot predicate returnPayload =>
        byteArrayFindIdxWatLines scratch ptr len start byteSlot predicate returnPayload
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyDone resultSlot =>
        byteArrayFoldMultiSlotWatLines scratch resultWidth ptr len start stop initValues accStart
          byteSlot bodyValues bodyDone resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyDone resultSlot =>
        rangeFoldMultiSlotWatLines scratch resultWidth start stop step initValues accStart itemSlot
          bodyValues bodyDone resultSlot
    | .heapLinearPredicate ptr continueTag fieldSlotCount recursiveFieldOffset fieldStart predicate
        stopWhenTrue terminalValue =>
        heapLinearPredicateWatLines scratch ptr continueTag fieldSlotCount recursiveFieldOffset
          fieldStart predicate stopWhenTrue terminalValue
    | .call index args => args.flatMap (exprWatLines scratch) ++ [s!"call {index}"]
    | .letCall slots index args body =>
        args.flatMap (exprWatLines scratch) ++ [s!"call {index}"] ++
          slots.reverse.map (fun slot => s!"local.set {slot}") ++ exprWatLines scratch body

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

partial def stmtWatLines (scratch : Nat) : Stmt → List String
  | .skip => []
  | .assign index value => exprWatLines scratch value ++ [s!"local.set {index}"]
  | .call slots index args =>
      args.flatMap (exprWatLines scratch) ++ [s!"call {index}"] ++
        slots.reverse.map (fun slot => s!"local.set {slot}")
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth array start stop initValues accStart itemStart
      bodyValues bodyDone targets =>
      arrayFoldMultiSlotAssignWatLines scratch sourceWidth resultWidth array start stop initValues
        accStart itemStart bodyValues bodyDone targets
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyDone targets =>
      byteArrayFoldMultiSlotAssignWatLines scratch resultWidth ptr len start stop initValues accStart
        byteSlot bodyValues bodyDone targets
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot bodyValues
      bodyDone targets =>
      rangeFoldMultiSlotAssignWatLines scratch resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyDone targets
  | .ite cond thenStmt elseStmt =>
      condWatLines scratch cond ++ ["if"] ++
        indent 2 (stmtWatLines scratch thenStmt) ++
        ["else"] ++
        indent 2 (stmtWatLines scratch elseStmt) ++
        ["end"]
  | .seq first second => stmtWatLines scratch first ++ stmtWatLines scratch second
  | .while cond loopBody =>
      ["block", "  loop"] ++
        indent 4 (condWatLines scratch cond ++ ["i32.eqz", "br_if 1"] ++
          stmtWatLines scratch loopBody ++ ["br 0"]) ++
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

def funcWatLines (func : Func) : List String :=
  let extra := func.locals - func.params + funcScratch func
  let scratch := func.locals
  let exportText :=
    match func.exportName with
    | some exportName => s!" (export \"{exportName}\")"
    | none => ""
  [s!"(func{exportText}{paramWat func.params}{resultWat func.results.length}"] ++
    indent 2
      (localWat extra ++ stmtWatLines scratch func.body ++
        func.results.flatMap (exprWatLines scratch)) ++
    [")"]

def moduleWat (module_ : Module) : String :=
  String.intercalate "\n" <|
    ["(module", "  (memory (export \"memory\") 16)", "  (global (mut i64) (i64.const 4096))"] ++
      (module_.funcs.toList.flatMap (fun func => indent 2 (funcWatLines func))) ++
      indent 2 [
        "(func (export \"alloc\") (param i64) (result i64)",
        "  global.get 0",
        "  global.get 0",
        "  local.get 0",
        "  i64.add",
        "  global.set 0",
        ")",
        "(func (export \"reset\")",
        "  i64.const 4096",
        "  global.set 0",
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
