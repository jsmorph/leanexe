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

def i64Store : List UInt8 :=
  ofNats [55, 3, 0]

def i32Load8U : List UInt8 :=
  ofNats [45, 0, 0]

def i32Store8 : List UInt8 :=
  ofNats [58, 0, 0]

def i64ExtendI32U : List UInt8 :=
  ofNats [173]

def i64LtU : List UInt8 :=
  ofNats [84]

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
    | .arrayAlloc cells => 2 + exprScratch cells
    | .arrayAllocSlots _ cells => 2 + exprScratch cells
    | .arrayReplicate cells value => 4 + max (exprScratch cells) (exprScratch value)
    | .arrayReplicateSlots _ cells values =>
        3 + values.length +
          max (exprScratch cells) (values.foldl (fun n value => max n (exprScratch value)) 0)
    | .arraySize array => 1 + exprScratch array
    | .arrayGet array index => 2 + max (exprScratch array) (exprScratch index)
    | .arrayGetSlot _ _ array index => 2 + max (exprScratch array) (exprScratch index)
    | .arraySet array index value =>
        6 + max (exprScratch array) (max (exprScratch index) (exprScratch value))
    | .arraySetSlots _ array index values =>
        6 + values.length +
          max (exprScratch array)
            (max (exprScratch index) (values.foldl (fun n value => max n (exprScratch value)) 0))
    | .arrayPush array value => 5 + max (exprScratch array) (exprScratch value)
    | .arrayPushSlots _ array values =>
        6 + values.length +
          max (exprScratch array) (values.foldl (fun n value => max n (exprScratch value)) 0)
    | .arrayPop array => 5 + exprScratch array
    | .arrayPopSlots _ array => 6 + exprScratch array
    | .arrayAppend left right => 7 + max (exprScratch left) (exprScratch right)
    | .arrayAppendSlots _ left right => 9 + max (exprScratch left) (exprScratch right)
    | .arrayExtract array start stop =>
        8 + max (exprScratch array) (max (exprScratch start) (exprScratch stop))
    | .arrayExtractSlots _ array start stop =>
        10 + max (exprScratch array) (max (exprScratch start) (exprScratch stop))
    | .arrayMap array _ body => 4 + max (exprScratch array) (exprScratch body)
    | .arrayMapSlots _ _ array _ bodyValues =>
        4 + max (exprScratch array)
          (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    | .arrayInsertIfInBounds array index value =>
        7 + max (exprScratch array) (max (exprScratch index) (exprScratch value))
    | .arrayInsertIfInBoundsSlots _ array index values =>
        8 + values.length +
          max (exprScratch array)
            (max (exprScratch index) (values.foldl (fun n value => max n (exprScratch value)) 0))
    | .arrayEraseIfInBounds array index =>
        6 + max (exprScratch array) (exprScratch index)
    | .arrayEraseIfInBoundsSlots _ array index =>
        8 + max (exprScratch array) (exprScratch index)
    | .arraySwapIfInBounds array left right =>
        6 + max (exprScratch array) (max (exprScratch left) (exprScratch right))
    | .arraySwapIfInBoundsSlots _ array left right =>
        7 + max (exprScratch array) (max (exprScratch left) (exprScratch right))
    | .arrayReverse array => 4 + exprScratch array
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
    | .byteArrayFold ptr len start stop init _ _ body =>
        7 + max
          (max (exprScratch ptr) (exprScratch len))
          (max (max (exprScratch start) (exprScratch stop))
            (max (exprScratch init) (exprScratch body)))
    | .call _ args => args.foldl (fun count arg => max count (exprScratch arg)) 0

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

def emitPrefixCopyLoop
    (arrayLocal newLocal indexLocal loopLocal : Nat) : List UInt8 :=
  i64Const 0 ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet indexLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
      arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

def emitInsertSuffixLoop
    (arrayLocal newLocal indexLocal lenLocal loopLocal : Nat) : List UInt8 :=
  localGet indexLocal ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress
        (localGet newLocal)
        (localGet loopLocal ++ i64Const 1 ++ ofNats [124]) ++
      arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

def emitEraseSuffixLoop
    (arrayLocal newLocal indexLocal newLenLocal loopLocal : Nat) : List UInt8 :=
  localGet indexLocal ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet newLenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
      arrayCellAddress
        (localGet arrayLocal)
        (localGet loopLocal ++ i64Const 1 ++ ofNats [124]) ++
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

def emitReverseCopyLoop (arrayLocal newLocal lenLocal loopLocal : Nat) : List UInt8 :=
  i64Const 0 ++ localSet loopLocal ++
    ofNats [2, 64, 3, 64] ++
      localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
      arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
      arrayCellAddress
        (localGet arrayLocal)
        (localGet lenLocal ++ localGet loopLocal ++ ofNats [125] ++ i64Const 1 ++
          ofNats [125]) ++
      i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
      ofNats [12] ++ u32leb 0 ++
    ofNats [11, 11]

mutual
  partial def emitArrayAlloc (scratch : Nat) (cells : Expr) : List UInt8 :=
    let len := scratch
    let ptr := scratch + 1
    emitExpr (scratch + 2) cells ++ localSet len ++
      globalGet 0 ++ localSet ptr ++
      localGet ptr ++ i32WrapI64 ++ localGet len ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet len ++ i64Const 8 ++
        ofNats [126, 124, 124] ++ globalSet 0 ++
      localGet ptr

  partial def emitArrayAllocSlots (scratch width : Nat) (cells : Expr) : List UInt8 :=
    let len := scratch
    let ptr := scratch + 1
    emitExpr (scratch + 2) cells ++ localSet len ++
      globalGet 0 ++ localSet ptr ++
      localGet ptr ++ i32WrapI64 ++ localGet len ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet len ++ i64Const width ++ ofNats [126] ++
        i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
      localGet ptr

  partial def emitFillLoop (newLocal lenLocal valueLocal loopLocal : Nat) : List UInt8 :=
    i64Const 0 ++ localSet loopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        arrayCellAddress (localGet newLocal) (localGet loopLocal) ++ localGet valueLocal ++ i64Store ++
        localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11]

  partial def emitArrayReplicate (scratch : Nat) (cells value : Expr) : List UInt8 :=
    let lenLocal := scratch
    let valueLocal := scratch + 1
    let ptrLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    emitExpr childScratch cells ++ localSet lenLocal ++
      emitExpr childScratch value ++ localSet valueLocal ++
      globalGet 0 ++ localSet ptrLocal ++
      localGet ptrLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const 8 ++
        ofNats [126, 124, 124] ++ globalSet 0 ++
      emitFillLoop ptrLocal lenLocal valueLocal loopLocal ++
      localGet ptrLocal

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

  partial def emitArrayGet (scratch : Nat) (array index : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let childScratch := scratch + 2
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet indexLocal ++ localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ i64LtU ++
      ofNats [4, 126] ++
        arrayCellAddress (localGet arrayLocal) (localGet indexLocal) ++ i64Load ++
      ofNats [5] ++
        ofNats [0] ++
      ofNats [11]

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

  partial def emitArraySet (scratch : Nat) (array index value : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let valueLocal := scratch + 2
    let lenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      emitExpr childScratch value ++ localSet valueLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal lenLocal loopLocal ++
        arrayCellAddress (localGet newLocal) (localGet indexLocal) ++
          localGet valueLocal ++ i64Store ++
        localGet newLocal ++
      ofNats [5] ++
        ofNats [0] ++
      ofNats [11]

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

  partial def emitArrayPush (scratch : Nat) (array value : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let valueLocal := scratch + 1
    let lenLocal := scratch + 2
    let newLocal := scratch + 3
    let loopLocal := scratch + 4
    let childScratch := scratch + 5
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch value ++ localSet valueLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Const 1 ++
        ofNats [124] ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const 1 ++ ofNats [124] ++
        i64Const 8 ++ ofNats [126, 124, 124] ++ globalSet 0 ++
      emitCopyLoop arrayLocal newLocal lenLocal loopLocal ++
      arrayCellAddress (localGet newLocal) (localGet lenLocal) ++ localGet valueLocal ++ i64Store ++
      localGet newLocal

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

  partial def emitArrayPop (scratch : Nat) (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLenLocal := scratch + 2
    let newLocal := scratch + 3
    let loopLocal := scratch + 4
    let childScratch := scratch + 5
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const 0 ++ ofNats [81] ++
      ofNats [4, 126] ++
        localGet arrayLocal ++
      ofNats [5] ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [125] ++ localSet newLenLocal ++
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal newLenLocal loopLocal ++
        localGet newLocal ++
      ofNats [11]

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

  partial def emitArrayAppend (scratch : Nat) (left right : Expr) : List UInt8 :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let leftLenLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let newLenLocal := scratch + 4
    let newLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ i32WrapI64 ++ i64Load ++ localSet leftLenLocal ++
      localGet rightLocal ++ i32WrapI64 ++ i64Load ++ localSet rightLenLocal ++
      localGet leftLenLocal ++ localGet rightLenLocal ++ ofNats [124] ++
        localSet newLenLocal ++
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const 8 ++
        ofNats [126, 124, 124] ++ globalSet 0 ++
      emitCopyLoop leftLocal newLocal leftLenLocal loopLocal ++
      emitCopyLoopAt rightLocal newLocal leftLenLocal rightLenLocal loopLocal ++
      localGet newLocal

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

  partial def emitArrayExtract (scratch : Nat) (array start stop : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let startLocal := scratch + 1
    let stopLocal := scratch + 2
    let sourceLenLocal := scratch + 3
    let stopBoundLocal := scratch + 4
    let newLenLocal := scratch + 5
    let newLocal := scratch + 6
    let loopLocal := scratch + 7
    let childScratch := scratch + 8
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
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const 8 ++
        ofNats [126, 124, 124] ++ globalSet 0 ++
      emitExtractCopyLoop arrayLocal newLocal startLocal newLenLocal loopLocal ++
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

  partial def emitArrayMap
      (scratch : Nat)
      (array : Expr)
      (itemSlot : Nat)
      (body : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      globalGet 0 ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
      globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const 8 ++
        ofNats [126, 124, 124] ++ globalSet 0 ++
      i64Const 0 ++ localSet loopLocal ++
      ofNats [2, 64, 3, 64] ++
        localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ ofNats [13] ++ u32leb 1 ++
        arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++
          localSet itemSlot ++
        arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
          emitExpr childScratch body ++ i64Store ++
        localGet loopLocal ++ i64Const 1 ++ ofNats [124] ++ localSet loopLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
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

  partial def emitArrayInsertIfInBounds (scratch : Nat) (array index value : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let valueLocal := scratch + 3
    let newLenLocal := scratch + 4
    let newLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LeU ++
      ofNats [4, 126] ++
        emitExpr childScratch value ++ localSet valueLocal ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [124] ++ localSet newLenLocal ++
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitPrefixCopyLoop arrayLocal newLocal indexLocal loopLocal ++
        arrayCellAddress (localGet newLocal) (localGet indexLocal) ++
          localGet valueLocal ++ i64Store ++
        emitInsertSuffixLoop arrayLocal newLocal indexLocal lenLocal loopLocal ++
        localGet newLocal ++
      ofNats [5] ++
        localGet arrayLocal ++
      ofNats [11]

  partial def emitArrayEraseIfInBounds (scratch : Nat) (array index : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let newLenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ofNats [4, 126] ++
        localGet lenLocal ++ i64Const 1 ++ ofNats [125] ++ localSet newLenLocal ++
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet newLenLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitPrefixCopyLoop arrayLocal newLocal indexLocal loopLocal ++
        emitEraseSuffixLoop arrayLocal newLocal indexLocal newLenLocal loopLocal ++
        localGet newLocal ++
      ofNats [5] ++
        localGet arrayLocal ++
      ofNats [11]

  partial def emitArraySwapIfInBounds (scratch : Nat) (array left right : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let leftLocal := scratch + 1
    let rightLocal := scratch + 2
    let lenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let swapBody :=
      globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitCopyLoop arrayLocal newLocal lenLocal loopLocal ++
        arrayCellAddress (localGet newLocal) (localGet leftLocal) ++
          arrayCellAddress (localGet arrayLocal) (localGet rightLocal) ++ i64Load ++ i64Store ++
        arrayCellAddress (localGet newLocal) (localGet rightLocal) ++
          arrayCellAddress (localGet arrayLocal) (localGet leftLocal) ++ i64Load ++ i64Store ++
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

  partial def emitArrayReverse (scratch : Nat) (array : Expr) : List UInt8 :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const 1 ++ i64LeU ++
      ofNats [4, 126] ++
        localGet arrayLocal ++
      ofNats [5] ++
        globalGet 0 ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        globalGet 0 ++ i64Const 8 ++ localGet lenLocal ++ i64Const 8 ++
          ofNats [126, 124, 124] ++ globalSet 0 ++
        emitReverseCopyLoop arrayLocal newLocal lenLocal loopLocal ++
        localGet newLocal ++
      ofNats [11]

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

  partial def emitByteArrayFold
      (scratch : Nat)
      (ptr len start stop init : Expr)
      (accSlot byteSlot : Nat)
      (foldBody : Expr) : List UInt8 :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitExpr childScratch init ++ localSet accSlot ++
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
        emitExpr childScratch foldBody ++ localSet accSlot ++
        localGet indexLocal ++ i64Const 1 ++ ofNats [124] ++ localSet indexLocal ++
        ofNats [12] ++ u32leb 0 ++
      ofNats [11, 11] ++
      localGet accSlot

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
    | .arrayAlloc cells => emitArrayAlloc scratch cells
    | .arrayAllocSlots width cells => emitArrayAllocSlots scratch width cells
    | .arrayReplicate cells value => emitArrayReplicate scratch cells value
    | .arrayReplicateSlots width cells values =>
        emitArrayReplicateSlots scratch width cells values
    | .arraySize array => emitArraySize scratch array
    | .arrayGet array index => emitArrayGet scratch array index
    | .arrayGetSlot width slot array index => emitArrayGetSlot scratch width slot array index
    | .arraySet array index value => emitArraySet scratch array index value
    | .arraySetSlots width array index values =>
        emitArraySetSlots scratch width array index values
    | .arrayPush array value => emitArrayPush scratch array value
    | .arrayPushSlots width array values => emitArrayPushSlots scratch width array values
    | .arrayPop array => emitArrayPop scratch array
    | .arrayPopSlots width array => emitArrayPopSlots scratch width array
    | .arrayAppend left right => emitArrayAppend scratch left right
    | .arrayAppendSlots width left right => emitArrayAppendSlots scratch width left right
    | .arrayExtract array start stop => emitArrayExtract scratch array start stop
    | .arrayExtractSlots width array start stop =>
        emitArrayExtractSlots scratch width array start stop
    | .arrayMap array itemSlot body => emitArrayMap scratch array itemSlot body
    | .arrayMapSlots sourceWidth resultWidth array itemStart bodyValues =>
        emitArrayMapSlots scratch sourceWidth resultWidth array itemStart bodyValues
    | .arrayInsertIfInBounds array index value =>
        emitArrayInsertIfInBounds scratch array index value
    | .arrayInsertIfInBoundsSlots width array index values =>
        emitArrayInsertIfInBoundsSlots scratch width array index values
    | .arrayEraseIfInBounds array index => emitArrayEraseIfInBounds scratch array index
    | .arrayEraseIfInBoundsSlots width array index =>
        emitArrayEraseIfInBoundsSlots scratch width array index
    | .arraySwapIfInBounds array left right =>
        emitArraySwapIfInBounds scratch array left right
    | .arraySwapIfInBoundsSlots width array left right =>
        emitArraySwapIfInBoundsSlots scratch width array left right
    | .arrayReverse array => emitArrayReverse scratch array
    | .arrayReverseSlots width array => emitArrayReverseSlots scratch width array
    | .byteArrayGet ptr len index => emitByteArrayGet scratch ptr len index
    | .byteArrayPushPtr ptr len value => emitByteArrayPushPtr scratch ptr len value
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        emitByteArrayAppendPtr scratch leftPtr leftLen rightPtr rightLen
    | .byteArraySetPtr ptr len index value =>
        emitByteArraySetPtr scratch ptr len index value
    | .byteArrayFromArrayPtr array => emitByteArrayFromArrayPtr scratch array
    | .byteArrayFold ptr len start stop init accSlot byteSlot body =>
        emitByteArrayFold scratch ptr len start stop init accSlot byteSlot body
    | .call index args => args.flatMap (emitExpr scratch) ++ call index

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

def prefixCopyLoopWat
    (arrayLocal newLocal indexLocal loopLocal : Nat) : List String :=
  [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {indexLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
      arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {loopLocal}"] ++
      ["i64.load align=8", "i64.store align=8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

def insertSuffixLoopWat
    (arrayLocal newLocal indexLocal lenLocal loopLocal : Nat) : List String :=
  [s!"local.get {indexLocal}", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat
        [s!"local.get {newLocal}"]
        [s!"local.get {loopLocal}", "i64.const 1", "i64.add"] ++
      arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {loopLocal}"] ++
      ["i64.load align=8", "i64.store align=8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

def eraseSuffixLoopWat
    (arrayLocal newLocal indexLocal newLenLocal loopLocal : Nat) : List String :=
  [s!"local.get {indexLocal}", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {newLenLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
      arrayCellAddressWat
        [s!"local.get {arrayLocal}"]
        [s!"local.get {loopLocal}", "i64.const 1", "i64.add"] ++
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

def reverseCopyLoopWat (arrayLocal newLocal lenLocal loopLocal : Nat) : List String :=
  [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
    indent 4 (
      [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
      arrayCellAddressWat
        [s!"local.get {arrayLocal}"]
        [s!"local.get {lenLocal}", s!"local.get {loopLocal}", "i64.sub",
          "i64.const 1", "i64.sub"] ++
      ["i64.load align=8", "i64.store align=8",
        s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
        "br 0"]) ++
    ["  end", "end"]

mutual
  partial def arrayAllocWatLines (scratch : Nat) (cells : Expr) : List String :=
    let len := scratch
    let ptr := scratch + 1
    exprWatLines (scratch + 2) cells ++
      [s!"local.set {len}", "global.get 0", s!"local.set {ptr}",
        s!"local.get {ptr}", "i32.wrap_i64", s!"local.get {len}", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {len}", "i64.const 8", "i64.mul",
        "i64.add", "i64.add", "global.set 0", s!"local.get {ptr}"]

  partial def arrayAllocSlotsWatLines (scratch width : Nat) (cells : Expr) : List String :=
    let len := scratch
    let ptr := scratch + 1
    exprWatLines (scratch + 2) cells ++
      [s!"local.set {len}", "global.get 0", s!"local.set {ptr}",
        s!"local.get {ptr}", "i32.wrap_i64", s!"local.get {len}", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {len}", s!"i64.const {width}",
        "i64.mul", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0",
        s!"local.get {ptr}"]

  partial def fillLoopWat (newLocal lenLocal valueLocal loopLocal : Nat) : List String :=
    [s!"i64.const 0", s!"local.set {loopLocal}", "block", "  loop"] ++
      indent 4 (
        [s!"local.get {loopLocal}", s!"local.get {lenLocal}", "i64.ge_u", "br_if 1"] ++
        arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
        [s!"local.get {valueLocal}", "i64.store align=8",
          s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
          "br 0"]) ++
      ["  end", "end"]

  partial def arrayReplicateWatLines (scratch : Nat) (cells value : Expr) : List String :=
    let lenLocal := scratch
    let valueLocal := scratch + 1
    let ptrLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    exprWatLines childScratch cells ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch value ++ [s!"local.set {valueLocal}",
        "global.get 0", s!"local.set {ptrLocal}",
        s!"local.get {ptrLocal}", "i32.wrap_i64", s!"local.get {lenLocal}", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {lenLocal}", "i64.const 8", "i64.mul",
        "i64.add", "i64.add", "global.set 0"] ++
      fillLoopWat ptrLocal lenLocal valueLocal loopLocal ++
      [s!"local.get {ptrLocal}"]

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

  partial def arrayGetWatLines (scratch : Nat) (array index : Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let childScratch := scratch + 2
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}",
        s!"local.get {indexLocal}", s!"local.get {arrayLocal}", "i32.wrap_i64",
        "i64.load align=8", "i64.lt_u", "if (result i64)"] ++
      indent 2 (arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {indexLocal}"] ++
        ["i64.load align=8"]) ++
      ["else", "  unreachable", "end"]

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

  partial def arraySetWatLines (scratch : Nat) (array index value : Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let valueLocal := scratch + 2
    let lenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch value ++ [s!"local.set {valueLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8", s!"local.set {lenLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.lt_u", "if (result i64)"] ++
      indent 2 (
        ["global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}", "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {lenLocal}", "i64.const 8",
          "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        copyLoopWat arrayLocal newLocal lenLocal loopLocal ++
        arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {indexLocal}"] ++
        [s!"local.get {valueLocal}", "i64.store align=8", s!"local.get {newLocal}"]) ++
      ["else", "  unreachable", "end"]

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

  partial def arrayPushWatLines (scratch : Nat) (array value : Expr) : List String :=
    let arrayLocal := scratch
    let valueLocal := scratch + 1
    let lenLocal := scratch + 2
    let newLocal := scratch + 3
    let loopLocal := scratch + 4
    let childScratch := scratch + 5
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch value ++ [s!"local.set {valueLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8", s!"local.set {lenLocal}",
        "global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}", "i64.const 1",
        "i64.add", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {lenLocal}", "i64.const 1",
        "i64.add", "i64.const 8", "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      copyLoopWat arrayLocal newLocal lenLocal loopLocal ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {lenLocal}"] ++
      [s!"local.get {valueLocal}", "i64.store align=8", s!"local.get {newLocal}"]

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

  partial def arrayPopWatLines (scratch : Nat) (array : Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLenLocal := scratch + 2
    let newLocal := scratch + 3
    let loopLocal := scratch + 4
    let childScratch := scratch + 5
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8", s!"local.set {lenLocal}",
      s!"local.get {lenLocal}", "i64.const 0", "i64.eq", "if (result i64)"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["else"] ++
      indent 2 (
        [s!"local.get {lenLocal}", "i64.const 1", "i64.sub", s!"local.set {newLenLocal}",
          "global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", "i64.const 8",
          "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        copyLoopWat arrayLocal newLocal newLenLocal loopLocal ++
        [s!"local.get {newLocal}"]) ++
      ["end"]

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

  partial def arrayAppendWatLines (scratch : Nat) (left right : Expr) : List String :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let leftLenLocal := scratch + 2
    let rightLenLocal := scratch + 3
    let newLenLocal := scratch + 4
    let newLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
    exprWatLines childScratch left ++ [s!"local.set {leftLocal}"] ++
      exprWatLines childScratch right ++ [s!"local.set {rightLocal}",
        s!"local.get {leftLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {leftLenLocal}",
        s!"local.get {rightLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {rightLenLocal}",
        s!"local.get {leftLenLocal}", s!"local.get {rightLenLocal}", "i64.add",
        s!"local.set {newLenLocal}",
        "global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
        "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", "i64.const 8",
        "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      copyLoopWat leftLocal newLocal leftLenLocal loopLocal ++
      copyLoopAtWat rightLocal newLocal leftLenLocal rightLenLocal loopLocal ++
      [s!"local.get {newLocal}"]

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

  partial def arrayExtractWatLines (scratch : Nat) (array start stop : Expr) : List String :=
    let arrayLocal := scratch
    let startLocal := scratch + 1
    let stopLocal := scratch + 2
    let sourceLenLocal := scratch + 3
    let stopBoundLocal := scratch + 4
    let newLenLocal := scratch + 5
    let newLocal := scratch + 6
    let loopLocal := scratch + 7
    let childScratch := scratch + 8
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
        "global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
        "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", "i64.const 8",
        "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      extractCopyLoopWat arrayLocal newLocal startLocal newLenLocal loopLocal ++
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

  partial def arrayMapWatLines
      (scratch : Nat)
      (array : Expr)
      (itemSlot : Nat)
      (body : Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}",
      s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
      s!"local.set {lenLocal}",
      "global.get 0", s!"local.set {newLocal}",
      s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}",
      "i64.store align=8",
      "global.get 0", "i64.const 8", s!"local.get {lenLocal}", "i64.const 8",
      "i64.mul", "i64.add", "i64.add", "global.set 0",
      "i64.const 0", s!"local.set {loopLocal}",
      "block", "  loop",
      s!"    local.get {loopLocal}", s!"    local.get {lenLocal}", "    i64.ge_u",
      "    br_if 1"] ++
      indent 4 (
        arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {loopLocal}"] ++
        ["i64.load align=8", s!"local.set {itemSlot}"] ++
        arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {loopLocal}"] ++
        exprWatLines childScratch body ++
        ["i64.store align=8",
          s!"local.get {loopLocal}", "i64.const 1", "i64.add", s!"local.set {loopLocal}",
          "br 0"]) ++
      ["  end", "end", s!"local.get {newLocal}"]

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

  partial def arrayInsertIfInBoundsWatLines
      (scratch : Nat)
      (array index value : Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let valueLocal := scratch + 3
    let newLenLocal := scratch + 4
    let newLocal := scratch + 5
    let loopLocal := scratch + 6
    let childScratch := scratch + 7
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {lenLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.le_u",
        "if (result i64)"] ++
      indent 2 (
        exprWatLines childScratch value ++ [s!"local.set {valueLocal}",
          s!"local.get {lenLocal}", "i64.const 1", "i64.add", s!"local.set {newLenLocal}",
          "global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", "i64.const 8",
          "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        prefixCopyLoopWat arrayLocal newLocal indexLocal loopLocal ++
        arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {indexLocal}"] ++
        [s!"local.get {valueLocal}", "i64.store align=8"] ++
        insertSuffixLoopWat arrayLocal newLocal indexLocal lenLocal loopLocal ++
        [s!"local.get {newLocal}"]) ++
      ["else"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["end"]

  partial def arrayEraseIfInBoundsWatLines
      (scratch : Nat)
      (array index : Expr) : List String :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let lenLocal := scratch + 2
    let newLenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    exprWatLines childScratch array ++ [s!"local.set {arrayLocal}"] ++
      exprWatLines childScratch index ++ [s!"local.set {indexLocal}",
        s!"local.get {arrayLocal}", "i32.wrap_i64", "i64.load align=8",
        s!"local.set {lenLocal}",
        s!"local.get {indexLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)"] ++
      indent 2 (
        [s!"local.get {lenLocal}", "i64.const 1", "i64.sub", s!"local.set {newLenLocal}",
          "global.get 0", s!"local.set {newLocal}",
          s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {newLenLocal}",
          "i64.store align=8",
          "global.get 0", "i64.const 8", s!"local.get {newLenLocal}", "i64.const 8",
          "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        prefixCopyLoopWat arrayLocal newLocal indexLocal loopLocal ++
        eraseSuffixLoopWat arrayLocal newLocal indexLocal newLenLocal loopLocal ++
        [s!"local.get {newLocal}"]) ++
      ["else"] ++
      indent 2 [s!"local.get {arrayLocal}"] ++
      ["end"]

  partial def arraySwapIfInBoundsWatLines
      (scratch : Nat)
      (array left right : Expr) : List String :=
    let arrayLocal := scratch
    let leftLocal := scratch + 1
    let rightLocal := scratch + 2
    let lenLocal := scratch + 3
    let newLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let swapBody :=
      ["global.get 0", s!"local.set {newLocal}",
        s!"local.get {newLocal}", "i32.wrap_i64", s!"local.get {lenLocal}",
        "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {lenLocal}", "i64.const 8",
        "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
      copyLoopWat arrayLocal newLocal lenLocal loopLocal ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {leftLocal}"] ++
      arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {rightLocal}"] ++
      ["i64.load align=8", "i64.store align=8"] ++
      arrayCellAddressWat [s!"local.get {newLocal}"] [s!"local.get {rightLocal}"] ++
      arrayCellAddressWat [s!"local.get {arrayLocal}"] [s!"local.get {leftLocal}"] ++
      ["i64.load align=8", "i64.store align=8", s!"local.get {newLocal}"]
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

  partial def arrayReverseWatLines (scratch : Nat) (array : Expr) : List String :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
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
          "global.get 0", "i64.const 8", s!"local.get {lenLocal}", "i64.const 8",
          "i64.mul", "i64.add", "i64.add", "global.set 0"] ++
        reverseCopyLoopWat arrayLocal newLocal lenLocal loopLocal ++
        [s!"local.get {newLocal}"]) ++
      ["end"]

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

  partial def byteArrayFoldWatLines
      (scratch : Nat)
      (ptr len start stop init : Expr)
      (accSlot byteSlot : Nat)
      (foldBody : Expr) : List String :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let stopLocal := scratch + 3
    let effectiveStopLocal := scratch + 4
    let childScratch := scratch + 5
    exprWatLines childScratch ptr ++ [s!"local.set {ptrLocal}"] ++
      exprWatLines childScratch len ++ [s!"local.set {lenLocal}"] ++
      exprWatLines childScratch start ++ [s!"local.set {indexLocal}"] ++
      exprWatLines childScratch stop ++ [s!"local.set {stopLocal}"] ++
      exprWatLines childScratch init ++ [s!"local.set {accSlot}",
        s!"local.get {stopLocal}", s!"local.get {lenLocal}", "i64.lt_u",
        "if (result i64)", s!"  local.get {stopLocal}", "else",
        s!"  local.get {lenLocal}", "end", s!"local.set {effectiveStopLocal}",
        "block", "loop",
        s!"local.get {indexLocal}", s!"local.get {effectiveStopLocal}", "i64.ge_u",
        "br_if 1",
        s!"local.get {ptrLocal}", s!"local.get {indexLocal}", "i64.add", "i32.wrap_i64",
        "i32.load8_u", "i64.extend_i32_u", s!"local.set {byteSlot}"] ++
      exprWatLines childScratch foldBody ++
      [s!"local.set {accSlot}",
        s!"local.get {indexLocal}", "i64.const 1", "i64.add", s!"local.set {indexLocal}",
        "br 0", "end", "end", s!"local.get {accSlot}"]

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
    | .arrayAlloc cells => arrayAllocWatLines scratch cells
    | .arrayAllocSlots width cells => arrayAllocSlotsWatLines scratch width cells
    | .arrayReplicate cells value => arrayReplicateWatLines scratch cells value
    | .arrayReplicateSlots width cells values =>
        arrayReplicateSlotsWatLines scratch width cells values
    | .arraySize array => arraySizeWatLines scratch array
    | .arrayGet array index => arrayGetWatLines scratch array index
    | .arrayGetSlot width slot array index =>
        arrayGetSlotWatLines scratch width slot array index
    | .arraySet array index value => arraySetWatLines scratch array index value
    | .arraySetSlots width array index values =>
        arraySetSlotsWatLines scratch width array index values
    | .arrayPush array value => arrayPushWatLines scratch array value
    | .arrayPushSlots width array values => arrayPushSlotsWatLines scratch width array values
    | .arrayPop array => arrayPopWatLines scratch array
    | .arrayPopSlots width array => arrayPopSlotsWatLines scratch width array
    | .arrayAppend left right => arrayAppendWatLines scratch left right
    | .arrayAppendSlots width left right => arrayAppendSlotsWatLines scratch width left right
    | .arrayExtract array start stop => arrayExtractWatLines scratch array start stop
    | .arrayExtractSlots width array start stop =>
        arrayExtractSlotsWatLines scratch width array start stop
    | .arrayMap array itemSlot body => arrayMapWatLines scratch array itemSlot body
    | .arrayMapSlots sourceWidth resultWidth array itemStart bodyValues =>
        arrayMapSlotsWatLines scratch sourceWidth resultWidth array itemStart bodyValues
    | .arrayInsertIfInBounds array index value =>
        arrayInsertIfInBoundsWatLines scratch array index value
    | .arrayInsertIfInBoundsSlots width array index values =>
        arrayInsertIfInBoundsSlotsWatLines scratch width array index values
    | .arrayEraseIfInBounds array index => arrayEraseIfInBoundsWatLines scratch array index
    | .arrayEraseIfInBoundsSlots width array index =>
        arrayEraseIfInBoundsSlotsWatLines scratch width array index
    | .arraySwapIfInBounds array left right =>
        arraySwapIfInBoundsWatLines scratch array left right
    | .arraySwapIfInBoundsSlots width array left right =>
        arraySwapIfInBoundsSlotsWatLines scratch width array left right
    | .arrayReverse array => arrayReverseWatLines scratch array
    | .arrayReverseSlots width array => arrayReverseSlotsWatLines scratch width array
    | .byteArrayGet ptr len index => byteArrayGetWatLines scratch ptr len index
    | .byteArrayPushPtr ptr len value => byteArrayPushPtrWatLines scratch ptr len value
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        byteArrayAppendPtrWatLines scratch leftPtr leftLen rightPtr rightLen
    | .byteArraySetPtr ptr len index value => byteArraySetPtrWatLines scratch ptr len index value
    | .byteArrayFromArrayPtr array => byteArrayFromArrayPtrWatLines scratch array
    | .byteArrayFold ptr len start stop init accSlot byteSlot body =>
        byteArrayFoldWatLines scratch ptr len start stop init accSlot byteSlot body
    | .call index args => args.flatMap (exprWatLines scratch) ++ [s!"call {index}"]

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
