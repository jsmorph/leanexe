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
    | .arrayReplicate cells value => 4 + max (exprScratch cells) (exprScratch value)
    | .arraySize array => 1 + exprScratch array
    | .arrayGet array index => 2 + max (exprScratch array) (exprScratch index)
    | .arraySet array index value =>
        6 + max (exprScratch array) (max (exprScratch index) (exprScratch value))
    | .arrayPush array value => 5 + max (exprScratch array) (exprScratch value)
    | .arrayPop array => 5 + exprScratch array
    | .arrayAppend left right => 7 + max (exprScratch left) (exprScratch right)
    | .arrayExtract array start stop =>
        8 + max (exprScratch array) (max (exprScratch start) (exprScratch stop))
    | .arrayInsertIfInBounds array index value =>
        7 + max (exprScratch array) (max (exprScratch index) (exprScratch value))
    | .arrayEraseIfInBounds array index =>
        6 + max (exprScratch array) (exprScratch index)
    | .byteArrayGet ptr len index =>
        3 + max (exprScratch ptr) (max (exprScratch len) (exprScratch index))
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
  max (stmtScratch func.body) (exprScratch func.result)

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
    | .arrayReplicate cells value => emitArrayReplicate scratch cells value
    | .arraySize array => emitArraySize scratch array
    | .arrayGet array index => emitArrayGet scratch array index
    | .arraySet array index value => emitArraySet scratch array index value
    | .arrayPush array value => emitArrayPush scratch array value
    | .arrayPop array => emitArrayPop scratch array
    | .arrayAppend left right => emitArrayAppend scratch left right
    | .arrayExtract array start stop => emitArrayExtract scratch array start stop
    | .arrayInsertIfInBounds array index value =>
        emitArrayInsertIfInBounds scratch array index value
    | .arrayEraseIfInBounds array index => emitArrayEraseIfInBounds scratch array index
    | .byteArrayGet ptr len index => emitByteArrayGet scratch ptr len index
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
  body (localDecls func) (emitStmt scratch func.body ++ emitExpr scratch func.result)

def typeForFunc (func : Func) : List UInt8 :=
  funcType (List.replicate func.params i64) [i64]

def typeSection (module_ : Module) : List UInt8 :=
  wasmSection 1 <| vec (
    module_.funcs.toList.map typeForFunc ++
      [funcType [i64] [i64], funcType [] []])

def functionSection (module_ : Module) : List UInt8 :=
  wasmSection 3 <| u32Vec (List.range (module_.funcs.size + 2))

def enumerateAux {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | item :: rest, index => (index, item) :: enumerateAux rest (index + 1)

def enumerate {α : Type} (items : List α) : List (Nat × α) :=
  enumerateAux items 0

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

mutual
  partial def arrayAllocWatLines (scratch : Nat) (cells : Expr) : List String :=
    let len := scratch
    let ptr := scratch + 1
    exprWatLines (scratch + 2) cells ++
      [s!"local.set {len}", "global.get 0", s!"local.set {ptr}",
        s!"local.get {ptr}", "i32.wrap_i64", s!"local.get {len}", "i64.store align=8",
        "global.get 0", "i64.const 8", s!"local.get {len}", "i64.const 8", "i64.mul",
        "i64.add", "i64.add", "global.set 0", s!"local.get {ptr}"]

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
    | .arrayReplicate cells value => arrayReplicateWatLines scratch cells value
    | .arraySize array => arraySizeWatLines scratch array
    | .arrayGet array index => arrayGetWatLines scratch array index
    | .arraySet array index value => arraySetWatLines scratch array index value
    | .arrayPush array value => arrayPushWatLines scratch array value
    | .arrayPop array => arrayPopWatLines scratch array
    | .arrayAppend left right => arrayAppendWatLines scratch left right
    | .arrayExtract array start stop => arrayExtractWatLines scratch array start stop
    | .arrayInsertIfInBounds array index value =>
        arrayInsertIfInBoundsWatLines scratch array index value
    | .arrayEraseIfInBounds array index => arrayEraseIfInBoundsWatLines scratch array index
    | .byteArrayGet ptr len index => byteArrayGetWatLines scratch ptr len index
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

def funcWatLines (func : Func) : List String :=
  let extra := func.locals - func.params + funcScratch func
  let scratch := func.locals
  let exportText :=
    match func.exportName with
    | some exportName => s!" (export \"{exportName}\")"
    | none => ""
  [s!"(func{exportText}{paramWat func.params} (result i64)"] ++
    indent 2 (localWat extra ++ stmtWatLines scratch func.body ++ exprWatLines scratch func.result) ++
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
