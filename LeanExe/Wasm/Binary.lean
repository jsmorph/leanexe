import LeanExe.Core
import LeanExe.IR.Core
import LeanExe.Wasm.Instr

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
abbrev Instr := LeanExe.Wasm.Instr

mutual
  /-- Serialize one structured instruction to the exact byte form the fused
  emitter produced.  This is the only place instruction opcodes live. -/
  def encodeInstr : Instr → List UInt8
    | .constI64 n => LeanExe.Wasm.Binary.i64Const n
    | .constI32 n => LeanExe.Wasm.Binary.i32Const n
    | .constI32NegOne => ofNats [65, 127]
    | .localGet n => LeanExe.Wasm.Binary.localGet n
    | .localSet n => LeanExe.Wasm.Binary.localSet n
    | .localTee n => LeanExe.Wasm.Binary.localTee n
    | .globalGet n => LeanExe.Wasm.Binary.globalGet n
    | .globalSet n => LeanExe.Wasm.Binary.globalSet n
    | .call n => LeanExe.Wasm.Binary.call n
    | .addI64 => ofNats [124]
    | .subI64 => ofNats [125]
    | .mulI64 => ofNats [126]
    | .divUI64 => ofNats [128]
    | .remUI64 => ofNats [130]
    | .andI64 => ofNats [131]
    | .orI64 => ofNats [132]
    | .xorI64 => ofNats [133]
    | .shlI64 => ofNats [134]
    | .shrUI64 => ofNats [136]
    | .eqI64 => ofNats [81]
    | .neI64 => ofNats [82]
    | .ltUI64 => ofNats [84]
    | .leUI64 => ofNats [88]
    | .geUI64 => ofNats [90]
    | .eqzI64 => ofNats [80]
    | .eqI32 => ofNats [70]
    | .eqzI32 => ofNats [69]
    | .andI32 => ofNats [113]
    | .wrapI64 => ofNats [167]
    | .extendUI32 => ofNats [173]
    | .load64 => ofNats [41, 3, 0]
    | .load32 => ofNats [40, 2, 0]
    | .load8U => ofNats [45, 0, 0]
    | .store64 => ofNats [55, 3, 0]
    | .store32 => ofNats [54, 2, 0]
    | .store8 => ofNats [58, 0, 0]
    | .memorySize => ofNats [63, 0]
    | .memoryGrow => ofNats [64, 0]
    | .unreachable => ofNats [0]
    | .ret => ofNats [15]
    | .drop => ofNats [26]
    | .block body => ofNats [2, 64] ++ encodeInstrs body ++ ofNats [11]
    | .loop body => ofNats [3, 64] ++ encodeInstrs body ++ ofNats [11]
    | .iff resultI64 thn els =>
        ofNats [4, if resultI64 then 126 else 64] ++ encodeInstrs thn ++
          (match els with
           | some elseBody => ofNats [5] ++ encodeInstrs elseBody
           | none => []) ++
          ofNats [11]
    | .iffI32 thn els =>
        ofNats [4, 127] ++ encodeInstrs thn ++
          (match els with
           | some elseBody => ofNats [5] ++ encodeInstrs elseBody
           | none => []) ++
          ofNats [11]
    | .br depth => ofNats [12] ++ u32leb depth
    | .brIf depth => ofNats [13] ++ u32leb depth

  def encodeInstrs : List Instr → List UInt8
    | [] => []
    | instr :: rest => encodeInstr instr ++ encodeInstrs rest
end

/-! Instruction-building atoms.  These shadow the byte-level helpers of the
same names in the outer namespace, so the emitters below build structured
instructions while the encoder above remains the only byte producer. -/

def i64Const (n : Nat) : List Instr :=
  [.constI64 n]

def i32Const (n : Nat) : List Instr :=
  [.constI32 n]

def localGet (index : Nat) : List Instr :=
  [.localGet index]

def localSet (index : Nat) : List Instr :=
  [.localSet index]

def localTee (index : Nat) : List Instr :=
  [.localTee index]

def call (index : Nat) : List Instr :=
  [.call index]

def globalGet (index : Nat) : List Instr :=
  [.globalGet index]

def globalSet (index : Nat) : List Instr :=
  [.globalSet index]


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
    | .heapAllocSlots childMask ownedMask values =>
        .heapAllocSlots childMask ownedMask (values.map (shiftExprCalls offset))
    | .heapLoadSlot ptr slot =>
        .heapLoadSlot (shiftExprCalls offset ptr) slot
    | .arrayLiteralSlots width childMask elements =>
        .arrayLiteralSlots width childMask
          (elements.map fun element =>
            (element.fst, element.snd.map (shiftExprCalls offset)))
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
    | .arrayFoldMultiSlot sourceWidth resultWidth reverse array start stop initValues accStart
        itemStart bodyValues bodyLets bodyDone releaseOffsets resultSlot =>
        .arrayFoldMultiSlot sourceWidth resultWidth reverse (shiftExprCalls offset array)
          (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart itemStart
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets resultSlot
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
        bodyValues bodyLets bodyDone releaseOffsets resultSlot =>
        .byteArrayFoldMultiSlot resultWidth (shiftExprCalls offset ptr)
          (shiftExprCalls offset len) (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart byteSlot
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone releaseOffsets resultSlot =>
        .rangeFoldMultiSlot resultWidth (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (shiftExprCalls offset step) (initValues.map (shiftExprCalls offset)) accStart
          itemSlot (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets resultSlot
    | .loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone
        releaseOffsets resultSlot =>
        .loopFoldMultiSlot resultWidth (initValues.map (shiftExprCalls offset)) accStart
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets resultSlot
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
    | .arrayFoldMultiSlotAssign sourceWidth resultWidth reverse array start stop initValues accStart
        itemStart bodyValues bodyLets bodyDone releaseOffsets targets =>
        .arrayFoldMultiSlotAssign sourceWidth resultWidth reverse (shiftExprCalls offset array)
          (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart itemStart
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets targets
    | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart
        byteSlot bodyValues bodyLets bodyDone releaseOffsets targets =>
        .byteArrayFoldMultiSlotAssign resultWidth (shiftExprCalls offset ptr)
          (shiftExprCalls offset len) (shiftExprCalls offset start) (shiftExprCalls offset stop)
          (initValues.map (shiftExprCalls offset)) accStart byteSlot
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets targets
    | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot
        bodyValues bodyLets bodyDone releaseOffsets targets =>
        .rangeFoldMultiSlotAssign resultWidth (shiftExprCalls offset start)
          (shiftExprCalls offset stop) (shiftExprCalls offset step)
          (initValues.map (shiftExprCalls offset)) accStart itemSlot
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets targets
    | .loopFoldMultiSlotAssign resultWidth initValues accStart bodyValues bodyLets bodyDone
        releaseOffsets targets =>
        .loopFoldMultiSlotAssign resultWidth (initValues.map (shiftExprCalls offset)) accStart
          (bodyValues.map (shiftExprCalls offset)) (bodyLets.map (shiftLocalLetCalls offset))
          (shiftExprCalls offset bodyDone) releaseOffsets targets
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

def emitU64Op : LeanExe.IR.U64Op → List Instr
  | .add => [Instr.addI64]
  | .natAdd => [Instr.addI64]
  | .sub => [Instr.subI64]
  | .natSub => [Instr.subI64]
  | .mul => [Instr.mulI64]
  | .natMul => [Instr.mulI64]
  | .divU => [Instr.divUI64]
  | .modU => [Instr.remUI64]
  | .bitAnd => [Instr.andI64]
  | .bitOr => [Instr.orI64]
  | .bitXor => [Instr.xorI64]
  | .shiftLeft => [Instr.shlI64]
  | .shiftRight => [Instr.shrUI64]

def coreGlobalSection : List UInt8 :=
  wasmSection 6 <| vec [
    ofNats [126, 1] ++ LeanExe.Wasm.Binary.i64Const 4096 ++ ofNats [11],
    ofNats [126, 1] ++ LeanExe.Wasm.Binary.i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ LeanExe.Wasm.Binary.i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ LeanExe.Wasm.Binary.i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ LeanExe.Wasm.Binary.i64Const 0 ++ ofNats [11],
    ofNats [126, 1] ++ LeanExe.Wasm.Binary.i64Const 0 ++ ofNats [11]
  ]

def coreMemorySection : List UInt8 :=
  wasmSection 5 <| vec [
    ofNats [0] ++ u32leb 16
  ]

def i32WrapI64 : List Instr :=
  [Instr.wrapI64]

def i64Load : List Instr :=
  [Instr.load64]

def i32Load : List Instr :=
  [Instr.load32]

def i64Eq : List Instr :=
  [Instr.eqI64]

def i64Store : List Instr :=
  [Instr.store64]

def i32Store : List Instr :=
  [Instr.store32]

def i32Load8U : List Instr :=
  [Instr.load8U]

def i32Store8 : List Instr :=
  [Instr.store8]

def i32Eq : List Instr :=
  [Instr.eqI32]

def i32ConstNegOne : List Instr :=
  [Instr.constI32NegOne]

def i64ExtendI32U : List Instr :=
  [Instr.extendUI32]

def i64LtU : List Instr :=
  [Instr.ltUI64]

def i64Ne : List Instr :=
  [Instr.neI64]

def i64LeU : List Instr :=
  [Instr.leUI64]

def i64GeU : List Instr :=
  [Instr.geUI64]

def i64And : List Instr :=
  [Instr.andI64]

def i64ShrU : List Instr :=
  [Instr.shrUI64]

def i64Eqz : List Instr :=
  [Instr.eqzI64]

def unreachable : List Instr :=
  [Instr.unreachable]

def returnOp : List Instr :=
  [Instr.ret]

def memorySize : List Instr :=
  [Instr.memorySize]

def memoryGrow : List Instr :=
  [Instr.memoryGrow]

def i64Align8 (value : List Instr) : List Instr :=
  value ++ i64Const 7 ++ [Instr.addI64] ++ i64Const 8 ++ [Instr.divUI64] ++
    i64Const 8 ++ [Instr.mulI64]

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

def incGlobal (index : Nat) : List Instr :=
  globalGet index ++ i64Const 1 ++ [Instr.addI64] ++ globalSet index

def rcHeaderAddress (ptr : List Instr) (offset : Nat) : List Instr :=
  ptr ++ i64Const offset ++ [Instr.subI64] ++ i32WrapI64

def rcHeaderLoad (ptr : List Instr) (offset : Nat) : List Instr :=
  rcHeaderAddress ptr offset ++ i64Load

def rcHeaderStore (ptr : List Instr) (offset : Nat) (value : List Instr) : List Instr :=
  rcHeaderAddress ptr offset ++ value ++ i64Store

def rcInitHeader
    (ptr capacity kind aux1 aux2 : List Instr) :
    List Instr :=
  rcHeaderStore ptr 48 (i64Const rcMagic) ++
    rcHeaderStore ptr 40 (i64Const 1) ++
    rcHeaderStore ptr 32 capacity ++
    rcHeaderStore ptr 24 kind ++
    rcHeaderStore ptr 16 aux1 ++
    rcHeaderStore ptr 8 aux2

def rcAllocPayload
    (scratch : Nat)
    (payloadBytes kind aux1 aux2 : List Instr) :
    List Instr :=
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
      ([Instr.iff false (localGet nextLocal ++ globalSet 1) (some (rcHeaderStore (localGet prevLocal) 8 (localGet nextLocal)))])
  let takeCurrent :=
    unlinkCurrent ++
      rcInitHeader (localGet currLocal) (localGet sizeLocal) kind aux1 aux2 ++
      localGet currLocal ++ localSet ptrLocal
  let searchLoop :=
    ([Instr.block [Instr.loop (localGet currLocal ++ i64Const 0 ++ i64Eq ++ [Instr.brIf 1] ++
      localGet ptrLocal ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
      rcHeaderLoad (localGet currLocal) 32 ++ localSet sizeLocal ++
      rcHeaderLoad (localGet currLocal) 8 ++ localSet nextLocal ++
      localGet sizeLocal ++ localGet alignedLocal ++ i64GeU ++
        ([Instr.iff false (takeCurrent) (some (localGet currLocal ++ localSet prevLocal ++
          localGet nextLocal ++ localSet currLocal))]) ++
      [Instr.br 0])]])
  let bumpAllocate :=
    globalGet 0 ++ i64Const rcHeaderBytes ++ [Instr.addI64] ++ localGet alignedLocal ++
      [Instr.addI64] ++ localTee endLocal ++
      globalGet 0 ++ i64LtU ++
      ([Instr.iff false (unreachable) none]) ++
      localGet endLocal ++ i64Const 1 ++ [Instr.subI64] ++ i64Const 65536 ++
        [Instr.divUI64] ++ i64Const 1 ++ [Instr.addI64] ++ localSet requiredPagesLocal ++
      memorySize ++ i64ExtendI32U ++ localGet requiredPagesLocal ++ i64LtU ++
      ([Instr.iff false (localGet requiredPagesLocal ++ memorySize ++ i64ExtendI32U ++ [Instr.subI64] ++
          i32WrapI64 ++ memoryGrow ++ i32ConstNegOne ++ i32Eq ++
          ([Instr.iff false (unreachable) none])) none]) ++
      globalGet 0 ++ i64Const rcHeaderBytes ++ [Instr.addI64] ++ localSet ptrLocal ++
      localGet endLocal ++ globalSet 0 ++
      rcInitHeader (localGet ptrLocal) (localGet alignedLocal) kind aux1 aux2
  i64Align8 payloadBytes ++ localSet alignedLocal ++
    localGet alignedLocal ++ i64Const 8 ++ i64LtU ++
      ([Instr.iff false (i64Const 8 ++ localSet alignedLocal) none]) ++
    i64Const 0 ++ localSet ptrLocal ++
    i64Const 0 ++ localSet prevLocal ++
    globalGet 1 ++ localSet currLocal ++
    searchLoop ++
    localGet ptrLocal ++ i64Const 0 ++ i64Eq ++
      ([Instr.iff false (bumpAllocate) none]) ++
    incGlobal (runtimeStatGlobal .allocs) ++
    localGet ptrLocal

def rcArrayPayloadBytes (width : Nat) (len : List Instr) : List Instr :=
  i64Const 8 ++ len ++ i64Const width ++ [Instr.mulI64] ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64]

def rcAllocArrayObject (scratch width childMask : Nat) (len : List Instr) : List Instr :=
  rcAllocPayload scratch
    (rcArrayPayloadBytes width len)
    (i64Const rcKindArray)
    (i64Const width)
    (i64Const childMask)

def rcAllocSlotObject (scratch slots childMask : Nat) : List Instr :=
  rcAllocPayload scratch
    (i64Const (slots * 8))
    (i64Const rcKindSlots)
    (i64Const slots)
    (i64Const childMask)

def rcAllocRawObject (scratch : Nat) (len : List Instr) : List Instr :=
  rcAllocPayload scratch (len) (i64Const rcKindRaw) (i64Const 0) (i64Const 0)

def arrayCellAddress (base index : List Instr) : List Instr :=
  base ++ index ++ i64Const 1 ++ [Instr.addI64] ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64] ++
    i32WrapI64

def arraySlotAddress (width slot : Nat) (base index : List Instr) : List Instr :=
  base ++ index ++ i64Const width ++ [Instr.mulI64] ++ i64Const (slot + 1) ++
    [Instr.addI64] ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64] ++ i32WrapI64

def enumerateAux {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | item :: rest, index => (index, item) :: enumerateAux rest (index + 1)

def enumerate {α : Type} (items : List α) : List (Nat × α) :=
  enumerateAux items 0

def maskBitSet (mask slot : Nat) : Bool :=
  (mask / (2 ^ slot)) % 2 == 1

def emitRetainLocal (ptrLocal rcLocal : Nat) : List Instr :=
  localGet ptrLocal ++ i64Const 0 ++ i64Ne ++
    ([Instr.iff false (rcHeaderLoad (localGet ptrLocal) 48 ++ i64Const rcMagic ++ i64Ne ++
        ([Instr.iff false (unreachable) none]) ++
      rcHeaderLoad (localGet ptrLocal) 40 ++ localSet rcLocal ++
      localGet rcLocal ++ i64Const 0 ++ i64Eq ++
        ([Instr.iff false (unreachable) none]) ++
      incGlobal (runtimeStatGlobal .retains) ++
      rcHeaderStore (localGet ptrLocal) 40 (localGet rcLocal ++ i64Const 1 ++ [Instr.addI64])) none])

def emitRetainArraySlotsAtIndex
    (width childMask skipMask childLocal rcLocal : Nat)
    (base index : List Instr) :
    List Instr :=
  (List.range width).flatMap fun slot =>
    if maskBitSet childMask slot && !maskBitSet skipMask slot then
      arraySlotAddress width slot base index ++ i64Load ++ localSet childLocal ++
        emitRetainLocal childLocal rcLocal
    else
      []

def emitRetainArrayRange
    (width childMask loopLocal childLocal rcLocal : Nat)
    (base start len : List Instr) :
    List Instr :=
  if childMask == 0 then
    []
  else
    let index := start ++ localGet loopLocal ++ [Instr.addI64]
    i64Const 0 ++ localSet loopLocal ++
      ([Instr.block [Instr.loop (localGet loopLocal ++ len ++ i64GeU ++ [Instr.brIf 1] ++
        emitRetainArraySlotsAtIndex width childMask 0 childLocal rcLocal base index ++
        localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
        [Instr.br 0])]])

def emitRetainArrayRangeWithSpecial
    (width childMask skipMask loopLocal childLocal rcLocal : Nat)
    (base start len specialIndex : List Instr) :
    List Instr :=
  if childMask == 0 then
    []
  else
    let index := start ++ localGet loopLocal ++ [Instr.addI64]
    i64Const 0 ++ localSet loopLocal ++
      ([Instr.block [Instr.loop (localGet loopLocal ++ len ++ i64GeU ++ [Instr.brIf 1] ++
        index ++ specialIndex ++ i64Eq ++
          ([Instr.iff false (emitRetainArraySlotsAtIndex width childMask skipMask childLocal rcLocal base index) (some (emitRetainArraySlotsAtIndex width childMask 0 childLocal rcLocal base index))]) ++
        localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
        [Instr.br 0])]])

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
    | .heapAllocSlots _ _ values =>
        3 + values.length +
          max 6 (values.foldl (fun n value => max n (exprScratch value)) 0)
    | .heapLoadSlot ptr _ => 1 + exprScratch ptr
    | .arrayLiteralSlots width _ elements =>
        3 + width +
          max 6
            (elements.foldl
              (fun n element =>
                element.snd.foldl (fun m value => max m (exprScratch value)) n)
              0)
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
    | .arrayFoldMultiSlot sourceWidth resultWidth _reverse array start stop initValues _ _ bodyValues
        bodyLets bodyDone _ _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
        let bodyScratch :=
          max letScratch <|
            max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        5 + sourceWidth + resultWidth + 2 +
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
        bodyLets bodyDone _ _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
        let bodyScratch :=
          max letScratch <|
            max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        5 + resultWidth + 2 +
          max
            (max (exprScratch ptr) (exprScratch len))
            (max (max (exprScratch start) (exprScratch stop))
              (max initScratch bodyScratch))
    | .rangeFoldMultiSlot resultWidth start stop step initValues _ _ bodyValues bodyLets bodyDone _ _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
        let bodyScratch :=
          max letScratch <|
            max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        4 +
          max
            (max (exprScratch start) (max (exprScratch stop) (exprScratch step)))
            (max (max initScratch bodyScratch) (max (bodyScratch + resultWidth + 1) 3))
    | .loopFoldMultiSlot resultWidth initValues _ bodyValues bodyLets bodyDone _ _ =>
        let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
        let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
        let bodyScratch :=
          max letScratch <|
            max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
        2 + resultWidth + max initScratch bodyScratch
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
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth _reverse array start stop initValues _ _ bodyValues
      bodyLets bodyDone _ _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
      let bodyScratch :=
        max letScratch <|
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      5 + sourceWidth + resultWidth + 2 +
        max
          (max (exprScratch array) (max (exprScratch start) (exprScratch stop)))
          (max initScratch bodyScratch)
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues _ _ bodyValues
      bodyLets bodyDone _ _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
      let bodyScratch :=
        max letScratch <|
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      5 + resultWidth + 2 +
        max
          (max (exprScratch ptr) (exprScratch len))
          (max (max (exprScratch start) (exprScratch stop))
            (max initScratch bodyScratch))
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues _ _ bodyValues bodyLets bodyDone _ _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
      let bodyScratch :=
        max letScratch <|
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      4 +
        max
          (max (exprScratch start) (max (exprScratch stop) (exprScratch step)))
          (max (max initScratch bodyScratch) (max (bodyScratch + resultWidth + 1) 3))
  | .loopFoldMultiSlotAssign resultWidth initValues _ bodyValues bodyLets bodyDone _ _ =>
      let initScratch := initValues.foldl (fun n value => max n (exprScratch value)) 0
      let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
      let bodyScratch :=
        max letScratch <|
          max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
      2 + resultWidth + max initScratch bodyScratch
  | .ite cond thenStmt elseStmt =>
      max (condScratch cond) (max (stmtScratch thenStmt) (stmtScratch elseStmt))
  | .seq first second => max (stmtScratch first) (stmtScratch second)
  | .while cond body => max (condScratch cond) (stmtScratch body)

def funcScratch (func : Func) : Nat :=
  max (stmtScratch func.body) (func.results.foldl (fun acc result => max acc (exprScratch result)) 0)

def emitCopyLoop (arrayLocal newLocal lenLocal loopLocal : Nat) : List Instr :=
  i64Const 0 ++ localSet loopLocal ++
    ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
      arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
      arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
      [Instr.br 0])]])

def emitCopyLoopAt
    (arrayLocal newLocal destOffsetLocal lenLocal loopLocal : Nat) : List Instr :=
  i64Const 0 ++ localSet loopLocal ++
    ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
      arrayCellAddress
        (localGet newLocal)
        (localGet destOffsetLocal ++ localGet loopLocal ++ [Instr.addI64]) ++
      arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
      [Instr.br 0])]])

def emitExtractCopyLoop
    (arrayLocal newLocal startLocal lenLocal loopLocal : Nat) : List Instr :=
  i64Const 0 ++ localSet loopLocal ++
    ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
      arrayCellAddress (localGet newLocal) (localGet loopLocal) ++
      arrayCellAddress
        (localGet arrayLocal)
        (localGet startLocal ++ localGet loopLocal ++ [Instr.addI64]) ++
      i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
      [Instr.br 0])]])

def emitRangeCopyLoop
    (arrayLocal newLocal : Nat)
    (sourceOffset destOffset : List Instr)
    (lenLocal loopLocal : Nat) : List Instr :=
  i64Const 0 ++ localSet loopLocal ++
    ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
      arrayCellAddress
        (localGet newLocal)
        (destOffset ++ localGet loopLocal ++ [Instr.addI64]) ++
      arrayCellAddress
        (localGet arrayLocal)
        (sourceOffset ++ localGet loopLocal ++ [Instr.addI64]) ++
      i64Load ++ i64Store ++
      localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
      [Instr.br 0])]])

def emitByteRangeCopyLoop
    (sourcePtrLocal destPtrLocal : Nat)
    (sourceOffset destOffset len : List Instr)
    (loopLocal : Nat) : List Instr :=
  i64Const 0 ++ localSet loopLocal ++
    ([Instr.block [Instr.loop (localGet loopLocal ++ len ++ i64GeU ++ [Instr.brIf 1] ++
      localGet destPtrLocal ++ destOffset ++ [Instr.addI64] ++
        localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
      localGet sourcePtrLocal ++ sourceOffset ++ [Instr.addI64] ++
        localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
      i32Load8U ++ i32Store8 ++
      localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
      [Instr.br 0])]])

mutual
  partial def emitArrayAllocSlots (scratch width childMask : Nat) (cells : Expr) : List Instr :=
    let len := scratch
    let ptr := scratch + 1
    let loopLocal := scratch + 2
    let cellCountLocal := scratch + 3
    let zeroLoop :=
      localGet len ++ i64Const width ++ [Instr.mulI64] ++ localSet cellCountLocal ++
        i64Const 0 ++ localSet loopLocal ++
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet cellCountLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          localGet ptr ++ i64Const 8 ++ [Instr.addI64] ++
            localGet loopLocal ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64] ++
            i32WrapI64 ++ i64Const 0 ++ i64Store ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
    emitExpr (scratch + 2) cells ++ localSet len ++
      rcAllocArrayObject (scratch + 2) width childMask (localGet len) ++ localSet ptr ++
      localGet ptr ++ i32WrapI64 ++ localGet len ++ i64Store ++
      zeroLoop ++
      localGet ptr

  partial def emitHeapAllocSlots
      (scratch childMask ownedMask : Nat)
      (values : List Expr) :
      List Instr :=
    let ptrLocal := scratch
    let valueStart := scratch + 1
    let retainChildLocal := scratch + 1 + values.length
    let retainRcLocal := retainChildLocal + 1
    let childScratch := retainRcLocal + 1
    let rec emitValueStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, _) :: rest =>
          localGet ptrLocal ++ i64Const (offset * 8) ++ [Instr.addI64] ++ i32WrapI64 ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    let retainBorrowedChildren :=
      (enumerate values).flatMap fun item =>
        let offset := item.fst
        if maskBitSet childMask offset && !maskBitSet ownedMask offset then
          localGet (valueStart + offset) ++ localSet retainChildLocal ++
            emitRetainLocal retainChildLocal retainRcLocal
        else
          []
    emitValueStores (enumerate values) ++
      rcAllocSlotObject childScratch values.length childMask ++ localSet ptrLocal ++
      emitSlotStores (enumerate values) ++
      retainBorrowedChildren ++
      localGet ptrLocal

  partial def emitHeapLoadSlot (scratch : Nat) (ptr : Expr) (slot : Nat) : List Instr :=
    let ptrLocal := scratch
    emitExpr (scratch + 1) ptr ++ localSet ptrLocal ++
      localGet ptrLocal ++ i64Const (slot * 8) ++ [Instr.addI64] ++ i32WrapI64 ++ i64Load

  partial def emitReleaseAccumulatorSlot
      (releaseIndex accStart offset : Nat)
      (priorOffsets : List Nat) :
      List Instr :=
    let slot := accStart + offset
    let distinct :=
      priorOffsets.foldl
        (fun cond prior =>
          cond ++ localGet slot ++ localGet (accStart + prior) ++ i64Ne ++ [Instr.andI32])
        (localGet slot ++ i64Const 0 ++ i64Ne)
    distinct ++
      ([Instr.iff false (localGet slot ++ call releaseIndex) none])

  partial def emitAccumulatorReleases
      (releaseIndex accStart : Nat)
      (releaseOffsets : List Nat) :
      List Instr :=
    let rec loop : List Nat → List Nat → List Instr
      | _, [] => []
      | prior, offset :: rest =>
          emitReleaseAccumulatorSlot releaseIndex accStart offset prior ++
            loop (offset :: prior) rest
    loop [] releaseOffsets

  partial def emitGuardedAccumulatorReleases
      (releaseIndex releaseReadyLocal accStart : Nat)
      (releaseOffsets : List Nat) :
      List Instr :=
    match releaseOffsets with
    | [] => []
    | _ =>
        localGet releaseReadyLocal ++ i64Const 0 ++ i64Ne ++
          ([Instr.iff false (emitAccumulatorReleases releaseIndex accStart releaseOffsets) none])

  partial def emitArrayLiteralSlots
      (scratch width childMask : Nat)
      (elements : List (Nat × List Expr)) : List Instr :=
    let ptrLocal := scratch
    let retainChildLocal := scratch + 1
    let retainRcLocal := scratch + 2
    let valueStart := scratch + 3
    let childScratch := valueStart + width
    let rec emitValueStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores (index : Nat) : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress width offset (localGet ptrLocal) (i64Const index) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores index rest
    let rec emitElements : List (Nat × (Nat × List Expr)) → List Instr
      | [] => []
      | (index, (ownedMask, slots)) :: rest =>
          emitValueStores (enumerate slots) ++
            emitSlotStores index (List.range slots.length) ++
            emitRetainArraySlotsAtIndex width childMask ownedMask retainChildLocal retainRcLocal
              (localGet ptrLocal) (i64Const index) ++
            emitElements rest
    rcAllocArrayObject childScratch width childMask (i64Const elements.length) ++
      localSet ptrLocal ++
      localGet ptrLocal ++ i32WrapI64 ++ i64Const elements.length ++ i64Store ++
      emitElements (enumerate elements) ++
      localGet ptrLocal

  partial def emitArrayReplicateSlots
      (scratch width childMask ownedMask : Nat)
      (cells : Expr)
      (values : List Expr) : List Instr :=
    let lenLocal := scratch
    let ptrLocal := scratch + 1
    let loopLocal := scratch + 2
    let valueStart := scratch + 3
    let retainChildLocal := scratch + 3 + values.length
    let retainRcLocal := retainChildLocal + 1
    let childScratch := retainRcLocal + 1
    let rec emitValueStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet ptrLocal) (localGet loopLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    let fillLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
          emitSlotStores (enumerate values) ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
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
      (array index : Expr) : List Instr :=
    let arrayLocal := scratch
    let indexLocal := scratch + 1
    let childScratch := scratch + 2
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet indexLocal ++ localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ i64LtU ++
      ([Instr.iff true (arraySlotAddress width slot (localGet arrayLocal) (localGet indexLocal) ++ i64Load) (some ([Instr.unreachable]))])

  partial def emitArraySize (scratch : Nat) (array : Expr) : List Instr :=
    let arrayLocal := scratch
    emitExpr (scratch + 1) array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load

  partial def emitArraySetSlots
      (scratch width childMask ownedMask : Nat)
      (array index : Expr)
      (values : List Expr) : List Instr :=
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
    let rec emitValueStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet indexLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      emitValueStores (enumerate values) ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ([Instr.iff true (localGet lenLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet cellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet lenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        emitSlotStores (enumerate values) ++
        emitRetainArrayRangeWithSpecial width childMask ownedMask loopLocal retainChildLocal
          retainRcLocal (localGet newLocal) (i64Const 0) (localGet lenLocal) (localGet indexLocal) ++
        localGet newLocal) (some ([Instr.unreachable]))])

  partial def emitArrayPushSlots
      (scratch width childMask ownedMask : Nat)
      (array : Expr)
      (values : List Expr) : List Instr :=
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
    let rec emitValueStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet lenLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitValueStores (enumerate values) ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet cellsLocal ++
      localGet lenLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet newLenLocal ++
      rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
      emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
      emitSlotStores (enumerate values) ++
      emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
        (localGet newLocal) (i64Const 0) (localGet lenLocal) ++
      emitRetainArraySlotsAtIndex width childMask ownedMask retainChildLocal retainRcLocal
        (localGet newLocal) (localGet lenLocal) ++
      localGet newLocal

  partial def emitArrayPopSlots (scratch width childMask : Nat) (array : Expr) : List Instr :=
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
      localGet lenLocal ++ i64Const 0 ++ [Instr.eqI64] ++
      ([Instr.iff true (localGet arrayLocal) (some (localGet lenLocal ++ i64Const 1 ++ [Instr.subI64] ++ localSet newLenLocal ++
        localGet newLenLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet cellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal cellsLocal loopLocal ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet newLenLocal) ++
        localGet newLocal))])

  partial def emitArrayAppendSlots
      (scratch width childMask : Nat)
      (left right : Expr) : List Instr :=
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
      localGet leftLenLocal ++ localGet rightLenLocal ++ [Instr.addI64] ++
        localSet newLenLocal ++
      localGet leftLenLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet leftCellsLocal ++
      localGet rightLenLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet rightCellsLocal ++
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
      (array start stop : Expr) : List Instr :=
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
      ([Instr.iff true (localGet stopLocal) (some (localGet sourceLenLocal))]) ++ localSet stopBoundLocal ++
      localGet startLocal ++ localGet stopBoundLocal ++ i64LtU ++
      ([Instr.iff true (localGet stopBoundLocal ++ localGet startLocal ++ [Instr.subI64]) (some (i64Const 0))]) ++ localSet newLenLocal ++
      localGet startLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet startCellLocal ++
      localGet newLenLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet cellsLocal ++
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
      (bodyValues : List Expr) : List Instr :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let retainChildLocal := scratch + 4
    let retainRcLocal := scratch + 5
    let childScratch := scratch + 6
    let rec emitSourceLoads : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet loopLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitResultStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          arraySlotAddress resultWidth offset (localGet newLocal) (localGet loopLocal) ++
            emitExpr childScratch value ++ i64Store ++ emitResultStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      rcAllocArrayObject childScratch resultWidth childMask (localGet lenLocal) ++ localSet newLocal ++
      localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
      i64Const 0 ++ localSet loopLocal ++
      ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
        emitSourceLoads (List.range sourceWidth) ++
        emitResultStores (enumerate bodyValues) ++
        emitRetainArraySlotsAtIndex resultWidth childMask ownedMask retainChildLocal retainRcLocal
          (localGet newLocal) (localGet loopLocal) ++
        localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
        [Instr.br 0])]]) ++
      localGet newLocal

  partial def emitArrayFoldMultiSlot
      (releaseIndex scratch sourceWidth resultWidth : Nat)
      (reverse : Bool)
      (array start stop : Expr)
      (initValues : List Expr)
      (accStart itemStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (resultSlot : Nat) : List Instr :=
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
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitSourceLoads : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let emitLoop :=
      if reverse then
        localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
        ([Instr.iff true (localGet indexLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
        localGet effectiveStopLocal ++ localSet indexLocal ++
        ([Instr.block [Instr.loop (localGet indexLocal ++ localGet stopLocal ++ i64LeU ++
            [Instr.brIf 1] ++
          localGet indexLocal ++ i64Const 1 ++ [Instr.subI64] ++ localSet indexLocal ++
          emitSourceLoads (List.range sourceWidth) ++
          bodyLets.flatMap (emitLocalLet childScratch) ++
          emitBodyStages (enumerate bodyValues) ++
          emitExpr childScratch bodyDone ++ localSet doneSlot ++
          emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
          emitTempCopies (List.range resultWidth) ++
          i64Const 1 ++ localSet releaseReadyLocal ++
          localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
          [Instr.br 0])]])
      else
        localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
        ([Instr.iff true (localGet stopLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
        ([Instr.block [Instr.loop (localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          emitSourceLoads (List.range sourceWidth) ++
          bodyLets.flatMap (emitLocalLet childScratch) ++
          emitBodyStages (enumerate bodyValues) ++
          emitExpr childScratch bodyDone ++ localSet doneSlot ++
          emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
          emitTempCopies (List.range resultWidth) ++
          i64Const 1 ++ localSet releaseReadyLocal ++
          localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
          localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
          [Instr.br 0])]])
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      emitLoop ++
      localGet (accStart + resultSlot)

  partial def emitArrayFoldMultiSlotAssign
      (releaseIndex scratch sourceWidth resultWidth : Nat)
      (reverse : Bool)
      (array start stop : Expr)
      (initValues : List Expr)
      (accStart itemStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (targets : List Nat) : List Instr :=
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
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitSourceLoads : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let rec emitTargetCopies : List (Nat × Nat) → List Instr
      | [] => []
      | (offset, target) :: rest =>
          localGet (accStart + offset) ++ localSet target ++ emitTargetCopies rest
    let emitLoop :=
      if reverse then
        localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
        ([Instr.iff true (localGet indexLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
        localGet effectiveStopLocal ++ localSet indexLocal ++
        ([Instr.block [Instr.loop (localGet indexLocal ++ localGet stopLocal ++ i64LeU ++
            [Instr.brIf 1] ++
          localGet indexLocal ++ i64Const 1 ++ [Instr.subI64] ++ localSet indexLocal ++
          emitSourceLoads (List.range sourceWidth) ++
          bodyLets.flatMap (emitLocalLet childScratch) ++
          emitBodyStages (enumerate bodyValues) ++
          emitExpr childScratch bodyDone ++ localSet doneSlot ++
          emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
          emitTempCopies (List.range resultWidth) ++
          i64Const 1 ++ localSet releaseReadyLocal ++
          localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
          [Instr.br 0])]])
      else
        localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
        ([Instr.iff true (localGet stopLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
        ([Instr.block [Instr.loop (localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          emitSourceLoads (List.range sourceWidth) ++
          bodyLets.flatMap (emitLocalLet childScratch) ++
          emitBodyStages (enumerate bodyValues) ++
          emitExpr childScratch bodyDone ++ localSet doneSlot ++
          emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
          emitTempCopies (List.range resultWidth) ++
          i64Const 1 ++ localSet releaseReadyLocal ++
          localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
          localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
          [Instr.br 0])]])
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      emitLoop ++
      emitTargetCopies (enumerate targets)

  partial def emitArrayFindIdxSlots
      (scratch sourceWidth : Nat)
      (array : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (returnPayload : Bool) : List Instr :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let foundValue := if returnPayload then localGet indexLocal else i64Const 1
    let rec emitSourceLoads : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      i64Const 0 ++ localSet indexLocal ++
      i64Const 0 ++ localSet resultLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        emitSourceLoads (List.range sourceWidth) ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ([Instr.iff false (foundValue ++ localSet resultLocal ++
          [Instr.br 2]) none]) ++
        localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
        [Instr.br 0])]]) ++
      localGet resultLocal

  partial def emitArrayFindSlot
      (scratch sourceWidth : Nat)
      (array : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (slot : Nat) : List Instr :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let resultLocal := scratch + 3
    let childScratch := scratch + 4
    let rec emitSourceLoads : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      i64Const 0 ++ localSet indexLocal ++
      i64Const 0 ++ localSet resultLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        emitSourceLoads (List.range sourceWidth) ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ([Instr.iff false (localGet (itemStart + slot) ++ localSet resultLocal ++
          [Instr.br 2]) none]) ++
        localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
        [Instr.br 0])]]) ++
      localGet resultLocal

  partial def emitArrayEqSlots
      (scratch width : Nat)
      (left right : Expr)
      (leftStart rightStart : Nat)
      (predicate : Expr) : List Instr :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let lenLocal := scratch + 2
    let indexLocal := scratch + 3
    let resultLocal := scratch + 4
    let childScratch := scratch + 5
    let rec emitElementLoads : List Nat → List Instr
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
      ([Instr.iff true (i64Const 0) (some (i64Const 0 ++ localSet indexLocal ++
        i64Const 1 ++ localSet resultLocal ++
        ([Instr.block [Instr.loop (localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          emitElementLoads (List.range width) ++
          emitExpr childScratch predicate ++ i64Const 0 ++ i64Eq ++
          ([Instr.iff false (i64Const 0 ++ localSet resultLocal ++
            [Instr.br 2]) none]) ++
          localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
          [Instr.br 0])]]) ++
        localGet resultLocal))])

  partial def emitArrayAnySlots
      (scratch sourceWidth : Nat)
      (array start stop : Expr)
      (itemStart : Nat)
      (predicate : Expr)
      (forAll : Bool) : List Instr :=
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
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++ [Instr.eqzI32]
      else
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne
    let rec emitSourceLoads : List Nat → List Instr
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
      ([Instr.iff true (localGet stopLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        emitSourceLoads (List.range sourceWidth) ++
        predicateCondition ++
        ([Instr.iff false (foundResult ++ localSet resultLocal ++
          [Instr.br 2]) none]) ++
        localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
        [Instr.br 0])]]) ++
      localGet resultLocal

  partial def emitArrayFilterSlots
      (scratch sourceWidth childMask : Nat)
      (array start stop : Expr)
      (itemStart : Nat)
      (predicate : Expr) : List Instr :=
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
    let rec emitSourceLoads : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet arrayLocal) (localGet indexLocal) ++
            i64Load ++ localSet (itemStart + offset) ++ emitSourceLoads rest
    let rec emitResultStores : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress sourceWidth offset (localGet newLocal) (localGet writeIndexLocal) ++
            localGet (itemStart + offset) ++ i64Store ++ emitResultStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      localGet lenLocal ++ i64Const sourceWidth ++ [Instr.mulI64] ++ localSet cellsLocal ++
      rcAllocArrayObject childScratch sourceWidth childMask (localGet lenLocal) ++ localSet newLocal ++
      i64Const 0 ++ localSet writeIndexLocal ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ([Instr.iff true (localGet stopLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        emitSourceLoads (List.range sourceWidth) ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ([Instr.iff false (emitResultStores (List.range sourceWidth) ++
          emitRetainArraySlotsAtIndex sourceWidth childMask 0 retainChildLocal retainRcLocal
            (localGet newLocal) (localGet writeIndexLocal) ++
          localGet writeIndexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet writeIndexLocal) none]) ++
        localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
        [Instr.br 0])]]) ++
      localGet newLocal ++ i32WrapI64 ++ localGet writeIndexLocal ++ i64Store ++
      localGet newLocal

  partial def emitArrayInsertIfInBoundsSlots
      (scratch width childMask ownedMask : Nat)
      (array index : Expr)
      (values : List Expr) : List Instr :=
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
    let rec emitValueStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (valueStart + offset) ++ emitValueStores rest
    let rec emitSlotStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, _) :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet indexLocal) ++
            localGet (valueStart + offset) ++ i64Store ++ emitSlotStores rest
    emitExpr childScratch array ++ localSet arrayLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LeU ++
      ([Instr.iff true (emitValueStores (enumerate values) ++
        localGet lenLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet newLenLocal ++
        localGet indexLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet prefixCellsLocal ++
        localGet lenLocal ++ localGet indexLocal ++ [Instr.subI64] ++
          i64Const width ++ [Instr.mulI64] ++ localSet suffixCellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal prefixCellsLocal loopLocal ++
        emitSlotStores (enumerate values) ++
        emitRangeCopyLoop
          arrayLocal
          newLocal
          (localGet prefixCellsLocal)
          (localGet prefixCellsLocal ++ i64Const width ++ [Instr.addI64])
          suffixCellsLocal
          loopLocal ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet indexLocal) ++
        emitRetainArraySlotsAtIndex width childMask ownedMask retainChildLocal retainRcLocal
          (localGet newLocal) (localGet indexLocal) ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (localGet indexLocal ++ i64Const 1 ++ [Instr.addI64])
          (localGet lenLocal ++ localGet indexLocal ++ [Instr.subI64]) ++
        localGet newLocal) (some (localGet arrayLocal))])

  partial def emitArrayEraseIfInBoundsSlots
      (scratch width childMask : Nat)
      (array index : Expr) : List Instr :=
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
      ([Instr.iff true (localGet lenLocal ++ i64Const 1 ++ [Instr.subI64] ++ localSet newLenLocal ++
        localGet indexLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet prefixCellsLocal ++
        localGet newLenLocal ++ localGet indexLocal ++ [Instr.subI64] ++
          i64Const width ++ [Instr.mulI64] ++ localSet suffixCellsLocal ++
        rcAllocArrayObject childScratch width childMask (localGet newLenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet newLenLocal ++ i64Store ++
        emitCopyLoop arrayLocal newLocal prefixCellsLocal loopLocal ++
        emitRangeCopyLoop
          arrayLocal
          newLocal
          (localGet prefixCellsLocal ++ i64Const width ++ [Instr.addI64])
          (localGet prefixCellsLocal)
          suffixCellsLocal
          loopLocal ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet indexLocal) ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (localGet indexLocal)
          (localGet newLenLocal ++ localGet indexLocal ++ [Instr.subI64]) ++
        localGet newLocal) (some (localGet arrayLocal))])

  partial def emitArraySwapIfInBoundsSlots
      (scratch width childMask : Nat)
      (array left right : Expr) : List Instr :=
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
    let rec emitSlotCopies : List Nat → List Instr
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
      localGet lenLocal ++ i64Const width ++ [Instr.mulI64] ++ localSet cellsLocal ++
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
      ([Instr.iff true (localGet rightLocal ++ localGet lenLocal ++ i64LtU ++
        ([Instr.iff true (swapBody) (some (localGet arrayLocal))])) (some (localGet arrayLocal))])

  partial def emitArrayReverseSlots
      (scratch width childMask : Nat)
      (array : Expr) : List Instr :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newLocal := scratch + 2
    let loopLocal := scratch + 3
    let retainChildLocal := scratch + 4
    let retainRcLocal := scratch + 5
    let childScratch := scratch + 6
    let sourceIndex :=
      localGet lenLocal ++ localGet loopLocal ++ [Instr.subI64] ++ i64Const 1 ++ [Instr.subI64]
    let rec emitSlotCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          arraySlotAddress width offset (localGet newLocal) (localGet loopLocal) ++
            arraySlotAddress width offset (localGet arrayLocal) sourceIndex ++
            i64Load ++ i64Store ++ emitSlotCopies rest
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
          emitSlotCopies (List.range width) ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      localGet lenLocal ++ i64Const 1 ++ i64LeU ++
      ([Instr.iff true (localGet arrayLocal) (some (rcAllocArrayObject childScratch width childMask (localGet lenLocal) ++ localSet newLocal ++
        localGet newLocal ++ i32WrapI64 ++ localGet lenLocal ++ i64Store ++
        copyLoop ++
        emitRetainArrayRange width childMask loopLocal retainChildLocal retainRcLocal
          (localGet newLocal) (i64Const 0) (localGet lenLocal) ++
        localGet newLocal))])

  partial def emitByteArrayGet (scratch : Nat) (ptr len index : Expr) : List Instr :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let childScratch := scratch + 3
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ([Instr.iff true (localGet ptrLocal ++ localGet indexLocal ++ [Instr.addI64] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U) (some ([Instr.unreachable]))])

  partial def emitByteArrayPushPtr (scratch : Nat) (ptr len value : Expr) : List Instr :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let valueLocal := scratch + 2
    let newPtrLocal := scratch + 3
    let newLenLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
          localGet newPtrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            localGet ptrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch value ++ localSet valueLocal ++
      localGet lenLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet newLenLocal ++
      rcAllocRawObject childScratch (localGet newLenLocal) ++ localSet newPtrLocal ++
      copyLoop ++
      localGet newPtrLocal ++ localGet lenLocal ++ [Instr.addI64] ++ i32WrapI64 ++
        localGet valueLocal ++ i32WrapI64 ++ i32Store8 ++
      localGet newPtrLocal

  partial def emitByteArrayAppendPtr
      (scratch : Nat)
      (leftPtr leftLen rightPtr rightLen : Expr) : List Instr :=
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
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet leftLenLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          localGet newPtrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            localGet leftPtrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
    let copyRightLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet rightLenLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          localGet newPtrLocal ++ localGet leftLenLocal ++ [Instr.addI64] ++
            localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            localGet rightPtrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
    emitExpr childScratch leftPtr ++ localSet leftPtrLocal ++
      emitExpr childScratch leftLen ++ localSet leftLenLocal ++
      emitExpr childScratch rightPtr ++ localSet rightPtrLocal ++
      emitExpr childScratch rightLen ++ localSet rightLenLocal ++
      localGet leftLenLocal ++ localGet rightLenLocal ++ [Instr.addI64] ++ localSet newLenLocal ++
      rcAllocRawObject childScratch (localGet newLenLocal) ++ localSet newPtrLocal ++
      copyLeftLoop ++
      copyRightLoop ++
      localGet newPtrLocal

  partial def emitByteArraySetPtr
      (scratch : Nat)
      (ptr len index value : Expr) : List Instr :=
    let ptrLocal := scratch
    let lenLocal := scratch + 1
    let indexLocal := scratch + 2
    let valueLocal := scratch + 3
    let newPtrLocal := scratch + 4
    let loopLocal := scratch + 5
    let childScratch := scratch + 6
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
          localGet newPtrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            localGet ptrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            i32Load8U ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch index ++ localSet indexLocal ++
      emitExpr childScratch value ++ localSet valueLocal ++
      localGet indexLocal ++ localGet lenLocal ++ i64LtU ++
      ([Instr.iff true (rcAllocRawObject childScratch (localGet lenLocal) ++ localSet newPtrLocal ++
        copyLoop ++
        localGet newPtrLocal ++ localGet indexLocal ++ [Instr.addI64] ++ i32WrapI64 ++
          localGet valueLocal ++ i32WrapI64 ++ i32Store8 ++
        localGet newPtrLocal) (some ([Instr.unreachable]))])

  partial def emitByteArrayFromArrayPtr (scratch : Nat) (array : Expr) : List Instr :=
    let arrayLocal := scratch
    let lenLocal := scratch + 1
    let newPtrLocal := scratch + 2
    let loopLocal := scratch + 3
    let childScratch := scratch + 4
    let copyLoop :=
      i64Const 0 ++ localSet loopLocal ++
        ([Instr.block [Instr.loop (localGet loopLocal ++ localGet lenLocal ++ i64GeU ++ [Instr.brIf 1] ++
          localGet newPtrLocal ++ localGet loopLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            arrayCellAddress (localGet arrayLocal) (localGet loopLocal) ++ i64Load ++
            i32WrapI64 ++ i32Store8 ++
          localGet loopLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet loopLocal ++
          [Instr.br 0])]])
    emitExpr childScratch array ++ localSet arrayLocal ++
      localGet arrayLocal ++ i32WrapI64 ++ i64Load ++ localSet lenLocal ++
      rcAllocRawObject childScratch (localGet lenLocal) ++ localSet newPtrLocal ++
      copyLoop ++
      localGet newPtrLocal

  partial def emitByteArrayCopySlicePtr
      (scratch : Nat)
      (srcPtr srcLen srcOff destPtr destLen destOff copyLen : Expr) : List Instr :=
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
      ([Instr.iff true (localGet srcLenLocal ++ localGet srcOffLocal ++ [Instr.subI64]) (some (i64Const 0))]) ++ localSet availableLocal ++
      localGet requestedLenLocal ++ localGet availableLocal ++ i64LtU ++
      ([Instr.iff true (localGet requestedLenLocal) (some (localGet availableLocal))]) ++ localSet copiedLenLocal ++
      localGet destOffLocal ++ localGet destLenLocal ++ i64LtU ++
      ([Instr.iff true (localGet destOffLocal) (some (localGet destLenLocal))]) ++ localSet prefixLenLocal ++
      localGet destOffLocal ++ localGet copiedLenLocal ++ [Instr.addI64] ++ localSet suffixStartLocal ++
      localGet suffixStartLocal ++ localGet destLenLocal ++ i64LtU ++
      ([Instr.iff true (localGet destLenLocal ++ localGet suffixStartLocal ++ [Instr.subI64]) (some (i64Const 0))]) ++ localSet suffixLenLocal ++
      localGet prefixLenLocal ++ localGet copiedLenLocal ++ [Instr.addI64] ++
        localGet suffixLenLocal ++ [Instr.addI64] ++ localSet newLenLocal ++
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
        (localGet prefixLenLocal ++ localGet copiedLenLocal ++ [Instr.addI64])
        (localGet suffixLenLocal)
        loopLocal ++
      localGet newPtrLocal

  partial def emitByteArrayEq
      (scratch : Nat)
      (leftPtr leftLen rightPtr rightLen : Expr) : List Instr :=
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
      ([Instr.iff true (i64Const 0) (some (i64Const 0 ++ localSet indexLocal ++
        i64Const 1 ++ localSet resultLocal ++
        ([Instr.block [Instr.loop (localGet indexLocal ++ localGet leftLenLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          localGet leftPtrLocal ++ localGet indexLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            i32Load8U ++ i64ExtendI32U ++
          localGet rightPtrLocal ++ localGet indexLocal ++ [Instr.addI64] ++ i32WrapI64 ++
            i32Load8U ++ i64ExtendI32U ++
          i64Ne ++
          ([Instr.iff false (i64Const 0 ++ localSet resultLocal ++
            [Instr.br 2]) none]) ++
          localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
          [Instr.br 0])]]) ++
        localGet resultLocal))])

  partial def emitByteArrayFindIdx
      (scratch : Nat)
      (ptr len start : Expr)
      (byteSlot : Nat)
      (predicate : Expr)
      (returnPayload : Bool) : List Instr :=
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
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet lenLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        localGet ptrLocal ++ localGet indexLocal ++ [Instr.addI64] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U ++ localSet byteSlot ++
        emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        ([Instr.iff false (foundValue ++ localSet resultLocal ++
          [Instr.br 2]) none]) ++
        localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
        [Instr.br 0])]]) ++
      localGet resultLocal

  partial def emitByteArrayFoldMultiSlot
      (releaseIndex scratch resultWidth : Nat)
      (ptr len start stop : Expr)
      (initValues : List Expr)
      (accStart byteSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (resultSlot : Nat) : List Instr :=
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
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ([Instr.iff true (localGet stopLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        localGet ptrLocal ++ localGet indexLocal ++ [Instr.addI64] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U ++ localSet byteSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
        emitTempCopies (List.range resultWidth) ++
        i64Const 1 ++ localSet releaseReadyLocal ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
        localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
        [Instr.br 0])]]) ++
      localGet (accStart + resultSlot)

  partial def emitByteArrayFoldMultiSlotAssign
      (releaseIndex scratch resultWidth : Nat)
      (ptr len start stop : Expr)
      (initValues : List Expr)
      (accStart byteSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (targets : List Nat) : List Instr :=
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
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let rec emitTargetCopies : List (Nat × Nat) → List Instr
      | [] => []
      | (offset, target) :: rest =>
          localGet (accStart + offset) ++ localSet target ++ emitTargetCopies rest
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      emitExpr childScratch len ++ localSet lenLocal ++
      emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      localGet stopLocal ++ localGet lenLocal ++ i64LtU ++
      ([Instr.iff true (localGet stopLocal) (some (localGet lenLocal))]) ++ localSet effectiveStopLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet effectiveStopLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        localGet ptrLocal ++ localGet indexLocal ++ [Instr.addI64] ++ i32WrapI64 ++
          i32Load8U ++ i64ExtendI32U ++ localSet byteSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
        emitTempCopies (List.range resultWidth) ++
        i64Const 1 ++ localSet releaseReadyLocal ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
        localGet indexLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet indexLocal ++
        [Instr.br 0])]]) ++
      emitTargetCopies (enumerate targets)

  partial def emitCheckedDivMod
      (scratch : Nat)
      (op : LeanExe.IR.U64Op)
      (left right : Expr) : List Instr :=
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
      localGet rightLocal ++ i64Const 0 ++ [Instr.eqI64] ++
      ([Instr.iff true (zeroValue) (some (localGet leftLocal ++ localGet rightLocal ++ emitU64Op op))])

  partial def emitNatAdd
      (scratch : Nat)
      (left right : Expr) : List Instr :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let resultLocal := scratch + 2
    let childScratch := scratch + 3
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ localGet rightLocal ++ [Instr.addI64] ++ localTee resultLocal ++
      localGet leftLocal ++ i64LtU ++
      ([Instr.iff true ([Instr.unreachable]) (some (localGet resultLocal))])

  partial def emitNatMul
      (scratch : Nat)
      (left right : Expr) : List Instr :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet rightLocal ++ i64Const 0 ++ [Instr.eqI64] ++
      ([Instr.iff true (i64Const 0) (some (i64Const (2 ^ 64 - 1) ++ localGet rightLocal ++ [Instr.divUI64] ++
          localGet leftLocal ++ i64LtU ++
        ([Instr.iff true ([Instr.unreachable]) (some (localGet leftLocal ++ localGet rightLocal ++ [Instr.mulI64]))])))])

  partial def emitNatSub
      (scratch : Nat)
      (left right : Expr) : List Instr :=
    let leftLocal := scratch
    let rightLocal := scratch + 1
    let childScratch := scratch + 2
    emitExpr childScratch left ++ localSet leftLocal ++
      emitExpr childScratch right ++ localSet rightLocal ++
      localGet leftLocal ++ localGet rightLocal ++ i64LtU ++
      ([Instr.iff true (i64Const 0) (some (localGet leftLocal ++ localGet rightLocal ++ [Instr.subI64]))])

  partial def emitRangeFoldMultiSlot
      (releaseIndex scratch resultWidth : Nat)
      (start stop step : Expr)
      (initValues : List Expr)
      (accStart itemSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (resultSlot : Nat) : List Instr :=
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
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitExpr childScratch step ++ localSet stepLocal ++
      emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet stopLocal ++ i64GeU ++ [Instr.brIf 1] ++
        localGet indexLocal ++ localSet itemSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
        emitTempCopies (List.range resultWidth) ++
        i64Const 1 ++ localSet releaseReadyLocal ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
        emitExpr childScratch (.u64Bin .natAdd (.local indexLocal) (.local stepLocal)) ++
          localSet indexLocal ++
        [Instr.br 0])]]) ++
      localGet (accStart + resultSlot)

  partial def emitRangeFoldMultiSlotAssign
      (releaseIndex scratch resultWidth : Nat)
      (start stop step : Expr)
      (initValues : List Expr)
      (accStart itemSlot : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (targets : List Nat) : List Instr :=
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
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let rec emitTargetCopies : List (Nat × Nat) → List Instr
      | [] => []
      | (offset, target) :: rest =>
          localGet (accStart + offset) ++ localSet target ++ emitTargetCopies rest
    emitExpr childScratch start ++ localSet indexLocal ++
      emitExpr childScratch stop ++ localSet stopLocal ++
      emitExpr childScratch step ++ localSet stepLocal ++
      emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      ([Instr.block [Instr.loop (localGet indexLocal ++ localGet stopLocal ++ i64GeU ++ [Instr.brIf 1] ++
        localGet indexLocal ++ localSet itemSlot ++
        bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
        emitTempCopies (List.range resultWidth) ++
        i64Const 1 ++ localSet releaseReadyLocal ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
        emitExpr childScratch (.u64Bin .natAdd (.local indexLocal) (.local stepLocal)) ++
          localSet indexLocal ++
        [Instr.br 0])]]) ++
      emitTargetCopies (enumerate targets)

  partial def emitLoopFoldMultiSlot
      (releaseIndex scratch resultWidth : Nat)
      (initValues : List Expr)
      (accStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (resultSlot : Nat) : List Instr :=
    let childScratch := scratch
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      ([Instr.block [Instr.loop (bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
        emitTempCopies (List.range resultWidth) ++
        i64Const 1 ++ localSet releaseReadyLocal ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
        [Instr.br 0])]]) ++
      localGet (accStart + resultSlot)

  partial def emitLoopFoldMultiSlotAssign
      (releaseIndex scratch resultWidth : Nat)
      (initValues : List Expr)
      (accStart : Nat)
      (bodyValues : List Expr)
      (bodyLets : List LocalLet)
      (bodyDone : Expr)
      (releaseOffsets : List Nat)
      (targets : List Nat) : List Instr :=
    let childScratch := scratch
    let letScratch := bodyLets.foldl (fun n item => max n (localLetScratch item)) 0
    let bodyScratch :=
      max letScratch <|
        max (exprScratch bodyDone) (bodyValues.foldl (fun n value => max n (exprScratch value)) 0)
    let doneSlot := childScratch + bodyScratch
    let tempStart := doneSlot + 1
    let releaseReadyLocal := tempStart + resultWidth
    let rec emitInitStores : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (accStart + offset) ++ emitInitStores rest
    let rec emitBodyStages : List (Nat × Expr) → List Instr
      | [] => []
      | (offset, value) :: rest =>
          emitExpr childScratch value ++ localSet (tempStart + offset) ++ emitBodyStages rest
    let rec emitTempCopies : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet (tempStart + offset) ++ localSet (accStart + offset) ++ emitTempCopies rest
    let rec emitTargetCopies : List (Nat × Nat) → List Instr
      | [] => []
      | (offset, target) :: rest =>
          localGet (accStart + offset) ++ localSet target ++ emitTargetCopies rest
    emitInitStores (enumerate initValues) ++
      i64Const 0 ++ localSet releaseReadyLocal ++
      ([Instr.block [Instr.loop (bodyLets.flatMap (emitLocalLet childScratch) ++
        emitBodyStages (enumerate bodyValues) ++
        emitExpr childScratch bodyDone ++ localSet doneSlot ++
        emitGuardedAccumulatorReleases releaseIndex releaseReadyLocal accStart releaseOffsets ++
        emitTempCopies (List.range resultWidth) ++
        i64Const 1 ++ localSet releaseReadyLocal ++
        localGet doneSlot ++ i64Const 0 ++ i64Ne ++ [Instr.brIf 1] ++
        [Instr.br 0])]]) ++
      emitTargetCopies (enumerate targets)

  partial def emitHeapLinearPredicate
      (scratch : Nat)
      (ptr : Expr)
      (continueTag fieldSlotCount recursiveFieldOffset fieldStart : Nat)
      (predicate : Expr)
      (stopWhenTrue terminalValue : Bool) : List Instr :=
    let ptrLocal := scratch
    let resultLocal := scratch + 1
    let childScratch := scratch + 2
    let rec emitFieldLoads : List Nat → List Instr
      | [] => []
      | offset :: rest =>
          localGet ptrLocal ++ i64Const ((1 + offset) * 8) ++ [Instr.addI64] ++
            i32WrapI64 ++ i64Load ++ localSet (fieldStart + offset) ++
            emitFieldLoads rest
    let stopCond :=
      emitExpr childScratch predicate ++ i64Const 0 ++ i64Ne ++
        (if stopWhenTrue then [] else [Instr.eqzI32])
    let stopValue := if stopWhenTrue then 1 else 0
    let terminal := if terminalValue then 1 else 0
    emitExpr childScratch ptr ++ localSet ptrLocal ++
      i64Const terminal ++ localSet resultLocal ++
      ([Instr.block [Instr.loop (localGet ptrLocal ++ i64Const 0 ++ [Instr.addI64] ++ i32WrapI64 ++ i64Load ++
          i64Const continueTag ++ i64Ne ++ [Instr.brIf 1] ++
        emitFieldLoads (List.range fieldSlotCount) ++
        stopCond ++ ([Instr.iff false (i64Const stopValue ++ localSet resultLocal ++ [Instr.br 2]) none]) ++
        localGet (fieldStart + recursiveFieldOffset) ++ localSet ptrLocal ++
        [Instr.br 0])]]) ++
      localGet resultLocal

  partial def emitExpr (scratch : Nat) : Expr → List Instr
    | .local index => localGet index
    | .trap => [Instr.unreachable]
    | .u64 value => i64Const value
    | .u64Bin .natAdd left right => emitNatAdd scratch left right
    | .u64Bin .natSub left right => emitNatSub scratch left right
    | .u64Bin .natMul left right => emitNatMul scratch left right
    | .u64Bin .divU left right => emitCheckedDivMod scratch .divU left right
    | .u64Bin .modU left right => emitCheckedDivMod scratch .modU left right
    | .u64Bin op left right => emitExpr scratch left ++ emitExpr scratch right ++ emitU64Op op
    | .ite cond thenValue elseValue =>
        emitCond scratch cond ++ ([Instr.iff true (emitExpr scratch thenValue) (some (emitExpr scratch elseValue))])
    | .letE slot value body => emitExpr scratch value ++ localSet slot ++ emitExpr scratch body
    | .arrayAllocSlots width childMask cells => emitArrayAllocSlots scratch width childMask cells
    | .runtimeStat stat => globalGet (runtimeStatGlobal stat)
    | .release ptr => emitExpr scratch ptr ++ unreachable
    | .heapAllocSlots childMask ownedMask values =>
        emitHeapAllocSlots scratch childMask ownedMask values
    | .heapLoadSlot ptr slot => emitHeapLoadSlot scratch ptr slot
    | .arrayLiteralSlots width childMask elements =>
        emitArrayLiteralSlots scratch width childMask elements
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
    | .arrayFoldMultiSlot sourceWidth resultWidth reverse array start stop initValues accStart itemStart
        bodyValues bodyLets bodyDone _releaseOffsets resultSlot =>
        emitArrayFoldMultiSlot 0 scratch sourceWidth resultWidth reverse array start stop initValues
          accStart itemStart bodyValues bodyLets bodyDone [] resultSlot
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
        bodyValues bodyLets bodyDone _releaseOffsets resultSlot =>
        emitByteArrayFoldMultiSlot 0 scratch resultWidth ptr len start stop initValues accStart
          byteSlot bodyValues bodyLets bodyDone [] resultSlot
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone _releaseOffsets resultSlot =>
        emitRangeFoldMultiSlot 0 scratch resultWidth start stop step initValues accStart itemSlot
          bodyValues bodyLets bodyDone [] resultSlot
    | .loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone
        _releaseOffsets resultSlot =>
        emitLoopFoldMultiSlot 0 scratch resultWidth initValues accStart bodyValues bodyLets
          bodyDone [] resultSlot
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
      List Instr :=
    match values with
    | .arrayFoldMultiSlot sourceWidth resultWidth reverse array start stop initValues accStart itemStart
        bodyValues bodyLets bodyDone releaseOffsets _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.arrayFoldMultiSlot sourceWidth resultWidth reverse array start stop initValues accStart
                itemStart bodyValues bodyLets bodyDone releaseOffsets offset
                : Expr)
          if values == expected then
            emitArrayFoldMultiSlotAssign 0 scratch sourceWidth resultWidth reverse array start stop
              initValues accStart itemStart bodyValues bodyLets bodyDone [] slots
          else
            (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
        else
          (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
        bodyValues bodyLets bodyDone releaseOffsets _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart
                byteSlot bodyValues bodyLets bodyDone releaseOffsets offset
                : Expr)
          if values == expected then
            emitByteArrayFoldMultiSlotAssign 0 scratch resultWidth ptr len start stop initValues
              accStart byteSlot bodyValues bodyLets bodyDone [] slots
          else
            (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
        else
          (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
        bodyLets bodyDone releaseOffsets _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot
                bodyValues bodyLets bodyDone releaseOffsets offset
                : Expr)
          if values == expected then
            emitRangeFoldMultiSlotAssign 0 scratch resultWidth start stop step initValues accStart
              itemSlot bodyValues bodyLets bodyDone [] slots
          else
            (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
        else
          (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
    | .loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone
        releaseOffsets _ :: _ =>
        if slots.length == resultWidth && values.length == resultWidth then
          let expected :=
            (List.range resultWidth).map fun offset =>
              (.loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone
                releaseOffsets offset
                : Expr)
          if values == expected then
            emitLoopFoldMultiSlotAssign 0 scratch resultWidth initValues accStart bodyValues
              bodyLets bodyDone [] slots
          else
            (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
        else
          (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst
    | _ =>
        (slots.zip values).flatMap fun item => emitExpr scratch item.snd ++ localSet item.fst

  partial def emitLocalLet (scratch : Nat) : LocalLet → List Instr
    | .expr slot value => emitExpr scratch value ++ localSet slot
    | .call slots index args =>
        args.flatMap (emitExpr scratch) ++ call index ++ slots.reverse.flatMap localSet
    | .slots slots values => emitSlotsAssign scratch slots values
    | .branch cond thenLets elseLets =>
        emitCond scratch cond ++ ([Instr.iff false (thenLets.flatMap (emitLocalLet scratch)) (some (elseLets.flatMap (emitLocalLet scratch)))])

  partial def emitCond (scratch : Nat) : Cond → List Instr
    | .true => [Instr.constI32 1]
    | .false => [Instr.constI32 0]
    | .eqU64 left right => emitExpr scratch left ++ emitExpr scratch right ++ [Instr.eqI64]
    | .ltU64 left right => emitExpr scratch left ++ emitExpr scratch right ++ i64LtU
    | .leU64 left right => emitExpr scratch left ++ emitExpr scratch right ++ i64LeU
    | .not cond => emitCond scratch cond ++ [Instr.eqzI32]
    | .and left right =>
        emitCond scratch left ++ ([Instr.iffI32 (emitCond scratch right) (some ([Instr.constI32 0]))])
    | .or left right =>
        emitCond scratch left ++ ([Instr.iffI32 ([Instr.constI32 1]) (some (emitCond scratch right))])
end

mutual
partial def emitExprWithRelease (releaseIndex scratch : Nat) : Expr → List Instr
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
      emitCondWithRelease releaseIndex scratch cond ++ ([Instr.iff true (emitExprWithRelease releaseIndex scratch thenValue) (some (emitExprWithRelease releaseIndex scratch elseValue))])
  | .letE slot value body =>
      emitExprWithRelease releaseIndex scratch value ++ localSet slot ++
        emitExprWithRelease releaseIndex scratch body
  | .letCall slots index args body =>
      args.flatMap (emitExprWithRelease releaseIndex scratch) ++ call index ++
        slots.reverse.flatMap localSet ++ emitExprWithRelease releaseIndex scratch body
  | .letLets lets body =>
      lets.flatMap (emitLocalLetWithRelease releaseIndex scratch) ++
        emitExprWithRelease releaseIndex scratch body
  | .runtimeStat stat => globalGet (runtimeStatGlobal stat)
  | .release ptr =>
      emitExprWithRelease releaseIndex scratch ptr ++ call releaseIndex ++
        globalGet (runtimeStatGlobal .frees)
  | .arrayFoldMultiSlot sourceWidth resultWidth reverse array start stop initValues accStart itemStart
      bodyValues bodyLets bodyDone releaseOffsets resultSlot =>
      emitArrayFoldMultiSlot releaseIndex scratch sourceWidth resultWidth reverse array start stop
        initValues accStart itemStart bodyValues bodyLets bodyDone releaseOffsets resultSlot
  | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyLets bodyDone releaseOffsets resultSlot =>
      emitByteArrayFoldMultiSlot releaseIndex scratch resultWidth ptr len start stop initValues
        accStart byteSlot bodyValues bodyLets bodyDone releaseOffsets resultSlot
  | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
      bodyLets bodyDone releaseOffsets resultSlot =>
      emitRangeFoldMultiSlot releaseIndex scratch resultWidth start stop step initValues accStart
        itemSlot bodyValues bodyLets bodyDone releaseOffsets resultSlot
  | .loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone releaseOffsets
      resultSlot =>
      emitLoopFoldMultiSlot releaseIndex scratch resultWidth initValues accStart bodyValues bodyLets
        bodyDone releaseOffsets resultSlot
  | expr => emitExpr scratch expr

partial def emitCondWithRelease (releaseIndex scratch : Nat) : Cond → List Instr
  | .true => [Instr.constI32 1]
  | .false => [Instr.constI32 0]
  | .eqU64 left right =>
      emitExprWithRelease releaseIndex scratch left ++
        emitExprWithRelease releaseIndex scratch right ++ [Instr.eqI64]
  | .ltU64 left right =>
      emitExprWithRelease releaseIndex scratch left ++
        emitExprWithRelease releaseIndex scratch right ++ i64LtU
  | .leU64 left right =>
      emitExprWithRelease releaseIndex scratch left ++
        emitExprWithRelease releaseIndex scratch right ++ i64LeU
  | .not cond => emitCondWithRelease releaseIndex scratch cond ++ [Instr.eqzI32]
  | .and left right =>
      emitCondWithRelease releaseIndex scratch left ++ ([Instr.iffI32 (emitCondWithRelease releaseIndex scratch right) (some ([Instr.constI32 0]))])
  | .or left right =>
      emitCondWithRelease releaseIndex scratch left ++ ([Instr.iffI32 ([Instr.constI32 1]) (some (emitCondWithRelease releaseIndex scratch right))])

partial def emitSlotsAssignWithRelease
    (releaseIndex scratch : Nat) (slots : List Nat) (values : List Expr) : List Instr :=
  match values with
  | .arrayFoldMultiSlot sourceWidth resultWidth reverse array start stop initValues accStart itemStart
      bodyValues bodyLets bodyDone releaseOffsets _ :: _ =>
      if slots.length == resultWidth && values.length == resultWidth then
        let expected :=
          (List.range resultWidth).map fun offset =>
            (.arrayFoldMultiSlot sourceWidth resultWidth reverse array start stop initValues accStart
              itemStart bodyValues bodyLets bodyDone releaseOffsets offset
              : Expr)
        if values == expected then
          emitArrayFoldMultiSlotAssign releaseIndex scratch sourceWidth resultWidth reverse array
            start stop initValues accStart itemStart bodyValues bodyLets bodyDone releaseOffsets slots
        else
          (slots.zip values).flatMap fun item =>
            emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
      else
        (slots.zip values).flatMap fun item =>
          emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
  | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyLets bodyDone releaseOffsets _ :: _ =>
      if slots.length == resultWidth && values.length == resultWidth then
        let expected :=
          (List.range resultWidth).map fun offset =>
            (.byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart
              byteSlot bodyValues bodyLets bodyDone releaseOffsets offset
              : Expr)
        if values == expected then
          emitByteArrayFoldMultiSlotAssign releaseIndex scratch resultWidth ptr len start stop
            initValues accStart byteSlot bodyValues bodyLets bodyDone releaseOffsets slots
        else
          (slots.zip values).flatMap fun item =>
            emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
      else
        (slots.zip values).flatMap fun item =>
          emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
  | .rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot bodyValues
      bodyLets bodyDone releaseOffsets _ :: _ =>
      if slots.length == resultWidth && values.length == resultWidth then
        let expected :=
          (List.range resultWidth).map fun offset =>
            (.rangeFoldMultiSlot resultWidth start stop step initValues accStart itemSlot
              bodyValues bodyLets bodyDone releaseOffsets offset
              : Expr)
        if values == expected then
          emitRangeFoldMultiSlotAssign releaseIndex scratch resultWidth start stop step initValues
            accStart itemSlot bodyValues bodyLets bodyDone releaseOffsets slots
        else
          (slots.zip values).flatMap fun item =>
            emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
      else
        (slots.zip values).flatMap fun item =>
          emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
  | .loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone
      releaseOffsets _ :: _ =>
      if slots.length == resultWidth && values.length == resultWidth then
        let expected :=
          (List.range resultWidth).map fun offset =>
            (.loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone
              releaseOffsets offset
              : Expr)
        if values == expected then
          emitLoopFoldMultiSlotAssign releaseIndex scratch resultWidth initValues accStart
            bodyValues bodyLets bodyDone releaseOffsets slots
        else
          (slots.zip values).flatMap fun item =>
            emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
      else
        (slots.zip values).flatMap fun item =>
          emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst
  | _ =>
      (slots.zip values).flatMap fun item =>
        emitExprWithRelease releaseIndex scratch item.snd ++ localSet item.fst

partial def emitLocalLetWithRelease (releaseIndex scratch : Nat) : LocalLet → List Instr
  | .expr slot value => emitExprWithRelease releaseIndex scratch value ++ localSet slot
  | .call slots index args =>
      args.flatMap (emitExprWithRelease releaseIndex scratch) ++ call index ++
        slots.reverse.flatMap localSet
  | .slots slots values => emitSlotsAssignWithRelease releaseIndex scratch slots values
  | .branch cond thenLets elseLets =>
      emitCondWithRelease releaseIndex scratch cond ++ ([Instr.iff false (thenLets.flatMap (emitLocalLetWithRelease releaseIndex scratch)) (some (elseLets.flatMap (emitLocalLetWithRelease releaseIndex scratch)))])

partial def emitCheckedDivModWithRelease
    (releaseIndex scratch : Nat)
    (op : LeanExe.IR.U64Op)
    (left right : Expr) : List Instr :=
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
    localGet rightLocal ++ i64Const 0 ++ [Instr.eqI64] ++
    ([Instr.iff true (zeroValue) (some (localGet leftLocal ++ localGet rightLocal ++ emitU64Op op))])

partial def emitNatAddWithRelease
    (releaseIndex scratch : Nat)
    (left right : Expr) : List Instr :=
  let leftLocal := scratch
  let rightLocal := scratch + 1
  let resultLocal := scratch + 2
  let childScratch := scratch + 3
  emitExprWithRelease releaseIndex childScratch left ++ localSet leftLocal ++
    emitExprWithRelease releaseIndex childScratch right ++ localSet rightLocal ++
    localGet leftLocal ++ localGet rightLocal ++ [Instr.addI64] ++ localTee resultLocal ++
    localGet leftLocal ++ i64LtU ++
    ([Instr.iff true ([Instr.unreachable]) (some (localGet resultLocal))])

partial def emitNatMulWithRelease
    (releaseIndex scratch : Nat)
    (left right : Expr) : List Instr :=
  let leftLocal := scratch
  let rightLocal := scratch + 1
  let childScratch := scratch + 2
  emitExprWithRelease releaseIndex childScratch left ++ localSet leftLocal ++
    emitExprWithRelease releaseIndex childScratch right ++ localSet rightLocal ++
    localGet rightLocal ++ i64Const 0 ++ [Instr.eqI64] ++
    ([Instr.iff true (i64Const 0) (some (i64Const (2 ^ 64 - 1) ++ localGet rightLocal ++ [Instr.divUI64] ++
        localGet leftLocal ++ i64LtU ++
      ([Instr.iff true ([Instr.unreachable]) (some (localGet leftLocal ++ localGet rightLocal ++ [Instr.mulI64]))])))])

partial def emitNatSubWithRelease
    (releaseIndex scratch : Nat)
    (left right : Expr) : List Instr :=
  let leftLocal := scratch
  let rightLocal := scratch + 1
  let childScratch := scratch + 2
  emitExprWithRelease releaseIndex childScratch left ++ localSet leftLocal ++
    emitExprWithRelease releaseIndex childScratch right ++ localSet rightLocal ++
    localGet leftLocal ++ localGet rightLocal ++ i64LtU ++
    ([Instr.iff true (i64Const 0) (some (localGet leftLocal ++ localGet rightLocal ++ [Instr.subI64]))])
end

partial def emitStmt (releaseIndex scratch : Nat) : Stmt → List Instr
  | .skip => []
  | .assign index value => emitExprWithRelease releaseIndex scratch value ++ localSet index
  | .call slots index args =>
      args.flatMap (emitExprWithRelease releaseIndex scratch) ++ call index ++
        slots.reverse.flatMap localSet
  | .release ptr => emitExprWithRelease releaseIndex scratch ptr ++ call releaseIndex
  | .arrayFoldMultiSlotAssign sourceWidth resultWidth reverse array start stop initValues accStart itemStart
      bodyValues bodyLets bodyDone releaseOffsets targets =>
      emitArrayFoldMultiSlotAssign releaseIndex scratch sourceWidth resultWidth reverse array start stop
        initValues accStart itemStart bodyValues bodyLets bodyDone releaseOffsets targets
  | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart byteSlot
      bodyValues bodyLets bodyDone releaseOffsets targets =>
      emitByteArrayFoldMultiSlotAssign releaseIndex scratch resultWidth ptr len start stop initValues
        accStart byteSlot bodyValues bodyLets bodyDone releaseOffsets targets
  | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart itemSlot bodyValues
      bodyLets bodyDone releaseOffsets targets =>
      emitRangeFoldMultiSlotAssign releaseIndex scratch resultWidth start stop step initValues accStart
        itemSlot bodyValues bodyLets bodyDone releaseOffsets targets
  | .loopFoldMultiSlotAssign resultWidth initValues accStart bodyValues bodyLets bodyDone
      releaseOffsets targets =>
      emitLoopFoldMultiSlotAssign releaseIndex scratch resultWidth initValues accStart bodyValues
        bodyLets bodyDone releaseOffsets targets
  | .ite cond thenStmt elseStmt =>
      emitCondWithRelease releaseIndex scratch cond ++ ([Instr.iff false (emitStmt releaseIndex scratch thenStmt) (some (emitStmt releaseIndex scratch elseStmt))])
  | .seq first second => emitStmt releaseIndex scratch first ++ emitStmt releaseIndex scratch second
  | .while cond loopBody =>
      ([Instr.block [Instr.loop (emitCond scratch cond ++ [Instr.eqzI32, Instr.brIf 1] ++
      emitStmt releaseIndex scratch loopBody ++
      [Instr.br 0])]])

def localDecls (func : Func) : List UInt8 :=
  let extra := func.locals - func.params + funcScratch func
  if extra == 0 then
    ofNats [0]
  else
    u32leb 1 ++ u32leb extra ++ ofNats [126]

def emitFuncBody (releaseIndex : Nat) (func : Func) : List UInt8 :=
  let scratch := func.locals
  body (localDecls func)
    (encodeInstrs (emitStmt releaseIndex scratch func.body ++
      func.results.flatMap (emitExprWithRelease releaseIndex scratch)))

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
        exportEntry "free" 0 (module_.funcs.size + 3),
        exportEntry "allocCount" 3 (runtimeStatGlobal .allocs),
        exportEntry "retainCount" 3 (runtimeStatGlobal .retains),
        exportEntry "releaseCount" 3 (runtimeStatGlobal .releases),
        exportEntry "freeCount" 3 (runtimeStatGlobal .frees)]

def bodyI (locals : List UInt8) (code : List Instr) : List UInt8 :=
  body locals (encodeInstrs code)

def coreAllocBody : List UInt8 :=
  bodyI
    (ofNats [1, 6, 126])
    (rcAllocRawObject 1 (localGet 0))

def coreResetBody : List UInt8 :=
  bodyI
    (ofNats [0])
    (i64Const 4096 ++ globalSet 0 ++
      i64Const 0 ++ globalSet 1 ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .allocs) ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .retains) ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .releases) ++
      i64Const 0 ++ globalSet (runtimeStatGlobal .frees))

def coreRetainBody : List UInt8 :=
  let rcLocal := 1
  bodyI
    (ofNats [1, 1, 126])
    (localGet 0 ++ i64Const 0 ++ i64Ne ++
      ([Instr.iff false (rcHeaderLoad (localGet 0) 48 ++ i64Const rcMagic ++ i64Ne ++
          ([Instr.iff false (unreachable) none]) ++
      rcHeaderLoad (localGet 0) 40 ++ localSet rcLocal ++
      localGet rcLocal ++ i64Const 0 ++ i64Eq ++
        ([Instr.iff false (unreachable) none]) ++
        incGlobal (runtimeStatGlobal .retains) ++
        rcHeaderStore (localGet 0) 40 (localGet rcLocal ++ i64Const 1 ++ [Instr.addI64])) none]) ++
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
      ([Instr.block [Instr.loop (localGet slotLocal ++ localGet limitLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        localGet maskLocal ++ localGet slotLocal ++ i64ShrU ++ i64Const 1 ++ i64And ++
          i64Const 0 ++ i64Ne ++
          ([Instr.iff false (localGet 0 ++ localGet slotLocal ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64] ++
              i32WrapI64 ++ i64Load ++ localSet childLocal ++
            callReleaseChild) none]) ++
        localGet slotLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet slotLocal ++
        [Instr.br 0])]])
  let arrayReleaseLoop :=
    localGet 0 ++ i32WrapI64 ++ i64Load ++ localSet limitLocal ++
      rcHeaderLoad (localGet 0) 16 ++ localSet widthLocal ++
      rcHeaderLoad (localGet 0) 8 ++ localSet maskLocal ++
      i64Const 0 ++ localSet itemLocal ++
      ([Instr.block [Instr.loop (localGet itemLocal ++ localGet limitLocal ++ i64GeU ++
          [Instr.brIf 1] ++
        i64Const 0 ++ localSet slotLocal ++
        ([Instr.block [Instr.loop (localGet slotLocal ++ localGet widthLocal ++ i64GeU ++
            [Instr.brIf 1] ++
          localGet maskLocal ++ localGet slotLocal ++ i64ShrU ++ i64Const 1 ++ i64And ++
            i64Const 0 ++ i64Ne ++
            ([Instr.iff false (localGet 0 ++ i64Const 8 ++ [Instr.addI64] ++
                localGet itemLocal ++ localGet widthLocal ++ [Instr.mulI64] ++
                localGet slotLocal ++ [Instr.addI64] ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64] ++
                i32WrapI64 ++ i64Load ++ localSet childLocal ++
              callReleaseChild) none]) ++
          localGet slotLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet slotLocal ++
          [Instr.br 0])]]) ++
        localGet itemLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet itemLocal ++
        [Instr.br 0])]])
  let freeCurrent :=
    incGlobal (runtimeStatGlobal .frees) ++
      rcHeaderStore (localGet 0) 40 (i64Const 0) ++
      rcHeaderStore (localGet 0) 8 (globalGet 1) ++
      localGet 0 ++ globalSet 1
  bodyI
    (ofNats [1, 8, 126])
    (localGet 0 ++ i64Const 0 ++ i64Eq ++
      ([Instr.iff false (returnOp) none]) ++
      rcHeaderLoad (localGet 0) 48 ++ i64Const rcMagic ++ i64Ne ++
        ([Instr.iff false (unreachable) none]) ++
      rcHeaderLoad (localGet 0) 40 ++ localSet rcLocal ++
      localGet rcLocal ++ i64Const 0 ++ i64Eq ++
        ([Instr.iff false (unreachable) none]) ++
      incGlobal (runtimeStatGlobal .releases) ++
      i64Const 1 ++ localGet rcLocal ++ i64LtU ++
        ([Instr.iff false (rcHeaderStore (localGet 0) 40 (localGet rcLocal ++ i64Const 1 ++ [Instr.subI64]) ++
          returnOp) none]) ++
      rcHeaderLoad (localGet 0) 24 ++ localSet kindLocal ++
      localGet kindLocal ++ i64Const rcKindSlots ++ i64Eq ++
        ([Instr.iff false (rcHeaderLoad (localGet 0) 16 ++ localSet limitLocal ++
          rcHeaderLoad (localGet 0) 8 ++ localSet maskLocal ++
          slotReleaseLoop) none]) ++
      localGet kindLocal ++ i64Const rcKindArray ++ i64Eq ++
        ([Instr.iff false (arrayReleaseLoop) none]) ++
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

def wasiWriteFd (fd ptrLocal lenLocal fdWriteIndex : Nat) : List Instr :=
  i32Const 0 ++ localGet ptrLocal ++ i32WrapI64 ++ i32Store ++
    i32Const 4 ++ localGet lenLocal ++ i32WrapI64 ++ i32Store ++
    i32Const 8 ++ i32Const 0 ++ i32Store ++
    i32Const fd ++ i32Const 0 ++ i32Const 1 ++ i32Const 8 ++ call fdWriteIndex ++
    [Instr.eqzI32] ++ ([Instr.iff false (i32Const 8 ++ i32Load ++ localGet lenLocal ++ i32WrapI64 ++ i32Eq ++
      ([Instr.iff false [] (some ([Instr.unreachable]))])) (some ([Instr.unreachable]))])

def wasiWriteStdout (ptrLocal lenLocal fdWriteIndex : Nat) : List Instr :=
  wasiWriteFd 1 ptrLocal lenLocal fdWriteIndex

def wasiStdoutStartBody (entryIndex : Nat) : List UInt8 :=
  bodyI
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

def wasiReadStdinLoop (maxInput : Nat) : List Instr :=
  ([Instr.block [Instr.loop (i64Const (maxInput + 1) ++ localGet 1 ++ [Instr.subI64] ++ localSet 2 ++
    i32Const 0 ++ localGet 0 ++ localGet 1 ++ [Instr.addI64] ++ i32WrapI64 ++ i32Store ++
    i32Const 4 ++ localGet 2 ++ i32WrapI64 ++ i32Store ++
    i32Const 8 ++ i32Const 0 ++ i32Store ++
    i32Const 0 ++ i32Const 0 ++ i32Const 1 ++ i32Const 8 ++ call 1 ++
    [Instr.eqzI32, Instr.iff false [] (some [Instr.unreachable])] ++
    i32Const 8 ++ i32Load ++ i64ExtendI32U ++ localSet 3 ++
    localGet 3 ++ i64Const 0 ++ i64Eq ++ [Instr.brIf 1] ++
    localGet 1 ++ localGet 3 ++ [Instr.addI64] ++ localSet 1 ++
    i64Const maxInput ++ localGet 1 ++ i64LtU ++ [Instr.iff false [Instr.unreachable] none] ++
    [Instr.br 0])]])

def wasiReadArgvArrayWithImports
    (argsSizesGetIndex argsGetIndex maxArgs maxArgBytes : Nat) :
    List Instr :=
  let arrayBytes := 8 + maxArgs * 24
  let tableBytes := (maxArgs + 1) * 4
  let reservedBytes := wasiArgvReservedBytes maxArgs maxArgBytes
  i64Align8 (globalGet 0) ++ localSet 0 ++
    localGet 0 ++ i64Const arrayBytes ++ [Instr.addI64] ++ localSet 1 ++
    localGet 1 ++ i64Const tableBytes ++ [Instr.addI64] ++ localSet 2 ++
    localGet 0 ++ i64Const reservedBytes ++ [Instr.addI64] ++ globalSet 0 ++
    i32Const 16 ++ i32Const 20 ++ call argsSizesGetIndex ++
    [Instr.eqzI32, Instr.iff false [] (some [Instr.unreachable])] ++
    i32Const 16 ++ i32Load ++ i64ExtendI32U ++ localSet 3 ++
    i32Const 20 ++ i32Load ++ i64ExtendI32U ++ localSet 4 ++
    i64Const (maxArgs + 1) ++ localGet 3 ++ i64LtU ++ [Instr.iff false [Instr.unreachable] none] ++
    i64Const maxArgBytes ++ localGet 4 ++ i64LtU ++ [Instr.iff false [Instr.unreachable] none] ++
    localGet 3 ++ i64Const 0 ++ i64Eq ++ ([Instr.iff false (i64Const 0 ++ localSet 5) (some (localGet 3 ++ i64Const 1 ++ [Instr.subI64] ++ localSet 5))]) ++
    localGet 0 ++ i32WrapI64 ++ localGet 5 ++ i64Store ++
    localGet 1 ++ i32WrapI64 ++ localGet 2 ++ i32WrapI64 ++ call argsGetIndex ++
    [Instr.eqzI32, Instr.iff false [] (some [Instr.unreachable])] ++
    i64Const 0 ++ localSet 6 ++
    ([Instr.block [Instr.loop (localGet 6 ++ localGet 5 ++ i64GeU ++ [Instr.brIf 1] ++
      localGet 1 ++ localGet 6 ++ i64Const 1 ++ [Instr.addI64] ++ i64Const 4 ++ [Instr.mulI64, Instr.addI64] ++
        i32WrapI64 ++ i32Load ++ i64ExtendI32U ++ localSet 7 ++
      i64Const 0 ++ localSet 8 ++
      ([Instr.block [Instr.loop (localGet 7 ++ localGet 8 ++ [Instr.addI64] ++ i32WrapI64 ++ i32Load8U ++
          [Instr.eqzI32, Instr.brIf 1] ++
        localGet 8 ++ i64Const 1 ++ [Instr.addI64] ++ localSet 8 ++
        [Instr.br 0])]]) ++
      arraySlotAddress 3 0 (localGet 0) (localGet 6) ++ i64Const 0 ++ i64Store ++
      arraySlotAddress 3 1 (localGet 0) (localGet 6) ++ localGet 7 ++ i64Store ++
      arraySlotAddress 3 2 (localGet 0) (localGet 6) ++ localGet 8 ++ i64Store ++
      localGet 6 ++ i64Const 1 ++ [Instr.addI64] ++ localSet 6 ++
      [Instr.br 0])]])

def wasiReadArgvArray (maxArgs maxArgBytes : Nat) : List Instr :=
  wasiReadArgvArrayWithImports 1 2 maxArgs maxArgBytes

def wasiStdinStartBody (maxInput entryIndex : Nat) : List UInt8 :=
  bodyI
    (ofNats [1, 4, 126])
    (globalGet 0 ++ localSet 0 ++
      i64Align8 (localGet 0 ++ i64Const (maxInput + 1) ++ [Instr.addI64]) ++ globalSet 0 ++
      i64Const 0 ++ localSet 1 ++
      wasiReadStdinLoop maxInput ++
      localGet 0 ++ localGet 1 ++ call entryIndex ++
      localSet 1 ++
      localSet 0 ++
      wasiWriteStdout 0 1 0)

def wasiStdinExceptStartBody (maxInput entryIndex : Nat) : List UInt8 :=
  bodyI
    (ofNats [1, 9, 126])
    (globalGet 0 ++ localSet 0 ++
      i64Align8 (localGet 0 ++ i64Const (maxInput + 1) ++ [Instr.addI64]) ++ globalSet 0 ++
      i64Const 0 ++ localSet 1 ++
      wasiReadStdinLoop maxInput ++
      localGet 0 ++ localGet 1 ++ call entryIndex ++
      localSet 8 ++
      localSet 7 ++
      localSet 6 ++
      localSet 5 ++
      localSet 4 ++
      localGet 4 ++ i64Const 0 ++ i64Eq ++ ([Instr.iff false (wasiWriteFd 2 5 6 0 ++
        i32Const 1 ++ call 2) (some (localGet 4 ++ i64Const 1 ++ i64Eq ++ ([Instr.iff false (wasiWriteStdout 7 8 0) (some ([Instr.unreachable]))])))]))

def wasiArgvExceptStartBody (maxArgs maxArgBytes entryIndex : Nat) : List UInt8 :=
  bodyI
    (ofNats [1, 16, 126])
    (wasiReadArgvArray maxArgs maxArgBytes ++
      i64Const 0 ++ localGet 0 ++ call entryIndex ++
      localSet 15 ++
      localSet 14 ++
      localSet 13 ++
      localSet 12 ++
      localSet 11 ++
      localSet 10 ++
      localSet 9 ++
      localGet 9 ++ i64Const 0 ++ i64Eq ++ ([Instr.iff false (wasiWriteFd 2 11 12 0 ++
        i32Const 1 ++ call 3) (some (localGet 9 ++ i64Const 1 ++ i64Eq ++ ([Instr.iff false (wasiWriteStdout 14 15 0) (some ([Instr.unreachable]))])))]))

def wasiStdinArgvExceptStartBody
    (maxInput maxArgs maxArgBytes entryIndex : Nat) :
    List UInt8 :=
  bodyI
    (ofNats [1, 16, 126])
    (globalGet 0 ++ localSet 0 ++
      i64Align8 (localGet 0 ++ i64Const (maxInput + 1) ++ [Instr.addI64]) ++ globalSet 0 ++
      i64Const 0 ++ localSet 1 ++
      wasiReadStdinLoop maxInput ++
      localGet 0 ++ localSet 14 ++
      localGet 1 ++ localSet 15 ++
      wasiReadArgvArrayWithImports 2 3 maxArgs maxArgBytes ++
      i64Const 0 ++ localGet 14 ++ localGet 15 ++ i64Const 0 ++ localGet 0 ++ call entryIndex ++
      localSet 15 ++
      localSet 14 ++
      localSet 13 ++
      localSet 12 ++
      localSet 11 ++
      localSet 10 ++
      localSet 9 ++
      localGet 9 ++ i64Const 0 ++ i64Eq ++ ([Instr.iff false (wasiWriteFd 2 11 12 0 ++
        i32Const 1 ++ call 4) (some (localGet 9 ++ i64Const 1 ++ i64Eq ++ ([Instr.iff false (wasiWriteStdout 14 15 0) (some ([Instr.unreachable]))])))]))

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
