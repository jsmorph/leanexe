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

partial def s64lebNat (n : Nat) : List UInt8 :=
  let low := n % 128
  let rest := n / 128
  if rest = 0 ∧ low < 64 then
    [byte low]
  else
    byte (low + 128) :: s64lebNat rest

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
  byte 66 :: s64lebNat n

def localGet (index : Nat) : List UInt8 :=
  ofNats [32] ++ u32leb index

def localSet (index : Nat) : List UInt8 :=
  ofNats [33] ++ u32leb index

def call (index : Nat) : List UInt8 :=
  ofNats [16] ++ u32leb index

namespace CoreWasm

abbrev Expr := LeanExe.IR.Expr
abbrev Cond := LeanExe.IR.Cond
abbrev Stmt := LeanExe.IR.Stmt
abbrev Func := LeanExe.IR.Func
abbrev Module := LeanExe.IR.Module

def emitU64Op : LeanExe.IR.U64Op → List UInt8
  | .add => ofNats [124]
  | .sub => ofNats [125]
  | .mul => ofNats [126]
  | .divU => ofNats [128]
  | .modU => ofNats [130]
  | .bitAnd => ofNats [131]

mutual
  partial def emitExpr : Expr → List UInt8
    | .local index => localGet index
    | .u64 value => i64Const value
    | .u64Bin op left right => emitExpr left ++ emitExpr right ++ emitU64Op op
    | .ite cond thenValue elseValue =>
        emitCond cond ++ ofNats [4, 126] ++ emitExpr thenValue ++ ofNats [5] ++
          emitExpr elseValue ++ ofNats [11]
    | .call index args => args.flatMap emitExpr ++ call index

  partial def emitCond : Cond → List UInt8
    | .true => ofNats [65, 1]
    | .false => ofNats [65, 0]
    | .eqU64 left right => emitExpr left ++ emitExpr right ++ ofNats [81]
    | .not cond => emitCond cond ++ ofNats [69]
    | .and left right => emitCond left ++ emitCond right ++ ofNats [113]
    | .or left right => emitCond left ++ emitCond right ++ ofNats [114]
end

partial def emitStmt : Stmt → List UInt8
  | .skip => []
  | .assign index value => emitExpr value ++ localSet index
  | .seq first second => emitStmt first ++ emitStmt second
  | .while cond loopBody =>
      ofNats [2, 64, 3, 64] ++
      emitCond cond ++ ofNats [69, 13, 1] ++
      emitStmt loopBody ++
      ofNats [12, 0, 11, 11]

def localDecls (func : Func) : List UInt8 :=
  let extra := func.locals - func.params
  if extra == 0 then
    ofNats [0]
  else
    u32leb 1 ++ u32leb extra ++ ofNats [126]

def emitFuncBody (func : Func) : List UInt8 :=
  body (localDecls func) (emitStmt func.body ++ emitExpr func.result)

def typeForFunc (func : Func) : List UInt8 :=
  funcType (List.replicate func.params i64) [i64]

def typeSection (module_ : Module) : List UInt8 :=
  wasmSection 1 <| vec (module_.funcs.toList.map typeForFunc)

def functionSection (module_ : Module) : List UInt8 :=
  wasmSection 3 <| u32Vec (List.range module_.funcs.size)

def enumerateAux {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | item :: rest, index => (index, item) :: enumerateAux rest (index + 1)

def enumerate {α : Type} (items : List α) : List (Nat × α) :=
  enumerateAux items 0

def exportSection (module_ : Module) : List UInt8 :=
  wasmSection 7 <| vec <|
    (enumerate module_.funcs.toList |>.filterMap fun item =>
      item.snd.exportName.map (fun exportName => exportEntry exportName 0 item.fst))

def codeSection (module_ : Module) : List UInt8 :=
  wasmSection 10 <| vec (module_.funcs.toList.map emitFuncBody)

def moduleBytes (module_ : Module) : ByteArray :=
  ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
    ++ typeSection module_
    ++ functionSection module_
    ++ exportSection module_
    ++ codeSection module_).toArray

def indent (spaces : Nat) (lines : List String) : List String :=
  let pad := String.ofList (List.replicate spaces ' ')
  lines.map (fun line => pad ++ line)

mutual
  partial def exprWatLines : Expr → List String
    | .local index => [s!"local.get {index}"]
    | .u64 value => [s!"i64.const {value}"]
    | .u64Bin .add left right => exprWatLines left ++ exprWatLines right ++ ["i64.add"]
    | .u64Bin .sub left right => exprWatLines left ++ exprWatLines right ++ ["i64.sub"]
    | .u64Bin .mul left right => exprWatLines left ++ exprWatLines right ++ ["i64.mul"]
    | .u64Bin .divU left right => exprWatLines left ++ exprWatLines right ++ ["i64.div_u"]
    | .u64Bin .modU left right => exprWatLines left ++ exprWatLines right ++ ["i64.rem_u"]
    | .u64Bin .bitAnd left right => exprWatLines left ++ exprWatLines right ++ ["i64.and"]
    | .ite cond thenValue elseValue =>
        condWatLines cond ++
          ["if (result i64)"] ++
          indent 2 (exprWatLines thenValue) ++
          ["else"] ++
          indent 2 (exprWatLines elseValue) ++
          ["end"]
    | .call index args => args.flatMap exprWatLines ++ [s!"call {index}"]

  partial def condWatLines : Cond → List String
    | .true => ["i32.const 1"]
    | .false => ["i32.const 0"]
    | .eqU64 left right => exprWatLines left ++ exprWatLines right ++ ["i64.eq"]
    | .not cond => condWatLines cond ++ ["i32.eqz"]
    | .and left right => condWatLines left ++ condWatLines right ++ ["i32.and"]
    | .or left right => condWatLines left ++ condWatLines right ++ ["i32.or"]
end

partial def stmtWatLines : Stmt → List String
  | .skip => []
  | .assign index value => exprWatLines value ++ [s!"local.set {index}"]
  | .seq first second => stmtWatLines first ++ stmtWatLines second
  | .while cond loopBody =>
      ["block", "  loop"] ++
        indent 4 (condWatLines cond ++ ["i32.eqz", "br_if 1"] ++
          stmtWatLines loopBody ++ ["br 0"]) ++
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
  let extra := func.locals - func.params
  let exportText :=
    match func.exportName with
    | some exportName => s!" (export \"{exportName}\")"
    | none => ""
  [s!"(func{exportText}{paramWat func.params} (result i64)"] ++
    indent 2 (localWat extra ++ stmtWatLines func.body ++ exprWatLines func.result) ++
    [")"]

def moduleWat (module_ : Module) : String :=
  String.intercalate "\n" <|
    ["(module"] ++
      (module_.funcs.toList.flatMap (fun func => indent 2 (funcWatLines func))) ++
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
