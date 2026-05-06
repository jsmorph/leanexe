import LeanExe.Core

namespace LeanExe.Wasm.Binary

def collatzMaxSteps : Nat :=
  10000

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

def collatzTypeSection : List UInt8 :=
  wasmSection 1 <| vec [
    funcType [i64] [i64]
  ]

def collatzFunctionSection : List UInt8 :=
  wasmSection 3 <| byteVec (ofNats [0])

def collatzExportSection : List UInt8 :=
  wasmSection 7 <| vec [
    exportEntry "collatz_steps" 0 0
  ]

def collatzBody : List UInt8 :=
  body
    (ofNats [1, 2, 126])
    (i64Const 0 ++ ofNats [
      33, 1
    ] ++ i64Const collatzMaxSteps ++ ofNats [
      33, 2,
      2, 64,
      3, 64,
      32, 2,
      80,
      13, 1,
      32, 0
    ] ++ i64Const 1 ++ ofNats [
      88,
      13, 1,
      32, 0
    ] ++ i64Const 1 ++ ofNats [
      131,
      80,
      4, 64,
      32, 0
    ] ++ i64Const 2 ++ ofNats [
      128,
      33, 0,
      5,
      32, 0
    ] ++ i64Const 3 ++ ofNats [
      126
    ] ++ i64Const 1 ++ ofNats [
      124,
      33, 0,
      11,
      32, 1
    ] ++ i64Const 1 ++ ofNats [
      124,
      33, 1,
      32, 2
    ] ++ i64Const 1 ++ ofNats [
      125,
      33, 2,
      12, 0,
      11,
      11,
      32, 1
    ])

def collatzCodeSection : List UInt8 :=
  wasmSection 10 <| vec [
    collatzBody
  ]

def collatzModuleBytes : ByteArray :=
  ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0]
    ++ collatzTypeSection
    ++ collatzFunctionSection
    ++ collatzExportSection
    ++ collatzCodeSection).toArray

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

def collatzWat : String :=
  String.intercalate "\n" [
    "(module",
    "  (func (export \"collatz_steps\") (param $n i64) (result i64)",
    "    (local $steps i64)",
    "    (local $fuel i64)",
    "    i64.const 0",
    "    local.set $steps",
    s!"    i64.const {collatzMaxSteps}",
    "    local.set $fuel",
    "    block $done",
    "      loop $loop",
    "        local.get $fuel",
    "        i64.eqz",
    "        br_if $done",
    "        local.get $n",
    "        i64.const 1",
    "        i64.le_u",
    "        br_if $done",
    "        local.get $n",
    "        i64.const 1",
    "        i64.and",
    "        i64.eqz",
    "        if",
    "          local.get $n",
    "          i64.const 2",
    "          i64.div_u",
    "          local.set $n",
    "        else",
    "          local.get $n",
    "          i64.const 3",
    "          i64.mul",
    "          i64.const 1",
    "          i64.add",
    "          local.set $n",
    "        end",
    "        local.get $steps",
    "        i64.const 1",
    "        i64.add",
    "        local.set $steps",
    "        local.get $fuel",
    "        i64.const 1",
    "        i64.sub",
    "        local.set $fuel",
    "        br $loop",
    "      end",
    "    end",
    "    local.get $steps)",
    ")",
    ""
  ]

end LeanExe.Wasm.Binary
