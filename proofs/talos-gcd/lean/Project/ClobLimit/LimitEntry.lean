import Project.ClobLimit.RunMatchCorrect

/-!
# Exported `limit` entry decomposition

Function 21 checks validity, calls function 18 on the valid path, and then
selects the filled or residual result.  These definitions keep each unselected
generated branch opaque while later proofs execute the surrounding control.
-/

namespace Project.ClobLimit.LimitEntry

open Wasm Project.ClobLimit

def limitArgs (book : UInt64) (order : Project.Clob.OrderL) : List Value :=
  [.i64 order.oqty, .i64 order.oprice, .i64 order.oside,
    .i64 order.otrader, .i64 order.oid, .i64 book]

def entryFrame (book : UInt64) (order : Project.Clob.OrderL) : Locals :=
  func21Def.toLocals (limitArgs book order).reverse

private def outerBranch (takeValid : Bool) : Wasm.Program :=
  match (func21[30]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ valid invalid) =>
      if takeValid then valid else invalid
  | _ => []

private def validResultBranch (takeFilled : Bool) : Wasm.Program :=
  match ((outerBranch true)[43]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ filled residual) =>
      if takeFilled then filled else residual
  | _ => []

def invalidProg : Wasm.Program :=
  outerBranch false

def residualProg : Wasm.Program :=
  validResultBranch false

def filledProg : Wasm.Program :=
  [
  .call 19,
  .localSet 31,
  .localGet 31,
  .localSet 37,
  .localGet 27,
  .localSet 38,
  .localGet 29,
  .localSet 39
]

def entryProg : Wasm.Program :=
  [
  .constI64 0,
  .localSet 6,
  .localGet 0,
  .localSet 7,
  .localGet 1,
  .localSet 8,
  .localGet 2,
  .localSet 9,
  .localGet 3,
  .localSet 10,
  .localGet 4,
  .localSet 11,
  .localGet 5,
  .localSet 12,
  .localGet 6,
  .localGet 7,
  .localGet 8,
  .localGet 9,
  .localGet 10,
  .localGet 11,
  .localGet 12,
  .call 6,
  .localSet 13,
  .localGet 13,
  .constI64 1,
  .eqI64,
  .iff 0 1 [.constI64 1] [.constI64 0],
  .constI64 0,
  .eqI64,
  .eqz
]

def validCallProg : Wasm.Program :=
  [
  .constI64 0,
  .localSet 14,
  .localGet 0,
  .localSet 15,
  .localGet 1,
  .localSet 16,
  .localGet 2,
  .localSet 17,
  .localGet 3,
  .localSet 18,
  .localGet 4,
  .localSet 19,
  .localGet 5,
  .localSet 20,
  .localGet 14,
  .localGet 15,
  .localGet 16,
  .localGet 17,
  .localGet 18,
  .localGet 19,
  .localGet 20,
  .call 18
]

def validResultStoreProg : Wasm.Program :=
  [
  .localSet 25,
  .localSet 24,
  .localSet 23,
  .localSet 22,
  .localSet 21,
  .localGet 22,
  .localSet 27,
  .localGet 24,
  .localSet 29,
  .localGet 25,
  .localSet 30
]

def validConditionProg : Wasm.Program :=
  [
  .localGet 30,
  .constI64 0,
  .eqI64,
  .iff 0 1 [.constI64 1] [.constI64 0],
  .constI64 1,
  .eqI64,
  .iff 0 1 [.constI64 1] [.constI64 0],
  .constI64 0,
  .eqI64,
  .eqz
]

def validResultPrefixProg : Wasm.Program :=
  validResultStoreProg ++ validConditionProg

def validPrefixProg : Wasm.Program :=
  validCallProg ++ validResultPrefixProg

def validProg : Wasm.Program :=
  validPrefixProg ++ [
  .iff 0 0 filledProg residualProg
]

def resultProg : Wasm.Program :=
  [
  .localGet 37,
  .localGet 38,
  .localGet 39
]

set_option maxRecDepth 1048576 in
theorem func21_decomposition :
    func21 = entryProg ++ [.iff 0 0 validProg invalidProg] ++ resultProg := by
  unfold func21 entryProg validProg validPrefixProg validCallProg
    validResultPrefixProg validResultStoreProg validConditionProg filledProg
    residualProg invalidProg validResultBranch outerBranch resultProg
  rfl

def residualStatusProg : Wasm.Program :=
  [
  .call 19,
  .localSet 32,
  .localGet 32,
  .localSet 37,
  .localGet 27,
  .localSet 33,
  .localGet 33,
  .localSet 40
]

def residualOrderFieldsProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 46,
  .localGet 2,
  .localSet 47,
  .localGet 3,
  .localSet 48,
  .localGet 4,
  .localSet 49,
  .localGet 30,
  .localSet 50
]

def residualLengthProg : Wasm.Program :=
  [
  .localGet 40,
  .wrapI64,
  .load64 0,
  .localSet 41,
  .localGet 41,
  .constI64 5,
  .mulI64,
  .localSet 42,
  .localGet 41,
  .constI64 1,
  .addI64,
  .localSet 43
]

def residualOrderPrepareProg : Wasm.Program :=
  residualOrderFieldsProg ++ residualLengthProg

def residualAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 43,
  .constI64 5,
  .mulI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .constI64 7,
  .addI64,
  .constI64 8,
  .divUI64,
  .constI64 8,
  .mulI64,
  .localSet 53,
  .localGet 53,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 53
  ] [],
  .constI64 0,
  .localSet 58,
  .constI64 0,
  .localSet 54,
  .globalGet 1,
  .localSet 55
]

def residualArrayPrepareProg : Wasm.Program :=
  residualOrderPrepareProg ++ residualAllocPrepareProg

def residualPrepareProg : Wasm.Program :=
  residualStatusProg ++ residualArrayPrepareProg

def residualAllocSearchBodyProg : Wasm.Program :=
  [
  .localGet 55,
  .constI64 0,
  .eqI64,
  .br_if 1,
  .localGet 58,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 55,
  .constI64 32,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 56,
  .localGet 55,
  .constI64 8,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 57,
  .localGet 56,
  .localGet 53,
  .geUI64,
  .iff 0 0 [
    .localGet 54,
    .constI64 0,
    .eqI64,
    .iff 0 0 [
      .localGet 57,
      .globalSet 1
    ] [
      .localGet 54,
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet 57,
      .store64 0
    ],
    .localGet 55,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 55,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 55,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 56,
    .store64 0,
    .localGet 55,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 55,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 5,
    .store64 0,
    .localGet 55,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0,
    .localGet 55,
    .localSet 58
  ] [
    .localGet 55,
    .localSet 54,
    .localGet 57,
    .localSet 55
  ],
  .br 0
]

def residualAllocSearchProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 residualAllocSearchBodyProg]]

def residualAllocBumpProg : Wasm.Program :=
  [
  .localGet 58,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localGet 53,
    .addI64,
    .localSet 56,
    .localGet 56,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 56,
    .constI64 1,
    .subI64,
    .constI64 65536,
    .divUI64,
    .constI64 1,
    .addI64,
    .localSet 57,
    .memorySize,
    .extendUI32,
    .localGet 57,
    .ltUI64,
    .iff 0 0 [
      .localGet 57,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const 4294967295,
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localSet 58,
    .localGet 56,
    .globalSet 0,
    .localGet 58,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 58,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 58,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 53,
    .store64 0,
    .localGet 58,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 58,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 5,
    .store64 0,
    .localGet 58,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0
  ] []
]

def residualAllocFinishProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 58,
  .localSet 44,
  .localGet 44,
  .wrapI64,
  .localGet 43,
  .store64 0,
  .constI64 0,
  .localSet 45
]

def residualAllocProg : Wasm.Program :=
  residualAllocSearchProg ++ residualAllocBumpProg ++ residualAllocFinishProg

def residualCopyProg : Wasm.Program :=
  (residualProg.drop 71).take 1

def residualFinishProg : Wasm.Program :=
  residualProg.drop 72

set_option maxRecDepth 1048576 in
theorem residualProg_decomposition :
    residualProg = residualPrepareProg ++ residualAllocProg ++
      residualCopyProg ++ residualFinishProg := by
  unfold residualPrepareProg residualStatusProg residualArrayPrepareProg
    residualOrderPrepareProg residualAllocPrepareProg residualAllocProg
    residualAllocSearchProg residualAllocSearchBodyProg residualAllocBumpProg
    residualAllocFinishProg residualOrderFieldsProg residualLengthProg
    residualCopyProg residualFinishProg residualProg validResultBranch
    outerBranch func21
  rfl

end Project.ClobLimit.LimitEntry
