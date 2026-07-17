import Project.ClobMarket.RunMatch
import Project.ClobMarket.Helpers

/-!
# Exported `market` decomposition

Function 21 checks validity, transforms the taker's price, calls function 18,
and returns its book and trades.  The definitions isolate the invalid
allocator from the valid matcher path.  Later proofs elaborate one selected
branch at a time.
-/

namespace Project.ClobMarket.Entry

open Wasm Project.Clob Project.ClobMarket

def marketArgs (book : UInt64) (order : OrderL) : List Value :=
  [.i64 order.oqty, .i64 order.oprice, .i64 order.oside,
    .i64 order.otrader, .i64 order.oid, .i64 book]

def entryFrame (book : UInt64) (order : OrderL) : Locals :=
  func21Def.toLocals (marketArgs book order).reverse

def outerBranch (takeValid : Bool) : Wasm.Program :=
  match (func21[30]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ valid invalid) =>
      if takeValid then valid else invalid
  | _ => []

def invalidProg : Wasm.Program :=
  outerBranch false

def invalidPrepareProg : Wasm.Program :=
  invalidProg.take 30

def invalidSearchProg : Wasm.Program :=
  (invalidProg.drop 30).take 1

def invalidBumpProg : Wasm.Program :=
  (invalidProg.drop 31).take 4

def invalidFinishProg : Wasm.Program :=
  invalidProg.drop 35

set_option maxRecDepth 1048576 in
theorem invalidProg_decomposition :
    invalidProg = invalidPrepareProg ++ invalidSearchProg ++
      invalidBumpProg ++ invalidFinishProg := by
  unfold invalidPrepareProg invalidSearchProg invalidBumpProg
    invalidFinishProg invalidProg outerBranch func21
  rfl

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

def bidPriceProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 14,
  .localGet 2,
  .localSet 15,
  .localGet 3,
  .localSet 16,
  .constI64 0xFFFFFFFFFFFFFFFF,
  .localSet 17,
  .localGet 5,
  .localSet 18
]

def askPriceProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 14,
  .localGet 2,
  .localSet 15,
  .localGet 3,
  .localSet 16,
  .constI64 0,
  .localSet 17,
  .localGet 5,
  .localSet 18
]

def priceProg : Wasm.Program :=
  [
  .localGet 3,
  .constI64 0,
  .eqI64,
  .iff 0 1 [.constI64 1] [.constI64 0],
  .constI64 1,
  .eqI64,
  .iff 0 1 [.constI64 1] [.constI64 0],
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 bidPriceProg askPriceProg
]

def callProg : Wasm.Program :=
  [
  .constI64 0,
  .localSet 19,
  .localGet 0,
  .localSet 20,
  .localGet 14,
  .localSet 21,
  .localGet 15,
  .localSet 22,
  .localGet 16,
  .localSet 23,
  .localGet 17,
  .localSet 24,
  .localGet 18,
  .localSet 25,
  .localGet 19,
  .localGet 20,
  .localGet 21,
  .localGet 22,
  .localGet 23,
  .localGet 24,
  .localGet 25,
  .call 18
]

def validResultProg : Wasm.Program :=
  [
  .localSet 30,
  .localSet 29,
  .localSet 28,
  .localSet 27,
  .localSet 26,
  .localGet 27,
  .localSet 32,
  .localGet 29,
  .localSet 34,
  .call 19,
  .localSet 36,
  .localGet 36,
  .localSet 39,
  .localGet 32,
  .localSet 40,
  .localGet 34,
  .localSet 41
]

def validProg : Wasm.Program :=
  priceProg ++ callProg ++ validResultProg

def resultProg : Wasm.Program :=
  [.localGet 39, .localGet 40, .localGet 41]

set_option maxRecDepth 1048576 in
theorem func21_decomposition :
    func21 = entryProg ++ [.iff 0 0 validProg invalidProg] ++ resultProg := by
  unfold func21 entryProg validProg priceProg bidPriceProg askPriceProg
    callProg validResultProg invalidProg outerBranch resultProg
  rfl

end Project.ClobMarket.Entry
