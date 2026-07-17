import Project.ClobDepth.Program

/-!
# Depth level-update decomposition

Function 3 scans for the first matching price, then allocates either an
appended array or a same-length replacement array.  These definitions isolate
the scan, allocation, copy, and final-store regions for separate proofs.
-/

namespace Project.ClobDepth.Entry

open Wasm Project.ClobDepth

def branchAt (program : Wasm.Program) (index : Nat)
    (takeThen : Bool) : Wasm.Program :=
  match (program[index]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ thenProg elseProg) =>
      if takeThen then thenProg else elseProg
  | _ => []

def scanProg : Wasm.Program :=
  func3.take 20

def scanPrepareProg : Wasm.Program :=
  scanProg.take 10

def scanLoopProg : Wasm.Program :=
  (scanProg.drop 10).take 1

def scanFinishProg : Wasm.Program :=
  scanProg.drop 11

set_option maxRecDepth 1048576 in
theorem scanProg_decomposition :
    scanProg = scanPrepareProg ++ scanLoopProg ++ scanFinishProg := by
  unfold scanPrepareProg scanLoopProg scanFinishProg scanProg func3
  rfl

def missingProg : Wasm.Program :=
  branchAt func3 20 true

def foundProg : Wasm.Program :=
  branchAt func3 20 false

def resultProg : Wasm.Program :=
  func3.drop 21

set_option maxRecDepth 1048576 in
theorem func3_decomposition :
    func3 = scanProg ++ [.iff 0 0 missingProg foundProg] ++ resultProg := by
  unfold scanProg missingProg foundProg resultProg branchAt func3
  rfl

def missingPrepareProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 7,
  .localGet 7,
  .localSet 14,
  .localGet 2,
  .localSet 20,
  .localGet 3,
  .localSet 21,
  .localGet 14,
  .wrapI64,
  .load64 0,
  .localSet 15,
  .localGet 15,
  .constI64 2,
  .mulI64,
  .localSet 16,
  .localGet 15,
  .constI64 1,
  .addI64,
  .localSet 17,
  .constI64 8,
  .localGet 17,
  .constI64 2,
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
  .localSet 24,
  .localGet 24,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [.constI64 8, .localSet 24] [],
  .constI64 0,
  .localSet 29,
  .constI64 0,
  .localSet 25,
  .globalGet 1,
  .localSet 26
]

def missingFieldsProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 7,
  .localGet 7,
  .localSet 14,
  .localGet 2,
  .localSet 20,
  .localGet 3,
  .localSet 21,
  .localGet 14,
  .wrapI64,
  .load64 0,
  .localSet 15,
  .localGet 15,
  .constI64 2,
  .mulI64,
  .localSet 16,
  .localGet 15,
  .constI64 1,
  .addI64,
  .localSet 17
]

def missingAllocPrepareProg : Wasm.Program :=
  [
  .constI64 8,
  .localGet 17,
  .constI64 2,
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
  .localSet 24,
  .localGet 24,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [.constI64 8, .localSet 24] [],
  .constI64 0,
  .localSet 29,
  .constI64 0,
  .localSet 25,
  .globalGet 1,
  .localSet 26
]

theorem missingPrepareProg_decomposition :
    missingPrepareProg = missingFieldsProg ++ missingAllocPrepareProg := by
  rfl

def missingSearchBodyProg : Wasm.Program :=
  [
  .localGet 26,
  .constI64 0,
  .eqI64,
  .br_if 1,
  .localGet 29,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 26,
  .constI64 32,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 27,
  .localGet 26,
  .constI64 8,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 28,
  .localGet 27,
  .localGet 24,
  .geUI64,
  .iff 0 0 [
    .localGet 25,
    .constI64 0,
    .eqI64,
    .iff 0 0 [
      .localGet 28,
      .globalSet 1
    ] [
      .localGet 25,
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet 28,
      .store64 0
    ],
    .localGet 26,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 26,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 26,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 27,
    .store64 0,
    .localGet 26,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 26,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 26,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0,
    .localGet 26,
    .localSet 29
  ] [
    .localGet 26,
    .localSet 25,
    .localGet 28,
    .localSet 26
  ],
  .br 0
]

def missingSearchProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 missingSearchBodyProg]]

def missingBumpBranchProg : Wasm.Program :=
  [
  .globalGet 0,
  .constI64 48,
  .addI64,
  .localGet 24,
  .addI64,
  .localSet 27,
  .localGet 27,
  .globalGet 0,
  .ltUI64,
  .iff 0 0 [.unreachable] [],
  .localGet 27,
  .constI64 1,
  .subI64,
  .constI64 65536,
  .divUI64,
  .constI64 1,
  .addI64,
  .localSet 28,
  .memorySize,
  .extendUI32,
  .localGet 28,
  .ltUI64,
  .iff 0 0 [
    .localGet 28,
    .memorySize,
    .extendUI32,
    .subI64,
    .wrapI64,
    .memoryGrow,
    .const 4294967295,
    .eq,
    .iff 0 0 [.unreachable] []
  ] [],
  .globalGet 0,
  .constI64 48,
  .addI64,
  .localSet 29,
  .localGet 27,
  .globalSet 0,
  .localGet 29,
  .constI64 48,
  .subI64,
  .wrapI64,
  .constI64 5501223100278326855,
  .store64 0,
  .localGet 29,
  .constI64 40,
  .subI64,
  .wrapI64,
  .constI64 1,
  .store64 0,
  .localGet 29,
  .constI64 32,
  .subI64,
  .wrapI64,
  .localGet 24,
  .store64 0,
  .localGet 29,
  .constI64 24,
  .subI64,
  .wrapI64,
  .constI64 2,
  .store64 0,
  .localGet 29,
  .constI64 16,
  .subI64,
  .wrapI64,
  .constI64 2,
  .store64 0,
  .localGet 29,
  .constI64 8,
  .subI64,
  .wrapI64,
  .constI64 0,
  .store64 0
]

def missingBumpProg : Wasm.Program :=
  [
  .localGet 29,
  .constI64 0,
  .eqI64,
  .iff 0 0 missingBumpBranchProg []
]

def missingAllocFinishProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 29,
  .localSet 18,
  .localGet 18,
  .wrapI64,
  .localGet 17,
  .store64 0,
  .constI64 0,
  .localSet 19
]

def missingCopyBodyProg : Wasm.Program :=
  [
  .localGet 19,
  .localGet 16,
  .geUI64,
  .br_if 1,
  .localGet 18,
  .localGet 19,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 14,
  .localGet 19,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet 19,
  .constI64 1,
  .addI64,
  .localSet 19,
  .br 0
]

def missingCopyProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 missingCopyBodyProg]]

def missingStoreProg : Wasm.Program :=
  [
  .localGet 18,
  .localGet 15,
  .constI64 2,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 20,
  .store64 0,
  .localGet 18,
  .localGet 15,
  .constI64 2,
  .mulI64,
  .constI64 2,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 21,
  .store64 0,
  .localGet 18,
  .localSet 8,
  .localGet 8,
  .localSet 12,
  .localGet 8,
  .localSet 13
]

set_option maxRecDepth 1048576 in
theorem missingProg_decomposition :
    missingProg = missingPrepareProg ++ missingSearchProg ++
      missingBumpProg ++ missingAllocFinishProg ++ missingCopyProg ++
      missingStoreProg := by
  unfold missingPrepareProg missingSearchProg missingSearchBodyProg
    missingBumpProg missingBumpBranchProg
    missingAllocFinishProg missingCopyProg missingCopyBodyProg
    missingStoreProg missingProg branchAt func3
  rfl

def foundPrepareProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 9,
  .localGet 6,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 6,
    .localSet 14,
    .constI64 1,
    .localSet 15,
    .localGet 14,
    .localGet 15,
    .ltUI64,
    .iff 0 1 [.constI64 0] [
      .localGet 14,
      .localGet 15,
      .subI64
    ]
  ] [.constI64 0],
  .localSet 10,
  .localGet 9,
  .localSet 14,
  .localGet 10,
  .localSet 15,
  .localGet 2,
  .localSet 20,
  .localGet 1,
  .localSet 24,
  .localGet 6,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 1 [
    .localGet 6,
    .localSet 26,
    .constI64 1,
    .localSet 27,
    .localGet 26,
    .localGet 27,
    .ltUI64,
    .iff 0 1 [.constI64 0] [
      .localGet 26,
      .localGet 27,
      .subI64
    ]
  ] [.constI64 0],
  .localSet 25,
  .localGet 25,
  .localGet 24,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 24,
    .localGet 25,
    .constI64 2,
    .mulI64,
    .constI64 2,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [.unreachable],
  .localGet 3,
  .addI64,
  .localSet 21,
  .localGet 14,
  .wrapI64,
  .load64 0,
  .localSet 16,
  .localGet 15,
  .localGet 16,
  .ltUI64
]

def foundAllocProg : Wasm.Program :=
  branchAt foundProg 38 true

def foundResultProg : Wasm.Program :=
  [
  .localSet 11,
  .localGet 11,
  .localSet 12,
  .localGet 11,
  .localSet 13
]

set_option maxRecDepth 1048576 in
theorem foundProg_decomposition :
    foundProg = foundPrepareProg ++
      [.iff 0 1 foundAllocProg [.unreachable]] ++ foundResultProg := by
  unfold foundPrepareProg foundAllocProg foundResultProg foundProg
    branchAt func3
  rfl

def foundAllocPrepareProg : Wasm.Program :=
  [
  .localGet 16,
  .constI64 2,
  .mulI64,
  .localSet 17,
  .constI64 8,
  .localGet 16,
  .constI64 2,
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
  .localSet 24,
  .localGet 24,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [.constI64 8, .localSet 24] [],
  .constI64 0,
  .localSet 29,
  .constI64 0,
  .localSet 25,
  .globalGet 1,
  .localSet 26
]

def foundSearchProg : Wasm.Program :=
  missingSearchProg

def foundBumpProg : Wasm.Program :=
  missingBumpProg

def foundAllocFinishProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 29,
  .localSet 18,
  .localGet 18,
  .wrapI64,
  .localGet 16,
  .store64 0,
  .constI64 0,
  .localSet 19
]

def foundCopyBodyProg : Wasm.Program :=
  [
  .localGet 19,
  .localGet 17,
  .geUI64,
  .br_if 1,
  .localGet 18,
  .localGet 19,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 14,
  .localGet 19,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet 19,
  .constI64 1,
  .addI64,
  .localSet 19,
  .br 0
]

def foundCopyProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 foundCopyBodyProg]]

def foundStoreProg : Wasm.Program :=
  [
  .localGet 18,
  .localGet 15,
  .constI64 2,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 20,
  .store64 0,
  .localGet 18,
  .localGet 15,
  .constI64 2,
  .mulI64,
  .constI64 2,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 21,
  .store64 0,
  .localGet 18
]

set_option maxRecDepth 1048576 in
theorem foundAllocProg_decomposition :
    foundAllocProg = foundAllocPrepareProg ++ foundSearchProg ++
      foundBumpProg ++ foundAllocFinishProg ++ foundCopyProg ++
      foundStoreProg := by
  unfold foundAllocPrepareProg foundSearchProg foundBumpProg
    foundAllocFinishProg foundCopyProg foundCopyBodyProg foundStoreProg
    missingSearchProg missingSearchBodyProg missingBumpProg
    missingBumpBranchProg foundAllocProg foundProg branchAt func3
  rfl

end Project.ClobDepth.Entry
