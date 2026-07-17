import Project.ClobLimit.RunMatchEmptyAlloc

/-!
# `runMatch` entry decomposition

Function 18 reads the book length, prepares the internal matcher arguments,
allocates two empty trade arrays, and calls function 17.  The decomposition
identifies both allocation regions with the one proved instruction block.
-/

namespace Project.ClobLimit.RunMatchEntry

open Wasm Project.ClobLimit

def prepareProg : Wasm.Program :=
  [
  .localGet 1,
  .localSet 32,
  .localGet 32,
  .wrapI64,
  .load64 0,
  .localSet 29,
  .constI64 1,
  .localSet 30,
  .localGet 29,
  .localGet 30,
  .addI64,
  .localSet 31,
  .localGet 31,
  .localGet 29,
  .ltUI64,
  .iff 0 1 [
    .unreachable
  ] [
    .localGet 31
  ],
  .localSet 7,
  .localGet 2,
  .localSet 8,
  .localGet 3,
  .localSet 9,
  .localGet 4,
  .localSet 10,
  .localGet 5,
  .localSet 11,
  .localGet 6,
  .localSet 12,
  .localGet 0,
  .localSet 14,
  .localGet 1,
  .localSet 15
]

def firstAllocResultProg : Wasm.Program :=
  [
  .localGet 13,
  .localSet 16
]

def secondAllocResultProg : Wasm.Program :=
  [
  .localGet 13,
  .localSet 17,
  .localGet 6,
  .localSet 18
]

def callProg : Wasm.Program :=
  [
  .localGet 7,
  .localGet 8,
  .localGet 9,
  .localGet 10,
  .localGet 11,
  .localGet 12,
  .localGet 14,
  .localGet 15,
  .localGet 16,
  .localGet 17,
  .localGet 18,
  .call 17
]

def resultProg : Wasm.Program :=
  [
  .localSet 23,
  .localSet 22,
  .localSet 21,
  .localSet 20,
  .localSet 19,
  .localGet 19,
  .localSet 24,
  .localGet 20,
  .localSet 25,
  .localGet 21,
  .localSet 26,
  .localGet 22,
  .localSet 27,
  .localGet 23,
  .localSet 28,
  .localGet 24,
  .localGet 25,
  .localGet 26,
  .localGet 27,
  .localGet 28
]

set_option maxRecDepth 1048576 in
theorem func18_decomposition :
    func18 = prepareProg ++ RunMatchEmptyAlloc.allocProg ++
      firstAllocResultProg ++ RunMatchEmptyAlloc.allocProg ++
      secondAllocResultProg ++ callProg ++ resultProg := by
  unfold func18 prepareProg RunMatchEmptyAlloc.allocProg
    RunMatchEmptyAlloc.prepareProg RunMatchEmptyAlloc.searchProg
    RunMatchEmptyAlloc.searchBodyProg RunMatchEmptyAlloc.bumpProg
    RunMatchEmptyAlloc.finishProg firstAllocResultProg secondAllocResultProg
    callProg resultProg
  simp only [List.cons_append, List.nil_append]

end Project.ClobLimit.RunMatchEntry
