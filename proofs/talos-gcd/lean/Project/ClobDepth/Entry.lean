import Project.ClobDepth.Program

/-!
# Depth level-update decomposition

Function 3 scans for the first matching price, then allocates either an
appended array or a same-length replacement array.  These definitions isolate
the scan, allocation, copy, and final-store regions for separate proofs.
-/

namespace Project.ClobDepth.Entry

open Wasm Project.ClobDepth

private def branchAt (program : Wasm.Program) (index : Nat)
    (takeThen : Bool) : Wasm.Program :=
  match (program[index]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ thenProg elseProg) =>
      if takeThen then thenProg else elseProg
  | _ => []

def scanProg : Wasm.Program :=
  func3.take 20

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
  missingProg.take 44

def missingSearchProg : Wasm.Program :=
  (missingProg.drop 44).take 1

def missingBumpProg : Wasm.Program :=
  (missingProg.drop 45).take 4

def missingAllocFinishProg : Wasm.Program :=
  (missingProg.drop 49).take 12

def missingCopyProg : Wasm.Program :=
  (missingProg.drop 61).take 1

def missingStoreProg : Wasm.Program :=
  missingProg.drop 62

set_option maxRecDepth 1048576 in
theorem missingProg_decomposition :
    missingProg = missingPrepareProg ++ missingSearchProg ++
      missingBumpProg ++ missingAllocFinishProg ++ missingCopyProg ++
      missingStoreProg := by
  unfold missingPrepareProg missingSearchProg missingBumpProg
    missingAllocFinishProg missingCopyProg missingStoreProg missingProg
    branchAt func3
  rfl

def foundPrepareProg : Wasm.Program :=
  foundProg.take 38

def foundAllocProg : Wasm.Program :=
  branchAt foundProg 38 true

def foundResultProg : Wasm.Program :=
  foundProg.drop 39

set_option maxRecDepth 1048576 in
theorem foundProg_decomposition :
    foundProg = foundPrepareProg ++
      [.iff 0 1 foundAllocProg [.unreachable]] ++ foundResultProg := by
  unfold foundPrepareProg foundAllocProg foundResultProg foundProg
    branchAt func3
  rfl

def foundAllocPrepareProg : Wasm.Program :=
  foundAllocProg.take 28

def foundSearchProg : Wasm.Program :=
  (foundAllocProg.drop 28).take 1

def foundBumpProg : Wasm.Program :=
  (foundAllocProg.drop 29).take 4

def foundAllocFinishProg : Wasm.Program :=
  (foundAllocProg.drop 33).take 12

def foundCopyProg : Wasm.Program :=
  (foundAllocProg.drop 45).take 1

def foundStoreProg : Wasm.Program :=
  foundAllocProg.drop 46

set_option maxRecDepth 1048576 in
theorem foundAllocProg_decomposition :
    foundAllocProg = foundAllocPrepareProg ++ foundSearchProg ++
      foundBumpProg ++ foundAllocFinishProg ++ foundCopyProg ++
      foundStoreProg := by
  unfold foundAllocPrepareProg foundSearchProg foundBumpProg
    foundAllocFinishProg foundCopyProg foundStoreProg foundAllocProg
    foundProg branchAt func3
  rfl

end Project.ClobDepth.Entry
