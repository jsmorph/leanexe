import Verified.TreeCopyCode
import LeanExe.IR.Function

namespace Verified.Examples.TreeCopy

open Wasm LeanExe.Runtime

def binaryShape : TreeShape := ⟨[true, false, true], by decide, by decide⟩

def function (shape : TreeShape) (action : Nat) : Wasm.Function :=
  { params := [.i64], locals := List.replicate 7 .i64, results := [.i64]
    typeIdx := some 0
    body := treeCopyCode shape 0 1 ++ [.localSet 7] ++
      match action with
      | 0 => [.localGet 7]
      | 1 => [.localGet 0, .call 1, .localGet 7]
      | 2 => [.localGet 7, .call 1, .localGet 0]
      | _ => [.localGet 7, .call 1, .localGet 0, .call 1, .constI64 0] }

def entries : List (String × TreeShape × Nat) :=
  [("copyList", listShape, 0), ("takeList", listShape, 1),
   ("discardList", listShape, 2), ("releaseList", listShape, 3),
   ("copyTree", binaryShape, 0), ("takeTree", binaryShape, 1),
   ("discardTree", binaryShape, 2), ("releaseTree", binaryShape, 3)]

def module : Module :=
  let types := [LeanExe.IR.wordToWord, LeanExe.IR.wordToNone]
  { funcs := [allocFunction 0, releaseFunction 1] ++ entries.map fun (_, shape, action) =>
      function shape action
    exports := [{ name := "alloc", funcIdx := 0 }, { name := "release", funcIdx := 1 }] ++
      entries.mapIdx fun i entry => { name := entry.1, funcIdx := 2 + i }
    memory := some { pagesMin := 16, pagesMax := some 65535 }
    globals := LeanExe.IR.runtimeGlobals
    types
    gcTypes := types.map fun type => { comp := .func type }
    globalExports := [("allocCount", 2), ("freeCount", 3)]
    memoryExports := [("memory", 0)] }

end Verified.Examples.TreeCopy
