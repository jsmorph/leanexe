import Project.Compiler.ContainerEncoding
import Project.Compiler.ContainerParsing
import Project.Compiler.StructuredParsing

namespace Project.Compiler.Parsing

open Wasm.Binary

def i64Locals (count : Nat) : List LocalDecl :=
  [{ count := UInt32.ofNat count, type := .i64 }]

theorem val_i64 : Parses valType [126] .i64 := by
  unfold valType
  apply bind_parses (a := [126]) (b := []) (read_byte 126)
  exact pure_parses _

theorem local_decl (count : Nat) (bound : count < 2 ^ 32) :
    Parses localDecl (LeanExe.Wasm.Binary.u32leb count ++ [126])
      { count := UInt32.ofNat count, type := .i64 } := by
  unfold localDecl
  apply bind_parses (u32 count bound)
  exact map_parses val_i64 (fun type => ({ count := UInt32.ofNat count, type } : LocalDecl))

theorem local_vector (count : Nat) (bound : count < 2 ^ 32) :
    Parses (Wasm.Binary.vector localDecl)
      (LeanExe.Wasm.Binary.u32leb 1 ++ (LeanExe.Wasm.Binary.u32leb count ++ [126]))
      (i64Locals count) := by
  have hp := vector (List.Forall₂.cons (local_decl count bound) List.Forall₂.nil)
    (by simp) (by simp)
  simpa only [List.length_cons, List.length_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, i64Locals] using hp

theorem function_body {func : LeanExe.IR.Func} {raw : List Wasm.Binary.Instr}
    (releaseIndex : Nat)
    (encoded : ArithmeticEncoding.ProgramEncoding
      (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex func) raw)
    (positive : 0 < func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func)
    (localBound : func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func < 2 ^ 32)
    (bodyBound : (LeanExe.Wasm.Binary.CoreWasm.localDecls func ++
      LeanExe.Wasm.Binary.CoreWasm.encodeInstrs
        (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex func) ++ [11]).length < 2 ^ 32) :
    Parses Wasm.Binary.code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody releaseIndex func)
      { locals := i64Locals (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func)
        body := raw } := by
  unfold LeanExe.Wasm.Binary.CoreWasm.emitFuncBody LeanExe.Wasm.Binary.body Wasm.Binary.code
  rw [ContainerEncoding.byte_vector]
  apply sized (bound := bodyBound)
  have localsParsed : Parses (Wasm.Binary.vector localDecl)
      (LeanExe.Wasm.Binary.CoreWasm.localDecls func)
      (i64Locals (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func)) := by
    have nonzero : (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func == 0) = false := by
      exact beq_eq_false_iff_ne.mpr (Nat.ne_of_gt positive)
    simpa [LeanExe.Wasm.Binary.CoreWasm.localDecls, nonzero, Bool.false_eq_true,
      ite_false, LeanExe.Wasm.Binary.ofNats, List.map_cons, List.map_nil,
      LeanExe.Wasm.Binary.byte, List.append_assoc] using local_vector _ localBound
  unfold codeBody
  simpa only [List.append_assoc] using
    (bind_parses (q := fun locals => do
      let body ← expression
      pure ({ locals, body } : Code)) localsParsed
      (map_parses encoded.expression_parses (fun body =>
        ({ locals := i64Locals (func.locals - func.params + LeanExe.Wasm.Binary.CoreWasm.funcScratch func), body } : Code))))

end Project.Compiler.Parsing
