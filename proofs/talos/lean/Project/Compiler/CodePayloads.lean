import LeanExe.Wasm.ArithmeticBounds
import Project.Compiler.PayloadVectors
import Project.Compiler.RuntimeFunctionParsing

namespace Project.Compiler.ArithmeticModule

open Project.Compiler.Parsing
open Wasm.Binary

abbrev codeItems (func : LeanExe.IR.Func) : List (List UInt8) :=
  LeanExe.Wasm.ArithmeticBounds.codeItems func

abbrev codePayload (func : LeanExe.IR.Func) : List UInt8 :=
  LeanExe.Wasm.ArithmeticBounds.codePayload func

def codeValues (user : Code) : List Code :=
  [user, RuntimeEncoding.allocCode, RuntimeEncoding.resetCode,
   RuntimeEncoding.retainCode, RuntimeEncoding.releaseCode]

theorem body_nonempty (locals instrs : List UInt8) :
    0 < (LeanExe.Wasm.Binary.body locals instrs).length := by
  unfold LeanExe.Wasm.Binary.body
  rw [ContainerEncoding.byte_vector, List.length_append]
  have h := unsigned_nonempty (locals ++ instrs ++ LeanExe.Wasm.Binary.ofNats [11]).length
  omega

theorem codes_parsed (func : LeanExe.IR.Func) (raw : Code)
    (userParsed : Parses code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func) raw) :
    Parses (Wasm.Binary.vector code) (codePayload func) (codeValues raw) := by
  apply encoded_vector (.cons userParsed (.cons RuntimeEncoding.alloc_body
    (.cons RuntimeEncoding.reset_body (.cons RuntimeEncoding.retain_body
      (.cons RuntimeEncoding.release_body .nil)))))
  · intro bs member
    simp only [codeItems, LeanExe.Wasm.ArithmeticBounds.codeItems, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact body_nonempty _ _
  · change 5 < 2 ^ 32
    decide

theorem code_section (func : LeanExe.IR.Func) :
    LeanExe.Wasm.Binary.CoreWasm.codeSection { funcs := #[func] } =
      LeanExe.Wasm.Binary.wasmSection 10 (codePayload func) := rfl

end Project.Compiler.ArithmeticModule
