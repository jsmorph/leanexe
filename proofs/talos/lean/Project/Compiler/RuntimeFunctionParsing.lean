import Project.Compiler.RuntimeBodies
import Project.Compiler.FunctionParsing

namespace Project.Compiler.RuntimeEncoding

open Project.Compiler.Parsing
open LeanExe.Wasm.Binary.CoreWasm

/-- The production runtime's complete body container, including the declared
locals and length prefix, decoded by the existing binary parser. -/
theorem body_parses {localBytes : List UInt8} {locals : List Wasm.Binary.LocalDecl}
    {source : List LeanExe.Wasm.Instr} {raw : List Wasm.Binary.Instr}
    (localParsed : Parses (Wasm.Binary.vector Wasm.Binary.localDecl) localBytes locals)
    (encoded : RuntimeProgram source raw)
    (bound : (localBytes ++ encodeInstrs source ++ [11]).length < 2 ^ 32) :
    Parses Wasm.Binary.code (bodyI localBytes source) { locals, body := raw } := by
  unfold bodyI LeanExe.Wasm.Binary.body Wasm.Binary.code
  rw [Project.Compiler.ContainerEncoding.byte_vector]
  apply sized (bound := bound)
  unfold Wasm.Binary.codeBody
  simpa only [List.append_assoc] using
    bind_parses (q := fun locals => do
      let body ← Wasm.Binary.expression
      pure ({ locals, body } : Wasm.Binary.Code)) localParsed
      (map_parses encoded.expression_parses (fun body => ({ locals, body } : Wasm.Binary.Code)))

theorem no_locals : Parses (Wasm.Binary.vector Wasm.Binary.localDecl) [0] [] := by
  have h := vector (List.Forall₂.nil (R := Parses Wasm.Binary.localDecl)) (by decide) (by decide)
  simpa [LeanExe.Wasm.Binary.u32leb, Project.Compiler.byteArray_toList,
    LeanExe.Wasm.Leb.u32lebU64_eq_lebList, LeanExe.Wasm.Leb.lebList] using h

theorem locals_one : Parses (Wasm.Binary.vector Wasm.Binary.localDecl) [1, 1, 126] (i64Locals 1) := by
  simpa [LeanExe.Wasm.Binary.u32leb, Project.Compiler.byteArray_toList,
    LeanExe.Wasm.Leb.u32lebU64_eq_lebList, LeanExe.Wasm.Leb.lebList] using local_vector 1 (by decide)

theorem locals_six : Parses (Wasm.Binary.vector Wasm.Binary.localDecl) [1, 6, 126] (i64Locals 6) := by
  simpa [LeanExe.Wasm.Binary.u32leb, Project.Compiler.byteArray_toList,
    LeanExe.Wasm.Leb.u32lebU64_eq_lebList, LeanExe.Wasm.Leb.lebList] using local_vector 6 (by decide)

theorem locals_eight : Parses (Wasm.Binary.vector Wasm.Binary.localDecl) [1, 8, 126] (i64Locals 8) := by
  simpa [LeanExe.Wasm.Binary.u32leb, Project.Compiler.byteArray_toList,
    LeanExe.Wasm.Leb.u32lebU64_eq_lebList, LeanExe.Wasm.Leb.lebList] using local_vector 8 (by decide)

def allocCode : Wasm.Binary.Code := { locals := i64Locals 6, body := allocEncoding.val }
def resetCode : Wasm.Binary.Code := { locals := [], body := resetEncoding.val }
def retainCode : Wasm.Binary.Code := { locals := i64Locals 1, body := retainEncoding.val }
def releaseCode : Wasm.Binary.Code := { locals := i64Locals 8, body := releaseEncoding.val }

theorem alloc_body (bound : (encodeInstrs coreAllocInstrs).length + 4 < 2 ^ 32) :
    Parses Wasm.Binary.code coreAllocBody allocCode := by
  exact body_parses locals_six allocEncoding.property (by simp only [LeanExe.Wasm.Binary.ofNats, List.length_append, List.length_map, List.length_cons, List.length_nil]; omega)

theorem reset_body (bound : (encodeInstrs coreResetInstrs).length + 2 < 2 ^ 32) :
    Parses Wasm.Binary.code coreResetBody resetCode := by
  exact body_parses no_locals resetEncoding.property (by simp only [LeanExe.Wasm.Binary.ofNats, List.length_append, List.length_map, List.length_cons, List.length_nil]; omega)

theorem retain_body (bound : (encodeInstrs coreRetainInstrs).length + 4 < 2 ^ 32) :
    Parses Wasm.Binary.code coreRetainBody retainCode := by
  exact body_parses locals_one retainEncoding.property (by simp only [LeanExe.Wasm.Binary.ofNats, List.length_append, List.length_map, List.length_cons, List.length_nil]; omega)

theorem release_body (bound : (encodeInstrs (coreReleaseInstrs 4)).length + 4 < 2 ^ 32) :
    Parses Wasm.Binary.code (coreReleaseBody 4) releaseCode := by
  exact body_parses locals_eight releaseEncoding.property (by simp only [LeanExe.Wasm.Binary.ofNats, List.length_append, List.length_map, List.length_cons, List.length_nil]; omega)

end Project.Compiler.RuntimeEncoding
