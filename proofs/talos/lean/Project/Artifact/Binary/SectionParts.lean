import Project.Artifact.Binary.ModuleParts

namespace Wasm.Binary
open Parser

theorem parseSection_type_eq {before : RawModule} {start finish : Cursor} {values : List FuncType}
    (h : sized (vector funcType) start = .ok (values, finish)) :
    parseSection .type before start = .ok ({ before with types := values }, finish) := by
  simp only [parseSection, Bind.bind, Pure.pure, Except.bind, h]

theorem parseSection_function_eq {before : RawModule} {start finish : Cursor} {values : List UInt32}
    (h : sized (vector Leb.u32) start = .ok (values, finish)) :
    parseSection .function before start = .ok ({ before with functionTypeIndices := values }, finish) := by
  simp only [parseSection, Bind.bind, Pure.pure, Except.bind, h]

theorem parseSection_memory_eq {before : RawModule} {start finish : Cursor} {values : List MemoryType}
    (h : sized (vector memoryType) start = .ok (values, finish)) :
    parseSection .memory before start = .ok ({ before with memories := values }, finish) := by
  simp only [parseSection, Bind.bind, Pure.pure, Except.bind, h]

theorem parseSection_global_eq {before : RawModule} {start finish : Cursor} {values : List Global}
    (h : sized (vector global) start = .ok (values, finish)) :
    parseSection .global before start = .ok ({ before with globals := values }, finish) := by
  simp only [parseSection, Bind.bind, Pure.pure, Except.bind, h]

theorem parseSection_export_eq {before : RawModule} {start finish : Cursor} {values : List Export}
    (h : sized (vector exportEntry) start = .ok (values, finish)) :
    parseSection .export before start = .ok ({ before with exports := values }, finish) := by
  simp only [parseSection, Bind.bind, Pure.pure, Except.bind, h]

theorem parseSection_code_eq {before : RawModule} {start finish : Cursor} {values : List Code}
    (h : sized (vector code) start = .ok (values, finish)) :
    parseSection .code before start = .ok ({ before with codes := values }, finish) := by
  simp only [parseSection, Bind.bind, Pure.pure, Except.bind, h]

#print axioms parseSection_type_eq
#print axioms parseSection_function_eq
#print axioms parseSection_memory_eq
#print axioms parseSection_global_eq
#print axioms parseSection_export_eq
#print axioms parseSection_code_eq

end Wasm.Binary
