import Project.Compiler.ModuleParsing

namespace Project.Compiler.Parsing

open Wasm.Binary

private theorem section_node (fuel lastRank : Nat) (id : SectionId)
    (initial middle result : RawModule) (payload rest : List UInt8)
    (fresh : id ∉ initial.sections) (ordered : lastRank < id.rank)
    (headParsed : Parses (parseSection id initial)
      (LeanExe.Wasm.Binary.u32leb payload.length ++ payload) middle)
    (tailParsed : ParsesEnd (sectionLoop fuel id.rank
      { middle with sections := middle.sections ++ [id] }) rest result) :
    ParsesEnd (sectionLoop (fuel + 1) lastRank initial)
      (LeanExe.Wasm.Binary.wasmSection id.byte.toNat payload ++ rest) result := by
  have h := sections_cons fuel lastRank id initial middle result
    (LeanExe.Wasm.Binary.u32leb payload.length ++ payload) rest fresh ordered headParsed tailParsed
  simpa [ContainerEncoding.section_bytes, List.append_assoc] using h

/-- Six payloads in the exact order emitted by the production library compiler.
The hypotheses describe only payload parsing and binary-format length limits. -/
structure ModulePayloads where
  typeBytes : List UInt8
  functionBytes : List UInt8
  memoryBytes : List UInt8
  globalBytes : List UInt8
  exportBytes : List UInt8
  codeBytes : List UInt8
  types : List FuncType
  functions : List UInt32
  memories : List MemoryType
  globals : List Global
  exports : List Export
  codes : List Code
  typesParsed : Parses (Wasm.Binary.vector funcType) typeBytes types
  functionsParsed : Parses (Wasm.Binary.vector Leb.u32) functionBytes functions
  memoriesParsed : Parses (Wasm.Binary.vector memoryType) memoryBytes memories
  globalsParsed : Parses (Wasm.Binary.vector global) globalBytes globals
  exportsParsed : Parses (Wasm.Binary.vector exportEntry) exportBytes exports
  codesParsed : Parses (Wasm.Binary.vector code) codeBytes codes
  typeBound : typeBytes.length < 2 ^ 32
  functionBound : functionBytes.length < 2 ^ 32
  memoryBound : memoryBytes.length < 2 ^ 32
  globalBound : globalBytes.length < 2 ^ 32
  exportBound : exportBytes.length < 2 ^ 32
  codeBound : codeBytes.length < 2 ^ 32

def ModulePayloads.bytes (p : ModulePayloads) : List UInt8 :=
  LeanExe.Wasm.Binary.wasmSection 1 p.typeBytes ++
  (LeanExe.Wasm.Binary.wasmSection 3 p.functionBytes ++
  (LeanExe.Wasm.Binary.wasmSection 5 p.memoryBytes ++
  (LeanExe.Wasm.Binary.wasmSection 6 p.globalBytes ++
  (LeanExe.Wasm.Binary.wasmSection 7 p.exportBytes ++
   LeanExe.Wasm.Binary.wasmSection 10 p.codeBytes))))

def ModulePayloads.raw (p : ModulePayloads) : RawModule :=
  { sections := [.type, .function, .memory, .global, .export, .code]
    types := p.types, functionTypeIndices := p.functions, memories := p.memories
    globals := p.globals, exports := p.exports, codes := p.codes }

theorem ModulePayloads.sections (p : ModulePayloads) (fuel : Nat) :
    ParsesEnd (sectionLoop (fuel + 6) 0 default) p.bytes p.raw := by
  unfold ModulePayloads.bytes
  apply section_node (fuel + 5) 0 .type
  · (try dsimp); decide
  · (try dsimp); decide
  · exact map_parses (sized p.typesParsed p.typeBound) (fun types => { (default : RawModule) with types })
  apply section_node (fuel + 4) 1 .function
  · (try dsimp); decide
  · (try dsimp); decide
  · exact map_parses (sized p.functionsParsed p.functionBound) (fun indices =>
      { (default : RawModule) with
        types := p.types, sections := [.type], functionTypeIndices := indices })
  apply section_node (fuel + 3) 2 .memory
  · (try dsimp); decide
  · (try dsimp); decide
  · exact map_parses (sized p.memoriesParsed p.memoryBound) (fun memories =>
      { (default : RawModule) with
        types := p.types, functionTypeIndices := p.functions,
        sections := [.type, .function], memories })
  apply section_node (fuel + 2) 3 .global
  · (try dsimp); decide
  · (try dsimp); decide
  · exact map_parses (sized p.globalsParsed p.globalBound) (fun globals =>
      { (default : RawModule) with
        types := p.types, functionTypeIndices := p.functions,
        memories := p.memories, sections := [.type, .function, .memory], globals })
  apply section_node (fuel + 1) 4 .export
  · (try dsimp); decide
  · (try dsimp); decide
  · exact map_parses (sized p.exportsParsed p.exportBound) (fun exports =>
      { (default : RawModule) with
        types := p.types, functionTypeIndices := p.functions,
        memories := p.memories, globals := p.globals,
        sections := [.type, .function, .memory, .global], exports })
  have finish : ParsesEnd (sectionLoop fuel 6 p.raw) [] p.raw := sections_end fuel 6 p.raw
  have last := section_node fuel 5 .code
    { (default : RawModule) with
        types := p.types, functionTypeIndices := p.functions,
        memories := p.memories, globals := p.globals, exports := p.exports,
        sections := [.type, .function, .memory, .global, .export] }
    { p.raw with sections := [.type, .function, .memory, .global, .export] }
    p.raw p.codeBytes [] (by (try dsimp); decide) (by decide)
    (map_parses (sized p.codesParsed p.codeBound) (fun codes =>
      ({ p.raw with sections := [.type, .function, .memory, .global, .export], codes } : RawModule))) finish
  simpa [SectionId.rank, SectionId.byte, ModulePayloads.raw] using last

theorem ModulePayloads.decode (p : ModulePayloads) :
    Wasm.Binary.decode (ByteArray.mk ([0, 97, 115, 109, 1, 0, 0, 0] ++ p.bytes).toArray) = .ok p.raw := by
  have enough : 6 ≤ p.bytes.length := by
    simp only [ModulePayloads.bytes, ContainerEncoding.section_bytes,
      List.length_append, List.length_cons, List.length_nil]
    omega
  have parsed := p.sections (p.bytes.length - 6)
  rw [Nat.sub_add_cancel enough] at parsed
  exact (module_end p.bytes p.raw parsed).runAll

end Project.Compiler.Parsing
