import Project.Artifact.Binary.Translate
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

/-!
A separate exact-binary profile for the section layout emitted by ByteIO.
The existing import-free artifact profile and its frozen packages retain
their grammar. This profile reuses its proved instruction decoder and type
validator, and adds function imports in the unified function index space.
Every required section occurs once, in order, and consumes its full payload.
-/
namespace Project.ByteIO.Binary
open Wasm.Binary Wasm.Binary.Parser

structure Import where
  moduleName : Name
  fieldName : Name
  typeIndex : UInt32
  deriving Repr, Inhabited, BEq

structure Raw where
  core : RawModule
  imports : List Import
  deriving Repr, Inhabited, BEq

def importEntry : Parser Import := do
  let moduleName ← name
  let fieldName ← name
  expectByte 0
  let typeIndex ← Leb.u32
  pure { moduleName, fieldName, typeIndex }

def parseSection (id : UInt8) (entry : Parser α) : Parser (List α) := do
  expectByte id
  sized (vector entry)

def moduleParser : Parser Raw := do
  expectBytes [0, 97, 115, 109, 1, 0, 0, 0]
  let types ← parseSection 1 funcType
  let imports ← parseSection 2 importEntry
  let functionTypeIndices ← parseSection 3 Leb.u32
  let memories ← parseSection 5 memoryType
  let globals ← parseSection 6 global
  let exports ← parseSection 7 exportEntry
  let codes ← parseSection 10 code
  pure { core := {
    sections := [.type, .function, .memory, .global, .export, .code]
    types, functionTypeIndices, memories, globals, exports, codes }, imports }

def decode (bytes : ByteArray) : Except Error Raw := runAll moduleParser bytes

def Raw.importTypeIndices (raw : Raw) : List UInt32 := raw.imports.map (·.typeIndex)

/-- Export indices include the imports; code bodies correspond only to the
locally defined functions. Keeping these two index spaces separate prevents
an import from being mistaken for the first local function. -/
def Raw.exportContext (raw : Raw) : RawModule :=
  { raw.core with functionTypeIndices := raw.importTypeIndices ++ raw.core.functionTypeIndices }

def validate (raw : Raw) : Except ValidationError Unit := do
  Validator.validateSections raw.core
  if raw.core.memories.length = 1 then
    Validator.validateLimits raw.core.memories.head!.limits
  else
    Validator.moduleFailure (.memoryCount raw.core.memories.length)
  Validator.validateGlobals raw.core.globals
  Validator.validateExports raw.exportContext
  let imported ← Validator.resolveTypes raw.core.types raw.importTypeIndices
  let defined ← Validator.resolveFunctionTypes raw.core
  Validator.validateFunctionPairs raw.core (imported ++ defined) raw.imports.length
    defined raw.core.codes

def Raw.toTalos (raw : Raw) : Wasm.Module :=
  { Translation.module raw.core with imports := raw.imports.map fun entry =>
      let type := raw.core.types[entry.typeIndex.toNat]!
      { module := entry.moduleName.text, name := entry.fieldName.text,
        params := type.params.map ValType.toTalos, results := type.results.map ValType.toTalos } }

theorem translation_fields (raw : Raw) :
    raw.toTalos.funcs = Translation.functions raw.core ∧
    raw.toTalos.exports = Translation.functionExports raw.core ∧
    raw.toTalos.imports.length = raw.imports.length ∧
    raw.toTalos.memory = Translation.memory raw.core := by
  simp [Raw.toTalos, Translation.module]

namespace Grammar

inductive Import : List UInt8 → Binary.Import → Prop
  | intro (moduleBytes fieldBytes typeBytes : List UInt8) (entry : Binary.Import)
      (hm : Wasm.Binary.Grammar.Name moduleBytes entry.moduleName)
      (hf : Wasm.Binary.Grammar.Name fieldBytes entry.fieldName)
      (ht : Wasm.Binary.Grammar.U32 typeBytes entry.typeIndex.toNat) :
      Import (moduleBytes ++ fieldBytes ++ [0] ++ typeBytes) entry

def Section (id : UInt8) (relation : List UInt8 → α → Prop)
    (bytes : List UInt8) (entries : List α) : Prop :=
  ∃ payload, bytes = id :: payload ∧ Wasm.Binary.Grammar.Sized
    (Wasm.Binary.Grammar.Vector relation) payload entries

end Grammar

theorem importEntry_sound : Sound importEntry Grammar.Import := by
  intro start entry finish hstart hrun
  unfold importEntry at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i first pair hm
    rcases pair with ⟨moduleName, s₁⟩
    split at hrun
    · contradiction
    · rename_i second pair hf
      rcases pair with ⟨fieldName, s₂⟩
      split at hrun
      · contradiction
      · rename_i third pair hz
        rcases pair with ⟨unit, s₃⟩
        split at hrun
        · contradiction
        · rename_i fourth pair ht
          rcases pair with ⟨typeIndex, s₄⟩
          cases hrun
          obtain ⟨bm, hcm, hgm⟩ := Wasm.Binary.Proof.name_sound _ _ _ hstart hm
          obtain ⟨bf, hcf, hgf⟩ := Wasm.Binary.Proof.name_sound _ _ _
            (hcm.finish_wellFormed hstart) hf
          obtain ⟨bz, hcz, hgz⟩ := expectByte_sound 0 _ _ _
            (hcf.finish_wellFormed (hcm.finish_wellFormed hstart)) hz
          obtain ⟨bt, hct, hgt⟩ := Leb.Proof.u32_sound _ _ _
            (hcz.finish_wellFormed (hcf.finish_wellFormed (hcm.finish_wellFormed hstart))) ht
          subst bz
          exact ⟨_, ((hcm.trans hcf).trans hcz).trans hct,
            Grammar.Import.intro bm bf bt _ hgm hgf hgt⟩

theorem section_sound (id : UInt8) (entry : Parser α)
    (relation : List UInt8 → α → Prop) (he : Sound entry relation) :
    Sound (parseSection id entry) (Grammar.Section id relation) := by
  intro start entries finish hstart hrun
  unfold parseSection at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hid
    rcases pair with ⟨unit, middle⟩
    obtain ⟨bh, hch, hgh⟩ := expectByte_sound id _ _ _ hstart hid
    obtain ⟨bp, hcp, hgp⟩ := Wasm.Binary.Proof.sized_sound
      (Wasm.Binary.Proof.vector_sound he) _ _ _ (hch.finish_wellFormed hstart) hrun
    subst bh
    exact ⟨_, hch.trans hcp, bp, rfl, hgp⟩

/-- Independent byte grammar for the complete canonical section sequence. -/
def Grammar.ModuleBytes : List UInt8 → Raw → Prop :=
  Sequence (fun bytes (_ : Unit) => bytes = [0, 97, 115, 109, 1, 0, 0, 0]) fun _ =>
  Sequence (Grammar.Section 1 Wasm.Binary.Grammar.FuncType) fun types =>
  Sequence (Grammar.Section 2 Grammar.Import) fun imports =>
  Sequence (Grammar.Section 3 (fun bytes index => Wasm.Binary.Grammar.U32 bytes index.toNat))
    fun functionTypeIndices =>
  Sequence (Grammar.Section 5 Wasm.Binary.Grammar.MemoryType) fun memories =>
  Sequence (Grammar.Section 6 Wasm.Binary.Grammar.Global) fun globals =>
  Sequence (Grammar.Section 7 Wasm.Binary.Grammar.Export) fun exports =>
  Sequence (Grammar.Section 10 Wasm.Binary.Grammar.Code) fun codes bytes result =>
    bytes = [] ∧ result = { core := {
      sections := [.type, .function, .memory, .global, .export, .code],
      types, functionTypeIndices, memories, globals, exports, codes }, imports }

theorem moduleParser_sound : Sound moduleParser Grammar.ModuleBytes := by
  unfold moduleParser Grammar.ModuleBytes
  apply sound_bind (expectBytes_sound _)
  intro _
  apply sound_bind (section_sound _ _ _ Wasm.Binary.Proof.funcType_sound)
  intro types
  apply sound_bind (section_sound _ _ _ importEntry_sound)
  intro imports
  apply sound_bind (section_sound _ _ _ Leb.Proof.u32_sound)
  intro functionTypeIndices
  apply sound_bind (section_sound _ _ _ Wasm.Binary.Proof.memoryType_sound)
  intro memories
  apply sound_bind (section_sound _ _ _ Wasm.Binary.Proof.global_sound)
  intro globals
  apply sound_bind (section_sound _ _ _ Wasm.Binary.Proof.exportEntry_sound)
  intro exports
  apply sound_bind (section_sound _ _ _ Wasm.Binary.Proof.code_sound)
  intro codes
  exact sound_pure _

theorem decode_sound {bytes : ByteArray} {raw : Raw} (h : decode bytes = .ok raw) :
    Grammar.ModuleBytes bytes.data.toList raw := runAll_sound moduleParser_sound h

/-- Both the imported and defined signatures are resolved in the same type
table. Validation of code uses their concatenation, while only the defined
signatures are paired with code bodies. -/
def Valid (raw : Raw) : Prop :=
  Validity.SectionsValid raw.core ∧
  (∃ memory, raw.core.memories = [memory] ∧ Validity.LimitsValid memory.limits) ∧
  Validity.GlobalsValid raw.core.globals ∧
  Validity.ExportsValid raw.exportContext ∧
  ∃ imported defined,
    Validity.ResolvedTypes raw.core.types raw.importTypeIndices imported ∧
    Validity.ResolvedTypes raw.core.types raw.core.functionTypeIndices defined ∧
    Validity.FunctionPairsValid raw.core (imported ++ defined) defined raw.core.codes

theorem validate_sound {raw : Raw} (h : validate raw = .ok ()) : Valid raw := by
  unfold validate at h
  dsimp [Bind.bind, Monad.toBind, Except.bind] at h
  split at h
  · contradiction
  · rename_i parsedSections _ hsections
    split at h
    · rename_i hmemoryCount
      split at h
      · contradiction
      · rename_i parsedLimits _ hlimits
        split at h
        · contradiction
        · rename_i parsedGlobals _ hglobals
          split at h
          · contradiction
          · rename_i parsedExports _ hexports
            split at h
            · contradiction
            · rename_i parsedImports imported himported
              split at h
              · contradiction
              · rename_i parsedDefined defined hdefined
                refine ⟨Wasm.Binary.Proof.validateSections_sound (by simpa using hsections), ?_,
                  Wasm.Binary.Proof.validateGlobals_sound raw.core.globals (by simpa using hglobals),
                  Wasm.Binary.Proof.validateExports_sound (by simpa using hexports),
                  imported, defined,
                  Wasm.Binary.Proof.resolveTypes_sound _ _ _ himported,
                  Wasm.Binary.Proof.resolveFunctionTypes_sound hdefined,
                  Wasm.Binary.Proof.validateFunctionPairs_sound _ _ _ _ _ h⟩
                obtain ⟨memory, hm⟩ := Wasm.Binary.Proof.exists_eq_singleton_of_length_eq_one
                  raw.core.memories hmemoryCount
                refine ⟨memory, hm, ?_⟩
                apply Wasm.Binary.Proof.validateLimits_sound
                rw [hm] at hlimits
                simpa [List.head!] using hlimits
    · contradiction

#print axioms decode_sound
#print axioms validate_sound

#print axioms importEntry_sound
#print axioms section_sound
#print axioms translation_fields

end Project.ByteIO.Binary
