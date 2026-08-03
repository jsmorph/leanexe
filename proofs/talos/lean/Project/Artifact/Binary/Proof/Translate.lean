import Project.Artifact.Binary.Translate

namespace Wasm.Binary.Proof

theorem toTalos_fields (validated : ValidatedModule) :
    let raw := validated.raw
    let translated := validated.toTalos
    translated.funcs = Translation.functions raw ∧
    translated.exports = Translation.functionExports raw ∧
    translated.memory = Translation.memory raw ∧
    translated.globals = Translation.globals raw ∧
    translated.types = raw.types.map FuncType.toTalos ∧
    translated.globalExports = [] ∧
    translated.memoryExports = [] ∧
    translated.extraMemories = [] ∧
    translated.imports = [] ∧
    translated.startFunc = none ∧
    translated.gcTypes = [] ∧
    translated.tables = [] ∧
    translated.elements = [] ∧
    translated.importedGlobals = [] ∧
    translated.importedTables = [] ∧
    translated.importedMemories = [] ∧
    translated.tableExports = [] ∧
    translated.tags = [] := by
  simp [ValidatedModule.toTalos, Translation.module]

end Wasm.Binary.Proof
