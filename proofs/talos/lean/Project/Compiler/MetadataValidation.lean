import Project.Compiler.ValidationRules
import LeanExe.Extract.Core

namespace Project.Compiler.ArithmeticModule

open Wasm.Binary

theorem sections_valid (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.validateSections (rawModule func entry user) = .ok () := by rfl

theorem limits_valid (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.validateLimits (rawModule func entry user).memories.head!.limits = .ok () := by rfl

theorem globals_valid (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.validateGlobals (rawModule func entry user).globals = .ok () := by
  simp [rawModule, globalValues, globalValue, Validator.validateGlobals,
    Validator.validateGlobal, Validator.constType, Validator.inSignedRange, ArithmeticValidation.signed64_range,
    bind, Except.bind, pure, Except.pure]

theorem types_resolved (func : LeanExe.IR.Func) (entry : String) (user : Code) :
    Validator.resolveFunctionTypes (rawModule func entry user) = .ok (typeValues func) := by rfl

theorem utf8_bytes_eq (a b : String) : a.toUTF8.data.toList = b.toUTF8.data.toList ↔ a = b := by
  constructor
  · intro same
    have dataEq := congrArg List.toArray same
    simp only [Array.toArray_toList] at dataEq
    have bytes := ByteArray.ext dataEq
    simpa only [String.toUTF8_eq_toByteArray, String.toByteArray_inj] using bytes
  · intro same
    subst b
    rfl

@[simp] theorem utf8_bytes_beq (a b : String) :
    (a.toUTF8.data.toList == b.toUTF8.data.toList) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, utf8_bytes_eq]

def exportLimit : Parsing.ExportKind → Nat
  | .func => 5
  | .memory => 1
  | .global => 6

theorem entry_valid (func : LeanExe.IR.Func) (entry text : String) (user : Code)
    (kind : Parsing.ExportKind) (index : Nat) (bound : index < exportLimit kind) :
    Validator.validateExportEntry (rawModule func entry user) (exportValue text kind index) = .ok () := by
  have format : index < 2 ^ 32 := by cases kind <;> dsimp [exportLimit] at bound <;> omega
  cases kind <;>
    simp [Validator.validateExportEntry, exportValue, Parsing.ExportKind.desc,
      String.toUTF8_eq_toByteArray, UInt32.toNat_ofNat_of_lt' format,
      rawModule, functionValues, memoryValues, globalValues, exportLimit, pure] at bound ⊢ <;>
    simp_all [Except.pure]

theorem duplicate_free_of_names (items : List Export)
    (matched : ∀ item ∈ items, item.name.bytes = item.name.text.toUTF8.data.toList)
    (uniqueNames : (items.map (fun item => item.name.text)).Nodup) :
    Validator.duplicateName? items = none := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have nodup := List.nodup_cons.mp uniqueNames
    have missing : ¬ rest.any (fun other => other.name.bytes == item.name.bytes) = true := by
      intro found
      obtain ⟨other, member, same⟩ := List.any_eq_true.mp found
      have bytesEq : other.name.bytes = item.name.bytes := by simpa only [beq_iff_eq] using same
      rw [matched other (by simp [member]), matched item (by simp)] at bytesEq
      have namesEq := (utf8_bytes_eq _ _).mp bytesEq
      exact nodup.1 (List.mem_map.mpr ⟨other, member, namesEq⟩)
    simp only [Validator.duplicateName?, missing, ite_false]
    exact ih (fun other member => matched other (by simp [member])) nodup.2

theorem exports_valid (func : LeanExe.IR.Func) (entry : String) (user : Code)
    (available : entry ∉ LeanExe.Extract.Core.reservedExportNames) :
    Validator.validateExports (rawModule func entry user) = .ok () := by
  have unique : Validator.duplicateName? (exportValues entry) = none := by
    apply duplicate_free_of_names
    · intro item member
      simp only [exportValues, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · simp only [exportValues, List.map_cons, List.map_nil, exportValue]
      simp_all [LeanExe.Extract.Core.reservedExportNames, ne_comm]
  unfold Validator.validateExports
  change (match Validator.duplicateName? (exportValues entry) with
    | some name => Validator.moduleFailure (.duplicateExportName name)
    | none => Validator.validateExportEntries (rawModule func entry user) (exportValues entry)) = .ok ()
  rw [unique]
  have h0 := entry_valid func entry "memory" user .memory 0 (by decide)
  have h1 := entry_valid func entry entry user .func 0 (by decide)
  have h2 := entry_valid func entry "alloc" user .func 1 (by decide)
  have h3 := entry_valid func entry "reset" user .func 2 (by decide)
  have h4 := entry_valid func entry "retain" user .func 3 (by decide)
  have h5 := entry_valid func entry "release" user .func 4 (by decide)
  have h6 := entry_valid func entry "free" user .func 4 (by decide)
  have h7 := entry_valid func entry "allocCount" user .global 2 (by decide)
  have h8 := entry_valid func entry "retainCount" user .global 3 (by decide)
  have h9 := entry_valid func entry "releaseCount" user .global 4 (by decide)
  have h10 := entry_valid func entry "freeCount" user .global 5 (by decide)
  simp only [Validator.validateExportEntries, exportValues, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, bind, Except.bind, pure, Except.pure]

end Project.Compiler.ArithmeticModule
