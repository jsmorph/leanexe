import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.ValidationParts
import Lean.Elab.Tactic.Cbv

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem validation_export_names : Validator.duplicateName? Cache.raw.exports = none := by cbv

theorem validation_export0 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[0]! = .ok () := by
  have hname : Cache.raw.exports[0]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[0]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export1 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[1]! = .ok () := by
  have hname : Cache.raw.exports[1]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[1]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export2 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[2]! = .ok () := by
  have hname : Cache.raw.exports[2]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[2]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export3 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[3]! = .ok () := by
  have hname : Cache.raw.exports[3]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[3]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export4 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[4]! = .ok () := by
  have hname : Cache.raw.exports[4]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[4]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export5 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[5]! = .ok () := by
  have hname : Cache.raw.exports[5]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[5]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export6 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[6]! = .ok () := by
  have hname : Cache.raw.exports[6]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[6]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export7 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[7]! = .ok () := by
  have hname : Cache.raw.exports[7]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[7]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export8 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[8]! = .ok () := by
  have hname : Cache.raw.exports[8]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[8]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export9 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[9]! = .ok () := by
  have hname : Cache.raw.exports[9]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[9]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_export10 :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[10]! = .ok () := by
  have hname : Cache.raw.exports[10]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[10]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

theorem validation_exports : Validator.validateExports Cache.raw = .ok () := by
  unfold Validator.validateExports
  rw [validation_export_names]
  change Validator.validateExportEntries Cache.raw
    [Cache.raw.exports[0]!, Cache.raw.exports[1]!, Cache.raw.exports[2]!, Cache.raw.exports[3]!, Cache.raw.exports[4]!, Cache.raw.exports[5]!, Cache.raw.exports[6]!, Cache.raw.exports[7]!, Cache.raw.exports[8]!, Cache.raw.exports[9]!, Cache.raw.exports[10]!] = .ok ()
  simp only [Validator.validateExportEntries, Bind.bind, Pure.pure, Except.pure, Except.bind, validation_export0, validation_export1, validation_export2, validation_export3, validation_export4, validation_export5, validation_export6, validation_export7, validation_export8, validation_export9, validation_export10]

#print axioms validation_exports

end Project.Gpt2QuantizedGroupedRows.Artifact
