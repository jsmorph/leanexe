import Project.ByteIO.ArtifactValidation

namespace Project.ByteIO.ValidationChecks
open Project.ByteIO.Artifact

/-- An imported signature must resolve before code validation begins. -/
theorem rejects_missing_import_type :
    (Binary.validate { raw with
      imports := raw.imports.map (fun entry => { entry with typeIndex := 1000 }) }).toOption.isNone = true := by
  cbv

/-- Export bounds include imports and definitions, and still reject the
first index beyond their combined function space. -/
theorem rejects_export_past_end :
    (Binary.validate { raw with core := { raw.core with exports :=
      [{ name := { bytes := [120], text := "x" },
         desc := .func (UInt32.ofNat (raw.imports.length + raw.core.codes.length)) }] } }).toOption.isNone = true := by
  cbv

#print axioms rejects_missing_import_type
#print axioms rejects_export_past_end

end Project.ByteIO.ValidationChecks
