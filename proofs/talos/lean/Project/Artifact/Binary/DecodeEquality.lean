import Project.Artifact.Binary.Decode
import Project.Artifact.Binary.Equality

namespace Wasm.Binary

/-- A successful Boolean comparison is checked in the kernel. The cached AST
is only a proposed result; this premise runs the actual binary decoder. -/
theorem decode_eq_of_comparison {bytes : ByteArray} {raw : RawModule} {fuel : Nat}
    (checked : ((decode bytes).toOption.map fun found =>
      Equality.rawModuleEqual fuel found raw) = some true) :
    decode bytes = .ok raw := by
  cases found : decode bytes with
  | error error => simp [found, Except.toOption] at checked
  | ok result =>
      have equality : Equality.rawModuleEqual fuel result raw = true := by
        simpa only [found, Except.toOption, Option.map_some, Option.some.injEq] using checked
      exact congrArg Except.ok (Equality.rawModuleEqual_sound equality)

#print axioms decode_eq_of_comparison
end Wasm.Binary
