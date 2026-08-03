import CodeLib

namespace LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec

def expected (input : UInt64) : UInt64 :=
  UInt64.ofNat input.toNat.primeFactorsList.length

end LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec

namespace LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec

def ArtifactSpec (module_ : Wasm.Module) : Prop :=
  ∃ entry, module_.findExport "compute" = some entry ∧
    ∀ (env : Wasm.HostEnv Unit) (initial : Wasm.Store Unit) (n : UInt64),
      Wasm.TerminatesWith env module_ entry initial [.i64 n] (fun _ results => results = [.i64 (expected n)])

end LeanExeGen.GeneratedRc8c2d9f87deb0758.FormalSpec
