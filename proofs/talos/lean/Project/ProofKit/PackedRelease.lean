import Project.ProofKit.FixedArrayRelease
import Project.Runtime.Spec

namespace Project.ProofKit.PackedRelease
open Wasm Project.Clob Project.Runtime

abbrev store := FixedArrayRelease.store

theorem exact (env : HostEnv Unit) (module_ : Wasm.Module) (id : Nat)
    (initial : Store Unit) (root head releases frees : UInt64)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[id - module_.imports.length]? =
      some { releaseFuncDef id with typeIdx := typeIdx })
    (hImport : module_.imports[id]? = none)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (hMagic : initial.mem.read64 (root - 48).toUInt32 = 5501223100278326855)
    (hRc : initial.mem.read64 (root - 40).toUInt32 = 1)
    (hKind : initial.mem.read64 (root - 24).toUInt32 = 0)
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees)) :
    TerminatesWith env module_ id initial [.i64 root]
      (fun final values => values = [] ∧ final = store initial root head releases frees) := by
  apply (release_frees_fresh_raw_full env module_ id initial root head releases frees
    hFunction hImport hRoot hRoot32 hFit hMagic hRc hKind hHead hReleases hFrees).mono
  rintro final values ⟨hValues, hMem, hGlobals, hStore⟩
  refine ⟨hValues, ?_⟩
  have hGlobals' : final.globals =
      { globals := ((initial.globals.globals.set 4 (.i64 (releases + 1))).set 5
        (.i64 (frees + 1))).set 1 (.i64 root) } := congrArg Globals.mk hGlobals
  rw [hStore, hMem, hGlobals']
  rfl

#print axioms exact

end Project.ProofKit.PackedRelease
