import Library.Numerics.Limiters.Minmod.Compiled
import Library.Numerics.Limiters.Minmod.Proof
import Verified.Master

namespace Library.Numerics.Limiters.Minmod

open CodeLib.IEEE64 (value)

theorem minmod_export :
    ({ name := "minmod", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `minmod`, called on two floats, returns a float whose value is the minmod of their
values: the value of smaller magnitude when the two have the same sign, and zero otherwise. -/
theorem minmod_master :
    Verified.Master compiled.module compiled.tables "minmod" compiled.minmod.bound (fun _ => True)
      (fun (x : Float × Float) (y : Float) =>
        value y.toBits = max 0 (min (value x.1.toBits) (value x.2.toBits)) +
          min 0 (max (value x.1.toBits) (value x.2.toBits))) :=
  .of_trapFree (.ofA compiled.minmod.trapFree) nofun minmod_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => real_minmod x.1 x.2

#print axioms minmod_master

end Library.Numerics.Limiters.Minmod
