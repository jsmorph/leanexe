import Library.Numerics.Filters.Cic.Compiled
import Library.Numerics.Filters.Cic.Proof
import Library.Numerics.Filters.Cic.Exact
import Verified.Master

namespace Library.Numerics.Filters.Cic

theorem cic_export :
    ({ name := "cic", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `cic`, called on an array of words, returns the CIC decimation filter of order 3,
decimation 8, and differential delay 1 of the words read as signed integers: each output word,
read as a signed integer, is the output of `outputs` reduced into `[-2 ^ 63, 2 ^ 63)`. -/
theorem cic_master :
    Verified.Master compiled.module compiled.tables "cic" compiled.cic.bound
      (fun _ => True)
      (fun (xs ys : Array UInt64) => ys.toList.map (fun w => w.toBitVec.toInt) =
        (outputs 3 8 1 (xs.toList.map fun w => w.toBitVec.toInt)).map (Int.bmod · (2 ^ 64))) :=
  .of_trapFree (.ofA compiled.cic.trapFree) nofun cic_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => by rw [cic_toList]; exact toInt_cascade 3 8 1 x.toList

#print axioms cic_master

end Library.Numerics.Filters.Cic
