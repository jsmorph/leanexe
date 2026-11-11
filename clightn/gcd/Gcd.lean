import TestSupport.Bare.Gcd
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.Proof.Rename
import LeanExe.Native.ClightN.Read
import ClightNGcd.GcdSpec

/-!
The statement `gcd_terminates` of the instance `Gcd.nsx` that `clightn/check.sh` writes with
`clightn/clightgen.py` from the Coq file that `clightgen` prints for the bare-metal program of
`gcd 1071 462`: N's program judgment holds of the file's definitions and `main`, with one volatile
store to `lx_out` of each byte of the result and the result 0.  The proof carries the copy's
`loopCompiled.gcd.program` (`tests/TestSupport/Bare/Gcd.lean`) to the file's program by the
renaming theorem and to N by `program_to_n`.  The kernel computes the translation and checks that
renaming its whole program gives the file's definitions, that the renaming is injective, that
CompCert's declarations before the translation's satisfy `PrefixOk`, and that `progOk` accepts the
file's program.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

noncomputable section

abbrev gcdT : Translation := TestSupport.Native.Gcd.loopCompiled.translation

def gcdMain : function := bareMain nativeCap 2 [1071, 462] .word

/-- CompCert's declarations in the file: its definitions less the translation's other than
`__builtin_fsqrt`, `lx_out`, and `main`. -/
def preL : Defs :=
  preOf (cst_gcd_defs.take (cst_gcd_defs.length - gcdT.cprogram.prog_defs.length - 1)) 0

def whole : program function := bareProgram preL gcdT gcdMain

def gOf : ident → ident := gOfL whole.prog_defs cst_gcd_defs

def tOf : ident → ident → ident := tOfL whole.prog_defs cst_gcd_defs

def gcdProgram : program function :=
  { prog_defs := cst_gcd_defs, prog_public := [], prog_main := cst_gcd_main }

/-- The functions that `main` reaches: `main`, `lx_init`, and the entry. -/
def gcdS : List ident := [gOf mainId, gOf initId, gOf (funId 2)]

theorem gcd_defs_eq : gcdProgram.prog_defs = renDefs gOf tOf whole.prog_defs := by
  decide +kernel

theorem gcd_main_eq : gcdProgram.prog_main = gOf whole.prog_main := by
  decide +kernel

theorem gcd_progG_sub : ∀ x ∈ progG whole, x ∈ whole.prog_defs.map (·.1) := by
  decide +kernel

theorem gcd_ids_nodup : ((whole.prog_defs.map (·.1)).map gOf).Nodup := by
  decide +kernel

theorem gcd_inj : ∀ x ∈ progG whole, ∀ y ∈ progG whole, gOf x = gOf y → x = y :=
  fun x hx y hy e => inj_of_nodup_map gcd_ids_nodup x (gcd_progG_sub x hx) y (gcd_progG_sub y hy) e

theorem gcd_temps_sub : ∀ id ∈ whole.prog_defs.map (·.1), ∀ x ∈ tempsOf whole.prog_defs id,
    x ∈ declOfL whole.prog_defs id := by
  decide +kernel

theorem gcd_temps_nodup :
    ∀ id ∈ whole.prog_defs.map (·.1), ((declOfL whole.prog_defs id).map (tOf id)).Nodup := by
  decide +kernel

theorem gcd_prefix : PrefixOk preL :=
  prefix_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem gcd_progOk : progOk cst_gcd_defs cst_gcd_main gcdS = true := by
  decide +kernel

theorem gcd_value : TestSupport.Native.Gcd.gcd 1071 462 = 21 := by
  rw [TestSupport.Native.Gcd.gcd, TestSupport.Native.Gcd.gcd, TestSupport.Native.Gcd.gcd,
    TestSupport.Native.Gcd.gcd, TestSupport.Native.Gcd.gcd]
  decide

theorem gcd_trace_eq (g : ident → ident) (hg : g outId = gOf outId) :
    renTrace g (outTrace (encodeWord 21)) = cst_gcd_trace := by
  simp only [renTrace, outTrace, List.map_map, Function.comp_def, renEvent, renEventval, hg]
  decide +kernel

theorem gcd_terminates : stmt_gcd_terminates := by
  rcases TestSupport.Native.Gcd.loopCompiled.gcd.program Archi.aarch64 ExtSem.none preL gcd_prefix
    with hp | ⟨hf, _⟩
  · obtain ⟨g', hg', hp'⟩ := bigstep_program_terminates_rename_on gcd_inj
      (tinj_of gcd_temps_sub gcd_temps_nodup) gcd_defs_eq gcd_main_eq hp ExtSem.none
    have hn := program_to_n gcdS gcd_progOk hp'
    rw [gcd_value, gcd_trace_eq g' (hg' outId (by decide +kernel))] at hn
    exact hn
  · cases hf

end

end ClightN.Proof

run_cmd ClightN.Read.dump
