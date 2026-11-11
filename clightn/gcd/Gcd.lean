import TestSupport.Bare.Gcd
import LeanExe.Native.ClightN.Exec
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
file's program.  The renaming is read off the two lists of definitions, which list the same
definitions in the same order: a global's identifier at its position, and a temporary's at its
position among a function's parameters and temporaries.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

noncomputable section

deriving instance DecidableEq for LClight.expr
deriving instance DecidableEq for LClight.statement, LClight.labeled_statements
deriving instance DecidableEq for LClight.function
deriving instance DecidableEq for LClight.fundef
deriving instance DecidableEq for LClight.globvar
deriving instance DecidableEq for LClight.globdef

abbrev gcdT : Translation := TestSupport.Native.Gcd.loopCompiled.translation

def gcdMain : function := bareMain nativeCap 2 [1071, 462] .word

/-- CompCert's declarations with the identifiers that the whole program gives them:
`__builtin_fsqrt` takes `sqrtId`, and the `j`-th of the others `4 j + 5`. -/
def preOf : Defs → Nat → Defs
  | [], _ => []
  | (_, d) :: rest, j =>
      if d = sqrtDef then (sqrtId, d) :: preOf rest j
      else (4 * j + 5, d) :: preOf rest (j + 1)

/-- CompCert's declarations in the file: its definitions less the translation's other than
`__builtin_fsqrt`, `lx_out`, and `main`. -/
def preL : Defs :=
  preOf (cst_gcd_defs.take (cst_gcd_defs.length - gcdT.cprogram.prog_defs.length - 1)) 0

def whole : program function := bareProgram preL gcdT gcdMain

/-- The file's identifier of each global, by position. -/
def gOf (x : ident) : ident :=
  (((whole.prog_defs.map (·.1)).zip (cst_gcd_defs.map (·.1))).lookup x).getD x

/-- The file's identifier of each temporary of the function `fid`, by position. -/
def tempsZip (fid : ident) : List (ident × ident) :=
  match whole.prog_defs.lookup fid, cst_gcd_defs.lookup (gOf fid) with
  | some (.Gfun (.Internal f)), some (.Gfun (.Internal f')) =>
      ((f.fn_params ++ f.fn_temps).map (·.1)).zip ((f'.fn_params ++ f'.fn_temps).map (·.1))
  | _, _ => []

def tOf (fid x : ident) : ident := ((tempsZip fid).lookup x).getD x

def gcdProgram : program function :=
  { prog_defs := cst_gcd_defs, prog_public := [], prog_main := cst_gcd_main }

/-- The functions that `main` reaches: `main`, `lx_init`, and the entry. -/
def gcdS : List ident := [gOf mainId, gOf initId, gOf (funId 2)]

theorem gcd_defs_eq : gcdProgram.prog_defs = renDefs gOf tOf whole.prog_defs := by
  decide +kernel

theorem gcd_main_eq : gcdProgram.prog_main = gOf whole.prog_main := by
  decide +kernel

/-- A map whose images of the list `l` are distinct is injective on `l`. -/
theorem inj_of_nodup_map {f : ident → ident} :
    ∀ {l : List ident}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, _, hx, _, _, _ => by cases hx
  | a :: l, h, x, hx, y, hy, e => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd e.symm (h.1 y hy')
      · exact absurd e (h.1 x hx')
      · exact inj_of_nodup_map h.2 x hx' y hy' e

/-- The parameters and temporaries that the function `fid` declares. -/
def declOf (fid : ident) : List ident :=
  match whole.prog_defs.lookup fid with
  | some (.Gfun (.Internal f)) => (f.fn_params ++ f.fn_temps).map (·.1)
  | _ => []

theorem gcd_progG_sub : ∀ x ∈ progG whole, x ∈ whole.prog_defs.map (·.1) := by
  decide +kernel

theorem gcd_ids_nodup : ((whole.prog_defs.map (·.1)).map gOf).Nodup := by
  decide +kernel

theorem gcd_inj : ∀ x ∈ progG whole, ∀ y ∈ progG whole, gOf x = gOf y → x = y :=
  fun x hx y hy e => inj_of_nodup_map gcd_ids_nodup x (gcd_progG_sub x hx) y (gcd_progG_sub y hy) e

theorem gcd_temps_sub : ∀ id ∈ whole.prog_defs.map (·.1), ∀ x ∈ tempsOf whole.prog_defs id,
    x ∈ declOf id := by
  decide +kernel

theorem gcd_temps_nodup : ∀ id ∈ whole.prog_defs.map (·.1), ((declOf id).map (tOf id)).Nodup := by
  decide +kernel

theorem gcd_tinj_defs : ∀ id ∈ whole.prog_defs.map (·.1), ∀ x ∈ tempsOf whole.prog_defs id,
    ∀ y ∈ tempsOf whole.prog_defs id, tOf id x = tOf id y → x = y :=
  fun id hid x hx y hy e => inj_of_nodup_map (gcd_temps_nodup id hid) x (gcd_temps_sub id hid x hx)
    y (gcd_temps_sub id hid y hy) e

theorem gcd_tinj : ∀ id, ∀ x ∈ tempsOf whole.prog_defs id, ∀ y ∈ tempsOf whole.prog_defs id,
    tOf id x = tOf id y → x = y := by
  intro id
  by_cases hid : id ∈ whole.prog_defs.map (·.1)
  · exact gcd_tinj_defs id hid
  · have : tempsOf whole.prog_defs id = [] := by
      simp only [tempsOf, List.flatMap_eq_nil_iff, List.mem_filter, beq_iff_eq, and_imp]
      intro d hd e
      exact absurd (e ▸ List.mem_map_of_mem (f := (·.1)) hd) hid
    simp [this]

theorem gcd_prefix : PrefixOk preL := by
  have hf : preL.all (fun d => match d.2 with | .Gfun _ => true | .Gvar _ => false) = true := by
    decide +kernel
  refine ⟨by decide +kernel, fun d hd => ?_, by decide +kernel, by decide +kernel⟩
  have := List.all_eq_true.mp hf d hd
  match d, this with
  | (_, .Gfun f), _ => exact ⟨f, rfl⟩
  | (_, .Gvar _), h => simp at h

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
  · obtain ⟨g', hg', hp'⟩ := bigstep_program_terminates_rename_on gcd_inj gcd_tinj gcd_defs_eq
      gcd_main_eq hp ExtSem.none
    have hn := program_to_n gcdS gcd_progOk hp'
    rw [gcd_value, gcd_trace_eq g' (hg' outId (by decide +kernel))] at hn
    exact hn
  · cases hf

end

end ClightN.Proof

run_cmd ClightN.Read.dump
