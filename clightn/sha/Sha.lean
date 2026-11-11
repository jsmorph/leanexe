import TestSupport.Bare.Input
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.Proof.Rename
import LeanExe.Native.ClightN.Read
import ClightNSha.ShaSpec

/-!
The statement `sha_reads` of the instance `Sha.nsx` that `clightn/check.sh` writes with
`clightn/clightgen.py` from the Coq file that `clightgen` prints for the program with input
around the export `sha256` of `Library.Hashing.Sha256.compiled`: for every sequence `σ` of the
values of its volatile loads, N's program judgment holds of the file's definitions and `main`
with a trace whose `k`-th volatile load reads `σ k`.  The proof carries the copy's
`TestSupport.Bare.sha256_input` to the file's program by the renaming theorem, to N by
`program_to_n`, and the trace's reads to N's `nreads` by `reads_nreads`.  The kernel computes the
translation and checks that renaming its whole program gives the file's definitions, that the
renaming is injective, that CompCert's declarations before the translation's satisfy `PrefixOk`,
and that `progOk` accepts the file's program with all of its internal functions.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

noncomputable section

abbrev shaT : Translation := Library.Hashing.Sha256.compiled.translation

def shaMain : function := inMain nativeCap 11 (.words 4)

/-- CompCert's declarations in the file: its definitions less the translation's other than
`__builtin_fsqrt`, `lx_in`, `lx_out`, and `main`. -/
def preL : Defs :=
  preOf (cst_sha_defs.take (cst_sha_defs.length - shaT.cprogram.prog_defs.length - 2)) 0

def whole : program function := inProgram preL shaT shaMain

def gOf : ident → ident := gOfL whole.prog_defs cst_sha_defs

def tOf : ident → ident → ident := tOfL whole.prog_defs cst_sha_defs

def shaProgram : program function :=
  { prog_defs := cst_sha_defs, prog_public := [], prog_main := cst_sha_main }

theorem sha_defs_eq : shaProgram.prog_defs = renDefs gOf tOf whole.prog_defs := by
  decide +kernel

theorem sha_main_eq : shaProgram.prog_main = gOf whole.prog_main := by
  decide +kernel

theorem sha_progG_sub : ∀ x ∈ progG whole, x ∈ whole.prog_defs.map (·.1) := by
  decide +kernel

theorem sha_ids_nodup : ((whole.prog_defs.map (·.1)).map gOf).Nodup := by
  decide +kernel

theorem sha_inj : ∀ x ∈ progG whole, ∀ y ∈ progG whole, gOf x = gOf y → x = y :=
  fun x hx y hy e => inj_of_nodup_map sha_ids_nodup x (sha_progG_sub x hx) y (sha_progG_sub y hy) e

theorem sha_temps_sub : ∀ id ∈ whole.prog_defs.map (·.1), ∀ x ∈ tempsOf whole.prog_defs id,
    x ∈ declOfL whole.prog_defs id := by
  decide +kernel

theorem sha_temps_nodup :
    ∀ id ∈ whole.prog_defs.map (·.1), ((declOfL whole.prog_defs id).map (tOf id)).Nodup := by
  decide +kernel

theorem sha_pre_sqrt : (sqrtId, sqrtDef) ∈ preL := by decide +kernel

theorem sha_pre_funs :
    preL.all (fun d => match d.2 with | .Gfun _ => true | .Gvar _ => false) = true := by
  decide +kernel

theorem sha_pre_nodup : (preL.map (·.1)).Nodup := by decide +kernel

theorem sha_pre_ids : ∀ x : Nat, x ∈ preL.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1) := by
  decide +kernel

theorem sha_prefix : PrefixOk preL :=
  prefix_of sha_pre_sqrt sha_pre_funs sha_pre_nodup sha_pre_ids

theorem sha_progOk :
    progOk shaProgram.prog_defs shaProgram.prog_main (internals cst_sha_defs) = true := by
  decide +kernel

theorem sha_reads : stmt_sha_reads := by
  intro σ
  obtain ⟨t, r, hp, hr, -⟩ := TestSupport.Bare.sha256_input Archi.aarch64 ExtSem.none preL
    sha_prefix σ
  obtain ⟨g', _, hp'⟩ := bigstep_program_terminates_rename_on sha_inj
    (tinj_of sha_temps_sub sha_temps_nodup) sha_defs_eq sha_main_eq hp ExtSem.none
  have hn := program_to_n (p := shaProgram) (internals cst_sha_defs) sha_progOk hp'
  exact ⟨renTrace g' t, r, hn,
    nreads_ren g' (reads_nreads hr (events_ren g' (nprog_events hn)))⟩

end

end ClightN.Proof

run_cmd ClightN.Read.dump
