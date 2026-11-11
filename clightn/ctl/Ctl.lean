import TestSupport.Bare.Ctl
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.Proof.Rename
import LeanExe.Native.ClightN.Read
import ClightNCtl.CtlSpec

/-!
The statement `ctl_reacts` of the instance `Ctl.nsx` that `clightn/check.sh` writes with
`clightn/clightgen.py` from the Coq file that `clightgen` prints for the controller program around
the step `ctlStep` of `tests/TestSupport/Bare/Ctl.lean`, from the state 0: there are functions `W`
and `P` of the sequence `σ` of the values of the volatile loads such that, for every `σ`, N's
judgment `nreacts` holds of the file's definitions and `main` with no event before the loop and
the trace `W σ n` in iteration `n`, `P σ n` is the trace of the first `n` iterations, and its
`k`-th volatile load reads `σ k`.  The proof carries the copy's `TestSupport.Bare.filter_program`
to the file's program by the renaming theorem of `LoopReacts` and to N by `reacts_to_n`, and the
reads that `ctl_reads` states to N's `nreads` by `reads_nreads`.  The renaming that
`exists_injective_renaming` gives does not depend on `σ`, so `W` and `P` are functions of `σ`
without a choice.  The kernel computes the translation and checks that renaming its whole program
gives the file's definitions, that the renaming is injective, that CompCert's declarations before
the translation's satisfy `PrefixOk`, and that `progOk` accepts the file's program with all of its
internal functions.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec
open LeanExe.Requests (windows)

noncomputable section

abbrev ctlT : Translation := TestSupport.Bare.ctlCompiled.translation

def ctlM : function := ctlMain 2 0

/-- CompCert's declarations in the file: its definitions less the translation's other than
`__builtin_fsqrt`, `lx_in`, `lx_out`, and `main`. -/
def preL : Defs :=
  preOf (cst_ctl_defs.take (cst_ctl_defs.length - ctlT.cprogram.prog_defs.length - 2)) 0

def whole : program function := inProgram preL ctlT ctlM

def gOf : ident → ident := gOfL whole.prog_defs cst_ctl_defs

def tOf : ident → ident → ident := tOfL whole.prog_defs cst_ctl_defs

def ctlProgram : program function :=
  { prog_defs := cst_ctl_defs, prog_public := [], prog_main := cst_ctl_main }

theorem ctl_defs_eq : ctlProgram.prog_defs = renDefs gOf tOf whole.prog_defs := by
  decide +kernel

theorem ctl_main_eq : ctlProgram.prog_main = gOf whole.prog_main := by
  decide +kernel

theorem ctl_progG_sub : ∀ x ∈ progG whole, x ∈ whole.prog_defs.map (·.1) := by
  decide +kernel

theorem ctl_ids_nodup : ((whole.prog_defs.map (·.1)).map gOf).Nodup := by
  decide +kernel

theorem ctl_inj : ∀ x ∈ progG whole, ∀ y ∈ progG whole, gOf x = gOf y → x = y :=
  fun x hx y hy e => inj_of_nodup_map ctl_ids_nodup x (ctl_progG_sub x hx) y (ctl_progG_sub y hy) e

theorem ctl_temps_sub : ∀ id ∈ whole.prog_defs.map (·.1), ∀ x ∈ tempsOf whole.prog_defs id,
    x ∈ declOfL whole.prog_defs id := by
  decide +kernel

theorem ctl_temps_nodup :
    ∀ id ∈ whole.prog_defs.map (·.1), ((declOfL whole.prog_defs id).map (tOf id)).Nodup := by
  decide +kernel

theorem ctl_pre_sqrt : (sqrtId, sqrtDef) ∈ preL := by decide +kernel

theorem ctl_pre_funs :
    preL.all (fun d => match d.2 with | .Gfun _ => true | .Gvar _ => false) = true := by
  decide +kernel

theorem ctl_pre_nodup : (preL.map (·.1)).Nodup := by decide +kernel

theorem ctl_pre_ids : ∀ x : Nat, x ∈ preL.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1) := by
  decide +kernel

theorem ctl_prefix : PrefixOk preL :=
  prefix_of ctl_pre_sqrt ctl_pre_funs ctl_pre_nodup ctl_pre_ids

theorem ctl_progOk :
    progOk ctlProgram.prog_defs ctlProgram.prog_main (internals cst_ctl_defs) = true := by
  decide +kernel

theorem inTrace_ls (σ : Nat → int) : ∀ a d, (inTrace σ a d).all isLS = true
  | _, 0 => rfl
  | a, d + 1 => by
      show (isLS (inEvent a (σ a)) && (inTrace σ (a + 1) d).all isLS) = true
      rw [inTrace_ls σ (a + 1) d]
      rfl

theorem outTrace_ls : ∀ bs : List UInt8, (outTrace bs).all isLS = true
  | [] => rfl
  | _ :: bs => by
      show (true && (outTrace bs).all isLS) = true
      rw [outTrace_ls bs]
      rfl

/-- A window of the controller holds only volatile loads and stores. -/
theorem ctlTrace_ls (ctl : UInt64 → UInt64 → UInt64) (s0 : UInt64) (σ : Nat → int) (n : Nat) :
    (ctlTrace ctl s0 σ n).all isLS = true := by
  rw [ctlTrace, List.all_append, inTrace_ls, outTrace_ls]
  rfl

theorem windows_ls {W : Nat → trace} (h : ∀ n, (W n).all isLS = true) :
    ∀ n, (windows W n).all isLS = true
  | 0 => rfl
  | n + 1 => by simp only [windows, List.all_append, windows_ls h n, h n, Bool.and_self]

theorem ctl_reacts : stmt_ctl_reacts := by
  obtain ⟨g', τ', hinj, hτ', heq, hsame⟩ :=
    exists_injective_renaming ctl_inj (tinj_of ctl_temps_sub ctl_temps_nodup)
  refine ⟨fun σ n => renTrace g' (ctlTrace TestSupport.Bare.ctlStep 0 σ n),
    fun σ n => renTrace g' (windows (ctlTrace TestSupport.Bare.ctlStep 0 σ) n),
    fun σ => ⟨?_, rfl, fun n => ?_, fun n => ?_⟩⟩
  · exact reacts_to_n (p := ctlProgram) (internals cst_ctl_defs) ctl_progOk
      (loopReacts_rename (p := whole) hinj hτ' (ExtRen.none g' ExtSem.none)
        (by rw [ctl_defs_eq, hsame]) (by rw [ctl_main_eq, heq _ (List.mem_cons_self ..)])
        (TestSupport.Bare.filter_program Archi.aarch64 ExtSem.none preL ctl_prefix σ))
  · simp only [windows, renTrace_append, ClightN.Base.app]
  · have hr := ctl_reads TestSupport.Bare.ctlStep 0 σ n
    simp only [E0, List.nil_append] at hr
    exact nreads_ren g' (reads_nreads hr (windows_ls (ctlTrace_ls _ _ σ) n))

end

end ClightN.Proof

run_cmd ClightN.Read.dump
