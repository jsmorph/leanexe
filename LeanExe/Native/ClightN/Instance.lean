import LeanExe.Native.ClightN.Reads
import LeanExe.Native.Proof.Main

/-!
What the instances of `clightn/check.sh` share: decidable equality of the copy's syntax, so that
the kernel compares a program it computes with the definitions of a Coq file, and the renaming
from a whole program to the file's program.  The renaming reads the file's identifiers off the
two lists of definitions, which list the same definitions in the same order: a global's
identifier at its position, and a temporary's at its position among a function's parameters and
temporaries.  `preOf` gives CompCert's declarations the identifiers of the whole program, and
`inj_of_nodup_map` reduces injectivity on a list to the absence of repetitions in its image, a
check in proportion to the list's length.
-/

namespace ClightN.Proof

open LClight LeanExe.Native

deriving instance DecidableEq for LClight.expr
deriving instance DecidableEq for LClight.statement, LClight.labeled_statements
deriving instance DecidableEq for LClight.function
deriving instance DecidableEq for LClight.fundef
deriving instance DecidableEq for LClight.globvar
deriving instance DecidableEq for LClight.globdef

/-- CompCert's declarations with the identifiers that the whole program gives them:
`__builtin_fsqrt` takes `sqrtId`, and the `j`-th of the others `4 j + 5`. -/
def preOf : Defs → Nat → Defs
  | [], _ => []
  | (_, d) :: rest, j =>
      if d = sqrtDef then (sqrtId, d) :: preOf rest j
      else (4 * j + 5, d) :: preOf rest (j + 1)

/-- The identifier in the definitions `fd` of each global of the definitions `wd`, by position. -/
def gOfL (wd fd : Defs) (x : ident) : ident :=
  (((wd.map (·.1)).zip (fd.map (·.1))).lookup x).getD x

/-- The identifier in `fd` of each temporary of the function `fid` of `wd`, by position. -/
def tempsZipL (wd fd : Defs) (fid : ident) : List (ident × ident) :=
  match wd.lookup fid, fd.lookup (gOfL wd fd fid) with
  | some (.Gfun (.Internal f)), some (.Gfun (.Internal f')) =>
      ((f.fn_params ++ f.fn_temps).map (·.1)).zip ((f'.fn_params ++ f'.fn_temps).map (·.1))
  | _, _ => []

def tOfL (wd fd : Defs) (fid x : ident) : ident := ((tempsZipL wd fd fid).lookup x).getD x

/-- The parameters and temporaries that the function `fid` of `wd` declares. -/
def declOfL (wd : Defs) (fid : ident) : List ident :=
  match wd.lookup fid with
  | some (.Gfun (.Internal f)) => (f.fn_params ++ f.fn_temps).map (·.1)
  | _ => []

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

/-- The renaming of temporaries is injective on each function's temporaries when it is on the
declared ones of each identifier of the program. -/
theorem tinj_of {p : program function} {τ : ident → ident → ident}
    (hsub : ∀ id ∈ p.prog_defs.map (·.1), ∀ x ∈ tempsOf p.prog_defs id, x ∈ declOfL p.prog_defs id)
    (hnd : ∀ id ∈ p.prog_defs.map (·.1), ((declOfL p.prog_defs id).map (τ id)).Nodup) :
    ∀ id, ∀ x ∈ tempsOf p.prog_defs id, ∀ y ∈ tempsOf p.prog_defs id,
      τ id x = τ id y → x = y := by
  intro id
  by_cases hid : id ∈ p.prog_defs.map (·.1)
  · exact fun x hx y hy e => inj_of_nodup_map (hnd id hid) x (hsub id hid x hx) y
      (hsub id hid y hy) e
  · have : tempsOf p.prog_defs id = [] := by
      simp only [tempsOf, List.flatMap_eq_nil_iff, List.mem_filter, beq_iff_eq, and_imp]
      intro d hd e
      exact absurd (e ▸ List.mem_map_of_mem (f := (·.1)) hd) hid
    simp [this]

/-- The declarations of `pre` that `PrefixOk` requires to be functions. -/
theorem prefix_of {pre : Defs} (hsq : (sqrtId, sqrtDef) ∈ pre)
    (hf : pre.all (fun d => match d.2 with | .Gfun _ => true | .Gvar _ => false) = true)
    (hnd : (pre.map (·.1)).Nodup)
    (hids : ∀ x : Nat, x ∈ pre.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1)) : PrefixOk pre := by
  refine ⟨hsq, fun d hd => ?_, hnd, hids⟩
  have := List.all_eq_true.mp hf d hd
  match d, this with
  | (_, .Gfun f), _ => exact ⟨f, rfl⟩
  | (_, .Gvar _), h => simp at h

end ClightN.Proof
