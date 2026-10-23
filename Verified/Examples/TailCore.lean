import Verified.Examples.TailModel
import Verified.Correct

namespace Verified.Examples.TailCore

open TailModel

def growNative (n : UInt64) (xs weights : Array UInt64) : Array UInt64 :=
  if n = 0 then xs
  else growNative (n - 1) (xs.push weights[(n - 1).toNat]!) weights
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def growMeaning (env : Env growParams) : Array UInt64 :=
  growNative (env.get (Var.ofIndex _ 0 rfl)) (env.get (Var.ofIndex _ 1 rfl))
    (env.get (Var.ofIndex _ 2 rfl))

theorem grow_fixed (env : Env growParams) :
    growMeaning env = (growBody.denote .nil env).elim growMeaning id := by
  cases env with
  | cons n rest =>
    cases rest with
    | cons xs rest =>
      cases rest with
      | cons weights rest =>
        cases rest
        change growNative n xs weights = _
        rw [grow_step, growNative.eq_def]
        by_cases hn : n = 0 <;> simp only [beq_iff_eq, hn, ↓reduceIte,
          Sum.elim_inl, Sum.elim_inr, id_eq] <;> rfl

def prog : Prog [grow.sig] := .consTail grow .nil

def funs : Funs [grow.sig] := .cons growMeaning .nil

theorem meaning : prog.Meaning funs :=
  Prog.Meaning.consTail (f := grow) (rest := .nil) (funs := .nil)
    growMeaning .nil grow_decreases grow_fixed

def module : Wasm.Module := compile prog

theorem grow_correct : FunSpec module grow.sig 2 growMeaning
    (prog.flags.params .here) (prog.flags.result .here)
    ((prog.boundsAt funs (framesAt 0)).get .here)
    ((prog.fitsAt funs (framesAt 0)).get .here) (fun d => d = 0) :=
  Prog.correct prog funs meaning (by decide +kernel) .here 0

#print axioms grow_correct

end Verified.Examples.TailCore
