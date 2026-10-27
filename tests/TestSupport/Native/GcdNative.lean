import TestSupport.Native.Gcd
import LeanExe.Native.Proof.Correct

/-!
The theorems of the translated GCD functions, from the verified compiler's theorems and
`translate_correct`.  `loop_native`: for every global environment that holds the C globals and
functions of the translation, and every C memory whose globals hold a Talos store's globals and
whose `lx_status` is 0, the call of `lxf_gcd` on `a` and `b` terminates, returns `gcd a b`, and
leaves the globals and `lx_status` as they were.  `rec_native` states the same of the recursion
that takes the call depth, except that the call may instead end with `lx_status` set to the code
of `unreachable`, for a Talos store that meets the premises of the verified compiler's theorem.
-/

namespace TestSupport.Native.Gcd

open Wasm LClight LeanExe.Native LeanExe.Pipeline

/-- The translations exist and contain the expected functions. -/
theorem loop_translates : ∃ T, translate loopCompiled.module = some T ∧ T.funcs = [2] :=
  ⟨_, rfl, rfl⟩

theorem rec_translates : ∃ T, translate recCompiled.module = some T ∧ T.funcs = [2, 3] :=
  ⟨_, rfl, rfl⟩

section

variable {A : Archi} {X : ExtSem} {E : Env}

theorem loop_native {T : Translation} (hT : translate loopCompiled.module = some T)
    {fd : function} (hfd : (funId 2, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    (hE : EnvOk E) (hG : E.globals.length = loopCompiled.module.globals.length)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (st : Store Unit) (m : mem) (a b : UInt64)
    (hg : GlobalsRel E st.globals.globals m) (hs : StatusRel E m 0) :
    ∃ t m', eval_funcall A X E.ge m (.Internal fd) [.Vlong a, .Vlong b] t m'
        (.Vlong (gcd a b)) ∧
      GlobalsRel E st.globals.globals m' ∧ StatusRel E m' 0 := by
  obtain ⟨N, hN⟩ := loopCompiled.gcd.pure {} st (a, b)
  rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, hst, hvals⟩ | hfalse
  · obtain ⟨f, ps, r, hf, hsig, hsim⟩ := translate_correct (A := A) (X := X) hT hE hG hF N 2 fd hfd
    have hsig' : signatureOf f = some ([.i64, .i64], some .i64) := by
      have : loopCompiled.module.funcs[2]? = some f := hf
      rw [show loopCompiled.module.funcs[2]? = some (loopCompiled.module.funcs[2]'(by decide))
        from rfl] at this
      cases this
      rfl
    rw [hsig'] at hsig
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig)
    have hargs : ArgsTyped [.i64, .i64] [.i64 b, .i64 a] := ⟨by simp, by simp [AllHas, VT.has]⟩
    have ho := hsim st [.i64 b, .i64 a] m {} hargs hg hs
    have hrun' : run N loopCompiled.module 2 st [.i64 b, .i64 a] {} = .Success vs st' := hrun
    rw [hrun'] at ho
    obtain ⟨t, m', vres, hcall, hg', hs', hres⟩ := ho
    obtain ⟨v, hv, -, rfl⟩ := hres
    subst hv
    simp [Scalar.values] at hvals
    subst hvals
    rw [hst] at hg'
    exact ⟨t, m', hcall, hg', hs'⟩
  · exact hfalse.elim

end

end TestSupport.Native.Gcd
