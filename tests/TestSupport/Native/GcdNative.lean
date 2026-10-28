import TestSupport.Native.Gcd
import TestSupport.Native.Common

/-!
The theorems of the translated GCD functions, with `lx_mem` of `cap` pages.  `verified_compile`
adds the translations and the theorems `loopCompiled.gcd.native` and `recCompiled.gcd.native`,
which carry the verified compiler's theorems to the C functions of the translations, as
`NativeImpl` states.  `loop_native_init` and `rec_native_init` call `lxf_gcd` from the state
that `lx_init` leaves in the translated program's initial memory: the loop returns `gcd a b`
with `lx_status` 0, and the recursion does too or ends with `lx_status` set to the code of
`unreachable`.
-/

namespace TestSupport.Native.Gcd

open Wasm LClight LeanExe.Native LeanExe.Pipeline TestSupport.Native

/-- The translations contain the runtime's `alloc` and `release` and the GCD functions. -/
theorem loop_funcs : loopCompiled.translation.funcs = [0, 1, 2] :=
  translate_funcs_eq loopCompiled.translation_eq loopCompiled.translation_funcs

theorem rec_funcs : recCompiled.translation.funcs = [0, 1, 2, 3] :=
  translate_funcs_eq recCompiled.translation_eq recCompiled.translation_funcs

/-- From the state that `lx_init` leaves, `lxf_gcd` on `a` and `b` returns `gcd a b` with
`lx_status` 0. -/
theorem loop_native_init (A : Archi) (X : ExtSem) (a b : UInt64) :
    ∃ m1 fd t m', StoreRel (envOf loopCompiled.translation loopCompiled.module.globals.length cap) (nativeStore loopCompiled.module cap) m1 ∧
      (funId 2, globdef.Gfun (fundef.Internal fd)) ∈ loopCompiled.translation.cprogram.prog_defs ∧
      eval_funcall A X (globalenv loopCompiled.translation.cprogram) m1 (.Internal fd) [.Vlong a, .Vlong b] t m'
        (.Vlong (gcd a b)) ∧ StatusRel (envOf loopCompiled.translation loopCompiled.module.globals.length cap) m' 0 := by
  obtain ⟨-, -, m1, -, -, -, -, hst, hs, hE, hG, hcap, hnres, hF⟩ := start loopCompiled.translation_eq A X
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := loopCompiled.gcd.native A X
  obtain ⟨rfl, rfl⟩ := sig_of hsig (ps0 := [.i64, .i64]) (rs0 := [.i64]) rfl
  obtain ⟨hheap, -, -⟩ := loopCompiled.initial
  obtain ⟨t, m', vres, final, hcall, -, hres⟩ := hnat _ hE hG hcap hnres hF
    (nativeStore loopCompiled.module cap) _ [.i64 a, .i64 b] (a, b) (heapAt_caps hheap [cap]) trivial
    (by rfl)
    Separate.nil
    (by rw [nativeStore_memoryCap]; decide) ⟨by simp, by simp [AllHas, VT.has]⟩ m1 hst hs
  have hge : (envOf loopCompiled.translation loopCompiled.module.globals.length cap).ge = globalenv loopCompiled.translation.cprogram :=
    rfl
  have hargs : argVals [.i64, .i64] [Value.i64 a, .i64 b].reverse = [.Vlong a, .Vlong b] := rfl
  rw [hge, hargs] at hcall
  rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | ⟨habs, -⟩
  · obtain ⟨v, rfl, -, rfl⟩ := hr
    have hv : [v].reverse = [Value.i64 (gcd a b)] := hown
    simp at hv
    subst hv
    exact ⟨m1, fd, t, m', hst, hfd, hcall, hs'⟩
  · cases habs

/-- From the state that `lx_init` leaves, `lxf_gcd` on `a` and `b` returns `gcd a b` with
`lx_status` 0, or ends with `lx_status` set to the code of `unreachable`. -/
theorem rec_native_init (A : Archi) (X : ExtSem) (a b : UInt64) :
    ∃ m1 fd t m' vres, StoreRel (envOf recCompiled.translation recCompiled.module.globals.length cap) (nativeStore recCompiled.module cap) m1 ∧
      (funId 3, globdef.Gfun (fundef.Internal fd)) ∈ recCompiled.translation.cprogram.prog_defs ∧
      eval_funcall A X (globalenv recCompiled.translation.cprogram) m1 (.Internal fd) [.Vlong a, .Vlong b] t m' vres ∧
      ((vres = .Vlong (gcd a b) ∧ StatusRel (envOf recCompiled.translation recCompiled.module.globals.length cap) m' 0) ∨
        StatusRel (envOf recCompiled.translation recCompiled.module.globals.length cap) m' trapUnreachable) := by
  obtain ⟨-, -, m1, -, -, -, -, hst, hs, hE, hG, hcap, hnres, hF⟩ := start recCompiled.translation_eq A X
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := recCompiled.gcd.native A X
  obtain ⟨rfl, rfl⟩ := sig_of hsig (ps0 := [.i64, .i64]) (rs0 := [.i64]) rfl
  obtain ⟨hheap, -, -⟩ := recCompiled.initial
  obtain ⟨t, m', vres, final, hcall, -, hres⟩ := hnat _ hE hG hcap hnres hF
    (nativeStore recCompiled.module cap) _ [.i64 a, .i64 b] (a, b) (heapAt_caps hheap [cap]) trivial
    (by rfl)
    Separate.nil
    (by rw [nativeStore_memoryCap]; decide) ⟨by simp, by simp [AllHas, VT.has]⟩ m1 hst hs
  have hge : (envOf recCompiled.translation recCompiled.module.globals.length cap).ge = globalenv recCompiled.translation.cprogram :=
    rfl
  have hargs : argVals [.i64, .i64] [Value.i64 a, .i64 b].reverse = [.Vlong a, .Vlong b] := rfl
  rw [hge, hargs] at hcall
  rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | ⟨-, htrap⟩
  · obtain ⟨v, rfl, -, rfl⟩ := hr
    have hv : [v].reverse = [Value.i64 (gcd a b)] := hown
    simp at hv
    subst hv
    exact ⟨m1, fd, t, m', _, hst, hfd, hcall, .inl ⟨rfl, hs'⟩⟩
  · exact ⟨m1, fd, t, m', vres, hst, hfd, hcall, .inr htrap⟩

end TestSupport.Native.Gcd
