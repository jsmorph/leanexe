import TestSupport.Native.Gcd
import TestSupport.Native.Common

/-!
The theorems of the translated GCD functions, with `lx_mem` of `cap` pages.  `loop_native` and
`rec_native` carry the verified compiler's theorems `loopCompiled.gcd.implements` and
`recCompiled.gcd.implements` to the C functions of the translations, as `NativeImpl` states.
`loop_native_init` and `rec_native_init` call `lxf_gcd` from the state that `lx_init` leaves
in the translated program's initial memory: the loop returns `gcd a b` with `lx_status` 0, and
the recursion does too or ends with `lx_status` set to the code of `unreachable`.
-/

namespace TestSupport.Native.Gcd

open Wasm LClight LeanExe.Native LeanExe.Pipeline TestSupport.Native

/-- The translation of the loop GCD. -/
def loopT : Translation := (translate cap loopCompiled.module).get (by decide +kernel)

theorem loopT_eq : translate cap loopCompiled.module = some loopT := (Option.some_get _).symm

attribute [irreducible] loopT

/-- The translation of the recursive GCD. -/
def recT : Translation := (translate cap recCompiled.module).get (by decide +kernel)

theorem recT_eq : translate cap recCompiled.module = some recT := (Option.some_get _).symm

attribute [irreducible] recT

/-- The translations contain the runtime's `alloc` and `release` and the GCD functions. -/
theorem loop_funcs : loopT.funcs = [0, 1, 2] := by decide +kernel

theorem rec_funcs : recT.funcs = [0, 1, 2, 3] := by decide +kernel

theorem loop_native (A : Archi) (X : ExtSem) : NativeImpl loopCompiled.gcd.implements A X cap loopT :=
  ImplementsA.nativeImpl _ loopT_eq (by decide +kernel)

theorem rec_native (A : Archi) (X : ExtSem) : NativeImpl recCompiled.gcd.implements A X cap recT :=
  ImplementsA.nativeImpl _ recT_eq (by decide +kernel)

/-- From the state that `lx_init` leaves, `lxf_gcd` on `a` and `b` returns `gcd a b` with
`lx_status` 0. -/
theorem loop_native_init (A : Archi) (X : ExtSem) (a b : UInt64) :
    ∃ m1 fd t m', StoreRel (envOf loopT loopCompiled.module.globals.length cap) (nativeStore loopCompiled.module cap) m1 ∧
      (funId 2, globdef.Gfun (fundef.Internal fd)) ∈ loopT.cprogram.prog_defs ∧
      eval_funcall A X (globalenv loopT.cprogram) m1 (.Internal fd) [.Vlong a, .Vlong b] t m'
        (.Vlong (gcd a b)) ∧ StatusRel (envOf loopT loopCompiled.module.globals.length cap) m' 0 := by
  obtain ⟨-, -, m1, -, -, -, -, hst, hs, hE, hG, hcap, hF⟩ := start loopT_eq A X
  obtain ⟨fd, ps, r, hfd, hsig, hnat⟩ := loop_native A X
  obtain ⟨rfl, rfl⟩ := sig_of hsig (ps0 := [.i64, .i64]) (r0 := some .i64) rfl
  obtain ⟨hheap, -, -⟩ := loopCompiled.initial
  obtain ⟨t, m', vres, final, hcall, -, hres⟩ := hnat _ hE hG hcap hF
    (nativeStore loopCompiled.module cap) _ [.i64 a, .i64 b] (a, b) (heapAt_caps hheap [cap]) trivial
    (by first | rfl | exact ⟨[.i64 a], [.i64 b], rfl, rfl, rfl⟩)
    (by first | exact Separate.nil | exact ⟨.nil, fun _ h => by simp at h⟩)
    (by rw [nativeStore_memoryCap]; decide) ⟨by simp, by simp [AllHas, VT.has]⟩ m1 hst hs
  have hge : (envOf loopT loopCompiled.module.globals.length cap).ge = globalenv loopT.cprogram :=
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
    ∃ m1 fd t m' vres, StoreRel (envOf recT recCompiled.module.globals.length cap) (nativeStore recCompiled.module cap) m1 ∧
      (funId 3, globdef.Gfun (fundef.Internal fd)) ∈ recT.cprogram.prog_defs ∧
      eval_funcall A X (globalenv recT.cprogram) m1 (.Internal fd) [.Vlong a, .Vlong b] t m' vres ∧
      ((vres = .Vlong (gcd a b) ∧ StatusRel (envOf recT recCompiled.module.globals.length cap) m' 0) ∨
        StatusRel (envOf recT recCompiled.module.globals.length cap) m' trapUnreachable) := by
  obtain ⟨-, -, m1, -, -, -, -, hst, hs, hE, hG, hcap, hF⟩ := start recT_eq A X
  obtain ⟨fd, ps, r, hfd, hsig, hnat⟩ := rec_native A X
  obtain ⟨rfl, rfl⟩ := sig_of hsig (ps0 := [.i64, .i64]) (r0 := some .i64) rfl
  obtain ⟨hheap, -, -⟩ := recCompiled.initial
  obtain ⟨t, m', vres, final, hcall, -, hres⟩ := hnat _ hE hG hcap hF
    (nativeStore recCompiled.module cap) _ [.i64 a, .i64 b] (a, b) (heapAt_caps hheap [cap]) trivial
    (by first | rfl | exact ⟨[.i64 a], [.i64 b], rfl, rfl, rfl⟩)
    (by first | exact Separate.nil | exact ⟨.nil, fun _ h => by simp at h⟩)
    (by rw [nativeStore_memoryCap]; decide) ⟨by simp, by simp [AllHas, VT.has]⟩ m1 hst hs
  have hge : (envOf recT recCompiled.module.globals.length cap).ge = globalenv recT.cprogram :=
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
