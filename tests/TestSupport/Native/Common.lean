import Verified.Native
import Verified.Instantiate

/-!
What the translator's tests share: the number of pages `cap` of `lx_mem` and `start`, the state
from which a translated program's functions are called.  `start` runs `lx_init` from the
program's initial memory and relates the result to `nativeStore`, Talos's initial store with the
memory's cap set to `cap`, in the environment `envOf` of the program's own global environment,
which meets every hypothesis on the environment of `NativeA`.  `heapAt_caps` and `borrowed_caps`
carry the verified compiler's instantiation theorem `p.initial` to `nativeStore`.
-/

namespace TestSupport.Native

open Wasm LClight LeanExe.Native LeanExe.Pipeline

/-- The pages of `lx_mem` in the tests: those of the translations that `verified_compile`
adds. -/
abbrev cap : Nat := LeanExe.Native.nativeCap

theorem heapAt_caps {heap : Heap} {store : Store Unit} (h : heap.At store) (caps : List Nat) :
    heap.At { store with memoryCaps := caps } :=
  ⟨h.globals, h.freeList, h.base, h.top, h.pages, h.above, h.below⟩

theorem borrowed_caps {heap : Heap} {store : Store Unit} {ptr : UInt64} {words : Array UInt64}
    (h : heap.Borrowed store ptr words) (caps : List Nat) :
    heap.Borrowed { store with memoryCaps := caps } ptr words :=
  ⟨h.values, h.below, h.separate⟩

/-- The parameters and results of a function, from their computed values. -/
theorem sig_of {mod : Module} {k : Nat} {ps ps0 rs rs0 : List VT}
    (hsig : ∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs))
    (h0 : (mod.funcs[k]?).bind signatureOf = some (ps0, rs0)) : ps = ps0 ∧ rs = rs0 := by
  cases hk : mod.funcs[k]? with
  | none => rw [hk] at h0; cases h0
  | some g =>
      rw [hk] at h0
      rw [show (some g).bind signatureOf = signatureOf g from rfl, hsig g hk] at h0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h0)
      exact ⟨rfl, rfl⟩

theorem nativeStore_memoryCap (m : Module) (cap : Nat) : (nativeStore m cap).memoryCap m 0 = cap :=
  rfl

/-- The state from which the functions of a translated program are called: `init_mem` gives
`m0`, and `lx_init` from `m0` gives `m1`, which `envOf`, which meets the hypotheses on the
environment of `NativeA`, relates to `nativeStore` with `lx_status` 0. -/
theorem start {m : Module} {T : Translation} (h : translate cap m = some T) (A : Archi)
    (X : ExtSem) :
    ∃ decl m0 m1, m.memory = some decl ∧ init_mem T.cprogram = some m0 ∧
      (initId, globdef.Gfun (.Internal (initFunction cap decl.data))) ∈ T.cprogram.prog_defs ∧
      eval_funcall A X (globalenv T.cprogram) m0 (.Internal (initFunction cap decl.data)) [] E0
        m1 .Vundef ∧
      StoreRel (envOf T m.globals.length cap) (nativeStore m cap) m1 ∧
      StatusRel (envOf T m.globals.length cap) m1 0 ∧
      EnvOk (envOf T m.globals.length cap) ∧
      (envOf T m.globals.length cap).globals.length = m.globals.length ∧
      (envOf T m.globals.length cap).cap = cap ∧ T.nres ≤ (envOf T m.globals.length cap).nres ∧
      (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
        ∃ b, Genv.find_symbol (envOf T m.globals.length cap).ge (funId k) = some b ∧
          Genv.find_funct_ptr (envOf T m.globals.length cap).ge b = some (.Internal fd)) := by
  obtain ⟨decl, m0, hdecl, hinit, hE, hmem, hrun⟩ := lx_init_correct h
  obtain ⟨m1, hcall, hst, hs⟩ := hrun A X
  exact ⟨decl, m0, m1, hdecl, hinit, hmem, hcall, hst, hs, hE, by simp [envOf], rfl,
    Nat.le_refl _, funcs_found h⟩

end TestSupport.Native
