import LeanExe.Native.Proof.Native
import Verified.Instantiate
import Verified.Correct

/-!
What the translator's tests share: the number of pages `cap` of `lx_mem`, the form `NativeTablesA`
of `NativeA` for a wrapper whose theorem is `ImplementsTables`, and `start`, the state from
which a translated program's functions are called.  `start` runs `lx_init` from the program's
initial memory and relates the result to `nativeStore`, Talos's initial store with the memory's
cap set to `cap`, in the environment `envOf` of the program's own global environment, which
meets every hypothesis on the environment of `NativeA`.  `heapAt_caps` and `borrowed_caps`
carry the verified compiler's instantiation theorem `p.initial` to `nativeStore`.
-/

namespace TestSupport.Native

open Wasm LClight LeanExe.Native LeanExe.Pipeline

/-- The pages of `lx_mem` in the tests. -/
def cap : Nat := 256

/-- `NativeA` for a wrapper, whose premises add that the tables `tables` are borrowed and apart
from the arrays that the call consumes. -/
def NativeTablesA {α β : Type} [Represent α] [Represent β] (A : Archi) (X : ExtSem) (cap : Nat)
    (mod : Module) (T : Translation) (k : Nat) (ps : List VT) (r : Option VT) (fd : function)
    (aborts : Bool) (f : α → β) (tables : List (UInt64 × Array UInt64))
    (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (E : Env), EnvOk E → E.globals.length = mod.globals.length → E.cap = cap →
    (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd)) →
    ∀ (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
      heap.At store → Pre x heap store →
      (∀ t ∈ tables, heap.Borrowed store t.1 t.2 ∧
        Apart store (Represent.moves store params x) (t.1.toNat, 8 * (t.2.size + 1))) →
      Represent.borrowed heap store params x →
      Separate store (Represent.moves store params x) (Represent.reads store params x) →
      store.memoryCap mod 0 ≤ 65535 → ArgsTyped ps params.reverse →
      ∀ m, StoreRel E store m → StatusRel E m 0 →
      ∃ t m' vres final, eval_funcall A X E.ge m (.Internal fd) (argVals ps params.reverse) t m'
          vres ∧ StoreRel E final m' ∧
        ((StatusRel E m' 0 ∧ ∃ (vs : List Value) (heap' : Heap),
            ResultRel r vs (params.reverse.drop ps.length) vres ∧
            heap'.At final ∧ Represent.owned heap' final vs.reverse (f x) ∧
            Post x heap store heap' final) ∨
          (aborts = true ∧ StatusRel E m' trapUnreachable))

/-- The translation of the wrapper of the theorem `h` computes its function as `h` states. -/
def NativeTablesImpl {α β : Type} [Represent α] [Represent β] {aborts : Bool} {mod : Module}
    {k : Nat} {f : α → β} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (_h : Verified.ImplementsTables aborts mod k f tables Pre Post) (A : Archi) (X : ExtSem)
    (cap : Nat) (T : Translation) : Prop :=
  ∃ fd ps r, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
    (∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, r)) ∧
    NativeTablesA A X cap mod T k ps r fd aborts f tables Pre Post

theorem ImplementsTables.nativeImpl {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : Verified.ImplementsTables aborts mod k f tables Pre Post) {cap : Nat} {T : Translation}
    (hT : translate cap mod = some T) (hk : k ∈ T.funcs) : NativeTablesImpl h A X cap T := by
  obtain ⟨fd, ps, r, hfd, hsig⟩ := translate_sig hT hk
  refine ⟨fd, ps, r, hfd, hsig, ?_⟩
  intro E hE hG hcap hF store heap params x hHeap hPre hTables hArgs hSep hCapS htyped m hst hs
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := Runs.native (A := A) (X := X) hT hE hG hcap hF
    hfd hsig (h {} store heap params x hHeap hPre hTables hArgs hSep hCapS) htyped hst hs
  refine ⟨t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨heap', hAt, hOwn, -, -, hPost⟩, hr⟩ | habort
  · exact .inl ⟨hs', vs, heap', hr, hAt, hOwn, hPost⟩
  · exact .inr habort

theorem heapAt_caps {heap : Heap} {store : Store Unit} (h : heap.At store) (caps : List Nat) :
    heap.At { store with memoryCaps := caps } :=
  ⟨h.globals, h.freeList, h.base, h.top, h.pages, h.above, h.below⟩

theorem borrowed_caps {heap : Heap} {store : Store Unit} {ptr : UInt64} {words : Array UInt64}
    (h : heap.Borrowed store ptr words) (caps : List Nat) :
    heap.Borrowed { store with memoryCaps := caps } ptr words :=
  ⟨h.values, h.below, h.separate⟩

/-- The parameters and result of a function, from their computed values. -/
theorem sig_of {mod : Module} {k : Nat} {ps ps0 : List VT} {r r0 : Option VT}
    (hsig : ∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, r))
    (h0 : (mod.funcs[k]?).bind signatureOf = some (ps0, r0)) : ps = ps0 ∧ r = r0 := by
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
      (envOf T m.globals.length cap).cap = cap ∧
      (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
        ∃ b, Genv.find_symbol (envOf T m.globals.length cap).ge (funId k) = some b ∧
          Genv.find_funct_ptr (envOf T m.globals.length cap).ge b = some (.Internal fd)) := by
  obtain ⟨decl, m0, hdecl, hinit, hE, hmem, hrun⟩ := lx_init_correct h
  obtain ⟨m1, hcall, hst, hs⟩ := hrun A X
  exact ⟨decl, m0, m1, hdecl, hinit, hmem, hcall, hst, hs, hE, by simp [envOf], rfl, funcs_found h⟩

end TestSupport.Native
