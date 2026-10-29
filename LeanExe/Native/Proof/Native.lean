import LeanExe.Native.Proof.Init
import LeanExe.Pipeline.Implements
import LeanExe.Pipeline.RuntimeSpec

/-!
The step from Talos's theorems to the translated functions.  `Runs.native` combines a `Runs`
statement, the form in which the verified compiler's `ImplementsA` and `ImplementsTables`
theorems conclude, with `translate_correct`: the C call of the translation terminates, its
final memory is related to a final Talos store, and either the call returns with `lx_status` 0
and Talos's results satisfy the postcondition and are related to the C result, or the
function may abort and `lx_status` holds the code of `unreachable`.

`NativeA` states this for a function that the verified compiler proves with `ImplementsA`, in
the terms of that theorem: for every global environment that holds the translation's globals,
memory, and functions, every store and heap that meet the premises of `ImplementsA`, and every
C memory related to the store with `lx_status` 0, the C call of the translation of entry `k`
terminates, and either returns with `lx_status` 0 and a result related to Talos's results,
which represent `f x` in a heap that meets the allocator invariant and the postcondition, or,
when `aborts`, ends with `lx_status` holding the code of `unreachable`.  `ImplementsA.native`
derives it from `ImplementsA`.  `NativeImpl h` states it for the translation of the function of
the theorem `h`, under the function's parameters and result, and `ImplementsA.nativeImpl`
derives it from `h` and the presence of the function in the translation.

`alloc_native` and `release_native` carry the runtime's theorems `alloc_spec_runs` and
`release_run` to the C functions `lxf_alloc` and `lxf_release` of a translated module.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## From Talos's theorems to the C functions -/

section

variable {A : Archi} {X : ExtSem}

/-- A function of a translated program whose runs return values satisfying `P` or, when
`aborts`, trap at `unreachable`, from a store related to the C memory `m`: the C call of its
translation terminates, with a final store `st'` related to the final memory, and either
`lx_status` is 0 and Talos's results `vs` satisfy `P st' vs` and are related to the C result,
or `aborts` holds and `lx_status` holds the code of `unreachable`. -/
theorem Runs.native {mod : Module} {cap : Nat} {T : Translation} (hT : translate cap mod = some T)
    {E : Env} (hE : EnvOk E) (hG : E.globals.length = mod.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    {k : Nat} {fd : function} (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    {ps rs : List VT}
    (hsig : ∀ f, mod.funcs[k]? = some f → signatureOf f = some (ps, rs))
    {aborts : Bool} {env : HostEnv Unit} {st : Store Unit} {args : List Value}
    {P : Store Unit → List Value → Prop} (hrun : Runs aborts env mod k st args P)
    (htyped : ArgsTyped ps args) {m : mem} (hst : StoreRel E st m) (hs : StatusRel E m 0) :
    ∃ t m' vres st', eval_funcall A X E.ge m (.Internal fd) (argVals ps args) t m' vres ∧
      StoreRel E st' m' ∧
      ((StatusRel E m' 0 ∧ ∃ vs, P st' vs ∧ ResultRel E rs vs (args.drop ps.length) vres m') ∨
        (aborts = true ∧ StatusRel E m' trapUnreachable)) := by
  obtain ⟨N, hN⟩ := hrun
  obtain ⟨f, ps', r', hf, hsig', hsim⟩ :=
    translate_correct (A := A) (X := X) hT hE hG hcap hnres hF N k fd hfd
  rw [hsig f hf] at hsig'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig')
  have ho := hsim st args m env htyped hst hs nofun
  rcases hN N (Nat.le_refl _) with ⟨vs, st', hr, hP⟩ | htr
  · rw [hr] at ho
    obtain ⟨t, m', vres, hcall, hst', hs', hres⟩ := ho
    exact ⟨t, m', vres, st', hcall, hst', .inl ⟨hs', vs, hP, hres⟩⟩
  · cases aborts with
    | false => exact htr.elim
    | true =>
        obtain ⟨st', hr⟩ := htr
        rw [hr] at ho
        obtain ⟨t, m', vres, hcall, hst', hs', -⟩ := ho
        exact ⟨t, m', vres, st', hcall, hst', .inr ⟨rfl, by rw [trapCode_unreachable] at hs'; exact hs'⟩⟩

end

open LeanExe.Pipeline in
/-- The C function `fd` of the translation `T` of `mod`, with parameters `ps` and results `rs`,
computes `f` as `ImplementsA aborts mod k f Pre Post` states for the function `k` that `fd`
translates. -/
def NativeA {α β : Type} [Represent α] [Represent β] (A : Archi) (X : ExtSem) (cap : Nat)
    (mod : Module) (T : Translation) (ps rs : List VT) (fd : function)
    (aborts : Bool) (f : α → β) (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (E : Env), EnvOk E → E.globals.length = mod.globals.length → E.cap = cap →
    T.nres ≤ E.nres → (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd)) →
    ∀ (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
      heap.At store → Pre x heap store → Represent.borrowed heap store params x →
      Separate store (Represent.moves store params x) (Represent.reads store params x) →
      store.memoryCap mod 0 ≤ 65535 → ArgsTyped ps params.reverse →
      ∀ m, StoreRel E store m → StatusRel E m 0 →
      ∃ t m' vres final, eval_funcall A X E.ge m (.Internal fd) (argVals ps params.reverse) t m'
          vres ∧ StoreRel E final m' ∧
        ((StatusRel E m' 0 ∧ ∃ (vs : List Value) (heap' : Heap),
            ResultRel E rs vs (params.reverse.drop ps.length) vres m' ∧
            heap'.At final ∧ Represent.owned heap' final vs.reverse (f x) ∧
            Post x heap store heap' final) ∨
          (aborts = true ∧ StatusRel E m' trapUnreachable))

open LeanExe.Pipeline in
theorem ImplementsA.native {α β : Type} [Represent α] [Represent β] {A : Archi} {X : ExtSem}
    {aborts : Bool} {mod : Module} {k : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts mod k f Pre Post) {cap : Nat} {T : Translation}
    (hT : translate cap mod = some T) {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    {ps rs : List VT}
    (hsig : ∀ f, mod.funcs[k]? = some f → signatureOf f = some (ps, rs)) :
    NativeA A X cap mod T ps rs fd aborts f Pre Post := by
  intro E hE hG hcap hnres hF store heap params x hHeap hPre hArgs hSep hCapS htyped m hst hs
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := Runs.native (A := A) (X := X) hT hE hG hcap
    hnres hF
    hfd hsig (h {} store heap params x hHeap hPre hArgs hSep hCapS) htyped hst hs
  refine ⟨t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨heap', hAt, hOwn, -, -, hPost⟩, hr⟩ | habort
  · exact .inl ⟨hs', vs, heap', hr, hAt, hOwn, hPost⟩
  · exact .inr habort

open LeanExe.Pipeline in
/-- The translation of the entry of the theorem `h` computes its function as `h` states, under
the function's parameters `ps` and results `rs`. -/
def NativeImpl {α β : Type} [Represent α] [Represent β] {aborts : Bool} {mod : Module} {k : Nat}
    {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (_h : ImplementsA aborts mod k f Pre Post) (A : Archi) (X : ExtSem) (cap : Nat)
    (T : Translation) : Prop :=
  ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
    (∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
    NativeA A X cap mod T ps rs fd aborts f Pre Post

/-- The signature of a function of a translation. -/
theorem translate_sig {mod : Module} {cap : Nat} {al : Bool} {T : Translation}
    (hT : translate cap mod al = some T)
    {k : Nat} (hk : k ∈ T.funcs) :
    ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
      ∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs) := by
  obtain ⟨fd, hfd⟩ := translate_funcs hT hk
  obtain ⟨-, -, hfuns⟩ := translate_spec hT
  obtain ⟨g, hg, -, htr, -⟩ := hfuns k fd hfd
  obtain ⟨ps, rs, hsig, -⟩ := trFunction_sig htr
  exact ⟨fd, ps, rs, hfd, fun g' hg' => by rw [hg] at hg'; cases hg'; exact hsig⟩

/-- A translation exists when its list of functions does. -/
theorem translate_isSome {mod : Module} {cap : Nat} {L : List Nat}
    (h : (translate cap mod).map Translation.funcs = some L) : (translate cap mod).isSome = true := by
  cases hT : translate cap mod with
  | none => rw [hT] at h; cases h
  | some _ => rfl

/-- The functions of a translation, from the list that `(translate cap mod).map funcs` gives. -/
theorem translate_mem_funcs {mod : Module} {cap : Nat} {T : Translation} {L : List Nat}
    (hT : translate cap mod = some T) (h : (translate cap mod).map Translation.funcs = some L)
    {k : Nat} (hk : k ∈ L) : k ∈ T.funcs := by
  rw [hT] at h
  cases h
  exact hk

theorem translate_funcs_eq {mod : Module} {cap : Nat} {T : Translation} {L : List Nat}
    (hT : translate cap mod = some T) (h : (translate cap mod).map Translation.funcs = some L) :
    T.funcs = L := by
  rw [hT] at h
  cases h
  rfl

open LeanExe.Pipeline in
theorem ImplementsA.nativeImpl {α β : Type} [Represent α] [Represent β] {A : Archi} {X : ExtSem}
    {aborts : Bool} {mod : Module} {k : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts mod k f Pre Post) {cap : Nat} {T : Translation}
    (hT : translate cap mod = some T) (hk : k ∈ T.funcs) : NativeImpl h A X cap T := by
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT hk
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.native h hT hfd hsig⟩

/-! ## The runtime -/

section

variable {A : Archi} {X : ExtSem}

open LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit in
/-- The runtime's `alloc` in a translated module: from a C memory related to a store whose heap
meets the allocator invariant, the C call of `alloc` on `bytes` terminates.  It returns the
address of the new block with `lx_status` 0, in a memory related to the store after the
allocation, or ends with `lx_status` holding the code of `unreachable`, when memory cannot
grow. -/
theorem alloc_native {mod : Module} {cap : Nat} {T : Translation} (hT : translate cap mod = some T)
    {typeIdx : Nat} (hFunc : mod.funcs[0]? = some (allocFunction typeIdx)) (h0 : 0 ∈ T.funcs)
    {E : Env} (hE : EnvOk E) (hG : E.globals.length = mod.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Store Unit) (bytes : UInt64) (hHeap : heap.At store)
    (hBytes : bytes.toNat ≤ 4294967296) (hCapS : store.memoryCap mod 0 ≤ 65535) (m : mem)
    (hst : StoreRel E store m) (hs : StatusRel E m 0) :
    ∃ fd, (funId 0, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
      ∃ t m' vres st', eval_funcall A X E.ge m (.Internal fd) [.Vlong bytes] t m' vres ∧
        StoreRel E st' m' ∧
        ((StatusRel E m' 0 ∧ heap.Fits (allocSize bytes) ∧
            st' = heap.allocateStore store (allocSize bytes) 1 ∧
            vres = .Vlong (FixedArrayAllocate.root heap.top (allocSize bytes) heap.free)) ∨
          StatusRel E m' trapUnreachable) := by
  obtain ⟨himp, h64, -⟩ := translate_spec hT
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT h0
  have hpr : signatureOf (allocFunction typeIdx) = some (ps, rs) := hsig _ hFunc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpr)
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := Runs.native (A := A) (X := X) hT hE hG hcap
    hnres hF
    hfd hsig (alloc_spec_runs true h64 himp hFunc {} heap store bytes hHeap hBytes hCapS
      (fun h => nomatch h)) ⟨by simp, by simp [AllHas, VT.has]⟩ hst hs
  refine ⟨fd, hfd, t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨hfits, rfl, rfl⟩, hr⟩ | ⟨-, htrap⟩
  · obtain ⟨v, hv, -, rfl⟩ := hr
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, -⟩ := hv
    exact .inl ⟨hs', hfits, rfl, rfl⟩
  · exact .inr htrap

open LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit in
/-- The runtime's `release` in a translated module: from a C memory related to a store whose
heap meets the allocator invariant and owns the object at `ptr`, the C call of `release` on
`ptr` returns with `lx_status` 0, in a memory related to the store after the release. -/
theorem release_native {mod : Module} {cap : Nat} {T : Translation}
    (hT : translate cap mod = some T) {typeIdx : Nat}
    (hFunc : mod.funcs[1]? = some (releaseFunction typeIdx)) (h1 : 1 ∈ T.funcs)
    {E : Env} (hE : EnvOk E) (hG : E.globals.length = mod.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Store Unit) (ptr : UInt64) (words : Array UInt64)
    (hHeap : heap.At store) (hOwned : heap.Owned store ptr words) (m : mem)
    (hst : StoreRel E store m) (hs : StatusRel E m 0) :
    ∃ fd, (funId 1, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
      ∃ t m', eval_funcall A X E.ge m (.Internal fd) [.Vlong ptr] t m' .Vundef ∧
        StoreRel E (heap.releaseStore store ptr) m' ∧ StatusRel E m' 0 := by
  obtain ⟨himp, -, -⟩ := translate_spec hT
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT h1
  have hpr : signatureOf (releaseFunction typeIdx) = some (ps, rs) := hsig _ hFunc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpr)
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := Runs.native (A := A) (X := X) (aborts := false)
    hT hE hG hcap hnres hF hfd hsig
    (TerminatesWith.runs (release_run himp hFunc {} heap store ptr words hHeap hOwned))
    ⟨by simp, by simp [AllHas, VT.has]⟩ hst hs
  rcases hres with ⟨hs', vs, ⟨-, rfl⟩, hr⟩ | ⟨habs, -⟩
  · obtain ⟨-, rfl⟩ := hr
    exact ⟨fd, hfd, t, m', hcall, hst', hs'⟩
  · cases habs

end

end LeanExe.Native
