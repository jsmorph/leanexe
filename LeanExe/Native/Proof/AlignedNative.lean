import LeanExe.Native.Proof.Native
import LeanExe.Pipeline.AlignedAlloc
import LeanExe.Pipeline.AlignedFreeList
import LeanExe.Pipeline.ImplementsAligned

/-!
The step from Talos's theorems to the translation without the test of alignment, the translation
with `alignedAccess`.  `RunsA.native` is `Runs.native` for that translation: it takes `RunsA`,
which adds to `Runs` that every run from some fuel on makes only aligned 64-bit accesses inside
memory, and it runs `translate_correct` at a fuel at which both hold.

`NativeAlignedA` is `NativeA` with the premise `AlignedInput` after `Separate` and, in the
conclusion for a return, the cap and region conclusions of `ImplementsAligned`, which `NativeA`
omits, and the alignment of the final heap and of the result's blocks (`AlignedOutput`), which a
host needs to meet `AlignedInput` at its next call.  `ImplementsAligned.native` derives it from
`ImplementsAligned` alone.  `NativeAlignedImpl h` states it for the function of the theorem `h`
of `ImplementsA`, as `NativeImpl h` states `NativeA`, and `ImplementsAligned.nativeImpl` derives
it from `ImplementsAligned` at the arguments of `h`.

`alloc_nativeA` and `release_nativeA` are `alloc_native` and `release_native` for the translation
without the test, from an aligned heap and, for `release`, an aligned pointer.  `Heap.Aligned.alloc`
gives the alignment of the pointer that `alloc` returns and of the heap after it, and
`Heap.Aligned.release` that of the heap after `release`.
-/

namespace LeanExe.Native

open Wasm LClight LeanExe.ProofKit

section

variable {A : Archi} {X : ExtSem}

/-- `Runs.native` for the translation without the test of alignment, from a run whose 64-bit
accesses inside memory are aligned from some fuel on. -/
theorem RunsA.native {mod : Module} {cap : Nat} {T : Translation}
    (hT : translate cap mod true = some T)
    {E : Env} (hE : EnvOk E) (hG : E.globals.length = mod.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    {k : Nat} {fd : function} (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    {ps rs : List VT}
    (hsig : ∀ f, mod.funcs[k]? = some f → signatureOf f = some (ps, rs))
    {aborts : Bool} {env : HostEnv Unit} {st : Store Unit} {args : List Value}
    {P : Store Unit → List Value → Prop} (hrun : RunsA aborts env mod k st args P)
    (htyped : ArgsTyped ps args) {m : mem} (hst : StoreRel E st m) (hs : StatusRel E m 0) :
    ∃ t m' vres st', eval_funcall A X E.ge m (.Internal fd) (argVals ps args) t m' vres ∧
      StoreRel E st' m' ∧
      ((StatusRel E m' 0 ∧ ∃ vs, P st' vs ∧ ResultRel E rs vs (args.drop ps.length) vres m') ∨
        (aborts = true ∧ StatusRel E m' trapUnreachable)) := by
  obtain ⟨⟨N, hN⟩, Na, hNa⟩ := hrun
  obtain ⟨f, ps', r', hf, hsig', hsim⟩ :=
    translate_correct (A := A) (X := X) hT hE hG hcap hnres hF (max N Na) k fd hfd
  rw [hsig f hf] at hsig'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig')
  have ho := hsim st args m env htyped hst hs fun _ => hNa _ (Nat.le_max_right _ _)
  rcases hN (max N Na) (Nat.le_max_left _ _) with ⟨vs, st', hr, hP⟩ | htr
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
/-- `NativeA` with the premise that the input is aligned, `AlignedInput`, after `Separate`, and,
after a return, the cap and region conclusions of `ImplementsA` and the alignment of the final
heap and of the result's blocks. -/
def NativeAlignedA {α β : Type} [Represent α] [Represent β] (A : Archi) (X : ExtSem) (cap : Nat)
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
      AlignedInput heap store params x →
      store.memoryCap mod 0 ≤ 65535 → ArgsTyped ps params.reverse →
      ∀ m, StoreRel E store m → StatusRel E m 0 →
      ∃ t m' vres final, eval_funcall A X E.ge m (.Internal fd) (argVals ps params.reverse) t m'
          vres ∧ StoreRel E final m' ∧
        ((StatusRel E m' 0 ∧ ∃ (vs : List Value) (heap' : Heap),
            ResultRel E rs vs (params.reverse.drop ps.length) vres m' ∧
            heap'.At final ∧ Represent.owned heap' final vs.reverse (f x) ∧
            final.memoryCaps = store.memoryCaps ∧
            (∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
              (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                heap'.Region r ∧ Represent.outside final vs.reverse (f x) r) ∧
            Post x heap store heap' final ∧ heap'.Aligned ∧ AlignedOutput final vs.reverse (f x)) ∨
          (aborts = true ∧ StatusRel E m' trapUnreachable))

open LeanExe.Pipeline in
/-- The translation without the test of alignment computes `f` as `ImplementsAligned` states, for
an aligned input. -/
theorem ImplementsAligned.native {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsAligned aborts mod k f Pre Post) {cap : Nat}
    {T : Translation} (hT : translate cap mod true = some T) {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    {ps rs : List VT}
    (hsig : ∀ f, mod.funcs[k]? = some f → signatureOf f = some (ps, rs)) :
    NativeAlignedA A X cap mod T ps rs fd aborts f Pre Post := by
  intro E hE hG hcap hnres hF store heap params x hHeap hPre hArgs hSep hAl hCapS htyped m hst hs
  obtain ⟨hAligned, hRuns⟩ := h {} store heap params x hHeap hPre hArgs hSep hCapS hAl
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := RunsA.native (A := A) (X := X) hT hE hG hcap
    hnres hF hfd hsig ⟨hRuns, hAligned⟩ htyped hst hs
  refine ⟨t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨heap', hAt, hOwn, hCaps, hRegion, hPost, hHeap', hOut⟩, hr⟩ |
    habort
  · exact .inl ⟨hs', vs, heap', hr, hAt, hOwn, hCaps, hRegion, hPost, hHeap', hOut⟩
  · exact .inr habort

open LeanExe.Pipeline in
/-- `NativeImpl` for the translation without the test of alignment: the translation of the
function of the theorem `h` computes its function as `NativeAlignedA` states. -/
def NativeAlignedImpl {α β : Type} [Represent α] [Represent β] {aborts : Bool} {mod : Module}
    {k : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (_h : ImplementsA aborts mod k f Pre Post) (A : Archi) (X : ExtSem) (cap : Nat)
    (T : Translation) : Prop :=
  ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
    (∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
    NativeAlignedA A X cap mod T ps rs fd aborts f Pre Post

open LeanExe.Pipeline in
theorem ImplementsAligned.nativeImpl {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts mod k f Pre Post) (hA : ImplementsAligned aborts mod k f Pre Post)
    {cap : Nat} {T : Translation} (hT : translate cap mod true = some T) (hk : k ∈ T.funcs) :
    NativeAlignedImpl h A X cap T := by
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT hk
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsAligned.native hA hT hfd hsig⟩

/-! ## The runtime -/

section

variable {A : Archi} {X : ExtSem}

open LeanExe.Pipeline LeanExe.Runtime in
/-- `alloc_native` for the translation without the test of alignment, from an aligned heap. -/
theorem alloc_nativeA {mod : Module} {cap : Nat} {T : Translation}
    (hT : translate cap mod true = some T)
    {typeIdx : Nat} (hFunc : mod.funcs[0]? = some (allocFunction typeIdx)) (h0 : 0 ∈ T.funcs)
    {E : Env} (hE : EnvOk E) (hG : E.globals.length = mod.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Store Unit) (bytes : UInt64) (hHeap : heap.At store)
    (hAligned : heap.Aligned) (hBytes : bytes.toNat ≤ 4294967296)
    (hCapS : store.memoryCap mod 0 ≤ 65535) (m : mem)
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
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := RunsA.native (A := A) (X := X) hT hE hG hcap
    hnres hF hfd hsig
    (alloc_spec_runsA true h64 himp hFunc {} heap store bytes hHeap hAligned hBytes hCapS nofun)
    ⟨by simp, by simp [AllHas, VT.has]⟩ hst hs
  refine ⟨fd, hfd, t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨hfits, rfl, rfl⟩, hr⟩ | ⟨-, htrap⟩
  · obtain ⟨v, hv, -, rfl⟩ := hr
    simp only [List.cons.injEq] at hv
    obtain ⟨rfl, -⟩ := hv
    exact .inl ⟨hs', hfits, rfl, rfl⟩
  · exact .inr htrap

open LeanExe.Pipeline LeanExe.Runtime in
/-- `release_native` for the translation without the test of alignment, from an aligned heap and
an aligned pointer. -/
theorem release_nativeA {mod : Module} {cap : Nat} {T : Translation}
    (hT : translate cap mod true = some T) {typeIdx : Nat}
    (hFunc : mod.funcs[1]? = some (releaseFunction typeIdx)) (h1 : 1 ∈ T.funcs)
    {E : Env} (hE : EnvOk E) (hG : E.globals.length = mod.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (heap : Heap) (store : Store Unit) (ptr : UInt64) (words : Array UInt64)
    (hHeap : heap.At store) (hOwned : heap.Owned store ptr words) (hAligned : heap.Aligned)
    (hPtrAl : ptr.toNat % 8 = 0) (m : mem)
    (hst : StoreRel E store m) (hs : StatusRel E m 0) :
    ∃ fd, (funId 1, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
      ∃ t m', eval_funcall A X E.ge m (.Internal fd) [.Vlong ptr] t m' .Vundef ∧
        StoreRel E (heap.releaseStore store ptr) m' ∧ StatusRel E m' 0 := by
  obtain ⟨himp, -, -⟩ := translate_spec hT
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT h1
  have hpr : signatureOf (releaseFunction typeIdx) = some (ps, rs) := hsig _ hFunc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpr)
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := RunsA.native (A := A) (X := X) (aborts := false)
    hT hE hG hcap hnres hF hfd hsig
    (release_leaf_runA himp hFunc {} heap store ptr hHeap hOwned.object hOwned.magic hOwned.count
      hOwned.childMask hAligned hPtrAl)
    ⟨by simp, by simp [AllHas, VT.has]⟩ hst hs
  rcases hres with ⟨hs', vs, ⟨-, rfl⟩, hr⟩ | ⟨habs, -⟩
  · obtain ⟨-, rfl⟩ := hr
    exact ⟨fd, hfd, t, m', hcall, hst', hs'⟩
  · cases habs

end

end LeanExe.Native
