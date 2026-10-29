import LeanExe.Native.Proof.Native
import LeanExe.Pipeline.AlignedRuns
import LeanExe.Pipeline.AlignedImplements

/-!
The step from Talos's theorems to the translation without the test of alignment, the translation
with `alignedAccess`.  `RunsA.native` is `Runs.native` for that translation: it takes `RunsA`,
which adds to `Runs` that every run from some fuel on makes only aligned 64-bit accesses inside
memory, and it runs `translate_correct` at a fuel at which both hold.

`NativeAlignedA` is `NativeA` with the premise `AlignedInput` after `Separate`, the form that the
proposal for the trusted statement gives `NativeA`.  `ImplementsA.nativeAligned` derives it from
`ImplementsA` and `ImplementsAligned` of the same entry, and `NativeAlignedImpl` and
`ImplementsA.nativeAlignedImpl` are `NativeImpl` and `ImplementsA.nativeImpl` for it.
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
/-- `NativeA` with the premise that the input is aligned, `AlignedInput`, after `Separate`. -/
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
            Post x heap store heap' final) ∨
          (aborts = true ∧ StatusRel E m' trapUnreachable))

open LeanExe.Pipeline in
/-- The translation without the test of alignment computes `f` as `ImplementsA` states, for an
aligned input, when `ImplementsAligned` holds of the same entry. -/
theorem ImplementsA.nativeAligned {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts mod k f Pre Post) (hA : ImplementsAligned mod k Pre) {cap : Nat}
    {T : Translation} (hT : translate cap mod true = some T) {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    {ps rs : List VT}
    (hsig : ∀ f, mod.funcs[k]? = some f → signatureOf f = some (ps, rs)) :
    NativeAlignedA A X cap mod T ps rs fd aborts f Pre Post := by
  intro E hE hG hcap hnres hF store heap params x hHeap hPre hArgs hSep hAl hCapS htyped m hst hs
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := RunsA.native (A := A) (X := X) hT hE hG hcap
    hnres hF hfd hsig
    ⟨h {} store heap params x hHeap hPre hArgs hSep hCapS,
      hA {} store heap params x hHeap hPre hArgs hSep hCapS hAl⟩ htyped hst hs
  refine ⟨t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨heap', hAt, hOwn, -, -, hPost⟩, hr⟩ | habort
  · exact .inl ⟨hs', vs, heap', hr, hAt, hOwn, hPost⟩
  · exact .inr habort

open LeanExe.Pipeline in
/-- `NativeImpl` for the translation without the test of alignment. -/
def NativeAlignedImpl {α β : Type} [Represent α] [Represent β] {aborts : Bool} {mod : Module}
    {k : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (_h : ImplementsA aborts mod k f Pre Post) (A : Archi) (X : ExtSem) (cap : Nat)
    (T : Translation) : Prop :=
  ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
    (∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
    NativeAlignedA A X cap mod T ps rs fd aborts f Pre Post

open LeanExe.Pipeline in
theorem ImplementsA.nativeAlignedImpl {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsA aborts mod k f Pre Post) (hA : ImplementsAligned mod k Pre) {cap : Nat}
    {T : Translation} (hT : translate cap mod true = some T) (hk : k ∈ T.funcs) :
    NativeAlignedImpl h A X cap T := by
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT hk
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsA.nativeAligned h hA hT hfd hsig⟩

end LeanExe.Native
