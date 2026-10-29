import Verified.Native
import Verified.AlignedEntries
import LeanExe.Native.Proof.AlignedNative

/-!
The translation without the test of alignment for a wrapper.  `NativeTablesAlignedA` is
`NativeTablesA` with the premise `AlignedInput` after `Separate` and, after a return, the
alignment of the final heap and of the result's blocks, as `NativeAlignedA` is for `NativeA`.
`ImplementsTablesAligned.native` derives it from `ImplementsTablesAligned` alone, and
`NativeTablesAlignedImpl` and `ImplementsTablesAligned.nativeImpl` are `NativeTablesImpl` and
`ImplementsTables.nativeImpl` for it.
-/

namespace Verified

open Wasm LClight LeanExe.Native LeanExe.Pipeline LeanExe.ProofKit

/-- `NativeTablesA` with the premise that the input is aligned, `AlignedInput`, after
`Separate`, and, after a return, the alignment of the final heap and of the result's blocks. -/
def NativeTablesAlignedA {α β : Type} [Represent α] [Represent β] (A : Archi) (X : ExtSem)
    (cap : Nat) (mod : Module) (T : Translation) (ps rs : List VT) (fd : function)
    (aborts : Bool) (f : α → β) (tables : List (UInt64 × Array UInt64))
    (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (E : LeanExe.Native.Env), EnvOk E → E.globals.length = mod.globals.length → E.cap = cap →
    T.nres ≤ E.nres → (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd)) →
    ∀ (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
      heap.At store → Pre x heap store →
      (∀ t ∈ tables, heap.Borrowed store t.1 t.2 ∧
        Apart store (Represent.moves store params x) (t.1.toNat, 8 * (t.2.size + 1))) →
      Represent.borrowed heap store params x →
      Separate store (Represent.moves store params x) (Represent.reads store params x) →
      AlignedInput heap store params x →
      store.memoryCap mod 0 ≤ 65535 → ArgsTyped ps params.reverse →
      ∀ m, StoreRel E store m → StatusRel E m 0 →
      ∃ t m' vres final, eval_funcall A X E.ge m (.Internal fd) (argVals ps params.reverse) t m'
          vres ∧ StoreRel E final m' ∧
        ((StatusRel E m' 0 ∧ ∃ (vs : List Value) (heap' : Heap),
            ResultRel E rs vs (params.reverse.drop ps.length) vres m' ∧
            heap'.At final ∧ Represent.owned heap' final vs.reverse (f x) ∧
            Post x heap store heap' final ∧ heap'.Aligned ∧ AlignedOutput final vs.reverse (f x)) ∨
          (aborts = true ∧ StatusRel E m' trapUnreachable))

/-- The translation of a wrapper without the test of alignment computes its function as
`ImplementsTablesAligned` states, for an aligned input. -/
theorem ImplementsTablesAligned.native {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTablesAligned aborts mod k f tables Pre Post) {cap : Nat} {T : Translation}
    (hT : translate cap mod true = some T) {fd : function}
    (hfd : (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs)
    {ps rs : List VT}
    (hsig : ∀ f, mod.funcs[k]? = some f → signatureOf f = some (ps, rs)) :
    NativeTablesAlignedA A X cap mod T ps rs fd aborts f tables Pre Post := by
  intro E hE hG hcap hnres hF store heap params x hHeap hPre hTables hArgs hSep hAl hCapS htyped m
    hst hs
  obtain ⟨hAligned, hRuns⟩ := h {} store heap params x hHeap hPre hTables hArgs hSep hCapS hAl
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := RunsA.native (A := A) (X := X) hT hE hG hcap
    hnres hF hfd hsig ⟨hRuns, hAligned⟩ htyped hst hs
  refine ⟨t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨heap', hAt, hOwn, -, -, hPost, hHeap', hOut⟩, hr⟩ | habort
  · exact .inl ⟨hs', vs, heap', hr, hAt, hOwn, hPost, hHeap', hOut⟩
  · exact .inr habort

/-- `NativeTablesImpl` for the translation without the test of alignment. -/
def NativeTablesAlignedImpl {α β : Type} [Represent α] [Represent β] {aborts : Bool}
    {mod : Module} {k : Nat} {f : α → β} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (_h : ImplementsTablesAligned aborts mod k f tables Pre Post) (A : Archi) (X : ExtSem)
    (cap : Nat) (T : Translation) : Prop :=
  ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
    (∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
    NativeTablesAlignedA A X cap mod T ps rs fd aborts f tables Pre Post

theorem ImplementsTablesAligned.nativeImpl {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTablesAligned aborts mod k f tables Pre Post) {cap : Nat} {T : Translation}
    (hT : translate cap mod true = some T) (hk : k ∈ T.funcs) :
    NativeTablesAlignedImpl h A X cap T := by
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT hk
  exact ⟨fd, ps, rs, hfd, hsig, ImplementsTablesAligned.native h hT hfd hsig⟩

end Verified
