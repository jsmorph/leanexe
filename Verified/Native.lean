import LeanExe.Native.Proof.Native
import Verified.Correct

/-!
What `verified_compile` uses to state `p.f.native` for a wrapper and for a module with literals:
`NativeTablesA` and `NativeStaticA`, the forms of `NativeA` for a function whose theorem is
`ImplementsTables` or `ImplementsStatic`.  `ImplementsTables.nativeImpl` and
`ImplementsStatic.nativeImpl` derive `NativeTablesImpl` and `NativeStaticImpl` from the
function's theorem and its presence in the translation, as `ImplementsA.nativeImpl` derives
`NativeImpl`.
-/

namespace Verified

open Wasm LClight LeanExe.Native LeanExe.Pipeline

/-- `NativeA` for a wrapper, whose premises add that the tables `tables` are borrowed and apart
from the arrays that the call consumes. -/
def NativeTablesA {α β : Type} [Represent α] [Represent β] (A : Archi) (X : ExtSem) (cap : Nat)
    (mod : Module) (T : Translation) (ps rs : List VT) (fd : function)
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
      store.memoryCap mod 0 ≤ 65535 → ArgsTyped ps params.reverse →
      ∀ m, StoreRel E store m → StatusRel E m 0 →
      ∃ t m' vres final, eval_funcall A X E.ge m (.Internal fd) (argVals ps params.reverse) t m'
          vres ∧ StoreRel E final m' ∧
        ((StatusRel E m' 0 ∧ ∃ (vs : List Value) (heap' : Heap),
            ResultRel E rs vs (params.reverse.drop ps.length) vres m' ∧
            heap'.At final ∧ Represent.owned heap' final vs.reverse (f x) ∧
            Post x heap store heap' final) ∨
          (aborts = true ∧ StatusRel E m' trapUnreachable))

/-- The translation of the wrapper of the theorem `h` computes its function as `h` states. -/
def NativeTablesImpl {α β : Type} [Represent α] [Represent β] {aborts : Bool} {mod : Module}
    {k : Nat} {f : α → β} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (_h : ImplementsTables aborts mod k f tables Pre Post) (A : Archi) (X : ExtSem)
    (cap : Nat) (T : Translation) : Prop :=
  ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
    (∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
    NativeTablesA A X cap mod T ps rs fd aborts f tables Pre Post

theorem ImplementsTables.nativeImpl {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {aborts : Bool} {mod : Module} {k : Nat} {f : α → β}
    {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsTables aborts mod k f tables Pre Post) {cap : Nat} {T : Translation}
    (hT : translate cap mod = some T) (hk : k ∈ T.funcs) : NativeTablesImpl h A X cap T := by
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT hk
  refine ⟨fd, ps, rs, hfd, hsig, ?_⟩
  intro E hE hG hcap hnres hF store heap params x hHeap hPre hTables hArgs hSep hCapS htyped m
    hst hs
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := Runs.native (A := A) (X := X) hT hE hG hcap
    hnres hF hfd hsig (h {} store heap params x hHeap hPre hTables hArgs hSep hCapS) htyped hst hs
  refine ⟨t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨heap', hAt, hOwn, -, -, hPost⟩, hr⟩ | habort
  · exact .inl ⟨hs', vs, heap', hr, hAt, hOwn, hPost⟩
  · exact .inr habort

/-- `NativeTablesA` for a function of a module with literals, whose premises add that the
literal pool `pool` holds the arguments' literals. -/
def NativeStaticA {α β : Type} [Represent α] [Represent β] (A : Archi) (X : ExtSem) (cap : Nat)
    (mod : Module) (T : Translation) (ps rs : List VT) (fd : function) (pool : Bytes.LiteralPool)
    (aborts : Bool) (f : α → β) (tables : List (UInt64 × Array UInt64))
    (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (E : LeanExe.Native.Env), EnvOk E → E.globals.length = mod.globals.length → E.cap = cap →
    T.nres ≤ E.nres → (∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd)) →
    ∀ (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
      heap.At store → Pre x heap store → pool.Input heap store params x →
      (∀ t ∈ tables, heap.Borrowed store t.1 t.2 ∧
        Apart store (Represent.moves store params x) (t.1.toNat, 8 * (t.2.size + 1))) →
      Represent.borrowed heap store params x →
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

/-- The translation of the function of the theorem `h` computes its function as `h` states. -/
def NativeStaticImpl {α β : Type} [Represent α] [Represent β] {pool : Bytes.LiteralPool}
    {aborts : Bool} {mod : Module} {k : Nat} {f : α → β} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (_h : ImplementsStatic pool aborts mod k f tables Pre Post) (A : Archi) (X : ExtSem)
    (cap : Nat) (T : Translation) : Prop :=
  ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
    (∀ g, mod.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
    NativeStaticA A X cap mod T ps rs fd pool aborts f tables Pre Post

theorem ImplementsStatic.nativeImpl {α β : Type} [Represent α] [Represent β] {A : Archi}
    {X : ExtSem} {pool : Bytes.LiteralPool} {aborts : Bool} {mod : Module} {k : Nat}
    {f : α → β} {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : ImplementsStatic pool aborts mod k f tables Pre Post) {cap : Nat} {T : Translation}
    (hT : translate cap mod = some T) (hk : k ∈ T.funcs) : NativeStaticImpl h A X cap T := by
  obtain ⟨fd, ps, rs, hfd, hsig⟩ := translate_sig hT hk
  refine ⟨fd, ps, rs, hfd, hsig, ?_⟩
  intro E hE hG hcap hnres hF store heap params x hHeap hPre hPool hTables hArgs hSep hCapS
    htyped m hst hs
  obtain ⟨t, m', vres, st', hcall, hst', hres⟩ := Runs.native (A := A) (X := X) hT hE hG hcap
    hnres hF hfd hsig (h {} store heap params x hHeap hPre hPool hTables hArgs hSep hCapS)
    htyped hst hs
  refine ⟨t, m', vres, st', hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, ⟨heap', hAt, hOwn, -, -, hPost⟩, hr⟩ | habort
  · exact .inl ⟨hs', vs, heap', hr, hAt, hOwn, hPost⟩
  · exact .inr habort

end Verified
