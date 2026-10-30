import LeanExe.Native.Proof.Native
import LeanExe.Native.Clight.Determinism

/-!
The execution that `NativeA` asserts is the only one with its trace.  `NativeA.unique` takes a
semantics `X` of external functions that meets `ExtSem.Determ` and the premises of `NativeA`.
It concludes that the C call has an execution with a trace `t`, and that every execution of the
call from the same memory whose trace agrees with `t` up to the length of the shorter has the
trace `t` and meets the conclusions of `NativeA`.  The proof applies
`eval_funcall_determ_prefix` of `LeanExe/Native/Clight/Determinism.lean` to the execution that
`NativeA` gives.
-/

namespace LeanExe.Native

open Wasm LClight

open LeanExe.Pipeline in
/-- Every execution of the call of `NativeA` whose trace agrees with the trace `t` of the
asserted execution, up to the length of the shorter, has the trace `t` and meets the conclusions
of `NativeA`. -/
theorem NativeA.unique {α β : Type} [Represent α] [Represent β] {A : Archi} {X : ExtSem}
    {cap : Nat} {mod : Module} {T : Translation} {ps rs : List VT} {fd : function}
    {aborts : Bool} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : NativeA A X cap mod T ps rs fd aborts f Pre Post) (hX : X.Determ)
    (E : Env) (hE : EnvOk E) (hG : E.globals.length = mod.globals.length) (hcap : E.cap = cap)
    (hnres : T.nres ≤ E.nres)
    (hF : ∀ k fd, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs →
      ∃ b, Genv.find_symbol E.ge (funId k) = some b ∧
        Genv.find_funct_ptr E.ge b = some (.Internal fd))
    (store : Store Unit) (heap : Heap) (params : List Value) (x : α)
    (hHeap : heap.At store) (hPre : Pre x heap store)
    (hArgs : Represent.borrowed heap store params x)
    (hSep : Separate store (Represent.moves store params x) (Represent.reads store params x))
    (hCapS : store.memoryCap mod 0 ≤ 65535) (htyped : ArgsTyped ps params.reverse)
    (m : mem) (hst : StoreRel E store m) (hs : StatusRel E m 0) :
    ∃ t, (∃ m' vres, eval_funcall A X E.ge m (.Internal fd) (argVals ps params.reverse) t m' vres) ∧
      ∀ t' m' vres u u', eval_funcall A X E.ge m (.Internal fd) (argVals ps params.reverse) t' m'
          vres → t ++ u = t' ++ u' →
        t' = t ∧ ∃ final, StoreRel E final m' ∧
          ((StatusRel E m' 0 ∧ ∃ (vs : List Value) (heap' : Heap),
              ResultRel E rs vs (params.reverse.drop ps.length) vres m' ∧
              heap'.At final ∧ Represent.owned heap' final vs.reverse (f x) ∧
              final.memoryCaps = store.memoryCaps ∧
              (∀ r, heap.Region r → 0 < r.2 →
                Apart store (Represent.moves store params x) r →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r ∧ Represent.outside final vs.reverse (f x) r) ∧
              Post x heap store heap' final) ∨
            (aborts = true ∧ StatusRel E m' trapUnreachable)) := by
  obtain ⟨t, m₁, v₁, final, hcall, hrest⟩ :=
    h E hE hG hcap hnres hF store heap params x hHeap hPre hArgs hSep hCapS htyped m hst hs
  refine ⟨t, ⟨m₁, v₁, hcall⟩, fun t' m' vres u u' hcall' hu => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := eval_funcall_determ_prefix hX hcall hcall' hu
  exact ⟨rfl, final, hrest⟩

end LeanExe.Native
