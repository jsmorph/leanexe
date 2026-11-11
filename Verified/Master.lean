import Verified.Call

/-!
The master statement of an export of a verified compilation.  `Master m tables name B D R` states
that the module `m` exports a function under `name` and that this function, called from a store
that `Ready m tables` states ready, with arguments `x` in the domain `D` whose moved objects are
separate from what the call reads and from the tables, and with room for `B x` bytes, returns
without a trap a value `y` with `R x y`.  The call leaves a ready store, raises `top` by at most
`B x`, and keeps the bytes and the regions of the heap that lie apart from the moved objects.
An argument that the function consumes, such as the array of an in-place sort, is a moved object.

The relation `R` is the specification.  A master theorem states `R` without the program's own
Lean function: as an equation with an independent definition, such as `Nat.gcd` or a transcription
of a standard, or as a relation, such as an accuracy bound against a real function.  The function
that the module computes appears only under the existential, so a reader of a master theorem needs
the definitions of `R`, `D`, and `B` and none of the program.  `B` is usually the generated bound
`p.f.bound` or a closed form of it.

`Master.of_trapFree` proves the statement from the generated theorem `p.f.trapFree` of the export,
the export's entry in the module, and the specification of the function.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- The export `name` of `m`, called on an argument `x` with `D x` from a ready store with room
for `B x` bytes, whose moved objects are pairwise apart and apart from the regions that the call
reads and from the tables, returns without a trap a value `y` with `R x y`, leaves a ready store
with `top` raised by at most `B x`, and keeps every region of the heap apart from the moved
objects. -/
def Master {α β : Type} [Represent α] [Represent β] (m : Module) (tables : List (Array UInt64))
    (name : String) (B : α → Nat) (D : α → Prop) (R : α → β → Prop) : Prop :=
  ∃ k, ({ name := name, funcIdx := k } : Wasm.Export) ∈ m.exports ∧
    ∃ f : α → β,
      (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (params : List Value) (x : α),
        Ready m tables heap store → Represent.borrowed heap store params x →
        Separate store (Represent.moves store params x) (Represent.reads store params x) →
        (∀ i (hi : i < tables.length), Apart store (Represent.moves store params x)
          ((tableAddr tables i).toNat, 8 * (tables[i].size + 1))) →
        D x → heap.Within store m (B x) →
        Runs false env m k store params.reverse fun final values =>
          ∃ heap' : Heap, R x (f x) ∧ Represent.owned heap' final values.reverse (f x) ∧
            Ready m tables heap' final ∧ heap'.top.toNat ≤ heap.top.toNat + B x ∧
            ∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
              (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                heap'.Region r ∧ Represent.outside final values.reverse (f x) r)

/-- `Master` from the theorem of an entry that cannot trap, whose tables are tables of the
program, when room for `B x` bytes gives its premise, its postcondition bounds the rise of `top`
by `B x`, and its function meets `R` on every represented argument in `D`.  For the generated `p.f.trapFree` with its bound,
the premises `hpre` and `hpost` hold by `fun _ _ _ _ h => h` and `fun _ _ _ _ _ h => h`, with
`trivial` in place of the first conclusion for a function that cannot abort. -/
theorem Master.of_trapFree {α β : Type} [Represent α] [Represent β] {m : Module}
    {tables : List (Array UInt64)} {k : Nat} {name : String} {f : α → β}
    {ts : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} {B : α → Nat} {D : α → Prop}
    {R : α → β → Prop}
    (hI : ImplementsTables false m k f ts Pre Post)
    (hts : ∀ t ∈ ts, ∃ i, ∃ hi : i < tables.length, t = (tableAddr tables i, tables[i]))
    (hexp : ({ name := name, funcIdx := k } : Wasm.Export) ∈ m.exports)
    (hpre : ∀ x heap store, D x → heap.Within store m (B x) → Pre x heap store)
    (hpost : ∀ x heap store heap' final, Post x heap store heap' final →
      heap'.top.toNat ≤ heap.top.toNat + B x)
    (hR : ∀ heap store params x, Represent.borrowed heap store params x → D x → R x (f x)) :
    Master m tables name B D R := by
  refine ⟨k, hexp, f, ?_⟩
  intro env heap store params x ⟨hAt, hCap, hTab⟩ hargs hsep happ hD hroom
  have htab : ∀ t ∈ ts, heap.Borrowed store t.1 t.2 ∧
      Apart store (Represent.moves store params x) (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := hts t ht
    exact ⟨hTab i hi, happ i hi⟩
  refine (hI env store heap params x hAt (hpre x heap store hD hroom) htab hargs hsep hCap).mono ?_
  intro final values ⟨heap', hAt', howned, hcaps, hframe, hpost'⟩
  refine ⟨heap', hR heap store params x hargs hD, howned,
    ⟨hAt', memoryCap_le_of_caps hcaps hCap, fun i hi => ?_⟩, hpost x heap store heap' final hpost',
    hframe⟩
  have hp := hTab i hi
  obtain ⟨hb, hr, -⟩ := hframe _ hp.region (by show 0 < 8 * (tables[i].size + 1); omega)
    (happ i hi)
  exact hp.keepIn hAt' hb hr

/-- The value that a `Master` statement promises: for an argument in the domain that moves no
object, from a ready store with room, the call returns some `y` with `R x y`. -/
theorem Master.runs {α β : Type} [Represent α] [Represent β] {m : Module}
    {tables : List (Array UInt64)} {name : String} {B : α → Nat} {D : α → Prop}
    {R : α → β → Prop} (h : Master m tables name B D R) :
    ∃ k, ({ name := name, funcIdx := k } : Wasm.Export) ∈ m.exports ∧
      ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (params : List Value) (x : α),
        Ready m tables heap store → Represent.borrowed heap store params x →
        Represent.moves store params x = [] → D x → heap.Within store m (B x) →
        Runs false env m k store params.reverse fun final values =>
          ∃ y heap', R x y ∧ Represent.owned heap' final values.reverse y ∧
            Ready m tables heap' final := by
  obtain ⟨k, hexp, f, hcall⟩ := h
  refine ⟨k, hexp, fun env heap store params x hReady hargs hmoves hD hroom => ?_⟩
  have hsep : Separate store (Represent.moves store params x) (Represent.reads store params x) := by
    rw [hmoves]; exact Separate.nil
  refine (hcall env heap store params x hReady hargs hsep (fun i _ => by rw [hmoves]; exact
    Apart.nil) hD hroom).mono ?_
  intro final values ⟨heap', hR, hv, hR', _⟩
  exact ⟨f x, heap', hR, hv, hR'⟩

#print axioms Master.of_trapFree
#print axioms Master.runs

open Lean Elab Command in
/-- `master_registry [t₁, …, tₙ]` checks that each `tᵢ` is a theorem whose statement is a
`Verified.Master` statement about a module, and fails otherwise.  The registry of the library,
`Library/Masters.lean`, lists every master theorem. -/
elab "master_registry " "[" names:ident,* "]" : command => do
  let env ← getEnv
  for stx in names.getElems do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx
    match env.find? n with
    | some (.thmInfo info) =>
      let ty ← liftTermElabM <| Meta.whnfR info.type
      unless ty.getAppFn.isConstOf ``Verified.Master do
        throwErrorAt stx "{n} is not a Verified.Master statement"
    | _ => throwErrorAt stx "{n} is not a theorem"
  logInfo m!"master_registry: {names.getElems.size} master theorems"

end Verified
