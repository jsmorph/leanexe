import Verified.Call

/-!
The master statement of an export of a verified compilation.  `Master m tables name B D R` states
that the module `m` exports a function under `name` and that this function, called from a store
that `Ready m tables` states ready, with arguments `x` in the domain `D` that move no object and
with room for `B x` bytes, returns without a trap a value `y` with `R x y`, leaves a ready store,
keeps every borrowed array and every region of the heap, and raises `top` by at most `B x`.

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
for `B x` bytes, returns without a trap a value `y` with `R x y` and leaves a ready store, as
`Call` states, with `top` raised by at most `B x`. -/
def Master {α β : Type} [Represent α] [Represent β] (m : Module) (tables : List (Array UInt64))
    (name : String) (B : α → Nat) (D : α → Prop) (R : α → β → Prop) : Prop :=
  ∃ k, ({ name := name, funcIdx := k } : Wasm.Export) ∈ m.exports ∧
    ∃ f : α → β,
      Call m tables k f (fun x heap store => D x ∧ heap.Within store m (B x))
        (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + B x) ∧
      ∀ x, D x → R x (f x)

/-- `Master` from the theorem of an entry that cannot trap, whose tables are tables of the
program, when room for `B x` bytes gives its premise, its postcondition bounds the rise of `top`
by `B x`, and its function meets `R` on `D`.  For the generated `p.f.trapFree` with its bound,
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
    (hR : ∀ x, D x → R x (f x)) :
    Master m tables name B D R := by
  refine ⟨k, hexp, f, ?_, hR⟩
  intro env heap store params x hReady hargs hmoves ⟨hD, hroom⟩
  refine (ImplementsTables.call hI tables hts env heap store params x hReady hargs hmoves
    (hpre x heap store hD hroom)).mono ?_
  intro final values ⟨heap', hv, hR', hkept, hkeep, hout, hP⟩
  exact ⟨heap', hv, hR', hkept, hkeep, hout, hpost x heap store heap' final hP⟩

/-- The value that a `Master` statement promises: for an argument in the domain, from a ready store
with room, the call returns some `y` with `R x y`. -/
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
  obtain ⟨k, hexp, f, hcall, hR⟩ := h
  refine ⟨k, hexp, fun env heap store params x hReady hargs hmoves hD hroom => ?_⟩
  refine (hcall env heap store params x hReady hargs hmoves ⟨hD, hroom⟩).mono ?_
  intro final values ⟨heap', hv, hR', _⟩
  exact ⟨f x, heap', hR x hD, hv, hR'⟩

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
