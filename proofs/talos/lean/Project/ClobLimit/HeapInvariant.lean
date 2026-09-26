import Project.ClobLimit.HeapFrames

namespace Project.ClobLimit.HeapInvariant
open Wasm Project.LocalRegion Project.ClobLimit.HeapProgram
open Project.ClobMatchFuel.LoopInvariant

def Invariant (ctx : Context) (st : Store Unit) (target : Locals) : Prop :=
  ∃ source, layout.Related source target ∧ ClobMatchFuel.LoopInvariant.Invariant ctx st source

def ExitAt (ctx : Context) (st : Store Unit) (target : Locals) : Prop :=
  ∃ source, layout.Related source target ∧ ClobMatchFuel.LoopInvariant.ExitAt ctx st source

def measure (_ : Store Unit) (s : Locals) : Nat :=
  match s.get 18 with
  | some (.i64 done) =>
      if done = 0 then
        match s.get 0 with
        | some (.i64 fuel) => 2 * fuel.toNat + 1
        | _ => 0
      else 0
  | _ => 0

theorem measure_eq (st : Store Unit) (h : layout.Related source target) :
    measure st target = ClobMatchFuel.LoopInvariant.measure st source := by
  have hd := h.reads 24 (by simp [Domain])
  have hf := h.reads 0 (by simp [Domain])
  change target.get 18 = source.get 24 at hd
  change target.get 0 = source.get 0 at hf
  simp only [measure, ClobMatchFuel.LoopInvariant.measure, hd, hf]
  rfl

theorem Invariant.values (h : Invariant ctx st target) : target.values = [] := by
  obtain ⟨source, hr, hi⟩ := h
  exact hr.values.trans hi.values

theorem ExitAt.values (h : ExitAt ctx st target) : target.values = [] := by
  obtain ⟨source, hr, hi⟩ := h
  exact hr.values.trans hi.values

#print axioms measure_eq
end Project.ClobLimit.HeapInvariant
