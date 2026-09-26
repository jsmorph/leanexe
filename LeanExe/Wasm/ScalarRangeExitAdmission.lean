import LeanExe.Wasm.ScalarRangeExitCertificate
import LeanExe.Wasm.ArithmeticAdmission
import LeanExe.Extract.ScalarRangeExitInvariant

namespace LeanExe.Wasm.ScalarDescriptor

def RangeExit.All (P : Expr → Prop) (descriptor : RangeExit) : Prop :=
  P descriptor.count ∧ P descriptor.initial ∧ P descriptor.step ∧ P descriptor.done ∧ P descriptor.result

end LeanExe.Wasm.ScalarDescriptor

namespace LeanExe.Extract.Core

open LeanExe.Wasm.ScalarDescriptor

/-- Source extraction derives arithmetic descriptors and bounds for every read,
including both branches of each expression in the setup, step and result. -/
theorem extractScalarRangeExit_admitted {source : Lean.Expr} {locals : List Nat}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith (locals.map fun index => .word (.local index)) slot source = some plan)
    (bounded : ∀ index ∈ locals, index < slot) :
    ∃ descriptor : RangeExit, descriptor.Matches plan ∧ descriptor.All Expr.Arithmetic ∧
      descriptor.All (fun e => ∀ index ∈ e.reads, index < slot + 3) := by
  let P := fun ir => ∃ descriptor, Expr.ofIR ir = some descriptor ∧ descriptor.Arithmetic ∧
    ∀ index ∈ descriptor.reads, index < slot + 3
  have get (index : Nat) (bound : index < slot + 3) : P (.local index) :=
    ⟨.get index, rfl, .get, by simpa [Expr.reads] using bound⟩
  have invariant : plan.Holds P := by
    refine extractScalarRangeExitWith_invariant P (fun _ => ⟨_, rfl, .const, by simp [Expr.reads]⟩)
      ?_ ?_ (get slot (by omega)) (get (slot + 1) (by omega)) compiled ?_
    · intro op a b ha hb
      obtain ⟨da, hda, aa, ba⟩ := ha
      obtain ⟨db, hdb, ab, bb⟩ := hb
      obtain ⟨dop, hop⟩ := op.descriptor
      refine ⟨.bin dop da db, by simp [ScalarPrimitive.lower, Expr.ofIR, hop, hda, hdb], .bin aa ab, ?_⟩
      intro index member
      rcases List.mem_append.mp member with member | member
      · exact ba index member
      · exact bb index member
    · intro op a b t e ha hb ht he
      obtain ⟨da, hda, aa, ba⟩ := ha
      obtain ⟨db, hdb, ab, bb⟩ := hb
      obtain ⟨dt, hdt, aTrue, bt⟩ := ht
      obtain ⟨de, hde, ae, be⟩ := he
      refine ⟨.ite (comparison op da db) dt de, by
        simp [Expr.ofIR, lowerComparison_descriptor op hda hdb, hdt, hde], .choose op aa ab aTrue ae, ?_⟩
      intro index member
      simp only [Expr.reads, comparison_reads, List.mem_append] at member
      rcases member with ((member | member) | member) | member
      · exact ba index member
      · exact bb index member
      · exact bt index member
      · exact be index member
    · intro binding member
      obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
      exact get index (Nat.lt_trans (bounded index present) (by omega))
  obtain ⟨⟨dc, hc, ac, bc⟩, ⟨di, hi, ai, bi⟩, ⟨ds, hs, aStep, bs⟩, ⟨dd, hd, ad, bd⟩, ⟨dr, hr, ar, br⟩⟩ := invariant
  exact ⟨⟨dc, di, ds, dd, dr⟩, ⟨hc, hi, hs, hd, hr⟩, ⟨ac, ai, aStep, ad, ar⟩, ⟨bc, bi, bs, bd, br⟩⟩

end LeanExe.Extract.Core
