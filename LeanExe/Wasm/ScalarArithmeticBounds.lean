import LeanExe.Wasm.ArithmeticAdmission

namespace LeanExe.Extract.Core
open LeanExe.Wasm.ScalarDescriptor

/-- An arithmetic descriptor with every read below the declared local bound. -/
def ScalarArithmeticBounded (count : Nat) (ir : LeanExe.IR.Expr) : Prop :=
  ∃ descriptor, Expr.ofIR ir = some descriptor ∧ descriptor.Arithmetic ∧
    ∀ index ∈ descriptor.reads, index < count

namespace ScalarArithmeticBounded

theorem literal (count n : Nat) : ScalarArithmeticBounded count (.u64 n) :=
  ⟨_, rfl, .const, by simp [Expr.reads]⟩

theorem get (index : Nat) {count : Nat} (bound : index < count) :
    ScalarArithmeticBounded count (.local index) :=
  ⟨.get index, rfl, .get, by simpa [Expr.reads] using bound⟩

theorem primitive {count : Nat} (op : ScalarPrimitive) {a b : LeanExe.IR.Expr}
    (ha : ScalarArithmeticBounded count a) (hb : ScalarArithmeticBounded count b) :
    ScalarArithmeticBounded count (op.lower a b) := by
  obtain ⟨da, hda, aa, ba⟩ := ha
  obtain ⟨db, hdb, ab, bb⟩ := hb
  obtain ⟨dop, hop⟩ := op.descriptor
  refine ⟨.bin dop da db, by simp [ScalarPrimitive.lower, Expr.ofIR, hop, hda, hdb], .bin aa ab, ?_⟩
  intro index member
  rcases List.mem_append.mp member with member | member
  · exact ba index member
  · exact bb index member

theorem choice {count : Nat} (op : LeanExe.Source.Scalar.Comparison) {a b t e : LeanExe.IR.Expr}
    (ha : ScalarArithmeticBounded count a) (hb : ScalarArithmeticBounded count b)
    (ht : ScalarArithmeticBounded count t) (he : ScalarArithmeticBounded count e) :
    ScalarArithmeticBounded count (.ite (lowerComparison op a b) t e) := by
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

theorem bindings (inputs : List LeanExe.Source.Scalar.PublicArgument) {count : Nat}
    (bound : inputs.length ≤ count) :
    ∀ binding ∈ publicBindings inputs, binding.Holds (ScalarArithmeticBounded count) := by
  apply publicBindingsFor_holds _ (literal count) (fun op _ _ _ _ => choice op)
  intro slot member
  apply get slot
  have found : slot < inputs.length := by simpa using member
  omega

end ScalarArithmeticBounded
end LeanExe.Extract.Core
