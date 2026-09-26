import Project.Gpt2QuantizedGroupedRows.Program
import Project.Gpt2QuantizedLinearRows.Program
import Project.FunctionRegion.Exec

set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

namespace Project.Gpt2QuantizedGroupedRows.ProjectionRegion
open Wasm Project.FunctionRegion

def domain (index : Nat) : Prop := index ∈ [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12]

def rename (index : Nat) : Nat := index

def renameType (index : Nat) : Nat := index

theorem portable0 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func0 := by
  prove_portable

theorem portable1 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func1 := by
  prove_portable
  all_goals simp [domain]

theorem portable2 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func2 := by
  prove_portable

theorem portable3 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func3 := by
  prove_portable
  all_goals simp [domain]

theorem portable4 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func4 := by
  prove_portable

theorem portable5 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func5 := by
  prove_portable

theorem portable6 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func6 := by
  prove_portable

theorem portable7 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func7 := by
  prove_portable

theorem portable9 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func9 := by
  prove_portable

theorem portable10 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func10 := by
  prove_portable

theorem portable11 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func11 := by
  prove_portable

theorem portable12 : PortableProgram domain Project.Gpt2QuantizedLinearRows.func12 := by
  prove_portable
  all_goals simp [domain]

theorem shift : Shift Project.Gpt2QuantizedLinearRows.«module» Project.Gpt2QuantizedGroupedRows.«module»
    rename renameType domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  simp only [domain, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Project.Gpt2QuantizedLinearRows.func0Def, rfl, rfl, portable0⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func1Def, rfl, rfl, portable1⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func2Def, rfl, rfl, portable2⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func3Def, rfl, rfl, portable3⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func4Def, rfl, rfl, portable4⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func5Def, rfl, rfl, portable5⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func6Def, rfl, rfl, portable6⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func7Def, rfl, rfl, portable7⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func9Def, rfl, rfl, portable9⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func10Def, rfl, rfl, portable10⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func11Def, rfl, rfl, portable11⟩
  · exact ⟨Project.Gpt2QuantizedLinearRows.func12Def, rfl, rfl, portable12⟩

#print axioms shift
end Project.Gpt2QuantizedGroupedRows.ProjectionRegion
