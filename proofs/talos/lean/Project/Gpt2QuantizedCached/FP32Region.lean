import Project.Gpt2QuantizedCached.Program
import Project.Gpt2CachedStep.Program
import Project.FunctionRegion.Exec

set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

namespace Project.Gpt2QuantizedCached.FP32Region
open Wasm Project.FunctionRegion

def domain (index : Nat) : Prop := index ∈ [16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 39, 40, 41, 42]

def rename : Nat → Nat
  | 16 => 29
  | 17 => 31
  | 18 => 32
  | 19 => 33
  | 20 => 34
  | 22 => 43
  | 23 => 44
  | 24 => 45
  | 25 => 46
  | 26 => 47
  | 27 => 48
  | 28 => 49
  | 29 => 50
  | 30 => 51
  | 31 => 52
  | 32 => 53
  | 39 => 62
  | 40 => 63
  | 41 => 64
  | 42 => 65
  | index => index

def renameType : Nat → Nat
  | 16 => 29
  | 17 => 31
  | 18 => 32
  | 19 => 33
  | 20 => 34
  | 22 => 43
  | 23 => 44
  | 24 => 45
  | 25 => 46
  | 26 => 47
  | 27 => 48
  | 28 => 49
  | 29 => 50
  | 30 => 51
  | 31 => 52
  | 32 => 53
  | 39 => 62
  | 40 => 63
  | 41 => 64
  | 42 => 65
  | index => index

theorem portable16 : PortableProgram domain Project.Gpt2CachedStep.func16 := by
  prove_portable

theorem portable17 : PortableProgram domain Project.Gpt2CachedStep.func17 := by
  prove_portable

theorem portable18 : PortableProgram domain Project.Gpt2CachedStep.func18 := by
  prove_portable
  all_goals simp [domain]

theorem portable19 : PortableProgram domain Project.Gpt2CachedStep.func19 := by
  prove_portable
  all_goals simp [domain]

theorem portable20 : PortableProgram domain Project.Gpt2CachedStep.func20 := by
  prove_portable
  all_goals simp [domain]

theorem portable22 : PortableProgram domain Project.Gpt2CachedStep.func22 := by
  prove_portable
  all_goals simp [domain]

theorem portable23 : PortableProgram domain Project.Gpt2CachedStep.func23 := by
  prove_portable
  all_goals simp [domain]

theorem portable24 : PortableProgram domain Project.Gpt2CachedStep.func24 := by
  prove_portable

theorem portable25 : PortableProgram domain Project.Gpt2CachedStep.func25 := by
  prove_portable
  all_goals simp [domain]

theorem portable26 : PortableProgram domain Project.Gpt2CachedStep.func26 := by
  prove_portable

theorem portable27 : PortableProgram domain Project.Gpt2CachedStep.func27 := by
  prove_portable
  all_goals simp [domain]

theorem portable28 : PortableProgram domain Project.Gpt2CachedStep.func28 := by
  prove_portable
  all_goals simp [domain]

theorem portable29 : PortableProgram domain Project.Gpt2CachedStep.func29 := by
  prove_portable
  all_goals simp [domain]

theorem portable30 : PortableProgram domain Project.Gpt2CachedStep.func30 := by
  prove_portable
  all_goals simp [domain]

theorem portable31 : PortableProgram domain Project.Gpt2CachedStep.func31 := by
  prove_portable
  all_goals simp [domain]

theorem portable32 : PortableProgram domain Project.Gpt2CachedStep.func32 := by
  prove_portable
  all_goals simp [domain]

theorem portable39 : PortableProgram domain Project.Gpt2CachedStep.func39 := by
  prove_portable

theorem portable40 : PortableProgram domain Project.Gpt2CachedStep.func40 := by
  prove_portable

theorem portable41 : PortableProgram domain Project.Gpt2CachedStep.func41 := by
  prove_portable

theorem portable42 : PortableProgram domain Project.Gpt2CachedStep.func42 := by
  prove_portable
  all_goals simp [domain]

theorem shift : Shift Project.Gpt2CachedStep.«module» Project.Gpt2QuantizedCached.«module»
    rename renameType domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  simp only [domain, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Project.Gpt2CachedStep.func16Def, rfl, rfl, portable16⟩
  · exact ⟨Project.Gpt2CachedStep.func17Def, rfl, rfl, portable17⟩
  · exact ⟨Project.Gpt2CachedStep.func18Def, rfl, rfl, portable18⟩
  · exact ⟨Project.Gpt2CachedStep.func19Def, rfl, rfl, portable19⟩
  · exact ⟨Project.Gpt2CachedStep.func20Def, rfl, rfl, portable20⟩
  · exact ⟨Project.Gpt2CachedStep.func22Def, rfl, rfl, portable22⟩
  · exact ⟨Project.Gpt2CachedStep.func23Def, rfl, rfl, portable23⟩
  · exact ⟨Project.Gpt2CachedStep.func24Def, rfl, rfl, portable24⟩
  · exact ⟨Project.Gpt2CachedStep.func25Def, rfl, rfl, portable25⟩
  · exact ⟨Project.Gpt2CachedStep.func26Def, rfl, rfl, portable26⟩
  · exact ⟨Project.Gpt2CachedStep.func27Def, rfl, rfl, portable27⟩
  · exact ⟨Project.Gpt2CachedStep.func28Def, rfl, rfl, portable28⟩
  · exact ⟨Project.Gpt2CachedStep.func29Def, rfl, rfl, portable29⟩
  · exact ⟨Project.Gpt2CachedStep.func30Def, rfl, rfl, portable30⟩
  · exact ⟨Project.Gpt2CachedStep.func31Def, rfl, rfl, portable31⟩
  · exact ⟨Project.Gpt2CachedStep.func32Def, rfl, rfl, portable32⟩
  · exact ⟨Project.Gpt2CachedStep.func39Def, rfl, rfl, portable39⟩
  · exact ⟨Project.Gpt2CachedStep.func40Def, rfl, rfl, portable40⟩
  · exact ⟨Project.Gpt2CachedStep.func41Def, rfl, rfl, portable41⟩
  · exact ⟨Project.Gpt2CachedStep.func42Def, rfl, rfl, portable42⟩

#print axioms shift
end Project.Gpt2QuantizedCached.FP32Region
