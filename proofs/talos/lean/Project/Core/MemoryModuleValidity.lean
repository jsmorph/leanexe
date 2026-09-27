import Project.Core.MemoryRuntime
import Project.Core.MemoryValidity

namespace Project.Core.MemoryModuleValidity

open Wasm.Encoding.Spec.Validity
open Project.Core.Validity
open Project.Core.MemoryRuntime

theorem type_lookup (source : LeanExe.Core.Module) (arity : Nat)
    (bound : arity ≤ max (maxParams source) 2) :
    (memoryModule source).types[arity]? = some (functionSignature arity) := by
  change ((List.range (max (maxParams source) 2 + 1)).map functionSignature)[arity]? = _
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem source_type_lookup (source : LeanExe.Core.Module) (index : Nat)
    (function : LeanExe.Core.Function) (found : source[index]? = some function) :
    (functionTypes (memoryModule source))[index]? = some (functionSignature function.params) := by
  change ((memoryModule source).funcs.map Wasm.Encoding.Spec.signature)[index]? = _
  rw [List.getElem?_map, source_lookup source index function found]
  rfl

theorem runtime_type_lookup (source : LeanExe.Core.Module) (operation : Nat)
    (function : Wasm.Function) (found : runtimeFunctions[operation]? = some function) :
    (functionTypes (memoryModule source))[source.length + operation]? =
      some (Wasm.Encoding.Spec.signature function) := by
  change ((memoryModule source).funcs.map Wasm.Encoding.Spec.signature)[source.length + operation]? = _
  rw [List.getElem?_map, runtime_lookup source operation function found]
  rfl

theorem primitive_call_typed (source : LeanExe.Core.Module) (operation arity : Nat)
    (function : Wasm.Function) (found : runtimeFunctions[operation]? = some function)
    (signature : Wasm.Encoding.Spec.signature function = functionSignature arity)
    (context : Wasm.Encoding.Spec.Validity.Context)
    (functions : context.functions = functionTypes (memoryModule source)) :
    Program context (code source.length operation) (List.replicate arity .i64) [.i64] := by
  have resolved := runtime_type_lookup source operation function found
  rw [signature] at resolved
  exact singleton (.call (source.length + operation) (functionSignature arity)
    (by rw [functions]; exact resolved)) numeric_i64

theorem primitive_typed (source : LeanExe.Core.Module) :
    PrimitiveTyping (functionTypes (memoryModule source)) (memoryModule source).memory
      LeanExe.Core.Memory.effectArity (code source.length) := by
  intro operation arity declared context functions _
  rcases operation with _ | (_ | (_ | (_ | operation)))
  · simp only [LeanExe.Core.Memory.effectArity, Option.some.injEq] at declared
    subst arity
    exact primitive_call_typed source 0 1 Memory.readFunction rfl rfl context functions
  · simp only [LeanExe.Core.Memory.effectArity, Option.some.injEq] at declared
    subst arity
    exact primitive_call_typed source 1 2 Memory.writeFunction rfl rfl context functions
  · simp only [LeanExe.Core.Memory.effectArity, Option.some.injEq] at declared
    subst arity
    exact primitive_call_typed source 2 0 Memory.sizeFunction rfl rfl context functions
  · simp only [LeanExe.Core.Memory.effectArity, Option.some.injEq] at declared
    subst arity
    exact primitive_call_typed source 3 1 growFunction rfl rfl context functions
  · simp [LeanExe.Core.Memory.effectArity] at declared

theorem read_valid (source : LeanExe.Core.Module) :
    Wasm.Encoding.Spec.Validity.Function (memoryModule source) Memory.readFunction := by
  refine ⟨⟨1, rfl, ?_⟩, numeric_nil, by decide, ?_⟩
  · exact type_lookup source 1 (by omega)
  · exact MemoryValidity.guarded_read_body_typed _ rfl rfl

theorem write_valid (source : LeanExe.Core.Module) :
    Wasm.Encoding.Spec.Validity.Function (memoryModule source) Memory.writeFunction := by
  refine ⟨⟨2, rfl, ?_⟩, numeric_nil, by decide, ?_⟩
  · exact type_lookup source 2 (by omega)
  · exact MemoryValidity.guarded_write_body_typed _ rfl rfl rfl

theorem size_valid (source : LeanExe.Core.Module) :
    Wasm.Encoding.Spec.Validity.Function (memoryModule source) Memory.sizeFunction := by
  refine ⟨⟨0, rfl, ?_⟩, numeric_nil, by decide, ?_⟩
  · exact type_lookup source 0 (by omega)
  · exact MemoryValidity.size_body_typed _ rfl

theorem grow_valid (source : LeanExe.Core.Module) :
    Wasm.Encoding.Spec.Validity.Function (memoryModule source) growFunction := by
  refine ⟨⟨1, rfl, ?_⟩, numeric_nil, by decide, ?_⟩
  · exact type_lookup source 1 (by omega)
  · exact MemoryValidity.grow_body_typed _ rfl rfl

theorem runtime_valid (source : LeanExe.Core.Module) (function : Wasm.Function)
    (member : function ∈ runtimeFunctions) :
    Wasm.Encoding.Spec.Validity.Function (memoryModule source) function := by
  simp only [runtimeFunctions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact read_valid source
  · exact write_valid source
  · exact size_valid source
  · exact grow_valid source

/-- Source well-formedness and finite index limits suffice: the memory
primitives, memory declaration, and all runtime function types are proved here. -/
theorem module_valid_exports (source : LeanExe.Core.Module) (exports : List Wasm.Export)
    (formed : ∀ function ∈ source,
      WellFormed source LeanExe.Core.Memory.effectArity
        (function.params + function.locals) function.body ∧
      Reads (function.params + function.locals) function.result.reads)
    (localBound : ∀ function ∈ source,
      function.params + function.locals + max (width function.body) function.result.scratchWidth < 2 ^ 32)
    (functionBound : source.length + 4 < 2 ^ 32)
    (exportBound : ∀ entry ∈ exports, entry.funcIdx < source.length + 4)
    (exportNames : (exports.map Wasm.Export.name).Nodup) :
    Wasm.Encoding.Spec.Validity.Module (memoryModule source exports) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> rfl
  · intro type member
    change type ∈ (List.range (max (maxParams source) 2 + 1)).map functionSignature at member
    obtain ⟨arity, _, rfl⟩ := List.mem_map.mp member
    exact ⟨numeric_words arity, numeric_i64⟩
  · simp [memoryModule, Project.Core.compile]
  · intro compiled member
    change compiled ∈ source.map (compileFunction 0 (code source.length)) ++ runtimeFunctions at member
    rcases List.mem_append.mp member with original | runtime
    · obtain ⟨function, sourceMember, rfl⟩ := List.mem_map.mp original
      apply function_valid_in source (memoryModule source exports) (code source.length)
        LeanExe.Core.Memory.effectArity function (formed function sourceMember).1
        (formed function sourceMember).2
      · exact type_lookup source function.params
          ((maxParams_bound sourceMember).trans (Nat.le_max_left _ _))
      · intro callee foundFunction found
        simpa [functionTypes, memoryModule, Project.Core.compile] using
          source_type_lookup source callee foundFunction found
      · exact primitive_typed source
      · exact localBound function sourceMember
    · exact runtime_valid source compiled runtime
  · intro declaration member
    have same : memoryDeclaration = declaration := by simpa [memoryModule, Project.Core.compile] using member
    subst declaration
    simp [Wasm.Encoding.Spec.Validity.Memory, memoryDeclaration, UInt32.le_iff_toNat_le]
  · simp [memoryModule, Project.Core.compile]
  · simpa [memoryModule, Project.Core.compile, runtimeFunctions] using functionBound
  · simpa [memoryModule, Project.Core.compile, runtimeFunctions] using exportBound
  · simp [memoryModule, Project.Core.compile]
  · simp [memoryModule, Project.Core.compile]
  · simpa [Wasm.Encoding.Spec.exports, memoryModule, Project.Core.compile,
      List.map_map, Function.comp_def] using exportNames

/-- The module without function exports is the default case. -/
theorem module_valid (source : LeanExe.Core.Module)
    (formed : ∀ function ∈ source,
      WellFormed source LeanExe.Core.Memory.effectArity
        (function.params + function.locals) function.body ∧
      Reads (function.params + function.locals) function.result.reads)
    (localBound : ∀ function ∈ source,
      function.params + function.locals + max (width function.body) function.result.scratchWidth < 2 ^ 32)
    (functionBound : source.length + 4 < 2 ^ 32) :
    Wasm.Encoding.Spec.Validity.Module (memoryModule source) :=
  module_valid_exports source [] formed localBound functionBound (by simp) (by simp)

end Project.Core.MemoryModuleValidity
