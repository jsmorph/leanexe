import Project.Compiler.FixedPayloads

namespace Project.Compiler.ArithmeticModule

open Project.Compiler.Parsing

theorem constant_length (n : Nat) : (LeanExe.Wasm.Binary.i64Const n).length ≤ 11 := by
  unfold LeanExe.Wasm.Binary.i64Const LeanExe.Wasm.Binary.s64lebInt
  simp only [List.length_cons]
  exact Nat.succ_le_succ (LebLengths.signed _)

theorem global_length (n : Nat) : (globalBytes n).length ≤ 14 := by
  have h := constant_length n
  simp only [globalBytes, LeanExe.Wasm.Binary.ofNats, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  omega

theorem memory_bound : memoryPayload.length < 2 ^ 32 := by
  have h := vector_length memoryItems
  have leb := LebLengths.unsigned 16
  simp only [memoryItems, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_append, List.length_cons, List.length_nil] at h
  change memoryPayload.length ≤ 10 + (1 + (LeanExe.Wasm.Leb.u32lebU64 16).toList.length) at h
  omega

theorem globals_bound : globalPayload.length < 2 ^ 32 := by
  have h := vector_length globalItems
  have zero := global_length 0
  have initial := global_length 4096
  simp only [globalItems, List.flatten_cons, List.flatten_nil, List.length_append,
    List.length_nil] at h
  change globalPayload.length ≤ _ at h
  omega

theorem functions_bound : functionPayload.length < 2 ^ 32 := by
  have h := unsigned_vector_length (List.range 5)
  simp only [List.length_range] at h
  change functionPayload.length ≤ _ at h
  omega

end Project.Compiler.ArithmeticModule
