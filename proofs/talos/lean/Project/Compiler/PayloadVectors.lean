import Project.Compiler.HeaderParsing
import Project.Compiler.LebLengths

namespace Project.Compiler.Parsing

open Wasm.Binary

theorem unsigned_nonempty (n : Nat) : 0 < (LeanExe.Wasm.Binary.u32leb n).length := by
  rw [LeanExe.Wasm.Binary.u32leb, byteArray_toList, LeanExe.Wasm.Leb.u32lebU64_eq_lebList]
  rw [LeanExe.Wasm.Leb.lebList]
  split <;> simp only [List.length_cons, List.length_nil] <;> omega

private theorem flatten_minimum (bytes : List (List UInt8))
    (positive : ∀ bs ∈ bytes, 0 < bs.length) : bytes.length ≤ bytes.flatten.length := by
  induction bytes with
  | nil => exact Nat.le_refl 0
  | cons a b ih =>
    have ha := positive a (by simp)
    have hb := ih (fun bs member => positive bs (by simp [member]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

theorem encoded_vector {p : Parser α} {bytes : List (List UInt8)} {values : List α}
    (items : List.Forall₂ (Parses p) bytes values)
    (positive : ∀ bs ∈ bytes, 0 < bs.length) (bound : values.length < 2 ^ 32) :
    Parses (Wasm.Binary.vector p) (LeanExe.Wasm.Binary.vec bytes) values := by
  rw [ContainerEncoding.vector, items.length_eq]
  exact vector items (by rw [← items.length_eq]; exact flatten_minimum bytes positive) bound

theorem unsigned_vector (values : List Nat)
    (bounded : ∀ n ∈ values, n < 2 ^ 32) (count : values.length < 2 ^ 32) :
    Parses (Wasm.Binary.vector Leb.u32) (LeanExe.Wasm.Binary.u32Vec values)
      (values.map UInt32.ofNat) := by
  rw [ContainerEncoding.unsigned_vector]
  have items : List.Forall₂ (Parses Leb.u32)
      (values.map LeanExe.Wasm.Binary.u32leb) (values.map UInt32.ofNat) := by
    induction values with
    | nil => exact .nil
    | cons a b ih =>
      exact .cons (u32 a (bounded a (by simp)))
        (ih (fun n hn => bounded n (by simp [hn])) (by simpa using Nat.lt_of_succ_lt count))
  apply encoded_vector items
  · intro bs member
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
    exact unsigned_nonempty n
  · simpa using count

theorem vector_length (bytes : List (List UInt8)) :
    (LeanExe.Wasm.Binary.vec bytes).length ≤ 10 + bytes.flatten.length := by
  rw [ContainerEncoding.vector, List.length_append]
  exact Nat.add_le_add_right (LebLengths.unsigned (UInt64.ofNat bytes.length)) _

theorem unsigned_vector_length (values : List Nat) :
    (LeanExe.Wasm.Binary.u32Vec values).length ≤ 10 + 10 * values.length := by
  rw [ContainerEncoding.unsigned_vector]
  have flat : (values.map LeanExe.Wasm.Binary.u32leb).flatten.length ≤ 10 * values.length := by
    induction values with
    | nil => simp
    | cons a b ih =>
      have ha := LebLengths.unsigned (UInt64.ofNat a)
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      change (LeanExe.Wasm.Leb.u32lebU64 (UInt64.ofNat a)).toList.length + _ ≤ _
      omega
  have h := vector_length (values.map LeanExe.Wasm.Binary.u32leb)
  omega

end Project.Compiler.Parsing
