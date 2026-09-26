import Project.Compiler.ArithmeticEncoding

namespace Project.Compiler.ContainerEncoding

open LeanExe.Wasm.Binary
open Project.Compiler.ArithmeticEncoding

theorem byte_vector (bytes : List UInt8) : byteVec bytes = u32leb bytes.length ++ bytes := by
  simp [byteVec, LeanExe.Wasm.Leb.byteVecBytes, u32leb, byteArray_toList,
    ByteArray.toList_data_append, ByteArray.size]

theorem section_bytes (id : Nat) (payload : List UInt8) :
    wasmSection id payload = [UInt8.ofNat id] ++ u32leb payload.length ++ payload := by
  simp [wasmSection, LeanExe.Wasm.Leb.sectionBytes, u32leb, byteArray_toList,
    ByteArray.toList_data_append, ByteArray.push, ByteArray.size]

private theorem fold_bytes (items : List ByteArray) (acc : ByteArray) :
    (items.foldl (· ++ ·) acc).toList = acc.toList ++ (items.map ByteArray.toList).flatten := by
  induction items generalizing acc with
  | nil => simp
  | cons a b ih => simp [List.foldl_cons, ih, List.append_assoc]

theorem vector (items : List (List UInt8)) :
    vec items = u32leb items.length ++ items.flatten := by
  simp only [vec, LeanExe.Wasm.Leb.vecBytes, List.size_toArray, List.length_map,
    List.forIn_toArray, List.forIn_pure_yield_eq_foldl, Id.run_pure, u32leb, pure_bind]
  rw [fold_bytes]
  simp [byteArray_toList, Function.comp_def]

private theorem fold_unsigned (items : List UInt64) (acc : ByteArray) :
    (items.foldl (fun bytes value => bytes ++ LeanExe.Wasm.Leb.u32lebU64 value) acc).toList =
      acc.toList ++ (items.map (fun value => (LeanExe.Wasm.Leb.u32lebU64 value).toList)).flatten := by
  induction items generalizing acc with
  | nil => simp
  | cons a b ih => simp [List.foldl_cons, ih, List.append_assoc]

theorem unsigned_vector (values : List Nat) :
    u32Vec values = vec (values.map u32leb) := by
  rw [vector]
  simp only [u32Vec, LeanExe.Wasm.Leb.u32VecBytes, List.size_toArray, List.length_map,
    List.forIn_toArray, List.forIn_pure_yield_eq_foldl, Id.run_pure, pure_bind]
  rw [fold_unsigned]
  simp only [List.map_map, u32leb, Function.comp_def]
  rfl

end Project.Compiler.ContainerEncoding
