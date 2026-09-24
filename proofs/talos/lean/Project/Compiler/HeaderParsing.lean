import Project.Compiler.FunctionParsing

namespace Project.Compiler.Parsing

open Wasm.Binary

theorem read_bytes (bytes : List UInt8) : Parses (Parser.readBytes bytes.length) bytes bytes := by
  intro before after limit enough within
  have room : bytes.length ≤ limit - before.length := by omega
  simp [Parser.readBytes, cursor, Cursor.remaining, ByteArray.size, room,
    ByteArray.data_extract, List.extract_eq_take_drop, List.append_assoc]

theorem byte_vector (bytes : List UInt8) (bound : bytes.length < 2 ^ 32) :
    Parses byteVector (LeanExe.Wasm.Binary.byteVec bytes) bytes := by
  rw [ContainerEncoding.byte_vector]
  unfold byteVector
  apply bind_parses (u32 bytes.length bound)
  simpa only [UInt32.toNat_ofNat_of_lt' bound] using read_bytes bytes

theorem utf8_roundtrip (text : String) : String.fromUTF8? text.toUTF8 = some text := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, text.isValidUTF8, dite_true]
  rfl

theorem name (text : String) (bound : text.toUTF8.size < 2 ^ 32) :
    Parses Wasm.Binary.name (LeanExe.Wasm.Binary.name text)
      { bytes := text.toUTF8.data.toList, text } := by
  unfold Wasm.Binary.name LeanExe.Wasm.Binary.name
  apply bind_last (byte_vector text.toUTF8.data.toList (by simpa only [Array.length_toList, ByteArray.size] using bound))
  have same : text.toUTF8.data.toList.toByteArray = text.toUTF8 := by
    apply ByteArray.ext
    simp only [List.data_toByteArray, Array.toArray_toList]
  rw [same, utf8_roundtrip]
  exact pure_parses _

theorem replicate_values (count : Nat) (bound : count < 2 ^ 32) :
    Parses (Wasm.Binary.vector valType)
      (LeanExe.Wasm.Binary.byteVec (List.replicate count 126)) (List.replicate count .i64) := by
  have items : List.Forall₂ (Parses valType) (List.replicate count [126]) (List.replicate count .i64) := by
    induction count with
    | zero => exact .nil
    | succ n ih => exact .cons val_i64 (ih (by omega))
  have parsed := vector items (by simp) (by simpa using bound)
  simpa [ContainerEncoding.byte_vector] using parsed

theorem function_type (params results : Nat) (pb : params < 2 ^ 32) (rb : results < 2 ^ 32) :
    Parses funcType
      (LeanExe.Wasm.Binary.funcType (List.replicate params 126) (List.replicate results 126))
      { params := List.replicate params .i64, results := List.replicate results .i64 } := by
  unfold funcType LeanExe.Wasm.Binary.funcType
  apply bind_parses (a := [96]) (expect_byte 96)
  apply bind_parses (replicate_values params pb)
  exact map_parses (replicate_values results rb)
    (fun values => ({ params := List.replicate params .i64, results := values } : FuncType))

end Project.Compiler.Parsing
