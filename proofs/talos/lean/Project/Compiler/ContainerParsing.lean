import Project.Compiler.LebParsing
import Project.Artifact.Binary.Primitives

namespace Project.Compiler.Parsing

open Wasm.Binary

theorem expect_byte (byte : UInt8) : Parses (Parser.expectByte byte) [byte] () := by
  intro before after limit enough within
  have h := read_byte byte before after limit enough within
  unfold Parser.expectByte
  change Except.bind (.ok (before.length, cursor _ _ _)) _ = _
  simp only [Except.bind]
  change Except.bind (Parser.readByte (cursor _ _ _)) _ = _
  rw [h]
  dsimp only [Except.bind]
  change (if byte = byte then (fun c : Cursor => (Except.ok ((), c) : Except Error (Unit × Cursor)))
    else (fun _ => Except.error { offset := before.length, kind := ErrorKind.expectedByte byte byte }))
    (cursor (before ++ [byte] ++ after) (before.length + [byte].length) limit) = _
  rw [if_pos rfl]

theorem bounded {p : Parser α} {bytes : List UInt8} {value : α}
    (h : Parses p bytes value) : Parses (Parser.bounded bytes.length p) bytes value := by
  intro before after limit enough within
  have result := h before after (before.length + bytes.length) le_rfl (by omega)
  have room : bytes.length ≤ limit - before.length := by omega
  have fits : before.length + bytes.length ≤ (before ++ bytes ++ after).toArray.size := by
    simp
  simp only [Parser.bounded, cursor, Cursor.remaining, ByteArray.size,
    room, fits, decide_true, Bool.true_and, ite_true]
  dsimp only [cursor] at result
  rw [result]
  simp

theorem sized {p : Parser α} {bytes : List UInt8} {value : α}
    (h : Parses p bytes value) (bound : bytes.length < 2 ^ 32) :
    Parses (Wasm.Binary.sized p) (LeanExe.Wasm.Binary.u32leb bytes.length ++ bytes) value := by
  unfold Wasm.Binary.sized
  apply bind_parses (u32 bytes.length bound)
  simpa only [UInt32.toNat_ofNat_of_lt' bound] using bounded h

theorem vector_loop {p : Parser α} {bytes : List (List UInt8)} {values : List α}
    (items : List.Forall₂ (Parses p) bytes values) :
    Parses (Wasm.Binary.Internal.vectorLoop p values.length) bytes.flatten values := by
  induction items with
  | nil => exact pure_parses []
  | cons first rest ih =>
    unfold Wasm.Binary.Internal.vectorLoop
    exact bind_parses first (map_parses ih (fun tail => _ :: tail))

theorem vector_rest {p : Parser α} {bytes : List UInt8} {values : List α}
    (h : Parses (Wasm.Binary.Internal.vectorLoop p values.length) bytes values)
    (minimum : values.length ≤ bytes.length) :
    Parses (do
      let remaining ← (fun c => .ok (c.remaining, c) : Parser Nat)
      if values.length ≤ remaining then Wasm.Binary.Internal.vectorLoop p values.length
      else Parser.fail (.vectorLengthExceedsInput values.length remaining)) bytes values := by
  intro before after limit enough within
  have available : values.length ≤ limit - before.length := by omega
  change Except.bind (.ok (limit - before.length, cursor _ _ _)) _ = _
  simpa only [Except.bind, available, ↓reduceIte] using h before after limit enough within

theorem vector {p : Parser α} {bytes : List (List UInt8)} {values : List α}
    (items : List.Forall₂ (Parses p) bytes values)
    (minimum : values.length ≤ bytes.flatten.length) (bound : values.length < 2 ^ 32) :
    Parses (Wasm.Binary.vector p)
      (LeanExe.Wasm.Binary.u32leb values.length ++ bytes.flatten) values := by
  unfold Wasm.Binary.vector
  apply bind_parses (u32 values.length bound)
  simpa only [UInt32.toNat_ofNat_of_lt' bound] using vector_rest (vector_loop items) minimum

end Project.Compiler.Parsing
