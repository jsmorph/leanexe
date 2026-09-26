import Project.Compiler.SectionParsing

namespace Project.Compiler.Parsing

open Wasm.Binary

theorem expect_bytes (bytes : List UInt8) : Parses (Parser.expectBytes bytes) bytes () := by
  induction bytes with
  | nil => exact pure_parses ()
  | cons byte bytes ih =>
    unfold Parser.expectBytes
    exact bind_parses (expect_byte byte) ih

/-- The exact module magic and version followed by a complete section stream. -/
theorem module_end (sections : List UInt8) (raw : RawModule)
    (h : ParsesEnd (sectionLoop sections.length 0 default) sections raw) :
    ParsesEnd moduleParser ([0, 97, 115, 109, 1, 0, 0, 0] ++ sections) raw := by
  have bodyParsed : ParsesEnd (remainingBytes >>= fun n => sectionLoop n 0 default) sections raw :=
    remaining_end (q := fun n => sectionLoop n 0 default) h
  have versionParsed := bind_end
    (q := fun _ : Unit => remainingBytes >>= fun n => sectionLoop n 0 default)
    (expect_bytes [1, 0, 0, 0]) bodyParsed
  have allParsed := bind_end
    (q := fun _ : Unit => do
      Parser.expectBytes [1, 0, 0, 0]
      let n ← remainingBytes
      sectionLoop n 0 default)
    (expect_bytes [0, 97, 115, 109]) versionParsed
  exact allParsed

end Project.Compiler.Parsing
