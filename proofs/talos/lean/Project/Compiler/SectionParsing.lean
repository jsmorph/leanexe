import Project.Compiler.MetadataParsing

namespace Project.Compiler.Parsing

open Wasm.Binary

/-- Parsing that consumes the entire enclosing input, while remaining independent
of its offset and bytes outside its limit. Used for the module section loop. -/
def ParsesEnd (parser : Parser α) (bytes : List UInt8) (value : α) : Prop :=
  ∀ before after : List UInt8,
    parser (cursor (before ++ bytes ++ after) before.length (before.length + bytes.length)) =
      .ok (value, cursor (before ++ bytes ++ after) (before.length + bytes.length)
        (before.length + bytes.length))

theorem Parses.toEnd {parser : Parser α} {bytes : List UInt8} {value : α}
    (h : Parses parser bytes value) : ParsesEnd parser bytes value := by
  intro before after
  exact h before after _ le_rfl (by omega)

theorem bind_end {p : Parser α} {q : α → Parser β} {a b : List UInt8} {x : α} {y : β}
    (first : Parses p a x) (rest : ParsesEnd (q x) b y) :
    ParsesEnd (p >>= q) (a ++ b) y := by
  intro before after
  have hp := first before (b ++ after) (before.length + (a ++ b).length)
    (by simp <;> omega) (by simp <;> omega)
  have hq := rest (before ++ a) after
  simp only [List.length_append, List.append_assoc, Nat.add_assoc] at hp hq ⊢
  change Except.bind (p (cursor _ _ _)) _ = _
  rw [hp]
  exact hq

theorem remaining_end {q : Nat → Parser α} {bytes : List UInt8} {value : α}
    (h : ParsesEnd (q bytes.length) bytes value) :
    ParsesEnd (remainingBytes >>= q) bytes value := by
  intro before after
  have result := h before after
  change Except.bind (.ok (before.length + bytes.length - before.length, cursor _ _ _)) _ = _
  simpa only [Nat.add_sub_cancel_left, Except.bind] using result

theorem section_info (id : SectionId) : sectionInfo id.byte = .ok (id, id.rank) := by
  cases id <;> rfl

theorem sections_end (fuel lastRank : Nat) (module_ : RawModule) :
    ParsesEnd (sectionLoop fuel lastRank module_) [] module_ := by
  cases fuel <;> unfold sectionLoop <;> apply remaining_end <;>
    exact (pure_parses module_).toEnd

theorem sections_cons (fuel lastRank : Nat) (id : SectionId)
    (module_ middle result : RawModule) (payload rest : List UInt8)
    (fresh : id ∉ module_.sections) (ordered : lastRank < id.rank)
    (headParsed : Parses (parseSection id module_) payload middle)
    (tailParsed : ParsesEnd (sectionLoop fuel id.rank
      { middle with sections := middle.sections ++ [id] }) rest result) :
    ParsesEnd (sectionLoop (fuel + 1) lastRank module_) (id.byte :: (payload ++ rest)) result := by
  unfold sectionLoop
  apply remaining_end
  simp only [List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
  unfold sectionStep
  apply bind_end (a := [id.byte]) (read_byte id.byte)
  rw [section_info]
  simp only [fresh, not_le.mpr ordered, ite_false]
  exact bind_end headParsed tailParsed

theorem ParsesEnd.runAll {p : Parser α} {bytes : List UInt8} {value : α}
    (h : ParsesEnd p bytes value) : Parser.runAll p (ByteArray.mk bytes.toArray) = .ok value := by
  have parsed := h [] []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at parsed
  unfold Parser.runAll Parser.run Cursor.start
  simp only [ByteArray.size, List.size_toArray]
  change Except.bind (p (cursor bytes 0 bytes.length)) _ = _
  rw [parsed]
  simp only [Except.bind]
  simp [cursor]
  rfl

end Project.Compiler.Parsing
