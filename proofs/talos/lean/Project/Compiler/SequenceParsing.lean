import Project.Compiler.ArithmeticParsing

namespace Project.Compiler.Parsing

open Wasm.Binary

def endByte : Terminator → UInt8
  | .end => 11
  | .otherwise => 5

theorem sequence_end (fuel : Nat) (allow : Bool) (term : Terminator)
    (allowed : term = .otherwise → allow = true) :
    Parses (instructionSequence (fuel + 1) allow) [endByte term] ([], term) := by
  unfold instructionSequence
  apply peek_then (tail := [])
  cases term with
  | «end» =>
    change Parses (Parser.readByte >>= fun _ => pure ([], Terminator.end)) [11] ([], .end)
    exact map_parses (read_byte 11) (fun _ => (([] : List Instr), Terminator.end))
  | otherwise =>
    have ha : allow = true := allowed rfl
    subst allow
    change Parses (Parser.readByte >>= fun _ => pure ([], Terminator.otherwise)) [5] ([], .otherwise)
    exact map_parses (read_byte 5) (fun _ => (([] : List Instr), Terminator.otherwise))

theorem sequence_cons (fuel : Nat) (allow : Bool) (headBytes tailBytes : List UInt8)
    (head : Instr) (tail : List Instr) (term : Terminator)
    (first : Parses (instruction fuel) headBytes head)
    (rest : Parses (instructionSequence fuel allow) tailBytes (tail, term))
    (header : ∃ opcode bytes, headBytes = opcode :: bytes ∧ opcode ≠ 11 ∧ opcode ≠ 5) :
    Parses (instructionSequence (fuel + 1) allow) (headBytes ++ tailBytes) (head :: tail, term) := by
  obtain ⟨opcode, bytes, rfl, notEnd, notElse⟩ := header
  unfold instructionSequence
  change Parses (Parser.peekByte >>= _) (opcode :: (bytes ++ tailBytes)) _
  apply peek_then
  simp only [notEnd, notElse, ite_false]
  apply bind_parses first
  exact map_parses rest (fun result => (head :: result.1, result.2))

theorem grammar_prefix {bytes : List UInt8} {instruction : Instr}
    (h : Grammar.Instr bytes instruction) :
    ∃ opcode rest, bytes = opcode :: rest ∧ opcode ≠ 11 ∧ opcode ≠ 5 := by
  cases h <;> exact ⟨_, _, rfl, by decide, by decide⟩

theorem grammar_nonempty {bytes : List UInt8} {instruction : Instr}
    (h : Grammar.Instr bytes instruction) : 0 < bytes.length := by
  obtain ⟨opcode, rest, rfl, _, _⟩ := grammar_prefix h
  simp

theorem block_i64 : Parses blockType [126] (.value .i64) := by
  unfold blockType
  apply bind_parses (a := [126]) (b := []) (read_byte 126)
  exact pure_parses _

end Project.Compiler.Parsing
