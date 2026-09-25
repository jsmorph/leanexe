import Project.Compiler.SequenceParsing

namespace Project.Compiler.ArithmeticEncoding

open Project.Compiler.Parsing

mutual
  theorem InstructionEncoding.parses {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
      (h : InstructionEncoding a b) (fuel : Nat)
      (room : (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a).length ≤ fuel) :
      Parses (Wasm.Binary.instruction fuel) (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a) b := by
    have positive := grammar_nonempty h.grammar
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases h with
      | atom h => exact h.parses fuel
      | @if64 a ra b rb left right =>
        have shape : LeanExe.Wasm.Binary.CoreWasm.encodeInstr (.iff true a (some b)) =
            [4, 126] ++ (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [5]) ++
              (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs b ++ [11]) := by
          simp [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
            image_sequence, List.append_assoc]
        rw [shape] at room ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at room
        have lp := ProgramEncoding.parses left fuel true .otherwise (by omega) (fun _ => rfl)
        have rp := ProgramEncoding.parses right fuel false .end (by omega) (by intro h; cases h)
        suffices parsed : Parses (Wasm.Binary.instruction (fuel + 1))
            ([4] ++ ([126] ++ ((LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [5]) ++
              (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs b ++ [11]))))
            (Wasm.Binary.Instr.iff (.value .i64) ra (some rb)) by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using parsed
        unfold Wasm.Binary.instruction
        apply bind_parses (a := [4]) (read_byte 4)
        apply bind_parses (a := [126]) block_i64
        apply bind_parses lp
        apply bind_last rp
        exact pure_parses _
      | @if0 a ra b rb left right =>
        have shape : LeanExe.Wasm.Binary.CoreWasm.encodeInstr (.iff false a (some b)) =
            [4, 64] ++ (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [5]) ++
              (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs b ++ [11]) := by
          simp [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
            image_sequence, List.append_assoc]
        rw [shape] at room ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at room
        have lp := ProgramEncoding.parses left fuel true .otherwise (by omega) (fun _ => rfl)
        have rp := ProgramEncoding.parses right fuel false .end (by omega) (by intro h; cases h)
        suffices parsed : Parses (Wasm.Binary.instruction (fuel + 1))
            ([4] ++ ([64] ++ ((LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [5]) ++
              (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs b ++ [11]))))
            (Wasm.Binary.Instr.iff .empty ra (some rb)) by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using parsed
        unfold Wasm.Binary.instruction
        apply bind_parses (a := [4]) (read_byte 4)
        apply bind_parses (a := [64]) block_empty
        apply bind_parses lp
        apply bind_last rp
        exact pure_parses _
      | @block0 a ra body =>
        have shape : LeanExe.Wasm.Binary.CoreWasm.encodeInstr (.block a) =
            [2, 64] ++ (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [11]) := by
          simp [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
            image_sequence, List.append_assoc]
        rw [shape] at room ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at room
        have bp := ProgramEncoding.parses body fuel false .end (by omega) (by intro h; cases h)
        suffices parsed : Parses (Wasm.Binary.instruction (fuel + 1))
            ([2] ++ ([64] ++ (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [11])))
            (Wasm.Binary.Instr.block .empty ra) by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using parsed
        unfold Wasm.Binary.instruction
        apply bind_parses (a := [2]) (read_byte 2)
        apply bind_parses (a := [64]) block_empty
        apply bind_last bp
        exact pure_parses _
      | @loop0 a ra body =>
        have shape : LeanExe.Wasm.Binary.CoreWasm.encodeInstr (.loop a) =
            [3, 64] ++ (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [11]) := by
          simp [LeanExe.Wasm.Binary.CoreWasm.encodeInstr, LeanExe.Wasm.Image.emitInstr,
            image_sequence, List.append_assoc]
        rw [shape] at room ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at room
        have bp := ProgramEncoding.parses body fuel false .end (by omega) (by intro h; cases h)
        suffices parsed : Parses (Wasm.Binary.instruction (fuel + 1))
            ([3] ++ ([64] ++ (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [11])))
            (Wasm.Binary.Instr.loop .empty ra) by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using parsed
        unfold Wasm.Binary.instruction
        apply bind_parses (a := [3]) (read_byte 3)
        apply bind_parses (a := [64]) block_empty
        apply bind_last bp
        exact pure_parses _
  termination_by sizeOf a

  theorem ProgramEncoding.parses {a : List LeanExe.Wasm.Instr} {b : List Wasm.Binary.Instr}
      (h : ProgramEncoding a b) (fuel : Nat) (allow : Bool) (term : Wasm.Binary.Terminator)
      (room : (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a).length + 1 ≤ fuel)
      (allowed : term = .otherwise → allow = true) :
      Parses (Wasm.Binary.instructionSequence fuel allow)
        (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [endByte term]) (b, term) := by
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases h with
      | nil => exact sequence_end fuel allow term allowed
      | @cons head rawHead tail rawTail eh et =>
        have positive := grammar_nonempty eh.grammar
        simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstrs, List.length_append] at room
        have hp := InstructionEncoding.parses eh fuel (by omega)
        have tp := ProgramEncoding.parses et fuel allow term (by omega) allowed
        simpa only [LeanExe.Wasm.Binary.CoreWasm.encodeInstrs, List.append_assoc] using
          sequence_cons fuel allow _ _ rawHead rawTail term hp tp (grammar_prefix eh.grammar)
  termination_by sizeOf a
end

/-- The existing expression parser consumes the complete production byte stream,
including its terminator, at any enclosing byte position and limit. -/
theorem ProgramEncoding.expression_parses {a : List LeanExe.Wasm.Instr}
    {b : List Wasm.Binary.Instr} (h : ProgramEncoding a b) :
    Parses Wasm.Binary.expression
      (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a ++ [11]) b := by
  intro before after limit enough within
  have room : (LeanExe.Wasm.Binary.CoreWasm.encodeInstrs a).length + 1 ≤ limit - before.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at enough
    omega
  have parsed := h.parses (limit - before.length) false .end room
    (by intro impossible; cases impossible) before after limit enough within
  simp only [endByte] at parsed
  simp only [Wasm.Binary.expression, cursor, Wasm.Binary.Cursor.remaining] at parsed ⊢
  rw [parsed]

end Project.Compiler.ArithmeticEncoding
