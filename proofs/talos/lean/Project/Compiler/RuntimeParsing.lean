import Project.Compiler.RuntimeStructure

namespace Project.Compiler.RuntimeEncoding

open Project.Compiler.Parsing
open Project.Compiler.ArithmeticEncoding

theorem RuntimeInstruction.nonempty {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
    (h : RuntimeInstruction a b) : 0 < (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a).length := by
  obtain ⟨opcode, rest, shape, _, _⟩ := h.prefix
  simp [shape]

mutual
  theorem RuntimeInstruction.parses {a : LeanExe.Wasm.Instr} {b : Wasm.Binary.Instr}
      (h : RuntimeInstruction a b) (fuel : Nat)
      (room : (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a).length ≤ fuel) :
      Parses (Wasm.Binary.instruction fuel) (LeanExe.Wasm.Binary.CoreWasm.encodeInstr a) b := by
    have positive := h.nonempty
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases h with
      | atom h => exact h.parses fuel
      | @control a b kind body =>
        rw [control_bytes] at room ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at room
        have bp := RuntimeProgram.parses body fuel kind.allowElse .end (by omega)
          (by intro impossible; cases impossible)
        cases kind <;> unfold Wasm.Binary.instruction
        · apply bind_parses (a := [2]) (read_byte 2)
          apply bind_parses (a := [64]) block_empty
          apply bind_last bp
          exact pure_parses _
        · apply bind_parses (a := [3]) (read_byte 3)
          apply bind_parses (a := [64]) block_empty
          apply bind_last bp
          exact pure_parses _
        · apply bind_parses (a := [4]) (read_byte 4)
          apply bind_parses (a := [64]) block_empty
          apply bind_last bp
          exact pure_parses _
      | @ifElse a ra b rb left right =>
        rw [if_else_bytes] at room ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at room
        have lp := RuntimeProgram.parses left fuel true .otherwise (by omega) (fun _ => rfl)
        have rp := RuntimeProgram.parses right fuel false .end (by omega) (by intro h; cases h)
        unfold Wasm.Binary.instruction
        apply bind_parses (a := [4]) (read_byte 4)
        apply bind_parses (a := [64]) block_empty
        apply bind_parses lp
        apply bind_last rp
        exact pure_parses _
  termination_by fuel

  theorem RuntimeProgram.parses {a : List LeanExe.Wasm.Instr} {b : List Wasm.Binary.Instr}
      (h : RuntimeProgram a b) (fuel : Nat) (allow : Bool) (term : Wasm.Binary.Terminator)
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
        have positive := eh.nonempty
        simp only [LeanExe.Wasm.Binary.CoreWasm.encodeInstrs, List.length_append] at room
        have hp := RuntimeInstruction.parses eh fuel (by omega)
        have tp := RuntimeProgram.parses et fuel allow term (by omega) allowed
        simpa only [LeanExe.Wasm.Binary.CoreWasm.encodeInstrs, List.append_assoc] using
          sequence_cons fuel allow _ _ rawHead rawTail term hp tp eh.prefix
  termination_by fuel
end

theorem RuntimeProgram.expression_parses {a : List LeanExe.Wasm.Instr}
    {b : List Wasm.Binary.Instr} (h : RuntimeProgram a b) :
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

end Project.Compiler.RuntimeEncoding
