import Project.Compiler.ArithmeticEncoding
import LeanExe.Wasm.ArithmeticAdmission

namespace Project.Compiler.ArithmeticEncoding

open LeanExe.Wasm.ScalarDescriptor

/-- Internal existence of a raw binary syntax tree; derived from source admission,
never supplied as a correctness certificate by a compiler caller. -/
def Encodable (code : List LeanExe.Wasm.Instr) : Prop :=
  ∃ raw, ProgramEncoding code raw

theorem ProgramEncoding.append {a b ra rb}
    (left : ProgramEncoding a ra) (right : ProgramEncoding b rb) :
    ProgramEncoding (a ++ b) (ra ++ rb) := by
  induction a generalizing ra with
  | nil => cases left; exact right
  | cons head tail ih =>
    cases left with
    | cons eh et => exact .cons eh (ih et)

theorem Encodable.nil : Encodable [] := ⟨[], .nil⟩

theorem Encodable.atom {a b} (h : Atom a b) : Encodable [a] :=
  ⟨[b], .cons (.atom h) .nil⟩

theorem Encodable.append {a b} (left : Encodable a) (right : Encodable b) :
    Encodable (a ++ b) := by
  obtain ⟨ra, ha⟩ := left
  obtain ⟨rb, hb⟩ := right
  exact ⟨ra ++ rb, ha.append hb⟩

theorem Encodable.iff {a b} (left : Encodable a) (right : Encodable b) :
    Encodable [.iff true a (some b)] := by
  obtain ⟨ra, ha⟩ := left
  obtain ⟨rb, hb⟩ := right
  exact ⟨[.iff (.value .i64) ra (some rb)], .cons (.if64 ha hb) .nil⟩

theorem operation_encodable (op : U64Op) : Encodable [op.instruction] := by
  cases op
  · exact .atom .add
  · exact .atom .sub
  · exact .atom .mul
  · exact .atom .div
  · exact .atom .rem
  · exact .atom .and
  · exact .atom .or
  · exact .atom .xor
  · exact .atom .shl
  · exact .atom .shr

theorem checked_tail (scratch : Nat) (op : U64Op) (zero : List LeanExe.Wasm.Instr)
    (zeroEncoded : Encodable zero) (bound : scratch + 1 < 2 ^ 32) :
    Encodable [.localGet (scratch + 1), .constI64 0, .eqI64,
      .iff true zero (some [.localGet scratch, .localGet (scratch + 1), op.instruction])] := by
  have first : scratch < 2 ^ 32 := by omega
  have branches := zeroEncoded.iff
    ((Encodable.atom (.get scratch first)).append
      ((Encodable.atom (.get (scratch + 1) bound)).append (operation_encodable op)))
  exact (Encodable.atom (.get (scratch + 1) bound)).append
    ((Encodable.atom (.const 0)).append ((Encodable.atom .eq).append branches))

theorem arithmetic_encodable {e : Expr} (arithmetic : e.Arithmetic) (scratch : Nat)
    (reads : ∀ index ∈ e.reads, index < 2 ^ 32)
    (room : scratch + e.scratchWidth ≤ 2 ^ 32) : Encodable (e.emit scratch) := by
  induction arithmetic generalizing scratch with
  | get => exact .atom (.get _ (reads _ (by simp [Expr.reads])))
  | const => exact .atom (.const _)
  | @bin left right op al ar ihl ihr =>
    have leftReads : ∀ index ∈ left.reads, index < 2 ^ 32 := by
      intro index member; exact reads index (by simp [Expr.reads, member])
    have rightReads : ∀ index ∈ right.reads, index < 2 ^ 32 := by
      intro index member; exact reads index (by simp [Expr.reads, member])
    by_cases checked : (op == .divU || op == .remU) = true
    · have capacity : scratch + (max left.scratchWidth right.scratchWidth + 2) ≤ 2 ^ 32 := by
        simpa only [Expr.scratchWidth, checked, ite_true] using room
      have slot : scratch + 1 < 2 ^ 32 := by omega
      have first : scratch < 2 ^ 32 := by omega
      have l := ihl (scratch + 2) leftReads (by omega)
      have r := ihr (scratch + 2) rightReads (by omega)
      have zeroEncoded : Encodable (if op == .divU then [.constI64 0] else [.localGet scratch]) := by
        split
        · exact .atom (.const 0)
        · exact .atom (.get scratch first)
      simpa only [Expr.emit, checked, ite_true, List.append_assoc] using
        (((l.append (.atom (.set scratch first))).append
          (r.append (.atom (.set (scratch + 1) slot)))).append
          (checked_tail scratch op _ zeroEncoded slot))
    · have capacity : scratch + max left.scratchWidth right.scratchWidth ≤ 2 ^ 32 := by
        simpa only [Expr.scratchWidth, checked, Bool.false_eq_true, ite_false] using room
      simpa only [Expr.emit, checked, Bool.false_eq_true, ite_false, List.append_assoc] using
        (ihl scratch leftReads (by omega)).append
          ((ihr scratch rightReads (by omega)).append (operation_encodable op))

end Project.Compiler.ArithmeticEncoding
