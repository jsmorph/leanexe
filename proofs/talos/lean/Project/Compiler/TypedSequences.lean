import Project.Compiler.ValidationRules

namespace Project.Compiler.ArithmeticValidation

open Wasm.Binary
open Wasm.Binary.Validator
open Project.Compiler.ArithmeticEncoding

/-- Every compiler-allocated parameter, result, and scratch local has i64 type. -/
def Locals64 (context : Context) (count : Nat) : Prop :=
  ∀ index, index < count → context.locals (UInt32.ofNat index) = some .i64

/-- Internal typed encoding of an actual compiler instruction sequence. This
relation is constructed by the general expression proof, never required from
individual source programs. Stack prefixes allow sequential composition. -/
def Sequence (count : Nat) (input output : List ValType)
    (source : List LeanExe.Wasm.Instr) : Prop :=
  ∃ raw, ProgramEncoding source raw ∧
    ∀ (context : Context), Locals64 context count →
      ∀ (path : List Nat) (base index : Nat) (rest : List ValType), base ≤ rest.length →
        validateInstrs context path base { values := input ++ rest, polymorphic := false } index raw =
          .ok { values := output ++ rest, polymorphic := false }

theorem Sequence.nil (count : Nat) (types : List ValType) : Sequence count types types [] := by
  exact ⟨[], .nil, fun _ _ _ _ _ _ _ => rfl⟩

theorem Sequence.append {count : Nat} {input middle output : List ValType}
    {left right : List LeanExe.Wasm.Instr}
    (a : Sequence count input middle left) (b : Sequence count middle output right) :
    Sequence count input output (left ++ right) := by
  obtain ⟨ra, ea, va⟩ := a
  obtain ⟨rb, eb, vb⟩ := b
  refine ⟨ra ++ rb, ea.append eb, ?_⟩
  intro context locals path base index rest room
  exact validate_append (va context locals path base index rest room)
    (vb context locals path base (index + ra.length) rest room)

theorem Sequence.frame {count : Nat} {input output : List ValType}
    {source : List LeanExe.Wasm.Instr} (h : Sequence count input output source)
    (under : List ValType) : Sequence count (input ++ under) (output ++ under) source := by
  obtain ⟨raw, encoded, valid⟩ := h
  refine ⟨raw, encoded, ?_⟩
  intro context locals path base index rest room
  simpa only [List.append_assoc] using valid context locals path base index (under ++ rest)
    (by simp only [List.length_append]; omega)

theorem Sequence.atom {count : Nat} {input output : List ValType}
    {source : LeanExe.Wasm.Instr} {raw : Instr} (encoded : Atom source raw)
    (valid : ∀ (context : Context), Locals64 context count →
      ∀ (path : List Nat) (base : Nat) (rest : List ValType), base ≤ rest.length →
        validateInstr context path base { values := input ++ rest, polymorphic := false } raw =
          .ok { values := output ++ rest, polymorphic := false }) :
    Sequence count input output [source] := by
  refine ⟨[raw], .cons (.atom encoded) .nil, ?_⟩
  intro context locals path base index rest room
  exact validate_cons (valid context locals (path ++ [index]) base rest room) rfl

theorem Sequence.get (count index : Nat) (present : index < count) (bound : index < 2 ^ 32) :
    Sequence count [] [.i64] [.localGet index] := by
  apply Sequence.atom (.get index bound)
  intro context locals path base rest room
  simp only [validateInstr, locals index present]
  rfl

theorem Sequence.set (count index : Nat) (present : index < count) (bound : index < 2 ^ 32) :
    Sequence count [.i64] [] [.localSet index] := by
  apply Sequence.atom (.set index bound)
  intro context locals path base rest room
  simp only [validateInstr, locals index present]
  exact pop_typed context path base .i64 rest room

theorem Sequence.const (count value : Nat) : Sequence count [] [.i64] [.constI64 value] := by
  apply Sequence.atom (.const value)
  intro context locals path base rest room
  exact validate_const64 context path base { values := rest, polymorphic := false } (UInt64.ofNat value)

theorem Sequence.eq (count : Nat) : Sequence count [.i64, .i64] [.i32] [.eqI64] := by
  apply Sequence.atom .eq
  intro context locals path base rest room
  exact binary_typed context path base .i64 .i32 rest room

theorem Sequence.lt (count : Nat) : Sequence count [.i64, .i64] [.i32] [.ltUI64] := by
  apply Sequence.atom .lt
  intro context locals path base rest room
  exact binary_typed context path base .i64 .i32 rest room

theorem Sequence.le (count : Nat) : Sequence count [.i64, .i64] [.i32] [.leUI64] := by
  apply Sequence.atom .le
  intro context locals path base rest room
  exact binary_typed context path base .i64 .i32 rest room

theorem Sequence.eqz32 (count : Nat) : Sequence count [.i32] [.i32] [.eqzI32] := by
  apply Sequence.atom .eqz32
  intro context locals path base rest room
  exact unary_typed context path base .i32 .i32 rest room

theorem Sequence.operation (count : Nat) (op : LeanExe.Wasm.ScalarDescriptor.U64Op) :
    Sequence count [.i64, .i64] [.i64] [op.instruction] := by
  cases op
  all_goals apply Sequence.atom (by constructor)
  all_goals intro context locals path base rest room
  all_goals exact binary_typed context path base .i64 .i64 rest room

end Project.Compiler.ArithmeticValidation
