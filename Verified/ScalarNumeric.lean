import Verified.ScalarAtoms

namespace Wasm

macro "scalar_atom" : tactic => `(tactic|
  (intro fuel
   cases fuel with
   | zero => intros; simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
   | succ fuel =>
     intros
     simp only [execOne.eq_def]
     repeat' first | rfl | split))

theorem OneUniform.subI64 (m : Module) : OneUniform m .subI64 := by scalar_atom

theorem OneNoReturnCall.subI64 (m : Module) : OneNoReturnCall m .subI64 := by scalar_atom

theorem OneUniform.divUI64 (m : Module) : OneUniform m .divUI64 := by scalar_atom

theorem OneNoReturnCall.divUI64 (m : Module) : OneNoReturnCall m .divUI64 := by scalar_atom

theorem OneUniform.remUI64 (m : Module) : OneUniform m .remUI64 := by scalar_atom

theorem OneNoReturnCall.remUI64 (m : Module) : OneNoReturnCall m .remUI64 := by scalar_atom

theorem OneUniform.andI64 (m : Module) : OneUniform m .andI64 := by scalar_atom

theorem OneNoReturnCall.andI64 (m : Module) : OneNoReturnCall m .andI64 := by scalar_atom

theorem OneUniform.orI64 (m : Module) : OneUniform m .orI64 := by scalar_atom

theorem OneNoReturnCall.orI64 (m : Module) : OneNoReturnCall m .orI64 := by scalar_atom

theorem OneUniform.xorI64 (m : Module) : OneUniform m .xorI64 := by scalar_atom

theorem OneNoReturnCall.xorI64 (m : Module) : OneNoReturnCall m .xorI64 := by scalar_atom

theorem OneUniform.shlI64 (m : Module) : OneUniform m .shlI64 := by scalar_atom

theorem OneNoReturnCall.shlI64 (m : Module) : OneNoReturnCall m .shlI64 := by scalar_atom

theorem OneUniform.shrUI64 (m : Module) : OneUniform m .shrUI64 := by scalar_atom

theorem OneNoReturnCall.shrUI64 (m : Module) : OneNoReturnCall m .shrUI64 := by scalar_atom

theorem OneUniform.eqI64 (m : Module) : OneUniform m .eqI64 := by scalar_atom

theorem OneNoReturnCall.eqI64 (m : Module) : OneNoReturnCall m .eqI64 := by scalar_atom

theorem OneUniform.neI64 (m : Module) : OneUniform m .neI64 := by scalar_atom

theorem OneNoReturnCall.neI64 (m : Module) : OneNoReturnCall m .neI64 := by scalar_atom

theorem OneUniform.ltUI64 (m : Module) : OneUniform m .ltUI64 := by scalar_atom

theorem OneNoReturnCall.ltUI64 (m : Module) : OneNoReturnCall m .ltUI64 := by scalar_atom

theorem OneUniform.leUI64 (m : Module) : OneUniform m .leUI64 := by scalar_atom

theorem OneNoReturnCall.leUI64 (m : Module) : OneNoReturnCall m .leUI64 := by scalar_atom

theorem OneUniform.geUI64 (m : Module) : OneUniform m .geUI64 := by scalar_atom

theorem OneNoReturnCall.geUI64 (m : Module) : OneNoReturnCall m .geUI64 := by scalar_atom

theorem OneUniform.eqzI64 (m : Module) : OneUniform m .eqzI64 := by scalar_atom

theorem OneNoReturnCall.eqzI64 (m : Module) : OneNoReturnCall m .eqzI64 := by scalar_atom

theorem OneUniform.extendUI32 (m : Module) : OneUniform m .extendUI32 := by scalar_atom

theorem OneNoReturnCall.extendUI32 (m : Module) : OneNoReturnCall m .extendUI32 := by scalar_atom

theorem OneUniform.wrapI64 (m : Module) : OneUniform m .wrapI64 := by scalar_atom

theorem OneNoReturnCall.wrapI64 (m : Module) : OneNoReturnCall m .wrapI64 := by scalar_atom

theorem OneUniform.f64Sub (m : Module) : OneUniform m .f64Sub := by scalar_atom

theorem OneNoReturnCall.f64Sub (m : Module) : OneNoReturnCall m .f64Sub := by scalar_atom

theorem OneUniform.f64Div (m : Module) : OneUniform m .f64Div := by scalar_atom

theorem OneNoReturnCall.f64Div (m : Module) : OneNoReturnCall m .f64Div := by scalar_atom

theorem OneUniform.f64Lt (m : Module) : OneUniform m .f64Lt := by scalar_atom

theorem OneNoReturnCall.f64Lt (m : Module) : OneNoReturnCall m .f64Lt := by scalar_atom

theorem OneUniform.f64Le (m : Module) : OneUniform m .f64Le := by scalar_atom

theorem OneNoReturnCall.f64Le (m : Module) : OneNoReturnCall m .f64Le := by scalar_atom

theorem OneUniform.f64Eq (m : Module) : OneUniform m .f64Eq := by scalar_atom

theorem OneNoReturnCall.f64Eq (m : Module) : OneNoReturnCall m .f64Eq := by scalar_atom

theorem OneUniform.f64Sqrt (m : Module) : OneUniform m .f64Sqrt := by scalar_atom

theorem OneNoReturnCall.f64Sqrt (m : Module) : OneNoReturnCall m .f64Sqrt := by scalar_atom

theorem OneUniform.f64Abs (m : Module) : OneUniform m .f64Abs := by scalar_atom

theorem OneNoReturnCall.f64Abs (m : Module) : OneNoReturnCall m .f64Abs := by scalar_atom

theorem OneUniform.f64ConvertI64U (m : Module) : OneUniform m .f64ConvertI64U := by scalar_atom

theorem OneNoReturnCall.f64ConvertI64U (m : Module) : OneNoReturnCall m .f64ConvertI64U := by scalar_atom

theorem OneUniform.f64ReinterpretI64 (m : Module) : OneUniform m .f64ReinterpretI64 := by scalar_atom

theorem OneNoReturnCall.f64ReinterpretI64 (m : Module) : OneNoReturnCall m .f64ReinterpretI64 := by scalar_atom

theorem OneUniform.i64TruncSatF64U (m : Module) : OneUniform m .i64TruncSatF64U := by scalar_atom

theorem OneNoReturnCall.i64TruncSatF64U (m : Module) : OneNoReturnCall m .i64TruncSatF64U := by scalar_atom

theorem OneUniform.i64ReinterpretF64 (m : Module) : OneUniform m .i64ReinterpretF64 := by scalar_atom

theorem OneNoReturnCall.i64ReinterpretF64 (m : Module) : OneNoReturnCall m .i64ReinterpretF64 := by scalar_atom

theorem OneUniform.f32Add (m : Module) : OneUniform m .f32Add := by scalar_atom

theorem OneNoReturnCall.f32Add (m : Module) : OneNoReturnCall m .f32Add := by scalar_atom

theorem OneUniform.f32Sub (m : Module) : OneUniform m .f32Sub := by scalar_atom

theorem OneNoReturnCall.f32Sub (m : Module) : OneNoReturnCall m .f32Sub := by scalar_atom

theorem OneUniform.f32Mul (m : Module) : OneUniform m .f32Mul := by scalar_atom

theorem OneNoReturnCall.f32Mul (m : Module) : OneNoReturnCall m .f32Mul := by scalar_atom

theorem OneUniform.f32Div (m : Module) : OneUniform m .f32Div := by scalar_atom

theorem OneNoReturnCall.f32Div (m : Module) : OneNoReturnCall m .f32Div := by scalar_atom

theorem OneUniform.f32Lt (m : Module) : OneUniform m .f32Lt := by scalar_atom

theorem OneNoReturnCall.f32Lt (m : Module) : OneNoReturnCall m .f32Lt := by scalar_atom

theorem OneUniform.f32Le (m : Module) : OneUniform m .f32Le := by scalar_atom

theorem OneNoReturnCall.f32Le (m : Module) : OneNoReturnCall m .f32Le := by scalar_atom

theorem OneUniform.f32Eq (m : Module) : OneUniform m .f32Eq := by scalar_atom

theorem OneNoReturnCall.f32Eq (m : Module) : OneNoReturnCall m .f32Eq := by scalar_atom

theorem OneUniform.f32Sqrt (m : Module) : OneUniform m .f32Sqrt := by scalar_atom

theorem OneNoReturnCall.f32Sqrt (m : Module) : OneNoReturnCall m .f32Sqrt := by scalar_atom

theorem OneUniform.f32Abs (m : Module) : OneUniform m .f32Abs := by scalar_atom

theorem OneNoReturnCall.f32Abs (m : Module) : OneNoReturnCall m .f32Abs := by scalar_atom

theorem OneUniform.f32Nearest (m : Module) : OneUniform m .f32Nearest := by scalar_atom

theorem OneNoReturnCall.f32Nearest (m : Module) : OneNoReturnCall m .f32Nearest := by scalar_atom

theorem OneUniform.f32ConvertI64U (m : Module) : OneUniform m .f32ConvertI64U := by scalar_atom

theorem OneNoReturnCall.f32ConvertI64U (m : Module) : OneNoReturnCall m .f32ConvertI64U := by scalar_atom

theorem OneUniform.f32ReinterpretI32 (m : Module) : OneUniform m .f32ReinterpretI32 := by scalar_atom

theorem OneNoReturnCall.f32ReinterpretI32 (m : Module) : OneNoReturnCall m .f32ReinterpretI32 := by scalar_atom

theorem OneUniform.f32ConvertI32S (m : Module) : OneUniform m .f32ConvertI32S := by scalar_atom

theorem OneNoReturnCall.f32ConvertI32S (m : Module) : OneNoReturnCall m .f32ConvertI32S := by scalar_atom

theorem OneUniform.i64TruncSatF32U (m : Module) : OneUniform m .i64TruncSatF32U := by scalar_atom

theorem OneNoReturnCall.i64TruncSatF32U (m : Module) : OneNoReturnCall m .i64TruncSatF32U := by scalar_atom

theorem OneUniform.i32ReinterpretF32 (m : Module) : OneUniform m .i32ReinterpretF32 := by scalar_atom

theorem OneNoReturnCall.i32ReinterpretF32 (m : Module) : OneNoReturnCall m .i32ReinterpretF32 := by scalar_atom

theorem OneUniform.i32TruncSatF32S (m : Module) : OneUniform m .i32TruncSatF32S := by scalar_atom

theorem OneNoReturnCall.i32TruncSatF32S (m : Module) : OneNoReturnCall m .i32TruncSatF32S := by scalar_atom

theorem OneUniform.ret (m : Module) : OneUniform m .ret := by scalar_atom

theorem OneNoReturnCall.ret (m : Module) : OneNoReturnCall m .ret := by scalar_atom

theorem OneUniform.drop (m : Module) : OneUniform m .drop := by scalar_atom

theorem OneNoReturnCall.drop (m : Module) : OneNoReturnCall m .drop := by scalar_atom

theorem OneUniform.select (m : Module) : OneUniform m .select := by scalar_atom

theorem OneNoReturnCall.select (m : Module) : OneNoReturnCall m .select := by scalar_atom

theorem OneUniform.nop (m : Module) : OneUniform m .nop := by scalar_atom

theorem OneNoReturnCall.nop (m : Module) : OneNoReturnCall m .nop := by scalar_atom

theorem OneUniform.unreachable (m : Module) : OneUniform m .unreachable := by scalar_atom

theorem OneNoReturnCall.unreachable (m : Module) : OneNoReturnCall m .unreachable := by scalar_atom

theorem OneUniform.localTee (m : Module) (index : Nat) :
    OneUniform m (.localTee index) := by scalar_atom

theorem OneNoReturnCall.localTee (m : Module) (index : Nat) :
    OneNoReturnCall m (.localTee index) := by scalar_atom

theorem OneUniform.const (m : Module) (value : UInt32) :
    OneUniform m (.const value) := by scalar_atom

theorem OneNoReturnCall.const (m : Module) (value : UInt32) :
    OneNoReturnCall m (.const value) := by scalar_atom

theorem OneUniform.f32Const (m : Module) (value : UInt32) :
    OneUniform m (.f32Const value) := by scalar_atom

theorem OneNoReturnCall.f32Const (m : Module) (value : UInt32) :
    OneNoReturnCall m (.f32Const value) := by scalar_atom

theorem OneUniform.br (m : Module) (label : Nat) :
    OneUniform m (.br label) := by scalar_atom

theorem OneNoReturnCall.br (m : Module) (label : Nat) :
    OneNoReturnCall m (.br label) := by scalar_atom

theorem OneUniform.br_if (m : Module) (label : Nat) :
    OneUniform m (.br_if label) := by scalar_atom

theorem OneNoReturnCall.br_if (m : Module) (label : Nat) :
    OneNoReturnCall m (.br_if label) := by scalar_atom

end Wasm
