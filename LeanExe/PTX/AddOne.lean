import LeanExe.PTX.Syntax

/-!
A kernel written by hand that adds one to each word of an array.  The input buffer holds the
length `n` in word 0 and the array in words `1` to `n`; the output buffer has the same layout, and
the host writes its word 0.  Thread `g` with `g < n` stores `input[1 + g] + 1` to `output[1 + g]`.
-/

namespace LeanExe.PTX

/-- The add-one kernel. -/
def addOne : Module where
  inputs := 1
  regs32 := 3
  regs64 := 10
  preds := 1
  body := [
    .instr none (.special 0 .ctaidX),
    .instr none (.special 1 .ntidX),
    .instr none (.special 2 .tidX),
    .instr none (.widen 0 2),
    .instr none (.madWide 1 0 1 0),
    .instr none (.ldParam 2 0),
    .instr none (.cvtaGlobal 2 2),
    .instr none (.ldParam 3 1),
    .instr none (.cvtaGlobal 3 3),
    .instr none (.ld 4 2 0),
    .instr none (.setp .lt 0 1 (.reg 4)),
    .ite 0 [
      .instr none (.shift .shl 5 1 (.imm 3)),
      .instr none (.bin64 .add 6 2 (.reg 5)),
      .instr none (.ld 7 6 8),
      .instr none (.bin64 .add 8 7 (.imm 1)),
      .instr none (.bin64 .add 9 3 (.reg 5)),
      .instr none (.st 9 8 8)] []]

end LeanExe.PTX
