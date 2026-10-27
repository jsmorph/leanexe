import Verified.Wasi.PureTransport
import LeanExe.Encoding.Domain

namespace Verified.Wasi.Relocation

open Wasm

mutual
  def instruction : Instruction → Instruction
    | .call index => .call (3 + index)
    | .block ps rs body pts rts => .block ps rs (program body) pts rts
    | .loop ps rs body pts rts => .loop ps rs (program body) pts rts
    | .iff ps rs yes no pts rts => .iff ps rs (program yes) (program no) pts rts
    | other => other

  def program : Program → Program
    | [] => []
    | head :: tail => instruction head :: program tail
end

def function (source : Function) : Function :=
  { source with body := program source.body, typeIdx := source.typeIdx.map (3 + ·) }

theorem function_shape (source : Function) :
    PureTransport.FunctionShape source (function source) := ⟨rfl, rfl, rfl⟩

@[simp] theorem program_append (first second : Program) :
    program (first ++ second) = program first ++ program second := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, program, ih]

@[simp] theorem program_length (source : Program) : (program source).length = source.length := by
  induction source with
  | nil => rfl
  | cons head tail ih => simp only [program, List.length_cons, ih]

mutual
  def instructionClosed (bound : Nat) : Instruction → Bool
    | .call index => decide (index < bound)
    | .block _ _ body _ _ | .loop _ _ body _ _ => programClosed bound body
    | .iff _ _ yes no _ _ => programClosed bound yes && programClosed bound no
    | _ => true

  def programClosed (bound : Nat) : Program → Bool
    | [] => true
    | head :: tail => instructionClosed bound head && programClosed bound tail
end

def Profile (m : Module) : Prop :=
  ∀ f ∈ m.funcs, Encoding.ProgramForm f.body ∧ programClosed m.funcs.length f.body = true

structure Layout (source target : Module) : Prop where
  sourceImports : source.imports = []
  targetImports : target.imports.length = 3
  functions : ∀ {index : Nat} {f : Function}, source.funcs[index]? = some f →
    target.funcs[index]? = some (function f)
  memory64 : target.memIs64 = source.memIs64
  memoryCap : target.memoryCap = source.memoryCap

end Verified.Wasi.Relocation
