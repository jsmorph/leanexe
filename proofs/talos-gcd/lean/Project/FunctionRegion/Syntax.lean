import Interpreter.Wasm.Spec.Defs

/-!
# Closed function-region renaming

Generated modules may contain the same closed helper-function region at
different indices.  These definitions rename direct calls while restricting
the instruction forms that may observe a module.
-/

namespace Project.FunctionRegion

open Wasm

mutual
  def renameInstruction (rename : Nat → Nat) : Instruction → Instruction
    | .block params results body =>
        .block params results (renameProgram rename body)
    | .loop params results body =>
        .loop params results (renameProgram rename body)
    | .iff params results thenBody elseBody =>
        .iff params results (renameProgram rename thenBody)
          (renameProgram rename elseBody)
    | .call id => .call (rename id)
    | inst => inst

  def renameProgram (rename : Nat → Nat) : Program → Program
    | [] => []
    | inst :: rest =>
        renameInstruction rename inst :: renameProgram rename rest
end

def renameFunction (rename : Nat → Nat) (f : Function) : Function :=
  { f with body := renameProgram rename f.body }

mutual
  inductive PortableInstruction (domain : Nat → Prop) : Instruction → Prop
    | localGet (i : Nat) : PortableInstruction domain (.localGet i)
    | localSet (i : Nat) : PortableInstruction domain (.localSet i)
    | const32 (value : UInt32) : PortableInstruction domain (.const value)
    | const64 (value : UInt64) : PortableInstruction domain (.constI64 value)
    | addI64 : PortableInstruction domain .addI64
    | subI64 : PortableInstruction domain .subI64
    | mulI64 : PortableInstruction domain .mulI64
    | eqI64 : PortableInstruction domain .eqI64
    | eqz : PortableInstruction domain .eqz
    | leUI64 : PortableInstruction domain .leUI64
    | ltUI64 : PortableInstruction domain .ltUI64
    | wrapI64 : PortableInstruction domain .wrapI64
    | load64 (offset : UInt32) : PortableInstruction domain (.load64 offset)
    | unreachable : PortableInstruction domain .unreachable
    | br (label : Nat) : PortableInstruction domain (.br label)
    | brIf (label : Nat) : PortableInstruction domain (.br_if label)
    | block (params results : Nat) (body : Program) :
        PortableProgram domain body →
        PortableInstruction domain (.block params results body)
    | loop (params results : Nat) (body : Program) :
        PortableProgram domain body →
        PortableInstruction domain (.loop params results body)
    | branch (params results : Nat) (thenBody elseBody : Program) :
        PortableProgram domain thenBody → PortableProgram domain elseBody →
        PortableInstruction domain (.iff params results thenBody elseBody)
    | call (id : Nat) : domain id → PortableInstruction domain (.call id)

  inductive PortableProgram (domain : Nat → Prop) : Program → Prop
    | nil : PortableProgram domain []
    | cons (inst : Instruction) (rest : Program) :
        PortableInstruction domain inst → PortableProgram domain rest →
        PortableProgram domain (inst :: rest)
end

macro "prove_portable" : tactic => `(tactic|
  repeat' (first
    | apply PortableProgram.nil
    | apply PortableProgram.cons
    | apply PortableInstruction.localGet
    | apply PortableInstruction.localSet
    | apply PortableInstruction.const32
    | apply PortableInstruction.const64
    | apply PortableInstruction.addI64
    | apply PortableInstruction.subI64
    | apply PortableInstruction.mulI64
    | apply PortableInstruction.eqI64
    | apply PortableInstruction.eqz
    | apply PortableInstruction.leUI64
    | apply PortableInstruction.ltUI64
    | apply PortableInstruction.wrapI64
    | apply PortableInstruction.load64
    | apply PortableInstruction.unreachable
    | apply PortableInstruction.br
    | apply PortableInstruction.brIf
    | apply PortableInstruction.block
    | apply PortableInstruction.loop
    | apply PortableInstruction.branch
    | apply PortableInstruction.call))

structure Shift (source target : Module) (rename : Nat → Nat)
    (domain : Nat → Prop) : Prop where
  sourceImports : source.imports = []
  targetImports : target.imports = []
  functions : ∀ id, domain id →
    ∃ f,
      source.funcs[id]? = some f ∧
      target.funcs[rename id]? = some (renameFunction rename f) ∧
      PortableProgram domain f.body

end Project.FunctionRegion
