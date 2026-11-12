import Verified.Wasi.PureTransport
import LeanExe.Encoding.Domain
import LeanExe.Wasi.Calls

/-!
Relocation of the pure module's code into a WASI module.  A WASI module imports `fd_read`,
`fd_write`, and `proc_exit` and then the flat calls `calls` that its program uses, so its defined
functions begin at `3 + calls.length`, and pure function `index` becomes function
`3 + calls.length + index`.  Type indices move by the three stream imports only, since the types
of the calls' imports follow every other type.  `instruction`, `program`, `function`, and `Layout` are the
forms of a module without calls.
-/

namespace Verified.Wasi.Relocation

open Wasm LeanExe.Wasi

mutual
  def instructionWith (calls : List Call) : Instruction → Instruction
    | .call index => .call (3 + calls.length + index)
    | .block ps rs body pts rts => .block ps rs (programWith calls body) pts rts
    | .loop ps rs body pts rts => .loop ps rs (programWith calls body) pts rts
    | .iff ps rs yes no pts rts => .iff ps rs (programWith calls yes) (programWith calls no) pts rts
    | other => other

  def programWith (calls : List Call) : Program → Program
    | [] => []
    | head :: tail => instructionWith calls head :: programWith calls tail
end

def instruction : Instruction → Instruction := instructionWith []

def program : Program → Program := programWith []

def functionWith (calls : List Call) (source : Function) : Function :=
  { source with body := programWith calls source.body, typeIdx := source.typeIdx.map (3 + ·) }

def function : Function → Function := functionWith []

theorem function_shape_with (calls : List Call) (source : Function) :
    PureTransport.FunctionShape source (functionWith calls source) := ⟨rfl, rfl, rfl⟩

theorem function_shape (source : Function) :
    PureTransport.FunctionShape source (function source) := function_shape_with [] source

@[simp] theorem programWith_nil (calls : List Call) : programWith calls [] = [] := by
  simp only [programWith]

@[simp] theorem programWith_cons (calls : List Call) (head : Instruction) (tail : Program) :
    programWith calls (head :: tail) = instructionWith calls head :: programWith calls tail := by
  simp only [programWith]

@[simp] theorem programWith_append (calls : List Call) (first second : Program) :
    programWith calls (first ++ second) = programWith calls first ++ programWith calls second := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, programWith_cons, ih]

@[simp] theorem programWith_length (calls : List Call) (source : Program) :
    (programWith calls source).length = source.length := by
  induction source with
  | nil => rfl
  | cons head tail ih => simp only [programWith_cons, List.length_cons, ih]

@[simp] theorem program_append (first second : Program) :
    program (first ++ second) = program first ++ program second :=
  programWith_append [] first second

@[simp] theorem program_length (source : Program) : (program source).length = source.length :=
  programWith_length [] source

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

/-- The relation of the pure module `source` to a WASI module `target` that imports `calls`. -/
structure LayoutWith (calls : List Call) (source target : Module) : Prop where
  sourceImports : source.imports = []
  targetImports : target.imports.length = 3 + calls.length
  functions : ∀ {index : Nat} {f : Function}, source.funcs[index]? = some f →
    target.funcs[index]? = some (functionWith calls f)
  memory64 : target.memIs64 = source.memIs64
  memoryCap : target.memoryCap = source.memoryCap

structure Layout (source target : Module) : Prop where
  sourceImports : source.imports = []
  targetImports : target.imports.length = 3
  functions : ∀ {index : Nat} {f : Function}, source.funcs[index]? = some f →
    target.funcs[index]? = some (function f)
  memory64 : target.memIs64 = source.memIs64
  memoryCap : target.memoryCap = source.memoryCap

theorem Layout.toWith {source target : Module} (layout : Layout source target) :
    LayoutWith [] source target :=
  ⟨layout.sourceImports, layout.targetImports, layout.functions, layout.memory64,
    layout.memoryCap⟩

theorem LayoutWith.toLayout {source target : Module} (layout : LayoutWith [] source target) :
    Layout source target :=
  ⟨layout.sourceImports, layout.targetImports, layout.functions, layout.memory64,
    layout.memoryCap⟩

end Verified.Wasi.Relocation

/-- Closes the goals that `apply` leaves when an existing theorem takes its proof from the form
for modules with imported calls at the empty list: each goal is a hypothesis or the conversion of
one.  Later files add conversions with further `macro_rules`. -/
syntax "layout_convert" : tactic

macro_rules
  | `(tactic| layout_convert) => `(tactic| assumption)

macro_rules
  | `(tactic| layout_convert) => `(tactic| (apply Verified.Wasi.Relocation.Layout.toWith; assumption))

/-- Turns a goal about a form without calls into the general form's at the empty list when the
two are separate structures.  Later files add conversions with further `macro_rules`. -/
syntax "layout_back" : tactic

macro_rules
  | `(tactic| layout_back) => `(tactic| skip)

macro_rules
  | `(tactic| layout_back) => `(tactic| apply Verified.Wasi.Relocation.LayoutWith.toLayout)

/-- Proves an existing theorem from the general form `name` at the empty list of calls. -/
syntax "layout_instance " ident : tactic

macro_rules
  | `(tactic| layout_instance $name) =>
    `(tactic| (layout_back; apply $name (calls := []) <;> layout_convert))
