import Interpreter.Wasm.Syntax

/-!
The modules that the translator to C accepts.  `InSubset m` holds when `m` has the shape of the
modules that `compileWith` produces and every function body uses only the 73 instruction forms
of the design's table, with blocks, loops, and conditionals that take no parameters and declare
at most one numeric result.  The check is syntactic.  The translator's static analysis of the
operand stack, which also checks local, global, and function indices, comes after it.

`violation m` names the first part of `m` outside the subset, and `InSubset m` is
`violation m = none`, which the kernel decides.  `verified_compile` states it as `p.inSubset`.
-/

namespace LeanExe.Native

open Wasm

/-- The value types of locals, parameters, results, and block results. -/
def numeric : ValueType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | _ => false

/-- No parameters, and at most one result whose type is declared. -/
def blockTypeOk (paramArity resultArity : Nat) (paramTypes resultTypes : List ValueType) :
    Bool :=
  paramArity == 0 && paramTypes.isEmpty && resultArity ≤ 1 &&
    resultTypes.length == resultArity && resultTypes.all numeric

mutual
  def instrOk (instr : Instruction) : Bool :=
    match instr with
    | .constI64 _ | .addI64 | .subI64 | .mulI64 | .divUI64 | .remUI64 | .andI64 | .orI64
    | .xorI64 | .shlI64 | .shrUI64 | .eqI64 | .neI64 | .ltUI64 | .leUI64 | .geUI64
    | .eqzI64 => true
    | .const _ | .eq | .eqz | .and | .wrapI64 | .extendUI32 => true
    | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _ => true
    | .load64 _ | .store64 _ | .load8U _ | .store8 _ | .memorySize | .memoryGrow => true
    | .br _ | .br_if _ | .call _ | .ret | .unreachable => true
    | .f64Const _ | .f64Add | .f64Sub | .f64Mul | .f64Div | .f64Eq | .f64Lt | .f64Le | .f64Sqrt
    | .f64Abs | .f64ConvertI64U | .f64ReinterpretI64 | .i64ReinterpretF64
    | .i64TruncSatF64U => true
    | .f32Const _ | .f32Add | .f32Sub | .f32Mul | .f32Div | .f32Eq | .f32Lt | .f32Le | .f32Sqrt
    | .f32Abs | .f32Nearest | .f32ConvertI64U | .f32ConvertI32S | .f32ReinterpretI32
    | .i32ReinterpretF32 | .i64TruncSatF32U | .i32TruncSatF32S => true
    | .block pa ra body pts rts => blockTypeOk pa ra pts rts && programOk body
    | .loop pa ra body pts rts => blockTypeOk pa ra pts rts && programOk body
    | .iff pa ra thn els pts rts => blockTypeOk pa ra pts rts && programOk thn && programOk els
    | _ => false

  def programOk (code : Program) : Bool :=
    match code with
    | [] => true
    | head :: tail => instrOk head && programOk tail
end

def functionViolation (k : Nat) (f : Function) : Option String :=
  if !(f.params.all numeric) then some s!"function {k}: a parameter type outside the subset"
  else if !(f.locals.all numeric) then some s!"function {k}: a local type outside the subset"
  else if !(f.results.all numeric) then some s!"function {k}: a result type outside the subset"
  else if !(programOk f.body) then some s!"function {k}: an instruction outside the subset"
  else none

/-- Every global holds an `i64` value and has no initializer to run. -/
def globalOk (g : GlobalDecl) : Bool :=
  (match g.init with
    | .i64 _ => true
    | _ => false) && g.initExpr.isEmpty

/-- An active segment of memory 0 at a literal offset, inside the initial pages.  Talos's
`initialStore` skips a segment that does not fit, and the check excludes that case. -/
def segmentOk (pages : Nat) (segment : DataSegment) : Bool :=
  match segment.offset with
  | some offset =>
      segment.memIdx == 0 && segment.offsetExpr.isEmpty &&
        offset.toNat + segment.bytes.length ≤ pages * 65536
  | none => false

def memoryViolation : Option MemDecl → Option String
  | none => some "the module has no memory"
  | some decl =>
      if decl.is64 then some "the memory is 64-bit"
      else if !(decl.data.all (segmentOk decl.pagesMin.toNat)) then
        some "a data segment is passive, not literal, or outside the initial pages"
      else none

def shapeViolation (m : Module) : Option String :=
  if !m.imports.isEmpty then some "the module imports functions"
  else if !m.extraMemories.isEmpty then some "the module has additional memories"
  else if m.dataWithoutMemory then some "the module has data without memory"
  else if m.startFunc.isSome then some "the module has a start function"
  else if !m.tables.isEmpty then some "the module has tables"
  else if !m.elements.isEmpty then some "the module has element segments"
  else if !m.tags.isEmpty then some "the module has exception tags"
  else if !(m.importedGlobals.isEmpty && m.importedTables.isEmpty &&
      m.importedMemories.isEmpty && m.importedTags.isEmpty) then
    some "the module imports globals, tables, memories, or tags"
  else if !(m.tableExports.isEmpty && m.tagExports.isEmpty) then
    some "the module exports tables or tags"
  else if !(m.globals.all globalOk) then some "a global is not a constant i64"
  else if !(m.exports.all (·.funcIdx < m.funcs.length)) then
    some "an export names a function that does not exist"
  else none

/-- The first part of `m` outside the subset, if any. -/
def violation (m : Module) : Option String :=
  match shapeViolation m with
  | some reason => some reason
  | none =>
      match memoryViolation m.memory with
      | some reason => some reason
      | none => (m.funcs.zipIdx.findSome? fun (f, k) => functionViolation k f)

def InSubset (m : Module) : Prop :=
  violation m = none

instance (m : Module) : Decidable (InSubset m) :=
  inferInstanceAs (Decidable (violation m = none))

end LeanExe.Native
