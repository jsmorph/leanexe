import Lean
import LeanExe.Native.ClightCheck

/-!
The executable `native-verified`, which translates the modules of the `tests/verified` corpus
to C with `lx_mem` of `nativeCap` pages, the translation that `verified_compile` states
its theorems about (`tests/native/verified.sh`).  It loads a module's constant from the compiled
Lean module that defines it, as `tools/Emit.lean` does.

* `survey MODULE CONSTANT NAME` prints which functions of the module translate and why the
  others do not.
* `emit MODULE CONSTANT NAME DIR` writes the C text of the translation as `DIR/NAME.c`, the glue
  of `tools/native-host.h` as `DIR/NAME_glue.c`, and the names of the exported functions that
  the translation contains, one per line, as `DIR/NAME.exports`, and the C names of the functions
  that take the call depth, one per line, as `DIR/NAME.depth`; for a module outside the subset or
  one that does not translate, it writes nothing and exits with status 3.  Compiled with
  `LX_STACK_MARK`, the glue measures the stack of each call with `lx_stack_mark` and
  `lx_stack_used` of `tools/baremetal/start.S` and reports it with `lx_stack_report`.
* `check MODULE CONSTANT NAME DIR` compares the translation with the Clight that `clightgen`
  wrote for `DIR/NAME.c` as `DIR/NAME.v`.
-/

open Lean LeanExe.Native

unsafe def loadModule (moduleName constName : Name) : IO Wasm.Module := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := moduleName, importAll := false, isExported := true, isMeta := false }] {}
  IO.ofExcept <| env.evalConst Wasm.Module {} constName

def exportName (m : Wasm.Module) (k : Nat) : String :=
  match m.exports.find? (·.funcIdx == k) with
  | some e => e.name
  | none => s!"#{k}"

/-- Why function `k` is not in the translation. -/
def reason (cap : Nat) (m : Wasm.Module) (k : Nat) : String :=
  match m.funcs[k]? with
  | none => "missing"
  | some f =>
      match signatureOf f with
      | none =>
          if f.results.length ≥ 2 then s!"{f.results.length} results, a binary32 one among them"
          else "a parameter or result type"
      | some _ =>
          match (fdefsOf cap m)[k]?.join with
          | none =>
              if f.results.length ≥ 2 then s!"an instruction form, with {f.results.length} results"
              else "an instruction form"
          | some _ => "a call of an omitted function"

def translation (m : Wasm.Module) (name : String) : IO Translation := do
  if let some v := violation m then
    throw <| IO.userError s!"{name}: outside the subset: {v}"
  match translate nativeCap m with
  | none => throw <| IO.userError s!"{name}: does not translate"
  | some t => pure t

unsafe def survey (moduleName constName : Name) (name : String) : IO UInt32 := do
  let m ← loadModule moduleName constName
  if let some v := violation m then
    IO.println s!"{name}: outside the subset: {v}"
    return 0
  match translate nativeCap m with
  | none =>
      IO.println s!"{name}: does not translate"
      return 0
  | some t =>
      let omitted := (List.range m.funcs.length).filter fun k => !t.funcs.contains k
      IO.println s!"{name}: {t.funcs.length} of {m.funcs.length} functions"
      for k in omitted do
        IO.println s!"  {exportName m k}: {reason nativeCap m k}"
      return 0

def LeanExe.Native.VT.cname : VT → String
  | .i32 => "unsigned int" | .i64 => "unsigned long long" | .f32 => "float" | .f64 => "double"

/-- The argument `a[j]` as a value of type `t`. -/
def argText (j : Nat) : VT → String
  | .i32 => s!"(unsigned int) a[{j}]"
  | .i64 => s!"a[{j}]"
  | .f32 => s!"lx_to_f32(a[{j}])"
  | .f64 => s!"lx_to_f64(a[{j}])"

/-- The bits of the value `e` of type `t`. -/
def resultText (e : String) : VT → String
  | .i32 => s!"(unsigned long long) {e}"
  | .i64 => e
  | .f32 => s!"lx_of_f32({e})"
  | .f64 => s!"lx_of_f64({e})"

/-- The C type of the result global `n`, from its suffix. -/
def resultCType (n : String) : String :=
  if n.endsWith "_i" then "unsigned int" else if n.endsWith "_d" then "double"
  else "unsigned long long"

/-- The lines of the entries of a C array, or `empty` for none, since C has no empty array. -/
def table (entries : List String) (empty : String) : String :=
  ",\n".intercalate (if entries.isEmpty then [empty] else entries) ++ "\n"

/-- The glue of `tools/native-host.h` for the exported functions of `m` that `t` contains. -/
def glue (t : Translation) (m : Wasm.Module) : Except String String := do
  let exports := m.exports.filter fun e => t.funcs.contains e.funcIdx
  let mut protos := ""
  let mut calls := ""
  let mut entries := #[]
  for e in exports do
    let some f := m.funcs[e.funcIdx]? | throw s!"function {e.funcIdx}"
    let some (ps, rs) := signatureOf f | throw s!"the signature of function {e.funcIdx}"
    let fname := functionName m e.funcIdx
    let ret := match rs with | [r] => r.cname | _ => "void"
    let params := if ps.isEmpty then "void" else ", ".intercalate (ps.map VT.cname)
    protos := protos ++ s!"{ret} {fname}({params});\n"
    let decls := String.join ((ps.zipIdx).map fun (p, j) =>
      s!"  {p.cname} x{j} = {argText j p};\n")
    let args := ", ".intercalate ((ps.zipIdx).map fun (_, j) => s!"x{j}")
    let call := s!"{fname}({args})"
    let (callStmt, results) := match rs with
      | [] => (s!"  {call};\n", "")
      | [r] => (s!"  {r.cname} v = {call};\n", s!"  r[0] = {resultText "v" r};\n")
      | rs => (s!"  {call};\n", String.join ((rs.zipIdx).map fun (r, i) =>
          s!"  r[{i}] = {resultText (t.gname (resId i r)) r};\n"))
    let cname := s!"lx_call_{e.funcIdx}"
    calls := calls ++
      s!"static void {cname}(const unsigned long long *a, unsigned long long *r) \{\n" ++
      (if ps.isEmpty then "  (void) a;\n" else "") ++
      (if rs.isEmpty then "  (void) r;\n" else "") ++ decls ++ "  LX_MARK();\n" ++ callStmt ++
      s!"  LX_REPORT(\"{fname}\");\n" ++ results ++ "}\n"
    let ptext := String.join (ps.map VT.letter)
    let rtext := String.join (rs.map VT.letter)
    entries := entries.push s!"  \{\"{e.name}\", \"{ptext}\", \"{rtext}\", {cname}}"
  let resGlobals := t.names.filterMap fun (_, n) =>
    if n.startsWith "lx_r" then
      some s!"extern {resultCType n} {n};\n"
    else none
  let globals := m.globalExports.filter fun (_, i) => i < m.globals.length
  let gdecls := String.join (globals.map fun (_, i) => s!"extern unsigned long long lx_g{i};\n")
  let gentries := globals.map fun (n, i) => s!"  \{\"{n}\", &lx_g{i}}"
  pure <|
    "/* Generated by native-verified. */\n#include \"native-host.h\"\n" ++
    "#ifdef LX_STACK_MARK\nvoid lx_stack_mark(void);\nunsigned long long lx_stack_used(void);\n" ++
    "void lx_stack_report(const char *name, unsigned long long used);\n" ++
    "#define LX_MARK() lx_stack_mark()\n" ++
    "#define LX_REPORT(f) lx_stack_report(f, lx_stack_used())\n" ++
    "#else\n#define LX_MARK()\n#define LX_REPORT(f)\n#endif\n" ++
    String.join resGlobals ++ gdecls ++ protos ++
    "static float lx_to_f32(unsigned long long b) {\n" ++
    "  union { unsigned int u; float f; } x;\n  x.u = (unsigned int) b;\n  return x.f;\n}\n" ++
    "static double lx_to_f64(unsigned long long b) {\n" ++
    "  union { unsigned long long u; double d; } x;\n  x.u = b;\n  return x.d;\n}\n" ++
    "static unsigned long long lx_of_f32(float f) {\n" ++
    "  union { unsigned int u; float f; } x;\n  x.f = f;\n  return x.u;\n}\n" ++
    "static unsigned long long lx_of_f64(double d) {\n" ++
    "  union { unsigned long long u; double d; } x;\n  x.d = d;\n  return x.u;\n}\n" ++
    calls ++
    s!"const lx_export lx_exports[] = \{\n{table entries.toList "  {0, 0, 0, 0}"}};\n" ++
    s!"const int lx_export_count = {entries.size};\n" ++
    s!"const lx_global_export lx_global_exports[] = \{\n{table gentries "  {0, 0}"}};\n" ++
    s!"const int lx_global_export_count = {gentries.length};\n"

unsafe def emit (moduleName constName : Name) (name dir : String) : IO UInt32 := do
  let m ← loadModule moduleName constName
  if let some v := violation m then
    IO.println s!"{name}: outside the subset: {v}"
    return 3
  let some t := translate nativeCap m
    | IO.println s!"{name}: does not translate"
      return 3
  let text ← IO.ofExcept <| t.text.mapError fun e => IO.userError s!"{name}: {e}"
  let glueText ← IO.ofExcept <| (glue t m).mapError fun e => IO.userError s!"{name}: {e}"
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/{name}.c" text
  IO.FS.writeFile s!"{dir}/{name}_glue.c" glueText
  let exports := m.exports.filter fun e => t.funcs.contains e.funcIdx
  IO.FS.writeFile s!"{dir}/{name}.exports" (String.join (exports.map (·.name ++ "\n")))
  IO.FS.writeFile s!"{dir}/{name}.depth" (String.join ((t.depthNames m).map (· ++ "\n")))
  IO.println s!"{name}: {t.funcs.length} of {m.funcs.length} functions, \
    {exports.length} of {m.exports.length} exports"
  return 0

unsafe def check (moduleName constName : Name) (name dir : String) : IO UInt32 := do
  let m ← loadModule moduleName constName
  let t ← translation m name
  let text ← IO.FS.readFile s!"{dir}/{name}.v"
  match ClightCheck.check t text with
  | .error e =>
      IO.eprintln s!"{name}: {e}"
      return 1
  | .ok [] =>
      IO.println s!"{name}: the clightgen program matches the translation"
      return 0
  | .ok errors =>
      for e in errors do IO.eprintln s!"{name}: {e}"
      return 1

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["survey", moduleText, constText, name] => survey moduleText.toName constText.toName name
  | ["emit", moduleText, constText, name, dir] =>
      emit moduleText.toName constText.toName name dir
  | ["check", moduleText, constText, name, dir] =>
      check moduleText.toName constText.toName name dir
  | _ => throw (IO.userError "usage: native-verified survey|emit|check MODULE CONSTANT NAME [DIR]")
