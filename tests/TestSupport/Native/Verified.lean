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
* `build MODULE CONSTANT NAME DIR` is the native build of a module: it writes the files of
  `emit`, runs `clightgen` on `DIR/NAME.c`, compares its Clight with the translation as `check`
  does, and only when they match compiles the same `DIR/NAME.c` with `ccomp -fno-common -c` to
  `DIR/NAME.o`.  `-fno-common` makes `lx_mem` and `lx_pun` definitions rather than common symbols,
  so that `ccomp` addresses them directly rather than through the global offset table.
  A mismatch, or a failure of either tool, stops it with a nonzero status before `ccomp` runs or
  after it fails.  The environment variables `CLIGHTGEN` and `CCOMP` name the tools, `clightgen`
  and `ccomp` by default, which must come from one CompCert 3.18 tree.

The option `--aligned`, before MODULE, makes `emit`, `check`, and `build` use the translation with
`alignedAccess`, whose `load64` and `store64` omit the test of alignment.  It is correct only for
functions whose theorems state that their 64-bit accesses are aligned, so `build --aligned`
compiles a module only when its theorems cover that translation (`alignedGaps`).  The constant
must be `p.module` of a `verified_compile` program `p` compiled with
`verified_compile.alignedNative`: `p.translationAligned_eq` states the translation, and a theorem
`p.f.nativeAligned`, of `NativeAlignedImpl` or `NativeTablesAlignedImpl`, covers each exported
function of the translation apart from the runtime's `alloc` and `release`, which
`alloc_nativeA` and `release_nativeA` cover.  For any other module, and for a program with byte
literals, it prints each missing theorem and exits with status 4 before it writes a file.  `emit
--aligned` and `check --aligned` write and compare the text without this check.
-/

open Lean LeanExe.Native

unsafe def loadEnv (moduleName constName : Name) : IO (Environment × Wasm.Module) := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := moduleName, importAll := false, isExported := true, isMeta := false }] {}
  return (env, ← IO.ofExcept <| env.evalConst Wasm.Module {} constName)

unsafe def loadModule (moduleName constName : Name) : IO Wasm.Module :=
  return (← loadEnv moduleName constName).2

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

def translation (m : Wasm.Module) (name : String) (aligned : Bool) : IO Translation := do
  if let some v := violation m then
    throw <| IO.userError s!"{name}: outside the subset: {v}"
  match translate nativeCap m aligned with
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
  else if n.endsWith "_f" then "float" else "unsigned long long"

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

/-- Writes the files of `emit` for the module `m`, and returns its translation, or `none` for a
module outside the subset or one that does not translate. -/
def emitModule (m : Wasm.Module) (name dir : String) (aligned : Bool) :
    IO (Option Translation) := do
  if let some v := violation m then
    IO.println s!"{name}: outside the subset: {v}"
    return none
  let some t := translate nativeCap m aligned
    | IO.println s!"{name}: does not translate"
      return none
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
  return some t

unsafe def emit (moduleName constName : Name) (name dir : String) (aligned : Bool) :
    IO UInt32 := do
  let m ← loadModule moduleName constName
  match ← emitModule m name dir aligned with
  | none => return 3
  | some _ => return 0

/-- Compares the translation `t` with the Clight that `clightgen` wrote as `DIR/NAME.v`. -/
def checkTranslation (t : Translation) (name dir : String) : IO UInt32 := do
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

unsafe def check (moduleName constName : Name) (name dir : String) (aligned : Bool) :
    IO UInt32 := do
  let m ← loadModule moduleName constName
  checkTranslation (← translation m name aligned) name dir

/-- Runs `cmd` with `args` in `cwd`, and fails with its standard error unless it exits with 0. -/
def runTool (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO Unit := do
  let out ← IO.Process.output { cmd, args, cwd }
  if out.exitCode != 0 then
    throw <| IO.userError s!"{cmd} exited with status {out.exitCode}:\n{out.stdout}{out.stderr}"

/-- The number that `e` denotes, a raw literal or an `OfNat.ofNat` of one. -/
partial def natValue? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natValue? (e.getArg! 1) else none

/-- The body of `e` under its leading `∀` binders. -/
def forallBody : Expr → Expr
  | .forallE _ _ b _ => forallBody b
  | .mdata _ b => forallBody b
  | e => e

/-- Whether `type` is `translate nativeCap module true = some translation`. -/
def isAlignedEq (module translation : Name) (type : Expr) : Bool :=
  match type.consumeMData.eq? with
  | some (_, lhs, rhs) =>
      lhs.isAppOfArity ``translate 3 && (lhs.getArg! 0).isConstOf ``nativeCap &&
        (lhs.getArg! 1).isConstOf module && (lhs.getArg! 2).isConstOf ``Bool.true &&
        rhs.isAppOfArity ``Option.some 2 && (rhs.getArg! 1).isConstOf translation
  | none => false

/-- The index of the function whose theorem has the type `type`, when `type` is
`∀ A X, NativeAlignedImpl h A X nativeCap translation` or the table form, for a theorem `h` about
`module`. -/
def alignedIndex? (module translation : Name) (type : Expr) : Option Nat := do
  let e := forallBody type
  let args := e.getAppArgs
  let (k, mod, cap, tr) ←
    if e.isAppOfArity `LeanExe.Native.NativeAlignedImpl 15 then
      some (args[6]!, args[5]!, args[13]!, args[14]!)
    else if e.isAppOfArity `Verified.NativeTablesAlignedImpl 16 then
      some (args[6]!, args[5]!, args[14]!, args[15]!)
    else none
  guard (mod.isConstOf module && cap.isConstOf ``nativeCap && tr.isConstOf translation)
  natValue? k

/-- What the theorems of `env` lack to cover the translation `t` of the module `m`, the constant
`constName`, without the test of alignment: empty when `constName` is `p.module` of a
`verified_compile` program `p` without byte literals, `p.translationAligned_eq` states
`translate nativeCap p.module true = some p.translationAligned`, and every exported function of
`t` has a theorem `p.f.nativeAligned` about `p.translationAligned`.  The exports `alloc` and
`release`, functions 0 and 1, need none when `p.module` is a `compileWith`, since
`compileWith_runtime` gives the premises of `alloc_nativeA` and `release_nativeA`.
`release_nativeA`, as `release_native`, covers the release of an array.  A program with byte
literals states `ImplementsStatic` theorems and has no aligned ones. -/
def alignedGaps (env : Environment) (constName : Name) (m : Wasm.Module) (t : Translation) :
    List String := Id.run do
  let p := constName.getPrefix
  unless constName == p ++ `module do
    return [s!"{constName} is not the module p.module of a verified_compile program p"]
  let translation := p ++ `translationAligned
  let (statics, covered) := env.constants.fold (init := (#[], ({} : Std.HashMap Nat Name)))
    fun (statics, covered) n ci =>
      match n with
      | .str (.str q _) "implements" =>
          if q == p && (forallBody ci.type).isAppOf `Verified.ImplementsStatic then
            (statics.push n, covered)
          else (statics, covered)
      | .str (.str q _) "nativeAligned" =>
          if q == p then
            match alignedIndex? constName translation ci.type with
            | some k => (statics, covered.insert k n)
            | none => (statics, covered)
          else (statics, covered)
      | _ => (statics, covered)
  if let some n := statics[0]? then
    return [s!"the program has byte literals ({n} is an ImplementsStatic theorem), and no \
      aligned theorem covers a program with byte literals"]
  let eqName := p ++ `translationAligned_eq
  match env.find? eqName with
  | none =>
      return [s!"{eqName} is missing: the program was not compiled with \
        verified_compile.alignedNative"]
  | some ci =>
      unless isAlignedEq constName translation ci.type do
        return [s!"{eqName} does not state translate nativeCap {constName} true = \
          some {translation}"]
  let runtime := match env.find? constName with
    | some (.defnInfo d) => d.value.getAppFn.isConstOf `Verified.compileWith
    | _ => false
  let mut gaps : List String := []
  for e in m.exports do
    let isRuntime := runtime &&
      ((e.funcIdx == 0 && e.name == "alloc") || (e.funcIdx == 1 && e.name == "release"))
    unless !t.funcs.contains e.funcIdx || covered.contains e.funcIdx || isRuntime do
      gaps := gaps ++ [s!"no theorem {p ++ Name.mkSimple e.name ++ `nativeAligned} covers the \
        export {e.name}, function {e.funcIdx}"]
  return gaps

unsafe def build (moduleName constName : Name) (name dir : String) (aligned : Bool) :
    IO UInt32 := do
  let (env, m) ← loadEnv moduleName constName
  if aligned && (violation m).isNone then
    if let some t := translate nativeCap m true then
      let gaps := alignedGaps env constName m t
      unless gaps.isEmpty do
        for g in gaps do
          IO.eprintln s!"{name}: refusing the translation without the alignment test: {g}"
        return 4
  let some t ← emitModule m name dir aligned | return 3
  runTool ((← IO.getEnv "CLIGHTGEN").getD "clightgen") #[s!"{name}.c"] (some dir)
  let status ← checkTranslation t name dir
  if status != 0 then return status
  runTool ((← IO.getEnv "CCOMP").getD "ccomp")
    #["-fno-common", "-c", "-o", s!"{dir}/{name}.o", s!"{dir}/{name}.c"]
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["survey", moduleText, constText, name] => survey moduleText.toName constText.toName name
  | ["emit", moduleText, constText, name, dir] =>
      emit moduleText.toName constText.toName name dir false
  | ["emit", "--aligned", moduleText, constText, name, dir] =>
      emit moduleText.toName constText.toName name dir true
  | ["check", moduleText, constText, name, dir] =>
      check moduleText.toName constText.toName name dir false
  | ["check", "--aligned", moduleText, constText, name, dir] =>
      check moduleText.toName constText.toName name dir true
  | ["build", moduleText, constText, name, dir] =>
      build moduleText.toName constText.toName name dir false
  | ["build", "--aligned", moduleText, constText, name, dir] =>
      build moduleText.toName constText.toName name dir true
  | _ => throw (IO.userError
      "usage: native-verified survey|emit|check|build [--aligned] MODULE CONSTANT NAME [DIR]")
