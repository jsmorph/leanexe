import LeanExe.WGSL.BodyEmit
import Lean

namespace LeanExe.WGSL.Source
open Lean Meta Elab Command

initialize wgslAttribute : TagAttribute ←
  registerTagAttribute `wgsl "Definition supported by the Lean-body WGSL compiler"

private structure Context where
  arithmetic : Expr
  a : Expr
  b : Expr
  row : Expr
  col : Expr
  indices : List Expr := []
  words : List Expr := []

private def slot (xs : List Expr) (e : Expr) : Option Nat :=
  xs.idxOf? e

private def unsupported (kind : String) (e : Expr) : MetaM α :=
  throwError "WGSL: unsupported {kind}: {e}"

/-- Unfold transparent helper definitions, beta redexes and typeclass syntax.
Fuel prevents recursive helpers from being silently accepted or hanging. -/
private partial def index (ctx : Context) (e : Expr) (fuel : Nat := 256) : MetaM Index := do
  if fuel == 0 then unsupported "index expression (normalization limit)" e
  let e := e.consumeMData
  if e == ctx.row then return .row
  if e == ctx.col then return .col
  if let some n := slot ctx.indices e then return .local n
  if let .lit (.natVal n) := e then return .lit n
  let args := e.getAppArgs
  if e.isAppOfArity ``Nat.add 2 then
    return .add (← index ctx args[0]! (fuel - 1)) (← index ctx args[1]! (fuel - 1))
  if e.isAppOfArity ``Nat.mul 2 then
    return .mul (← index ctx args[0]! (fuel - 1)) (← index ctx args[1]! (fuel - 1))
  let reduced ← whnf e
  if reduced != e then index ctx reduced (fuel - 1) else unsupported "index expression" e

private partial def expression (ctx : Context) (e : Expr) (fuel : Nat := 512) : MetaM Source.Term := do
  if fuel == 0 then unsupported "word expression (normalization limit)" e
  let e := e.consumeMData
  if let some n := slot ctx.words e then return .local n
  if let .letE name type value body _ := e then
    if ← isDefEq type (mkConst ``UInt32) then
      let value ← expression ctx value (fuel - 1)
      return ← withLocalDeclD name type fun fvar => do
        let body ← expression {ctx with words := fvar :: ctx.words} (body.instantiate1 fvar) (fuel - 1)
        pure (.letE value body)
    else if ← isDefEq type (mkConst ``Nat) then
      return ← expression ctx (body.instantiate1 value) (fuel - 1)
    else unsupported "local binding type" type
  let fn := e.getAppFn
  let args := e.getAppArgs
  if e.isAppOfArity ``OfNat.ofNat 3 && args[0]! == mkConst ``UInt32 then
    let .lit word ← index ctx args[1]! | unsupported "nonliteral word" e
    if word > 4294967295 then throwError "WGSL: word literal must fit u32"
    return .lit (UInt32.ofNat word)
  if fn == ctx.a && args.size == 1 then return .readA (← index ctx args[0]!)
  if fn == ctx.b && args.size == 1 then return .readB (← index ctx args[0]!)
  let arithmeticOp ← match fn with
    | .proj ``ScalarArithmetic n base => pure (if base == ctx.arithmetic then some n else none)
    | .const ``ScalarArithmetic.add _ => pure (if args.size == 3 && args[0]! == ctx.arithmetic then some 0 else none)
    | .const ``ScalarArithmetic.mul _ => pure (if args.size == 3 && args[0]! == ctx.arithmetic then some 1 else none)
    | _ => pure none
  if let some n := arithmeticOp then
    if args.size < 2 then unsupported "partial arithmetic application" e
    let x ← expression ctx args[args.size - 2]! (fuel - 1)
    let y ← expression ctx args[args.size - 1]! (fuel - 1)
    if n == 0 then return .add x y
    if n == 1 then return .mul x y
  if e.isAppOfArity ``Source.fold 3 then
    let count ← index ctx args[0]!
    let .lit count := count | unsupported "nonliteral fold count" args[0]!
    if count > 65535 then throwError "WGSL: fold count exceeds 65535"
    let initial ← expression ctx args[1]! (fuel - 1)
    return ← lambdaTelescope args[2]! fun locals body => do
      unless locals.size == 2 do unsupported "fold callback (expected index and accumulator)" args[2]!
      let body ← expression {ctx with indices := locals[0]! :: ctx.indices, words := locals[1]! :: ctx.words} body (fuel - 1)
      pure (.fold count initial body)
  if e.isAppOfArity ``UInt32.ofNat 1 then
    let .lit word ← index ctx args[0]! | unsupported "nonliteral word conversion" e
    if word > 4294967295 then throwError "WGSL: word literal must fit u32"
    return .lit (UInt32.ofNat word)
  let reduced ← whnf e
  if reduced != e then expression ctx reduced (fuel - 1) else unsupported "word expression" e

private def extract (name : Name) : MetaM Source.Term := do
  unless wgslAttribute.hasTag (← getEnv) name do throwError "WGSL: mark the definition with @[wgsl]"
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do throwError "WGSL: polymorphic entries are unsupported"
  unless ← isDefEq info.type (mkConst ``Kernel) do
    throwError "WGSL: entry must have type LeanExe.WGSL.Source.Kernel"
  let some body := info.value? | throwError "WGSL: entry has no definition body"
  lambdaTelescope body fun xs e => do
    unless xs.size == 5 do throwError "WGSL: expected five explicit entry parameters"
    expression {arithmetic := xs[0]!, a := xs[1]!, b := xs[2]!, row := xs[3]!, col := xs[4]!} e

/-- Compile the elaborated body, then ask Lean's kernel to check the source
equality. Output is written only after that check succeeds. -/
syntax (name := compileWGSL) "#compile_wgsl " ident num num num num str : command

@[command_elab compileWGSL] def elabCompileWGSL : CommandElab := fun stx => do
  let `(command| #compile_wgsl $entry:ident $rows:num $cols:num $a:num $b:num $directory:str) := stx
    | throwUnsupportedSyntax
  let name ← liftTermElabM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo entry
  let shape : Shape := ⟨rows.getNat, cols.getNat, a.getNat, b.getNat⟩
  let body ← liftTermElabM <| extract name
  match validate shape body with
  | .error message => throwError "WGSL: {message}"
  | .ok () => pure ()
  let bodyText := s!"({body.lean} : LeanExe.WGSL.Source.Term)"
  let bodySyntax ← match Parser.runParserCategory (← getEnv) `term bodyText with
    | .ok parsed => pure parsed
    | .error message => throwError "WGSL internal expression serialization error: {message}"
  let bodyName := mkIdent (name ++ `wgslBody)
  let proofName := mkIdent (name ++ `wgslSourceCorrect)
  let bodyTerm : TSyntax `term := ⟨bodySyntax⟩
  elabCommand (← `(def $bodyName : Source.Term := $bodyTerm))
  elabCommand (← `(theorem $proofName : $entry = Source.Term.kernel $bodyName := by rfl))
  if (← get).messages.hasErrors then throwError "WGSL: source equality did not pass Lean checking"
  let output : System.FilePath := directory.getString
  if ← output.pathExists then throwError "WGSL: output directory already exists: {output}"
  liftIO <| IO.FS.createDirAll output
  liftIO <| IO.FS.writeFile (output / "kernel.wgsl") (emit shape body)
  liftIO <| IO.FS.writeFile (output / "manifest.json") <| (Lean.Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("kind", toJson "lean-body-wgsl"),
    ("sourceDeclaration", toJson name.toString), ("entryPoint", toJson "lean_kernel"),
    ("shape", toJson shape), ("workgroupSize", toJson ([8,8,1] : List Nat)),
    ("sourceEqualityChecked", toJson true), ("shaderSemanticsProved", toJson false)]).pretty
  liftIO <| IO.FS.writeFile (output / "source-equality.lean.txt")
    s!"def {bodyName.getId} : LeanExe.WGSL.Source.Term := {body.lean}\ntheorem {proofName.getId} : {name} = LeanExe.WGSL.Source.Term.kernel {bodyName.getId} := by rfl\n"
  logInfo m!"WGSL: compiled body of {name}; source equality checked; wrote {output}"

end LeanExe.WGSL.Source
