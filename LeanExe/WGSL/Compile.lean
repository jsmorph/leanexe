import LeanExe.WGSL.BodyEmit
import LeanExe.WGSL.BodyExecution
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
Fuel bounds expression traversal; Lean's heartbeat limit also applies to
definitional reduction inside `whnf`. -/
private partial def index (ctx : Context) (e : Expr) (fuel : Nat := 256) : MetaM Index := do
  if fuel == 0 then unsupported "index expression (normalization limit)" e
  let e := e.consumeMData
  if e == ctx.row then return .row
  if e == ctx.col then return .col
  if let some n := slot ctx.indices e then return .local n
  if let .lit (.natVal n) := e then return .lit n
  let args := e.getAppArgs
  if (e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6) &&
      args[0]! == mkConst ``Nat && args[1]! == mkConst ``Nat && args[2]! == mkConst ``Nat then
    let a ← index ctx args[4]! (fuel - 1)
    let b ← index ctx args[5]! (fuel - 1)
    return if e.isAppOf ``HAdd.hAdd then .add a b else .mul a b
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
  -- Expose one helper body before weak-head normalization can evaluate a
  -- literal-count Source.fold into hundreds of nested arithmetic operations.
  if let some reduced ← unfoldDefinition? e then
    if reduced != e then return ← expression ctx reduced (fuel - 1)
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

private def compileDefinition (entry : TSyntax `ident) (rows cols a b : TSyntax `num)
    (directory : TSyntax `str) (existing : Option System.FilePath := none) : CommandElabM Unit :=
  withScope (fun scope => {scope with opts := maxRecDepth.set (Lean.Elab.async.set scope.opts false) 16384}) do
  let output : System.FilePath := directory.getString
  if ← output.pathExists then throwError "WGSL: output directory already exists: {output}"
  let name ← liftTermElabM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo entry
  let shape : Shape := ⟨rows.getNat, cols.getNat, a.getNat, b.getNat⟩
  let extracted ← liftTermElabM <| extract name
  match validate shape extracted with
  | .error message => throwError "WGSL: {message}"
  | .ok () => pure ()
  let shader ← match existing with
    | none => pure (emit shape extracted)
    | some path => do
        let bytes ← liftIO (IO.FS.readBinFile path)
        if bytes.size > 65536 then throwError "WGSL: shader exceeds 64 KiB check limit"
        let some text := String.fromUTF8? bytes | throwError "WGSL: shader is not valid UTF-8"
        pure text
  if shader.toUTF8.size > 65536 then throwError "WGSL: shader exceeds 64 KiB check limit"
  let parsed ← match Source.parse shader with
    | .ok parsed => pure parsed
    | .error message => throwError "WGSL: emitted shader failed independent parsing: {message}"
  unless parsed.rows == shape.rows && parsed.cols == shape.cols do
    throwError "WGSL: emitted shader changed output dimensions"
  let body := parsed.body
  match validate shape body with
  | .error message => throwError "WGSL: parsed shader failed validation: {message}"
  | .ok () => pure ()
  let codeText := s!"({parsed.code.lean} : LeanExe.WGSL.Statement.Code)"
  let codeSyntax ← match Parser.runParserCategory (← getEnv) `term codeText with
    | .ok parsed => pure parsed
    | .error message => throwError "WGSL internal expression serialization error: {message}"
  let bodyName := mkIdent (name ++ `wgslBody)
  let codeName := mkIdent (name ++ `wgslCode)
  let shapeName := mkIdent (name ++ `wgslShape)
  let validName := mkIdent (name ++ `wgslCodeValid)
  let shapeValidName := mkIdent (name ++ `wgslShapeValid)
  let executionName := mkIdent (name ++ `wgslExecutionCorrect)
  let proofName := mkIdent (name ++ `wgslSourceCorrect)
  let parseName := mkIdent (name ++ `wgslShaderParsed)
  let tokensName := mkIdent (name ++ `wgslTokens)
  let lexedName := mkIdent (name ++ `wgslLexed)
  let tokensParsedName := mkIdent (name ++ `wgslTokensParsed)
  let ts ← match tokenize shader with
    | .ok ts => pure ts
    | .error message => throwError "WGSL: {message}"
  let tokensSyntax ← match Parser.runParserCategory (← getEnv) `term (reprStr ts) with
    | .ok parsed => pure parsed
    | .error message => throwError "WGSL: {message}"
  let tokensTerm : TSyntax `term := ⟨tokensSyntax⟩
  let codeTerm : TSyntax `term := ⟨codeSyntax⟩
  elabCommand (← `(def $codeName : Statement.Code := $codeTerm))
  elabCommand (← `(def $shapeName : Source.Shape := ⟨$rows, $cols, $a, $b⟩))
  elabCommand (← `(def $bodyName : Source.Term := Statement.Code.term $codeName))
  elabCommand (← `(theorem $proofName : $entry = Source.Term.kernel $bodyName := by
    funext ar a b row col
    dsimp only [$bodyName:ident, $codeName:ident, Source.Term.kernel, Statement.Code.term,
      Statement.Prim.term, Source.Term.eval, Source.Index.eval]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    try rfl))
  if (← get).messages.hasErrors then throwError "WGSL: source equality did not pass Lean checking"
  let shaderLiteral := Syntax.mkStrLit shader
  elabCommand (← `(def $tokensName : List String := $tokensTerm))
  elabCommand (← `(theorem $lexedName : tokenize $shaderLiteral = Except.ok $tokensName :=
    Source.ok_of_toOption _ _ (by decide +kernel)))
  elabCommand (← `(theorem $tokensParsedName : Source.parseTokens $tokensName =
    Except.ok (Source.Parsed.mk $rows $cols $codeName) :=
    Source.ok_of_toOption _ _ (by decide +kernel)))
  elabCommand (← `(theorem $parseName : Source.parse $shaderLiteral =
    Except.ok (Source.Parsed.mk $rows $cols $codeName) :=
    Source.parse_of_tokens _ _ _ $lexedName $tokensParsedName))
  elabCommand (← `(theorem $validName : Statement.Code.Valid $shapeName [] 0 $codeName := by decide +kernel))
  elabCommand (← `(theorem $shapeValidName : Statement.ShapeValid $shapeName := by decide +kernel))
  elabCommand (← `(theorem $executionName : Statement.Implements $shaderLiteral $shapeName $entry :=
    Statement.shader_implements _ _ _ _ $parseName $shapeValidName $validName $proofName))
  if (← get).messages.hasErrors then throwError "WGSL: execution proof did not pass Lean checking"
  for declaration in [proofName.getId, parseName.getId, executionName.getId] do
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "WGSL: proof {declaration} depends on forbidden axiom {axiomName}"
  liftIO <| IO.FS.createDirAll output
  liftIO <| IO.FS.writeFile (output / "kernel.wgsl") shader
  liftIO <| IO.FS.writeFile (output / "manifest.json") <| (Lean.Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)), ("kind", toJson "lean-body-wgsl"),
    ("sourceDeclaration", toJson name.toString), ("entryPoint", toJson "lean_kernel"),
    ("shape", toJson shape), ("workgroupSize", toJson ([8,8,1] : List Nat)),
    ("sourceEqualityChecked", toJson true), ("shaderParseChecked", toJson true),
    ("statementExecutionChecked", toJson true),
    ("proofScope", toJson "parsed statement execution terminates without local, load, store or loop-budget errors and equals the Lean definition for every invocation and input under the same explicit scalar arithmetic"),
    ("executionSemantics", toJson "LeanExe.WGSL.Statement.runShader"),
    ("universalRuntimeConformanceEstablished", toJson false)]).pretty
  liftIO <| IO.FS.writeFile (output / "source-equality.lean.txt")
    (String.intercalate "\n" [
      "set_option maxRecDepth 16384",
      s!"def {codeName.getId} : LeanExe.WGSL.Statement.Code := {parsed.code.lean}",
      s!"def {shapeName.getId} : LeanExe.WGSL.Source.Shape := ⟨{shape.rows}, {shape.cols}, {shape.elementsA}, {shape.elementsB}⟩",
      s!"def {bodyName.getId} : LeanExe.WGSL.Source.Term := {codeName.getId}.term",
      s!"theorem {proofName.getId} : {name} = LeanExe.WGSL.Source.Term.kernel {bodyName.getId} := by\n  funext ar a b row col\n  dsimp only [{bodyName.getId}, {codeName.getId}, LeanExe.WGSL.Source.Term.kernel, LeanExe.WGSL.Statement.Code.term, LeanExe.WGSL.Statement.Prim.term, LeanExe.WGSL.Source.Term.eval, LeanExe.WGSL.Source.Index.eval]\n  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]\n  try rfl",
      s!"def {tokensName.getId} : List String := {reprStr ts}",
      s!"theorem {lexedName.getId} : LeanExe.WGSL.tokenize {reprStr shader} = Except.ok {tokensName.getId} := LeanExe.WGSL.Source.ok_of_toOption _ _ (by decide +kernel)",
      s!"theorem {tokensParsedName.getId} : LeanExe.WGSL.Source.parseTokens {tokensName.getId} = Except.ok (LeanExe.WGSL.Source.Parsed.mk {shape.rows} {shape.cols} {codeName.getId}) := LeanExe.WGSL.Source.ok_of_toOption _ _ (by decide +kernel)",
      s!"theorem {parseName.getId} : LeanExe.WGSL.Source.parse {reprStr shader} = Except.ok (LeanExe.WGSL.Source.Parsed.mk {shape.rows} {shape.cols} {codeName.getId}) := LeanExe.WGSL.Source.parse_of_tokens _ _ _ {lexedName.getId} {tokensParsedName.getId}",
      s!"theorem {validName.getId} : LeanExe.WGSL.Statement.Code.Valid {shapeName.getId} [] 0 {codeName.getId} := by decide +kernel",
      s!"theorem {shapeValidName.getId} : LeanExe.WGSL.Statement.ShapeValid {shapeName.getId} := by decide +kernel",
      s!"theorem {executionName.getId} : LeanExe.WGSL.Statement.Implements {reprStr shader} {shapeName.getId} {name} := LeanExe.WGSL.Statement.shader_implements _ _ _ _ {parseName.getId} {shapeValidName.getId} {validName.getId} {proofName.getId}", ""])
  logInfo m!"WGSL: compiled body of {name}; shader parse, source equality and statement execution checked; wrote {output}"

@[command_elab compileWGSL] def elabCompileWGSL : CommandElab := fun stx => do
  let `(command| #compile_wgsl $entry:ident $rows:num $cols:num $a:num $b:num $directory:str) := stx
    | throwUnsupportedSyntax
  compileDefinition entry rows cols a b directory

/-- Check an existing shader against a source definition using the same
parser and kernel proof gate. Used also for adversarial artifact tests. -/
syntax (name := checkWGSL) "#check_wgsl " ident num num num num str str : command

@[command_elab checkWGSL] def elabCheckWGSL : CommandElab := fun stx => do
  let `(command| #check_wgsl $entry:ident $rows:num $cols:num $a:num $b:num $shader:str $directory:str) := stx
    | throwUnsupportedSyntax
  compileDefinition entry rows cols a b directory (some shader.getString)

end LeanExe.WGSL.Source
