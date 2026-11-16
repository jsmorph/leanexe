import Lean

/-!
The kernel's cost of the declarations of a built module.
`stats MODULE` prints, for each constant that MODULE declares, its name, its kind, and the numbers
of distinct objects (`Expr.numObjs`) of its type and its value.
`check MODULE NAME...` adds each named theorem or definition again under a fresh name, in the
environment that imports MODULE, and prints the kernel's time for it in seconds and the 25
constants that the kernel unfolded most often, with their counts; `all` names every theorem and
definition of MODULE.
`diff MODULE NAME...` prints, for each named constant, the first subterms at which the type that
the elaborator infers for its value and its stated type differ, unfolding the side of greater
reducibility height first as the kernel does, which locates the work of a slow definitional check.
Usage: `tools/leanrun --timeout 1h lake env lean --run tools/DeclStats.lean stats|check|diff MODULE [NAME...]`
-/

open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "ax" | .opaqueInfo _ => "opq"
  | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

def recheck (env : Environment) (c : ConstantInfo) :
    IO (Option (Float × Array (Name × Nat))) := do
  let env := Kernel.enableDiag env true
  let fresh := c.name ++ `recheck
  let decl? : Option Declaration := match c with
    | .thmInfo v => some (.thmDecl { v with name := fresh })
    | .defnInfo v => some (.defnDecl { v with name := fresh, all := [fresh] })
    | _ => none
  let some decl := decl? | return none
  let t0 ← IO.monoNanosNow
  let env' ← match env.addDeclCore 0 100000 decl none with
    | .ok env' => pure env'
    | .error e => throw <| IO.userError s!"{c.name}: {← (e.toMessageData {}).toString}"
  let t1 ← IO.monoNanosNow
  let counts := (Kernel.getDiagnostics env').unfoldCounter.toList.toArray.qsort (·.2 > ·.2)
  return some ((t1 - t0).toFloat / 1e9, counts)

/-- The pairs of subterms at which `a` and `b` first differ, after beta reduction, walking
applications with the same head and arity, binders, and projections.  At applications of
different constants, it unfolds the one of greater height, as the kernel does, up to `fuel` times. -/
partial def diffs (fuel : Nat) (a b : Expr) : MetaM (List (Expr × Expr)) := do
  let a := a.headBeta
  let b := b.headBeta
  if a == b then return []
  let height (e : Expr) : MetaM Nat := do
    let .const n _ := e.getAppFn | return 0
    match (← getEnv).find? n with
    | some (.defnInfo v) => return match v.hints with | .regular h => h.toNat | _ => 0
    | _ => return 0
  match a, b with
  | .app .., .app .. | .app .., .const .. | .const .., .app .. | .const .., .const .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let xa := a.getAppArgs
    let xb := b.getAppArgs
    if fa == fb && xa.size == xb.size then
      return (← (xa.zip xb).toList.mapM fun (x, y) => diffs fuel x y).flatten
    if fuel > 0 && fa.isConst && fb.isConst then
      let ha ← height a
      let hb ← height b
      if ha ≥ hb then
        if let some a' ← Meta.unfoldDefinition? a then return ← diffs (fuel - 1) a' b
      if let some b' ← Meta.unfoldDefinition? b then return ← diffs (fuel - 1) a b'
    return [(a, b)]
  | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _ => return (← diffs fuel t₁ t₂) ++ (← diffs fuel b₁ b₂)
  | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _ => return (← diffs fuel t₁ t₂) ++ (← diffs fuel b₁ b₂)
  | .mdata _ x, _ => diffs fuel x b
  | _, .mdata _ y => diffs fuel a y
  | _, _ => return [(a, b)]

def showExpr (e : Expr) : MetaM String := do
  let s := toString (← Meta.ppExpr e)
  return if s.length > 400 then (s.take 400).toString ++ " [cut]" else s

unsafe def main (args : List String) : IO Unit := do
  let mode :: m :: names := args | throw <| IO.userError "usage: stats|check|diff MODULE [NAME...]"
  initSearchPath (← findSysroot)
  let m := m.toName
  let env ← importModules #[{ module := m }] {}
  let some idx := env.getModuleIdx? m | throw <| IO.userError s!"no module {m}"
  let own := env.header.moduleData[idx.toNat]!.constNames
  match mode with
  | "stats" =>
    for n in own do
      let some c := env.find? n | throw <| IO.userError s!"no constant {n}"
      let v ← match c.value? (allowOpaque := true) with
        | some e => e.numObjs
        | none => pure 0
      IO.println s!"{n} {kindOf c} {← c.type.numObjs} {v}"
  | "check" =>
    let targets := if names == ["all"] then own.toList else names.map String.toName
    for n in targets do
      let some c := env.find? n | throw <| IO.userError s!"no constant {n}"
      if let some (s, counts) ← recheck env c then
        IO.println s!"{n} {kindOf c} {s}"
        for (d, k) in counts.extract 0 25 do
          IO.println s!"  {k} {d}"
        (← IO.getStdout).flush
  | "diff" =>
    for n in names do
      let some c := env.find? n.toName | throw <| IO.userError s!"no constant {n}"
      let some v := c.value? (allowOpaque := true) | continue
      let act : MetaM Unit := do
        let ty ← instantiateMVars (← Meta.inferType v)
        let ds ← diffs 4 (← Core.betaReduce ty) (← Core.betaReduce c.type)
        IO.println s!"{n}: {ds.length} differences"
        for (x, y) in ds.take 12 do
          IO.println s!"  proof: {← showExpr x}"
          IO.println s!"  claim: {← showExpr y}"
      let ctx : Core.Context := { fileName := "", fileMap := default, maxHeartbeats := 0 }
      discard <| (act.run' {}).toIO ctx { env }
  | _ => throw <| IO.userError s!"unknown mode {mode}"
