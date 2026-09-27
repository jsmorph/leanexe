import LeanExe.Extract.ScalarExprCore
run_elab do
  let info ← Lean.getConstInfo `LeanExe.Extract.Core.extractScalarExprWith.induct
  Lean.Meta.forallTelescope info.type fun parameters _ => do
    for parameter in parameters do
      let declaration ← parameter.fvarId!.getDecl
      if declaration.userName ∈ [`case49, `case50, `case51, `case58, `case59, `case60, `case61] then
        Lean.logInfo m!"{declaration.userName}: {declaration.type}"
