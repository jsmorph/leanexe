import LeanExe.Extract.ScalarStepSupported
run_elab do
  let info ← Lean.getConstInfo `LeanExe.Extract.Core.extractScalarStepWith.induct
  Lean.Meta.forallTelescope info.type fun parameters _ => do
    for parameter in parameters do
      let declaration ← parameter.fvarId!.getDecl
      if declaration.userName ∈ [`case24, `case45] then
        Lean.logInfo m!"{declaration.userName}: {declaration.type}"
