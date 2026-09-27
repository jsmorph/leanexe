import LeanExe.Extract.ScalarRangeExit
run_elab do
  let info ← Lean.getConstInfo `LeanExe.Extract.Core.extractScalarRangeExitWith.induct
  Lean.Meta.forallTelescope info.type fun parameters _ => do
    for parameter in parameters do
      let declaration ← parameter.fvarId!.getDecl
      if declaration.userName ∈ [`case13, `case25] then
        Lean.logInfo m!"{declaration.userName}: {declaration.type}"
