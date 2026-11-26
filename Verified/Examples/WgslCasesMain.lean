module

public import Verified.Examples.WgslCases
public import Examples.Binary32.VerifiedGpuCases

@[expose] public section

def main : IO Unit := do
  Verified.Examples.WgslCases.runCases true
  Examples.Binary32.VerifiedGpuCases.cases
