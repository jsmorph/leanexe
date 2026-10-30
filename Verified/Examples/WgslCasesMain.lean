import Verified.Examples.WgslCases
import Examples.Binary32.VerifiedGpuCases

def main : IO Unit := do
  Verified.Examples.WgslCases.runCases true
  Examples.Binary32.VerifiedGpuCases.cases
