import Lake

open Lake DSL

package leanexe where
  version := v!"0.1.0"

require Verifier from ".lake/packages/CodeLib/verifier"
-- Lake loads requirements in reverse order, so CodeLib must follow Verifier.
require CodeLib from git "https://github.com/jsmorph/talos"
  @ "87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47" / "codelib"

@[default_target] lean_lib LeanExe
@[default_target] lean_lib Examples
lean_lib Library
@[default_target] lean_lib Demos

lean_lib TestSupport where
  srcDir := "tests"

lean_lib Verified

lean_exe «gpt32-lines» where
  root := `Demos.Gpt32.Lines

lean_exe «euler-native» where
  root := `Demos.Euler.Native

target runningSumRead pkg : System.FilePath := do
  let source ← inputTextFile (pkg.dir / "Demos" / "RunningSum" / "read.c")
  buildO (pkg.buildDir / "native" / "running-sum-read.o") source
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"] "cc" getLeanTrace

lean_exe «running-sum-native» where
  root := `Demos.RunningSum.Native
  moreLinkObjs := #[`@/runningSumRead]

lean_exe «running-sumfp-native» where
  root := `Demos.RunningSumFp.Native
  moreLinkObjs := #[`@/runningSumRead]

-- The checks of the hashing transcriptions and programs on their vectors
-- (tests/TestSupport/Hashing); not default targets.
lean_exe «sha3-vectors» where
  srcDir := "tests"
  root := `TestSupport.Hashing.Sha3Vectors

lean_exe «crc-vectors» where
  srcDir := "tests"
  root := `TestSupport.Hashing.CrcVectors

lean_exe «siphash-vectors» where
  srcDir := "tests"
  root := `TestSupport.Hashing.SipHashVectors

lean_exe «xxhash64-vectors» where
  srcDir := "tests"
  root := `TestSupport.Hashing.XxHash64Vectors
