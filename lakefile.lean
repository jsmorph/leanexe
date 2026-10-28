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

-- The case generators of tests/verified/run.sh, compiled so that their runs fit the driver's time
-- limit; not default targets.
lean_exe «verified-cases» where
  root := `Verified.Examples.Cases

lean_exe «verified-cases-treecopy» where
  root := `Verified.Examples.TreeCopyCasesMain

lean_exe «verified-cases-treecore» where
  root := `Verified.Examples.TreeCasesMain

lean_exe «verified-cases-lists» where
  root := `Verified.Examples.ListsCasesMain

lean_exe «verified-cases-composition» where
  root := `Verified.Examples.CompositionCasesMain

lean_exe «verified-cases-scalarcomposition» where
  root := `Verified.Examples.ScalarCompositionCasesMain

lean_exe «verified-cases-relocation» where
  root := `Verified.Examples.RelocationCasesMain

lean_exe «verified-cases-wgsl» where
  root := `Verified.Examples.WgslWasmCasesMain

lean_exe «verified-cases-gpt32» where
  root := `Demos.Gpt32.VerifiedWasmCasesMain

lean_exe «verified-cases-listrecursion» where
  root := `Verified.Examples.ListRecursionCasesMain

lean_exe «verified-cases-listloops» where
  root := `Verified.Examples.ListLoopsCasesMain

lean_exe «verified-cases-listtail» where
  root := `Verified.Examples.ListTailCasesMain

lean_exe «verified-cases-recursivetypes» where
  root := `Verified.Examples.RecursiveTypesCasesMain

lean_exe «verified-cases-sha256» where
  srcDir := "tests"
  root := `TestSupport.Hashing.Sha256CasesMain

lean_exe «verified-cases-sha512» where
  srcDir := "tests"
  root := `TestSupport.Hashing.Sha512CasesMain

lean_exe «verified-cases-hmac» where
  srcDir := "tests"
  root := `TestSupport.Hashing.HmacCasesMain

lean_exe «verified-cases-taggedtypes» where
  root := `Verified.Examples.TaggedTypesCasesMain

lean_exe «verified-cases-heapsums» where
  root := `Verified.Examples.HeapSumsCasesMain

lean_exe «verified-cases-typedtrees» where
  root := `Verified.Examples.TypedTreesCasesMain

lean_exe «verified-cases-regex» where
  srcDir := "tests"
  root := `TestSupport.Regex.CasesMain

lean_exe «verified-cases-sha3» where
  srcDir := "tests"
  root := `TestSupport.Hashing.Sha3CasesMain

lean_exe «verified-cases-crc» where
  srcDir := "tests"
  root := `TestSupport.Hashing.CrcCasesMain

lean_exe «verified-cases-siphash» where
  srcDir := "tests"
  root := `TestSupport.Hashing.SipHashCasesMain

lean_exe «verified-cases-xxhash64» where
  srcDir := "tests"
  root := `TestSupport.Hashing.XxHash64CasesMain

lean_exe «verified-cases-slew» where
  srcDir := "tests"
  root := `TestSupport.Slew.CasesMain

-- The differential test of the Lean copy of Clight against CompCert's reference interpreter
-- (tests/native/clight.sh); not a default target.
lean_exe «clight-diff» where
  srcDir := "tests"
  root := `TestSupport.Native.ClightDiff

-- The C text, host programs, and Talos's results for the translator's end-to-end test
-- (tests/native/run.sh); not a default target.
lean_exe «native-emit» where
  srcDir := "tests"
  root := `TestSupport.Native.Emit

-- The translation of the tests/verified corpus to C (tests/native/verified.sh); not a default
-- target.
lean_exe «native-verified» where
  srcDir := "tests"
  root := `TestSupport.Native.Verified
  supportInterpreter := true

-- The module cases that tests/native/verified.sh runs natively, compiled as the case generators
-- of tests/verified/run.sh are; not a default target.
lean_exe «native-module-cases» where
  srcDir := "tests"
  root := `TestSupport.Native.ModuleCases
