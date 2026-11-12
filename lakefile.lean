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

-- The co-simulation of the AArch64 model (tests/baremetal/a64-cosim.sh); not a default target.
lean_exe «a64-cosim» where
  srcDir := "tests"
  root := `TestSupport.A64.CosimMain

-- The test of the floating-point forms' meanings (tests/baremetal/a64-fpvectors.sh); not a default
-- target.
lean_exe «a64-fpvectors» where
  srcDir := "tests"
  root := `TestSupport.A64.FpVectorsMain

-- The exhaustive test of the single-precision forms (tests/baremetal/a64-fpexhaust.sh); not a
-- default target.
lean_exe «a64-fpexhaust» where
  srcDir := "tests"
  root := `TestSupport.A64.FpExhaustMain

-- The comparison of the Cortex-M7 encoder with the GNU assembler (tests/baremetal/m7-encode.sh)
-- and the co-simulation of the Cortex-M7 model (tests/baremetal/m7-cosim.sh); not default
-- targets.
lean_exe «m7-encode» where
  srcDir := "tests"
  root := `TestSupport.M7.EncodeMain

lean_exe «m7-cosim» where
  srcDir := "tests"
  root := `TestSupport.M7.CosimMain

-- The window counts of the Cortex-M7 back end's generated programs in the model; not a default
-- target.
lean_exe «m7-windows» where
  srcDir := "tests"
  root := `TestSupport.M7.WindowsMain

-- The comparison of the AArch64 encoder with the GNU assembler (tests/baremetal/a64-encode.sh);
-- not a default target.
lean_exe «a64-encode» where
  srcDir := "tests"
  root := `TestSupport.A64.EncodeMain

-- The arm64 Images of the AArch64 back end's bare-metal programs (tests/baremetal/a64-images.sh);
-- not a default target.
lean_exe «a64-programs» where
  srcDir := "tests"
  root := `TestSupport.A64.ProgramsMain

-- The arm64 Image of the AArch64 back end that reads its arguments from the UART
-- (tests/baremetal/a64-uart.sh); not a default target.
lean_exe «a64-uart» where
  srcDir := "tests"
  root := `TestSupport.A64.UartMain

-- The arm64 Image of the Oakland tabulator that reads a canonical file from the UART
-- (tests/baremetal/a64-rcv.sh); not a default target.
lean_exe «a64-rcv» where
  srcDir := "tests"
  root := `TestSupport.A64.RcvMain

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

lean_exe «verified-cases-signed» where
  root := `Verified.Examples.SignedCasesMain

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

lean_exe «verified-cases-arraytrees» where
  root := `Verified.Examples.ArrayTreesCasesMain

lean_exe «verified-cases-buffertrees» where
  root := `Verified.Examples.BufferTreesCasesMain

lean_exe «verified-cases-regex» where
  srcDir := "tests"
  root := `TestSupport.Regex.CasesMain

lean_exe «verified-cases-sha3» where
  srcDir := "tests"
  root := `TestSupport.Hashing.Sha3CasesMain

lean_exe «verified-cases-crc» where
  srcDir := "tests"
  root := `TestSupport.Hashing.CrcCasesMain

lean_exe «verified-cases-crcbitwise» where
  srcDir := "tests"
  root := `TestSupport.Hashing.CrcBitwiseCasesMain

lean_exe «verified-cases-siphash» where
  srcDir := "tests"
  root := `TestSupport.Hashing.SipHashCasesMain

lean_exe «verified-cases-xxhash64» where
  srcDir := "tests"
  root := `TestSupport.Hashing.XxHash64CasesMain

lean_exe «verified-cases-slew» where
  srcDir := "tests"
  root := `TestSupport.Slew.CasesMain

lean_exe «verified-cases-energy» where
  srcDir := "tests"
  root := `TestSupport.Energy.CasesMain

lean_exe «verified-cases-orderbook» where
  srcDir := "tests"
  root := `TestSupport.OrderBook.CasesMain

lean_exe «verified-cases-rcv» where
  srcDir := "tests"
  root := `TestSupport.Rcv.CasesMain

lean_exe «verified-cases-rcv-maine» where
  srcDir := "tests"
  root := `TestSupport.Rcv.MaineCasesMain

lean_exe «rcv-bound» where
  srcDir := "tests"
  root := `TestSupport.Rcv.BoundMain

lean_exe «rcv-maine-bound» where
  srcDir := "tests"
  root := `TestSupport.Rcv.MaineBoundMain

lean_exe «verified-cases-conjunction» where
  srcDir := "tests"
  root := `TestSupport.Conjunction.CasesMain

lean_exe «verified-cases-accuracy» where
  srcDir := "tests"
  root := `TestSupport.Conjunction.AccuracyCasesMain

lean_exe «verified-cases-passivesafety» where
  srcDir := "tests"
  root := `TestSupport.PassiveSafety.CasesMain

lean_exe «verified-cases-attitude» where
  srcDir := "tests"
  root := `TestSupport.Attitude.CasesMain

lean_exe «verified-cases-qmethod» where
  srcDir := "tests"
  root := `TestSupport.Attitude.QCasesMain

lean_exe «verified-cases-screening» where
  srcDir := "tests"
  root := `TestSupport.Screening.CasesMain

lean_exe «verified-cases-chisquare» where
  srcDir := "tests"
  root := `TestSupport.Gate.ChiSquareCasesMain

lean_exe «verified-cases-gate» where
  srcDir := "tests"
  root := `TestSupport.Gate.GateCasesMain

lean_exe «verified-cases-assignment» where
  srcDir := "tests"
  root := `TestSupport.Gate.AssignmentCasesMain

lean_exe «verified-cases-events» where
  srcDir := "tests"
  root := `TestSupport.Events.CasesMain

lean_exe «verified-cases-frames» where
  srcDir := "tests"
  root := `TestSupport.Frames.CasesMain

lean_exe «verified-cases-avoidance» where
  srcDir := "tests"
  root := `TestSupport.Avoidance.CasesMain

lean_exe «verified-cases-geolocation» where
  srcDir := "tests"
  root := `TestSupport.Geolocation.CasesMain

lean_exe «verified-cases-sgp4» where
  srcDir := "tests"
  root := `TestSupport.Sgp4.CasesMain

lean_exe «verified-cases-sgp4box» where
  srcDir := "tests"
  root := `TestSupport.Sgp4.BoxCasesMain

lean_exe «verified-cases-sgp4omm» where
  srcDir := "tests"
  root := `TestSupport.Sgp4.OmmCasesMain

lean_exe «verified-cases-orbit» where
  srcDir := "tests"
  root := `TestSupport.Orbit.CasesMain

-- The native comparison of the order book's program with its specification
-- (tests/orderbook/run.sh); not a default target.
lean_exe «orderbook-compare» where
  srcDir := "tests"
  root := `TestSupport.OrderBook.Compare

-- The order book's process on stdin and stdout, and its scripted-host tests
-- (tests/orderbook/process.sh); not default targets.
lean_exe «orderbook-native» where
  root := `Demos.OrderBook.ProcessNative
  moreLinkObjs := #[`@/runningSumRead]

lean_exe «orderbook-process» where
  srcDir := "tests"
  root := `TestSupport.OrderBook.Process

-- The ranked-choice specification on canonical ballot files (Demos/Rcv/Native.lean); not a
-- default target.
lean_exe «rcv-spec» where
  root := `Demos.Rcv.Native

-- The ranked-choice reader, printer, and export on canonical ballot files
-- (Demos/Rcv/TabulateNative.lean); not a default target.
lean_exe «rcv-tabulate» where
  root := `Demos.Rcv.TabulateNative

-- The tabulator's WASI process on stdin and stdout (Demos/Rcv/ProcessNative.lean); not a default
-- target.
lean_exe «rcv-process» where
  root := `Demos.Rcv.ProcessNative
  moreLinkObjs := #[`@/runningSumRead]

lean_exe «rcv-rounds» where
  root := `Demos.Rcv.RoundsNative

lean_exe «rcv-stability» where
  root := `Demos.Rcv.StabilityNative

lean_exe «rcv-properties» where
  root := `Demos.Rcv.PropertiesNative

-- The Maine specification on canonical ballot files and the native tests of its theorems'
-- statements (Demos/Rcv/Maine/Native.lean); not a default target.
lean_exe «rcv-maine» where
  root := `Demos.Rcv.Maine.Native

-- The native tests of the statements of the Maine count's T12 to T15
-- (Demos/Rcv/Maine/PropertiesNative.lean); not a default target.
lean_exe «rcv-maine-properties» where
  root := `Demos.Rcv.Maine.PropertiesNative

-- The Maine module's WASI process on stdin and stdout (Demos/Rcv/Maine/ProcessNative.lean); not a
-- default target.
lean_exe «rcv-maine-process» where
  root := `Demos.Rcv.Maine.ProcessNative
  moreLinkObjs := #[`@/runningSumRead]

-- The differential test of the Lean copy of Clight against CompCert's reference interpreter
-- (tests/native/clight.sh); not a default target.
lean_exe «clight-diff» where
  srcDir := "tests"
  root := `TestSupport.Native.ClightDiff

-- The replay of the BMS bridge's logs against the specification (Demos/Bms/Host.md); not a
-- default target.
lean_exe «bms-replay» where
  srcDir := "tests"
  root := `TestSupport.Bms.Replay

-- The C text, host programs, and Talos's results for the translator's end-to-end test
-- (tests/native/run.sh); not a default target.
lean_exe «native-emit» where
  srcDir := "tests"
  root := `TestSupport.Native.Emit

-- The bare-metal programs, their C text with `main`, and their expected output
-- (tests/baremetal/programs.sh); not a default target.
lean_exe «native-bare» where
  srcDir := "tests"
  root := `TestSupport.Bare.Emit

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
