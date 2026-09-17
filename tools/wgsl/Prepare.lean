import LeanExe.WGSL.Manifest

open LeanExe.WGSL

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def readUTF8 (file : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile file
  if bytes.size > 65536 then throw (IO.userError "verification input exceeds 64 KiB")
  let some source := String.fromUTF8? bytes | throw (IO.userError "invalid UTF-8 input")
  return source

/-- Produce an untrusted proof draft from the actual files. All reductions in
the draft are rechecked by the kernel in a separate invocation. -/
def main (args : List String) : IO Unit := do
  let [shaderPath, manifestPath, outputPath] := args
    | throw (IO.userError "usage: Prepare.lean KERNEL MANIFEST FRESH_PROOF_FILE")
  let source ← readUTF8 shaderPath
  let manifestSource ← readUTF8 manifestPath
  let metadata ← unwrap (decodeManifest manifestSource)
  let kernel ← unwrap (checkGemm source)
  let tokens ← unwrap (tokenize source)
  let tag ← if metadata.profile.id == restrictedProfileId then pure "separate"
    else if metadata.profile.id == fusionProfileId then pure "fusion"
    else throw (IO.userError "unsupported profile")
  let selected := if tag == "separate" then ProfileTag.separate else ProfileTag.fusion
  unless decide (metadata.Matches kernel.ast.config selected) do
    throw (IO.userError "manifest does not match parsed WGSL and supported profile")
  let text := String.intercalate "\n" [
    "import Project.WGSL.Package",
    "namespace CheckedWGSLPackage",
    "open LeanExe.WGSL Project.WGSL.Binary32",
    "def source : String := " ++ reprStr source,
    "def manifestSource : String := " ++ reprStr manifestSource,
    "def metadata : Manifest :=\n  " ++ (reprStr metadata).replace "\n" "\n  ",
    "def config : GemmConfig :=\n  " ++ (reprStr kernel.ast.config).replace "\n" "\n  ",
    "def ast : GemmSyntax := ⟨config, .guardedRowMajor⟩",
    "def tokenHints : List String := " ++ reprStr tokens,
    "theorem lexed : tokenize source = .ok tokenHints :=",
    "  except_ok_of_toOption _ _ (by decide +kernel)",
    "theorem tokensParsed : parseGemmTokens tokenHints = .ok ast :=",
    "  except_ok_of_toOption _ _ (by decide +kernel)",
    "theorem parsed : parseGemm source = .ok ast :=",
    "  parseGemm_of_tokens source tokenHints ast lexed tokensParsed",
    "def checked : CheckedGemm := ⟨ast, by decide +kernel⟩",
    "def package : Package source metadata where",
    "  tag := ." ++ tag,
    "  kernel := checked",
    "  parsed := parsed",
    "  matched := by decide +kernel",
    "def artifact := package.artifact",
    "def numerical := @Package.numerical source metadata package",
    "def numericalWide := @Package.numerical_wide source metadata package",
    "def exact := @Package.exact source metadata package",
    "#print axioms package",
    "#print axioms artifact",
    "#print axioms numerical",
    "#print axioms numericalWide",
    "#print axioms exact",
    "end CheckedWGSLPackage",
    "def main (args : List String) : IO Unit := do",
    "  let [shaderPath, manifestPath] := args",
    "    | throw (IO.userError \"expected shader and manifest paths\")",
    "  unless (← IO.FS.readBinFile shaderPath) == CheckedWGSLPackage.source.toUTF8 do",
    "    throw (IO.userError \"shader differs from kernel-checked source\")",
    "  unless (← IO.FS.readBinFile manifestPath) == CheckedWGSLPackage.manifestSource.toUTF8 do",
    "    throw (IO.userError \"manifest differs from checked file\")",
    "  let actual ← match LeanExe.WGSL.decodeManifest CheckedWGSLPackage.manifestSource with",
    "    | .ok value => pure value",
    "    | .error message => throw (IO.userError message)",
    "  unless actual == CheckedWGSLPackage.metadata do",
    "    throw (IO.userError \"JSON metadata differs from checked metadata\")",
    "  IO.println (\"WGSL_PACKAGE_BINDING \" ++ (Lean.toJson CheckedWGSLPackage.metadata).compress)",
    ""
  ]
  let output : System.FilePath := outputPath
  if ← output.pathExists then throw (IO.userError "proof output already exists")
  IO.FS.writeFile output text
  IO.println s!"Prepared independent WGSL proof draft: {output}"
