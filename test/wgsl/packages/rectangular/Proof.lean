import Project.WGSL.Package
namespace CheckedWGSLPackage
open LeanExe.WGSL Project.WGSL.Binary32
def source : String := "// leanexe WGSL GEMM v1; row-major f32 storage buffers\nconst M: u32 = 3u;\nconst N: u32 = 5u;\nconst K: u32 = 2u;\n\n@group(0) @binding(0) var<storage, read> a: array<f32>;\n@group(0) @binding(1) var<storage, read> b: array<f32>;\n@group(0) @binding(2) var<storage, read_write> c: array<f32>;\n\n@compute @workgroup_size(8, 8, 1)\nfn gemm_f32(@builtin(global_invocation_id) gid: vec3<u32>) {\n  let col: u32 = gid.x;\n  let row: u32 = gid.y;\n  if (col >= N || row >= M) { return; }\n  var acc: f32 = 0.0f;\n  for (var k: u32 = 0u; k < K; k = k + 1u) {\n    let product: f32 = a[row * K + k] * b[k * N + col];\n    acc = acc + product;\n  }\n  c[row * N + col] = acc;\n}\n"
def manifestSource : String := "{\"workgroupSize\": [8, 8, 1],\n \"wgslRevision\": \"2026-08-17\",\n \"schemaVersion\": 1,\n \"profile\": {\"revision\": 1, \"id\": \"leanexe-f32-rne-separate-v1\"},\n \"kernel\": \"gemm_f32\",\n \"entryPoint\": \"gemm_f32\",\n \"dispatchWorkgroups\": [1, 1, 1],\n \"dimensions\": {\"rows\": 3, \"inner\": 2, \"cols\": 5},\n \"buffers\":\n {\"c\": {\"elements\": 15, \"bytes\": 60},\n  \"b\": {\"elements\": 10, \"bytes\": 40},\n  \"a\": {\"elements\": 6, \"bytes\": 24}},\n \"bindings\": {\"group\": 0, \"c\": 2, \"b\": 1, \"a\": 0}}\n"
def metadata : Manifest :=
  { schemaVersion := 1,
    kernel := "gemm_f32",
    entryPoint := "gemm_f32",
    wgslRevision := "2026-08-17",
    profile := { id := "leanexe-f32-rne-separate-v1", revision := 1 },
    dimensions := { rows := 3, cols := 5, inner := 2 },
    bindings := { group := 0, a := 0, b := 1, c := 2 },
    buffers := { a := { elements := 6, bytes := 24 },
                 b := { elements := 10, bytes := 40 },
                 c := { elements := 15, bytes := 60 } },
    workgroupSize := [8, 8, 1],
    dispatchWorkgroups := [1, 1, 1] }
def config : GemmConfig :=
  { rows := 3,
    cols := 5,
    inner := 2,
    group := 0,
    bindingA := 0,
    bindingB := 1,
    bindingC := 2,
    workgroupX := 8,
    workgroupY := 8 }
def ast : GemmSyntax := ⟨config, .guardedRowMajor⟩
def tokenHints : List String := ["const", "M", ":", "u32", "=", "3u", ";", "const", "N", ":", "u32", "=", "5u", ";", "const", "K", ":", "u32", "=",
 "2u", ";", "@", "group", "(", "0", ")", "@", "binding", "(", "0", ")", "var", "<", "storage", ",", "read", ">", "a",
 ":", "array", "<", "f32", ">", ";", "@", "group", "(", "0", ")", "@", "binding", "(", "1", ")", "var", "<", "storage",
 ",", "read", ">", "b", ":", "array", "<", "f32", ">", ";", "@", "group", "(", "0", ")", "@", "binding", "(", "2", ")",
 "var", "<", "storage", ",", "read_write", ">", "c", ":", "array", "<", "f32", ">", ";", "@", "compute", "@",
 "workgroup_size", "(", "8", ",", "8", ",", "1", ")", "fn", "gemm_f32", "(", "@", "builtin", "(",
 "global_invocation_id", ")", "gid", ":", "vec3", "<", "u32", ">", ")", "{", "let", "col", ":", "u32", "=", "gid", ".",
 "x", ";", "let", "row", ":", "u32", "=", "gid", ".", "y", ";", "if", "(", "col", ">=", "N", "||", "row", ">=", "M",
 ")", "{", "return", ";", "}", "var", "acc", ":", "f32", "=", "0.0f", ";", "for", "(", "var", "k", ":", "u32", "=",
 "0u", ";", "k", "<", "K", ";", "k", "=", "k", "+", "1u", ")", "{", "let", "product", ":", "f32", "=", "a", "[", "row",
 "*", "K", "+", "k", "]", "*", "b", "[", "k", "*", "N", "+", "col", "]", ";", "acc", "=", "acc", "+", "product", ";",
 "}", "c", "[", "row", "*", "N", "+", "col", "]", "=", "acc", ";", "}"]
theorem lexed : tokenize source = .ok tokenHints :=
  except_ok_of_toOption _ _ (by decide +kernel)
theorem tokensParsed : parseGemmTokens tokenHints = .ok ast :=
  except_ok_of_toOption _ _ (by decide +kernel)
theorem parsed : parseGemm source = .ok ast :=
  parseGemm_of_tokens source tokenHints ast lexed tokensParsed
def checked : CheckedGemm := ⟨ast, by decide +kernel⟩
def package : Package source metadata where
  tag := .separate
  kernel := checked
  parsed := parsed
  matched := by decide +kernel
def artifact := package.artifact
def numerical := @Package.numerical source metadata package
def exact := @Package.exact source metadata package
#print axioms package
#print axioms artifact
#print axioms numerical
#print axioms exact
end CheckedWGSLPackage
def main (args : List String) : IO Unit := do
  let [shaderPath, manifestPath] := args
    | throw (IO.userError "expected shader and manifest paths")
  unless (← IO.FS.readBinFile shaderPath) == CheckedWGSLPackage.source.toUTF8 do
    throw (IO.userError "shader differs from kernel-checked source")
  unless (← IO.FS.readBinFile manifestPath) == CheckedWGSLPackage.manifestSource.toUTF8 do
    throw (IO.userError "manifest differs from checked file")
  let actual ← match LeanExe.WGSL.decodeManifest CheckedWGSLPackage.manifestSource with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  unless actual == CheckedWGSLPackage.metadata do
    throw (IO.userError "JSON metadata differs from checked metadata")
  IO.println ("WGSL_PACKAGE_BINDING " ++ (Lean.toJson CheckedWGSLPackage.metadata).compress)
