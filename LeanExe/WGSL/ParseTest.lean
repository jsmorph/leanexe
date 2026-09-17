import LeanExe.WGSL.Parse
import LeanExe.WGSL.GenerateTest

namespace LeanExe.WGSL.ParseTest

/-- Exact captured source, checked against the file by main below. -/
def rectangularSource : String := "// leanexe WGSL GEMM v1; row-major f32 storage buffers\nconst M: u32 = 3u;\nconst N: u32 = 5u;\nconst K: u32 = 2u;\n\n@group(0) @binding(0) var<storage, read> a: array<f32>;\n@group(0) @binding(1) var<storage, read> b: array<f32>;\n@group(0) @binding(2) var<storage, read_write> c: array<f32>;\n\n@compute @workgroup_size(8, 8, 1)\nfn gemm_f32(@builtin(global_invocation_id) gid: vec3<u32>) {\n  let col: u32 = gid.x;\n  let row: u32 = gid.y;\n  if (col >= N || row >= M) { return; }\n  var acc: f32 = 0.0f;\n  for (var k: u32 = 0u; k < K; k = k + 1u) {\n    let product: f32 = a[row * K + k] * b[k * N + col];\n    acc = acc + product;\n  }\n  c[row * N + col] = acc;\n}\n"

def accepts (source : String) : Bool :=
  match checkGemm source with | .ok _ => true | .error _ => false

def hasConfig (source : String) (config : GemmConfig) : Bool :=
  match checkGemm source with | .ok k => k.ast.config == config | .error _ => false

#guard hasConfig rectangularSource GenerateTest.rectangular
#guard (match tokenize "const/**/M" with | .ok ts => ts == ["const", "M"] | .error _ => false)
#guard (match tokenize "/* outside /* nested */ done */const" with | .ok ts => ts == ["const"] | .error _ => false)
#guard !accepts (rectangularSource ++ "/* unterminated")
#guard !accepts (rectangularSource ++ "/* outer /* inner */")
#guard !accepts (rectangularSource ++ "*/")
#guard !accepts (rectangularSource ++ "//" ++ String.singleton (Char.ofNat 0))
#guard !accepts (String.singleton (Char.ofNat 65279) ++ rectangularSource)
#guard !accepts (rectangularSource.replace "const M" "con/**/st M")
#guard !accepts (rectangularSource.replace "3u" "03u")
#guard !accepts (rectangularSource.replace "3u" "3 u")
#guard !accepts (rectangularSource.replace "3u" "4294967296u")
#guard !accepts (rectangularSource.replace "3u" "0u")
#guard !accepts (rectangularSource.replace "binding(2)" "binding(1)")
#guard !accepts (rectangularSource.replace "workgroup_size(8, 8, 1)" "workgroup_size(8, 8, 2)")
#guard !accepts (rectangularSource.replace "workgroup_size(8, 8, 1)" "workgroup_size(32, 32, 1)")
#guard !accepts (rectangularSource.replace "@group(0) @binding(2)" "@group(1) @binding(2)")
#guard !accepts (rectangularSource.replace "storage, read_write" "storage, read")
#guard !accepts (rectangularSource.replace "acc = acc + product" "acc = product + acc")
#guard !accepts (rectangularSource.replace "a[row * K + k]" "a[row * N + k]")
#guard !accepts (rectangularSource.replace "c[row * N + col] = acc" "c[0u] = acc")
#guard !accepts (rectangularSource.replace "col >= N || row >= M" "col >= N || row >= N")
#guard !accepts (rectangularSource.replace "1u) {" "2u) {")
#guard !accepts (rectangularSource.replace "0.0f" "-0.0f")
#guard !accepts (rectangularSource ++ "fn extra() {}")
#guard !accepts (rectangularSource ++ rectangularSource)

/-- An extra store after every normative line ending must stay visible. -/
def rejectsHiddenStore (code : Nat) : Bool :=
  !accepts (rectangularSource.replace "= acc;" ("= acc; // comment" ++
    String.singleton (Char.ofNat code) ++ "c[row * N + col] = 0.0f;"))

#guard [10, 11, 12, 13, 133, 8232, 8233].all rejectsHiddenStore
#guard accepts (rectangularSource.replace "const M" "const/* outer /* nested */ */M")
#guard accepts (rectangularSource.replace "\n" "\r\n")
#guard accepts (rectangularSource ++ "// final comment")
#guard [9, 10, 11, 12, 13, 32, 133, 8206, 8207, 8232, 8233].all
  (fun c => accepts (rectangularSource.replace "const M" ("const" ++ String.singleton (Char.ofNat c) ++ "M")))

/-- Generation is exercised only as an independent positive corpus, never as
an input to the recognizer's body grammar. -/
def configurations : List GemmConfig := [
  { rows := 1, cols := 1, inner := 1 },
  { rows := 1, cols := 1, inner := 2, workgroupX := 1, workgroupY := 1 },
  { rows := 9, cols := 17, inner := 3 },
  { rows := 7, cols := 13, inner := 4, group := 3, bindingA := 7,
    bindingB := 19, bindingC := 999, workgroupX := 16, workgroupY := 4 }]

#guard configurations.all (fun config => hasConfig (renderGemm config) config)

end LeanExe.WGSL.ParseTest

/-- Filesystem identity is a regression gate, not an IO axiom in any theorem. -/
def main : IO Unit := do
  let actual ← IO.FS.readFile "test/wgsl/artifacts/rectangular/kernel.wgsl"
  unless actual == LeanExe.WGSL.ParseTest.rectangularSource do
    throw (IO.userError "captured rectangular WGSL differs from the checked literal")
  IO.println "WGSL golden source identity and parser adversarial corpus passed"
