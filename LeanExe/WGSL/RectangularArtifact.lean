import LeanExe.WGSL.Index

namespace LeanExe.WGSL.RectangularArtifact

deriving instance DecidableEq for GemmConfig
deriving instance DecidableEq for GemmSyntax

/-- Exact captured UTF-8 source text. The file-identity gate checks the bytes. -/
def source : String := "// leanexe WGSL GEMM v1; row-major f32 storage buffers\nconst M: u32 = 3u;\nconst N: u32 = 5u;\nconst K: u32 = 2u;\n\n@group(0) @binding(0) var<storage, read> a: array<f32>;\n@group(0) @binding(1) var<storage, read> b: array<f32>;\n@group(0) @binding(2) var<storage, read_write> c: array<f32>;\n\n@compute @workgroup_size(8, 8, 1)\nfn gemm_f32(@builtin(global_invocation_id) gid: vec3<u32>) {\n  let col: u32 = gid.x;\n  let row: u32 = gid.y;\n  if (col >= N || row >= M) { return; }\n  var acc: f32 = 0.0f;\n  for (var k: u32 = 0u; k < K; k = k + 1u) {\n    let product: f32 = a[row * K + k] * b[k * N + col];\n    acc = acc + product;\n  }\n  c[row * N + col] = acc;\n}\n"

def ast : GemmSyntax := ⟨{ rows := 3, cols := 5, inner := 2 }, .guardedRowMajor⟩

private theorem of_toOption {E A : Type} (result : Except E A) (value : A)
    (h : result.toOption = some value) : result = .ok value := by
  cases result with
  | error _ => cases h
  | ok actual => cases Option.some.inj h; rfl

/-- The candidate token list is untrusted until lexed proves its identity. -/
def sourceTokens : List String := ["const","M",":","u32","=","3u",";","const","N",":","u32","=","5u",";","const","K",":","u32","=","2u",";","@","group","(","0",")","@","binding","(","0",")","var","<","storage",",","read",">","a",":","array","<","f32",">",";","@","group","(","0",")","@","binding","(","1",")","var","<","storage",",","read",">","b",":","array","<","f32",">",";","@","group","(","0",")","@","binding","(","2",")","var","<","storage",",","read_write",">","c",":","array","<","f32",">",";","@","compute","@","workgroup_size","(","8",",","8",",","1",")","fn","gemm_f32","(","@","builtin","(","global_invocation_id",")","gid",":","vec3","<","u32",">",")","{","let","col",":","u32","=","gid",".","x",";","let","row",":","u32","=","gid",".","y",";","if","(","col",">=","N","||","row",">=","M",")","{","return",";","}","var","acc",":","f32","=","0.0f",";","for","(","var","k",":","u32","=","0u",";","k","<","K",";","k","=","k","+","1u",")","{","let","product",":","f32","=","a","[","row","*","K","+","k","]","*","b","[","k","*","N","+","col","]",";","acc","=","acc","+","product",";","}","c","[","row","*","N","+","col","]","=","acc",";","}"]

theorem lexedOption : (tokenize source).toOption = some sourceTokens := by decide +kernel

theorem lexed : tokenize source = .ok sourceTokens := of_toOption _ _ lexedOption

theorem tokensParsedOption : (parseGemmTokens sourceTokens).toOption = some ast := by decide +kernel

theorem tokensParsed : parseGemmTokens sourceTokens = .ok ast :=
  of_toOption _ _ tokensParsedOption

/-- Kernel-reduced parsing of this exact text; no native-decide witness. -/
theorem parsed : parseGemm source = .ok ast :=
  parseGemm_of_tokens source sourceTokens ast lexed tokensParsed

theorem valid : ast.config.Valid := by decide

def checked : CheckedGemm := ⟨ast, valid⟩

/-- Concrete access safety follows from the general parser-envelope theorem. -/
theorem indices {row col k : Nat} (hr : row < 3) (hc : col < 5) (hk : k < 2) :
    Index.CellBounds ast.config row col k :=
  Index.cell_bounds checked hr hc hk

#print axioms parsed
#print axioms valid
#print axioms indices

end LeanExe.WGSL.RectangularArtifact
