import Lean

namespace LeanExe.WGSL

/-- The first lowering is a fixed, row-major `C = A * B` kernel. Dimensions
are specialized into the artifact; buffers contain IEEE binary32 words. -/
structure GemmConfig where
  rows : Nat
  cols : Nat
  inner : Nat
  group : Nat := 0
  bindingA : Nat := 0
  bindingB : Nat := 1
  bindingC : Nat := 2
  workgroupX : Nat := 8
  workgroupY : Nat := 8
  deriving BEq, Repr, Lean.ToJson

def GemmConfig.elementsA (config : GemmConfig) : Nat := config.rows * config.inner
def GemmConfig.elementsB (config : GemmConfig) : Nat := config.inner * config.cols
def GemmConfig.elementsC (config : GemmConfig) : Nat := config.rows * config.cols

/-- Natural-number ceiling division. Validation excludes a zero divisor. -/
def ceilDiv (n divisor : Nat) : Nat := (n + divisor - 1) / divisor

def GemmConfig.dispatchX (config : GemmConfig) : Nat := ceilDiv config.cols config.workgroupX
def GemmConfig.dispatchY (config : GemmConfig) : Nat := ceilDiv config.rows config.workgroupY

/-- Conservative resource envelope for the first native harness. The runtime
must still check its actual adapter limits and provision disjoint A/B/C buffers.
The element cap is 128 MiB per storage binding, and also keeps all shader
index products inside u32. These are generation limits, not a runtime theorem. -/
def GemmConfig.Valid (config : GemmConfig) : Prop :=
  0 < config.rows ∧ 0 < config.cols ∧ 0 < config.inner ∧
  config.rows ≤ 4294967295 ∧ config.cols ≤ 4294967295 ∧ config.inner ≤ 4294967295 ∧
  config.elementsA ≤ 33554432 ∧ config.elementsB ≤ 33554432 ∧
  config.elementsC ≤ 33554432 ∧
  config.group < 4 ∧ config.bindingA < 1000 ∧ config.bindingB < 1000 ∧
  config.bindingC < 1000 ∧
  config.bindingA ≠ config.bindingB ∧ config.bindingA ≠ config.bindingC ∧
  config.bindingB ≠ config.bindingC ∧
  0 < config.workgroupX ∧ 0 < config.workgroupY ∧
  config.workgroupX ≤ 256 ∧ config.workgroupY ≤ 256 ∧
  config.workgroupX * config.workgroupY ≤ 256 ∧
  config.dispatchX ≤ 65535 ∧ config.dispatchY ≤ 65535

instance (config : GemmConfig) : Decidable config.Valid := by
  unfold GemmConfig.Valid
  infer_instance

structure ValidatedGemmConfig where
  config : GemmConfig
  valid : config.Valid

private def configError (config : GemmConfig) : String :=
  if config.rows = 0 ∨ config.cols = 0 ∨ config.inner = 0 then
    "GEMM dimensions must be positive"
  else if config.rows > 4294967295 ∨ config.cols > 4294967295 ∨ config.inner > 4294967295 then
    "GEMM dimensions must fit u32"
  else if config.elementsA > 33554432 ∨ config.elementsB > 33554432 ∨
      config.elementsC > 33554432 then
    "GEMM storage bindings must not exceed 128 MiB"
  else if config.group ≥ 4 then
    "GEMM bind group must be below 4"
  else if config.bindingA ≥ 1000 ∨ config.bindingB ≥ 1000 ∨ config.bindingC ≥ 1000 then
    "GEMM binding indices must be below 1000"
  else if config.bindingA = config.bindingB ∨ config.bindingA = config.bindingC ∨
      config.bindingB = config.bindingC then
    "GEMM A, B, and C require distinct binding indices"
  else if config.workgroupX = 0 ∨ config.workgroupY = 0 then
    "GEMM workgroup dimensions must be positive"
  else if config.workgroupX > 256 ∨ config.workgroupY > 256 ∨
      config.workgroupX * config.workgroupY > 256 then
    "GEMM workgroups must contain at most 256 invocations"
  else
    "GEMM dispatch dimensions must not exceed 65535 workgroups"

def validateConfig (config : GemmConfig) : Except String ValidatedGemmConfig :=
  if valid : config.Valid then .ok ⟨config, valid⟩ else .error (configError config)

/-- Explicit scalar operations for the checked source definition. These are
parameters, not a claim that host arithmetic implements WGSL. A later scalar
model and artifact theorem supply their binary32 interpretation. -/
structure ScalarArithmetic where
  add : UInt32 → UInt32 → UInt32
  mul : UInt32 → UInt32 → UInt32

abbrev WordBuffer := Nat → UInt32

/-- Source-ordered GEMM accumulation, initialized with positive zero's raw
binary32 encoding. It performs a separate multiplication and addition at each
step. Native shader evaluation needs a profile-conformance assumption before
it can be identified with these source operations. -/
def gemmAccum (arithmetic : ScalarArithmetic) (config : GemmConfig)
    (a b : WordBuffer) (row col : Nat) : Nat → UInt32
  | 0 => 0
  | k + 1 => arithmetic.add (gemmAccum arithmetic config a b row col k)
      (arithmetic.mul (a (row * config.inner + k)) (b (k * config.cols + col)))

def gemmCell (arithmetic : ScalarArithmetic) (config : GemmConfig)
    (a b : WordBuffer) (row col : Nat) : UInt32 :=
  gemmAccum arithmetic config a b row col config.inner

abbrev GemmImplementation := ScalarArithmetic → GemmConfig → WordBuffer →
  WordBuffer → Nat → Nat → UInt32

/-- The deliberately narrow equivalent of a kernel annotation. A checked Lean
declaration with this type selects GEMM lowering and carries a proof that its
implementation is the supported source definition. This is not arbitrary Lean
extraction. The witness constrains source selection; it does not prove anything
about the emitted WGSL, which must be parsed and checked independently. -/
structure KernelCandidate where
  config : GemmConfig
  implementation : GemmImplementation
  loweringWitness : implementation = gemmCell

def gemmCandidate (config : GemmConfig) : KernelCandidate :=
  { config, implementation := gemmCell, loweringWitness := rfl }

/-- Canonical rendering for the untiled subset. This function is intentionally
not trusted by artifact proofs. There are no barriers or shared-memory writes:
one global invocation computes one output cell. Out-of-range invocations exit
before any access, including partially filled workgroups at matrix edges. -/
def renderGemm (config : GemmConfig) : String :=
  String.intercalate "\n" [
    "// leanexe WGSL GEMM v1; row-major f32 storage buffers",
    s!"const M: u32 = {config.rows}u;",
    s!"const N: u32 = {config.cols}u;",
    s!"const K: u32 = {config.inner}u;",
    "",
    s!"@group({config.group}) @binding({config.bindingA}) var<storage, read> a: array<f32>;",
    s!"@group({config.group}) @binding({config.bindingB}) var<storage, read> b: array<f32>;",
    s!"@group({config.group}) @binding({config.bindingC}) var<storage, read_write> c: array<f32>;",
    "",
    s!"@compute @workgroup_size({config.workgroupX}, {config.workgroupY}, 1)",
    "fn gemm_f32(@builtin(global_invocation_id) gid: vec3<u32>) {",
    "  let col: u32 = gid.x;",
    "  let row: u32 = gid.y;",
    "  if (col >= N || row >= M) { return; }",
    "  var acc: f32 = 0.0f;",
    "  for (var k: u32 = 0u; k < K; k = k + 1u) {",
    "    let product: f32 = a[row * K + k] * b[k * N + col];",
    "    acc = acc + product;",
    "  }",
    "  c[row * N + col] = acc;",
    "}",
    ""
  ]

structure GeneratedKernel where
  config : GemmConfig
  configValid : config.Valid
  source : String
  deriving Repr

def lowerCandidate (candidate : KernelCandidate) : Except String GeneratedKernel := do
  let checked ← validateConfig candidate.config
  pure {
    config := checked.config
    configValid := checked.valid
    source := renderGemm checked.config
  }

def generateGemm (config : GemmConfig) : Except String GeneratedKernel :=
  lowerCandidate (gemmCandidate config)

private def bufferManifest (elements : Nat) : Lean.Json :=
  Lean.Json.mkObj [("elements", Lean.toJson elements), ("bytes", Lean.toJson (4 * elements))]

/-- Runtime manifest for the exact file emitted alongside it. Profile metadata
is a caller-supplied selection, not evidence of native runtime conformance.
Artifact identity must additionally record the actual source bytes. -/
def renderManifest (kernel : GeneratedKernel) (profileId : String)
    (profileRevision : Nat) : String :=
  let config := kernel.config
  Lean.Json.pretty (Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("kernel", Lean.toJson "gemm_f32"),
    ("entryPoint", Lean.toJson "gemm_f32"),
    ("wgslRevision", Lean.toJson "2026-08-17"),
    ("dimensions", Lean.Json.mkObj [
      ("rows", Lean.toJson config.rows), ("cols", Lean.toJson config.cols),
      ("inner", Lean.toJson config.inner)]),
    ("bindings", Lean.Json.mkObj [
      ("group", Lean.toJson config.group), ("a", Lean.toJson config.bindingA),
      ("b", Lean.toJson config.bindingB), ("c", Lean.toJson config.bindingC)]),
    ("workgroupSize", Lean.toJson [config.workgroupX, config.workgroupY, 1]),
    ("dispatchWorkgroups", Lean.toJson [config.dispatchX, config.dispatchY, 1]),
    ("buffers", Lean.Json.mkObj [
      ("a", bufferManifest config.elementsA), ("b", bufferManifest config.elementsB),
      ("c", bufferManifest config.elementsC)]),
    ("profile", Lean.Json.mkObj [
      ("id", Lean.toJson profileId), ("revision", Lean.toJson profileRevision)])
  ]) ++ "\n"

end LeanExe.WGSL
