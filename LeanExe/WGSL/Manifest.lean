import LeanExe.WGSL.Parse
import LeanExe.WGSL.Profile

namespace LeanExe.WGSL

inductive ProfileTag where
  | separate
  | fusion
  deriving Repr, DecidableEq, BEq

def ProfileTag.profile : ProfileTag → Profile
  | .separate => restricted
  | .fusion => LeanExe.WGSL.fusion

def ProfileTag.id : ProfileTag → String
  | .separate => restrictedProfileId
  | .fusion => fusionProfileId

theorem ProfileTag.acceptsScalar (tag : ProfileTag) : tag.profile.scalar ieeeChoice := by
  cases tag <;> rfl

theorem ProfileTag.acceptsSeparate (tag : ProfileTag) : tag.profile.evaluation .separate := by
  cases tag
  · rfl
  · trivial

structure ManifestProfile where
  id : String
  revision : Nat
  deriving Lean.FromJson, Lean.ToJson, Repr, BEq, DecidableEq

structure ManifestDimensions where
  rows : Nat
  cols : Nat
  inner : Nat
  deriving Lean.FromJson, Lean.ToJson, Repr, BEq, DecidableEq

structure ManifestBindings where
  group : Nat
  a : Nat
  b : Nat
  c : Nat
  deriving Lean.FromJson, Lean.ToJson, Repr, BEq, DecidableEq

structure ManifestBuffer where
  elements : Nat
  bytes : Nat
  deriving Lean.FromJson, Lean.ToJson, Repr, BEq, DecidableEq

structure ManifestBuffers where
  a : ManifestBuffer
  b : ManifestBuffer
  c : ManifestBuffer
  deriving Lean.FromJson, Lean.ToJson, Repr, BEq, DecidableEq

/-- Metadata interpreted by the native harness. The independent file checker
decodes the JSON and compares it with this embedded value; the kernel checks
every semantic field against the independently parsed shader below. -/
structure Manifest where
  schemaVersion : Nat
  kernel : String
  entryPoint : String
  wgslRevision : String
  profile : ManifestProfile
  dimensions : ManifestDimensions
  bindings : ManifestBindings
  buffers : ManifestBuffers
  workgroupSize : List Nat
  dispatchWorkgroups : List Nat
  deriving Lean.FromJson, Lean.ToJson, Repr, BEq, DecidableEq

def decodeManifest (source : String) : Except String Manifest := do
  Lean.fromJson? (← Lean.Json.parse source)

def Manifest.Matches (m : Manifest) (c : GemmConfig) (tag : ProfileTag) : Prop :=
  m.schemaVersion = 1 ∧ m.kernel = "gemm_f32" ∧ m.entryPoint = "gemm_f32" ∧
  m.wgslRevision = "2026-08-17" ∧ m.profile.id = tag.id ∧ m.profile.revision = 1 ∧
  m.dimensions.rows = c.rows ∧ m.dimensions.cols = c.cols ∧ m.dimensions.inner = c.inner ∧
  m.bindings.group = c.group ∧ m.bindings.a = c.bindingA ∧
  m.bindings.b = c.bindingB ∧ m.bindings.c = c.bindingC ∧
  m.buffers.a.elements = c.elementsA ∧ m.buffers.a.bytes = 4 * c.elementsA ∧
  m.buffers.b.elements = c.elementsB ∧ m.buffers.b.bytes = 4 * c.elementsB ∧
  m.buffers.c.elements = c.elementsC ∧ m.buffers.c.bytes = 4 * c.elementsC ∧
  m.workgroupSize = [c.workgroupX, c.workgroupY, 1] ∧
  m.dispatchWorkgroups = [c.dispatchX, c.dispatchY, 1]

instance (m : Manifest) (c : GemmConfig) (tag : ProfileTag) : Decidable (m.Matches c tag) := by
  unfold Manifest.Matches
  infer_instance

end LeanExe.WGSL
