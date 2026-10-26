import Library.Hashing.SipHash.Spec
import LeanExe.Pipeline.Implements

/-! The state is represented as the tuple of its fields, in declaration order. -/

namespace Library.Hashing.SipHash

open LeanExe.Pipeline

instance : Flat Spec.State (UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun s => (s.v0, s.v1, s.v2, s.v3)⟩

end Library.Hashing.SipHash
