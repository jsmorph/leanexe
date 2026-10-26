import Library.Hashing.XxHash64.Spec
import LeanExe.Pipeline.Implements

/-! The accumulators are represented as the tuple of their fields, in declaration order. -/

namespace Library.Hashing.XxHash64

open LeanExe.Pipeline

instance : Flat Spec.Accs (UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun a => (a.acc1, a.acc2, a.acc3, a.acc4)⟩

end Library.Hashing.XxHash64
