import Library.Hashing.Sha3.Program
import LeanExe.Pipeline.Implements

/-! The lanes are represented as the tuple of their fields, in declaration order. -/

namespace Library.Hashing.Sha3

open LeanExe.Pipeline

instance : Flat Lanes
    (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64) :=
  ⟨fun s => (s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8,
    s.a9, s.a10, s.a11, s.a12, s.a13, s.a14, s.a15, s.a16, s.a17,
    s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24)⟩

end Library.Hashing.Sha3
