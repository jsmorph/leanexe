import Library.Hashing.Words.Program
import LeanExe.Pipeline.Implements

/-! Each word structure is represented as the tuple of its fields, in declaration order. -/

namespace Library.Hashing.Words

open LeanExe.Pipeline

instance : Flat Words4 (UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun d => (d.w0, d.w1, d.w2, d.w3)⟩

instance : Flat Words6 (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun d => (d.w0, d.w1, d.w2, d.w3, d.w4, d.w5)⟩

instance : Flat Words8
    (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun d => (d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7)⟩

instance : Flat Words16
    (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun d => (d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7,
    d.w8, d.w9, d.w10, d.w11, d.w12, d.w13, d.w14, d.w15)⟩

end Library.Hashing.Words
