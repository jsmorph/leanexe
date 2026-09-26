import Project.Compiler.Parsing
import Project.Compiler.UnsignedLeb
import Project.Compiler.SignedLeb

namespace Project.Compiler.Parsing

open Wasm.Binary
open Wasm.Binary.Leb Wasm.Binary.Leb.Proof

theorem unsigned_trace {width shift fuel acc : Nat} {bytes : List UInt8} {value : Nat}
    (h : UnsignedTrace width shift fuel acc bytes value) :
    Parses (Internal.unsignedLoop width shift fuel acc) bytes value := by
  induction h with
  | terminal fuel byte terminal shiftFits fits =>
    unfold Internal.unsignedLoop
    apply bind_parses (a := [byte]) (b := []) (read_byte byte)
    simpa [fits, terminal] using pure_parses _
  | next fuel byte tail result continuation positive trace ih =>
    unfold Internal.unsignedLoop
    apply bind_parses (a := [byte]) (b := tail) (read_byte byte)
    simpa [show fuel ≠ 0 by omega, show ¬ byte.toNat < 128 by omega] using ih

theorem signed_trace {width shift fuel acc : Nat} {bytes : List UInt8} {value : Int}
    (h : SignedTrace width shift fuel acc bytes value) :
    Parses (Internal.signedLoop width shift fuel acc) bytes value := by
  induction h with
  | terminal fuel byte terminal shiftFits fits =>
    unfold Internal.signedLoop
    apply bind_parses (a := [byte]) (b := []) (read_byte byte)
    simpa [fits, terminal] using pure_parses _
  | next fuel byte tail result continuation positive trace ih =>
    unfold Internal.signedLoop
    apply bind_parses (a := [byte]) (b := tail) (read_byte byte)
    simpa [show fuel ≠ 0 by omega, show ¬ byte.toNat < 128 by omega] using ih

theorem u32 (n : Nat) (bound : n < 2 ^ 32) :
    Parses Leb.u32 (LeanExe.Wasm.Binary.u32leb n) (UInt32.ofNat n) := by
  have hn : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (by change n < 2 ^ 64; omega)
  have trace := UnsignedLeb.trace 5 5 32 0 0 n (by decide) (by decide) bound
  have parsed := unsigned_trace trace
  have encoded : LeanExe.Wasm.Binary.u32leb n = UnsignedLeb.bytes 10 n := by
    simp only [LeanExe.Wasm.Binary.u32leb, byteArray_toList,
      LeanExe.Wasm.Leb.u32lebU64_eq_lebList, UnsignedLeb.native_bytes, hn]
  rw [encoded]
  unfold Leb.u32
  simpa using bind_parses (q := fun value => pure (UInt32.ofNat value))
    (by simpa using parsed) (pure_parses (UInt32.ofNat n))

theorem s64 (v : UInt64) :
    Parses Leb.s64 (LeanExe.Wasm.Leb.s64lebU64 v).toList v.toBitVec.toInt := by
  have trace := SignedLeb.trace 10 64 0 0 v.toBitVec.toInt (by decide) (by decide)
    (BitVec.le_toInt _) BitVec.toInt_lt
  have encoded : (LeanExe.Wasm.Leb.s64lebU64 v).toList = SignedLeb.bytes 10 v.toBitVec.toInt := by
    rw [byteArray_toList]
    simp only [LeanExe.Wasm.Leb.s64lebU64, SignedLeb.native_bytes, ByteArray.data_empty,
      Array.toList_empty, List.nil_append]
  rw [encoded]
  simpa [Leb.s64] using signed_trace trace

end Project.Compiler.Parsing
