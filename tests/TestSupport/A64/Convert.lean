import Examples.Convert.Compiled
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorems of the bare-metal programs of `Examples.Convert` for AArch64, in the form
`ProgramRuns`, for every room and cap.  `main` calls entry 2 of `compiled.module`, `toDouble`,
entry 3, `toSingle`, or entry 4, `ofDouble`, on one word, or entry 6, `scale`, on the word of an
`Int64` and the bits of a double, and the machine writes the eight bytes of the result's word to
the UART and returns 0.  A double's word is its bits, a single's word is its bits zero-extended,
and an `Int64`'s word is its two's-complement bits.  The compiler's theorems of the entries
exclude every trap, and `stackBound` gives at most 4096 bytes.  `ofSingle` takes an `f32`
parameter, which `main` does not pass, and has no program.
-/

namespace TestSupport.A64.Convert

open LeanExe.A64 Examples.Convert

/-- An owned result of type `Int64` gives the eight bytes of its word. -/
theorem writes_int64 (heap : LeanExe.Pipeline.Heap) (st : Wasm.Store Unit) (vs : List Wasm.Value)
    (y : Int64) (h : LeanExe.Pipeline.Represent.owned heap st vs y) :
    Writes .word st vs (LeanExe.Native.encodeWord y.toUInt64) :=
  ⟨.i64 y.toUInt64, y.toUInt64, h, rfl, rfl⟩

/-- An owned result of type `Float` gives the eight bytes of its bits. -/
theorem writes_double (heap : LeanExe.Pipeline.Heap) (st : Wasm.Store Unit) (vs : List Wasm.Value)
    (y : Float) (h : LeanExe.Pipeline.Represent.owned heap st vs y) :
    Writes .word st vs (LeanExe.Native.encodeWord y.toBits) :=
  ⟨.f64 y.toBits, y.toBits, h, rfl, rfl⟩

/-- An owned result of type `Float32` gives the eight bytes of its bits zero-extended. -/
theorem writes_float32 (heap : LeanExe.Pipeline.Heap) (st : Wasm.Store Unit)
    (vs : List Wasm.Value) (y : Float32) (h : LeanExe.Pipeline.Represent.owned heap st vs y) :
    Writes .word st vs (LeanExe.Native.encodeWord y.toBits.toUInt64) :=
  ⟨.f32 y.toBits, y.toBits.toUInt64, h, rfl, rfl⟩

theorem entry2_ok : entryOk compiled.module 2 [.i64] 1 .word = true := by decide +kernel

theorem entry3_ok : entryOk compiled.module 3 [.i64] 1 .word = true := by decide +kernel

theorem entry4_ok : entryOk compiled.module 4 [.f64] 1 .word = true := by decide +kernel

theorem entry6_ok : entryOk compiled.module 6 [.i64, .f64] 2 .word = true := by decide +kernel

/-- The theorem of `toDouble`'s program on the word `w` of `a`. -/
theorem toDouble_runs (a : Int64) {w : UInt64} (hw : a.toUInt64 = w) (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 2 [w] room cap .word
      (LeanExe.Native.encodeWord (toDouble a).toBits) fun _ => False := by
  subst hw
  exact program_runs_bounded compiled.toDouble.implements a compiled.initial.1
    (fun _ => trivial) writes_double (.inl (by decide +kernel)) [.i64] rfl entry2_ok

/-- The theorem of `toSingle`'s program on the word `w` of `a`. -/
theorem toSingle_runs (a : Int64) {w : UInt64} (hw : a.toUInt64 = w) (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 3 [w] room cap .word
      (LeanExe.Native.encodeWord (toSingle a).toBits.toUInt64) fun _ => False := by
  subst hw
  exact program_runs_bounded compiled.toSingle.implements a compiled.initial.1
    (fun _ => trivial) writes_float32 (.inl (by decide +kernel)) [.i64] rfl entry3_ok

/-- The theorem of `ofDouble`'s program on the bits `w` of `x`. -/
theorem ofDouble_runs (x : Float) {w : UInt64} (hw : x.toBits = w) (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 4 [w] room cap .word
      (LeanExe.Native.encodeWord (ofDouble x).toUInt64) fun _ => False := by
  subst hw
  exact program_runs_bounded compiled.ofDouble.implements x compiled.initial.1
    (fun _ => trivial) writes_int64 (.inl (by decide +kernel)) [.f64] rfl entry4_ok

/-- The theorem of `scale`'s program on the word `wa` of `a` and the bits `wk` of `k`. -/
theorem scale_runs (a : Int64) (k : Float) {wa wk : UInt64} (ha : a.toUInt64 = wa)
    (hk : k.toBits = wk) (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 6 [wa, wk] room cap .word
      (LeanExe.Native.encodeWord (scale a k).toUInt64) fun _ => False := by
  subst ha hk
  exact program_runs_bounded compiled.scale.implements (a, k) compiled.initial.1
    (fun _ => trivial) writes_int64 (.inl (by decide +kernel)) [.i64, .f64] rfl entry6_ok

end TestSupport.A64.Convert
