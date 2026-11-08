import TestSupport.A64.GptLayer32
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorems of the binary32 GPT-2 layer's bare-metal program for AArch64.  `layerCheck_eq` states
the wrapper's result as the words of the row that `Demos.Gpt32.layerStep32` gives for one head, an
MLP of width 64, position `p`, the weights `layer`, the row `row0`, and the caches `keys0 p` and
`values0 p`.  `runs` is the program's theorem in the form `ProgramRuns`, for every room and cap:
`main` calls entry 14 of `compiled.module`, the wrapper `layerCheck`, on 2, and the machine writes
the array's length word and its elements, `encodeArray (layerCheck 2)`, to the UART and returns 0.
`compiled.layerCheck.trapFree` excludes the trap at `unreachable`, since the allocations of
`layerCheck 2` fit the module's initial pages above the heap's `top`, and `stackBound` lies within
the 4096 bytes that every room exceeds, so the stack does not overflow.
-/

namespace TestSupport.A64.Gpt32

open LeanExe.A64 Demos.Gpt32

/-- The layer's weights of `layerCheck`. -/
def layer : Layer32 :=
  { g1 := vals 64 7 32 64 32.0 0.0, b1 := vals 64 5 1 64 64.0 0.5,
    wq := vals 4096 31 2 101 409.0 0.125, bq := vals 64 3 1 17 64.0 0.125,
    wk := vals 4096 43 9 103 409.0 0.125, bk := vals 64 11 2 19 64.0 0.125,
    wv := vals 4096 47 4 107 409.0 0.125, bv := vals 64 13 3 23 64.0 0.125,
    wo := vals 4096 59 6 109 409.0 0.125, bo := vals 64 17 4 29 64.0 0.125,
    g2 := vals 64 9 32 64 32.0 0.0, b2 := vals 64 7 5 64 64.0 0.5,
    wfc := vals 4096 61 8 113 409.0 0.125, bfc := vals 64 19 5 31 64.0 0.125,
    wproj := vals 4096 67 10 127 409.0 0.125, bproj := vals 64 23 6 37 64.0 0.125 }

/-- The row at position `p` of `layerCheck`. -/
def row0 : Array Float32 := vals 64 37 5 97 13.0 3.5

/-- The key cache of `p` positions of `layerCheck`. -/
def keys0 (p : UInt64) : Array Float32 := vals (p * 64) 53 7 89 41.0 1.0

/-- The value cache of `p` positions of `layerCheck`. -/
def values0 (p : UInt64) : Array Float32 := vals (p * 64) 29 3 83 37.0 1.0

/-- `bits32` gives the zero-extended word of each element of an array of fewer than 2^64
elements. -/
theorem bits32_eq (xs : Array Float32) (h : xs.size < 2 ^ 64) :
    bits32 xs = xs.map fun x => x.toBits.toUInt64 := by
  have hs : xs.size.toUInt64.toNat = xs.size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' h]
  apply Array.ext
  · simp [bits32, LeanExe.build, hs]
  · intro i h1 h2
    have hi : i < xs.size := by simpa using h2
    have e : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi h)
    simp only [bits32, LeanExe.build, Array.getElem_ofFn, Array.getElem_map, e]
    rw [getElem!_pos xs i hi]

theorem add32_size (a b : Array Float32) :
    (Library.Numerics.LinearAlgebra.Binary32.add32 a b).size = a.size % 2 ^ 64 := by
  simp [Library.Numerics.LinearAlgebra.Binary32.add32, LeanExe.build, Nat.toUInt64]

theorem vals_size (n a b q : UInt64) (c o : Float32) : (vals n a b q c o).size = n.toNat := by
  simp [vals, LeanExe.build]

theorem linear32_size (x w b : Array Float32) (k m : UInt64) :
    (Library.Numerics.LinearAlgebra.Binary32.linear32 x w b k m).size = m.toNat := by
  simp [Library.Numerics.LinearAlgebra.Binary32.linear32, LeanExe.build]

theorem row0_size : row0.size = 64 := by
  simp [row0, vals, LeanExe.build]

/-- The row after the layer has 64 elements, as the row before it does. -/
theorem row_size (p : UInt64) :
    (layerStep32 1 64 p layer row0 (keys0 p) (values0 p)).1.size = 64 := by
  simp only [layerStep32, add32_size, row0_size, Nat.reducePow, Nat.reduceMod]

/-- The wrapper is `bits32` of the row after the layer `layer` at position `p`. -/
theorem layerCheck_bits (p : UInt64) :
    layerCheck p = bits32 (layerStep32 1 64 p layer row0 (keys0 p) (values0 p)).1 := by
  simp only [layerCheck, layerStep32, layer, row0, keys0, values0, UInt64.reduceMul]

/-- The wrapper's result is the words of the row after the layer `layer` at position `p`, with
one head and an MLP of width 64. -/
theorem layerCheck_eq (p : UInt64) : layerCheck p =
    (layerStep32 1 64 p layer row0 (keys0 p) (values0 p)).1.map fun x => x.toBits.toUInt64 := by
  rw [layerCheck_bits, bits32_eq _ (by rw [row_size]; decide)]

/-- The heap's `top` at the module's start, plus the allocations of `layerCheck 2`, fits the
initial pages of the memory of `compiled.module`. -/
theorem heap_room : (Verified.initialHeap compiled.tables).top.toNat +
    compiled.layerCheck.bound 2 ≤ 65536 * initialPages compiled.module := by
  rw [compiled.layerCheck.bound_eq]
  simp only [compiled.vals.bound_eq, compiled.layerNorm32.bound_eq, compiled.linear32.bound_eq,
    compiled.append32.bound_eq, compiled.scores32.bound_eq, compiled.headMax32.bound_eq,
    compiled.headSum32.bound_eq, compiled.probs32.bound_eq, compiled.mix32.bound_eq,
    compiled.add32.bound_eq, compiled.geluArray32.bound_eq, compiled.bits32.bound_eq,
    add32_size, vals_size, linear32_size, Verified.blockCost_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The theorem of the binary32 GPT-2 layer's program. -/
theorem runs (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 14 [2] room cap .array
      (LeanExe.Native.encodeArray (layerCheck 2)) fun _ => False :=
  program_runs_bounded compiled.layerCheck.trapFree 2 compiled.initial.1
    (fun hp => room_initStore heap_room hp) writes_array (.inl (by decide +kernel))

end TestSupport.A64.Gpt32
