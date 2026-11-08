import TestSupport.A64.GptScores
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorems of the GPT-2 kernel's bare-metal program for AArch64.  `scoresCheck_eq` states the
wrapper's result as the words of `Demos.Gpt.scores` on the inputs of `TestSupport.A64.GptScores`.
`runs` is the program's theorem in the form `ProgramRuns`, for every room and cap: `main` calls
entry 14 of `compiled.module`, the wrapper `scoresCheck`, on 3, and the machine writes the array's
length word and its elements, `encodeArray (scoresCheck 3)`, to the UART and returns 0.
`compiled.scoresCheck.trapFree` excludes the trap at `unreachable`, since the allocations of
`scoresCheck 3`, 6,848 bytes, fit the module's initial pages above the heap's `top` at byte 4096,
and `stackBound`, 2,688 bytes, lies within the 4096 bytes that every room exceeds, so the stack
does not overflow.
-/

namespace TestSupport.A64.Gpt

open LeanExe.A64 Demos.Gpt

/-- `bits` gives the word of each element of an array of fewer than 2^64 elements. -/
theorem bits_eq (xs : Array Float) (h : xs.size < 2 ^ 64) : bits xs = xs.map Float.toBits := by
  have hs : xs.size.toUInt64.toNat = xs.size := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' h]
  apply Array.ext
  · simp [bits, LeanExe.build, hs]
  · intro i h1 h2
    have hi : i < xs.size := by simpa using h2
    have e : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi h)
    simp only [bits, LeanExe.build, Array.getElem_ofFn, Array.getElem_map, e]
    rw [getElem!_pos xs i hi]

/-- The wrapper's result is the words of the scores of the last position of the cache of `p`
positions against the 32 embeddings, after the final layer norm, with one layer, two heads of
width 8, and `eps` 1e-5. -/
theorem scoresCheck_eq (p : UInt64) : scoresCheck p =
    (scores (cacheOf p) (embeddings 32 16) (gains 16) (biases 16) 1 2 8 32 1e-5).map
      Float.toBits := by
  apply bits_eq
  simp [scores, Library.Numerics.LinearAlgebra.Float64.matMulT, LeanExe.build]

/-- The heap's `top` at the module's start, plus the allocations of `scoresCheck 3`, fits the
initial pages of the memory of `compiled.module`. -/
theorem heap_room : (Verified.initialHeap compiled.tables).top.toNat +
    compiled.scoresCheck.bound 3 ≤ 65536 * initialPages compiled.module := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The theorem of the GPT-2 kernel's program. -/
theorem runs (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 14 [3] room cap .array
      (LeanExe.Native.encodeArray (scoresCheck 3)) fun _ => False :=
  program_runs_bounded compiled.scoresCheck.trapFree 3 compiled.initial.1
    (fun hp => room_initStore heap_room hp) writes_array (.inl (by decide +kernel))

end TestSupport.A64.Gpt
