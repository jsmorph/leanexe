import Demos.RunningSumFp.Kernel
import Demos.StreamFold.Model

namespace Demos.RunningSumFp

open Library.Numerics.Decimal.Shared.StrconvGrammar
open Library.Numerics.Decimal.Shared.StrconvRound

def InputLine (line : Array UInt64) (number : Num) : Prop :=
  ∃ text : List UInt8, line = words text ∧ text.length < 2 ^ 32 ∧ LineDenotes text number

/-- Each line of `input` holds fewer than `2^32` bytes. -/
def ShortLines (input : List UInt64) : Prop :=
  ∀ line ∈ StreamFold.Model.lines input, ∃ text : List UInt8, line = words text ∧ text.length < 2 ^ 32

theorem words_injective {a b : List UInt8} (same : words a = words b) : a = b := by
  have lists : a.map UInt8.toUInt64 = b.map UInt8.toUInt64 := by
    simpa [words] using congrArg Array.toList same
  exact List.map_injective_iff.mpr
    (fun x y equal => UInt8.toNat_inj.mp (by simpa using congrArg UInt64.toNat equal)) lists

theorem inputLine_unique {line : Array UInt64} {a b : Num} (first : InputLine line a)
    (second : InputLine line b) : a = b := by
  obtain ⟨text, rfl, _, meaning⟩ := first
  obtain ⟨other, same, _, otherMeaning⟩ := second
  cases words_injective same
  exact lineDenotes_unique text a b meaning otherMeaning

theorem lineRooms {lines : List (Array UInt64)}
    (short : ∀ line ∈ lines, ∃ text : List UInt8, line = words text ∧ text.length < 2 ^ 32)
    (total : Float) : StreamFold.Model.LineRooms kernelSpec total lines := by
  induction lines generalizing total with
  | nil => trivial
  | cons line rest ih =>
      obtain ⟨text, rfl, bound⟩ := short line (List.mem_cons_self ..)
      exact ⟨show (words text).size < 2 ^ 32 by simpa [words] using bound,
        fun _ => ih (fun line member => short line (List.mem_cons_of_mem _ member)) _⟩

theorem foldOutcome_fp {lines : List (Array UInt64)}
    (short : ∀ line ∈ lines, ∃ text : List UInt8, line = words text ∧ text.length < 2 ^ 32)
    (total : Float) :
    ∃ numbers status, StreamFold.Model.LineValues InputLine lines numbers status ∧
      StreamFold.Model.foldOutcome lineKernel total lines =
        ((prefixFloats total numbers).map render, status) := by
  classical
  induction lines generalizing total with
  | nil => exact ⟨[], 0, .nil, rfl⟩
  | cons line rest ih =>
      obtain ⟨text, rfl, bound⟩ := short _ (List.mem_cons_self ..)
      by_cases valid : ∃ number, LineDenotes text number
      · obtain ⟨number, meaning⟩ := valid
        obtain ⟨numbers, status, values, folded⟩ :=
          ih (fun line member => short line (List.mem_cons_of_mem _ member))
            (total + Float.ofBits (round64 number))
        refine ⟨number :: numbers, status, .accept ⟨text, rfl, bound, meaning⟩ values, ?_⟩
        simp [StreamFold.Model.foldOutcome, lineKernel, parse_accept text number bound meaning,
          folded, prefixFloats]
      · have invalid : ∀ number, ¬ LineDenotes text number := by simpa using valid
        refine ⟨[], 28, .reject fun number denotes => ?_, ?_⟩
        · obtain ⟨other, same, _, meaning⟩ := denotes
          cases words_injective same
          exact invalid number meaning
        · simp [StreamFold.Model.foldOutcome, lineKernel, parse_reject text bound invalid,
            prefixFloats]

end Demos.RunningSumFp
