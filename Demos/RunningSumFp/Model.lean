import Demos.RunningSumFp.Kernel
import Demos.StreamFold.Model

namespace Demos.RunningSumFp

open Library.Numerics.Decimal.Shared.StrconvGrammar
open Library.Numerics.Decimal.Shared.StrconvRound

def InputLine (line : Array UInt64) (number : Num) : Prop :=
  ∃ text : List UInt8, line = words text ∧ text.length < 2 ^ 32 ∧ LineDenotes text number

def ValidInput (input : List UInt64) (numbers : List Num) : Prop :=
  ∃ lines, StreamFold.Model.ValidInput (fun _ => True) input lines ∧
    List.Forall₂ InputLine lines numbers

noncomputable def finalTotal (total : Float) (numbers : List Num) : Float :=
  numbers.foldl (fun total number => total + Float.ofBits (round64 number)) total

theorem finalTotal_bits (total : Float) (numbers : List Num) :
    (finalTotal total numbers).toBits =
      numbers.foldl (fun bits number => Wasm.IEEE64.add bits (lineBits number)) total.toBits := by
  induction numbers generalizing total with
  | nil => rfl
  | cons number rest ih =>
      change (finalTotal (total + Float.ofBits (round64 number)) rest).toBits = _
      rw [ih, add_bits]
      rfl

theorem inputLine_size {line : Array UInt64} {number : Num} (valid : InputLine line number) :
    line.size < 2 ^ 32 := by
  obtain ⟨text, rfl, bound, _⟩ := valid
  simpa [words] using bound

theorem lineRooms {lines : List (Array UInt64)} {numbers : List Num}
    (valid : List.Forall₂ InputLine lines numbers) (total : Float) :
    StreamFold.Model.LineRooms kernelSpec total lines := by
  induction valid generalizing total with
  | nil => trivial
  | cons line rest ih =>
      exact ⟨inputLine_size line, fun _ => ih _⟩

theorem foldLines_correct {lines : List (Array UInt64)} {numbers : List Num}
    (valid : List.Forall₂ InputLine lines numbers) (total : Float) :
    StreamFold.Model.foldLines lineKernel total lines =
      .ok (finalTotal total numbers, (prefixFloats total numbers).map render) := by
  induction valid generalizing total with
  | nil => rfl
  | @cons line number lines numbers valid rest ih =>
      obtain ⟨text, rfl, bound, meaning⟩ := valid
      simp only [StreamFold.Model.foldLines, lineKernel, parse_accept text number bound meaning,
        ↓reduceIte, ih, prefixFloats, List.map_cons, finalTotal, List.foldl_cons]

theorem model_fp_correct {input : List UInt64} {numbers : List Num}
    (valid : ValidInput input numbers) :
    (StreamFold.Model.consume lineKernel (StreamFold.Model.initial (0 : Float)) input >>=
      StreamFold.Model.finish lineKernel) =
      .ok ⟨finalTotal 0 numbers, #[], (prefixFloats 0 numbers).map render⟩ := by
  obtain ⟨lines, trace, meanings⟩ := valid
  rw [StreamFold.Model.finish_consume_input trace (0 : Float), foldLines_correct meanings]

theorem validInput_safe_and_finalRoom {input : List UInt64} {numbers : List Num}
    (valid : ValidInput input numbers) :
    StreamFold.Model.Safe kernelSpec (StreamFold.Model.initial (0 : Float)) input ∧
      ∀ final, StreamFold.Model.consume lineKernel (StreamFold.Model.initial (0 : Float)) input =
        .ok final → final.pending.size ≠ 0 → kernelSpec.Room final.total final.pending := by
  obtain ⟨lines, trace, meanings⟩ := valid
  exact StreamFold.Model.validInput_safe_and_finalRoom kernelSpec trace 0 (lineRooms meanings 0)

end Demos.RunningSumFp
