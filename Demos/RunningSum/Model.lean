import Demos.RunningSum.Kernel
import Demos.StreamFold.Model
import Mathlib.Data.List.Forall2

namespace Demos.RunningSum

def integerDigitCount (value : Int) : Nat := (Nat.digits 10 value.natAbs).length

/-- The cumulative totals of `values` after `total`. -/
def prefixTotals (total : Int) : List Int → List Int
  | [] => []
  | value :: rest => (total + value) :: prefixTotals (total + value) rest

/-- Each line holds fewer than `2^64 - 3` bytes, and for each prefix of valid lines, `total`
plus the sum of their integers has fewer than `2^64 - 3` decimal digits. -/
structure BoundsFrom (total : Int) (lines : List (Array UInt64)) : Prop where
  lineSizes : ∀ line ∈ lines, line.size + 3 < UInt64.size
  totals : ∀ prior, prior <+: lines → (∀ line ∈ prior, ValidLine line) →
    integerDigitCount (total + (prior.map lineInteger).sum) + 3 < UInt64.size

def InputBounds (input : List UInt64) : Prop := BoundsFrom 0 (StreamFold.Model.lines input)

theorem BoundsFrom.current {total : Int} {lines : List (Array UInt64)}
    (bounds : BoundsFrom total lines) : integerDigitCount total + 3 < UInt64.size := by
  simpa using bounds.totals [] List.nil_prefix (by simp)

theorem BoundsFrom.tail {total : Int} {line : Array UInt64} {lines : List (Array UInt64)}
    (bounds : BoundsFrom total (line :: lines)) (valid : ValidLine line) :
    BoundsFrom (total + lineInteger line) lines := by
  refine ⟨fun next member => bounds.lineSizes next (List.mem_cons_of_mem _ member), ?_⟩
  intro prior isPrefix allValid
  have bound := bounds.totals (line :: prior) (List.cons_prefix_cons.mpr ⟨rfl, isPrefix⟩)
    (by
      intro next member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ valid
      · exact allValid next member)
  simpa only [List.map_cons, List.sum_cons, add_assoc] using bound

theorem decimal_digitCount (number : Decimal) (normal : number.Valid) :
    integerDigitCount number.value = number.digits.size := by
  unfold integerDigitCount Decimal.value
  cases number.negative <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Int.natAbs_neg, Int.natAbs_natCast, normal_natDigits number.digits normal,
    List.length_map, List.length_reverse, Array.length_toList]

theorem BoundsFrom.room {total : Decimal} {line : Array UInt64} {lines : List (Array UInt64)}
    (normal : total.Valid) (bounds : BoundsFrom total.value (line :: lines)) :
    kernelSpec.Room total line := by
  have totalBound := bounds.current
  rw [decimal_digitCount total normal] at totalBound
  have lineBound := bounds.lineSizes line List.mem_cons_self
  change max total.digits.size line.size + 3 < UInt64.size
  omega

theorem lineRooms {lines : List (Array UInt64)} {total : Decimal} (normal : total.Valid)
    (bounds : BoundsFrom total.value lines) :
    StreamFold.Model.LineRooms kernelSpec total lines := by
  induction lines generalizing total with
  | nil => trivial
  | cons line rest ih =>
      have room := bounds.room normal
      refine ⟨room, fun accepted => ?_⟩
      have valid : ValidLine line := (parse_valid_iff line (kernelSpec.lineFits room)).mp accepted
      obtain ⟨sumNormal, _, sumValue⟩ := kernel_accepted normal room accepted
      apply ih sumNormal
      rw [sumValue]
      exact bounds.tail valid

theorem decimalLine_unique {line : Array UInt64} {a b : Int} (first : DecimalLine line a)
    (second : DecimalLine line b) : a = b := by
  rw [((decimalLine_iff line a).mp first).2, ((decimalLine_iff line b).mp second).2]

theorem foldOutcome_integer {lines : List (Array UInt64)} {total : Decimal} (normal : total.Valid)
    (bounds : BoundsFrom total.value lines) :
    ∃ values status, StreamFold.Model.LineValues DecimalLine lines values status ∧
      ∃ outputs, StreamFold.Model.foldOutcome lineKernel total lines = (outputs, status) ∧
        List.Forall₂ DecimalOutput (prefixTotals total.value values) outputs := by
  induction lines generalizing total with
  | nil => exact ⟨[], 0, .nil, [], rfl, .nil⟩
  | cons line rest ih =>
      have room := bounds.room normal
      have lineBound : line.size < UInt64.size := kernelSpec.lineFits room
      by_cases valid : ValidLine line
      · have accepted : (parse line).valid = true := (parse_valid_iff line lineBound).mpr valid
        obtain ⟨sumNormal, sumFits, sumValue⟩ := kernel_accepted normal room accepted
        obtain ⟨values, status, lineValues, outputs, folded, encoded⟩ :=
          ih sumNormal (by rw [sumValue]; exact bounds.tail valid)
        refine ⟨lineInteger line :: values, status,
          .accept ((decimalLine_iff line _).mpr ⟨valid, rfl⟩) lineValues,
          render (add total (parse line).value) :: outputs, ?_, ?_⟩
        · simp [StreamFold.Model.foldOutcome, lineKernel, accepted, folded]
        · rw [prefixTotals, ← sumValue]
          exact .cons (render_correct _ sumNormal sumFits) encoded
      · have rejected : (parse line).valid = false := by
          cases parsed : (parse line).valid with
          | false => rfl
          | true => exact absurd ((parse_valid_iff line lineBound).mp parsed) valid
        refine ⟨[], 28, .reject fun value denotes => valid ((decimalLine_iff line value).mp denotes).1,
          [], ?_, .nil⟩
        simp [StreamFold.Model.foldOutcome, lineKernel, rejected]

end Demos.RunningSum
