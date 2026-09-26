import Project.RunningSum.Parse

namespace Project.RunningSum

open LeanExe.Examples.RunningSum (Decimal render)

def DecimalOutput (value : Int) (bytes : ByteArray) : Prop :=
  (value = 0 ∧ bytes = "0\n".toUTF8) ∨
  ∃ digits, Canonical digits ∧ 0 < digits.size ∧
    ((value = (magnitude digits : Int) ∧ bytes = digits.push 10) ∨
     (value = -(magnitude digits : Int) ∧ bytes = ("-".toUTF8 ++ digits).push 10))

theorem magnitude_empty : magnitude ByteArray.empty = 0 := rfl

theorem magnitude_positive (bytes : ByteArray) (h : Canonical bytes) (hn : 0 < bytes.size) :
    0 < magnitude bytes := by
  have := magnitude_ge_pow bytes h hn
  have hp : 0 < 10 ^ (bytes.size - 1) := by positivity
  omega

theorem render_correct (value : Decimal) (h : Canonical value.digits) :
    DecimalOutput (integer value) (render value) := by
  by_cases hs : value.digits.size = 0
  · have he : value.digits = ByteArray.empty := ByteArray.size_eq_zero_iff.mp hs
    left
    simp [render, integer, he, magnitude_empty]
  · right
    refine ⟨value.digits, h, by omega, ?_⟩
    cases hn : value.negative
    · left
      simp [render, hs, integer, hn]
    · right
      simp [render, hs, integer, hn]

theorem line_add_correct (total : Decimal) (ht : Canonical total.digits)
    (input : ByteArray) (hi : ValidLine input) :
    ∃ value, LeanExe.Examples.RunningSum.parse input = some value ∧
      Canonical (LeanExe.Examples.RunningSum.add total value).digits ∧
      integer (LeanExe.Examples.RunningSum.add total value) = integer total + lineInteger input ∧
      DecimalOutput (integer total + lineInteger input)
        (render (LeanExe.Examples.RunningSum.add total value)) := by
  obtain ⟨value, hp, hc, hv⟩ := parse_valid input hi
  obtain ⟨hnext, hsum⟩ := add_correct total value ht hc
  rw [hv] at hsum
  refine ⟨value, hp, hnext, hsum, ?_⟩
  rw [← hsum]
  exact render_correct _ hnext

#print axioms render_correct
#print axioms line_add_correct

end Project.RunningSum
