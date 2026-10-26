import Demos.RunningSum.Addition
import Demos.RunningSum.Parsing
import Demos.RunningSum.Rendering
import Demos.RunningSum.StreamView

namespace Demos.RunningSum

open LeanExe

theorem render_size_bound (number : Decimal) : (render number).data.size < UInt64.size := by
  unfold render
  split
  · decide
  · rw [Bytes.data_size_build]
    exact UInt64.toNat_lt_size _

theorem kernel_accepted {total : Decimal} {line : Array UInt64} (normal : total.Valid)
    (room : max total.digits.size line.size + 3 < UInt64.size)
    (accepted : (parse line).valid = true) :
    (add total (parse line).value).Valid ∧ (add total (parse line).value).Fits ∧
      (add total (parse line).value).value = total.value + lineInteger line := by
  have lineBound : line.size < UInt64.size := by omega
  have parsedNormal := parse_valid line lineBound accepted
  have parsedSize := parse_digits_size_le line lineBound
  have addBound : max total.digits.size (parse line).value.digits.size + 3 < UInt64.size := by
    omega
  obtain ⟨sumNormal, sumFits, sumValue, _⟩ :=
    add_correct total (parse line).value normal parsedNormal addBound
  exact ⟨sumNormal, sumFits, by rw [sumValue, parse_value line lineBound]⟩

def kernelSpec : StreamFold.KernelSpec lineKernel where
  Good := fun total => total.Valid
  Room := fun total line => max total.digits.size line.size + 3 < UInt64.size
  lineFits := fun room => by omega
  accepted := fun normal room valid =>
    ⟨(kernel_accepted normal room valid).1,
      render_nonempty _ (kernel_accepted normal room valid).2.1⟩
  outputBound := fun _ _ _ => render_size_bound _

end Demos.RunningSum
