import Demos.RunningSum.InputBounds

open Lean Elab Command in
elab "check_running_sum_math_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Demos.RunningSum.zero_value,
    ``Demos.RunningSum.Magnitude.lowValue_size,
    ``Demos.RunningSum.Magnitude.add_digit,
    ``Demos.RunningSum.Magnitude.sub_digit,
    ``Demos.RunningSum.magnitudeLess_correct,
    ``Demos.RunningSum.combine_add,
    ``Demos.RunningSum.combine_sub,
    ``Demos.RunningSum.add_correct,
    ``Demos.RunningSum.add_fits,
    ``Demos.RunningSum.decimalLine_iff,
    ``Demos.RunningSum.parse_correct,
    ``Demos.RunningSum.parse_decimalLine,
    ``Demos.RunningSum.parse_zero_sign,
    ``Demos.RunningSum.validLine_noLF,
    ``Demos.RunningSum.normal_natDigits,
    ``Demos.RunningSum.render_correct,
    ``Demos.RunningSum.render_zero,
    ``Demos.RunningSum.decimalOutput_unique,
    ``Demos.RunningSum.StreamModel.consume_correct,
    ``Demos.RunningSum.StreamModel.consumeChunks_eq,
    ``Demos.RunningSum.StreamModel.stream_correct,
    ``Demos.RunningSum.StreamModel.safe_append_iff,
    ``Demos.RunningSum.StreamModel.validInput_safe_and_finalRoom,
    ``Demos.RunningSum.StreamModel.stream_correct_of_inputBounds]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Running sum mathematics axiom check passed for {declarations.size} theorems"

check_running_sum_math_axioms
