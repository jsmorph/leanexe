/* The loop measures of FPRoundBase__1 from termination_measures.sail, where only the Rocq
   target reads them, for the Lean target: the back end then writes the loops with whileFuelM. */

termination_measure FPRoundBase__1
  while RoundUp(Real(1) / mantissa),
  while RoundUp(mantissa)
