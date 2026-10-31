# Limiters

[Minmod](Minmod/Program.lean) selects the input with smaller word magnitude when both sign bits
agree, and returns zero when they differ.  [Its compilation](Minmod/Compiled.lean) has the
verified compiler's execution theorems.  [The real theory](Minmod/Real.lean) proves magnitude, symmetry, sign reversal, slope, and reconstructed
face properties.  [The binary64 proof](Minmod/Proof.lean) connects the word implementation to real
minmod through `CodeLib.IEEE64.value`.  The [Euler reconstruction analysis](../../../Demos/Euler/ReconstructionAccuracy.lean)
uses these results to bound differences and reconstructed faces for the solver's rounded inputs.
