module

public import Demos.BignumCalc.MessageCompiled
public import Library.Numerics.Bignum.Export

@[expose] public section

/-!
# The bounds of the library's functions in the calculator's module

The calculator's module `messageCompiled` compiles the library's functions again, and the verified
compiler generates their allocation bounds again, in terms of the bounds of the same module's
callees.  Each bound equals the bound of the same function in `compiled`: `rfl` is out of reach of
the elaborator's budget, so each equation rewrites both generated equations `bound_eq` and the
callees' equations, from the leaves up.  The closed forms of `Bound.lean` and `Export.lean` then
hold in the calculator's module.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

theorem m_add_bound : messageCompiled.add.bound = compiled.add.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.add.bound_eq a b, compiled.add.bound_eq a b]

theorem m_sub_bound : messageCompiled.sub.bound = compiled.sub.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.sub.bound_eq a b, compiled.sub.bound_eq a b]

theorem m_mul_bound : messageCompiled.mul.bound = compiled.mul.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.mul.bound_eq a b, compiled.mul.bound_eq a b]

theorem m_mulSmall_bound : messageCompiled.mulSmall.bound = compiled.mulSmall.bound := by
  funext x
  obtain ⟨a, b, c⟩ := x
  rw [messageCompiled.mulSmall.bound_eq a b c, compiled.mulSmall.bound_eq a b c]

theorem m_shortDiv_bound : messageCompiled.shortDiv.bound = compiled.shortDiv.bound := by
  funext x
  obtain ⟨a, b, c⟩ := x
  rw [messageCompiled.shortDiv.bound_eq a b c, compiled.shortDiv.bound_eq a b c]

theorem m_longDiv_bound : messageCompiled.longDiv.bound = compiled.longDiv.bound := by
  funext x
  obtain ⟨a, b, c⟩ := x
  rw [messageCompiled.longDiv.bound_eq a b c, compiled.longDiv.bound_eq a b c, m_mulSmall_bound, m_shortDiv_bound]

theorem m_divide_bound : messageCompiled.divide.bound = compiled.divide.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.divide.bound_eq a b, compiled.divide.bound_eq a b, m_shortDiv_bound, m_longDiv_bound]

theorem m_natTrim_bound : messageCompiled.natTrim.bound = compiled.natTrim.bound := by
  funext x
  rw [messageCompiled.natTrim.bound_eq x, compiled.natTrim.bound_eq x]

theorem m_natAdd_bound : messageCompiled.natAdd.bound = compiled.natAdd.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.natAdd.bound_eq a b, compiled.natAdd.bound_eq a b, m_add_bound, m_natTrim_bound]

theorem m_natSub_bound : messageCompiled.natSub.bound = compiled.natSub.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.natSub.bound_eq a b, compiled.natSub.bound_eq a b, m_sub_bound, m_natTrim_bound]

theorem m_natMul_bound : messageCompiled.natMul.bound = compiled.natMul.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.natMul.bound_eq a b, compiled.natMul.bound_eq a b, m_mul_bound, m_natTrim_bound]

theorem m_intNeg_bound : messageCompiled.intNeg.bound = compiled.intNeg.bound := by
  funext x
  rw [messageCompiled.intNeg.bound_eq x, compiled.intNeg.bound_eq x, m_natTrim_bound]

theorem m_intAdd_bound : messageCompiled.intAdd.bound = compiled.intAdd.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.intAdd.bound_eq a b, compiled.intAdd.bound_eq a b, m_natAdd_bound, m_natSub_bound]

theorem m_intSub_bound : messageCompiled.intSub.bound = compiled.intSub.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.intSub.bound_eq a b, compiled.intSub.bound_eq a b, m_natAdd_bound, m_natSub_bound]

theorem m_intMul_bound : messageCompiled.intMul.bound = compiled.intMul.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.intMul.bound_eq a b, compiled.intMul.bound_eq a b, m_natMul_bound]

theorem m_intToText_bound : messageCompiled.intToText.bound = compiled.intToText.bound := by
  funext x
  rw [messageCompiled.intToText.bound_eq x, compiled.intToText.bound_eq x]

theorem m_intOfText_bound : messageCompiled.intOfText.bound = compiled.intOfText.bound := by
  funext x
  rw [messageCompiled.intOfText.bound_eq x, compiled.intOfText.bound_eq x, m_natTrim_bound]

theorem m_textNeg_bound : messageCompiled.textNeg.bound = compiled.textNeg.bound := by
  funext x
  rw [messageCompiled.textNeg.bound_eq x, compiled.textNeg.bound_eq x, m_intOfText_bound, m_intNeg_bound, m_intToText_bound]

theorem m_textCmp_bound : messageCompiled.textCmp.bound = compiled.textCmp.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textCmp.bound_eq a b, compiled.textCmp.bound_eq a b, m_intOfText_bound]

theorem m_textAdd_bound : messageCompiled.textAdd.bound = compiled.textAdd.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textAdd.bound_eq a b, compiled.textAdd.bound_eq a b, m_intOfText_bound, m_intAdd_bound, m_intToText_bound]

theorem m_textSub_bound : messageCompiled.textSub.bound = compiled.textSub.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textSub.bound_eq a b, compiled.textSub.bound_eq a b, m_intOfText_bound, m_intSub_bound, m_intToText_bound]

theorem m_textMul_bound : messageCompiled.textMul.bound = compiled.textMul.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textMul.bound_eq a b, compiled.textMul.bound_eq a b, m_intOfText_bound, m_intMul_bound, m_intToText_bound]

theorem m_textTDiv_bound : messageCompiled.textTDiv.bound = compiled.textTDiv.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textTDiv.bound_eq a b, compiled.textTDiv.bound_eq a b, m_intOfText_bound, m_natTrim_bound, m_divide_bound, m_intToText_bound]

theorem m_textTMod_bound : messageCompiled.textTMod.bound = compiled.textTMod.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textTMod.bound_eq a b, compiled.textTMod.bound_eq a b, m_intOfText_bound, m_natTrim_bound, m_divide_bound, m_intToText_bound]

theorem m_textEDiv_bound : messageCompiled.textEDiv.bound = compiled.textEDiv.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textEDiv.bound_eq a b, compiled.textEDiv.bound_eq a b, m_intOfText_bound, m_natTrim_bound, m_divide_bound, m_natAdd_bound, m_natSub_bound, m_intToText_bound]

theorem m_textEMod_bound : messageCompiled.textEMod.bound = compiled.textEMod.bound := by
  funext x
  obtain ⟨a, b⟩ := x
  rw [messageCompiled.textEMod.bound_eq a b, compiled.textEMod.bound_eq a b, m_intOfText_bound, m_natTrim_bound, m_divide_bound, m_natAdd_bound, m_natSub_bound, m_intToText_bound]

end Demos.BignumCalc
