import Library.Numerics.Decimal.PrintFloat.PrintFloatBytes
import Verified.Master

namespace Library.Numerics.Decimal.PrintFloat

open Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvRound

/-- The export `print64`, called on a binary64 word `w`, returns the bytes `s`, one to a word, of
a number `n` of the general grammar with `round64 n = canon64 w`; for finite `w`, `s` is also a
number of RFC 8259's grammar, and for finite nonzero `w` it is the scientific layout of a
`Shortest64` decimal `t · 10 ^ k` with no trailing zero. -/
theorem print64_master :
    Verified.Master compiled.module compiled.tables "print64" compiled.print64.bound
      (fun _ => True)
      (fun (w : UInt64) (y : Array UInt64) =>
        ∃ s n, y = (s.map UInt8.toUInt64).toArray ∧ Derives true s n ∧ round64 n = canon64 w ∧
          (Wasm.IEEE64.isFinite w = true → Derives false s n) ∧
          (Wasm.IEEE64.isFinite w = true → Wasm.IEEE64.scaledMagnitude w ≠ 0 →
            ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧ s = sciLayout neg t k)) :=
  .of_trapFree (.ofA compiled.print64.trapFree) nofun PrintFloatBytes.print64_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ w _ _ => by
      obtain ⟨s, n, h1, h2, h3, h4, -, h6⟩ := PrintFloatTheorem.derives64 false w
      exact ⟨s, n, h1, h2, h4, h3, h6⟩

/-- The export `print64Ecma`, called on a binary64 word `w`, returns the bytes `s`, one to a word,
of a number `n` of the general grammar with `round64 n = canon64 w`; for finite `w`, `s` is also
a number of RFC 8259's grammar, and for finite nonzero `w` it is the layout of ECMA-262's
Number::toString of a `Shortest64` decimal `t · 10 ^ k` with no trailing zero. -/
theorem print64Ecma_master :
    Verified.Master compiled.module compiled.tables "print64Ecma" compiled.print64Ecma.bound
      (fun _ => True)
      (fun (w : UInt64) (y : Array UInt64) =>
        ∃ s n, y = (s.map UInt8.toUInt64).toArray ∧ Derives true s n ∧ round64 n = canon64 w ∧
          (Wasm.IEEE64.isFinite w = true → Derives false s n) ∧
          (Wasm.IEEE64.isFinite w = true → Wasm.IEEE64.scaledMagnitude w ≠ 0 →
            ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧ s = ecmaLayout neg t k)) :=
  .of_trapFree (.ofA compiled.print64Ecma.trapFree) nofun PrintFloatBytes.print64Ecma_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ w _ _ => by
      obtain ⟨s, n, h1, h2, h3, h4, -, h6⟩ := PrintFloatTheorem.derives64 true w
      exact ⟨s, n, h1, h2, h4, h3, h6⟩

/-- The export `print32`, called on a word `w`, returns the bytes `s`, one to a word, of a number
`n` of the general grammar with `round32 n = canon32 w.toUInt32` for the binary32 pattern in the
low 32 bits of `w`; for a finite pattern, `s` is also a number of RFC 8259's grammar, and for a
finite nonzero pattern it is the scientific layout of a `Shortest32` decimal `t · 10 ^ k` with no
trailing zero. -/
theorem print32_master :
    Verified.Master compiled.module compiled.tables "print32" compiled.print32.bound
      (fun _ => True)
      (fun (w : UInt64) (y : Array UInt64) =>
        ∃ s n, y = (s.map UInt8.toUInt64).toArray ∧ Derives true s n ∧
          round32 n = canon32 w.toUInt32 ∧
          (Wasm.IEEE32.isFinite w.toUInt32 = true → Derives false s n) ∧
          (Wasm.IEEE32.isFinite w.toUInt32 = true → Wasm.IEEE32.scaledMagnitude w.toUInt32 ≠ 0 →
            ∃ neg t k, t % 10 ≠ 0 ∧ Shortest32 w.toUInt32 neg t k ∧ s = sciLayout neg t k)) :=
  .of_trapFree (.ofA compiled.print32.trapFree) nofun PrintFloatBytes.print32_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ w _ _ => by
      obtain ⟨s, n, h1, h2, h3, h4, -, h6⟩ := PrintFloatTheorem.derives32 false w.toUInt32
      exact ⟨s, n, (PrintFloatWord32.print32_low w).trans h1, h2, h4, h3, h6⟩

/-- The export `print32Ecma`, called on a word `w`, returns the bytes `s`, one to a word, of a
number `n` of the general grammar with `round32 n = canon32 w.toUInt32` for the binary32 pattern
in the low 32 bits of `w`; for a finite pattern, `s` is also a number of RFC 8259's grammar, and
for a finite nonzero pattern it is the layout of ECMA-262's Number::toString of a `Shortest32`
decimal `t · 10 ^ k` with no trailing zero. -/
theorem print32Ecma_master :
    Verified.Master compiled.module compiled.tables "print32Ecma" compiled.print32Ecma.bound
      (fun _ => True)
      (fun (w : UInt64) (y : Array UInt64) =>
        ∃ s n, y = (s.map UInt8.toUInt64).toArray ∧ Derives true s n ∧
          round32 n = canon32 w.toUInt32 ∧
          (Wasm.IEEE32.isFinite w.toUInt32 = true → Derives false s n) ∧
          (Wasm.IEEE32.isFinite w.toUInt32 = true → Wasm.IEEE32.scaledMagnitude w.toUInt32 ≠ 0 →
            ∃ neg t k, t % 10 ≠ 0 ∧ Shortest32 w.toUInt32 neg t k ∧ s = ecmaLayout neg t k)) :=
  .of_trapFree (.ofA compiled.print32Ecma.trapFree) nofun PrintFloatBytes.print32Ecma_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ w _ _ => by
      obtain ⟨s, n, h1, h2, h3, h4, -, h6⟩ := PrintFloatTheorem.derives32 true w.toUInt32
      exact ⟨s, n, (PrintFloatWord32.print32Ecma_low w).trans h1, h2, h4, h3, h6⟩

#print axioms print64_master
#print axioms print64Ecma_master
#print axioms print32_master
#print axioms print32Ecma_master

end Library.Numerics.Decimal.PrintFloat
