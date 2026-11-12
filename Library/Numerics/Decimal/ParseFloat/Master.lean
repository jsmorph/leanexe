import Library.Numerics.Decimal.ParseFloat.ParseFloatBytes
import Verified.Master

namespace Library.Numerics.Decimal.ParseFloat

open Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvRound

/-- The export `parse64`, called on the flag `general` of the general grammar and an array that
holds the bytes `s` one to a word, returns `(true, round64 n)`, the binary64 word of
roundTiesToEven applied to `n`, when `s` is a number `n` of the grammar, and `(false, 0)` when
`s` is no number of the grammar. -/
theorem parse64_master :
    Verified.Master compiled.module compiled.tables "parse64" compiled.parse64.bound
      (fun _ => True)
      (fun (x : Bool × Array UInt64) (y : Bool × UInt64) =>
        ∀ s : List UInt8, (s.map UInt8.toUInt64).toArray = x.2 →
          (∀ n, Derives x.1 s n → y = (true, round64 n)) ∧
          ((∀ n, ¬ Derives x.1 s n) → y = (false, 0))) :=
  .of_trapFree (.ofA compiled.parse64.trapFree) nofun ParseFloatBytes.parse64_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ ⟨general, ws⟩ ⟨_, _, _, _, _, _, hb⟩ _ s hs => by
      obtain rfl : (s.map UInt8.toUInt64).toArray = ws := hs
      have hlen : s.length < 2 ^ 32 := by
        have := hb.values.size_lt_memory32
        rw [List.size_toArray, List.length_map] at this
        omega
      exact ⟨fun n hn => ParseFloatTheorem.parse64_accept general s n hlen hn,
        ParseFloatTheorem.parse64_reject general s hlen⟩

/-- The export `parse32`, called on the flag `general` of the general grammar and an array that
holds the bytes `s` one to a word, returns `(true, w)`, with the binary32 pattern `round32 n` of
roundTiesToEven applied to `n` in the low 32 bits of `w`, when `s` is a number `n` of the
grammar, and `(false, 0)` when `s` is no number of the grammar. -/
theorem parse32_master :
    Verified.Master compiled.module compiled.tables "parse32" compiled.parse32.bound
      (fun _ => True)
      (fun (x : Bool × Array UInt64) (y : Bool × UInt64) =>
        ∀ s : List UInt8, (s.map UInt8.toUInt64).toArray = x.2 →
          (∀ n, Derives x.1 s n → y = (true, (round32 n).toUInt64)) ∧
          ((∀ n, ¬ Derives x.1 s n) → y = (false, 0))) :=
  .of_trapFree (.ofA compiled.parse32.trapFree) nofun ParseFloatBytes.parse32_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ ⟨general, ws⟩ ⟨_, _, _, _, _, _, hb⟩ _ s hs => by
      obtain rfl : (s.map UInt8.toUInt64).toArray = ws := hs
      have hlen : s.length < 2 ^ 32 := by
        have := hb.values.size_lt_memory32
        rw [List.size_toArray, List.length_map] at this
        omega
      exact ⟨fun n hn => ParseFloatTheorem.parse32_accept general s n hlen hn,
        ParseFloatTheorem.parse32_reject general s hlen⟩

#print axioms parse64_master
#print axioms parse32_master

end Library.Numerics.Decimal.ParseFloat
