import Library.Numerics.Decimal.Int64Text.Compiled
import Verified.Master

namespace Library.Numerics.Decimal.Int64Text

/-- The export `printInt64`, called on an `Int64` `x`, returns the array of the bytes of Lean's
decimal text `toString x`, one byte to a word. -/
theorem printInt64_master :
    Verified.Master compiled.module compiled.tables "printInt64" compiled.printInt64.bound
      (fun _ => True)
      (fun (x : Int64) (y : Array UInt64) =>
        y = (((toString x).toList.map Char.toUInt8).map UInt8.toUInt64).toArray) :=
  .of_trapFree (.ofA compiled.printInt64.trapFree) nofun printInt64_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => printInt64_eq x

/-- The export `readInt64`, called on an array of words `s`, returns `(true, v)` exactly when `s`
holds the bytes of Lean's decimal text `toString v` of an `Int64` `v`, one byte to a word, and
`(false, 0)` when `s` is the text of no `Int64`. -/
theorem readInt64_master :
    Verified.Master compiled.module compiled.tables "readInt64" compiled.readInt64.bound
      (fun _ => True)
      (fun (s : Array UInt64) (y : Bool × Int64) =>
        (∀ v : Int64,
          y = (true, v) ↔ s = (((toString v).toList.map Char.toUInt8).map UInt8.toUInt64).toArray) ∧
        ((∀ v : Int64,
            s ≠ (((toString v).toList.map Char.toUInt8).map UInt8.toUInt64).toArray) →
          y = (false, 0))) :=
  .of_trapFree (.ofA compiled.readInt64.trapFree) nofun readInt64_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ s ⟨_, _, hs⟩ _ => by
      rw [readInt64_eq s hs.values.size_lt]
      exact ⟨fun v => (expectedRead_eq_true_iff s v).trans eq_comm,
        fun h => expectedRead_reject s fun v hv => h v hv.symm⟩

#print axioms printInt64_master
#print axioms readInt64_master

end Library.Numerics.Decimal.Int64Text
