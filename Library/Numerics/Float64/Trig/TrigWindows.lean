import Library.Numerics.Float64.Trig.TrigPi

/-!
The three windows that `Trig.remLarge` reads from `Trig.invPi`.  For each exponent field `E` of
the Payne–Hanek range, `g = E - 1013` is the position of the window in the 1280-bit table, and
the three words read at word `g / 64` and bit `g % 64` are the 192 bits of the table from bit `g`
on.  The kernel checks every `E` from 1043 to 2046.
-/

namespace Library.Numerics.Float64.Trig.TrigWindows

open TrigPi

set_option exponentiation.threshold 4096

theorem windows_eq : ∀ E : Nat, E < 2047 → 1043 ≤ E →
    (Trig.window Trig.invPi ((UInt64.ofNat E - 1013) >>> 6)
        ((UInt64.ofNat E - 1013) &&& 63)).toNat * 2 ^ 128 +
      (Trig.window Trig.invPi ((UInt64.ofNat E - 1013) >>> 6 + 1)
        ((UInt64.ofNat E - 1013) &&& 63)).toNat * 2 ^ 64 +
      (Trig.window Trig.invPi ((UInt64.ofNat E - 1013) >>> 6 + 2)
        ((UInt64.ofNat E - 1013) &&& 63)).toNat =
    tableNum * 2 ^ (E - 1013) / 2 ^ 1088 % 2 ^ 192 := by
  decide +kernel

#print axioms windows_eq

end Library.Numerics.Float64.Trig.TrigWindows
