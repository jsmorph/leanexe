import Project.Validate.Program
import Project.Common
import LeanExe.Examples.AsciiDigits
import Interpreter.Wasm.Wp.Tactic

/-!
# Loop invariant for `validateGeneric`

The frame, invariant, and measure for the `func2` fuel loop, with the two
list lemmas that turn a scanned prefix or a witness byte into the final
`all` value.
-/

namespace Project.Validate.Spec

open Wasm
open Project.Common
open LeanExe.Examples.AsciiDigits

def vFrame
    (fuel owner ptr len index l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15
      l16 l17 l18 l19 l20 l21 l22 l23 : UInt64) : Locals :=
  { params := [.i64 fuel, .i64 owner, .i64 ptr, .i64 len, .i64 index],
    locals := [.i64 l5, .i64 l6, .i64 l7, .i64 l8, .i64 l9, .i64 l10, .i64 l11,
      .i64 l12, .i64 l13, .i64 l14, .i64 l15, .i64 l16, .i64 l17, .i64 l18,
      .i64 l19, .i64 l20, .i64 l21, .i64 l22, .i64 l23],
    values := [] }

/-- Loop invariant: either the scan is still running at position `i` with every
byte below `i` a digit, or the done flag is set and the result local holds the
final answer. -/
def vInv (st0 : Store Unit) (owner ptr : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    st = st0 ∧
    ∃ (fuel index l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19
        l20 l21 l22 l23 : UInt64),
      s = vFrame fuel owner ptr (UInt64.ofNat bytes.length) index l5 l6 l7 l8 l9
        l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 ∧
      ((l6 = 0 ∧ ∃ i : Nat, i ≤ bytes.length ∧ index = UInt64.ofNat i ∧
          fuel = UInt64.ofNat (bytes.length + 1 - i) ∧
          ∀ j : Nat, j < i → isAsciiDigit bytes[j]! = true) ∨
        (l6 = 1 ∧ l5 = validateExpected bytes))

def vMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.params, s.locals with
  | .i64 fuel :: _, _ :: .i64 l6 :: _ =>
      2 * fuel.toNat + (if l6 = 0 then 1 else 0)
  | _, _ => 0

theorem all_of_prefix {bytes : List UInt8}
    (h : ∀ j : Nat, j < bytes.length → isAsciiDigit bytes[j]! = true) :
    bytes.all isAsciiDigit = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have := h j hj
  rwa [getBang_eq hj] at this

theorem not_all_of_witness {bytes : List UInt8} {i : Nat}
    (hi : i < bytes.length) (h : isAsciiDigit bytes[i]! = false) :
    bytes.all isAsciiDigit = false := by
  rw [getBang_eq hi] at h
  cases hval : bytes.all isAsciiDigit
  · rfl
  · have := List.all_eq_true.mp hval (bytes[i]'hi) (List.getElem_mem hi)
    rw [h] at this
    exact Bool.noConfusion this

end Project.Validate.Spec
