import Project.EncodingGcd.Program
import Project.Common

namespace Project.EncodingGcd

open Wasm

def frame
    (a b l2 l3 x y l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 : UInt64) :
    Locals :=
  { params := [.i64 a, .i64 b]
    locals := [.i64 l2, .i64 l3, .i64 x, .i64 y, .i64 l6, .i64 l7,
      .i64 l8, .i64 l9, .i64 l10, .i64 l11, .i64 l12, .i64 l13,
      .i64 l14, .i64 l15, .i64 l16, .i64 l17, .i64 l18, .i64 l19,
      .i64 l20, .i64 l21, .i64 l22]
    values := [] }

def loopInvariant (initial : Store Unit) (a b : UInt64) : AssertionF Unit :=
  fun st s =>
    st = initial ∧
    ∃ l2 l3 x y l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22,
      s = frame a b l2 l3 x y l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 ∧
      Nat.gcd x.toNat y.toNat = Nat.gcd a.toNat b.toNat

def measure (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals with
  | _ :: _ :: _ :: .i64 y :: _ => y.toNat
  | _ => 0

theorem gcd_zero_value {a b x : UInt64}
    (h : x.toNat = Nat.gcd a.toNat b.toNat) :
    x = UInt64.ofNat (Nat.gcd a.toNat b.toNat) := by
  calc
    x = UInt64.ofNat x.toNat := UInt64.ofNat_toNat.symm
    _ = UInt64.ofNat (Nat.gcd a.toNat b.toNat) := by rw [h]

theorem gcd_step (x y : UInt64) :
    Nat.gcd y.toNat (x % y).toNat = Nat.gcd x.toNat y.toNat := by
  rw [UInt64.toNat_mod]
  calc
    Nat.gcd y.toNat (x.toNat % y.toNat) = Nat.gcd (x.toNat % y.toNat) y.toNat := Nat.gcd_comm _ _
    _ = Nat.gcd y.toNat x.toNat := (Nat.gcd_rec _ _).symm
    _ = Nat.gcd x.toNat y.toNat := Nat.gcd_comm _ _

theorem remainder_lt (x y : UInt64) (nonzero : y ≠ 0) :
    (x % y).toNat < y.toNat := by
  have positive : 0 < y.toNat := Nat.pos_of_ne_zero (by
    intro zero
    apply nonzero
    exact UInt64.toNat_inj.mp (by simpa using zero))
  simpa only [UInt64.toNat_mod] using Nat.mod_lt x.toNat positive

end Project.EncodingGcd
