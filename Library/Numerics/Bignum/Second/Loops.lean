module

public import Library.Numerics.Bignum.NatProof
public import Library.Numerics.Bignum.Second.Program

@[expose] public section

/-!
The new versions of the first iteration's natural functions are equal to them as functions.  A
carry `x / 2^32` is `x >>> 32` and a digit `x % 2^32` is `x &&& 0xFFFFFFFF` for every word, so
rewriting MultiPrecision's Algorithms A, S, and D with `div_two32` and `mod_two32` gives the bodies
of `addS`, `subS`, and `longDivS`, in which a `let` names each word that MultiPrecision computes
twice.  Every theorem of the first iteration about `natAdd`, `natSub`, and `natDivModChecked`
therefore holds for the new versions, and `natAddS_eq`, `natSubS_eq`, and `natDivModCheckedS_eq`
restate the first iteration's equations.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision

theorem div_two32 (x : UInt64) : x / (4294967296 : UInt64) = x >>> 32 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, Library.Numerics.Arithmetic.Uscale.UscaleTheorem.shr32]; rfl

theorem mod_two32 (x : UInt64) : x % 4294967296 = x &&& 0xFFFFFFFF := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, Library.Numerics.Arithmetic.Uscale.UscaleTheorem.and_mask]; rfl

theorem addS_eq_add : addS = add := by
  funext u v
  unfold addS add
  simp only [div_two32, mod_two32]

theorem subS_eq_sub : subS = sub := by
  funext u v
  unfold subS sub
  simp only [div_two32, mod_two32]

theorem longDivS_eq_longDiv : longDivS = longDiv := by
  funext u v t
  unfold longDivS longDiv
  simp only [div_two32, mod_two32]

theorem divideS_eq_divide : divideS = divide := by
  funext u v
  unfold divideS divide
  rw [longDivS_eq_longDiv]

theorem natAddS_eq_natAdd : natAddS = natAdd := by
  funext u v; unfold natAddS natAdd; rw [addS_eq_add]

theorem natSubS_eq_natSub : natSubS = natSub := by
  funext u v; unfold natSubS natSub; rw [subS_eq_sub]

theorem natDivModCheckedS_eq_natDivModChecked : natDivModCheckedS = natDivModChecked := by
  funext u v
  unfold natDivModCheckedS natDivModChecked natDivMod
  rw [divideS_eq_divide]
  split <;> simp_all

theorem natAddS_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) : natAddS u v = limbsOf (value u + value v) := by
  rw [natAddS_eq_natAdd]; exact natAdd_eq hu hv hsu hsv

theorem natSubS_eq {u v : Array UInt64} (hu : Digits u) (hv : Digits v) (hsu : u.size < 2 ^ 32)
    (hsv : v.size < 2 ^ 32) : natSubS u v = natSubSpec (value u) (value v) := by
  rw [natSubS_eq_natSub]; exact natSub_eq hu hv hsu hsv

theorem natDivModCheckedS_eq {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModCheckedS u v = natDivModCheckedSpec (value u) (value v) := by
  rw [natDivModCheckedS_eq_natDivModChecked]; exact natDivModChecked_eq hu hv hsu hsv

end Library.Numerics.Bignum
