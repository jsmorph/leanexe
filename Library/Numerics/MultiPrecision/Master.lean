import Library.Numerics.MultiPrecision.Compiled
import Verified.Master

/-! The master theorems of multiple-precision arithmetic.  A number is an array of digits in base
`2 ^ 32`, least significant first: `value u` is its value, `digits n x` is the array of the `n`
least significant digits of `x`, and `Digits u` states that every word of `u` is below `2 ^ 32`,
as `Library.Numerics.MultiPrecision.Spec` defines them. -/

namespace Library.Numerics.MultiPrecision

/-- The export `add`, called on two arrays of digits `u` and `v`, returns the `k + 1` least
significant digits of `value u + value v`, where `k` is the larger length. -/
theorem add_master :
    Verified.Master compiled.module compiled.tables "add" compiled.add.bound
      (fun x : Array UInt64 × Array UInt64 => Digits x.1 ∧ Digits x.2)
      (fun x (y : Array UInt64) =>
        y = digits (max x.1.size x.2.size + 1) (value x.1 + value x.2)) :=
  .of_trapFree (.ofA compiled.add.trapFree) nofun add_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      add_eq x.1 x.2 hu hv h1.values.size_lt h2.values.size_lt

#print axioms add_master

/-- The export `sub`, called on two arrays of digits `u` and `v`, returns the `k` least
significant digits of `value u + 2 ^ (32 k) - value v`, where `k` is the larger length. -/
theorem sub_master :
    Verified.Master compiled.module compiled.tables "sub" compiled.sub.bound
      (fun x : Array UInt64 × Array UInt64 => Digits x.1 ∧ Digits x.2)
      (fun x (y : Array UInt64) =>
        y = digits (max x.1.size x.2.size)
          (value x.1 + (2 ^ 32) ^ max x.1.size x.2.size - value x.2)) :=
  .of_trapFree (.ofA compiled.sub.trapFree) nofun sub_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ ⟨hu, hv⟩ =>
      sub_eq x.1 x.2 hu hv h1.values.size_lt h2.values.size_lt

#print axioms sub_master

/-- The export `mul`, called on arrays of digits `u` and `v` whose lengths sum to less than
`2 ^ 64`, returns the `u.size + v.size` digits of `value u * value v`. -/
theorem mul_master :
    Verified.Master compiled.module compiled.tables "mul" compiled.mul.bound
      (fun x : Array UInt64 × Array UInt64 =>
        Digits x.1 ∧ Digits x.2 ∧ x.1.size + x.2.size < 2 ^ 64)
      (fun x (y : Array UInt64) => y = digits (x.1.size + x.2.size) (value x.1 * value x.2)) :=
  .of_trapFree (.ofA compiled.mul.trapFree) nofun mul_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hu, hv, hs⟩ => mul_eq x.1 x.2 hu hv hs

#print axioms mul_master

/-- The export `divide`, called on arrays of digits `u` and `v` whose lengths sum to less than
`2 ^ 62`, returns the `u.size` least significant digits of `value u / value v` followed by the
`v.size` least significant digits of `value u % value v`. -/
theorem divide_master :
    Verified.Master compiled.module compiled.tables "divide" compiled.divide.bound
      (fun x : Array UInt64 × Array UInt64 =>
        Digits x.1 ∧ Digits x.2 ∧ x.1.size + x.2.size < 2 ^ 62)
      (fun x (y : Array UInt64) => y =
        digits x.1.size (value x.1 / value x.2) ++ digits x.2.size (value x.1 % value x.2)) :=
  .of_trapFree (.ofA compiled.divide.trapFree) nofun divide_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hu, hv, hs⟩ => divide_eq x.1 x.2 hu hv hs

#print axioms divide_master

end Library.Numerics.MultiPrecision
