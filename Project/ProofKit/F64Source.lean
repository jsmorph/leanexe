import LeanExe.Float64
import Interpreter.Wasm.IEEE64
import Mathlib.Tactic

namespace Project.ProofKit.F64Source

def add (left right : UInt64) : UInt64 :=
  (Float.Model.add (Float.Model.ofBits left) (Float.Model.ofBits right)).toBits

def sub (left right : UInt64) : UInt64 :=
  (Float.Model.sub (Float.Model.ofBits left) (Float.Model.ofBits right)).toBits

def mul (left right : UInt64) : UInt64 :=
  (Float.Model.mul (Float.Model.ofBits left) (Float.Model.ofBits right)).toBits

def div (left right : UInt64) : UInt64 :=
  (Float.Model.div (Float.Model.ofBits left) (Float.Model.ofBits right)).toBits

def sqrt (value : UInt64) : UInt64 :=
  (Float.Model.sqrt (Float.Model.ofBits value)).toBits

theorem infinity_eq_encodeFinite (negative : Bool) :
    Wasm.IEEE64.infinity negative = Wasm.IEEE64.encodeFinite negative 0x7FF 0 := by
  cases negative <;> decide

theorem exponent_lt (x : UInt64) : Wasm.IEEE64.exponent x < 2 ^ 11 :=
  Nat.mod_lt _ (by norm_num)

theorem fraction_lt (x : UInt64) : Wasm.IEEE64.fraction x < 2 ^ 52 :=
  Nat.mod_lt _ (by norm_num)

theorem exponent_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.exponent (Wasm.IEEE64.encodeFinite negative e f) = e := by
  cases negative <;>
    simp [Wasm.IEEE64.exponent, Wasm.IEEE64.encodeFinite, UInt64.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem fraction_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.fraction (Wasm.IEEE64.encodeFinite negative e f) = f := by
  cases negative <;>
    simp [Wasm.IEEE64.fraction, Wasm.IEEE64.encodeFinite, UInt64.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem sign_encodeFinite (negative : Bool) (e f : Nat)
    (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite negative e f) = negative := by
  cases negative <;>
    simp [Wasm.IEEE64.sign, Wasm.IEEE64.encodeFinite, UInt64.toNat_ofNat, Nat.mod_eq_of_lt] <;>
    omega

theorem add_source (left right : UInt64) : LeanExe.Float64.addBits left right = add left right := rfl
theorem sub_source (left right : UInt64) : LeanExe.Float64.subBits left right = sub left right := rfl
theorem mul_source (left right : UInt64) : LeanExe.Float64.mulBits left right = mul left right := rfl
theorem div_source (left right : UInt64) : LeanExe.Float64.divBits left right = div left right := rfl
theorem sqrt_source (value : UInt64) : LeanExe.Float64.sqrtBits value = sqrt value := rfl

#print axioms add_source
#print axioms sub_source
#print axioms mul_source
#print axioms div_source
#print axioms sqrt_source

end Project.ProofKit.F64Source
