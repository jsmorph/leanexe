import LeanExe.Float32
import Interpreter.Wasm.IEEE32
import Mathlib.Tactic

namespace Project.ProofKit.F32Source

def add (left right : UInt32) : UInt32 :=
  (Float32.Model.add (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def sub (left right : UInt32) : UInt32 :=
  (Float32.Model.sub (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def mul (left right : UInt32) : UInt32 :=
  (Float32.Model.mul (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def div (left right : UInt32) : UInt32 :=
  (Float32.Model.div (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def sqrt (value : UInt32) : UInt32 :=
  (Float32.Model.sqrt (Float32.Model.ofBits value)).toBits

theorem add_source (left right : UInt32) : LeanExe.Float32.addBits left right = add left right := rfl
theorem sub_source (left right : UInt32) : LeanExe.Float32.subBits left right = sub left right := rfl
theorem mul_source (left right : UInt32) : LeanExe.Float32.mulBits left right = mul left right := rfl
theorem div_source (left right : UInt32) : LeanExe.Float32.divBits left right = div left right := rfl
theorem sqrt_source (value : UInt32) : LeanExe.Float32.sqrtBits value = sqrt value := rfl

#print axioms add_source
#print axioms sub_source
#print axioms mul_source
#print axioms div_source
#print axioms sqrt_source

end Project.ProofKit.F32Source
