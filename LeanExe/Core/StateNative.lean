import LeanExe.Core.Native
import LeanExe.Core.Memory

namespace LeanExe.Core

/-- Ordinary state computations with machine-word arguments and results. -/
def StateNative (σ : Type) : Nat → Type
  | 0 => StateM σ UInt64
  | n + 1 => UInt64 → StateNative σ n

def applyStateNative : {n : Nat} → StateNative σ n → List UInt64 → StateM σ UInt64
  | 0, computation, _ => computation
  | n + 1, function, args =>
    applyStateNative (n := n) (function (args.headD 0)) args.tail

/-- The source result and final state are the ordinary Lean computation's pair. -/
structure StateCertificate {arity : Nat} (effects : Effects σ)
    (function : StateNative σ arity) where
  source : Module
  entry : Nat
  correct : ∀ args, args.length = arity → ∀ initial,
    Invokes source effects entry initial args
      (applyStateNative function args initial).2
      (applyStateNative function args initial).1

theorem Memory.effects.run_read (address : UInt64) (initial : ByteArray) :
    Memory.effects 0 [address] initial
      (Memory.read address initial).1 (Memory.read address initial).2 := .read rfl

theorem Memory.effects.run_write (address value : UInt64) (initial : ByteArray) :
    Memory.effects 1 [address, value] initial
      (Memory.write address value initial).1 (Memory.write address value initial).2 := .write rfl

theorem Memory.effects.run_size (initial : ByteArray) :
    Memory.effects 2 [] initial (Memory.size initial).1 (Memory.size initial).2 := .size rfl

theorem Memory.effects.run_grow (delta : UInt64) (initial : ByteArray) :
    Memory.effects 3 [delta] initial
      (Memory.grow delta initial).1 (Memory.grow delta initial).2 := .grow rfl

end LeanExe.Core
