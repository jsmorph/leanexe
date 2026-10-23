import Library.Hashing.Sha2.Impl.SHA256
import Library.Hashing.Sha2.Spec.HashAlgorithms

/-!
# Lifting impl `UInt32` containers to spec `BitVec 32` containers

The implementation uses sized vectors of `UInt32` for the working state
(`Impl.State = Vector UInt32 8`) and message block (`Impl.Block =
Vector UInt32 16`).  The spec, in the SHA-256 namespace, uses
`Vector (BitVec 32) 8` and `Vector (BitVec 32) 16` (under the
`HashValue` and `Block` notations from `spec/Functions.lean`).

This file defines the lifting maps `toSpecState` / `toSpecBlock` and
proves the size and indexing facts the equivalence proof relies on.
The three lemmas are all `@[simp]` so that downstream `simp` calls can
freely commute lifting with size queries and indexing.
-/

open scoped SHS.SHA256

open SHS.SHA256

namespace SHS.Equiv.SHA256.Lift

/-! ## Lifting maps -/

/-- Lift the implementation's working state (eight `UInt32`s) to the
spec's `HashValue` (a `Vector` of eight `BitVec 32`s). -/
def toSpecState (s : Impl.State) : HashValue :=
  s.map UInt32.toBitVec

/-- Lift the implementation's message block (sixteen `UInt32`s) to the
spec's `Block` (a `Vector` of sixteen `BitVec 32`s). -/
def toSpecBlock (b : Impl.Block) : Block :=
  b.map UInt32.toBitVec

/-! ## Indexing simp lemmas

Bridge spec-side indexing on a lifted container to the implementation's
bounds-checked `_[i]` access.  Phrased over `Fin n` so the bound is
automatic. -/

@[simp] theorem getElem!_toSpecState (s : Impl.State) (i : Fin 8) :
    (toSpecState s)[i.val]! = s[i].toBitVec := by
  simp [toSpecState, getElem!_pos]

@[simp] theorem getElem!_toSpecBlock (b : Impl.Block) (i : Fin 16) :
    (toSpecBlock b)[i.val]! = b[i].toBitVec := by
  simp [toSpecBlock, getElem!_pos]

/-! ## Initial-state bridge -/

/-- The impl's initial hash value `H256_256` lifts to the spec's `H0_256`.
    Eight literal `UInt32` / `BitVec 32` constants, pointwise; we enumerate
    the indices rather than calling `native_decide` (which would inflate the
    trust base with `Lean.ofReduceBool`/`trustCompiler`). -/
@[simp] theorem toSpecState_H256_256 :
    toSpecState Impl.H256_256 = SHS.SHA256.H0_256 := by
  apply Vector.ext; intro i hi
  unfold toSpecState Impl.H256_256 SHS.SHA256.H0_256
  rw [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- The impl's SHA-224 IV `H256_224` lifts to the spec's `H0_224`.
    Same eight-index enumeration shape as `toSpecState_H256_256`; the
    impl's `UInt32` literals and the spec's `BitVec 32` literals match
    pointwise via `rfl`. -/
@[simp] theorem toSpecState_H256_224 :
    toSpecState Impl.H256_224 = SHS.SHA256.H0_224 := by
  apply Vector.ext; intro i hi
  unfold toSpecState Impl.H256_224 SHS.SHA256.H0_224
  rw [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

end SHS.Equiv.SHA256.Lift
