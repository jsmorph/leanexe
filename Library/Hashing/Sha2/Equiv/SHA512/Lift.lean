import Library.Hashing.Sha2.Impl.SHA512
import Library.Hashing.Sha2.Spec.HashAlgorithms
import Library.Hashing.Sha2.Spec.SHA512t

/-!
# Lifting impl `UInt64` containers to spec `BitVec 64` containers

Parallel to `equiv/SHA256/Lift.lean` at 64-bit width.  The
implementation uses `Vector UInt64` for working state and message
block; the spec's `SHA512` namespace uses `Vector (BitVec 64)` of the
same shape (under the `HashValue` / `Block` scoped notations from
`spec/Functions.lean`). -/

open scoped SHS.SHA512

open SHS.SHA512

namespace SHS.Equiv.SHA512.Lift

/-! ## Lifting maps -/

/-- Lift the implementation's working state (eight `UInt64`s) to the
spec's `HashValue` (a `Vector` of eight `BitVec 64`s). -/
def toSpecState (s : Impl.State) : HashValue :=
  s.map UInt64.toBitVec

/-- Lift the implementation's message block (sixteen `UInt64`s) to the
spec's `Block` (a `Vector` of sixteen `BitVec 64`s). -/
def toSpecBlock (b : Impl.Block) : Block :=
  b.map UInt64.toBitVec

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

/-! ## Initial-state bridge

Each `Impl.H0_*` and `SHS.SHA512.H0_*` is eight literal 64-bit
constants; the four IV lifts below are pointwise by `rfl` per index.
We enumerate the eight indices via `match` rather than calling
`native_decide` (which would inflate the trust base with
`Lean.ofReduceBool`/`trustCompiler`). -/

/-- The impl's initial hash value `H0_512` lifts to the spec's `H0_512`. -/
@[simp] theorem toSpecState_H0_512 :
    toSpecState Impl.H0_512 = SHS.SHA512.H0_512 := by
  apply Vector.ext; intro i hi
  unfold toSpecState Impl.H0_512 SHS.SHA512.H0_512
  rw [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- SHA-384 IV lift; same eight-index enumeration shape as
`toSpecState_H0_512`. -/
@[simp] theorem toSpecState_H0_384 :
    toSpecState Impl.H0_384 = SHS.SHA512.H0_384 := by
  apply Vector.ext; intro i hi
  unfold toSpecState Impl.H0_384 SHS.SHA512.H0_384
  rw [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- SHA-512/256 IV lift; same eight-index enumeration shape. -/
@[simp] theorem toSpecState_H0_512_256 :
    toSpecState Impl.H0_512_256 = SHS.SHA512.H0_512_256 := by
  apply Vector.ext; intro i hi
  unfold toSpecState Impl.H0_512_256 SHS.SHA512.H0_512_256
  rw [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- SHA-512/224 IV lift; same eight-index enumeration shape. -/
@[simp] theorem toSpecState_H0_512_224 :
    toSpecState Impl.H0_512_224 = SHS.SHA512.H0_512_224 := by
  apply Vector.ext; intro i hi
  unfold toSpecState Impl.H0_512_224 SHS.SHA512.H0_512_224
  rw [Vector.getElem_map]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

end SHS.Equiv.SHA512.Lift
