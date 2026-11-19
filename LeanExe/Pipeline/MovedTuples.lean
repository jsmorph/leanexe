import LeanExe.Pipeline.FlatRecords

/-!
A tuple or a structure that the caller moves to a call, for a parameter of a tuple type that
holds arrays, buffers, or trees and that the call consumes.  A component without heap data is
moved as its words, a pair as its components, and a structure or a sum as its `Flat` tuple.
-/

namespace LeanExe.Pipeline

/-- A value without heap data inside a value that the caller moves: its words. -/
instance instScalarMoved [Scalar α] : Scalar (Moved α) := ⟨fun x => Scalar.values x.val⟩

/-- A pair that the caller moves: the words of its first component followed by those of its
second, each component moved, and the objects of the first apart from those of the second.  The
call reads nothing of the pair and consumes the objects of both components.  A pair without heap
data has the instance from `Scalar`, which comes first. -/
instance (priority := 50) instRepresentMovedProd [Represent (Moved α)] [Represent (Moved β)] :
    Represent (Moved (α × β)) where
  width p := Represent.width (Moved.mk p.val.1) + Represent.width (Moved.mk p.val.2)
  borrowed heap store vs p := ∃ first second, vs = first ++ second ∧
    Represent.borrowed heap store first (Moved.mk p.val.1) ∧
    Represent.borrowed heap store second (Moved.mk p.val.2) ∧
    ∀ b ∈ Represent.blocks store first (Moved.mk p.val.1),
      Represent.outside store second (Moved.mk p.val.2) b
  owned heap store vs p := ∃ first second, vs = first ++ second ∧
    Represent.owned heap store first (Moved.mk p.val.1) ∧
    Represent.owned heap store second (Moved.mk p.val.2) ∧
    ∀ b ∈ Represent.blocks store first (Moved.mk p.val.1),
      Represent.outside store second (Moved.mk p.val.2) b
  blocks store vs p :=
    Represent.blocks store (vs.take (Represent.width (Moved.mk p.val.1))) (Moved.mk p.val.1) ++
      Represent.blocks store (vs.drop (Represent.width (Moved.mk p.val.1))) (Moved.mk p.val.2)
  reads _ _ _ := []
  moves store vs p :=
    Represent.moves store (vs.take (Represent.width (Moved.mk p.val.1))) (Moved.mk p.val.1) ++
      Represent.moves store (vs.drop (Represent.width (Moved.mk p.val.1))) (Moved.mk p.val.2)

/-- A structure or a sum that the caller moves is moved as its `Flat` tuple. -/
instance (priority := 50) instRepresentMovedFlat [Flat α β] [Represent (Moved β)] :
    Represent (Moved α) where
  width x := Represent.width (Moved.mk (Flat.flat x.val))
  borrowed heap store vs x := Represent.borrowed heap store vs (Moved.mk (Flat.flat x.val))
  owned heap store vs x := Represent.owned heap store vs (Moved.mk (Flat.flat x.val))
  blocks store vs x := Represent.blocks store vs (Moved.mk (Flat.flat x.val))
  reads store vs x := Represent.reads store vs (Moved.mk (Flat.flat x.val))
  moves store vs x := Represent.moves store vs (Moved.mk (Flat.flat x.val))

end LeanExe.Pipeline
