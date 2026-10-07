import LeanExe.Pipeline.Implements

/-!
A structure whose `Flat` tuple holds arrays, such as a grid of cells with a time and a step
count, is represented as that tuple: its values are the tuple's values, and it reads, owns, and
consumes the tuple's arrays.  A structure whose tuple has no arrays keeps the `Scalar` route of
`Implements.lean`, which has a higher priority.
-/

namespace LeanExe.Pipeline

/-- A structure is represented as its `Flat` tuple.  The priority, below `low`, keeps every type
that has an instance in `Implements.lean` on that instance, as the pair instance's does. -/
instance (priority := 50) instRepresentOfFlat [Flat α β] [Represent β] : Represent α where
  width x := Represent.width (Flat.flat x)
  borrowed heap store vs x := Represent.borrowed heap store vs (Flat.flat x)
  owned heap store vs x := Represent.owned heap store vs (Flat.flat x)
  blocks store vs x := Represent.blocks store vs (Flat.flat x)
  reads store vs x := Represent.reads store vs (Flat.flat x)
  moves store vs x := Represent.moves store vs (Flat.flat x)

end LeanExe.Pipeline
