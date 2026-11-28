module

public import Library.Numerics.Bounds.Program
public import LeanExe.Pipeline.Implements

@[expose] public section

namespace Library.Numerics.Bounds

instance : LeanExe.Pipeline.Flat Checked (UInt64 × Float) := ⟨fun c => (c.status, c.value)⟩

end Library.Numerics.Bounds
