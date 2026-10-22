import Library.Numerics.Bounds.Program
import LeanExe.Pipeline.Implements

namespace Library.Numerics.Bounds

instance : LeanExe.Pipeline.Flat Checked (UInt64 × Float) := ⟨fun c => (c.status, c.value)⟩

end Library.Numerics.Bounds
