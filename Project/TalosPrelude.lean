import CodeLib.Attrs
import CodeLib.Basic
import CodeLib.Entry

-- The only RustStd.Frame fact used by the compiler is this definitional identity.
-- Keep it here without importing that module's bit-vector proofs.
namespace Wasm
@[simp] theorem Mem.write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl
end Wasm

/-!
# LeanExe's focused Talos surface

LeanExe imports the stable interpreter and proof modules it uses directly.
The broader CodeLib umbrella now includes unrelated separation-logic examples
and Iris. This explicit artifact boundary keeps those modules out of integer
and floating-point execution proofs.
-/
