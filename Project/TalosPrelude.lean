import CodeLib.Attrs
import CodeLib.Basic
import CodeLib.Entry

namespace Project.TalosPrelude
@[simp] theorem write64_pages (m : Wasm.Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl
end Project.TalosPrelude

/-!
# LeanExe's focused Talos surface

LeanExe imports the stable interpreter and proof modules it uses directly.
The broader CodeLib umbrella now includes unrelated separation-logic examples
and Iris. This explicit artifact boundary keeps those modules out of integer
and floating-point execution proofs.
-/
