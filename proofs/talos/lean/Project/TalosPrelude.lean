import CodeLib.Attrs
import CodeLib.Basic
import CodeLib.Entry
import CodeLib.RustStd.Frame

/-!
# LeanExe's focused Talos surface

LeanExe imports the stable interpreter and proof modules it uses directly.
The broader CodeLib umbrella now includes unrelated separation-logic examples
and Iris. This explicit artifact boundary keeps those modules out of integer
and floating-point execution proofs.
-/
