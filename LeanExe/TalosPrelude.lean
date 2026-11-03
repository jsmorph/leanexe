import CodeLib.Attrs
import CodeLib.Basic
import CodeLib.Entry
import CodeLib.RustStd.Frame

/-!
# The Talos modules that LeanExe imports

LeanExe imports the stable interpreter and proof modules it uses directly.
The top-level CodeLib module imports unrelated separation-logic examples
and Iris. This explicit list of imports keeps those modules out of integer
and floating-point execution proofs.
-/
