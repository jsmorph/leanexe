module

public import CodeLib.Attrs
public import CodeLib.Basic
public import CodeLib.Entry
public import CodeLib.RustStd.Frame

public section

/-!
# The Talos modules that LeanExe imports

LeanExe imports the stable interpreter and proof modules it uses directly.
The top-level CodeLib module imports unrelated separation-logic examples
and Iris. This explicit list of imports keeps those modules out of integer
and floating-point execution proofs.
-/
