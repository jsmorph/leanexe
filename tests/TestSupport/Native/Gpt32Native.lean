import TestSupport.Native.Common
import Demos.Gpt32.Verified

/-!
The theorems that `verified_compile` adds for the binary32 GPT-2 kernels, the exit criterion of
milestone M6.  The translation of the module contains every one of its functions, and the
kernels have their theorems `p.f.native`, which carry the verified compiler's theorems to the C
functions of the translation.  `layerNorm32` takes a square root, and `probs32` rounds to the
nearest integer in its range reduction.
-/

namespace TestSupport.Native.Gpt32

open LClight LeanExe.Native Demos.Gpt32.Verified

theorem gpt32_all : compiled.translation.funcs.length = compiled.module.funcs.length := by
  rw [translate_funcs_eq compiled.translation_eq compiled.translation_funcs, compiled.funcs_count]
  rfl

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.layerNorm32.implements A X cap compiled.translation :=
  compiled.layerNorm32.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl compiled.probs32.implements A X cap compiled.translation :=
  compiled.probs32.native A X

end TestSupport.Native.Gpt32
