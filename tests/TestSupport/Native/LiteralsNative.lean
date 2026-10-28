import TestSupport.Native.Common
import Verified.Examples.Literals
import Verified.Examples.Bytes

/-!
The theorems that `verified_compile` adds for the literal and byte examples.  The translation of
each module contains every one of its functions.  The literal example's module has a literal
pool, so its functions' theorems are `ImplementsStatic`, whose premises add that the pool holds
the literals, and their theorems `p.f.native` are `NativeStaticImpl`.  The byte example's module
has no literal, and its theorems `p.f.native` are `NativeImpl`.  `tests/native/bytes.sh` runs the
cases of both examples on their translations.
-/

namespace TestSupport.Native.Literals

open LClight LeanExe.Native

theorem literals_all : Verified.Examples.Literals.compiled.translation.funcs.length =
    Verified.Examples.Literals.compiled.module.funcs.length := by
  rw [translate_funcs_eq Verified.Examples.Literals.compiled.translation_eq
    Verified.Examples.Literals.compiled.translation_funcs,
    Verified.Examples.Literals.compiled.funcs_count]
  rfl

theorem bytes_all : Verified.Examples.Bytes.compiled.translation.funcs.length =
    Verified.Examples.Bytes.compiled.module.funcs.length := by
  rw [translate_funcs_eq Verified.Examples.Bytes.compiled.translation_eq
    Verified.Examples.Bytes.compiled.translation_funcs,
    Verified.Examples.Bytes.compiled.funcs_count]
  rfl

example (A : Archi) (X : ExtSem) :
    Verified.NativeStaticImpl Verified.Examples.Literals.compiled.constant.implements A X cap
      Verified.Examples.Literals.compiled.translation :=
  Verified.Examples.Literals.compiled.constant.native A X

example (A : Archi) (X : ExtSem) :
    Verified.NativeStaticImpl Verified.Examples.Literals.compiled.lookup.implements A X cap
      Verified.Examples.Literals.compiled.translation :=
  Verified.Examples.Literals.compiled.lookup.native A X

example (A : Archi) (X : ExtSem) :
    Verified.NativeStaticImpl Verified.Examples.Literals.compiled.tail.implements A X cap
      Verified.Examples.Literals.compiled.translation :=
  Verified.Examples.Literals.compiled.tail.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl Verified.Examples.Bytes.compiled.copyByBuild.implements A X cap
      Verified.Examples.Bytes.compiled.translation :=
  Verified.Examples.Bytes.compiled.copyByBuild.native A X

example (A : Archi) (X : ExtSem) :
    NativeImpl Verified.Examples.Bytes.compiled.readByte.implements A X cap
      Verified.Examples.Bytes.compiled.translation :=
  Verified.Examples.Bytes.compiled.readByte.native A X

end TestSupport.Native.Literals
