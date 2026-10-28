import Verified.Reflect.Command
import LeanExe.Native.CText

/-!
Euclid's algorithm, compiled twice for the native translator's milestone M2: `loopCompiled` as
the verified compiler compiles a tail recursion, a loop, and `recCompiled` with tail loops off,
a recursion that takes the call depth and calls itself.
-/

namespace TestSupport.Native.Gcd

def gcd (a b : UInt64) : UInt64 :=
  if b = 0 then a else gcd b (a % b)
termination_by b.toNat
decreasing_by
  rename_i h
  have hb : b.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  simp_wf
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

verified_compile loopCompiled := [gcd]

set_option verified.tailLoops false in
verified_compile recCompiled := [gcd]

end TestSupport.Native.Gcd
