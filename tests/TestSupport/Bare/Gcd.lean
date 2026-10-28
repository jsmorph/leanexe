import TestSupport.Native.GcdNative
import LeanExe.Native.Proof.Main

/-!
The theorem of the bare-metal program that computes `gcd 1071 462` with the loop of
`loopCompiled`: for every list of CompCert's declarations that `PrefixOk` accepts, the whole
program terminates with result 0 after writing the eight bytes of the result to `lx_out`.
-/

namespace TestSupport.Bare.Gcd

open Wasm LClight LeanExe.Native LeanExe.Pipeline TestSupport.Native TestSupport.Native.Gcd

theorem loop_program (A : Archi) (X : ExtSem) (pre : List (ident × globdef (fundef function) type))
    (hpre : PrefixOk pre) :
    bigstep_program_terminates A X
      (bareProgram pre loopCompiled.translation (bareMain cap 2 [1071, 462] .word))
      (outTrace (encodeWord (gcd 1071 462))) 0 := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := loopCompiled.gcd.native A X
  obtain ⟨rfl, rfl⟩ := sig_of hsig (ps0 := [.i64, .i64]) (rs0 := [.i64]) rfl
  obtain ⟨hheap, -, -⟩ := loopCompiled.initial
  have hty := entry_type loopCompiled.translation_eq hfd hsig
  rcases bare_program loopCompiled.translation_eq hpre hfd [1071, 462] .word hty A X
      (aborts := false) (fun E hE hG hcap hnres hF m1 hst hs => by
        obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap hnres hF
          (nativeStore loopCompiled.module cap) _ [.i64 1071, .i64 462] (1071, 462)
          (heapAt_caps hheap [cap]) trivial (by rfl) Separate.nil
          (by rw [nativeStore_memoryCap]; decide) ⟨by simp, by simp [AllHas, VT.has]⟩ m1 hst hs
        refine ⟨t, m', vres, final, hcall, hst', ?_⟩
        rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | habort
        · exact .inl ⟨hs', outOk_word hr rfl hown⟩
        · exact .inr habort) with h | ⟨h, -⟩
  · exact h
  · cases h

end TestSupport.Bare.Gcd
