import Library.Numerics.Float64.Tgamma.TgammaLogdRed

/-!
The reduction check of `TgammaLogdRed` for `Tgamma.logdTable`, evaluated by the kernel one bucket per
declaration: a single evaluation of all 32 buckets ran out of memory.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaLogdCheck
open Library.Numerics.Float64.Tgamma.TgammaLogdRed

theorem ic0 : iCheck Tgamma.logdTable 0 = true := by decide +kernel
theorem ic1 : iCheck Tgamma.logdTable 1 = true := by decide +kernel
theorem ic2 : iCheck Tgamma.logdTable 2 = true := by decide +kernel
theorem ic3 : iCheck Tgamma.logdTable 3 = true := by decide +kernel
theorem ic4 : iCheck Tgamma.logdTable 4 = true := by decide +kernel
theorem ic5 : iCheck Tgamma.logdTable 5 = true := by decide +kernel
theorem ic6 : iCheck Tgamma.logdTable 6 = true := by decide +kernel
theorem ic7 : iCheck Tgamma.logdTable 7 = true := by decide +kernel
theorem ic8 : iCheck Tgamma.logdTable 8 = true := by decide +kernel
theorem ic9 : iCheck Tgamma.logdTable 9 = true := by decide +kernel
theorem ic10 : iCheck Tgamma.logdTable 10 = true := by decide +kernel
theorem ic11 : iCheck Tgamma.logdTable 11 = true := by decide +kernel
theorem ic12 : iCheck Tgamma.logdTable 12 = true := by decide +kernel
theorem ic13 : iCheck Tgamma.logdTable 13 = true := by decide +kernel
theorem ic14 : iCheck Tgamma.logdTable 14 = true := by decide +kernel
theorem ic15 : iCheck Tgamma.logdTable 15 = true := by decide +kernel
theorem ic16 : iCheck Tgamma.logdTable 16 = true := by decide +kernel
theorem ic17 : iCheck Tgamma.logdTable 17 = true := by decide +kernel
theorem ic18 : iCheck Tgamma.logdTable 18 = true := by decide +kernel
theorem ic19 : iCheck Tgamma.logdTable 19 = true := by decide +kernel
theorem ic20 : iCheck Tgamma.logdTable 20 = true := by decide +kernel
theorem ic21 : iCheck Tgamma.logdTable 21 = true := by decide +kernel
theorem ic22 : iCheck Tgamma.logdTable 22 = true := by decide +kernel
theorem ic23 : iCheck Tgamma.logdTable 23 = true := by decide +kernel
theorem ic24 : iCheck Tgamma.logdTable 24 = true := by decide +kernel
theorem ic25 : iCheck Tgamma.logdTable 25 = true := by decide +kernel
theorem ic26 : iCheck Tgamma.logdTable 26 = true := by decide +kernel
theorem ic27 : iCheck Tgamma.logdTable 27 = true := by decide +kernel
theorem ic28 : iCheck Tgamma.logdTable 28 = true := by decide +kernel
theorem ic29 : iCheck Tgamma.logdTable 29 = true := by decide +kernel
theorem ic30 : iCheck Tgamma.logdTable 30 = true := by decide +kernel
theorem ic31 : iCheck Tgamma.logdTable 31 = true := by decide +kernel

theorem iCheck_logd : ∀ i < 32, iCheck Tgamma.logdTable i = true
  | 0, _ => ic0
  | 1, _ => ic1
  | 2, _ => ic2
  | 3, _ => ic3
  | 4, _ => ic4
  | 5, _ => ic5
  | 6, _ => ic6
  | 7, _ => ic7
  | 8, _ => ic8
  | 9, _ => ic9
  | 10, _ => ic10
  | 11, _ => ic11
  | 12, _ => ic12
  | 13, _ => ic13
  | 14, _ => ic14
  | 15, _ => ic15
  | 16, _ => ic16
  | 17, _ => ic17
  | 18, _ => ic18
  | 19, _ => ic19
  | 20, _ => ic20
  | 21, _ => ic21
  | 22, _ => ic22
  | 23, _ => ic23
  | 24, _ => ic24
  | 25, _ => ic25
  | 26, _ => ic26
  | 27, _ => ic27
  | 28, _ => ic28
  | 29, _ => ic29
  | 30, _ => ic30
  | 31, _ => ic31
  | n + 32, h => absurd h (by omega)

#print axioms iCheck_logd

end Library.Numerics.Float64.Tgamma.TgammaLogdCheck
