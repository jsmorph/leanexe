import Library.Numerics.Bounds.Proof
import LeanExe.ProofKit.F64Bits

/-! The bits of the Euler solvers' float constants, and words that are not NaN patterns. -/

namespace Demos.Euler

export Library.Numerics.Bounds (not_nan_of_exponent not_nan_of_finite toBits_ofBits_of_finite)

open LeanExe.ProofKit

theorem zero_toBits : (0 : Float).toBits = 0 := by decide +kernel
theorem half_toBits : (0.5 : Float).toBits = 0x3FE0000000000000 := by decide +kernel
theorem twoFifths_toBits : (0.4 : Float).toBits = 0x3FD999999999999A := by decide +kernel
theorem sevenFifths_toBits : (1.4 : Float).toBits = 0x3FF6666666666666 := by decide +kernel
theorem one_toBits : (1 : Float).toBits = 0x3FF0000000000000 := by decide +kernel
theorem endTime_toBits : (0.8 : Float).toBits = 0x3FE999999999999A := by decide +kernel
theorem fifth_toBits : (0.2 : Float).toBits = 4596373779694328218 := by decide +kernel
theorem threeFifths_toBits : (0.6 : Float).toBits = 4603579539098121011 := by decide +kernel
theorem p029_toBits : (0.029 : Float).toBits = 4584015902316823577 := by decide +kernel
theorem p138_toBits : (0.138 : Float).toBits = 4594139994279152452 := by decide +kernel
theorem p1206_toBits : (1.206 : Float).toBits = 4608110160323255730 := by decide +kernel
theorem p3_toBits : (0.3 : Float).toBits = 4599075939470750515 := by decide +kernel
theorem p5323_toBits : (0.5323 : Float).toBits = 4602969751708575046 := by decide +kernel
theorem p15_toBits : (1.5 : Float).toBits = 4609434218613702656 := by decide +kernel

end Demos.Euler
