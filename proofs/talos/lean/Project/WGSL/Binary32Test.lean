import Project.WGSL.Binary32

namespace Project.WGSL.Binary32

/-- (1+2^-23)(1-2^-23)-1 is -2^-46 with fusion and +0 separately. -/
theorem fusion_sensitive : fma 0x3f800001 0x3f7ffffe 0xbf800000 = 0xa8800000 := by decide +kernel
theorem separate_sensitive :
    Wasm.IEEE32.add 0xbf800000 (Wasm.IEEE32.mul 0x3f800001 0x3f7ffffe) = 0 := by decide +kernel

theorem negative_zero : fma 0x80000000 0x3f800000 0x80000000 = 0x80000000 := by decide +kernel
theorem cancellation_zero : fma 0x80000000 0x3f800000 0 = 0 := by decide +kernel
theorem gradual_underflow : fma 0x00800000 0x3f000000 0x00000001 = 0x00400001 := by decide +kernel
theorem underflow_tie_even : fma 0x00000001 0x3f000000 0 = 0 := by decide +kernel
theorem underflow_tie_up : fma 0x00000003 0x3f000000 0 = 0x00000002 := by decide +kernel
theorem finite_overflow : fma 0x7f7fffff 0x40000000 0 = 0x7f800000 := by decide +kernel
theorem infinity_times_zero : fma 0x7f800000 0 0 = 0x7fc00000 := by decide +kernel
theorem opposite_infinities : fma 0x7f800000 0x3f800000 0xff800000 = 0x7fc00000 := by decide +kernel
theorem nan_propagation : fma 0x7fc00001 0x3f800000 0 = 0x7fc00000 := by decide +kernel

#print axioms fusion_sensitive
#print axioms gradual_underflow

end Project.WGSL.Binary32
