import Project.ProofKit.F32LogitCertificate

open Project.ProofKit.F32LogitCertificate

example : check #[0x40000000, 0x3F800000] #[0x40000000, 0x3F800000] #[0, 0] 0 0 = true := by
  decide +kernel

example : check #[0x3F800000, 0x3F800000] #[0x3F800000, 0x3F800000] #[0, 0] 0 0 = false := by
  decide +kernel

example : check #[0x40000000, 0x3F800000] #[0x3FC00000, 0x3FC00000] #[2 ^ 148, 2 ^ 148] 0 0 = false := by
  decide +kernel

example : check #[0x40000000, 0x3F800000] #[0x3F800000, 0x40000000] #[2 ^ 149, 2 ^ 149] 0 0 = false := by
  decide +kernel

example : check #[0x40000000, 0x3F800000] #[0x41400000, 0x41300000] #[0, 0] (10 * 2 ^ 149) 0 = true := by
  decide +kernel

example : check #[0x40000000, 0x3F800000] #[0x7F800000, 0x3F800000] #[2 ^ 277, 0] 0 0 = false := by
  decide +kernel
