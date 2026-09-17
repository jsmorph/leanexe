import LeanExe.WGSL.Generate

namespace LeanExe.WGSL.GenerateTest

def rectangular : GemmConfig := { rows := 3, cols := 5, inner := 2 }
def edgeWorkgroups : GemmConfig := { rows := 9, cols := 17, inner := 3 }

private def accepts (config : GemmConfig) : Bool :=
  match generateGemm config with
  | .ok _ => true
  | .error _ => false

private def rejectsWith (message : String) (config : GemmConfig) : Bool :=
  match generateGemm config with
  | .error actual => actual == message
  | .ok _ => false

#guard accepts rectangular
#guard accepts edgeWorkgroups
#guard edgeWorkgroups.dispatchX == 3 && edgeWorkgroups.dispatchY == 2
#guard rejectsWith "GEMM dimensions must be positive" { rectangular with inner := 0 }
#guard rejectsWith "GEMM dimensions must fit u32" { rectangular with rows := 4294967296 }
#guard rejectsWith "GEMM storage bindings must not exceed 128 MiB"
  { rectangular with rows := 33554433 }
#guard rejectsWith "GEMM A, B, and C require distinct binding indices"
  { rectangular with bindingC := 1 }
#guard rejectsWith "GEMM bind group must be below 4" { rectangular with group := 4 }
#guard rejectsWith "GEMM binding indices must be below 1000"
  { rectangular with bindingA := 1000 }
#guard rejectsWith "GEMM workgroup dimensions must be positive"
  { rectangular with workgroupX := 0 }
#guard rejectsWith "GEMM workgroups must contain at most 256 invocations"
  { rectangular with workgroupX := 32, workgroupY := 16 }
#guard rejectsWith "GEMM dispatch dimensions must not exceed 65535 workgroups"
  { rows := 1, cols := 65536, inner := 1, workgroupX := 1, workgroupY := 1 }

/-- Integer word operations test source order and row-major addressing only;
they are deliberately not used as a binary32 reference implementation. -/
def wordArithmetic : ScalarArithmetic := { add := (· + ·), mul := (· * ·) }
def sourceA : WordBuffer := fun i => UInt32.ofNat (i + 1)
def sourceB : WordBuffer := fun i => UInt32.ofNat (i + 7)

example : gemmCell wordArithmetic { rows := 2, cols := 3, inner := 2 }
    sourceA sourceB 0 0 = 27 := by decide
example : gemmCell wordArithmetic { rows := 2, cols := 3, inner := 2 }
    sourceA sourceB 1 2 = 75 := by decide

/-- A definition marked for the first lowering mechanism. -/
def markedRectangularGemm : KernelCandidate := gemmCandidate rectangular

example : markedRectangularGemm.implementation = gemmCell :=
  markedRectangularGemm.loweringWitness

end LeanExe.WGSL.GenerateTest
