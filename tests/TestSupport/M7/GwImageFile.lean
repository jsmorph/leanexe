import TestSupport.M7.GwStep
import TestSupport.M7.Windows
import LeanExe.M7.Proof.Parts

/-!
The kernel's check of the code of the gateway for USART3 that `m7-windows image gateway-usart3`
writes, in parts.  `tests/baremetal/m7-image.sh` elaborates this file in the directory of that file,
so `file_nat%` and `file_size%` read it, and no build target includes it.  The check of the whole
file as one declaration does not fit 16 GiB, so each part has a declaration of its own: `main`,
the step `gwTickUsart3`, `gwTickWith`, two groups of the other functions that calls reach from the
step, and the trap stubs with `udivmod64`.  `sizes` lists the functions' sizes in units in the
order of `reachFrom`, and each function's part checks its entry.  `fileOk_parts` joins the parts
into the check of the file against `genProgram` on the step's module and index, the words of
`gwInit`, the code's base, the stack's limit, the device window, and the code of `udivmod64`, the
program of which `gwUsart3_step` states the call of the step.
-/

namespace TestSupport.M7.GwImageFile

open LeanExe.M7 TestSupport.M7.Windows Demos.Energy

def gwBytes : Nat := file_nat% "gateway-usart3.bin"
def gwSize : Nat := file_size% "gateway-usart3.bin"

/-- The sizes in units of the functions that calls reach from `gwTickUsart3`. -/
def sizes : List Nat :=
  [795, 9735, 31, 110, 154, 596, 134, 5550, 96, 512, 186, 230, 118, 177, 114, 2853, 469, 390, 390,
    146, 547, 141, 84, 69, 174, 69, 174, 42, 81, 81, 160, 43]

abbrev gwState : List UInt64 := gwWords gwInit

theorem gw_main : mainPartOk gwCompiled.module 34 gwState codeBase devBase gwBytes 0 = true := by
  decide +kernel

theorem gw_count : sizes.length = (reachedFns gwCompiled.module 34).length := by
  decide +kernel

/-- `gwTickUsart3`. -/
theorem gw_fns0 : functionsPartOk gwCompiled.module 34 gwState codeBase stackLimit sizes gwBytes
    0 0 1 = true := by
  decide +kernel

/-- `gwTickWith`, the largest function. -/
theorem gw_fns1 : functionsPartOk gwCompiled.module 34 gwState codeBase stackLimit sizes gwBytes
    0 1 2 = true := by
  decide +kernel

/-- `readReq`, `writeReq`, `shiftIn`, `gateway`, `siteProf`, and `gatewayWith`. -/
theorem gw_fns2 : functionsPartOk gwCompiled.module 34 gwState codeBase stackLimit sizes gwBytes
    0 2 8 = true := by
  decide +kernel

/-- The other functions. -/
theorem gw_fns8 : functionsPartOk gwCompiled.module 34 gwState codeBase stackLimit sizes gwBytes
    0 8 32 = true := by
  decide +kernel

theorem gw_tail : tailPartOk gwState sizes udivmod64 gwBytes 0 242 = true := by
  decide +kernel

theorem gw_size : gwSize = 4 * (mainSize gwState + sizes.sum) + 242 ∧ gwBytes < 256 ^ gwSize := by
  decide +kernel

/-- The file holds the bytes of the gateway's generated program. -/
theorem gw_file :
    fileOk (genProgram gwCompiled.module 34 gwState codeBase stackLimit devBase udivmod64) gwBytes
      gwSize = true :=
  fileOk_parts gw_main gw_count
    (functionsPartOk_append
      (functionsPartOk_append (functionsPartOk_append gw_fns0 gw_fns1) gw_fns2) gw_fns8)
    gw_tail gw_size.1 gw_size.2

/-- The instructions whose bytes the file holds, for which `gwUsart3_step` holds at `codeBase`. -/
theorem gw_image : ∃ is, genProgram gwCompiled.module 34 gwState codeBase stackLimit devBase
    udivmod64 = .ok is ∧ LeanExe.FileNat.natOfBytes (imageBytes is) = gwBytes ∧
    (imageBytes is).length = gwSize :=
  fileOk_ok gw_file

end TestSupport.M7.GwImageFile

#print axioms TestSupport.M7.GwImageFile.gw_image
#print axioms TestSupport.M7.gwUsart3_step
#print axioms TestSupport.M7.gwTick_step
#print axioms TestSupport.M7.gw_covered
#print axioms TestSupport.M7.gw_stack
#print axioms LeanExe.M7.fileOk_parts
#print axioms LeanExe.M7.bootFileOk_parts
