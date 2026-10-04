import Project.Gpt32.Module
import Project.WGSL.Build

/-!
The WGSL kernel of each binary32 GPT-2 function, read from its compiled IR: `specOf` takes the
build apart into the parts a `Spec` names, and `Spec.module` translates it.
-/

namespace Project.Gpt32

open Project.IR Project.WGSL

/-- The destination, limit, and index locals, the count, the per-element statements, and the
element of a compiled build. -/
def buildParts? : Project.IR.Stmt →
    Option (Nat × Nat × Nat × Project.IR.Expr .u64 × Project.IR.Stmt × Project.IR.Expr .u64)
  | .seq (.assign (type := .u64) limit count) (.seq (.ite _ .skip .abort) (.seq (.call 0 _ [dst])
      (.seq (.store _ _) (.seq (.assign index _) (.while _ (.seq body (.seq (.store _ element) _))))))) =>
      some (dst, limit, index, count, body, element)
  | _ => none

/-- The locals that `body` assigns, with their types in `f`. -/
def assignedVars (f : Func) (body : Project.IR.Stmt) : List (Nat × ScalarType) :=
  body.writes.eraseDups.map fun j => (j, (f.vars[j - f.params.length]?).getD .u64)

/-- The kernel specification of a compiled build whose count is a parameter or the size of an
array parameter, with the parameters' kinds `kinds`. -/
def specOf (f : Func) (kinds : List Kind) : Option Spec := do
  let width := f.params.length + f.vars.length
  match f.body with
  | .seq (.load .u64 s (.get src)) rest =>
      let (_, _, index, count, body, element) ← buildParts? rest
      let .get c := count | none
      if c = s then
        pure { kinds, index, count := .size s src, vars := assignedVars f body, width, body,
               element }
      else none
  | rest =>
      let (_, _, index, count, body, element) ← buildParts? rest
      let .get j := count | none
      pure { kinds, index, count := .param j, vars := assignedVars f body, width, body, element }

/-- The kernel of a compiled build, or the empty module when it is outside the translation. -/
def kernelOf (f : Func) (kinds : List Kind) : Module :=
  ((specOf f kinds).bind Spec.module).getD ⟨0, 0, []⟩

def embedKernel := kernelOf gpt32.embed32.ir [.array, .array, .word, .word, .word]
def layerNormKernel := kernelOf gpt32.layerNorm32.ir [.array, .array, .array, .word, .float]
def linearKernel := kernelOf gpt32.linear32.ir [.array, .array, .array, .word, .word]
def appendKernel := kernelOf gpt32.append32.ir [.array, .array, .word, .word]
def scoresKernel := kernelOf gpt32.scores32.ir [.array, .array, .word, .word, .word]
def headMaxKernel := kernelOf gpt32.headMax32.ir [.array, .word, .word]
def headSumKernel := kernelOf gpt32.headSum32.ir [.array, .array, .word, .word]
def probsKernel := kernelOf gpt32.probs32.ir [.array, .array, .array, .word, .word]
def mixKernel := kernelOf gpt32.mix32.ir [.array, .array, .word, .word]
def addKernel := kernelOf gpt32.add32.ir [.array, .array]
def geluKernel := kernelOf gpt32.geluArray32.ir [.array]
def logitsKernel := kernelOf gpt32.logits32.ir [.array, .array, .word, .word]

end Project.Gpt32
