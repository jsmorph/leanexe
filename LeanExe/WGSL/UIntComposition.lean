import LeanExe.WGSL.UIntCertificate

namespace LeanExe.WGSL.UInt

/-- Compose a checked statement with the remaining checked statements without
reducing the parser again inside the final artifact proof. -/
theorem steps_cons {line : String} {lines : List String} {start middle finish : Locals}
    (head : lineStep start line = some middle) (tail : steps lines middle = some finish) :
    steps (line::lines) start = some finish := by
  unfold steps
  rw [List.foldlM_cons, head]
  exact tail

theorem steps_nil (state : Locals) : steps [] state = some state := rfl

end LeanExe.WGSL.UInt
