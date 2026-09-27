import LeanExe.Extract.ScalarRangeExitCorrectness
import LeanExe.IR.ScalarFrame

namespace LeanExe.Extract.Core

/-- Sequential loop plans allocate distinct locals for every leaf. -/
inductive ScalarSequencePlan where
  | leaf (plan : ScalarRangeExitPlan)
  | bind (first second : ScalarSequencePlan)
  deriving Repr

namespace ScalarSequencePlan

def width : ScalarSequencePlan → Nat
  | .leaf _ => 4
  | .bind first second => first.width + second.width

def resultSlot : ScalarSequencePlan → Nat → Nat
  | .leaf _, slot => slot
  | .bind first second, slot => second.resultSlot (slot + first.width)

def body : ScalarSequencePlan → Nat → LeanExe.IR.Stmt
  | .leaf plan, slot => plan.body slot
  | .bind first second, slot => .seq (first.body slot) (second.body (slot + first.width))

theorem width_pos (plan : ScalarSequencePlan) : 0 < plan.width := by
  induction plan with
  | leaf => simp [width]
  | bind first second ih₁ ih₂ => simp only [width]; omega

theorem resultSlot_bounds (plan : ScalarSequencePlan) (slot : Nat) :
    slot ≤ plan.resultSlot slot ∧ plan.resultSlot slot < slot + plan.width := by
  induction plan generalizing slot with
  | leaf => simp [resultSlot, width]
  | bind first second ih₁ ih₂ =>
    have bounds := ih₂ (slot + first.width)
    simp only [resultSlot, width]
    omega

/-- Executing a plan preserves captured locals and stores its result in its own allocation. -/
def Meaning (plan : ScalarSequencePlan) (saved : List UInt64) (value : UInt64) : Prop :=
  ∃ scratch : List UInt64, scratch.length = plan.width ∧
    (plan.body saved.length).ScalarEval (saved ++ List.replicate plan.width 0) (saved ++ scratch) ∧
    (saved ++ scratch)[plan.resultSlot saved.length]? = some value

theorem Meaning.leaf {plan : ScalarRangeExitPlan} {saved : List UInt64} {value : UInt64}
    (meaning : plan.Meaning saved value) : (ScalarSequencePlan.leaf plan).Meaning saved value := by
  obtain ⟨stop, flag, evaluated⟩ := meaning.body_correct
  refine ⟨[value, UInt64.ofNat stop.toNat, stop, flag], rfl, ?_, ?_⟩
  · exact evaluated
  · exact LeanExe.IR.rangeExitStore_value saved value stop.toNat stop flag

/-- Sequential execution preserves the first allocation while evaluating the continuation. -/
theorem Meaning.bind {first second : ScalarSequencePlan} {saved left : List UInt64} {value : UInt64}
    (leftSize : left.length = first.width)
    (firstEval : (first.body saved.length).ScalarEval
      (saved ++ List.replicate first.width 0) (saved ++ left))
    (secondMeaning : second.Meaning (saved ++ left) value) :
    (ScalarSequencePlan.bind first second).Meaning saved value := by
  obtain ⟨right, rightSize, secondEval, result⟩ := secondMeaning
  refine ⟨left ++ right, by simp [width, leftSize, rightSize], ?_, ?_⟩
  · have before := firstEval.append (List.replicate second.width 0)
    have after := secondEval
    simp only [List.length_append, leftSize] at after
    simpa only [body, width, List.append_assoc, List.replicate_append_replicate] using
      LeanExe.IR.Stmt.ScalarEval.seq before after
  · simpa only [resultSlot, List.length_append, leftSize, List.append_assoc] using result

def func (plan : ScalarSequencePlan) (name : Lean.Name) (exportName : Option String)
    (arity : Nat) : LeanExe.IR.Func :=
  { sourceName := name, exportName, params := arity, locals := arity + plan.width
    body := .seq (plan.body arity) (.assign arity (.local (plan.resultSlot arity)))
    results := [.local arity] }

/-- The public result slot is written after all loops have finished. -/
theorem Meaning.func_correct {plan : ScalarSequencePlan} {args : List UInt64} {value : UInt64}
    (meaning : plan.Meaning args value) (name : Lean.Name) (exportName : Option String) :
    (plan.func name exportName args.length).ScalarEval args value := by
  obtain ⟨scratch, length, evaluated, result⟩ := meaning
  have room : args.length < (args ++ scratch).length := by
    have := plan.width_pos
    simp only [List.length_append, length]
    omega
  have written : LeanExe.IR.ScalarStore.write (args ++ scratch) args.length value =
      some ((args ++ scratch).set args.length value) := by
    simp only [LeanExe.IR.ScalarStore.write, room, ite_true]
  refine .run (afterBody := (args ++ scratch).set args.length value)
    (afterResult := (args ++ scratch).set args.length value) rfl (by simp [func]) ?_ rfl ?_
  · simpa only [func, Nat.add_sub_cancel_left] using
      LeanExe.IR.Stmt.ScalarEval.seq evaluated (.assign (.local result) written)
  · exact .local (LeanExe.IR.ScalarStore.read_write_same written)

end ScalarSequencePlan
end LeanExe.Extract.Core
