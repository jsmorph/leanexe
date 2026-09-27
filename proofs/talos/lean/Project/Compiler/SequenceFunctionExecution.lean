import Project.Compiler.ScalarProgramExecution
import Project.Compiler.FunctionState
import LeanExe.Wasm.ScalarSequenceCertificate

namespace Project.Compiler.ScalarLowering

open Project.ProofKit.ScalarTransition (State)
open LeanExe.Wasm.ScalarDescriptor (LoopSequence Program)

/-- Complete consecutive-loop execution through the production function emitter. -/
theorem sequence_function_execution (args : List UInt64) (name : Lean.Name)
    (exportName : Option String) (releaseIndex : Nat)
    {plan : LeanExe.Extract.Core.ScalarSequencePlan} {descriptor : LoopSequence} {value : UInt64}
    (matched : descriptor.Matches plan) (meaning : plan.Meaning args value)
    (m : Wasm.Module) (env : Wasm.HostEnv α) (store : Wasm.Store α) :
    ∃ (code : Wasm.Program) (next : State),
      program (LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs releaseIndex
        (plan.func name exportName args.length)) = some code ∧
      Wasm.wp m code (fun outcome => outcome = .Fallthrough store (next.toLocals [.i64 value]))
        store ((functionState (plan.func name exportName args.length) args).toLocals []) env := by
  obtain ⟨locals, localSize, evaluated, result⟩ := meaning
  let initial := functionState (plan.func name exportName args.length) args
  let scratch := args.length + plan.width
  have initialAgrees : Agrees (args ++ List.replicate plan.width 0) initial := by
    apply agrees_of_flatten (List.replicate descriptor.scratchWidth (.i64 0))
    dsimp only [initial, functionState]
    rw [matched.func_scratch]
    simp [LeanExe.Extract.Core.ScalarSequencePlan.func, List.map_append, List.map_replicate, List.append_assoc]
  have initialSize : capacity initial = scratch + descriptor.scratchWidth := by
    dsimp only [initial, functionState, capacity]
    rw [matched.func_scratch]
    simp [LeanExe.Extract.Core.ScalarSequencePlan.func, scratch, Nat.add_assoc]
  have programScratch : (descriptor.program args.length).scratchWidth = descriptor.scratchWidth :=
    (Program.ofIR_scratch (matched.ofIR_program args.length)).symm.trans (matched.body_scratch args.length)
  obtain ⟨afterProgram, trace, agrees, size⟩ := program_eval (matched.ofIR_program args.length)
    evaluated scratch initial initialAgrees (by simp [scratch]) (by rw [programScratch, initialSize])
  have room : args.length < capacity afterProgram := by
    have := plan.width_pos
    rw [size, initialSize]
    dsimp [scratch]
    omega
  obtain ⟨next, written, nextSize⟩ := set_exists (state := afterProgram) (index := args.length) (.i64 value) room
  let tail : Wasm.Program := [.localGet (plan.resultSlot args.length), .localSet args.length, .localGet args.length]
  let code := sequenceCode (descriptor.program args.length) scratch ++ tail
  refine ⟨code, next, ?_, ?_⟩
  · rw [matched.func_emit]
    simp [code, tail, scratch, program_append, sequenceCode_translation, program, instruction]
  · apply trace.program_spec [] m env store tail _
    apply Project.ProofKit.ScalarTransition.localGet_spec (agrees _ _ result)
    apply Project.ProofKit.ScalarTransition.localSet_spec written
    apply Project.ProofKit.ScalarTransition.localGet_spec (State.get_set?_same written)
    simp

end Project.Compiler.ScalarLowering
