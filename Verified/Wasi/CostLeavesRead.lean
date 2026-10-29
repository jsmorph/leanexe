import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.ResourceCompilerCost
import Verified.Wasi.ReadCommand
import Verified.AlignedCorrect

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem cost_command_read_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool) (sourceHost : HostEnv Unit)
    (capacity : Expr pureSigs context .word) :
    CostCommandCodeSpec source target pure program pool (.read capacity) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ depthParam positions vars at_ safe scratch cap low room ready covered place resource
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := capacity.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  have noCoerce : coerceCode h .word (capacity.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have selected : ∀ i, live i = true → (live i || capacity.uses i) = true := by
    intro index used
    simp only [used, Bool.true_or]
  have allowed : (!(capacity.fits pure.funs (pure.callFits depth) env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost pure.funs pure.flags (pure.callBounds depth) capacity env slots [] live
          (PureTransport.erase initial) locals))) = true → aborts = true := by
    intro failure
    cases aborts with
    | true => rfl
    | false =>
      obtain ⟨within, bounded⟩ := resource rfl
      obtain ⟨withinRead, fitsCapacity⟩ := bounded.read_resources locals within
      have withinCapacity := withinRead.mono (Nat.le_add_right _ _)
      simp only [Resource.PureContext.exprFits] at fitsCapacity
      simp [fitsCapacity, withinCapacity] at failure
  obtain ⟨typeIndex, lookup⟩ := facts.read
  have execution := wp_return facts.runtime facts.layout facts.profile spec
    (by simpa only [noCoerce, List.append_nil] using fragment.1)
    (by simpa only [noCoerce, List.append_nil] using fragment.2)
    positions rfl vars at_ safe cap low
    (by simpa only [Command.width, copyWidth, Ty.scalar, ite_true, Nat.max_zero] using room) place
    (rest := [.call (Wrappers.readIndex source)]) (targetHost := targetHost)
    (Q := CostCommandResult host pure program (.read capacity) depth env slots
      (fun i => live i || capacity.uses i) live base heap initial locals aborts)
    (fun failure final sameWorld =>
      .trapped final "unreachable" (CommandResult.resource_refl (allowed failure) sameWorld))
    (fun middleHeap middle middleLocals words first sameWorld prefixTop => by
      have wordsEq : words = [.i64 (capacity.denote pure.funs env)] := first.rep
      subst words
      refine wp_read_helper (aborts := aborts) facts.runtime facts.layout facts.profile facts.imports sourceHost
        lookup valid first.step.at_ (by rw [first.step.cap source]; exact cap) ?_ ?_ ?_ ?_
      · intro small nonzero noAbort
        obtain ⟨within, bounded⟩ := resource noAbort
        obtain ⟨withinRead, fitsCapacity⟩ := bounded.read_resources locals within
        apply read_room_of_budget small nonzero (by rw [first.step.cap source]; exact cap)
        exact withinRead.shift (prefixTop fitsCapacity) le_rfl (first.step.cap source)
      · intro finalHeap final root length result trace readExecution readStep rep readTop
        rw [wp_nil]
        have primitive := read_after (errno := result.errno) first.holds
          (first.scratch vars scratch selected) readStep rep
        have after := After.thenWord vars scratch first primitive selected (fun _ used => used)
        have returned : Exec (observedHost host) (readSome (capacity.denote pure.funs env))
            initial.host trace (.returned result) final.host := by
          rw [← sameWorld]
          exact readExecution
        have flat : Exec (observedHost host)
            ((Command.read capacity).denote pure.funs (program.funs pure.funs) env)
            initial.host trace (.returned (result.errno, result.bytes)) final.host := by
          simpa only [Command.denote, List.append_nil] using
            returned.bind (β := (ResultTy.value (.pair .word .bytes)).denote)
              (next := fun result => .pure (result.errno, result.bytes)) (rest := [])
              (Exec.pure (α := (ResultTy.value (.pair .word .bytes)).denote)
                final.host (result.errno, result.bytes))
        refine CostCommandResult.returned (result := .value (.pair .word .bytes))
          (result.errno, result.bytes) finalHeap final middleLocals
          [.i64 result.errno, .i64 root, .i64 length] trace
          (pure.readCost depth (slots.map Slot.mode) live capacity env) (pure.exprFits depth capacity env)
          (.read program depth (slots.map Slot.mode) live capacity env flat) after ?_
        intro fitsCapacity
        have prefixGrowth := prefixTop fitsCapacity
        rw [pure.returnWordCost_nil] at prefixGrowth
        change finalHeap.top.toNat ≤ heap.top.toNat +
          (pure.exprCost depth (slots.map Slot.mode) live capacity env +
            readCost (capacity.denote pure.funs env))
        omega
      · intro finalHeap final root message trace readExecution _ _
        have trapped : Exec (observedHost host) (readSome (capacity.denote pure.funs env))
            initial.host trace (.trapped message) final.host := by
          rw [← sameWorld]
          exact readExecution
        have flat : Exec (observedHost host)
            ((Command.read capacity).denote pure.funs (program.funs pure.funs) env)
            initial.host trace (.trapped message) final.host := by
          simpa only [Command.denote, List.append_nil] using
            trapped.bind (β := (ResultTy.value (.pair .word .bytes)).denote)
              (next := fun result => .pure (result.errno, result.bytes)) (rest := []) ⟨rfl, rfl, rfl⟩
        exact .trapped final message (.terminal final trace (.trapped message) message flat rfl)
      · intro allowed final finalWorld
        exact .trapped final "unreachable"
          (CommandResult.resource_refl allowed (finalWorld.trans sameWorld)))
  simpa only [noCoerce, List.append_nil, Command.code, Command.uses] using execution

end Verified.Wasi
