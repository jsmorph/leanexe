import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.WriteCommand

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem cost_command_write_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool) (sourceHost : HostEnv Unit)
    (output : Output) (bytes : Var context .bytes) :
    CostCommandCodeSpec source target pure program pool (.write output bytes) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ _ positions vars at_ _ scratch _ _ _ ready _ _ _
  have fragment := ready _ (List.mem_singleton_self _)
  obtain ⟨typeIndex, lookup⟩ := facts.write_function output
  let all := fun i => live i || i == bytes.index
  let selected := fun i => i == bytes.index && !live i
  let index := match output with
    | .stdout => source.funcs.length + 1
    | .stderr => source.funcs.length + 2
  let action : Action (UInt64 × UInt64) :=
    Action.bind (.write output (env.get bytes) .pure) fun result => .pure (result.errno, result.count)
  have actionEq : (Command.write output bytes).denote pure.funs (program.funs pure.funs) env = action := by
    cases output <;> rfl
  have hBytes : all bytes.index = true := by simp only [all, beq_self_eq_true, Bool.or_true]
  obtain ⟨_, words, held, represented⟩ := vars.get bytes hBytes
  obtain ⟨root, length, rfl, rep⟩ := represented
  have selectLive : ∀ i, selected i = true → all i = true := by
    intro i member
    simp only [selected, Bool.and_eq_true] at member
    simp only [all, member.1, Bool.or_true]
  have liveEq : (fun i => all i && !selected i) = live := by
    funext i
    dsimp only [all, selected]
    cases live i <;> cases (i == bytes.index) <;> rfl
  suffices execution : wp target (loadCode h (slots.getD bytes.index default).loc Ty.bytes.types ++
      ([.call (3 + index)] ++ Relocation.program (releaseWhere context slots selected)))
      (CostCommandResult host pure program (.write output bytes) depth env slots all live base
        heap initial locals aborts) initial locals targetHost by
    cases output <;>
      simpa only [Command.code, Command.uses, index, selected, Wrappers.stdoutIndex, Wrappers.stderrIndex,
        Module.extraIndex, List.append_assoc, Nat.add_assoc] using execution
  refine wp_loadCode [.i64 root, .i64 length] rfl positions held ?_
  refine wp_write_helper_at facts.imports lookup valid at_ rep ?_ ?_
  · intro middle result trace execution frame _ _
    have middleVars := frame.scratchHolds at_ vars scratch (Frame.refl base locals)
    let current : Locals :=
      { locals with values := .i64 result.count :: .i64 result.errno :: locals.values }
    have currentVars : Holds env slots all base heap (PureTransport.erase middle) current :=
      middleVars.agree Frame.ofValues
    rw [← List.append_nil (Relocation.program (releaseWhere context slots selected))]
    refine wp_release_context (sourceHost := sourceHost) (rest := [])
      facts.runtime facts.layout facts.profile fragment.1 fragment.2
      currentVars (frame.scratchHeap at_) selectLive ?_
    intro finalHeap final evolution topEq sameWorld
    rw [wp_nil]
    have evolved : Evolves env slots all live base heap (PureTransport.erase middle) locals
        finalHeap (PureTransport.erase final) locals := by
      have originalInitial : Evolves env slots all (fun i => all i && !selected i) base heap
          (PureTransport.erase middle) locals finalHeap (PureTransport.erase final) current :=
        ⟨evolution.step, evolution.frame.values, evolution.holds⟩
      simpa only [current, liveEq] using originalInitial.values locals.values
    have returned : Exec (observedHost host) (.write output (env.get bytes) .pure)
        initial.host trace (.returned result) final.host := by
      rw [sameWorld]
      exact execution
    have flat : Exec (observedHost host) action initial.host trace
        (.returned (result.errno, result.count)) final.host := by
      simpa only [List.append_nil] using
        returned.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) (.pure final.host (result.errno, result.count))
    refine CostCommandResult.returned (result := .value (.elem (.prod .word .word)))
      (result.errno, result.count) finalHeap final locals
      [.i64 result.errno, .i64 result.count] trace 0 true (.write ?_)
      (write_after_release at_ vars scratch frame evolved) ?_
    · rw [actionEq]
      exact flat
    · intro _
      rw [topEq]
      exact Nat.le_add_right _ _
  · intro final message trace execution _ _ _
    have flat : Exec (observedHost host) action initial.host trace (.trapped message) final.host := by
      simpa only [List.append_nil] using
        execution.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) ⟨rfl, rfl, rfl⟩
    exact .trapped final message (.terminal final trace (.trapped message) message
      (actionEq.symm ▸ flat) rfl)

end Verified.Wasi
