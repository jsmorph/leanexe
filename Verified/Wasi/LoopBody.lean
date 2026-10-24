import Verified.Wasi.LoopContext
import Verified.Wasi.LoopCommand
import Verified.Wasi.LoopRelease
import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.Cleanup

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopBody {World : Type} {source target : Wasm.Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty} {type : Ty}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)} {pool : Bytes.LiteralPool}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool}
    {state : type.denote} {index depth : UInt64} {stateWords : List Value}
    {heap currentHeap : Heap} {initial current : Store (Observed World)} {locals currentLocals : Locals}
    {h base : Nat} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (bodySpec : CommandCodeSpec source target pure effects pool step)
    (hostValid : targetHost.Satisfies target (hostSpec host))
    (below : depth < depthLimit) (head : currentLocals.params.head? = some (.i64 depth))
    (positions : currentLocals.positions = h)
    (after : After env slots liveIn live base heap initial locals (.value type) state
      currentHeap current currentLocals stateWords)
    (scratch : Holds.ApartFrom env slots live (PureTransport.erase current) currentLocals ABI.scratch)
    (static : pool.Static currentHeap (PureTransport.erase current))
    (fresh : ∀ region ∈ pool.regions, ∀ block ∈ type.blocks (PureTransport.erase current) stateWords state,
      regionsDisjoint region block)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (held : LocalsHold currentLocals (base + 2) type.types stateWords)
    (counter : currentLocals.get (base + 1) = some (.i64 index))
    (usesSelected : ∀ i, step.uses (i + 2) = true → live i = true)
    (cap : (PureTransport.erase current).memoryCap source 0 ≤ 65535)
    (low : currentLocals.params.length ≤ base)
    (room : base + 2 + type.width + step.width ≤ h)
    (releaseForm : Encoding.ProgramForm (releaseCode type (base + 2)))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseCode type (base + 2)) = true)
    (ready : step.Ready source h
      (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) (shift 2 live) pool)
    (covered : step.Covered pool) (place : step.placeArgs = true)
    (next : ∀ finalHeap final stored words value trace,
      Exec (observedHost host) (step.denote pure.funs effects (.cons state (.cons index env)))
        current.host trace (.returned value) final.host →
      After env slots liveIn live base heap initial locals (.value type) value
        finalHeap final stored words →
      Frame (base + 2) currentLocals stored →
      LocalsHold stored (base + 2) type.types words → stored.values = currentLocals.values →
      Q (.Fallthrough final stored))
    (terminal : ∀ final trace outcome message,
      Exec (observedHost host) (step.denote pure.funs effects (.cons state (.cons index env)))
        current.host trace outcome final.host →
      TerminalMessage message outcome → Q (.Trap final message))
    (resource : ∀ final trace residual,
      Prefix (observedHost host) (step.denote pure.funs effects (.cons state (.cons index env)))
        current.host trace residual final.host → Q (.Trap final "unreachable")) :
    wp target ((if step.uses 0 = false then Relocation.program (releaseCode type (base + 2)) else []) ++
      step.code (pool := pool) source h
        (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
        (base + 2 + type.width) (shift 2 live) ++ storeCode h (base + 2) type.types)
      Q current currentLocals targetHost := by
  let releaseIn := fun i => decide (i < 2) || shift 2 live i
  let bodyIn := fun i => shift 2 live i || step.uses i
  let bodySlots : List Slot :=
    ⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots
  have tailLive : (fun i => releaseIn (i + 2)) = live := by
    funext i
    simp only [releaseIn, show ¬ i + 2 < 2 by omega, decide_false, Bool.false_or, shift_add]
  have selected : ∀ i, bodyIn i = true → releaseIn i = true := by
    intro i isLive
    cases i with
    | zero => rfl
    | succ i =>
        cases i with
        | zero => rfl
        | succ i =>
            have liveTail : live i = true := by
              simp only [bodyIn, shift_add, Bool.or_eq_true] at isLive
              exact isLive.elim id (usesSelected i)
            simp only [releaseIn, show ¬ i + 2 < 2 by omega, decide_false,
              Bool.false_or, shift_add, liveTail]
  have vars : Holds (.cons state (.cons (t := .word) index env)) bodySlots releaseIn
      (base + 2 + type.width) currentHeap (PureTransport.erase current) currentLocals :=
    loop_context_holds (live := releaseIn) (by simpa only [tailLive] using after.holds)
      held after.rep (by simpa only [ResultTy.Apart, tailLive] using after.apart) counter
  have apart : Holds.ApartFrom (.cons state (.cons (t := .word) index env)) bodySlots releaseIn
      (PureTransport.erase current) currentLocals ABI.scratch :=
    loop_context_scratch (live := releaseIn) (by simpa only [tailLive] using after.holds)
      (by simpa only [tailLive] using scratch) held after.rep counter
  have safe : pool.Safe (.cons state (.cons (t := .word) index env)) bodySlots releaseIn
      currentHeap (PureTransport.erase current) currentLocals :=
    loop_context_safe static held after.rep fresh counter
  have released := wp_loopRelease (sourceHost := sourceHost) runtime layout profile
    releaseForm releaseClosed vars after.step.at_ (by rfl)
    (show bodyIn 0 = step.uses 0 from by simp [bodyIn, shift]) selected
    (rest := step.code (pool := pool) source h bodySlots (base + 2 + type.width) (shift 2 live) ++
      storeCode h (base + 2) type.types) (Q := Q) (fun middleHeap middle cleanup top sameWorld => by
      have cleanupAfter := cleanup_after cleanup
      have bodyRun := bodySpec World host targetHost depth (.cons state (.cons index env)) bodySlots
        (shift 2 live) h (base + 2 + type.width) middleHeap middle currentLocals
        hostValid below head positions cleanup.holds cleanup.step.at_
        (cleanupAfter.pool_safe safe vars apart selected poolApart).1
        (cleanupAfter.scratch vars apart selected)
        (by rw [cleanup.step.cap source]; exact cap) (by omega) room ready covered place
      apply wp_append
      refine wp.conseq (fun continuation result => ?_) bodyRun
      cases result with
      | returned value finalHeap final finalLocals words trace execution bodyAfter =>
          change wp target (storeCode h (base + 2) type.types) Q final
            { finalLocals with values := words.reverse ++ currentLocals.values } targetHost
          have stepKeep := loop_body_step held after.rep cleanup bodyAfter
          have advanced := after.loopAdvance scratch stepKeep (bodyAfter.frame.mono (by omega)) bodyAfter.rep
          have storeRun : wp target (storeCode h (base + 2) type.types ++ []) Q final
              { finalLocals with values := words.reverse ++ currentLocals.values } targetHost := by
            refine wp_storeCode words h (base + 2) type.types finalLocals currentLocals.values
              bodyAfter.rep.typed (bodyAfter.frame.positions.trans positions)
              (by rw [bodyAfter.frame.params]; omega)
              (by rw [bodyAfter.frame.positions, positions, Ty.types_length]; omega) ?_
            intro stored frame storedWords _
            rw [wp_nil]
            let finalFrame : Frame (base + 2) finalLocals { stored with values := currentLocals.values } :=
              ⟨frame.params, frame.length, frame.below, frame.below32⟩
            apply next finalHeap final _ words value trace
            · simpa only [sameWorld] using execution
            · exact advanced.reframe (finalFrame.mono (by omega))
            · exact (bodyAfter.frame.mono (by omega)).trans finalFrame
            · exact storedWords
            · rfl
          simpa only [List.append_nil] using storeRun
      | terminal final trace outcome message execution status =>
          exact terminal final trace outcome message (by simpa only [sameWorld] using execution) status
      | resource final trace residual _ progress =>
          exact resource final trace residual (by simpa only [sameWorld] using progress))
  simpa only [List.append_assoc, bodySlots] using released

end Verified.Wasi
