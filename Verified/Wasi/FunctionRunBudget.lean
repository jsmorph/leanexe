import Verified.Wasi.FunctionRun
import Verified.Wasi.FunctionEntryBudget

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem function_body_wp_with_aborts {World : Type} {host : Host World} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {depth : UInt64}
    {params : List Value} {args : Env function.params} {action : Action function.result.denote}
    {aborts : Bool}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)))
    (closed : Relocation.programClosed source.funcs.length (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) = true)
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep function.sig.mode heap (PureTransport.erase initial) params args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) function.sig.mode params args)
      (Env.reads (PureTransport.erase initial) function.sig.mode params args))
    (input : @Bytes.LiteralPool.Input (Env function.params)
      (Env.represent function.params function.modes) pool heap (PureTransport.erase initial) params args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) function.sig.mode params args,
      regionsDisjoint ABI.scratch region)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (guardFailure : depthLimit ≤ depth → aborts = true)
    (body : ∀ (middleHeap : Heap) (middle : Store (Observed World)) (middleLocals : Locals),
      depth < depthLimit → middleLocals.params = .i64 depth :: params →
      middleLocals.positions = function.positions → middleLocals.values = [] →
      middleHeap.top = heap.top → middle.host = initial.host →
      middleHeap.At (PureTransport.erase middle) →
      Holds args (paramSlots function.params function.modes 1) function.body.uses
        (1 + widthSum function.params) middleHeap (PureTransport.erase middle) middleLocals →
      pool.Safe args (paramSlots function.params function.modes 1) function.body.uses
        middleHeap (PureTransport.erase middle) middleLocals →
      Holds.ApartFrom args (paramSlots function.params function.modes 1) function.body.uses
        (PureTransport.erase middle) middleLocals ABI.scratch →
      (PureTransport.erase middle).memoryCap source 0 ≤ 65535 →
      wp target (function.body.code (pool := pool) source function.positions
          (paramSlots function.params function.modes 1) (1 + widthSum function.params) (fun _ => false))
        (CommandResult host args (paramSlots function.params function.modes 1) function.body.uses
          (fun _ => false) (1 + widthSum function.params) function.result action
          middleHeap middle middleLocals aborts) middle middleLocals targetHost) :
    wp target (function.function source typeIdx pool).body
      (FunctionPost host function.sig action args params heap initial aborts) initial
      ((function.function source typeIdx pool).toLocals (.i64 depth :: params)) targetHost := by
  change wp target (guardCode ++
    paramCopyCode function.positions 1 (function.params.flatMap Ty.types) ++
    Relocation.program (releaseWhere function.params (paramSlots function.params function.modes 1)
      (fun i => !function.body.uses i)) ++
    function.body.code (pool := pool) source function.positions
      (paramSlots function.params function.modes 1) (1 + widthSum function.params) (fun _ => false))
    (FunctionPost host function.sig action args params heap initial aborts) initial
    ((function.function source typeIdx pool).toLocals (.i64 depth :: params)) targetHost
  refine wp_function_entry_framed (sourceHost := sourceHost)
    runtime layout profile form closed at_ rep separate input scratch poolApart ?_ ?_
  · intro high
    exact FunctionResult.resource initial [] action (guardFailure high) (Prefix.refl action initial.host)
  · intro copied middleHeap middle below parameters positions values held evolution top sameWorld safe apart
    have prologue := cleanup_after evolution
    have execution := body middleHeap middle copied below parameters positions values top sameWorld
      evolution.step.at_ evolution.holds safe apart (by rw [evolution.step.cap source]; exact cap)
    exact wp.conseq (fun continuation proof =>
      function_post_body rep separate scratch held prologue sameWorld values proof) execution

end Verified.Wasi
