import Verified.Wasi.FunctionEntry

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_parameter_cleanup_framed {World : Type}
    {context : List Ty} {args : Env context} {slots : List Slot} {used : Nat → Bool} {base : Nat}
    {source target : Module} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {heap : Heap} {initial : Store World} {locals : Locals} {pool : Bytes.LiteralPool}
    {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere context slots (fun i => !used i)))
    (closed : Relocation.programClosed source.funcs.length
      (releaseWhere context slots (fun i => !used i)) = true)
    (at_ : heap.At (PureTransport.erase initial))
    (vars : Holds args slots (fun _ => true) base heap (PureTransport.erase initial) locals)
    (safe : pool.Safe args slots (fun _ => true) heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom args slots (fun _ => true) (PureTransport.erase initial) locals ABI.scratch)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (next : ∀ finalHeap final,
      Evolves args slots (fun _ => true) used base heap (PureTransport.erase initial) locals
        finalHeap (PureTransport.erase final) locals →
      finalHeap.top = heap.top → final.host = initial.host →
      pool.Safe args slots used finalHeap (PureTransport.erase final) locals →
      Holds.ApartFrom args slots used (PureTransport.erase final) locals ABI.scratch →
      wp target rest Q final locals targetHost) :
    wp target (Relocation.program (releaseWhere context slots (fun i => !used i)) ++ rest)
      Q initial locals targetHost := by
  have liveEq : (fun i => true && !(!used i)) = used := by
    funext i
    cases used i <;> rfl
  refine wp_release_context (sourceHost := sourceHost)
    runtime layout profile form closed vars at_ (fun _ _ => rfl) ?_
  intro finalHeap final evolution top sameWorld
  have normalized : Evolves args slots (fun _ => true) used base heap
      (PureTransport.erase initial) locals finalHeap (PureTransport.erase final) locals := by
    simpa only [liveEq] using evolution
  have after := cleanup_after normalized
  have selected : ∀ i, used i = true → true = true := fun _ _ => rfl
  exact next finalHeap final normalized top sameWorld
    (after.pool_safe safe vars apart selected poolApart).1
    (after.scratch vars apart selected)

theorem wp_function_entry_framed {World : Type} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {initial : Store World} {heap : Heap} {depth : UInt64}
    {words : List Value} {args : Env function.params} {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)))
    (closed : Relocation.programClosed source.funcs.length (releaseWhere function.params
      (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) = true)
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep (paramMode function.params function.modes) heap
      (PureTransport.erase initial) words args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) (paramMode function.params function.modes) words args)
      (Env.reads (PureTransport.erase initial) (paramMode function.params function.modes) words args))
    (input : @Bytes.LiteralPool.Input (Env function.params)
      (Env.represent function.params function.modes) pool heap (PureTransport.erase initial) words args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial)
      (paramMode function.params function.modes) words args, regionsDisjoint ABI.scratch region)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (resource : depthLimit ≤ depth → Q (.Trap initial "unreachable"))
    (next : ∀ (copied : Locals) (finalHeap : Heap) (final : Store World),
      depth < depthLimit → copied.params = .i64 depth :: words →
      copied.positions = function.positions → copied.values = [] →
      (∀ {type : Ty} (x : Var function.params type),
        LocalsHold copied (1 + x.offset) type.types ((words.drop x.offset).take type.width)) →
      Evolves args (paramSlots function.params function.modes 1) (fun _ => true) function.body.uses
        (1 + widthSum function.params) heap (PureTransport.erase initial) copied
        finalHeap (PureTransport.erase final) copied →
      finalHeap.top = heap.top → final.host = initial.host →
      pool.Safe args (paramSlots function.params function.modes 1) function.body.uses
        finalHeap (PureTransport.erase final) copied →
      Holds.ApartFrom args (paramSlots function.params function.modes 1) function.body.uses
        (PureTransport.erase final) copied ABI.scratch →
      wp target rest Q final copied targetHost) :
    wp target (guardCode ++
      paramCopyCode function.positions 1 (function.params.flatMap Ty.types) ++
      Relocation.program (releaseWhere function.params
        (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) ++ rest)
      Q initial ((function.function source typeIdx pool).toLocals (.i64 depth :: words)) targetHost := by
  simp only [List.append_assoc]
  refine wp_function_parameters (source := source) (function := function) (typeIdx := typeIdx)
    (pool := pool) rep separate input scratch resource ?_
  intro copied below parameters positions values held vars safe apart
  refine wp_parameter_cleanup_framed (sourceHost := sourceHost)
    runtime layout profile form closed at_ vars safe apart poolApart ?_
  intro finalHeap final evolution top sameWorld finalSafe finalApart
  exact next copied finalHeap final below parameters positions values held evolution
    top sameWorld finalSafe finalApart

end Verified.Wasi
