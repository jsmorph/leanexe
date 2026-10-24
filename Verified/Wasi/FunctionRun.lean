import Verified.Wasi.FunctionEntry
import Verified.Wasi.EffectSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem ResultTy.Rep.length {result : ResultTy} {heap : Heap} {store : Store Unit}
    {words : List Value} {value : result.denote} (rep : result.Rep heap store words value) :
    words.length = result.width := by
  cases result with
  | unit =>
      have empty : words = [] := rep
      rw [empty]
      rfl
  | value type => exact Ty.Rep.length rep

theorem ResultTy.types_length (result : ResultTy) : result.types.length = result.width := by
  cases result with
  | unit => rfl
  | value type => exact type.types_length

theorem keep_params {params : List Ty} {modes : List Mode} {args : Env params}
    {words : List Value} {heap : Heap} {store : Store Unit} {locals : Locals}
    {region : Nat × Nat}
    (rep : Env.Rep (paramMode params modes) heap store words args)
    (held : ∀ {type : Ty} (x : Var params type),
      LocalsHold locals (1 + x.offset) type.types ((words.drop x.offset).take type.width))
    (apart : Apart store (Env.moves store (paramMode params modes) words args) region) :
    Holds.KeepDying args (paramSlots params modes 1) (fun _ => true) (fun _ => false)
      store locals region := by
  intro type x _ _ owned values hValues width block member
  rw [paramSlots_getD x] at hValues owned
  obtain rfl := LocalsHold.unique hValues (held x) (width.trans (rep.var x).length.symm)
  rw [Ty.blocks_pointers] at member
  obtain ⟨root, hRoot, rfl⟩ := List.mem_map.mp member
  exact apart root (Env.moves_var x rep owned root hRoot)

theorem function_after_step {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {args : Env function.params}
    {params words : List Value} {heap finalHeap : Heap} {initial final : Store World}
    {locals finalLocals : Locals} {value : function.result.denote}
    (rep : Env.Rep function.sig.mode heap (PureTransport.erase initial) params args)
    (held : ∀ {type : Ty} (x : Var function.params type),
      LocalsHold locals (1 + x.offset) type.types ((params.drop x.offset).take type.width))
    (after : After args (paramSlots function.params function.modes 1)
      (fun _ => true) (fun _ => false) (1 + widthSum function.params)
      heap initial locals function.result value finalHeap final finalLocals words) :
    Step heap (PureTransport.erase initial)
      (fun region => Apart (PureTransport.erase initial)
          (Env.moves (PureTransport.erase initial) function.sig.mode params args) region ∧
        regionsDisjoint region ABI.scratch)
      finalHeap (PureTransport.erase final)
      (function.result.fresh (PureTransport.erase final) words value) :=
  after.step.mono (fun _ kept => ⟨keep_params rep held kept.1, kept.2⟩)
    (fun _ member => member)

def FunctionPost {World : Type} (host : Host World) (signature : EffectSig)
    (action : Action signature.result.denote) (args : Env signature.params)
    (params : List Value) (heap : Heap) (initial : Store (Observed World)) (aborts : Bool) :
    Assertion (Observed World) := fun continuation =>
  match continuation with
  | .Fallthrough final locals =>
      FunctionResult host signature action args params heap initial aborts
        (.Success (locals.values.take signature.result.width) final)
  | .Trap final message =>
      FunctionResult host signature action args params heap initial aborts (.Trap final message)
  | _ => False

theorem function_result_after {World : Type} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {args : Env function.params}
    {action : Action function.result.denote} {params words : List Value}
    {heap finalHeap : Heap} {initial final : Store (Observed World)}
    {locals finalLocals : Locals} {value : function.result.denote} {trace : List Event} {aborts : Bool}
    (rep : Env.Rep function.sig.mode heap (PureTransport.erase initial) params args)
    (held : ∀ {type : Ty} (x : Var function.params type),
      LocalsHold locals (1 + x.offset) type.types ((params.drop x.offset).take type.width))
    (execution : Exec (observedHost host) action initial.host trace (.returned value) final.host)
    (after : After args (paramSlots function.params function.modes 1)
      (fun _ => true) (fun _ => false) (1 + widthSum function.params)
      heap initial locals function.result value finalHeap final finalLocals words) :
    FunctionResult host function.sig action args params heap initial aborts
      (.Success words.reverse final) := by
  change FunctionResult host ⟨function.name, function.params, function.modes, function.result⟩
    action args params heap initial aborts (.Success words.reverse final)
  exact FunctionResult.returned
    (signature := ⟨function.name, function.params, function.modes, function.result⟩)
    value finalHeap final words trace execution
    (function_after_step (function := function) rep held after) after.rep

theorem function_post_body {World : Type} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {args : Env function.params}
    {action : Action function.result.denote} {params : List Value}
    {heap middleHeap : Heap} {initial middle : Store (Observed World)}
    {locals middleLocals : Locals} {aborts : Bool} {continuation : Continuation (Observed World)}
    (rep : Env.Rep function.sig.mode heap (PureTransport.erase initial) params args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) function.sig.mode params args)
      (Env.reads (PureTransport.erase initial) function.sig.mode params args))
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial)
      function.sig.mode params args, regionsDisjoint ABI.scratch region)
    (held : ∀ {type : Ty} (x : Var function.params type),
      LocalsHold locals (1 + x.offset) type.types ((params.drop x.offset).take type.width))
    (prologue : After args (paramSlots function.params function.modes 1)
      (fun _ => true) function.body.uses (1 + widthSum function.params)
      heap initial locals .unit () middleHeap middle middleLocals [])
    (sameWorld : middle.host = initial.host) (empty : middleLocals.values = [])
    (body : CommandResult host args (paramSlots function.params function.modes 1)
      function.body.uses (fun _ => false) (1 + widthSum function.params) function.result action
      middleHeap middle middleLocals aborts continuation) :
    FunctionPost host function.sig action args params heap initial aborts continuation := by
  cases body with
  | returned value finalHeap final finalLocals words trace execution after =>
      change FunctionResult host function.sig action args params heap initial aborts
        (.Success ((words.reverse ++ middleLocals.values).take function.result.width) final)
      have out : (words.reverse ++ middleLocals.values).take function.result.width = words.reverse := by
        rw [empty, List.append_nil]
        exact List.take_of_length_le (by rw [List.length_reverse, after.rep.length])
      rw [out]
      have combined := After.thenUnit (params_holds rep separate held)
        (params_scratch rep scratch held) prologue after
        (fun _ _ => rfl) (fun _ impossible => Bool.noConfusion impossible)
      have returned : Exec (observedHost host) action initial.host trace (.returned value) final.host := by
        rw [← sameWorld]
        exact execution
      exact function_result_after rep held returned combined
  | terminal final trace outcome message execution terminal =>
      change FunctionResult host function.sig action args params heap initial aborts (.Trap final message)
      apply FunctionResult.terminal (signature := function.sig) final trace outcome message
      · rw [← sameWorld]
        exact execution
      · exact terminal
  | resource final trace residual allowed progress =>
      change FunctionResult host function.sig action args params heap initial aborts (.Trap final "unreachable")
      apply FunctionResult.resource final trace residual allowed
      rw [← sameWorld]
      exact progress

theorem function_body_wp {World : Type} {host : Host World} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {depth : UInt64}
    {params : List Value} {args : Env function.params} {action : Action function.result.denote}
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
    (body : ∀ (middleHeap : Heap) (middle : Store (Observed World)) (middleLocals : Locals),
      depth < depthLimit → middleLocals.params = .i64 depth :: params →
      middleLocals.positions = function.positions → middleLocals.values = [] →
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
          middleHeap middle middleLocals true) middle middleLocals targetHost) :
    wp target (function.function source typeIdx pool).body
      (FunctionPost host function.sig action args params heap initial true) initial
      ((function.function source typeIdx pool).toLocals (.i64 depth :: params)) targetHost := by
  change wp target (guardCode ++
    paramCopyCode function.positions 1 (function.params.flatMap Ty.types) ++
    Relocation.program (releaseWhere function.params (paramSlots function.params function.modes 1)
      (fun i => !function.body.uses i)) ++
    function.body.code (pool := pool) source function.positions
      (paramSlots function.params function.modes 1) (1 + widthSum function.params) (fun _ => false))
    (FunctionPost host function.sig action args params heap initial true) initial
    ((function.function source typeIdx pool).toLocals (.i64 depth :: params)) targetHost
  refine wp_function_entry (host := host) (sourceHost := sourceHost)
    runtime layout profile form closed at_ rep separate input scratch poolApart ?_ ?_
  · intro _
    exact FunctionResult.resource initial [] action rfl (Prefix.refl action initial.host)
  · intro copied middleHeap middle middleLocals below parameters positions values held
      prologue safe apart empty sameWorld
    have execution := body middleHeap middle middleLocals below
      (prologue.frame.params.trans parameters) (prologue.frame.positions.trans positions) empty
      prologue.step.at_ prologue.holds safe apart (by rw [prologue.step.cap source]; exact cap)
    exact wp.conseq (fun continuation proof =>
      function_post_body rep separate scratch held prologue sameWorld empty proof) execution

theorem effectFunction_run {World : Type} {host : Host World} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {pool : Bytes.LiteralPool} {index typeIdx : Nat}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)}
    {heap : Heap} {depth : UInt64} {params : List Value} {args : Env function.params}
    {action : Action function.result.denote}
    (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[index]? = some (function.function source typeIdx pool))
    (length : params.length = widthSum function.params)
    (body : wp target (function.function source typeIdx pool).body
      (FunctionPost host function.sig action args params heap initial true) initial
      ((function.function source typeIdx pool).toLocals (.i64 depth :: params)) targetHost) :
    ∃ bound, ∀ fuel ≥ bound,
      FunctionResult host function.sig action args params heap initial true
        (run fuel target (3 + index) initial (.i64 depth :: params).reverse targetHost) := by
  unfold wp at body
  obtain ⟨bound, hBound⟩ := body
  have hImport : target.imports[3 + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.imports_length]; omega)
  have hNum : (function.function source typeIdx pool).numParams = 1 + widthSum function.params := by
    change (ValueType.i64 :: function.params.flatMap Ty.types).length = 1 + widthSum function.params
    rw [List.length_cons, flatMap_types_length]
    omega
  have hResults : (function.function source typeIdx pool).results.length = function.result.width :=
    function.result.types_length
  have hTake : (((Value.i64 depth :: params).reverse).take
      (function.function source typeIdx pool).numParams).reverse = .i64 depth :: params := by
    rw [List.take_of_length_le (by
      rw [List.length_reverse, List.length_cons, length, hNum]
      omega), List.reverse_reverse]
  have hDrop : (Value.i64 depth :: params).reverse.drop
      (function.function source typeIdx pool).numParams = [] :=
    List.drop_eq_nil_of_le (by
      rw [List.length_reverse, List.length_cons, length, hNum]
      omega)
  refine ⟨bound, fun fuel enough => ?_⟩
  have post := hBound fuel enough
  rw [run_eq hImport]
  simp only [hImports, ABI.imports_length,
    show 3 + index - 3 = index by omega, hFunction, hTake, hDrop, hResults, List.append_nil]
  cases executed : exec fuel target initial
      ((function.function source typeIdx pool).toLocals (.i64 depth :: params))
      (function.function source typeIdx pool).body targetHost with
  | Fallthrough final locals => simpa only [FunctionPost, executed, EffectFunc.sig] using post
  | Trap final message => simpa only [FunctionPost, executed] using post
  | Break label final locals =>
      exact False.elim (by simpa only [FunctionPost, executed] using post)
  | Return final values =>
      exact False.elim (by simpa only [FunctionPost, executed] using post)
  | Invalid message =>
      exact False.elim (by simpa only [FunctionPost, executed] using post)
  | OutOfFuel =>
      exact False.elim (by simpa only [FunctionPost, executed] using post)
  | ReturnCall entry final values =>
      exact False.elim (by simpa only [FunctionPost, executed] using post)
  | Throwing tag values final locals =>
      exact False.elim (by simpa only [FunctionPost, executed] using post)

end Verified.Wasi
