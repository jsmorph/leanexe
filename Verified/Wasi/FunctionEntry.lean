import Verified.Wasi.OwnedScratch
import Verified.Wasi.Code
import Verified.Bytes.StaticInput
import Verified.Wasi.Cleanup

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem exec_pure_shape {World : Type} {host : Host World} {type : Type} {value : type}
    {initial final : World} {trace : List Event} {outcome : Outcome type}
    (execution : Exec host (.pure value) initial trace outcome final) :
    trace = [] ∧ outcome = .returned value ∧ final = initial := by
  cases execution
  exact ⟨rfl, rfl, rfl⟩

theorem params_holds {params : List Ty} {modes : List Mode} {args : Env params}
    {words : List Value} {heap : Heap} {store : Store Unit} {locals : Locals} {base : Nat}
    (rep : Env.Rep (paramMode params modes) heap store words args)
    (separate : Separate store (Env.moves store (paramMode params modes) words args)
      (Env.reads store (paramMode params modes) words args))
    (held : ∀ {type : Ty} (x : Var params type),
      LocalsHold locals (base + x.offset) type.types ((words.drop x.offset).take type.width)) :
    Holds args (paramSlots params modes base) (fun _ => true) (base + widthSum params)
      heap store locals := by
  refine ⟨?_, ?_⟩
  · intro type x _
    rw [paramSlots_getD x]
    exact ⟨by
        change base + x.offset + type.width ≤ base + widthSum params
        have := x.offset_width
        omega,
      _, held x, rep.var x⟩
  · intro type other x y _ _ distinct owned first second hFirst firstWidth hSecond secondWidth
    rw [paramSlots_getD x] at hFirst owned
    rw [paramSlots_getD y] at hSecond ⊢
    obtain rfl := LocalsHold.unique hFirst (held x) (firstWidth.trans (rep.var x).length.symm)
    obtain rfl := LocalsHold.unique hSecond (held y) (secondWidth.trans (rep.var y).length.symm)
    exact rep.apart x separate y distinct owned

theorem params_scratch {params : List Ty} {modes : List Mode} {args : Env params}
    {words : List Value} {heap : Heap} {store : Store Unit} {locals : Locals} {base : Nat}
    (rep : Env.Rep (paramMode params modes) heap store words args)
    (scratch : ∀ region ∈ Env.reads store (paramMode params modes) words args,
      regionsDisjoint ABI.scratch region)
    (held : ∀ {type : Ty} (x : Var params type),
      LocalsHold locals (base + x.offset) type.types ((words.drop x.offset).take type.width)) :
    Holds.ApartFrom args (paramSlots params modes base) (fun _ => true) store locals ABI.scratch := by
  intro type x _ values hValues width region member
  rw [paramSlots_getD x] at hValues member
  have xRep := rep.var x
  obtain rfl := LocalsHold.unique hValues (held x) (width.trans xRep.length.symm)
  cases mode : paramMode params modes x.index with
  | owned =>
      rw [mode] at xRep member
      exact owned_scratch xRep region member
  | borrowed =>
      rw [mode] at member
      exact scratch region (Env.reads_var x rep mode region member)

theorem params_get {locals : Locals} {depth : UInt64} {words : List Value}
    (parameters : locals.params = .i64 depth :: words) (index : Nat) (bound : index < words.length) :
    locals.get (1 + index) = some words[index] := by
  have hIndex : index + 1 < (Value.i64 depth :: words).length := by
    rw [List.length_cons]
    omega
  simp only [Locals.get, parameters, show 1 + index = index + 1 by omega, hIndex, ite_true]
  rw [List.getElem?_cons_succ,
    List.getElem?_eq_getElem bound]

theorem copied_params_hold {params : List Ty} {initial copied : Locals} {depth : UInt64}
    {words : List Value} {h : Nat}
    (parameters : initial.params = .i64 depth :: words)
    (length : words.length = widthSum params) (positions : copied.positions = h)
    (copies : ∀ q, 1 ≤ q → q < 1 + (params.flatMap Ty.types).length →
      copied.get (slotIndex h q ((params.flatMap Ty.types).getD (q - 1) .i64)) = initial.get q) :
    ∀ {type : Ty} (x : Var params type),
      LocalsHold copied (1 + x.offset) type.types ((words.drop x.offset).take type.width) := by
  intro type x index bound
  have hSlice := bound
  simp only [List.length_take, List.length_drop] at hSlice
  have hWord : x.offset + index < words.length := by have := x.offset_width; omega
  have hWidth : index < type.width := by omega
  rw [List.getElem_take, List.getElem_drop, positions]
  have copiedWord := copies (1 + x.offset + index) (by omega)
    (by rw [flatMap_types_length]; have := x.offset_width; omega)
  rw [show 1 + x.offset + index - 1 = x.offset + index by omega,
    x.types_getD hWidth] at copiedWord
  rw [copiedWord, Nat.add_assoc]
  exact params_get parameters _ hWord

theorem wp_guard_entry {World : Type} {target : Module} {targetHost : HostEnv World}
    {initial : Store World} {locals : Locals} {depth : UInt64} {rest : Program}
    {Q : Assertion World} (depthValue : locals.get 0 = some (.i64 depth))
    (resource : depthLimit ≤ depth → Q (.Trap initial "unreachable"))
    (next : depth < depthLimit → wp target rest Q initial locals targetHost) :
    wp target (guardCode ++ rest) Q initial locals targetHost := by
  simp only [guardCode, List.cons_append, List.nil_append, wp_localGet_cons, depthValue,
    wp_constI64_cons, wp_geUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases high : depthLimit ≤ depth
  · simp (config := { decide := true }) only [ge_iff_le, high, ite_true]
    rw [wp_unreachable_cons]
    exact resource high
  · simp (config := { decide := true }) only [ge_iff_le, high, ite_false]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    exact next (UInt64.not_le.mp high)

theorem wp_function_parameters {World : Type} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {targetHost : HostEnv World} {initial : Store World} {heap : Heap}
    {depth : UInt64} {words : List Value} {args : Env function.params}
    {rest : Program} {Q : Assertion World}
    (rep : Env.Rep (paramMode function.params function.modes) heap
      (PureTransport.erase initial) words args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) (paramMode function.params function.modes) words args)
      (Env.reads (PureTransport.erase initial) (paramMode function.params function.modes) words args))
    (input : @Bytes.LiteralPool.Input (Env function.params)
      (Env.represent function.params function.modes) pool heap (PureTransport.erase initial) words args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial)
      (paramMode function.params function.modes) words args, regionsDisjoint ABI.scratch region)
    (resource : depthLimit ≤ depth → Q (.Trap initial "unreachable"))
    (next : ∀ copied : Locals, depth < depthLimit →
      copied.params = .i64 depth :: words → copied.positions = function.positions → copied.values = [] →
      (∀ {type : Ty} (x : Var function.params type),
        LocalsHold copied (1 + x.offset) type.types ((words.drop x.offset).take type.width)) →
      Holds args (paramSlots function.params function.modes 1) (fun _ => true)
        (1 + widthSum function.params) heap (PureTransport.erase initial) copied →
      pool.Safe args (paramSlots function.params function.modes 1) (fun _ => true)
        heap (PureTransport.erase initial) copied →
      Holds.ApartFrom args (paramSlots function.params function.modes 1) (fun _ => true)
        (PureTransport.erase initial) copied ABI.scratch →
      wp target rest Q initial copied targetHost) :
    wp target (guardCode ++
      paramCopyCode function.positions 1 (function.params.flatMap Ty.types) ++ rest) Q initial
      ((function.function source typeIdx pool).toLocals (.i64 depth :: words)) targetHost := by
  let initialLocals := (function.function source typeIdx pool).toLocals (.i64 depth :: words)
  have parameters : initialLocals.params = .i64 depth :: words := rfl
  have values : initialLocals.values = [] := rfl
  have localLength : initialLocals.locals.length =
      function.body.width + function.positions + function.positions := by
    simp only [initialLocals, Function.toLocals, EffectFunc.function, List.length_map,
      List.length_append, List.length_replicate, Nat.add_assoc]
  have total : initialLocals.params.length + initialLocals.locals.length =
      function.positions + function.positions + function.positions := by
    rw [parameters, localLength, List.length_cons, rep.length]
    unfold EffectFunc.positions
    omega
  have positions : initialLocals.positions = function.positions := by
    simp only [Locals.positions, total]
    omega
  have depthValue : initialLocals.get 0 = some (.i64 depth) := rfl
  simp only [List.append_assoc]
  refine wp_guard_entry depthValue resource (fun below => ?_)
  refine wp_paramCopyCode (function.params.flatMap Ty.types) 1
    (by rw [flatMap_types_length, parameters, List.length_cons, rep.length]; omega)
    (by rw [parameters, List.length_cons, rep.length]; unfold EffectFunc.positions; omega)
    positions (fun copied frame stack copies => ?_)
  have copiedPositions : copied.positions = function.positions := frame.positions.trans positions
  have held : ∀ {type : Ty} (x : Var function.params type),
      LocalsHold copied (1 + x.offset) type.types ((words.drop x.offset).take type.width) :=
    fun x => copied_params_hold parameters rep.length copiedPositions copies x
  exact next copied below (frame.params.trans parameters) copiedPositions (stack.trans values)
    held (params_holds rep separate held) (input.params rep held) (params_scratch rep scratch held)

theorem wp_parameter_cleanup {World : Type} {host : Host World}
    {context : List Ty} {args : Env context} {slots : List Slot} {used : Nat → Bool} {base : Nat}
    {source target : Module} {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {pool : Bytes.LiteralPool}
    {rest : Program} {Q : Assertion (Observed World)}
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
    (next : ∀ finalHeap final finalLocals,
      After args slots (fun _ => true) used base heap initial locals .unit ()
        finalHeap final finalLocals [] →
      pool.Safe args slots used finalHeap (PureTransport.erase final) finalLocals →
      Holds.ApartFrom args slots used (PureTransport.erase final) finalLocals ABI.scratch →
      finalLocals.values = locals.values → final.host = initial.host →
      wp target rest Q final finalLocals targetHost) :
    wp target (Relocation.program (releaseWhere context slots (fun i => !used i)) ++ rest)
      Q initial locals targetHost := by
  have cleanup := wp_cleanup (host := host) (sourceHost := sourceHost) (targetHost := targetHost)
    (aborts := false) runtime layout profile form closed vars at_ (fun _ _ => rfl)
  have liveEq : (fun i => true && !(!used i)) = used := by
    funext i
    cases used i <;> rfl
  apply wp_append
  refine wp.conseq (fun continuation execution => ?_) cleanup
  cases execution with
  | returned value finalHeap final finalLocals words trace execution after =>
      cases value
      have empty : words = [] := after.rep
      subst words
      simp only [List.reverse_nil, List.nil_append, Then]
      let adjusted : Locals := { finalLocals with values := locals.values }
      have normalized : After args slots (fun _ => true) used base heap initial locals .unit ()
          finalHeap final adjusted [] := by
        have unchanged : After args slots (fun _ => true) (fun i => true && !(!used i))
            base heap initial locals .unit () finalHeap final adjusted [] :=
          ⟨after.step, ⟨after.frame.params, after.frame.length, after.frame.below, after.frame.below32⟩,
            after.holds, after.rep, after.apart⟩
        simpa only [liveEq] using unchanged
      have selected : ∀ i, used i = true → true = true := fun _ _ => rfl
      have finalSafe := (normalized.pool_safe safe vars apart selected poolApart).1
      have finalApart := normalized.scratch vars apart selected
      have sameWorld : final.host = initial.host := (exec_pure_shape execution).2.2
      exact next finalHeap final adjusted normalized finalSafe finalApart rfl sameWorld
  | terminal final trace outcome message execution terminal =>
      rw [(exec_pure_shape execution).2.1] at terminal
      exact False.elim terminal
  | resource final trace residual allowed progress => exact Bool.noConfusion allowed

theorem wp_function_entry {World : Type} {host : Host World} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {pool : Bytes.LiteralPool} {typeIdx : Nat}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {depth : UInt64}
    {words : List Value} {args : Env function.params} {rest : Program}
    {Q : Assertion (Observed World)}
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
    (next : ∀ (copied : Locals) (finalHeap : Heap) (final : Store (Observed World))
      (finalLocals : Locals), depth < depthLimit →
      copied.params = .i64 depth :: words → copied.positions = function.positions → copied.values = [] →
      (∀ {type : Ty} (x : Var function.params type),
        LocalsHold copied (1 + x.offset) type.types ((words.drop x.offset).take type.width)) →
      After args (paramSlots function.params function.modes 1) (fun _ => true) function.body.uses
        (1 + widthSum function.params) heap initial copied .unit () finalHeap final finalLocals [] →
      pool.Safe args (paramSlots function.params function.modes 1) function.body.uses
        finalHeap (PureTransport.erase final) finalLocals →
      Holds.ApartFrom args (paramSlots function.params function.modes 1) function.body.uses
        (PureTransport.erase final) finalLocals ABI.scratch →
      finalLocals.values = [] → final.host = initial.host →
      wp target rest Q final finalLocals targetHost) :
    wp target (guardCode ++
      paramCopyCode function.positions 1 (function.params.flatMap Ty.types) ++
      Relocation.program (releaseWhere function.params
        (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) ++ rest)
      Q initial ((function.function source typeIdx pool).toLocals (.i64 depth :: words)) targetHost := by
  simp only [List.append_assoc]
  refine wp_function_parameters (source := source) (function := function) (typeIdx := typeIdx)
    (pool := pool) rep separate input scratch resource ?_
  intro copied below parameters positions values held vars safe apart
  refine wp_parameter_cleanup (host := host) (sourceHost := sourceHost)
    runtime layout profile form closed at_ vars safe apart poolApart ?_
  intro finalHeap final finalLocals after finalSafe finalApart finalValues sameWorld
  exact next copied finalHeap final finalLocals below parameters positions values held
    after finalSafe finalApart (finalValues.trans values) sameWorld

end Verified.Wasi
