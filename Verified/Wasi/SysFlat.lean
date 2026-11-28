module

public import Verified.Wasi.SysFlatInvoke
public import Verified.Wasi.ReadAllocation

@[expose] public section

/-! The code of a flat call without an output from the argument test to the result words on the
stack: the test of the arguments, the locals set to 0, the accepted call, and the pushes of the
errno and the result words. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem held_transfer {s s' : Locals} :
    ∀ {locs : List Nat} {values : List UInt64},
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    (∀ place ∈ locs, s'.get place = s.get place) →
    List.Forall₂ (fun place value => s'.get place = some (.i64 value)) locs values
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, same =>
    .cons ((same _ (List.mem_cons_self ..)).trans head)
      (held_transfer tail fun place member => same place (List.mem_cons_of_mem _ member))

/-- The pushes of the errno and the result words. -/
theorem wp_sys_flat_finish {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {rest : Program} {Q : Assertion α} {base : Nat} {s : Locals}
    {errno : UInt64} {words : List UInt64}
    (hErrno : s.get base = some (.i64 errno))
    (hWords : ∀ i, i < words.length → s.get (base + 3 + i) = some (.i64 (words.getD i 0)))
    (h : wp m rest Q st { s with values :=
      ((errno :: words).map Value.i64).reverse ++ s.values } env) :
    wp m (.localGet base :: ((List.range words.length).map
      (fun index => .localGet (base + 3 + index)) ++ rest)) Q st s env := by
  rw [wp_localGet_cons, hErrno]
  dsimp only
  refine wp_push_words words (base + 3) _ (fun i hi => by simpa using hWords i hi) ?_
  simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    using h

/-! ## Calls with inputs -/

theorem inputsHeld_transfer {s s' : Locals} :
    ∀ {places : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)},
    List.Forall₂ (InputHeld s) places inputs →
    (∀ place ∈ places, s'.get place = s.get place ∧ s'.get (place + 1) = s.get (place + 1)) →
    List.Forall₂ (InputHeld s') places inputs
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, same => by
    have first := same _ (List.mem_cons_self ..)
    refine .cons ⟨first.1.trans head.1, first.2.trans head.2.1, head.2.2⟩
      (inputsHeld_transfer tail fun place member => same place (List.mem_cons_of_mem _ member))

/-- An input that a step from `initial` to `before` keeps, whose blocks lie apart from the low
memory, lies at its root before the call, apart from the low memory and from the buffer that the
step allocated. -/
theorem input_at_call {World : Type} {initial before : Store World} {heap heapA : Heap}
    {root capacity : UInt64} {input : UInt64 × LeanExe.Bytes}
    (hRep : ∃ length, Bytes.Rep heap (PureTransport.erase initial) input.1 length input.2 ∧
      ∀ r ∈ Bytes.regions (PureTransport.erase initial) input.1, regionsDisjoint r ABI.low)
    (hStep : Step heap (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.low)
      heapA (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root))
    (hReady : ReadReady heapA (PureTransport.erase before) root capacity) :
    (Bytes.At before.mem input.1 input.2 ∧ input.1.toNat < 4294967296) ∧
      regionsDisjoint (input.1.toNat, input.2.data.size) ABI.low ∧
      regionsDisjoint (input.1.toNat, input.2.data.size) (root.toNat, capacity.toNat) := by
  obtain ⟨length, rep, apart⟩ := hRep
  obtain ⟨rep', _, fresh⟩ := rep.step hStep apart
  have at_ : Bytes.At before.mem input.1 input.2 := rep'.toAt hStep.at_
  rcases rep.buffer with ⟨hNull, hEmpty⟩ | hBuffer
  · rw [hNull] at at_ ⊢
    refine ⟨⟨at_, by decide⟩, ?_, ?_⟩ <;>
      simp [LeanExe.Runtime.regionsDisjoint, ABI.low, hEmpty]
  · have hBase := hBuffer.object.base
    have hAddress := hBuffer.object.address
    have hCapacity := hBuffer.capacity
    refine ⟨⟨at_, by omega⟩, by simp only [LeanExe.Runtime.regionsDisjoint, ABI.low]; omega,
      ?_⟩
    rcases hReady with ⟨rfl, rfl⟩ | ⟨previous, hBuf, hCap⟩
    · simp [LeanExe.Runtime.regionsDisjoint]
    · have hNonzero := hBuf.nonzero
      have hBase' := hBuf.object.base
      have apartBlocks := fresh (block (PureTransport.erase initial) input.1)
        (by simp [Bytes.regions, hBuffer.nonzero]) (block (PureTransport.erase before) root)
        (by simp [Bytes.regions, hNonzero])
      simp only [block, LeanExe.Runtime.regionsDisjoint] at apartBlocks
      simp only [LeanExe.Runtime.regionsDisjoint]
      omega

/-- An input whose blocks lie apart from the low memory lies at its root, apart from the low
memory. -/
theorem input_at {World : Type} {initial : Store World} {heap : Heap}
    {input : UInt64 × LeanExe.Bytes} (hHeap : heap.At (PureTransport.erase initial))
    (hRep : ∃ length, Bytes.Rep heap (PureTransport.erase initial) input.1 length input.2 ∧
      ∀ r ∈ Bytes.regions (PureTransport.erase initial) input.1, regionsDisjoint r ABI.low) :
    (Bytes.At initial.mem input.1 input.2 ∧ input.1.toNat < 4294967296) ∧
      regionsDisjoint (input.1.toNat, input.2.data.size) ABI.low := by
  obtain ⟨length, rep, apart⟩ := hRep
  have at_ : Bytes.At initial.mem input.1 input.2 := rep.toAt hHeap
  rcases rep.buffer with ⟨hNull, hEmpty⟩ | hBuffer
  · rw [hNull] at at_ ⊢
    refine ⟨⟨at_, by decide⟩, ?_⟩
    simp [LeanExe.Runtime.regionsDisjoint, ABI.low, hEmpty]
  · have hBase := hBuffer.object.base
    have hAddress := hBuffer.object.address
    have hCapacity := hBuffer.capacity
    exact ⟨⟨at_, by omega⟩, by simp only [LeanExe.Runtime.regionsDisjoint, ABI.low]; omega⟩

/-- The code of a flat call with inputs and without an output, from the argument words and the
inputs in their locals to the errno and the result words on the stack.  A rejected request returns
its errno without a call; an accepted request runs the call, whose specification gives the reply,
the frame, and the outputs. -/
theorem wp_sys_flat_inputs_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64}
    {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.inputKind = true) (hOutputs : call.params.count .output = 0)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hLocs : ∀ place ∈ locs, place < base ∨ base + 6 ≤ place)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hInputLocs : ∀ place ∈ inputLocs, place + 2 ≤ base ∨ base + 6 ≤ place)
    (hInputReps : ∀ input ∈ inputs, ∃ length,
      Bytes.Rep heap (PureTransport.erase initial) input.1 length input.2 ∧
        ∀ r ∈ Bytes.regions (PureTransport.erase initial) input.1, regionsDisjoint r ABI.low)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      ReadAllOutside base s finalLocals →
      wp target rest Q final { finalLocals with values :=
        ((reply.errno :: resultWords call.params reply 0).map Value.i64).reverse ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysFlatInputsCodeWith calls call locs inputLocs base ++ rest) Q initial s env := by
  have hPositions : base + 6 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hInputCount' : inputs.length = call.params.count .input := by
    rw [hInputCount, Call.inputCount_of_inputKind hKinds]
  have hWordsLength := fun reply => resultWords_length reply call.params 0
  have hNone := flatCapacityWith_none call.params values (inputs.map Prod.snd) hOutputs
  simp only [sysFlatInputsCodeWith, List.append_assoc]
  refine wp_sys_reject_inputs call.params locs values inputLocs inputs s _ Q hKinds hHeld
    (by rw [hCount, Call.wordCount_of_inputKind hKinds]) hInputs hInputCount' ?_
  generalize hRejectEq : rejectArgs call.params
    (flatArgsWith call.params values (inputs.map Prod.snd)) = reject
  have outside0 := ReadAllOutside.refl base s
  have bound := fun i (hi : base ≤ i) (hi' : i < base + 6) =>
    outside0.bounds hLow hHigh hi hi'
  simp only [List.cons_append]
  refine wp_localSet_local (bound base le_rfl (by omega)).1 (bound base le_rfl (by omega)).2 ?_
  let s1 := setLocal { s with values := s.values } base (.i64 reject)
  have outside1 : ReadAllOutside base s s1 := (outside0.values s.values).set hLow le_rfl (by omega)
  change wp target _ Q initial s1 env
  refine wp_set_word (outside1.bounds hLow hHigh (i := base + 1) (by omega) (by omega)).1
    (outside1.bounds hLow hHigh (i := base + 1) (by omega) (by omega)).2 ?_
  let s2 := setLocal s1 (base + 1) (.i64 0)
  have outside2 : ReadAllOutside base s s2 := outside1.set hLow (by omega) (by omega)
  change wp target _ Q initial s2 env
  refine wp_set_word (outside2.bounds hLow hHigh (i := base + 2) (by omega) (by omega)).1
    (outside2.bounds hLow hHigh (i := base + 2) (by omega) (by omega)).2 ?_
  let s3 := setLocal s2 (base + 2) (.i64 0)
  have outside3 : ReadAllOutside base s s3 := outside2.set hLow (by omega) (by omega)
  change wp target _ Q initial s3 env
  refine wp_set_word (outside3.bounds hLow hHigh (i := base + 3) (by omega) (by omega)).1
    (outside3.bounds hLow hHigh (i := base + 3) (by omega) (by omega)).2 ?_
  let s4 := setLocal s3 (base + 3) (.i64 0)
  have outside4 : ReadAllOutside base s s4 := outside3.set hLow (by omega) (by omega)
  change wp target _ Q initial s4 env
  refine wp_set_word (outside4.bounds hLow hHigh (i := base + 4) (by omega) (by omega)).1
    (outside4.bounds hLow hHigh (i := base + 4) (by omega) (by omega)).2 ?_
  let s5 := setLocal s4 (base + 4) (.i64 0)
  have outside5 : ReadAllOutside base s s5 := outside4.set hLow (by omega) (by omega)
  change wp target _ Q initial s5 env
  have q1 := (outside0.bounds hLow hHigh (i := base) le_rfl (by omega))
  have q2 := (outside1.bounds hLow hHigh (i := base + 1) (by omega) (by omega))
  have q3 := (outside2.bounds hLow hHigh (i := base + 2) (by omega) (by omega))
  have q4 := (outside3.bounds hLow hHigh (i := base + 3) (by omega) (by omega))
  have q5 := (outside4.bounds hLow hHigh (i := base + 4) (by omega) (by omega))
  have g5 : ∀ j, s5.get j = if j = base + 4 then some (.i64 0)
      else if j = base + 3 then some (.i64 0) else if j = base + 2 then some (.i64 0)
      else if j = base + 1 then some (.i64 0) else if j = base then some (.i64 reject)
      else s.get j := by
    intro j
    by_cases h4 : j = base + 4
    · subst h4; simp only [ite_true]; exact Locals.get_setLocal_same q5.1 q5.2
    rw [ite_eq_right h4, Locals.get_setLocal_ne q5.1 h4]
    by_cases h3 : j = base + 3
    · subst h3; simp only [ite_true]; exact Locals.get_setLocal_same q4.1 q4.2
    rw [ite_eq_right h3, Locals.get_setLocal_ne q4.1 h3]
    by_cases h2 : j = base + 2
    · subst h2; simp only [ite_true]; exact Locals.get_setLocal_same q3.1 q3.2
    rw [ite_eq_right h2, Locals.get_setLocal_ne q3.1 h2]
    by_cases h1 : j = base + 1
    · subst h1; simp only [ite_true]; exact Locals.get_setLocal_same q2.1 q2.2
    rw [ite_eq_right h1, Locals.get_setLocal_ne q2.1 h1]
    by_cases h0 : j = base
    · subst h0; simp only [ite_true]
      exact Locals.get_setLocal_same (s := { s with values := s.values }) q1.1 q1.2
    rw [ite_eq_right h0]
    exact Locals.get_setLocal_ne (s := { s with values := s.values }) q1.1 h0
  have e0 : s5.get base = some (.i64 reject) := by rw [g5]; simp
  have e1 : s5.get (base + 1) = some (.i64 0) := by rw [g5]; simp
  have e3 : s5.get (base + 3) = some (.i64 0) := by rw [g5]; simp
  have e4 : s5.get (base + 4) = some (.i64 0) := by rw [g5]; simp
  have eOut : ∀ j, (j < base ∨ base + 6 ≤ j) → s5.get j = s.get j := fun j hj =>
    outside5.others j hj
  have held5 := held_transfer hHeld fun place member => eOut place (hLocs place member)
  have inputs5 := inputsHeld_transfer hInputs fun place member => by
    rcases hInputLocs place member with h | h
    · exact ⟨eOut place (by omega), eOut (place + 1) (by omega)⟩
    · exact ⟨eOut place (by omega), eOut (place + 1) (by omega)⟩
  simp only [wp_localGet_cons, e0, wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have finish : ∀ (final : Store (Observed World)) (sF : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params values (inputs.map Prod.snd)) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.low)
        heap (PureTransport.erase final) [] →
      ReadAllOutside base s sF →
      sF.get base = some (.i64 reply.errno) →
      (∀ i, i < call.params.countP Param.isResult → sF.get (base + 3 + i) =
        some (.i64 ((resultWords call.params reply 0).getD i 0))) →
      wp target (.localGet base :: ((List.range (call.params.countP Param.isResult)).map
        (fun index => .localGet (base + 3 + index)) ++ rest)) Q final
        { sF with values := s.values } env := by
    intro final sF trace reply execution step outsideF errnoF wordsF
    rw [← hWordsLength reply]
    refine wp_sys_flat_finish errnoF
      (fun i hi => wordsF i (by rw [← hWordsLength reply]; exact hi)) ?_
    exact hNext final { sF with values := s.values } trace reply execution step
      (outsideF.values s.values)
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hRejectZero : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0 := by
      change rejectArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd)) = 0
      rw [hRejectEq]; exact hAccepted
    have facts := fun input (member : input ∈ inputs) => input_at hHeap (hInputReps input member)
    refine wp_sys_flat_invoke_inputs_with (s0 := s) hImports hHost hCall hKinds
      (by omega) hResults hNone hRejectZero held5 hCount inputs5 hInputCount hHeap hLow hHigh
      (outside5.values _) e1 e3 e4 (fun input member => (facts input member).1)
      (fun input member => (facts input member).2) ?_ ?_
    · intro final sF errno outputs hSys hStep hOutsideF _ hErrnoF hWordsF
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      exact finish final sF
        [.sys call (flatArgsWith call.params values (inputs.map Prod.snd))
          (.returned errno outputs)]
        (sysReply errno outputs) (.sys_return hRejectZero hSys (.pure final.host _)) hStep
        hOutsideF hErrnoF hWordsF
    · intro final message outputs hSys
      exact hTrap final message _ (.sys_trap hRejectZero hSys)
  · rw [ite_eq_right (by simp [hAccepted] :
      ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
    have hReject : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) ≠ 0 := by
      change rejectArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd)) ≠ 0
      rw [hRejectEq]; exact hAccepted
    have hReply : (⟨call.reject (flatArgsWith call.params values (inputs.map Prod.snd)), []⟩ :
        Reply) = ⟨reject, []⟩ := by
      change (⟨rejectArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd)),
        []⟩ : Reply) = _
      rw [hRejectEq]
    refine finish initial s5 [] ⟨reject, []⟩ ?_ (Step.refl hHeap _) outside5 e0 ?_
    · rw [← hReply]
      exact .sys_reject hReject (.pure initial.host _)
    · intro i hi
      rw [resultWords_empty]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi] using e3
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi] using e4

end Verified.Wasi
