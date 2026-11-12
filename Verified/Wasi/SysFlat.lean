import Verified.Wasi.SysFlatInvoke
import Verified.Wasi.ReadAllocation

/-! The code of a flat call from the argument test to the result words on the stack: the test of
the arguments, the locals set to 0, the accepted call with its buffer, and the pushes of the
errno, the result words, and the buffer's root and length. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The words that the code pushes for the output buffer. -/
def pushedBytes (buffer : Option Nat) (root length : UInt64) : List Value :=
  match buffer with
  | some _ => [.i64 root, .i64 length]
  | none => []

/-- The heap that a flat call allocates. -/
def flatCost (call : LeanExe.Wasi.Call) (values : List UInt64) : Nat :=
  match flatCapacity call.params values with
  | some capacity => readCost capacity
  | none => 0

theorem held_transfer {s s' : Locals} :
    ∀ {locs : List Nat} {values : List UInt64},
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    (∀ place ∈ locs, s'.get place = s.get place) →
    List.Forall₂ (fun place value => s'.get place = some (.i64 value)) locs values
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, same =>
    .cons ((same _ (List.mem_cons_self ..)).trans head)
      (held_transfer tail fun place member => same place (List.mem_cons_of_mem _ member))

/-- The pushes of the errno, the result words, and the buffer's root and length. -/
theorem wp_sys_flat_finish {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {rest : Program} {Q : Assertion α} {buffer : Option Nat} {base : Nat} {s : Locals}
    {errno root length : UInt64} {words : List UInt64}
    (hErrno : s.get base = some (.i64 errno))
    (hWords : ∀ i, i < words.length → s.get (base + 3 + i) = some (.i64 (words.getD i 0)))
    (hRoot : buffer.isSome → s.get (base + 1) = some (.i64 root))
    (hLength : buffer.isSome → s.get (base + 2) = some (.i64 length))
    (h : wp m rest Q st { s with values :=
      ((errno :: words).map Value.i64 ++ pushedBytes buffer root length).reverse ++ s.values } env) :
    wp m (.localGet base :: ((List.range words.length).map
      (fun index => .localGet (base + 3 + index)) ++ (sysPushBytesCode buffer base ++ rest)))
      Q st s env := by
  rw [wp_localGet_cons, hErrno]
  dsimp only
  refine wp_push_words words (base + 3) _ (fun i hi => by simpa using hWords i hi) ?_
  cases buffer with
  | none =>
    simpa only [sysPushBytesCode, pushedBytes, List.nil_append, List.append_nil, List.map_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append] using h
  | some place =>
    simp only [sysPushBytesCode, List.cons_append, List.nil_append, wp_localGet_cons,
      Locals.get_values, hRoot rfl, hLength rfl]
    simpa only [pushedBytes, List.map_cons, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc,
      List.singleton_append] using h


/-- An accepted flat request: the allocation of the output buffer, the host call, and the code
after it, with the continuation `K` of the enclosing `iff`. -/
theorem wp_sys_flat_accept_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64}
    {s0 s : Locals} {base : Nat} {aborts : Bool} {K : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.flatKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hAccepted : call.reject (flatArgs call.params values) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.argCount)
    (hLocs : ∀ place ∈ locs, place < base ∨ base + 6 ≤ place)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s0.params.length ≤ base) (hHigh : base + 6 ≤ s0.positions)
    (hOutside : ReadAllOutside base s0 s)
    (e1 : s.get (base + 1) = some (.i64 0)) (e2 : s.get (base + 2) = some (.i64 0))
    (e3 : s.get (base + 3) = some (.i64 0)) (e4 : s.get (base + 4) = some (.i64 0))
    (hRoom : aborts = false → ∀ capacity, flatCapacity call.params values = some capacity →
      capacity.toNat < 4294967296 → capacity ≠ 0 →
      heap.Room (PureTransport.erase initial) source (allocSize capacity))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → K (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (sF : Locals)
      (errno root length : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call (flatArgs call.params values)
        (.returned errno outputs) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length
        (resultBytes call.params (sysReply errno outputs) 0) →
      heap'.top.toNat ≤ heap.top.toNat + flatCost call values →
      ReadAllOutside base s0 sF → sF.values = s.values →
      sF.get base = some (.i64 errno) →
      (∀ i, i < call.params.countP Param.isResult → sF.get (base + 3 + i) =
        some (.i64 ((resultWords call.params (sysReply errno outputs) 0).getD i 0))) →
      sF.get (base + 1) = some (.i64 root) → sF.get (base + 2) = some (.i64 length) →
      K (.Fallthrough final sF))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys initial.host call (flatArgs call.params values)
        (.trapped message outputs) final.host → K (.Trap final message)) :
    wp target (sysFlatCallCodeWith calls call locs base (outputLocal call.params locs)) K
      initial s env := by
  have hPositions : base + 6 ≤ s0.params.length + s0.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have bound := fun i (hi : base ≤ i) (hi' : i < base + 6) =>
    hOutside.bounds hLow hHigh hi hi'
  -- The invocation from the state after the allocation.
  have invoke : ∀ (before : Store (Observed World)) (heapA : Heap) (sA : Locals)
      (root capacity : UInt64) (buffer : Option Nat),
      ((buffer = none ∧ flatCapacity call.params values = none ∧ root = 0 ∧ capacity = 0) ∨
        ∃ place, buffer = some place ∧ flatCapacity call.params values = some capacity ∧
          sA.get place = some (.i64 capacity) ∧ (place < base ∨ base + 6 ≤ place)) →
      ReadReady heapA (PureTransport.erase before) root capacity →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heapA (PureTransport.erase before) (Bytes.regions (PureTransport.erase before) root) →
      before.host = initial.host →
      heapA.top.toNat ≤ heap.top.toNat + flatCost call values →
      ReadAllOutside base s0 sA → sA.values = s.values →
      sA.get (base + 1) = some (.i64 root) → sA.get (base + 2) = some (.i64 0) →
      sA.get (base + 3) = some (.i64 0) → sA.get (base + 4) = some (.i64 0) →
      List.Forall₂ (fun place value => sA.get place = some (.i64 value)) locs values →
      wp target (sysLowerCode call.params locs (base + 1) 0 ++
        [.call (3 + calls.idxOf call), .extendUI32, .localSet base, .localGet base, .eqzI64,
         .iff 0 0 (sysLoadCode call.params 0 (base + 3) ++ sysKeepCode buffer base)
           (sysDiscardCodeWith calls buffer base) [] []]) K before sA env := by
    intro before heapA sA root capacity buffer hBuffer hReady hBefore hWorld hTop hOutsideA
      hValuesA hRootA hLengthA hThreeA hFourA hHeldA
    exact wp_sys_flat_invoke_with (s0 := s0) runtime layout profile hImports sourceHost hHost
      hCall hKinds hOutputs hResults hAccepted hHeldA hCount hBuffer hReady hBefore hWorld hTop
      hLow hHigh hOutsideA hRootA hLengthA hThreeA hFourA
      (fun heap' final sF errno root' length outputs hSys hStep hRep hTop' hOutsideF hValues =>
        hNext heap' final sF errno root' length outputs hSys hStep hRep hTop' hOutsideF
          (hValues.trans hValuesA))
      hTrap
  simp only [sysFlatCallCodeWith, List.append_assoc]
  rcases outputLocal_spec call.params locs values hKinds hHeld hCount with
    ⟨hNone, hCapNone, _⟩ | ⟨place, capacity, hSome, hCapSome, hPlace, hMember, _⟩
  · rw [hNone]
    simp only [sysAllocateBufferWith, List.nil_append]
    exact invoke initial heap s 0 0 none (Or.inl ⟨rfl, hCapNone, rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
      (by simpa only [Bytes.regions, ite_true] using
        Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch))
      rfl (by simp [flatCost, hCapNone]) hOutside rfl e1 e2 e3 e4 hHeld
  · rw [hSome]
    simp only [sysAllocateBufferWith, List.append_assoc]
    have hSmall := flatCapacity_small call.params values capacity hKinds hAccepted hCapSome
    have hPlaceOut := hLocs place hMember
    have hLowA := (bound (base + 1) (by omega) (by omega)).1
    have hHighA := (bound (base + 1) (by omega) (by omega)).2
    have afterAllocation : ∀ root : UInt64,
        ReadAllOutside base s0 (setLocal s (base + 1) (.i64 root)) ∧
        (setLocal s (base + 1) (.i64 root)).get (base + 1) = some (.i64 root) ∧
        (∀ j, j ≠ base + 1 → (setLocal s (base + 1) (.i64 root)).get j = s.get j) :=
      fun root => ⟨hOutside.set hLow (by omega) (by omega),
        Locals.get_setLocal_same hLowA hHighA, fun j hj => Locals.get_setLocal_ne hLowA hj⟩
    refine wp_sys_allocate_with (capacityLocal := place) (rootLocal := base + 1) runtime layout
      profile hImports sourceHost hHeap (by omega) hCap hPlace hLowA hHighA
      (fun hNonzero hAbort => hRoom hAbort capacity hCapSome hSmall hNonzero)
      hResource ?_ ?_
    · intro hZero
      subst hZero
      obtain ⟨outsideA, rootA, otherA⟩ := afterAllocation 0
      exact invoke initial heap _ 0 0 (some place)
        (Or.inr ⟨place, rfl, hCapSome, (otherA place (by omega)).trans hPlace, hPlaceOut⟩)
        (Or.inl ⟨rfl, rfl⟩)
        (by simpa only [Bytes.regions, ite_true] using
          Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch))
        rfl (by simp [flatCost, hCapSome]) outsideA rfl rootA
        ((otherA (base + 2) (by omega)).trans e2) ((otherA (base + 3) (by omega)).trans e3)
        ((otherA (base + 4) (by omega)).trans e4)
        (held_transfer hHeld fun place' member => otherA place' (by
          rcases hLocs place' member with h | h <;> omega))
    · intro hNonzero before hFits hStore hWorld
      obtain ⟨hAllocate, hBuffer, hCapacity, hTopAlloc⟩ :=
        read_allocation_buffer hHeap (by omega) hFits hStore
      let root := FixedArrayAllocate.root heap.top (allocSize capacity) heap.free
      obtain ⟨outsideA, rootA, otherA⟩ := afterAllocation root
      have hBefore : Step heap (PureTransport.erase initial)
          (fun region => regionsDisjoint region ABI.scratch)
          (heap.allocate (allocSize capacity)) (PureTransport.erase before)
          (Bytes.regions (PureTransport.erase before) root) := by
        have hRoot : root ≠ 0 := hBuffer.nonzero
        rw [Bytes.regions, ite_eq_right hRoot]
        exact hAllocate.mono
          (keep' := fun region => regionsDisjoint region ABI.scratch)
          (fresh' := [block (PureTransport.erase before) root])
          (fun _ _ => True.intro) (fun _ h => h)
      exact invoke before (heap.allocate (allocSize capacity)) _ root capacity (some place)
        (Or.inr ⟨place, rfl, hCapSome, (otherA place (by omega)).trans hPlace, hPlaceOut⟩)
        (Or.inr ⟨_, hBuffer, hCapacity⟩) hBefore hWorld
        (by simp only [flatCost, hCapSome]; rw [readCost_positive hSmall hNonzero]; exact hTopAlloc)
        outsideA rfl rootA
        ((otherA (base + 2) (by omega)).trans e2) ((otherA (base + 3) (by omega)).trans e3)
        ((otherA (base + 4) (by omega)).trans e4)
        (held_transfer hHeld fun place' member => otherA place' (by
          rcases hLocs place' member with h | h <;> omega))

/-- The code of a flat call, from the argument words in their locals to the errno, the result
words, and the buffer's root and length on the stack.  A rejected request returns its errno
without a call; an accepted request runs the call, whose contract gives the reply, the frame, and
the outputs. -/
theorem wp_sys_flat_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {env : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)} {aborts : Bool}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.flatKind = true) (hOutputs : call.params.count .output ≤ 1)
    (hResults : call.params.countP Param.isResult ≤ 2)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.argCount)
    (hLocs : ∀ place ∈ locs, place < base ∨ base + 6 ≤ place)
    (hHeap : heap.At (PureTransport.erase initial))
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hRoom : aborts = false → ∀ capacity, flatCapacity call.params values = some capacity →
      capacity.toNat < 4294967296 → capacity ≠ 0 →
      heap.Room (PureTransport.erase initial) source (allocSize capacity))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (heap' : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (root length : UInt64) (trace : List Event) (reply : Reply),
      Exec (observedHost host) (.sys call (flatArgs call.params values) Action.pure) initial.host
        trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length (resultBytes call.params reply 0) →
      heap'.top.toNat ≤ heap.top.toNat + flatCost call values →
      ReadAllOutside base s finalLocals →
      wp target rest Q final { finalLocals with values :=
        ((reply.errno :: resultWords call.params reply 0).map Value.i64 ++
          pushedBytes (outputLocal call.params locs) root length).reverse ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (.sys call (flatArgs call.params values) Action.pure) initial.host
        trace (.trapped message) final.host → Q (.Trap final message)) :
    wp target (sysFlatCodeWith calls call locs base ++ rest) Q initial s env := by
  have hPositions : base + 6 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hWordsLength := fun reply => resultWords_length reply call.params 0
  simp only [sysFlatCodeWith, List.append_assoc]
  refine wp_sys_reject call.params locs values s _ Q hKinds hHeld hCount ?_
  generalize hRejectEq : rejectArgs call.params (flatArgs call.params values) = reject
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
  -- The values of the locals that the code set.
  have p1 := (outside1.bounds hLow hHigh (i := base) le_rfl (by omega)).1
  have p2 := (outside2.bounds hLow hHigh (i := base + 1) (by omega) (by omega)).1
  have p3 := (outside3.bounds hLow hHigh (i := base + 2) (by omega) (by omega)).1
  have p4 := (outside4.bounds hLow hHigh (i := base + 3) (by omega) (by omega)).1
  have p5 := (outside5.bounds hLow hHigh (i := base + 4) (by omega) (by omega)).1
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
  have e2 : s5.get (base + 2) = some (.i64 0) := by rw [g5]; simp
  have e3 : s5.get (base + 3) = some (.i64 0) := by rw [g5]; simp
  have e4 : s5.get (base + 4) = some (.i64 0) := by rw [g5]; simp
  have eOut : ∀ j, (j < base ∨ base + 6 ≤ j) → s5.get j = s.get j := fun j hj =>
    outside5.others j hj
  have held5 := held_transfer hHeld fun place member => eOut place (hLocs place member)
  simp only [wp_localGet_cons, e0, wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  -- The pushes after the iff, from the locals that the iff leaves.
  have finish : ∀ (final : Store (Observed World)) (sF : Locals) (heap' : Heap)
      (root length : UInt64) (trace : List Event) (reply : Reply),
      Exec (observedHost host) (.sys call (flatArgs call.params values) Action.pure)
        initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap' (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap' (PureTransport.erase final) root length (resultBytes call.params reply 0) →
      heap'.top.toNat ≤ heap.top.toNat + flatCost call values →
      ReadAllOutside base s sF →
      sF.get base = some (.i64 reply.errno) →
      (∀ i, i < call.params.countP Param.isResult → sF.get (base + 3 + i) =
        some (.i64 ((resultWords call.params reply 0).getD i 0))) →
      sF.get (base + 1) = some (.i64 root) → sF.get (base + 2) = some (.i64 length) →
      wp target (.localGet base :: ((List.range (call.params.countP Param.isResult)).map
        (fun index => .localGet (base + 3 + index)) ++
        (sysPushBytesCode (outputLocal call.params locs) base ++ rest))) Q final
        { sF with values := s.values } env := by
    intro final sF heap' root length trace reply execution step rep top outsideF errnoF wordsF
      rootF lengthF
    rw [← hWordsLength reply]
    refine wp_sys_flat_finish (root := root) (length := length) errnoF
      (fun i hi => wordsF i (by rw [← hWordsLength reply]; exact hi)) (fun _ => rootF)
      (fun _ => lengthF) ?_
    exact hNext heap' final { sF with values := s.values } root length trace reply execution
      step rep top (outsideF.values s.values)
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hRejectZero : call.reject (flatArgs call.params values) = 0 := by
      change rejectArgs call.params (flatArgs call.params values) = 0
      rw [hRejectEq]; exact hAccepted
    refine wp_sys_flat_accept_with (s0 := s) runtime layout profile hImports sourceHost hHost
      hCall hKinds hOutputs hResults hRejectZero held5 hCount hLocs hHeap hCap hLow hHigh
      (outside5.values _) e1 e2 e3 e4 hRoom ?_ ?_ ?_
    · intro hAbort final hWorld
      exact hResource hAbort final hWorld
    · intro heap' final sF errno root length outputs hSys hStep hRep hTop hOutsideF _ hErrnoF
        hWordsF hRootF hLengthF
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      exact finish final sF heap' root length
        [.sys call (flatArgs call.params values) (.returned errno outputs)]
        (sysReply errno outputs) (.sys_return hRejectZero hSys (.pure final.host _)) hStep hRep
        hTop hOutsideF hErrnoF hWordsF hRootF hLengthF
    · intro final message outputs hSys
      exact hTrap final message _ (.sys_trap hRejectZero hSys)
  · rw [ite_eq_right (by simp [hAccepted] :
      ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
    have hReject : call.reject (flatArgs call.params values) ≠ 0 := by
      change rejectArgs call.params (flatArgs call.params values) ≠ 0
      rw [hRejectEq]; exact hAccepted
    have hReply : (⟨call.reject (flatArgs call.params values), []⟩ : Reply) = ⟨reject, []⟩ := by
      change (⟨rejectArgs call.params (flatArgs call.params values), []⟩ : Reply) = _
      rw [hRejectEq]
    refine finish initial s5 heap 0 0 [] ⟨reject, []⟩ ?_ ?_ ?_ (by omega) outside5 e0 ?_ e1 e2
    · rw [← hReply]
      exact .sys_reject hReject (.pure initial.host _)
    · simpa only [Bytes.regions, ite_true] using
        Step.refl hHeap (fun region => regionsDisjoint region ABI.scratch)
    · rw [resultBytes_empty]
      exact Bytes.Rep.empty heap (PureTransport.erase initial)
    · intro i hi
      rw [resultWords_empty]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi] using e3
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_replicate, hi] using e4

end Verified.Wasi
