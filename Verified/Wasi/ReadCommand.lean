import Verified.Wasi.SysCommand
import Verified.Wasi.ReadFunction

/-! The command `read buffer start count`: the take of the buffer, as a `sys` command takes its
buffer, and the read of stdin into the window of the taken buffer through the read wrapper, which
reads into the buffer's block, with its correctness and its cost.  After an errno the code stores
0 into the window, as a fill of a flat call does.  The result's buffer holds, in the window, the
bytes of memory there after the call: the bytes read, followed by the bytes that the host left,
which `Exec.read_return` admits as the read's range. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The bytes of memory at the `length` positions from `address`. -/
def memoryRange (mem : Mem) (address length : Nat) : LeanExe.Bytes :=
  ⟨⟨Array.ofFn fun (i : Fin length) => mem.bytes (address + i)⟩⟩

@[simp] theorem memoryRange_size (mem : Mem) (address length : Nat) :
    (memoryRange mem address length).data.size = length := by
  simp [memoryRange, ByteArray.size]

theorem memoryRange_get (mem : Mem) (address length i : Nat)
    (hi : i < (memoryRange mem address length).data.size) :
    (memoryRange mem address length).data[i] = mem.bytes (address + i) := by
  simp [memoryRange, ByteArray.getElem_eq_getElem_data]

/-- The memory at a region whose first bytes hold `committed` begins with `committed`. -/
theorem memoryRange_prefix {mem : Mem} {address : UInt64} {length : Nat}
    {committed : LeanExe.Bytes} (hAt : Bytes.At mem address committed)
    (hSize : committed.data.size ≤ length) :
    (memoryRange mem address.toNat length).data.extract 0 committed.data.size =
      committed.data := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, ByteArray.size_extract, memoryRange_size]
    omega
  · intro i hLeft hRight
    have hi : i < committed.data.size := by simpa using hRight
    have hGet : (memoryRange mem address.toNat length).data[i]'(by
        rw [memoryRange_size]; omega) = committed.data[i] := by
      rw [memoryRange_get, hAt.contents i hi]
    simpa [ByteArray.getElem_eq_getElem_data, ByteArray.data_extract] using hGet

/-- A call of the read wrapper with the address and the length of a window of a represented buffer
reads at most the window's length of stdin into the window. -/
theorem wp_read_helper_at_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {target : Module} {host : Host World}
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {root size : UInt64} {buffer : LeanExe.Bytes} {start count address length : UInt64}
    {index typeIdx : Nat} {s : Locals} {values : List Value} {rest : Program}
    {Q : Assertion (Observed World)}
    (hImports : target.imports = ABI.importsWith calls)
    (hFunction : target.funcs[index]? = some (readFunction typeIdx))
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hHeap : heap.At (PureTransport.erase initial))
    (hWindow : WindowAt heap (PureTransport.erase initial) root size buffer start count
      address length)
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (committed : LeanExe.Bytes),
      (observedHost host).read initial.host length (.returned errno committed) final.host →
      GuestFrame initial final [ABI.scratch, (address.toNat, length.toNat)] →
      (errno = 0 → Bytes.At final.mem address committed) →
      wp target rest Q final
        { s with values := .i64 (if errno = 0 then committed.size else 0) :: .i64 errno :: values }
        env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (committed : LeanExe.Bytes),
      (observedHost host).read initial.host length (.trapped message committed) final.host →
      GuestFrame initial final [ABI.scratch, (address.toNat, length.toNat)] →
      Q (.Trap final message)) :
    wp target (.call (3 + calls.length + index) :: rest) Q initial
      { s with values := .i64 length :: .i64 address :: values } env := by
  have hMemory : 16 ≤ initial.mem.pages * 65536 := by
    have := hHeap.base
    have := hHeap.top
    change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
    omega
  have hSeparate : length = 0 ∨ 16 ≤ address.toNat := by
    rcases hWindow.separate with high | ⟨zero, _⟩
    · exact Or.inr high
    · exact Or.inl zero
  obtain ⟨bound, hBound⟩ := readFunction_run_with (calls := calls) (index := index) hImports
    hFunction hHost hMemory hWindow.memory hWindow.fits hSeparate
  have hImport : target.imports[3 + calls.length + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.importsWith_length]; omega)
  have hLookup : target.funcs[3 + calls.length + index - target.imports.length]? =
      some (readFunction typeIdx) := by
    simpa only [hImports, ABI.importsWith_length, Nat.add_sub_cancel_left] using hFunction
  have hAt := hBound bound le_rfl
  generalize hRun : run bound target (3 + calls.length + index) initial
    [.i64 length, .i64 address] env = outcome at hAt
  cases hAt with
  | returned final errno committed hRead hFrame hData =>
      have hCall := run_append_of_success hImport hLookup (by rfl) hRun values
      exact wp_call_returned_at hCall (hNext final errno committed hRead hFrame hData)
  | hostTrap final message committed hRead hFrame =>
      have hCall := run_append_of_trap hImport hLookup (by rfl) hRun values
      exact wp_call_trapped_at hCall (hTrap final message committed hRead hFrame)

/-- The code of a read of stdin into the window of the buffer whose root and size lie in the two
locals from `rootLocal`, from the window's start and count in their locals to the errno, the count,
and the buffer's root and size on the stack.  The buffer keeps its block, and after an errno the
window's bytes are 0. -/
theorem wp_read_fill_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {index typeIdx rootLocal startLocal countLocal base : Nat}
    {root size start count : UInt64} {buffer : LeanExe.Bytes}
    {s : Locals} {rest : Program} {Q : Assertion (Observed World)}
    (hFunction : target.funcs[index]? = some (readFunction typeIdx))
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hRoot : s.get rootLocal = some (.i64 root))
    (hSize : s.get (rootLocal + 1) = some (.i64 size)) (hRootBelow : rootLocal + 2 ≤ base)
    (hStart : s.get startLocal = some (.i64 start)) (hStartBelow : startLocal < base)
    (hCount : s.get countLocal = some (.i64 count)) (hCountBelow : countLocal < base)
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s.params.length ≤ base) (hHigh : base + 5 ≤ s.positions)
    (hNext : ∀ (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event)
      (result : FillResult),
      Exec (observedHost host) (readStdin buffer start count) initial.host trace
        (.returned result) final.host →
      Step heap (PureTransport.erase initial)
        (fun r => regionsDisjoint r ABI.low ∧
          ∀ b ∈ Bytes.regions (PureTransport.erase initial) root, regionsDisjoint r b)
        heap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap (PureTransport.erase final) root size result.buffer →
      LocalsOutside s finalLocals base 5 →
      wp target rest Q final { finalLocals with values :=
        [Value.i64 size, .i64 root, .i64 result.count, .i64 result.errno] ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (readStdin buffer start count) initial.host trace
        (.trapped message) final.host →
      Q (.Trap final message)) :
    wp target (readFillCode (3 + calls.length + index) rootLocal startLocal countLocal base ++
      rest) Q initial s env := by
  have hPositions : base + 5 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  obtain ⟨_, hLength, hLengthEq⟩ := window_words hRep.length_eq start count
  have hWindow := window_at hRep hHeap start count
  have hAddrNat := hWindow.address_toNat
  have hFits := hWindow.fits
  have hMem := hWindow.memory
  have hWindowLe := buffer.window_le start count
  have hCapacity : (buffer.windowLength start count).toNat < 2 ^ 32 := by
    rw [← hLengthEq]
    omega
  have hRange : ∀ mem : Mem, (memoryRange mem (root.toNat + (buffer.window start count).1)
      (buffer.window start count).2).data.size = (buffer.windowLength start count).toNat := by
    intro mem
    rw [memoryRange_size, LeanExe.Bytes.windowLength_toNat]
  simp only [readFillCode, List.append_assoc]
  refine wp_window_code hRoot hSize hStart hCount (by omega) (by omega) (by omega) (by omega) ?_
  intro s1 outside1 values1 getAddress getLength
  simp only [List.cons_append, List.nil_append]
  refine wp_localGet_get getAddress ?_
  refine wp_localGet_get (by rw [Locals.get_values]; exact getLength) ?_
  refine wp_read_helper_at_with
    (s := { s1 with values := .i64 (root + windowFirstWord size start) :: s1.values })
    (values := s1.values) hImports hFunction hHost hHeap hWindow ?_ ?_
  · intro final errno committed hRead hFrame hData
    rw [hLengthEq] at hRead
    have hFrameWindow : GuestFrame initial final
        [ABI.scratch, (root.toNat + (buffer.window start count).1, (buffer.window start count).2)] :=
      by rw [← hAddrNat, ← hLength]; exact hFrame
    have hSizeBound : committed.data.size ≤ (buffer.window start count).2 := by
      have := ((observedHost host).read_bound hRead).1
      simpa only [Transfer.committed, LeanExe.Bytes.windowLength_toNat] using this
    let range := memoryRange final.mem (root.toNat + (buffer.window start count).1)
      (buffer.window start count).2
    let used := (readReply errno committed range).bytes.size
    have hUsed : used = if errno = 0 then committed.size else 0 := by
      by_cases hZero : errno = 0
      · simp [used, readReply, hZero]
      · simp [used, readReply, hZero, LeanExe.Bytes.size_empty]
    have hPrefix : errno = 0 → range.data.extract 0 committed.data.size = committed.data := by
      intro hZero
      have hAt := hData hZero
      have := memoryRange_prefix (length := (buffer.window start count).2) hAt hSizeBound
      rw [hAddrNat] at this
      exact this
    have hLow1 : s1.params.length ≤ base + 3 := by rw [outside1.params]; omega
    have hHigh1 : base + 3 < s1.params.length + s1.locals.length := by
      rw [outside1.params, outside1.length]; omega
    rw [← hUsed]
    change wp target (.localSet (base + 3) :: .localSet base :: (fillTailCode rootLocal base ++ rest))
      Q final { s1 with values := .i64 used :: .i64 errno :: s1.values } env
    refine wp_localSet_local hLow1 hHigh1 ?_
    let s2 := setLocal { s1 with values := .i64 errno :: s1.values } (base + 3) (.i64 used)
    have hLow2 : s2.params.length ≤ base := by simp only [s2, setLocal]; rw [outside1.params]; omega
    have hHigh2 : base < s2.params.length + s2.locals.length := by
      simp only [s2, setLocal, List.length_set]; rw [outside1.params, outside1.length]; omega
    change wp target (.localSet base :: (fillTailCode rootLocal base ++ rest)) Q final
      { s2 with values := .i64 errno :: s1.values } env
    refine wp_localSet_local (s := s2) (vs := s1.values) hLow2 hHigh2 ?_
    let s3 := setLocal { s2 with values := s1.values } base (.i64 errno)
    change wp target (fillTailCode rootLocal base ++ rest) Q final s3 env
    have get2 : ∀ j, j ≠ base + 3 → s2.get j = s1.get j := fun j hj => by
      simp only [s2]
      rw [Locals.get_setLocal_ne (s := { s1 with values := .i64 errno :: s1.values }) hLow1 hj,
        Locals.get_values]
    have get3 : ∀ j, j ≠ base → s3.get j = s2.get j := fun j hj => by
      simp only [s3]
      rw [Locals.get_setLocal_ne (s := { s2 with values := s1.values }) hLow2 hj,
        Locals.get_values]
    have outside3 : LocalsOutside s s3 base 5 := by
      have o2 : LocalsOutside s s2 base 5 :=
        ((outside1.widen (by omega) (by omega)).values _).set hLow (by omega) (by omega)
      exact (o2.values _).set hLow le_rfl (by omega)
    have errno3 : s3.get base = some (.i64 errno) :=
      Locals.get_setLocal_same (s := { s2 with values := s1.values }) hLow2 hHigh2
    have address3 : s3.get (base + 1) = some (.i64 (root + windowFirstWord size start)) := by
      rw [get3 _ (by omega), get2 _ (by omega)]; exact getAddress
    have length3 : s3.get (base + 2) = some (.i64 (windowLengthWord size start count)) := by
      rw [get3 _ (by omega), get2 _ (by omega)]; exact getLength
    have count3 : s3.get (base + 3) = some (.i64 used) := by
      rw [get3 _ (by omega)]
      exact Locals.get_setLocal_same (s := { s1 with values := .i64 errno :: s1.values })
        hLow1 hHigh1
    have root3 : s3.get rootLocal = some (.i64 root) := by
      rw [outside3.others _ (by omega)]; exact hRoot
    have size3 : s3.get (rootLocal + 1) = some (.i64 size) := by
      rw [outside3.others _ (by omega)]; exact hSize
    have values3 : s3.values = s1.values := rfl
    refine wp_fill_tail errno3 address3 length3 count3 root3 size3 (by omega)
      (by rw [outside3.params]; omega) (by rw [outside3.params, outside3.length]; omega)
      hFits (by rw [hFrame.pages]; exact hMem) ?_
    intro final' s' same zeros outside' values'
    have hHost' : final'.host = final.host := by
      by_cases hZero : errno = 0
      · rw [same hZero]
      · rw [(zeros hZero).1.1]
    obtain ⟨hRep', hStep'⟩ := fill_after (used := used) (out := range) hRep hHeap hFrameWindow
      (fun _ => ⟨memoryRange_size _ _ _, fun i hi => (memoryRange_get _ _ _ i hi).symm⟩) same
      (fun nonzero => by
        obtain ⟨writes, zeroBytes⟩ := zeros nonzero
        rw [hAddrNat, hLength] at writes
        refine ⟨writes, fun i hi => ?_⟩
        have := zeroBytes i (by rw [hLength]; exact hi)
        rwa [hAddrNat] at this)
    have hExec : Exec (observedHost host) (readStdin buffer start count) initial.host
        [.read (buffer.windowLength start count) (.returned errno committed)]
        (.returned (FillResult.of buffer start count errno used range)) final'.host := by
      rw [hHost']
      exact .read_return hCapacity hRead (hRange final.mem) hPrefix (.pure final.host _)
    have hCountEq : (FillResult.of buffer start count errno used range).count = used := by
      by_cases hZero : errno = 0
      · simp [FillResult.of, hZero]
      · simp [FillResult.of, hZero, hUsed]
    have hErrnoEq : (FillResult.of buffer start count errno used range).errno = errno := by
      by_cases hZero : errno = 0
      · simp [FillResult.of, hZero]
      · simp [FillResult.of, hZero]
    have next := hNext final' s' _ _ hExec hStep' hRep'
      (outside3.trans (outside'.widen (by omega) (by omega)))
    rw [hCountEq, hErrnoEq] at next
    have values1' : s1.values = s.values := values1
    rw [values3, values1']
    exact next
  · intro final message committed hRead _
    rw [hLengthEq] at hRead
    exact hTrap final message _ (.read_trap hCapacity hRead)

/-- The code of a read gives a `ValueResult` when the buffer variable is owned and dies at the
read. -/
theorem wp_read_fill_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {buffer : Var context .bytes} {start count : Var context .word} {index typeIdx : Nat}
    (hFunction : target.funcs[index]? = some (readFunction typeIdx))
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.low)
    (selected : ∀ i, live i = true → liveIn i = true)
    (hBufferIn : liveIn buffer.index = true) (hBufferOut : live buffer.index = false)
    (hOwned : (slots.getD buffer.index default).mode = .owned)
    (hStartIn : liveIn start.index = true) (hCountIn : liveIn count.index = true)
    (at_ : heap.At (PureTransport.erase initial))
    (low : locals.params.length ≤ base) (room : base + 5 ≤ locals.positions) :
    wp target (readFillCode (3 + calls.length + index) (slots.getD buffer.index default).loc
        (slots.getD start.index default).loc (slots.getD count.index default).loc base)
      (ValueResult host env slots liveIn live base (wordsBytesTy 2)
        (Action.bind (readStdin (env.get buffer) (env.get start) (env.get count)) fun result =>
          .pure (fillValue result))
        (fun _ => 0) heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨root, size, bufferHeld, hRoot, hSize, hRep, bufferBelow, _⟩ :=
    sys_buffer_held vars hBufferIn hOwned
  obtain ⟨_, _, _, _, _, _, hStart, startBelow, hCount, countBelow⟩ :=
    write_args_held (buffer := buffer) (start := start) (count := count) vars hBufferIn hStartIn
      hCountIn
  rw [← List.append_nil (readFillCode _ _ _ _ base)]
  refine wp_read_fill_with hImports hFunction hHost hRoot hSize bufferBelow hStart startBelow
    hCount countBelow hRep at_ low room ?_ ?_
  · intro final finalLocals trace result execution step rep outside
    rw [wp_nil]
    have exec := execution.bind (rest := []) (next := fun result =>
      Action.pure (fillValue result)) (Exec.pure final.host _)
    rw [List.append_nil] at exec
    have after := fill_sys_after (type := wordsBytesTy 2) vars apart selected hBufferIn
      hBufferOut hOwned bufferHeld step (outside.frame room) (fillValue_rep rep)
      (fillValue_blocks _ root size _)
    exact .returned _ heap final finalLocals _ trace exec after (by simp)
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun result =>
      Action.pure (fillValue result)) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

/-- The code of a read, the take of its buffer and the read into the taken buffer's window, gives a
`ValueResult` whose charge is the take's. -/
theorem wp_read_command_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    {World : Type} {host : Host World} {targetHost : HostEnv (Observed World)} {depth : UInt64}
    {env : Env context} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {aborts : Bool} {budget : Nat}
    {buffer : Var context .bytes} {start count : Var context .word}
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (depthParam : locals.params.head? = some (.i64 depth))
    (positions : locals.positions = h)
    (vars : Holds env slots (fun i => live i || (Command.read (pureSigs := pureSigs)
      (effectSigs := effectSigs) buffer start count).uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || (Command.read (pureSigs := pureSigs)
      (effectSigs := effectSigs) buffer start count).uses i) heap
      (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots (fun i => live i || (Command.read (pureSigs := pureSigs)
      (effectSigs := effectSigs) buffer start count).uses i)
      (PureTransport.erase initial) locals ABI.low)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + (Command.read (pureSigs := pureSigs) (effectSigs := effectSigs) buffer start
      count).width ≤ h)
    (ready : (Command.read (pureSigs := pureSigs) (effectSigs := effectSigs) buffer start
      count).ReadyWith calls source h slots base live pool)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      pure.sysTakeCost depth (slots.map Slot.mode) live [start, count] [] [buffer] env ≤ budget) :
    wp target ((Command.read (pureSigs := pureSigs) (effectSigs := effectSigs) buffer start
        count).codeWith calls (pool := pool) source h slots base live)
      (ValueResult host env slots (fun i => live i || (Command.read (pureSigs := pureSigs)
          (effectSigs := effectSigs) buffer start count).uses i) live base (wordsBytesTy 2)
        ((Command.read (pureSigs := pureSigs) (effectSigs := effectSigs) buffer start
          count).denote pure.funs effects env)
        (fun _ => pure.sysTakeCost depth (slots.map Slot.mode) live [start, count] [] [buffer] env)
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨fragments, _⟩ := ready
  have takeFragment := fragments _ (List.mem_singleton_self _)
  have takeEq : (fun i => sysTakeLive live [start, count] [] i ||
      (Expr.var (S := pureSigs) buffer).uses i) =
      (fun i => live i || (Command.read (pureSigs := pureSigs) (effectSigs := effectSigs)
        buffer start count).uses i) := by
    funext i
    simp only [sysTakeLive, Expr.uses, Command.uses, List.any_cons, List.any_nil,
      Bool.or_false, Bool.false_or]
    cases live i <;> cases (i == buffer.index) <;> cases (i == start.index) <;>
      cases (i == count.index) <;> rfl
  have selected : ∀ i, live i = true → sysTakeLive live [start, count] [] i = true := by
    intro i hi
    simp [sysTakeLive, hi]
  let bodyIn : Nat → Bool := fun i => shift 1 live i ||
    (i == 0 || (i == start.index + 1 || i == count.index + 1))
  have tailSelected : ∀ i, bodyIn (i + 1) = true →
      sysTakeLive live [start, count] [] i = true := by
    intro i hi
    simp only [bodyIn, shift_add, Nat.add_right_cancel_iff, beq_iff_eq,
      Nat.add_one_ne_zero, decide_false, Bool.false_or] at hi
    simp only [sysTakeLive, List.any_cons, List.any_nil, Bool.or_false, Bool.false_or]
    simpa using hi
  have outputSelected : ∀ i, shift 1 live i = true → bodyIn i = true := by
    intro i hi
    simp [bodyIn, hi]
  obtain ⟨typeIndex, lookup⟩ := facts.read
  have indexEq : Wrappers.readIndexWith calls source = 3 + calls.length + source.funcs.length := by
    simp [Wrappers.readIndexWith, Module.extraIndexWith]
  rw [← takeEq] at vars safe scratch ⊢
  simp only [Command.codeWith, List.append_assoc, indexEq]
  refine wp.conseq (fun continuation result => ?_)
    (wp_take_with facts sourceHost (host := host) (targetHost := targetHost) (bodyIn := bodyIn)
      (width := 5) (cost := fun _ => 0)
      (action := (Command.read (pureSigs := pureSigs) (effectSigs := effectSigs) buffer start
        count).denote pure.funs effects env)
      selected tailSelected outputSelected depthParam positions vars at_ safe scratch cap low room
      takeFragment.1 takeFragment.2
      (fun noAbort => ⟨(resources noAbort).1, fun _ _ _ _ => by
        have := (resources noAbort).2
        simpa [Resource.PureContext.sysTakeCost] using this⟩) ?_)
  · cases result with
    | returned value finalHeap final finalLocals words trace execution after top =>
      refine .returned value finalHeap final finalLocals words trace execution after ?_
      simpa [Resource.PureContext.sysTakeCost] using top
    | trapped final message result => exact .trapped final message result
  · intro takeHeap takeStore boundLocals _ boundVars boundScratch takeAt _ boundLow boundRoom _ _
    have codeEq : readFillCode (3 + calls.length + source.funcs.length) base
        (slots.getD start.index default).loc (slots.getD count.index default).loc
        (base + Ty.bytes.width) =
        readFillCode (3 + calls.length + source.funcs.length)
          ((⟨base, .owned⟩ :: slots : List Slot).getD
            (Var.here : Var (.bytes :: context) .bytes).index default).loc
          ((⟨base, .owned⟩ :: slots : List Slot).getD (start.there (s := .bytes)).index
            default).loc
          ((⟨base, .owned⟩ :: slots : List Slot).getD (count.there (s := .bytes)).index
            default).loc
          (base + Ty.bytes.width) := by
      simp [Var.index]
    rw [codeEq]
    exact wp_read_fill_result_with (buffer := .here) (start := start.there) (count := count.there)
      facts.imports lookup valid boundVars boundScratch outputSelected
      (by simp [bodyIn, Var.index]) (by simp [shift, Var.index]) rfl
      (by simp [bodyIn, Var.index]) (by simp [bodyIn, Var.index]) takeAt boundLow
      (by simp only [Ty.width] at boundRoom ⊢; omega)

theorem command_read_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    (buffer : Var context .bytes) (start count : Var context .word) :
    CommandCodeSpecWith calls source target pure effects pool (.read buffer start count) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ depthParam positions vars at_ safe scratch cap low room ready _ _
  refine wp.conseq (fun continuation result => ?_)
    (wp_read_command_with (aborts := true) (budget := 0) facts sourceHost valid depthParam
      positions vars at_ safe scratch cap low room ready
      (fun impossible => Bool.noConfusion impossible))
  cases result with
  | returned value finalHeap final finalLocals words trace execution after top =>
    exact CommandResult.returned (result := .value (wordsBytesTy 2)) value finalHeap final
      finalLocals words trace execution after
  | trapped final message result => exact result

theorem cost_command_read_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit)
    (buffer : Var context .bytes) (start count : Var context .word) :
    CostCommandCodeSpecWith calls source target pure program pool (.read buffer start count) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ depthParam positions vars at_ safe scratch cap low room ready _ _ resources
  refine wp.conseq (fun continuation result => ?_)
    (wp_read_command_with (aborts := aborts) (budget := budget) facts sourceHost valid depthParam
      positions vars at_ safe scratch cap low room ready
      (fun hAbort => ⟨(resources hAbort).1, (resources hAbort).2.read⟩))
  cases result with
  | returned value finalHeap final finalLocals words trace execution after top =>
    exact CostCommandResult.returned (command := .read buffer start count) value
      finalHeap final finalLocals words trace _ true
      (.read _ _ _ _ buffer start count env execution) after (fun _ => top)
  | trapped final message result =>
    exact CostCommandResult.trapped final message result

end Verified.Wasi
