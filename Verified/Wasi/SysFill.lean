import Verified.Wasi.SysWindow

/-! The code of a call that fills a window of a buffer, from the window's computation to the
errno, the count, and the buffer's root and size on the stack.  The window's length takes the
place of its start and count among the call's words, so the code tests and lowers the arguments
as a flat call or a read does with that length as the capacity and the window's address as the
buffer's root.  The buffer keeps its block: after the call the window holds the bytes that the
host wrote, or after an errno the zeros that the code stores. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## Lowered words and inputs -/

theorem lowerWords_plain : ∀ (params : List Param) (values : List UInt64)
    (buffers : List LeanExe.Bytes), params.all (fun param => !param.isWindow) = true →
    values.length = (params.map Param.argWords).sum → lowerWords params values buffers = values
  | [], values, _, _, count => by
    simp only [List.map_nil, List.sum_nil, List.length_eq_zero_iff] at count
    subst count
    rfl
  | param :: params, values, buffers, plain, count => by
    simp only [List.all_cons, Bool.and_eq_true] at plain
    simp only [List.map_cons, List.sum_cons] at count
    cases param with
    | output | iovec => simp [Param.isWindow] at plain
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      cases values with
      | nil => simp only [List.length_nil, Param.argWords, Param.argCount] at count; omega
      | cons value values =>
        simp only [lowerWords, List.headD_cons, List.tail_cons]
        rw [lowerWords_plain params values buffers plain.2
          (by simp [Param.argWords, Param.argCount] at count; omega)]
    | input | result32 | result64 | reported | record =>
      simp only [lowerWords]
      exact lowerWords_plain params values buffers plain.2
        (by simpa [Param.argWords, Param.argCount] using count)
    | subscriptions records =>
      simp only [lowerWords]
      rw [lowerWords_plain params (values.drop (argFields records).length) buffers plain.2
        (by simp [Param.argWords, Param.argCount] at count ⊢; omega), List.take_append_drop]

theorem lowerInputs_flat : ∀ (params : List Param) (values : List UInt64)
    (inputs : List LeanExe.Bytes), params.all Param.inputKind = true →
    inputs.length = params.count .input → lowerInputs params values inputs = inputs
  | [], _, inputs, _, count => by
    simp only [List.count_nil, List.length_eq_zero_iff] at count
    subst count
    rfl
  | param :: params, values, inputs, kinds, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [lowerInputs, List.headD_cons, List.tail_cons]
        rw [lowerInputs_flat params values inputs kinds.2 (by simpa [List.count_cons] using count)]
    | word32 | handle | word64 | enum32 | flags32 | flags64 | output | result32 | result64 =>
      simp only [lowerInputs]
      exact lowerInputs_flat params _ inputs kinds.2 (by simpa [List.count_cons] using count)

theorem lowerWords_length : ∀ (params : List Param) (values : List UInt64)
    (buffers : List LeanExe.Bytes), params.all Param.inputKind = true →
    values.length = (params.map Param.argWords).sum →
    (lowerWords params values buffers).length = (params.map Param.wordCount).sum
  | [], _, _, _, _ => rfl
  | param :: params, values, buffers, kinds, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    simp only [List.map_cons, List.sum_cons] at count ⊢
    cases param with
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | output =>
      simp only [lowerWords, List.length_cons]
      rw [lowerWords_length params _ _ kinds.2 (by simp [Param.argWords] at count; simp; omega)]
      simp [Param.wordCount, Param.takesBytes, Param.argCount]
      omega
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      simp only [lowerWords, List.length_cons]
      rw [lowerWords_length params _ _ kinds.2
        (by simp [Param.argWords, Param.argCount] at count; simp; omega)]
      simp [Param.wordCount, Param.takesBytes, Param.argCount]
      omega
    | input | result32 | result64 =>
      simp only [lowerWords]
      rw [lowerWords_length params _ _ kinds.2 (by simpa [Param.argWords, Param.argCount] using count)]
      simp [Param.wordCount, Param.takesBytes, Param.argCount]

theorem params_count_output {param : Param} {params : List Param} (h : param ≠ .output) :
    (param :: params).count .output = params.count .output := by
  rw [List.count_cons]
  simp [h]

/-- The lowered words of a flat call with at most one output take the window's length in place of
its start and count, from the local `length`. -/
theorem lowerLocs_held {s : Locals} {length : Nat} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64)
      (buffers : List LeanExe.Bytes),
    params.all Param.inputKind = true → params.count .output ≤ 1 →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = (params.map Param.argWords).sum →
    (params.count .output = 1 → s.get length = some (.i64 ((buffers.headD .empty).windowLength
      (windowWords params values).1 (windowWords params values).2))) →
    List.Forall₂ (fun place value => s.get place = some (.i64 value))
      (lowerLocs params locs length) (lowerWords params values buffers)
  | [], _, _, _, _, _, _, _, _ => .nil
  | param :: params, locs, values, buffers, kinds, outputs, held, count, hLength => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    simp only [List.map_cons, List.sum_cons] at count
    cases param with
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | output =>
      have none : params.count .output = 0 := by
        rw [List.count_cons] at outputs
        simp at outputs
        omega
      cases held with
      | nil => simp only [List.length_nil, List.length_cons, Param.argWords] at count; omega
      | cons first held =>
        cases held with
        | nil => simp only [List.length_nil, List.length_cons, Param.argWords] at count; omega
        | cons second held =>
          simp only [lowerLocs, lowerWords, List.drop_succ_cons, List.drop_zero, List.headD_cons,
            List.tail_cons]
          refine .cons ?_ (lowerLocs_held params _ _ buffers.tail kinds.2 (by omega) held
            (by simp [Param.argWords] at count; omega) (fun one => by omega))
          have one : (Param.output :: params).count .output = 1 := by
            rw [List.count_cons]
            simp [none]
          simpa [windowWords] using hLength one
    | input | result32 | result64 =>
      simp only [lowerLocs, lowerWords]
      exact lowerLocs_held params locs values buffers kinds.2
        (by rwa [params_count_output (by intro h; cases h)] at outputs) held
        (by simpa [Param.argWords, Param.argCount] using count) (fun one => by
          have := hLength (by rwa [params_count_output (by intro h; cases h)])
          simpa [windowWords, Param.argWords, Param.argCount] using this)
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      cases held with
      | nil => simp only [List.length_nil, Param.argWords, Param.argCount] at count; omega
      | cons first held =>
        simp only [lowerLocs, lowerWords, List.headD_cons, List.tail_cons]
        exact .cons first (lowerLocs_held params _ _ buffers kinds.2
          (by rwa [params_count_output (by intro h; cases h)] at outputs) held
          (by simp [Param.argWords, Param.argCount] at count; omega) (fun one => by
            have := hLength (by rwa [params_count_output (by intro h; cases h)])
            simpa [windowWords, Param.argWords, Param.argCount] using this))

/-- The locals of the start and the count of a flat call's window hold the window's words. -/
theorem windowLocs_held {s : Locals} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64),
    params.all Param.inputKind = true → params.count .output = 1 →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = (params.map Param.argWords).sum →
    s.get (windowLocs params locs).1 = some (.i64 (windowWords params values).1) ∧
      s.get (windowLocs params locs).2 = some (.i64 (windowWords params values).2) ∧
      (windowLocs params locs).1 ∈ locs ∧ (windowLocs params locs).2 ∈ locs
  | [], _, _, _, one, _, _ => by simp at one
  | param :: params, locs, values, kinds, one, held, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    simp only [List.map_cons, List.sum_cons] at count
    cases param with
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | output =>
      cases held with
      | nil => simp only [List.length_nil, List.length_cons, Param.argWords] at count; omega
      | cons first held =>
        cases held with
        | nil => simp only [List.length_nil, List.length_cons, Param.argWords] at count; omega
        | cons second held =>
          simp only [windowLocs, windowWords, List.headD_cons, List.tail_cons]
          exact ⟨first, second, List.mem_cons_self .., List.mem_cons_of_mem _ List.mem_cons_self⟩
    | input | result32 | result64 =>
      simp only [windowLocs, windowWords, Param.argWords, Param.argCount, List.drop_zero]
      exact windowLocs_held params locs values kinds.2
        (by rwa [params_count_output (by intro h; cases h)] at one) held
        (by simpa [Param.argWords, Param.argCount] using count)
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      cases held with
      | nil => simp only [List.length_nil, Param.argWords, Param.argCount] at count; omega
      | cons first held =>
        simp only [windowLocs, windowWords, Param.argWords, Param.argCount, List.drop_succ_cons,
          List.drop_zero]
        obtain ⟨start, count', startIn, countIn⟩ := windowLocs_held params _ _ kinds.2
          (by rwa [params_count_output (by intro h; cases h)] at one) held
          (by simp [Param.argWords, Param.argCount] at count; omega)
        exact ⟨start, count', List.mem_cons_of_mem _ startIn, List.mem_cons_of_mem _ countIn⟩

theorem flatCapacityWith_lower : ∀ (params : List Param) (values : List UInt64)
    (inputs buffers : List LeanExe.Bytes),
    params.all Param.inputKind = true → params.count .output = 1 →
    values.length = (params.map Param.argWords).sum → inputs.length = params.count .input →
    flatCapacityWith params (lowerWords params values buffers) inputs =
      some ((buffers.headD .empty).windowLength (windowWords params values).1
        (windowWords params values).2)
  | [], _, _, _, _, one, _, _ => by simp at one
  | param :: params, values, inputs, buffers, kinds, one, count, inputCount => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    simp only [List.map_cons, List.sum_cons] at count
    cases param with
    | reported | record | iovec | subscriptions => simp [Param.inputKind, Param.flatKind] at kinds
    | output => rfl
    | input =>
      cases inputs with
      | nil => simp at inputCount
      | cons input inputs =>
        simp only [lowerWords, flatCapacityWith, windowWords, Param.argWords, List.drop_zero]
        exact flatCapacityWith_lower params values inputs buffers kinds.2
          (by rwa [params_count_output (by intro h; cases h)] at one)
          (by simpa [Param.argWords] using count) (by simpa [List.count_cons] using inputCount)
    | result32 | result64 =>
      simp only [lowerWords, flatCapacityWith, windowWords, Param.argWords, Param.argCount,
        Param.takesArg, List.drop_zero, Bool.false_eq_true, ↓reduceIte]
      exact flatCapacityWith_lower params values inputs buffers kinds.2
        (by rwa [params_count_output (by intro h; cases h)] at one)
        (by simpa [Param.argWords, Param.argCount] using count)
        (by simpa [List.count_cons] using inputCount)
    | word32 | handle | word64 | enum32 | flags32 | flags64 =>
      cases values with
      | nil => simp only [List.length_nil, Param.argWords, Param.argCount] at count; omega
      | cons value values =>
        simp only [lowerWords, flatCapacityWith, windowWords, Param.argWords, Param.argCount,
          Param.takesArg, List.headD_cons, List.tail_cons, List.drop_succ_cons, List.drop_zero,
          ↓reduceIte]
        exact flatCapacityWith_lower params values inputs buffers kinds.2
          (by rwa [params_count_output (by intro h; cases h)] at one)
          (by simp [Param.argWords, Param.argCount] at count; omega)
          (by simpa [List.count_cons] using inputCount)

/-! ## The buffer after a fill -/

/-- After a frame that writes the scratch bytes and the window, which then holds `out`, the buffer
holds the splice of `out` into the window, in the same block, which the step names fresh. -/
theorem fill_rep {World : Type} {before after : Store World} {heap : Heap}
    {root size : UInt64} {buffer out : LeanExe.Bytes} {start count : UInt64}
    (rep : Bytes.Rep heap (PureTransport.erase before) root size buffer)
    (hHeap : heap.At (PureTransport.erase before))
    (hSize : out.data.size = (buffer.window start count).2)
    (hFrame : GuestFrame before after
      [ABI.scratch, (root.toNat + (buffer.window start count).1, (buffer.window start count).2)])
    (hData : ∀ (i : Nat) (hi : i < out.data.size),
      after.mem.bytes (root.toNat + (buffer.window start count).1 + i) = out.data[i]) :
    Bytes.Rep heap (PureTransport.erase after) root size
        (buffer.splice (buffer.window start count).1 out) ∧
      Step heap (PureTransport.erase before)
        (fun r => regionsDisjoint r ABI.scratch ∧
          ∀ b ∈ Bytes.regions (PureTransport.erase before) root, regionsDisjoint r b)
        heap (PureTransport.erase after) (Bytes.regions (PureTransport.erase after) root) := by
  have hWindow := buffer.window_le start count
  have hSplice := LeanExe.Bytes.splice_size (buffer := buffer)
    (first := (buffer.window start count).1) (bytes := out) (by omega)
  refine ⟨⟨by rw [hSplice]; exact rep.length_eq, ?_⟩, window_step rep hHeap hWindow hFrame⟩
  rcases rep.buffer with ⟨rfl, hEmpty⟩ | hBuffer
  · exact Or.inl ⟨rfl, by rw [hSplice, hEmpty]⟩
  · exact Or.inr (window_splice_buffer hBuffer hHeap (by omega) (by rwa [hSize]) hData)

theorem fillResult_errno (buffer : LeanExe.Bytes) (start count errno used : UInt64)
    (bytes : LeanExe.Bytes) : (FillResult.of buffer start count errno used bytes).errno = errno := by
  unfold FillResult.of
  split
  · rename_i h
    exact h.symm
  · rfl

theorem GuestFrame.ofWritesRange {World : Type} {before after : Store World} {start stop : Nat}
    (h : Memory.WritesRange before after start stop) :
    GuestFrame before after [(start, stop - start)] := by
  refine ⟨congrArg (fun store : Store World => store.mapHost (fun _ => ())) h.1, h.2.1, ?_⟩
  intro address hOutside
  apply h.2.2
  have hRange := hOutside _ (List.mem_singleton_self _)
  dsimp only [InRange] at hRange
  omega

theorem GuestFrame.refl {World : Type} (store : Store World) (writable : List (Nat × Nat)) :
    GuestFrame store store writable :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- The store after a fill's call and its zero fill: the frame of the window, and in the window the
bytes of the output on errno 0, or zeros after an errno.  The buffer holds the fill's result. -/
theorem fill_after {World : Type} {initial final final' : Store World} {heap : Heap}
    {root size : UInt64} {buffer out : LeanExe.Bytes} {start count errno used : UInt64}
    (rep : Bytes.Rep heap (PureTransport.erase initial) root size buffer)
    (hHeap : heap.At (PureTransport.erase initial))
    (hFrame : GuestFrame initial final
      [ABI.scratch, (root.toNat + (buffer.window start count).1, (buffer.window start count).2)])
    (hOut : errno = 0 → out.data.size = (buffer.window start count).2 ∧
      ∀ (i : Nat) (hi : i < out.data.size),
        final.mem.bytes (root.toNat + (buffer.window start count).1 + i) = out.data[i])
    (hSame : errno = 0 → final' = final)
    (hZeros : errno ≠ 0 →
      Memory.WritesRange final final' (root.toNat + (buffer.window start count).1)
        (root.toNat + (buffer.window start count).1 + (buffer.window start count).2) ∧
      ∀ i, i < (buffer.window start count).2 →
        final'.mem.bytes (root.toNat + (buffer.window start count).1 + i) = 0) :
    Bytes.Rep heap (PureTransport.erase final') root size
        (FillResult.of buffer start count errno used out).buffer ∧
      Step heap (PureTransport.erase initial)
        (fun r => regionsDisjoint r ABI.scratch ∧
          ∀ b ∈ Bytes.regions (PureTransport.erase initial) root, regionsDisjoint r b)
        heap (PureTransport.erase final') (Bytes.regions (PureTransport.erase final') root) := by
  by_cases hZero : errno = 0
  · obtain rfl := hSame hZero
    obtain ⟨hSize, hData⟩ := hOut hZero
    simp only [FillResult.of, hZero, ite_true]
    exact fill_rep rep hHeap hSize hFrame hData
  · obtain ⟨writes, zeros⟩ := hZeros hZero
    simp only [FillResult.of, hZero, ite_false, LeanExe.Bytes.clear]
    have hFrame' : GuestFrame initial final'
        [ABI.scratch, (root.toNat + (buffer.window start count).1,
          (buffer.window start count).2)] := by
      refine hFrame.trans ((GuestFrame.ofWritesRange writes).weaken fun region member => ?_)
      rw [List.mem_singleton] at member
      subst member
      exact List.mem_cons_of_mem _ (by simp)
    refine fill_rep rep hHeap (LeanExe.Bytes.zeros_size _) hFrame' fun i hi => ?_
    rw [LeanExe.Bytes.zeros_get]
    exact zeros i (by rwa [LeanExe.Bytes.zeros_size] at hi)

/-- The code of a flat call that fills the window of the buffer whose root and size lie in the two
locals from `rootLocal`, from the words and the inputs in their locals to the errno, the count, and
the buffer's root and size on the stack.  A rejected request and an errno of the host leave the
window's bytes 0. -/
theorem wp_sys_flat_fill_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {env : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    {call : LeanExe.Wasi.Call} {locs : List Nat} {values : List UInt64}
    {inputLocs : List Nat} {inputs : List (UInt64 × LeanExe.Bytes)}
    {rootLocal : Nat} {root size : UInt64} {buffer : LeanExe.Bytes}
    {s : Locals} {base : Nat} {rest : Program} {Q : Assertion (Observed World)}
    (hHost : env.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hKinds : call.params.all Param.inputKind = true) (hOutput : call.params.count .output = 1)
    (hResults : call.params.countP Param.isResult ≤ 1)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.argWords)
    (hLocs : ∀ place ∈ locs, place < base)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hInputLocs : ∀ place ∈ inputLocs, place + 2 ≤ base)
    (hInputReps : ∀ input ∈ inputs, ∃ length,
      Bytes.Rep heap (PureTransport.erase initial) input.1 length input.2 ∧
        ∀ r ∈ Bytes.regions (PureTransport.erase initial) input.1, regionsDisjoint r ABI.scratch)
    (hInputApart : ∀ input ∈ inputs, ∀ b ∈ Bytes.regions (PureTransport.erase initial) root,
      regionsDisjoint (input.1.toNat, input.2.data.size) b)
    (hRoot : s.get rootLocal = some (.i64 root))
    (hSize : s.get (rootLocal + 1) = some (.i64 size)) (hRootBelow : rootLocal + 2 ≤ base)
    (hRep : Bytes.Rep heap (PureTransport.erase initial) root size buffer)
    (hHeap : heap.At (PureTransport.erase initial))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (lowerWords call.params values [buffer])
          (inputs.map Prod.snd)) Action.pure) initial.host trace (.returned reply) final.host →
      Step heap (PureTransport.erase initial)
        (fun r => regionsDisjoint r ABI.scratch ∧
          ∀ b ∈ Bytes.regions (PureTransport.erase initial) root, regionsDisjoint r b)
        heap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap (PureTransport.erase final) root size
        (flatFill call.params values buffer reply).buffer →
      LocalsOutside s finalLocals base 6 →
      wp target rest Q final { finalLocals with values :=
        [Value.i64 size, .i64 root, .i64 (flatFill call.params values buffer reply).count,
          .i64 reply.errno] ++ s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (lowerWords call.params values [buffer])
          (inputs.map Prod.snd)) Action.pure) initial.host trace (.trapped message) final.host →
      Q (.Trap final message)) :
    wp target (sysFlatFillCodeWith calls call locs inputLocs rootLocal base ++ rest) Q initial s
      env := by
  have hPositions : base + 6 ≤ s.params.length + s.locals.length := by
    have := hHigh
    simp only [Locals.positions] at this
    omega
  have hOutputs : call.params.count .output ≤ 1 := by omega
  have hInputCount' : inputs.length = call.params.count .input := by
    rw [hInputCount, Call.inputCount_of_inputKind hKinds]
  have hArgWords : values.length = (call.params.map Param.argWords).sum := hCount
  obtain ⟨hStartLocal, hCountLocal, hStartIn, hCountIn⟩ :=
    windowLocs_held call.params locs values hKinds hOutput hHeld hArgWords
  have hStartBelow := hLocs _ hStartIn
  have hCountBelow := hLocs _ hCountIn
  obtain ⟨hFirst, hLength, hLengthEq⟩ := window_words hRep.length_eq
    (windowWords call.params values).1 (windowWords call.params values).2
  obtain ⟨_, _, hAddrNat, _, hFits, hMem, hSep⟩ := window_at hRep hHeap
    (windowWords call.params values).1 (windowWords call.params values).2
  have hWindowLe := buffer.window_le (windowWords call.params values).1
    (windowWords call.params values).2
  generalize hP : root + windowFirstWord size (windowWords call.params values).1 = P
    at hAddrNat hFits hMem hSep
  generalize hLw : windowLengthWord size (windowWords call.params values).1
    (windowWords call.params values).2 = Lw at hFits hMem hSep hLength hLengthEq
  generalize hFirstNat : (buffer.window (windowWords call.params values).1
    (windowWords call.params values).2).1 = first at hFirst hAddrNat hWindowLe
  generalize hLengthNat : (buffer.window (windowWords call.params values).1
    (windowWords call.params values).2).2 = length at hLength hWindowLe
  have hLowered := lowerWords_length call.params values [buffer] hKinds hArgWords
  have hCapacity := flatCapacityWith_lower call.params values (inputs.map Prod.snd) [buffer] hKinds
    hOutput hArgWords (by rw [List.length_map]; exact hInputCount')
  simp only [List.headD_cons] at hCapacity
  rw [← hLengthEq] at hCapacity
  simp only [sysFlatFillCodeWith, List.append_assoc]
  refine wp_window_code hRoot hSize hStartLocal hCountLocal (by omega) (by omega) (by omega)
    (by omega) ?_
  intro s1 outside1 values1 getP getL
  rw [hP] at getP
  rw [hLw] at getL
  have held1 := held_transfer hHeld fun place member =>
    outside1.others place (Or.inl (by have := hLocs place member; omega))
  have inputs1 := inputsHeld_transfer hInputs fun place member =>
    ⟨outside1.others place (Or.inl (by have := hInputLocs place member; omega)),
      outside1.others (place + 1) (Or.inl (by have := hInputLocs place member; omega))⟩
  have lowered1 := lowerLocs_held (s := s1) (length := base + 2) call.params locs values [buffer]
    hKinds hOutputs held1 hArgWords (fun _ => by rw [getL, hLengthEq]; rfl)
  refine wp_sys_reject_inputs call.params (lowerLocs call.params locs (base + 2))
    (lowerWords call.params values [buffer]) inputLocs inputs s1 _ Q hKinds lowered1
    (by rw [hLowered, ← Call.wordCount_of_inputKind hKinds]; rfl) inputs1 hInputCount' ?_
  generalize hRejectEq : rejectArgs call.params (flatArgsWith call.params
    (lowerWords call.params values [buffer]) (inputs.map Prod.snd)) = reject
  have hPsmall : P.toNat < 4294967296 := by have := hFits; omega
  have hMemory : 16 ≤ initial.mem.pages * 65536 := by
    have hBase := hHeap.base
    have hBound := hHeap.top
    change 16 ≤ (PureTransport.erase initial).mem.pages * 65536
    omega
  have hWindowFrame : ∀ final : Store (Observed World),
      GuestFrame initial final [ABI.scratch, (P.toNat, Lw.toNat)] →
      GuestFrame initial final [ABI.scratch, (root.toNat + first, length)] := by
    intro final frame
    rw [hAddrNat, hLength] at frame
    exact frame
  -- The zero fill, the pushes, and the result, from the store after the call.
  have afterCall : ∀ (final : Store (Observed World)) (sF : Locals) (trace : List Event)
      (reply : Reply),
      Exec (observedHost host)
        (.sys call (flatArgsWith call.params (lowerWords call.params values [buffer])
          (inputs.map Prod.snd)) Action.pure) initial.host trace (.returned reply) final.host →
      GuestFrame initial final [ABI.scratch, (root.toNat + first, length)] →
      (reply.errno = 0 → (resultBytes call.params reply 0).data.size = length ∧
        ∀ (i : Nat) (hi : i < (resultBytes call.params reply 0).data.size),
          final.mem.bytes (root.toNat + first + i) = (resultBytes call.params reply 0).data[i]) →
      LocalsOutside s sF base 6 → sF.values = s.values →
      sF.get base = some (.i64 reply.errno) → sF.get (base + 1) = some (.i64 P) →
      sF.get (base + 2) = some (.i64 Lw) →
      sF.get (base + 3) = some (.i64 (flatFill call.params values buffer reply).count) →
      wp target (fillTailCode rootLocal base ++ rest) Q final sF env := by
    intro final sF trace reply execution frame output outsideF valuesF errnoF addressF lengthF
      countF
    have pagesF : final.mem.pages = initial.mem.pages := frame.pages
    refine wp_fill_tail errnoF addressF lengthF countF
      (by rw [outsideF.others _ (by omega)]; exact hRoot)
      (by rw [outsideF.others _ (by omega)]; exact hSize) (by omega)
      (by rw [outsideF.params]; omega) (by rw [outsideF.params, outsideF.length]; omega)
      hFits (by rw [pagesF]; exact hMem) ?_
    intro final' s' same zeros outside' values'
    have hHost' : final'.host = final.host := by
      by_cases hZero : reply.errno = 0
      · rw [same hZero]
      · have writes := (zeros hZero).1
        rw [writes.1]
    obtain ⟨hRep', hStep'⟩ := fill_after (used := fillCount (resultWords call.params reply 0)
        (buffer.windowLength (windowWords call.params values).1
          (windowWords call.params values).2))
      hRep hHeap (by rw [hFirstNat, hLengthNat]; exact frame)
      (fun zero => by rw [hFirstNat, hLengthNat]; exact output zero) same
      (fun nonzero => by
        obtain ⟨writes, zeroBytes⟩ := zeros nonzero
        rw [hFirstNat, hLengthNat]
        rw [hAddrNat, hLength] at writes
        refine ⟨writes, fun i hi => ?_⟩
        have := zeroBytes i (by rw [hLength]; exact hi)
        rwa [hAddrNat] at this)
    rw [valuesF]
    exact hNext final' s' trace reply (by rw [hHost']; exact execution) hStep' hRep'
      (outsideF.trans (outside'.widen (by omega) (by omega)))
  simp only [List.cons_append, List.nil_append]
  have hLow1 : s1.params.length ≤ base := by rw [outside1.params]; exact hLow
  have hHigh1 : base + 5 < s1.params.length + s1.locals.length := by
    rw [outside1.params, outside1.length]; omega
  refine wp_localSet_local hLow1 (by omega) ?_
  let s2 := setLocal { s1 with values := s1.values } base (.i64 reject)
  have hLow2 : s2.params.length ≤ base + 3 := by simp only [s2, setLocal]; omega
  have hHigh2 : base + 3 < s2.params.length + s2.locals.length := by
    simp only [s2, setLocal, List.length_set]; omega
  refine wp_set_word hLow2 hHigh2 ?_
  let s3 := setLocal s2 (base + 3) (.i64 0)
  have get3 : ∀ j, s3.get j = if j = base + 3 then some (.i64 0)
      else if j = base then some (.i64 reject) else s1.get j := by
    intro j
    by_cases h3 : j = base + 3
    · subst h3
      simp only [ite_true]
      exact Locals.get_setLocal_same hLow2 hHigh2
    · rw [ite_eq_right h3, Locals.get_setLocal_ne hLow2 h3]
      by_cases h0 : j = base
      · subst h0
        simp only [ite_true]
        exact Locals.get_setLocal_same (s := { s1 with values := s1.values }) hLow1 (by omega)
      · rw [ite_eq_right h0]
        exact Locals.get_setLocal_ne (s := { s1 with values := s1.values }) hLow1 h0
  have outside3 : LocalsOutside s s3 base 6 := by
    refine ⟨outside1.params, by simp only [s3, s2, setLocal, List.length_set]; exact outside1.length,
      fun j hj => ?_⟩
    rw [get3, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact outside1.others j (by omega)
  have values3 : s3.values = s.values := values1
  have errno3 : s3.get base = some (.i64 reject) := by rw [get3]; simp
  have address3 : s3.get (base + 1) = some (.i64 P) := by rw [get3]; simpa using getP
  have length3 : s3.get (base + 2) = some (.i64 Lw) := by rw [get3]; simpa using getL
  have count3 : s3.get (base + 3) = some (.i64 0) := by rw [get3]; simp
  have below3 : ∀ j, j < base → s3.get j = s.get j := fun j hj =>
    outside3.others j (Or.inl hj)
  change wp _ _ _ _ s3 _
  simp only [wp_localGet_cons, errno3, wp_eqzI64_cons]
  refine wp_iff_cons rfl ?_
  by_cases hAccepted : reject = 0
  · rw [ite_eq_left (by simp [hAccepted] : (if reject = 0 then (1 : UInt32) else 0) ≠ 0)]
    have hRejectZero : call.reject (flatArgsWith call.params (lowerWords call.params values [buffer])
        (inputs.map Prod.snd)) = 0 := by
      change rejectArgs call.params _ = 0
      rw [hRejectEq]; exact hAccepted
    have held3 := held_transfer hHeld fun place member => below3 place (hLocs place member)
    have lowered3 := lowerLocs_held (s := s3) (length := base + 2) call.params locs values [buffer]
      hKinds hOutputs held3 hArgWords (fun _ => by rw [length3, hLengthEq]; rfl)
    have inputs3 := inputsHeld_transfer hInputs fun place member =>
      ⟨below3 place (by have := hInputLocs place member; omega),
        below3 (place + 1) (by have := hInputLocs place member; omega)⟩
    have facts := fun input (member : input ∈ inputs) => input_at hHeap (hInputReps input member)
    refine wp_sys_flat_call_inputs_with (rootLocal := base + 1) (root := P) hImports hHost hCall
      hKinds hOutputs (by omega) hRejectZero lowered3
      (by rw [hLowered]; rfl) inputs3 hInputCount address3
      hPsmall hMemory (fun capacity found => by
        rw [hCapacity] at found
        cases found
        exact ⟨hMem, by have := hFits; omega,
          hSep.imp_right fun zero => ⟨by rw [zero.1]; rfl, zero.2⟩⟩)
      (fun input member => (facts input member).1)
      (fun input member => ⟨(facts input member).2, fun capacity found => by
        rw [hCapacity] at found
        cases found
        rcases hRep.buffer with ⟨rfl, hEmpty⟩ | hBuffer
        · have hZeroLength : Lw.toNat = 0 := by omega
          have hFirstZero : first = 0 := by omega
          have hPZero : P.toNat = 0 := by rw [hAddrNat, hFirstZero]; rfl
          simp only [LeanExe.Runtime.regionsDisjoint, hZeroLength, hPZero]
          omega
        · have apart := hInputApart input member _
            (by simp [Bytes.regions, hBuffer.nonzero] : block (PureTransport.erase initial) root ∈
              Bytes.regions (PureTransport.erase initial) root)
          have hBase := hBuffer.object.base
          have hCap := hBuffer.capacity
          simp only [block, LeanExe.Runtime.regionsDisjoint] at apart ⊢
          rw [hAddrNat, hLength]
          omega⟩) ?_ ?_
    · intro after errno outputs hSys hFrame hShown
      have hFrame' := flat_frame_cover_inputs (capacity := Lw.toNat) hKinds hOutputs (by omega)
        hInputCount' hPsmall (fun value found => by rw [hCapacity] at found; cases found; rfl)
        hFrame
      have hBound := (observedHost host).sys_bound hSys
      have hErrno : errno.toNat ≤ 76 := hBound.2
      have hSizes : outputs.map (fun output => output.data.size) =
          outputSizesOf call.params (host.reported initial.host.world call)
            (flatArgsWith call.params (lowerWords call.params values [buffer])
              (inputs.map Prod.snd)) := hBound.1
      have hMemoryAfter : 16 ≤ after.mem.pages * 65536 := by rw [hFrame.pages]; exact hMemory
      have hExec : Exec (observedHost host)
          (.sys call (flatArgsWith call.params (lowerWords call.params values [buffer])
            (inputs.map Prod.snd)) Action.pure) initial.host
          [.sys call (flatArgsWith call.params (lowerWords call.params values [buffer])
            (inputs.map Prod.snd)) (.returned errno outputs)]
          (.returned (sysReply errno outputs)) after.host :=
        .sys_return hRejectZero hSys (.pure after.host _)
      simp only [wp_extendUI32_cons, sys_extend_errno hErrno]
      have hLow3 : s3.params.length ≤ base := by rw [outside3.params]; exact hLow
      have hHigh3 : base + 5 < s3.params.length + s3.locals.length := by
        rw [outside3.params, outside3.length]; omega
      refine wp_localSet_local hLow3 (by omega) ?_
      let s4 := setLocal { s3 with values := s3.values } base (.i64 errno)
      have get4 : ∀ j, j ≠ base → s4.get j = s3.get j := fun j hj =>
        Locals.get_setLocal_ne (s := { s3 with values := s3.values }) hLow3 hj
      have errno4 : s4.get base = some (.i64 errno) :=
        Locals.get_setLocal_same (s := { s3 with values := s3.values }) hLow3 (by omega)
      have outside4 : LocalsOutside s s4 base 6 :=
        (outside3.values s3.values).set hLow le_rfl (by omega)
      change wp _ _ _ _ s4 _
      simp only [wp_localGet_cons, errno4, wp_eqzI64_cons]
      refine wp_iff_cons rfl ?_
      by_cases hZero : errno = 0
      · rw [ite_eq_left (by simp [hZero] : (if errno = 0 then (1 : UInt32) else 0) ≠ 0)]
        have hReply : sysReply errno outputs = ⟨errno, outputs⟩ := by simp [sysReply, hZero]
        obtain ⟨hOutAt, hOutSize⟩ := flat_output_at_inputs (errno := errno) call.params
          (lowerWords call.params values [buffer]) inputs outputs 0 Lw hKinds hOutputs
          hInputCount' (hShown hZero) hSizes hCapacity
        rw [read_narrow64 P hPsmall] at hOutAt
        refine wp_sys_loads_inputs (errno := errno) hMemoryAfter call.params
          (lowerWords call.params values [buffer]) inputs 0 (base + 3) outputs _ _ _ hKinds
          hOutputs (by omega) hInputCount' (hShown hZero) hSizes
          (by rw [outside4.params]; omega) (by rw [outside4.params, outside4.length]; omega) ?_
        intro sL outsideL heldL
        have outsideL' : LocalsOutside s sL base 6 :=
          outside4.trans (outsideL.widen (by omega) (by omega))
        have keepL : ∀ j, j ≠ base + 3 → sL.get j = s4.get j := fun j hj =>
          outsideL.others j (by omega)
        have hWords := resultWords_length (sysReply errno outputs) call.params 0
        have count5 : ∀ s5 : Locals, LocalsOutside sL s5 (base + 3) 1 → s5.values = s.values →
            s5.get (base + 3) = some (.i64 (flatFill call.params values buffer
              (sysReply errno outputs)).count) →
            wp target (fillTailCode rootLocal base ++ rest) Q after s5 env := by
          intro s5 outside5 values5 count5
          refine afterCall after _ _ (sysReply errno outputs) hExec (hWindowFrame after hFrame')
            (fun _ => ?_) (outsideL'.trans (outside5.widen (by omega) (by omega))) values5
            ?_ ?_ ?_ count5
          · rw [hReply]
            refine ⟨by rw [hOutSize, hLength], fun i hi => ?_⟩
            have := hOutAt.contents i hi
            rwa [hAddrNat] at this
          · rw [outside5.others _ (by omega), keepL _ (by omega)]
            simpa [sysReply, hZero] using errno4
          · rw [outside5.others _ (by omega), keepL _ (by omega), get4 _ (by omega)]
            exact address3
          · rw [outside5.others _ (by omega), keepL _ (by omega), get4 _ (by omega)]
            exact length3
        have hLowL : sL.params.length ≤ base + 3 := by rw [outsideL'.params]; omega
        have hHighL : base + 3 < sL.params.length + sL.locals.length := by
          rw [outsideL'.params, outsideL'.length]; omega
        have lengthL : sL.get (base + 2) = some (.i64 Lw) := by
          rw [keepL _ (by omega), get4 _ (by omega)]
          exact length3
        by_cases hNoWord : call.params.countP Param.isResult = 0
        · simp only [fillCountCode, hNoWord, ite_true, List.nil_append, wp_localGet_cons,
            Locals.get_values, lengthL]
          refine wp_localSet_local hLowL hHighL ?_
          simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
          refine count5 _
            (((LocalsOutside.refl sL _ 1).values _ |>.set hLowL le_rfl (by omega)).values _)
            (by simp only [List.take_zero, List.nil_append, List.drop_zero]; exact values1) ?_
          rw [Locals.get_values,
            Locals.get_setLocal_same (s := { sL with values := s4.values }) hLowL hHighL]
          have hEmpty : resultWords call.params (sysReply errno outputs) 0 = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [hWords, hNoWord]
          simp only [flatFill]
          rw [hEmpty, hReply]
          simp only [FillResult.of, hZero, ite_true, fillCount, ← hLengthEq]
        · have hOne : call.params.countP Param.isResult = 1 := by omega
          have wordL := heldL 0 (by omega)
          simp only [Nat.add_zero] at wordL
          simp only [fillCountCode, hNoWord, ite_false, List.append_assoc, List.cons_append,
            List.nil_append]
          refine wp_min_code wordL lengthL ?_
          refine wp_localSet_local hLowL hHighL ?_
          simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
          refine count5 _
            (((LocalsOutside.refl sL _ 1).values _ |>.set hLowL le_rfl (by omega)).values _)
            (by simp only [List.take_zero, List.nil_append, List.drop_zero]; exact values1) ?_
          rw [Locals.get_values,
            Locals.get_setLocal_same (s := { sL with values := s4.values }) hLowL hHighL]
          obtain ⟨word, hSingle⟩ : ∃ word,
              resultWords call.params (sysReply errno outputs) 0 = [word] := by
            match hList : resultWords call.params (sysReply errno outputs) 0, hWords with
            | [word], _ => exact ⟨word, rfl⟩
            | [], h => simp at h; omega
            | _ :: _ :: _, h => simp at h; omega
          simp only [flatFill]
          rw [hReply] at hSingle ⊢
          simp only [hSingle, List.getD_cons_zero] at wordL ⊢
          simp only [FillResult.of, hZero, ite_true, fillCount, ← hLengthEq, readLength_eq_min]
      · rw [ite_eq_right (by simp [hZero] : ¬((if errno = 0 then (1 : UInt32) else 0) ≠ 0))]
        simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
        have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, hZero]
        refine afterCall after _ _ (sysReply errno outputs) hExec (hWindowFrame after hFrame')
          (fun zero => absurd (by simpa [hReply] using zero) hZero) (outside4.values _)
          (by simp only [List.take_zero, List.nil_append, List.drop_zero]; exact values1)
          (by rw [Locals.get_values, hReply]; exact errno4) ?_ ?_ ?_
        · rw [Locals.get_values, get4 _ (by omega)]
          exact address3
        · rw [Locals.get_values, get4 _ (by omega)]
          exact length3
        · rw [Locals.get_values, get4 _ (by omega), count3]
          simp [flatFill, FillResult.of, hReply, hZero]
    · intro final message outputs hSys _
      exact hTrap final message _ (.sys_trap hRejectZero hSys)
  · rw [ite_eq_right (by simp [hAccepted] : ¬((if reject = 0 then (1 : UInt32) else 0) ≠ 0))]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero]
    have hReject : call.reject (flatArgsWith call.params (lowerWords call.params values [buffer])
        (inputs.map Prod.snd)) ≠ 0 := by
      change rejectArgs call.params _ ≠ 0
      rw [hRejectEq]; exact hAccepted
    have hReply : (⟨call.reject (flatArgsWith call.params (lowerWords call.params values [buffer])
        (inputs.map Prod.snd)), []⟩ : Reply) = ⟨reject, []⟩ := by
      change (⟨rejectArgs call.params _, []⟩ : Reply) = _
      rw [hRejectEq]
    have hExecReject : Exec (observedHost host)
        (.sys call (flatArgsWith call.params (lowerWords call.params values [buffer])
          (inputs.map Prod.snd)) Action.pure) initial.host [] (.returned ⟨reject, []⟩)
        initial.host := by
      rw [← hReply]
      exact .sys_reject hReject (.pure initial.host _)
    refine afterCall initial _ [] ⟨reject, []⟩ hExecReject (GuestFrame.refl _ _)
      (fun zero => absurd zero hAccepted)
      (outside3.values _) values3 errno3 address3 length3 ?_
    rw [count3]
    simp [flatFill, FillResult.of, hAccepted]


end Verified.Wasi
