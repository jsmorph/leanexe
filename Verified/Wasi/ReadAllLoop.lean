import Verified.Wasi.ReadAllCode
import Verified.Wasi.ReadAllBuffer
import Verified.Wasi.ReadCall
import Verified.Wasi.ReadInvoke
import Verified.Wasi.Write

/-! The read loop of `readAll`.  Each pass reads at most 4,096 bytes into the buffer's tail, and the
loop ends at an errno, at a read of no bytes, or when more than the limit is held.  The invariant
relates the bytes held to a run of `readAllFrom` that extends to a run of `readAll`, and the number
of bytes below the limit plus one decreases at every pass that continues. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- Locals that agree with `s` outside the positions `base` to `base + 5`. -/
structure ReadAllOutside (base : Nat) (s s' : Locals) : Prop where
  params : s'.params = s.params
  length : s'.locals.length = s.locals.length
  others : ∀ j, (j < base ∨ base + 6 ≤ j) → s'.get j = s.get j

namespace ReadAllOutside

theorem refl (base : Nat) (s : Locals) : ReadAllOutside base s s :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem values {base : Nat} {s s' : Locals} (h : ReadAllOutside base s s')
    (values : List Value) : ReadAllOutside base s { s' with values } :=
  ⟨h.params, h.length, h.others⟩

theorem bounds {base i : Nat} {s s' : Locals} (h : ReadAllOutside base s s')
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hBase : base ≤ i) (hi : i < base + 6) :
    s'.params.length ≤ i ∧ i < s'.params.length + s'.locals.length := by
  rw [h.params, h.length]
  exact ⟨by omega, Locals.lt_total (by omega)⟩

theorem set {base i : Nat} {s s' : Locals} {v : Value} (h : ReadAllOutside base s s')
    (hLow : s.params.length ≤ base) (hBase : base ≤ i) (hi : i < base + 6) :
    ReadAllOutside base s (setLocal s' i v) := by
  have hParams : s'.params.length ≤ i := by rw [h.params]; omega
  refine ⟨h.params, by simp only [setLocal, List.length_set, h.length], fun j hj => ?_⟩
  rw [Locals.get_setLocal_ne hParams (by omega)]
  exact h.others j hj

theorem frame {base : Nat} {s s' : Locals} (h : ReadAllOutside base s s')
    (hHigh : base + 6 ≤ s.positions) : Frame base s s' :=
  ⟨h.params, h.length, fun j hj => ⟨h.others j (Or.inl hj), h.others _ (Or.inr (by omega))⟩,
    fun j _ => h.others _ (Or.inr (by omega))⟩

end ReadAllOutside

theorem wp_set_sum {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {a b t : Nat} {x y : UInt64} {rest : Program} {Q : Assertion α}
    (hA : s.get a = some (.i64 x)) (hB : s.get b = some (.i64 y))
    (hLow : s.params.length ≤ t) (hHigh : t < s.params.length + s.locals.length)
    (h : wp m rest Q st (setLocal s t (.i64 (x + y))) env) :
    wp m (.localGet a :: .localGet b :: .addI64 :: .localSet t :: rest) Q st s env := by
  simp only [wp_localGet_cons, Locals.get_values, hA, hB, wp_addI64_cons]
  exact wp_localSet_local (s := s) (vs := s.values) hLow hHigh h

theorem wp_set_word {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {t : Nat} {x : UInt64} {rest : Program} {Q : Assertion α}
    (hLow : s.params.length ≤ t) (hHigh : t < s.params.length + s.locals.length)
    (h : wp m rest Q st (setLocal s t (.i64 x)) env) :
    wp m (.constI64 x :: .localSet t :: rest) Q st s env := by
  simp only [wp_constI64_cons]
  exact wp_localSet_local (s := s) (vs := s.values) hLow hHigh h

/-- A nonzero word in local `e` breaks out of the enclosing block. -/
theorem wp_break_nonzero {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {e : Nat} {word : UInt64} {rest : Program} {Q : Assertion α}
    (hE : s.get e = some (.i64 word))
    (hBreak : word ≠ 0 → Q (.Break 1 st s)) (hNext : word = 0 → wp m rest Q st s env) :
    wp m (.localGet e :: .eqzI64 :: .eqz :: .br_if 1 :: rest) Q st s env := by
  simp only [wp_localGet_cons, hE, wp_eqzI64_cons, wp_eqz_cons, wp_br_if_cons]
  by_cases hZero : word = 0
  · simp (config := { decide := true }) only [hZero, ↓reduceIte]
    exact hNext hZero
  · simp (config := { decide := true }) only [hZero, ↓reduceIte]
    exact hBreak hZero

/-- A zero word in local `c` breaks out of the enclosing block. -/
theorem wp_break_zero {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {c : Nat} {word : UInt64} {rest : Program} {Q : Assertion α}
    (hC : s.get c = some (.i64 word))
    (hBreak : word = 0 → Q (.Break 1 st s)) (hNext : word ≠ 0 → wp m rest Q st s env) :
    wp m (.localGet c :: .eqzI64 :: .br_if 1 :: rest) Q st s env := by
  simp only [wp_localGet_cons, hC, wp_eqzI64_cons, wp_br_if_cons]
  by_cases hZero : word = 0
  · simp (config := { decide := true }) only [hZero, ↓reduceIte]
    exact hBreak hZero
  · simp (config := { decide := true }) only [hZero, ↓reduceIte]
    exact hNext hZero

/-- A word in local `a` below the word in local `b` breaks out of the enclosing block. -/
theorem wp_break_below {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {a b : Nat} {x y : UInt64} {rest : Program} {Q : Assertion α}
    (hA : s.get a = some (.i64 x)) (hB : s.get b = some (.i64 y))
    (hBreak : x < y → Q (.Break 1 st s)) (hNext : ¬x < y → wp m rest Q st s env) :
    wp m (.localGet a :: .localGet b :: .ltUI64 :: .br_if 1 :: rest) Q st s env := by
  simp only [wp_localGet_cons, Locals.get_values, hA, hB, wp_ltUI64_cons, wp_br_if_cons]
  by_cases hBelow : x < y
  · simp (config := { decide := true }) only [hBelow, ↓reduceIte]
    exact hBreak hBelow
  · simp (config := { decide := true }) only [hBelow, ↓reduceIte]
    exact hNext hBelow

/-- The state of the read loop: the bytes `held` and the events `prior` of a partial run, the
buffer that holds them, and the locals of the code. -/
structure ReadAllFacts {World : Type} (host : Host World) (base : Nat) (limit root : UInt64)
    (initial : Store (Observed World)) (heap0 heap : Heap) (s0 : Locals)
    (held : LeanExe.Bytes) (prior : List Event) (fuel index : Nat)
    (st : Store (Observed World)) (si : Locals) : Prop where
  rest : ReadAllRest (observedHost host) limit initial.host prior fuel index held st.host
  enough : limit.toNat + 2 ≤ fuel + held.data.size
  buffer : Heap.Buffer heap (PureTransport.erase st) root held
  small : held.data.size ≤ limit.toNat
  room : limit.toNat + 4096 ≤ capacityAt (PureTransport.erase st) root
  step : Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
    heap (PureTransport.erase st) [block (PureTransport.erase st) root]
  outside : ReadAllOutside base s0 si
  stack : si.values = s0.values
  limitLocal : si.get base = some (.i64 limit)
  rootLocal : si.get (base + 2) = some (.i64 root)
  lengthLocal : si.get (base + 3) = some (.i64 (UInt64.ofNat held.data.size))
  chunkLocal : si.get (base + 5) = some (.i64 4096)

/-- The bytes below the limit plus one, from the length local. -/
def readAllMeasure (base : Nat) (limit : UInt64) (si : Locals) : Nat :=
  match si.get (base + 3) with
  | some (.i64 length) => limit.toNat + 1 - length.toNat
  | _ => 0

theorem readAll_rep_of_buffer {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) :
    Bytes.Rep heap store root (UInt64.ofNat bytes.data.size) bytes := by
  have hFit := h.object.address
  have hCap := h.capacity
  refine ⟨?_, Or.inr h⟩
  exact UInt64.toNat_ofNat_of_lt' (by
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega)

theorem readAll_regions {World : Type} {initial final : Store World} {heap0 heap : Heap}
    {root : UInt64} {held : LeanExe.Bytes}
    (hStep : Step heap0 (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase final) [block (PureTransport.erase final) root])
    (h : Heap.Buffer heap (PureTransport.erase final) root held) :
    Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
      heap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) := by
  simpa only [Bytes.regions, ite_eq_right h.nonzero] using hStep

theorem wp_readAll_loop {World : Type} {m : Module} {host : Host World}
    {env : HostEnv (Observed World)} {base : Nat} {limit root : UInt64}
    {initial : Store (Observed World)} {heap0 heap : Heap} {s0 : Locals}
    {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.imports) (hHost : env.Satisfies m (hostSpec host))
    (hLow : s0.params.length ≤ base) (hHigh : base + 6 ≤ s0.positions)
    (hDone : ∀ (final : Store (Observed World)) (si : Locals) (result : LeanExe.Wasi.ReadResult)
      (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.returned result) final.host →
      Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Bytes.Rep heap (PureTransport.erase final) root (UInt64.ofNat result.bytes.data.size)
        result.bytes →
      ReadAllOutside base s0 si → si.values = s0.values →
      si.get (base + 1) = some (.i64 result.errno) →
      si.get (base + 2) = some (.i64 root) →
      si.get (base + 3) = some (.i64 (UInt64.ofNat result.bytes.data.size)) →
      wp m rest Q final si env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.trapped message) final.host →
      Step heap0 (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
        heap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root) →
      Q (.Trap final message))
    {st : Store (Observed World)} {sb : Locals} {held : LeanExe.Bytes} {prior : List Event}
    {fuel index : Nat}
    (facts : ReadAllFacts host base limit root initial heap0 heap s0 held prior fuel index st
      sb) :
    wp m (readAllLoopCode base ++ rest) Q st sb env := by
  have entryStack := facts.stack
  simp only [readAllLoopCode, List.singleton_append]
  refine wp_block_cons ?_
  refine wp_loop_cons (rest := [])
    (fun st si => ∃ held prior fuel index,
      ReadAllFacts host base limit root initial heap0 heap s0 held prior fuel index st si)
    (fun _ si => readAllMeasure base limit si) ⟨held, prior, fuel, index, facts⟩ ?_
  rintro st si ⟨held, prior, fuel, index, facts⟩
  have hBase := facts.buffer.object.base
  have hFit := facts.buffer.object.address
  have hBelow := facts.buffer.object.below
  have hHeap := facts.step.at_
  have hTop := hHeap.top
  have hFloor := hHeap.base
  have hRoom := facts.room
  have hSmall := facts.small
  have hEnoughBefore := facts.enough
  obtain ⟨fuel, rfl⟩ : ∃ rest, fuel = rest + 1 := ⟨fuel - 1, by omega⟩
  have hHeld : held.data.size < 4294967296 := by omega
  have hHeldNat : (UInt64.ofNat held.data.size).toNat = held.data.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hPointer : (root + UInt64.ofNat held.data.size).toNat = root.toNat + held.data.size :=
    readAll_tail_address (by omega)
  have hPointerSmall : (root + UInt64.ofNat held.data.size).toNat < 4294967296 := by omega
  have hPointerNat : (root + UInt64.ofNat held.data.size).toUInt32.toNat =
      root.toNat + held.data.size := by
    rw [Memory.toUInt32_toNat, hPointer, Nat.mod_eq_of_lt (by omega)]
  have bound := fun i (hi : base ≤ i) (hi' : i < base + 6) =>
    facts.outside.bounds hLow hHigh hi hi'
  -- The address of the read.
  rw [readAllBody, List.append_assoc]
  simp only [readAllAddressCode, List.cons_append, List.nil_append]
  have hLow1 : si.params.length ≤ base + 4 := (bound (base + 4) (by omega) (by omega)).1
  have hHigh1 := (bound (base + 4) (by omega) (by omega)).2
  refine wp_set_sum facts.rootLocal facts.lengthLocal hLow1 hHigh1 ?_
  let s1 := setLocal si (base + 4) (.i64 (root + UInt64.ofNat held.data.size))
  have outside1 : ReadAllOutside base s0 s1 := facts.outside.set hLow (by omega) (by omega)
  have get1 : ∀ j, j ≠ base + 4 → s1.get j = si.get j := fun j hj =>
    Locals.get_setLocal_ne hLow1 hj
  change wp m _ _ st s1 env
  have hChunk : (4096 : UInt32).toUInt64 = 4096 := rfl
  have hMemory : 16 ≤ st.mem.pages * 65536 := by
    change 16 ≤ (PureTransport.erase st).mem.pages * 65536
    omega
  -- The read.
  refine wp_read_call (pointer := (root + UInt64.ofNat held.data.size).toUInt32)
    (capacity := 4096) hImports hHost hMemory
    (by
      rw [hPointerNat]
      change _ ≤ (PureTransport.erase st).mem.pages * 65536
      simp only [UInt32.reduceToNat]
      omega)
    (by rw [hPointerNat]; simp only [UInt32.reduceToNat]; omega)
    (Or.inr (by rw [hPointerNat]; omega))
    (by rw [read_narrow64 _ hPointerSmall]; exact Locals.get_setLocal_same hLow1 hHigh1)
    (by rw [hChunk, get1 (base + 5) (by omega)]; exact facts.chunkLocal) ?_ ?_
  · intro final errno committed hRead hFrame hData
    rw [hChunk] at hRead
    rw [hPointerNat] at hFrame
    simp only [UInt32.reduceToNat] at hFrame
    rw [read_narrow64 _ hPointerSmall] at hData
    have hReply := hRead
    have hCommitted := ((observedHost host).read_bound hRead).1
    have hErrnoBound := ((observedHost host).read_bound hRead).2
    change committed.data.size ≤ 4096 at hCommitted
    change errno.toNat ≤ 76 at hErrnoBound
    have hRoomH : held.data.size + 4096 ≤ capacityAt (PureTransport.erase st) root := by omega
    have hStep' := readAll_tail_step facts.step facts.buffer hRoomH hFrame
    have hKept := readAll_buffer_keep facts.buffer hHeap hRoomH hFrame
    have hCapacity := readAll_capacity facts.buffer hRoomH hFrame
    simp only [readAllTestCode, wp_extendUI32_cons,
      narrow_word errno (by omega)]
    have hLow2 := (outside1.bounds hLow hHigh (i := base + 1) (by omega) (by omega)).1
    have hHigh2 := (outside1.bounds hLow hHigh (i := base + 1) (by omega) (by omega)).2
    refine wp_localSet_local (s := s1) (vs := s1.values) hLow2 hHigh2 ?_
    let s2 := setLocal s1 (base + 1) (.i64 errno)
    have outside2 : ReadAllOutside base s0 s2 := outside1.set hLow (by omega) (by omega)
    have get2 : ∀ j, j ≠ base + 1 → s2.get j = s1.get j := fun j hj =>
      Locals.get_setLocal_ne hLow2 hj
    have errno2 : s2.get (base + 1) = some (.i64 errno) := Locals.get_setLocal_same hLow2 hHigh2
    change wp m _ _ final s2 env
    refine wp_break_nonzero errno2 ?_ ?_
    · -- A read that returned an errno ends the loop with the bytes held.
      intro hFailed
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      refine hDone final { s2 with values := sb.values } ⟨errno, held⟩ _
        (facts.rest.failed hReply hFailed) (readAll_regions hStep' hKept)
        (readAll_rep_of_buffer hKept) (outside2.values _) entryStack ?_ ?_ ?_
      · simpa only [Locals.get_values] using errno2
      · rw [Locals.get_values, get2 _ (by omega), get1 _ (by omega)]
        exact facts.rootLocal
      · rw [Locals.get_values, get2 _ (by omega), get1 _ (by omega)]
        exact facts.lengthLocal
    intro hSucceeded
    subst hSucceeded
    obtain ⟨hAt, hCount⟩ := hData rfl
    have hPages : final.mem.pages = st.mem.pages := hFrame.pages
    -- The count of the read.
    simp only [wp_const_cons, wp_load32_cons, UInt32.reduceToNat, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hPages]; omega), hCount]
    simp only [wp_extendUI32_cons]
    rw [UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; omega)]
    have hLow3 := (outside2.bounds hLow hHigh (i := base + 4) (by omega) (by omega)).1
    have hHigh3 := (outside2.bounds hLow hHigh (i := base + 4) (by omega) (by omega)).2
    refine wp_localSet_local (s := s2) (vs := s2.values) hLow3 hHigh3 ?_
    let s3 := setLocal s2 (base + 4) (.i64 (UInt64.ofNat committed.data.size))
    have outside3 : ReadAllOutside base s0 s3 := outside2.set hLow (by omega) (by omega)
    have get3 : ∀ j, j ≠ base + 4 → s3.get j = s2.get j := fun j hj =>
      Locals.get_setLocal_ne hLow3 hj
    have count3 : s3.get (base + 4) = some (.i64 (UInt64.ofNat committed.data.size)) :=
      Locals.get_setLocal_same hLow3 hHigh3
    have hCountNat : (UInt64.ofNat committed.data.size).toNat = committed.data.size :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    change wp m _ _ final s3 env
    refine wp_break_zero count3 ?_ ?_
    · -- A read of no bytes ends the loop with the bytes held.
      intro hEmpty
      have hEmptyNat : committed.data.size = 0 := by
        have hZero := congrArg UInt64.toNat hEmpty
        rw [hCountNat] at hZero
        exact hZero
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      refine hDone final { s3 with values := sb.values } ⟨0, held⟩ _
        (facts.rest.ended hReply hEmptyNat) (readAll_regions hStep' hKept)
        (readAll_rep_of_buffer hKept) (outside3.values _) entryStack ?_ ?_ ?_
      · rw [Locals.get_values, get3 _ (by omega)]
        exact errno2
      · rw [Locals.get_values, get3 _ (by omega), get2 _ (by omega), get1 _ (by omega)]
        exact facts.rootLocal
      · rw [Locals.get_values, get3 _ (by omega), get2 _ (by omega), get1 _ (by omega)]
        exact facts.lengthLocal
    intro hNonempty
    have hNonemptyNat : committed.data.size ≠ 0 := by
      intro hZero
      apply hNonempty
      rw [hZero]
      rfl
    -- The new length.
    have length3 : s3.get (base + 3) = some (.i64 (UInt64.ofNat held.data.size)) := by
      rw [get3 _ (by omega), get2 _ (by omega), get1 _ (by omega)]
      exact facts.lengthLocal
    have hLow4 := (outside3.bounds hLow hHigh (i := base + 3) (by omega) (by omega)).1
    have hHigh4 := (outside3.bounds hLow hHigh (i := base + 3) (by omega) (by omega)).2
    refine wp_set_sum length3 count3 hLow4 hHigh4 ?_
    have hSum : UInt64.ofNat held.data.size + UInt64.ofNat committed.data.size =
        UInt64.ofNat (appendBytes held committed).data.size := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, hHeldNat, hCountNat, appendBytes_size,
        UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
      omega
    rw [hSum]
    let s4 := setLocal s3 (base + 3) (.i64 (UInt64.ofNat (appendBytes held committed).data.size))
    have outside4 : ReadAllOutside base s0 s4 := outside3.set hLow (by omega) (by omega)
    have get4 : ∀ j, j ≠ base + 3 → s4.get j = s3.get j := fun j hj =>
      Locals.get_setLocal_ne hLow4 hj
    have length4 : s4.get (base + 3) =
        some (.i64 (UInt64.ofNat (appendBytes held committed).data.size)) :=
      Locals.get_setLocal_same hLow4 hHigh4
    have limit4 : s4.get base = some (.i64 limit) := by
      rw [get4 _ (by omega), get3 _ (by omega), get2 _ (by omega), get1 _ (by omega)]
      exact facts.limitLocal
    have root4 : s4.get (base + 2) = some (.i64 root) := by
      rw [get4 _ (by omega), get3 _ (by omega), get2 _ (by omega), get1 _ (by omega)]
      exact facts.rootLocal
    have errno4 : s4.get (base + 1) = some (.i64 0) := by
      rw [get4 _ (by omega), get3 _ (by omega)]
      exact errno2
    have hAppendNat : (UInt64.ofNat (appendBytes held committed).data.size).toNat =
        held.data.size + committed.data.size := by
      rw [appendBytes_size]
      exact UInt64.toNat_ofNat_of_lt' (by
        rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    have hAppended := readAll_buffer_append facts.buffer hHeap hRoomH hFrame hCommitted hAt
    change wp m _ _ final s4 env
    refine wp_break_below limit4 length4 ?_ ?_
    · -- A read that brings the bytes above the limit ends the loop with them.
      intro hAbove
      have hAboveNat : limit.toNat < held.data.size + committed.data.size := by
        rw [UInt64.lt_iff_toNat_lt, hAppendNat] at hAbove
        exact hAbove
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      exact hDone final { s4 with values := sb.values } ⟨0, appendBytes held committed⟩ _
        (facts.rest.over hReply hNonemptyNat hAboveNat) (readAll_regions hStep' hAppended)
        (readAll_rep_of_buffer hAppended) (outside4.values _) entryStack
        (by simpa only [Locals.get_values] using errno4)
        (by simpa only [Locals.get_values] using root4)
        (by simpa only [Locals.get_values] using length4)
    · -- Any other read continues the loop.
      intro hWithin
      have hWithinNat : ¬limit.toNat < held.data.size + committed.data.size := by
        rw [UInt64.lt_iff_toNat_lt, hAppendNat] at hWithin
        exact hWithin
      rw [wp_br_cons]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      have hEnough := facts.enough
      refine ⟨⟨appendBytes held committed, prior ++ [.read 4096 (.returned 0 committed)], fuel,
        index + 1,
        ⟨facts.rest.next hReply hNonemptyNat hWithinNat,
          by simp only [appendBytes_size]; omega, hAppended,
          by simp only [appendBytes_size]; omega, by rw [hCapacity]; exact hRoom,
          hStep', outside4.values _, facts.stack,
          by simpa only [Locals.get_values] using limit4,
          by simpa only [Locals.get_values] using root4,
          by simpa only [Locals.get_values] using length4, ?_⟩⟩, ?_⟩
      · rw [Locals.get_values, get4 _ (by omega), get3 _ (by omega), get2 _ (by omega),
          get1 _ (by omega)]
        exact facts.chunkLocal
      · simp only [readAllMeasure, Locals.get_values, length4, facts.lengthLocal, hAppendNat,
          hHeldNat]
        omega
  · -- A trap of the read ends the loop with the trap.
    intro final message committed hRead hFrame
    rw [hChunk] at hRead
    rw [hPointerNat] at hFrame
    simp only [UInt32.reduceToNat] at hFrame
    have hRoomH : held.data.size + 4096 ≤ capacityAt (PureTransport.erase st) root := by omega
    have hStep' := readAll_tail_step facts.step facts.buffer hRoomH hFrame
    have hKept := readAll_buffer_keep facts.buffer hHeap hRoomH hFrame
    exact hTrap final message _ (facts.rest.trapped hRead) (readAll_regions hStep' hKept)

end Verified.Wasi
