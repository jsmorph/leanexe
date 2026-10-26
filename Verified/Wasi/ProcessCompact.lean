import Verified.Wasi.ProcessMemory
import Verified.Wasi.CompactHeap
import Verified.Wasi.PurePrefix

/-! The process state between steps, and the compaction in the process module. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

/-- The process state `current` between steps: the locals from position 0 hold its words, which
represent it with the literal pool intact; the heap has no free block and ends between `base` and
`base` plus the state's copy cost; local `processAux state` holds `base`, which lies above the
reserved area and the literal pool. -/
structure ProcessStored {World : Type} (target : Wasm.Module) (state : Ty)
    (pool : Bytes.LiteralPool) (base : UInt64) (current : ProcessStep state.denote)
    (store : Store (Observed World)) (locals : Locals) : Prop where
  represented : ∃ heap words,
    ProcessMemory (processResultTy state) pool heap (PureTransport.erase store)
      words (processValue state current) ∧
    LocalsHold locals 0 (processResultTy state).types words ∧
    heap.free = [] ∧ base.toNat ≤ heap.top.toNat ∧
    heap.top.toNat ≤ base.toNat + state.copyCost current.state
  base : locals.get (processAux state) = some (.i64 base)
  low : 4096 ≤ base.toNat
  pool : ∀ region ∈ pool.regions, region.1 + region.2 ≤ base.toNat
  params : locals.params = []
  positions : locals.positions = processPositions state
  cap : (PureTransport.erase store).memoryCap target 0 ≤ 65535

theorem ProcessStored.parts {World : Type} {target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {current : ProcessStep state.denote}
    {store : Store (Observed World)} {locals : Locals}
    (stored : ProcessStored target state pool base current store locals) :
    ∃ heap stateWords,
      ProcessMemory state pool heap (PureTransport.erase store) stateWords current.state ∧
      LocalsHold locals 2 state.types stateWords ∧
      locals.get 0 = some (.i64 (boolWord current.running)) ∧
      heap.free = [] ∧ base.toNat ≤ heap.top.toNat ∧
      heap.top.toNat ≤ base.toNat + state.copyCost current.state := by
  obtain ⟨heap, words, memory, held, free, low, high⟩ := stored.represented
  obtain ⟨stateWords, wordsEq, _⟩ := processValue_rep.mp memory.rep
  have dropped : words.drop 2 = stateWords := by simp [wordsEq]
  have stateMemory : ProcessMemory state pool heap (PureTransport.erase store)
      stateWords current.state := by
    simpa only [dropped] using memory.state
  have split := (LocalsHold.append (s := locals) (loc := 0)
    (tys1 := [.i64, .i64]) (tys2 := state.types)
    (first := [.i64 (boolWord current.running), .i64 current.status])
    (second := stateWords) rfl).mp
      (by simpa only [processResult_types, wordsEq] using held)
  refine ⟨heap, stateWords, stateMemory, ?_, ?_, free, low, high⟩
  · simpa only [List.length_cons, List.length_nil, Nat.zero_add] using split.2
  · have first := split.1 0 (by simp)
    change locals.get 0 = some (.i64 (boolWord current.running)) at first
    exact first

theorem ProcessStored.status {World : Type} {target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {current : ProcessStep state.denote}
    {store : Store (Observed World)} {locals : Locals}
    (stored : ProcessStored target state pool base current store locals) :
    locals.get 1 = some (.i64 current.status) := by
  obtain ⟨heap, words, memory, held, _⟩ := stored.represented
  obtain ⟨stateWords, wordsEq, _⟩ := processValue_rep.mp memory.rep
  have split := (LocalsHold.append (s := locals) (loc := 0)
    (tys1 := [.i64, .i64]) (tys2 := state.types)
    (first := [.i64 (boolWord current.running), .i64 current.status])
    (second := stateWords) rfl).mp
      (by simpa only [processResult_types, wordsEq] using held)
  have status := split.1 1 (by simp)
  change locals.get 1 = some (.i64 current.status) at status
  exact status

theorem ProcessStored.values {World : Type} {target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {current : ProcessStep state.denote}
    {store : Store (Observed World)} {locals : Locals} (values : List Value)
    (stored : ProcessStored target state pool base current store locals) :
    ProcessStored target state pool base current store { locals with values } :=
  { represented := stored.represented
    base := stored.base
    low := stored.low
    pool := stored.pool
    params := stored.params
    positions := stored.positions
    cap := stored.cap }

/-- A step from a heap with no free block leaves the top at or above the old one: the region from
the end of the reserved area to the old top survives it. -/
theorem _root_.Verified.Step.top_le {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (step : Step heap store keep heap' store' fresh) (at_ : heap.At store) (free : heap.free = [])
    (hKeep : keep (4096, heap.top.toNat - 4096)) : heap.top.toNat ≤ heap'.top.toNat := by
  have hBase := at_.base
  have hBase' := step.at_.base
  by_cases hEq : heap.top.toNat = 4096
  · omega
  · have hRegion : heap.Region (4096, heap.top.toNat - 4096) :=
      ⟨by simp only; omega, fun node member => by rw [free] at member; exact nomatch member⟩
    obtain ⟨_, hRegion', _⟩ := step.keeps _ hRegion (by simp only; omega) hKeep
    have := hRegion'.below
    simp only at this
    omega

/-- The literal pool lies below the top of a heap that keeps it static. -/
theorem _root_.Verified.Bytes.LiteralPool.Static.below {pool : Bytes.LiteralPool} {heap : Heap}
    {store : Store Unit} (h : pool.Static heap store) :
    ∀ region ∈ pool.regions, region.1 + region.2 ≤ heap.top.toNat := by
  intro region member
  by_cases hEmpty : pool.payload = []
  · simp [Bytes.LiteralPool.regions, hEmpty] at member
  · simp only [Bytes.LiteralPool.regions, hEmpty, ↓reduceIte, List.mem_singleton] at member
    subst member
    exact (h.resolve_left hEmpty).2.below

theorem scratch_apart_above (n : Nat) : regionsDisjoint (4096, n) ABI.scratch := by
  simp only [regionsDisjoint, ABI.scratch]
  omega

/-- The memory facts of a call's result: the result represents its value, the call kept the
literal pool, and the result's blocks lie apart from the pool. -/
theorem ProcessMemory.called {oldType resultType : Ty} {pool : Bytes.LiteralPool}
    {heap middleHeap : Heap} {initial middle : Store Unit}
    {oldWords resultWords : List Value} {oldValue : oldType.denote}
    {resultValue : resultType.denote}
    (current : ProcessMemory oldType pool heap initial oldWords oldValue)
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (called : Step heap initial (fun region => regionsDisjoint region ABI.scratch)
      middleHeap middle (resultType.blocks middle resultWords resultValue))
    (resultRep : resultType.Rep .owned middleHeap middle resultWords resultValue) :
    ProcessMemory resultType pool middleHeap middle resultWords resultValue := by
  obtain ⟨middleStatic, poolFresh⟩ := current.static.step called poolScratch
  exact ⟨called.at_, resultRep, middleStatic, poolFresh⟩

/-- The process memory and the base facts after the compaction: the pool, which lies below the
base, keeps its bytes and its region, and lies apart from the state's blocks, which lie at or
above the base. -/
theorem ProcessMemory.compacted {state : Ty} {pool : Bytes.LiteralPool} {heap heap' : Heap}
    {store store' : Store Unit} {words stateWords : List Value} {value : ProcessStep state.denote}
    {base : UInt64}
    (memory : ProcessMemory (processResultTy state) pool heap store words (processValue state value))
    (poolBelow : ∀ region ∈ pool.regions, region.1 + region.2 ≤ base.toNat)
    (at_ : heap'.At store') (free : heap'.free = []) (baseTop : base.toNat ≤ heap'.top.toNat)
    (rep : state.Rep .owned heap' store' stateWords value.state)
    (above : ∀ b ∈ state.blocks store' stateWords value.state, base.toNat ≤ b.1)
    (bytes : ∀ a, a < base.toNat → store'.mem.bytes a = store.mem.bytes a) :
    ProcessMemory (processResultTy state) pool heap' store'
      ([.i64 (boolWord value.running), .i64 value.status] ++ stateWords) (processValue state value) := by
  refine ⟨at_, processValue_rep.mpr ⟨stateWords, rfl, rep⟩, ?_, ?_⟩
  · by_cases hEmpty : pool.payload = []
    · exact Or.inl hEmpty
    · obtain ⟨valid, _⟩ := memory.static.resolve_left hEmpty
      have hEnd := poolBelow _ (by simp [Bytes.LiteralPool.regions, hEmpty])
      have hTop := at_.top
      refine Or.inr ⟨valid.frame (by simp only [Bytes.LiteralPool.endAddress]; omega)
        fun address _ high => bytes address (by
          simp only [Bytes.LiteralPool.endAddress] at high; omega), ?_, ?_⟩
      · simp only; omega
      · intro node member
        rw [free] at member
        exact nomatch member
  · intro region member block blockMember
    rw [processValue_blocks] at blockMember
    simp only [List.drop_left' (show [Value.i64 (boolWord value.running), .i64 value.status].length = 2
      from rfl)] at blockMember
    have hEnd := poolBelow region member
    have hAbove := above block blockMember
    simp only [regionsDisjoint]
    omega

/-- The compaction of the state in the process module.  It traps only at `unreachable`, and only
when the copy finds no room above the rounded top.  Otherwise it leaves the state stored as
`ProcessStored` describes, with the host and the operand stack unchanged. -/
theorem wp_process_compact {World : Type} {source target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {targetHost : HostEnv (Observed World)}
    {store : Store (Observed World)} {heap : Heap} {locals : Locals} {words : List Value}
    {value : ProcessStep state.denote} {rest : Program} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (compactable : state.compactable = true)
    (form : Encoding.ProgramForm (processCompaction state))
    (closed : Relocation.programClosed source.funcs.length (processCompaction state) = true)
    (memory : ProcessMemory (processResultTy state) pool heap (PureTransport.erase store) words
      (processValue state value))
    (held : LocalsHold locals 0 (processResultTy state).types words)
    (baseTop : base.toNat ≤ heap.top.toNat)
    (baseLocal : locals.get (processAux state) = some (.i64 base)) (low : 4096 ≤ base.toNat)
    (poolBelow : ∀ region ∈ pool.regions, region.1 + region.2 ≤ base.toNat)
    (params : locals.params = []) (positions : locals.positions = processPositions state)
    (cap : (PureTransport.erase store).memoryCap target 0 ≤ 65535)
    (trap : ¬ roundWord heap.top.toNat + state.copyCost value.state ≤
        65536 * (PureTransport.erase store).memoryCap source 0 →
      ∀ final : Store (Observed World), final.host = store.host → Q (.Trap final "unreachable"))
    (next : ∀ final after, final.host = store.host →
      (PureTransport.erase final).memoryCaps = (PureTransport.erase store).memoryCaps →
      ProcessStored target state pool base value final after → after.values = locals.values →
      wp target rest Q final after targetHost) :
    wp target (Relocation.program (processCompaction state) ++ rest) Q store locals targetHost := by
  obtain ⟨stateWords, wordsEq, stateRep⟩ := processValue_rep.mp memory.rep
  have hStateLen := stateRep.length
  have split := (LocalsHold.append (s := locals) (loc := 0)
    (tys1 := [.i64, .i64]) (tys2 := state.types)
    (first := [.i64 (boolWord value.running), .i64 value.status])
    (second := stateWords) rfl).mp
      (by simpa only [processResult_types, wordsEq] using held)
  have stateHeld : LocalsHold locals 2 state.types stateWords := by
    simpa only [List.length_cons, List.length_nil, Nat.zero_add] using split.2
  have sourceCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535 := by
    rw [← PureTransport.memoryCap_zero_eq layout.memoryCap]; exact cap
  let room := roundWord heap.top.toNat + state.copyCost value.state ≤
    65536 * (PureTransport.erase store).memoryCap source 0
  let post : Assertion Unit := fun continuation => match continuation with
    | .Fallthrough final after => ∃ heap' stateWords',
        heap'.At final ∧ heap'.free = [] ∧ base.toNat ≤ heap'.top.toNat ∧
        heap'.top.toNat ≤ base.toNat + state.copyCost value.state ∧
        state.Rep .owned heap' final stateWords' value.state ∧
        (∀ b ∈ state.blocks final stateWords' value.state, base.toNat ≤ b.1) ∧
        (∀ a, a < base.toNat → final.mem.bytes a = (PureTransport.erase store).mem.bytes a) ∧
        final.memoryCaps = (PureTransport.erase store).memoryCaps ∧
        Frame 2 locals after ∧ LocalsHold after 2 state.types stateWords' ∧
        after.get (processAux state) = some (.i64 base) ∧ after.values = locals.values
    | .Trap _ message => message = "unreachable" ∧ ¬ room
    | _ => False
  have hWidth : 2 + state.width ≤ processAux state := by
    simp only [processAux, processResult_width]; omega
  have compacted : wp source (processCompaction state) post (PureTransport.erase store) locals
      (HostEnv.empty : HostEnv Unit) := by
    have run := wp_compactCode (host := HostEnv.empty) runtime compactable (rest := []) (Q := post)
      memory.at_ sourceCap stateRep stateHeld positions (by rw [params]; exact Nat.zero_le _)
      hWidth (by simp only [processPositions]; omega) baseLocal low baseTop
      (by
        cases hRoom : decide room
        · intro final
          exact ⟨rfl, of_decide_eq_false hRoom⟩
        · trivial)
      fun heap' store' s' ws' at' free' low' high' rep' above' bytes' caps' frame' held' base'
          values' => by
        rw [wp_nil]
        exact ⟨heap', ws', at', free', low', high', rep', above', bytes', caps', frame', held',
          base', values'⟩
    simpa only [processCompaction, List.append_nil] using run
  have transported := PureTransport.wp_prefix layout profile form closed store.host compacted
    (targetHost := targetHost) (rest := rest) (Q := Q) (fun continuation result => by
      cases continuation with
      | Fallthrough final after =>
          obtain ⟨heap', stateWords', at', free', low', high', rep', above', bytes', caps',
            frame', held', base', values'⟩ := result
          change wp target rest Q (PureTransport.restore store.host final) after targetHost
          refine next _ after (by simp) (by rw [PureTransport.erase_restore]; exact caps') ?_
            values'
          have controlHeld : LocalsHold after 0 [.i64, .i64]
              [.i64 (boolWord value.running), .i64 value.status] :=
            (LocalsHold.frame frame' rfl (by simp)).mpr split.1
          refine ⟨⟨heap', [.i64 (boolWord value.running), .i64 value.status] ++ stateWords', ?_,
              ?_, free', low', high'⟩, base', low, poolBelow, frame'.params.trans params,
              frame'.positions.trans positions, ?_⟩
          · simpa only [PureTransport.erase_restore] using
              memory.compacted poolBelow at' free' low' rep' above' bytes'
          · simpa only [processResult_types] using
              (LocalsHold.append (s := after) (loc := 0) (tys1 := [.i64, .i64])
                (tys2 := state.types) (first := [.i64 (boolWord value.running), .i64 value.status])
                (second := stateWords') rfl).mpr ⟨controlHeld, held'⟩
          · rw [PureTransport.erase_restore]
            have sameCap : final.memoryCap target 0 =
                (PureTransport.erase store).memoryCap target 0 := by
              simp only [Store.memoryCap, caps']
            rw [sameCap]
            exact cap
      | Trap final message =>
          obtain ⟨rfl, noRoom⟩ := result
          exact trap noRoom _ (by simp)
      | _ => exact result.elim)
  simpa only [PureTransport.restore_erase] using transported

end Verified.Wasi
