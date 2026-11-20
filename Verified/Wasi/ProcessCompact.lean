import Verified.Wasi.ProcessMemory
import Verified.Wasi.CompactHeap
import Verified.Wasi.PurePrefix

/-! The process state between steps, and the compaction in the process module. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

/-- The process state `current` between steps: the locals from position 0 hold its words, which
represent it with the literal pool intact; the heap's free blocks and the state's blocks lie at or
above `base`, and the heap ends between `base` and `base` plus four times the state's copy cost;
local `processAux state` holds `base`, which lies above the reserved area and the literal pool.
Between `base` and the top the heap holds the state, free blocks, and the blocks that steps left
unreleased since the last compaction. -/
structure ProcessStored {World : Type} (target : Wasm.Module) (state : Ty)
    (pool : Bytes.LiteralPool) (base : UInt64) (current : ProcessStep state.denote)
    (store : Store (Observed World)) (locals : Locals) : Prop where
  represented : ∃ heap words,
    ProcessMemory (processResultTy state) pool heap (PureTransport.erase store)
      words (processValue state current) ∧
    LocalsHold locals 0 (processResultTy state).types words ∧
    (∀ node ∈ heap.free, base.toNat ≤ node.region.1) ∧
    (∀ block ∈ state.blocks (PureTransport.erase store) (words.drop 2) current.state,
      base.toNat ≤ block.1) ∧
    base.toNat ≤ heap.top.toNat ∧ heap.top.toNat ≤ base.toNat + 4 * state.copyCost current.state
  baseLocal : locals.get (processAux state) = some (.i64 base)
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
      (∀ node ∈ heap.free, base.toNat ≤ node.region.1) ∧
      (∀ block ∈ state.blocks (PureTransport.erase store) stateWords current.state,
        base.toNat ≤ block.1) ∧
      base.toNat ≤ heap.top.toNat ∧
      heap.top.toNat ≤ base.toNat + 4 * state.copyCost current.state := by
  obtain ⟨heap, words, memory, held, free, above, low, high⟩ := stored.represented
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
  refine ⟨heap, stateWords, stateMemory, ?_, ?_, free, by simpa only [dropped] using above, low,
    high⟩
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
    baseLocal := stored.baseLocal
    low := stored.low
    pool := stored.pool
    params := stored.params
    positions := stored.positions
    cap := stored.cap }

/-- A step that keeps the region from the end of the reserved area to `base`, from a heap whose top
is at least `base` and whose free blocks lie at or above `base`, leaves the top at or above
`base`.  Every free block of the new heap, and every block that the step leaves fresh apart from
the reserved area, lies at or above `base`. -/
theorem _root_.Verified.Step.base_le {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)} {base : Nat}
    (step : Step heap store keep heap' store' fresh) (low : 4096 ≤ base)
    (baseTop : base ≤ heap.top.toNat) (free : ∀ node ∈ heap.free, base ≤ node.region.1)
    (hKeep : keep (4096, base - 4096)) :
    base ≤ heap'.top.toNat ∧ (∀ node ∈ heap'.free, base ≤ node.region.1) ∧
      ∀ b ∈ fresh, 0 < b.2 → regionsDisjoint b ABI.low → base ≤ b.1 := by
  have hAbove := step.at_.above
  by_cases hEq : base = 4096
  · subst hEq
    refine ⟨step.at_.base, fun node member => ?_, fun b _ positive apart => ?_⟩
    · have := hAbove node member
      simp only [FreeNode.region]
      omega
    · simp only [regionsDisjoint, ABI.low] at apart
      omega
  · have hRegion : heap.Region (4096, base - 4096) :=
      ⟨show 4096 + (base - 4096) ≤ heap.top.toNat by omega, fun node member => by
        have := free node member
        simp only [regionsDisjoint]
        omega⟩
    obtain ⟨_, hRegion', hFresh⟩ := step.keeps _ hRegion (show 0 < base - 4096 by omega) hKeep
    refine ⟨by have := hRegion'.below; omega, fun node member => ?_,
      fun b member positive apart => ?_⟩
    · have hSeparate := hRegion'.separate node member
      have := hAbove node member
      simp only [regionsDisjoint, FreeNode.region] at hSeparate ⊢
      omega
    · have := hFresh b member
      simp only [regionsDisjoint, ABI.low] at this apart
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

theorem low_apart_above (n : Nat) : regionsDisjoint (4096, n) ABI.low := by
  simp only [regionsDisjoint, ABI.low]
  omega

/-- The memory facts of a call's result: the result represents its value, the call kept the
literal pool, and the result's blocks lie apart from the pool. -/
theorem ProcessMemory.called {oldType resultType : Ty} {pool : Bytes.LiteralPool}
    {heap middleHeap : Heap} {initial middle : Store Unit}
    {oldWords resultWords : List Value} {oldValue : oldType.denote}
    {resultValue : resultType.denote} {keep : Nat × Nat → Prop}
    (current : ProcessMemory oldType pool heap initial oldWords oldValue)
    (poolKept : ∀ region ∈ pool.regions, keep region)
    (called : Step heap initial keep middleHeap middle
      (resultType.blocks middle resultWords resultValue))
    (resultRep : resultType.Rep .owned middleHeap middle resultWords resultValue) :
    ProcessMemory resultType pool middleHeap middle resultWords resultValue := by
  obtain ⟨middleStatic, poolFresh⟩ := current.static.step called poolKept
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
      have hEnd : pool.base + pool.payload.length ≤ base.toNat :=
        poolBelow (pool.base, pool.payload.length) (by simp [Bytes.LiteralPool.regions, hEmpty])
      have hTop := at_.top
      refine Or.inr ⟨valid.frame (by simp only [Bytes.LiteralPool.endAddress]; omega)
        fun address _ high => bytes address (by
          simp only [Bytes.LiteralPool.endAddress] at high; omega), ?_, ?_⟩
      · show pool.base + pool.payload.length ≤ heap'.top.toNat
        omega
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

/-- The facts of the source module after the compaction of the state, or after a test that omits
it: a heap at `final` that holds the state, of the result words of `value`, with the literal pool,
whose free blocks and the state's blocks lie at or above `base` and whose top lies between `base`
and `base` plus four times the state's copy cost, with the memory caps of `store`, the locals of
`locals` below position 2, the state's words from position 2, `base` in local `processAux state`,
and the operand stack of `locals`.  The only trap is the one at `unreachable` when `room` fails. -/
abbrev CompactPost (state : Ty) (pool : Bytes.LiteralPool) (base : UInt64) (store : Store Unit)
    (locals : Locals) (value : ProcessStep state.denote) (room : Prop) : Assertion Unit :=
  fun continuation => match continuation with
  | .Fallthrough final after => ∃ heap' stateWords',
      ProcessMemory (processResultTy state) pool heap' final
        ([.i64 (boolWord value.running), .i64 value.status] ++ stateWords')
        (processValue state value) ∧
      (∀ node ∈ heap'.free, base.toNat ≤ node.region.1) ∧
      (∀ b ∈ state.blocks final stateWords' value.state, base.toNat ≤ b.1) ∧
      base.toNat ≤ heap'.top.toNat ∧
      heap'.top.toNat ≤ base.toNat + 4 * state.copyCost value.state ∧
      final.memoryCaps = store.memoryCaps ∧
      Frame 2 locals after ∧ LocalsHold after 2 state.types stateWords' ∧
      after.get (processAux state) = some (.i64 base) ∧ after.values = locals.values
  | .Trap _ message => message = "unreachable" ∧ ¬ room
  | _ => False

/-- A source-level program whose runs end as `CompactPost` states runs in the process module from
the state stored with its control words in locals 0 and 1, and leaves the state stored as
`ProcessStored` describes, with the host and the operand stack unchanged, or traps at
`unreachable` when `room` fails. -/
theorem wp_compacted_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {targetHost : HostEnv (Observed World)}
    {store : Store (Observed World)} {locals : Locals} {value : ProcessStep state.denote}
    {code rest : Program} {room : Prop} {Q : Assertion (Observed World)}
    (layout : Relocation.LayoutWith calls source target) (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm code)
    (closed : Relocation.programClosed source.funcs.length code = true)
    (controlHeld : LocalsHold locals 0 [.i64, .i64]
      [.i64 (boolWord value.running), .i64 value.status])
    (low : 4096 ≤ base.toNat)
    (poolBelow : ∀ region ∈ pool.regions, region.1 + region.2 ≤ base.toNat)
    (params : locals.params = []) (positions : locals.positions = processPositions state)
    (cap : (PureTransport.erase store).memoryCap target 0 ≤ 65535)
    (compacted : wp source code
      (CompactPost state pool base (PureTransport.erase store) locals value room)
      (PureTransport.erase store) locals (HostEnv.empty : HostEnv Unit))
    (trap : ¬ room → ∀ final : Store (Observed World), final.host = store.host →
      Q (.Trap final "unreachable"))
    (next : ∀ final after, final.host = store.host →
      (PureTransport.erase final).memoryCaps = (PureTransport.erase store).memoryCaps →
      ProcessStored target state pool base value final after → after.values = locals.values →
      wp target rest Q final after targetHost) :
    wp target (Relocation.programWith calls code ++ rest) Q store locals targetHost := by
  have transported := PureTransport.wp_prefix_with (calls := calls) layout profile form closed
    store.host compacted (targetHost := targetHost) (rest := rest) (Q := Q)
    (fun continuation result => by
      cases continuation with
      | Fallthrough final after =>
          obtain ⟨heap', stateWords', memory', free', above', low', high', caps', frame', held',
            base', values'⟩ := result
          change wp target rest Q (PureTransport.restore store.host final) after targetHost
          refine next _ after (by simp) (by rw [PureTransport.erase_restore]; exact caps') ?_
            values'
          have controlHeld' : LocalsHold after 0 [.i64, .i64]
              [.i64 (boolWord value.running), .i64 value.status] :=
            (LocalsHold.frame frame' rfl (by simp)).mpr controlHeld
          refine ⟨⟨heap', [.i64 (boolWord value.running), .i64 value.status] ++ stateWords', ?_,
              ?_, free', ?_, low', high'⟩, base', low, poolBelow, frame'.params.trans params,
              frame'.positions.trans positions, ?_⟩
          · simpa only [PureTransport.erase_restore] using memory'
          · simpa only [processResult_types] using
              (LocalsHold.append (s := after) (loc := 0) (tys1 := [.i64, .i64])
                (tys2 := state.types) (first := [.i64 (boolWord value.running), .i64 value.status])
                (second := stateWords') rfl).mpr ⟨controlHeld', held'⟩
          · simpa only [PureTransport.erase_restore, List.drop_left'
              (show [Value.i64 (boolWord value.running), .i64 value.status].length = 2 from rfl)]
              using above'
          · rw [PureTransport.erase_restore]
            have sameCap : final.memoryCap target 0 =
                (PureTransport.erase store).memoryCap target 0 := by
              simp only [Store.memoryCap, caps']
            rw [sameCap]
            exact cap
      | Trap final message =>
          obtain ⟨rfl, noRoom⟩ := result
          exact trap noRoom _ (by simp)
      | _ => exact False.elim result)
  simpa only [PureTransport.restore_erase] using transported

/-- The compaction of the state in the source module, from locals that hold the state's words
from position 2 and `base` in local `processAux state`, ends as `CompactPost` states, with no free
block and the heap's top at most `base` plus the state's copy cost. -/
theorem wp_process_compaction_source {source : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {store : Store Unit} {heap : Heap} {locals : Locals}
    {stateWords : List Value} {value : ProcessStep state.denote} {Q : Assertion Unit}
    (runtime : Runtime source) (compactable : state.compactable = true)
    (memory : ProcessMemory (processResultTy state) pool heap store
      ([.i64 (boolWord value.running), .i64 value.status] ++ stateWords)
      (processValue state value))
    (stateHeld : LocalsHold locals 2 state.types stateWords)
    (baseTop : base.toNat ≤ heap.top.toNat)
    (baseLocal : locals.get (processAux state) = some (.i64 base)) (low : 4096 ≤ base.toNat)
    (poolBelow : ∀ region ∈ pool.regions, region.1 + region.2 ≤ base.toNat)
    (params : locals.params = []) (positions : locals.positions = processPositions state)
    (sourceCap : store.memoryCap source 0 ≤ 65535)
    (post : ∀ continuation, CompactPost state pool base store locals value
      (roundWord heap.top.toNat + state.copyCost value.state ≤ 65536 * store.memoryCap source 0)
      continuation → Q continuation) :
    wp source (processCompaction state) Q store locals (HostEnv.empty : HostEnv Unit) := by
  obtain ⟨stateWords0, wordsEq, stateRep⟩ := processValue_rep.mp memory.rep
  obtain rfl := List.append_cancel_left wordsEq
  have hWidth : 2 + state.width ≤ processAux state := by
    simp only [processAux, processResult_width]; omega
  have run := wp_compactCode (host := HostEnv.empty) runtime compactable (rest := []) (Q := Q)
    memory.at_ sourceCap stateRep stateHeld
    positions (by rw [params]; exact Nat.zero_le _) hWidth (by simp only [processPositions]; omega)
    baseLocal low baseTop
    (by
      unfold TrapOK
      split
      · rename_i noRoom
        intro final
        exact post _ ⟨rfl, by simpa using noRoom⟩
      · trivial)
    fun heap' store' s' ws' at' free' low' high' rep' above' bytes' caps' frame' held' base'
        values' => by
      rw [wp_nil]
      refine post _ ⟨heap', ws', memory.compacted poolBelow at' free' low' rep' above' bytes',
        (fun node member => by rw [free'] at member; exact nomatch member), above', low', by omega,
        caps', frame', held', base', values'⟩
  simpa only [processCompaction, List.append_nil] using run

/-- The compaction of the state in the process module.  It traps only at `unreachable`, and only
when the copy finds no room above the rounded top.  Otherwise it leaves the state stored as
`ProcessStored` describes, with the host and the operand stack unchanged. -/
theorem wp_process_compact_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {targetHost : HostEnv (Observed World)}
    {store : Store (Observed World)} {heap : Heap} {locals : Locals} {words : List Value}
    {value : ProcessStep state.denote} {rest : Program} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
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
    wp target (Relocation.programWith calls (processCompaction state) ++ rest) Q store locals targetHost := by
  obtain ⟨stateWords, wordsEq, _⟩ := processValue_rep.mp memory.rep
  subst wordsEq
  have split := (LocalsHold.append (s := locals) (loc := 0)
    (tys1 := [.i64, .i64]) (tys2 := state.types)
    (first := [.i64 (boolWord value.running), .i64 value.status])
    (second := stateWords) rfl).mp (by simpa only [processResult_types] using held)
  have sourceCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535 := by
    rw [← PureTransport.memoryCap_zero_eq layout.memoryCap]; exact cap
  exact wp_compacted_with layout profile form closed split.1 low poolBelow params positions cap
    (wp_process_compaction_source runtime compactable memory
      (by simpa only [List.length_cons, List.length_nil, Nat.zero_add] using split.2) baseTop
      baseLocal low poolBelow params positions sourceCap fun _ result => result)
    trap next

theorem programForm_append {first second : Program} (firstForm : Encoding.ProgramForm first)
    (secondForm : Encoding.ProgramForm second) : Encoding.ProgramForm (first ++ second) := by
  induction first with
  | nil => simpa using secondForm
  | cons head tail ih =>
    cases firstForm with
    | cons _ _ headForm tailForm => exact .cons _ _ headForm (ih tailForm)

theorem programForm_tail {head : Instruction} {tail : Program}
    (form : Encoding.ProgramForm (head :: tail)) : Encoding.ProgramForm tail := by
  cases form with
  | cons _ _ _ tailForm => exact tailForm

theorem programForm_head {head : Instruction} {tail : Program}
    (form : Encoding.ProgramForm (head :: tail)) : Encoding.InstructionForm head := by
  cases form with
  | cons _ _ headForm _ => exact headForm

/-- The code of the copy cost has a form that the encoder writes, when its locals' indices do. -/
theorem copyCostCode_form : (t : Ty) → t.compactable = true → (loc : Nat) →
    loc + t.width < 2 ^ 32 → Encoding.ProgramForm (copyCostCode t loc)
  | .elem _, _, _, _ => .cons _ _ (.const64 0) .nil
  | .array _, _, loc, bound => by
    simp only [Ty.width] at bound
    exact .cons _ _ (.localGet loc (by omega)) (.cons _ _ .wrapI64 (.cons _ _ (.load64 0)
      (.cons _ _ (.const64 1) (.cons _ _ .addI64 (.cons _ _ (.const64 8) (.cons _ _ .mulI64
        (.cons _ _ (.const64 48) (.cons _ _ .addI64 .nil))))))))
  | .bytes, _, loc, bound => by
    simp only [Ty.width] at bound
    have body : Encoding.ProgramForm [.localGet (loc + 1), .constI64 7, .addI64, .constI64 8,
        .divUI64, .constI64 8, .mulI64, .constI64 48, .addI64] :=
      .cons _ _ (.localGet (loc + 1) (by omega)) (.cons _ _ (.const64 7) (.cons _ _ .addI64
        (.cons _ _ (.const64 8) (.cons _ _ .divUI64 (.cons _ _ (.const64 8) (.cons _ _ .mulI64
          (.cons _ _ (.const64 48) (.cons _ _ .addI64 .nil))))))))
    exact .cons _ _ (.localGet (loc + 1) (by omega)) (.cons _ _ .eqzI64
      (.cons _ _ (.iff [.i64] _ _ (.value .i64 (.inr (.inl rfl))) (.cons _ _ (.const64 0) .nil) body)
        .nil))
  | .pair a b, compactable, loc, bound => by
    obtain ⟨ha, hb⟩ := Ty.compactable_pair compactable
    simp only [Ty.width] at bound
    exact programForm_append (programForm_append (copyCostCode_form a ha loc (by omega))
      (copyCostCode_form b hb (loc + a.width) (by omega))) (.cons _ _ .addI64 .nil)
  | .tree _, compactable, _, _ | .treeHeader _ _, compactable, _, _ => by
    simp [Ty.compactable] at compactable

/-- The local that holds the heap's base lies below `2 ^ 32` when the compaction has a form that
the encoder writes: the compaction sets the local after it. -/
theorem processCompaction_aux_lt {state : Ty}
    (form : Encoding.ProgramForm (processCompaction state)) : processAux state + 1 < 2 ^ 32 := by
  simp only [processCompaction, compactCode, List.cons_append] at form
  have head := programForm_head (programForm_tail (programForm_tail (programForm_tail
    (programForm_tail (programForm_tail (programForm_tail (programForm_tail (programForm_tail
      (programForm_tail form)))))))))
  cases head with
  | localSet _ bound => exact bound

theorem processCompactWhen_form {state : Ty} (compactable : state.compactable = true)
    (form : Encoding.ProgramForm (processCompaction state)) :
    Encoding.ProgramForm (processCompactWhen state) := by
  have aux := processCompaction_aux_lt form
  have width : 2 + state.width ≤ processAux state := by
    simp only [processAux, processResult_width]; omega
  exact programForm_append (programForm_append (copyCostCode_form state compactable 2 (by omega))
    (.cons _ _ (.const64 2) (.cons _ _ .shlI64 .nil)))
    (.cons _ _ (.globalGet 0 (by decide)) (.cons _ _ (.localGet _ (by omega)) (.cons _ _ .subI64
      (.cons _ _ .ltUI64 (.cons _ _ (.iff [] _ _ .empty form .nil) .nil)))))

theorem programClosed_append (bound : Nat) (first second : Program) :
    Relocation.programClosed bound (first ++ second) =
      (Relocation.programClosed bound first && Relocation.programClosed bound second) := by
  induction first with
  | nil => simp [Relocation.programClosed]
  | cons head tail ih => simp [Relocation.programClosed, ih, Bool.and_assoc]

theorem copyCostCode_closed (bound : Nat) :
    (t : Ty) → (loc : Nat) → Relocation.programClosed bound (copyCostCode t loc) = true
  | .array _, _ | .bytes, _ | .elem _, _ | .tree _, _ | .treeHeader _ _, _ => by
    simp [copyCostCode, Relocation.programClosed, Relocation.instructionClosed]
  | .pair a b, loc => by
    simp [copyCostCode, programClosed_append, copyCostCode_closed bound a,
      copyCostCode_closed bound b, Relocation.programClosed, Relocation.instructionClosed]

theorem processCompactWhen_closed {state : Ty} {bound : Nat}
    (closed : Relocation.programClosed bound (processCompaction state) = true) :
    Relocation.programClosed bound (processCompactWhen state) = true := by
  simp [processCompactWhen, programClosed_append, copyCostCode_closed, Relocation.programClosed,
    Relocation.instructionClosed, closed]

/-- The word that `processCompactWhen` compares with the heap's extent above the base, four times
the state's copy cost modulo `2 ^ 64`, is at most four times the copy cost. -/
theorem quadruple_toNat_le (cost : Nat) : (UInt64.ofNat cost <<< 2).toNat ≤ 4 * cost := by
  have shifted : (UInt64.ofNat cost <<< 2).toNat = (UInt64.ofNat cost).toNat * 4 % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft]
    simp [Nat.shiftLeft_eq]
  have reduced : (UInt64.ofNat cost).toNat ≤ cost := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_le _ _
  rw [shifted]
  exact Nat.le_trans (Nat.mod_le _ _) (by omega)

/-- The compaction of the state in the process module when the heap above the base exceeds four
times the state's copy cost, from a stored result whose free blocks and state's blocks lie at or
above the base.  It traps only at `unreachable`, and only when the compaction runs and the copy finds no
room above the rounded top.  Otherwise it leaves the state stored as `ProcessStored` describes,
with the host and the operand stack unchanged. -/
theorem wp_process_compact_when_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {targetHost : HostEnv (Observed World)}
    {store : Store (Observed World)} {heap : Heap} {locals : Locals} {words : List Value}
    {value : ProcessStep state.denote} {rest : Program} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (compactable : state.compactable = true)
    (form : Encoding.ProgramForm (processCompaction state))
    (closed : Relocation.programClosed source.funcs.length (processCompaction state) = true)
    (memory : ProcessMemory (processResultTy state) pool heap (PureTransport.erase store) words
      (processValue state value))
    (held : LocalsHold locals 0 (processResultTy state).types words)
    (free : ∀ node ∈ heap.free, base.toNat ≤ node.region.1)
    (above : ∀ block ∈ state.blocks (PureTransport.erase store) (words.drop 2) value.state,
      base.toNat ≤ block.1)
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
    wp target (Relocation.programWith calls (processCompactWhen state) ++ rest) Q store locals
      targetHost := by
  obtain ⟨stateWords, wordsEq, stateRep⟩ := processValue_rep.mp memory.rep
  subst wordsEq
  have dropped : ([Value.i64 (boolWord value.running), .i64 value.status] ++ stateWords).drop 2 =
      stateWords := rfl
  rw [dropped] at above
  have split := (LocalsHold.append (s := locals) (loc := 0)
    (tys1 := [.i64, .i64]) (tys2 := state.types)
    (first := [.i64 (boolWord value.running), .i64 value.status])
    (second := stateWords) rfl).mp (by simpa only [processResult_types] using held)
  have stateHeld : LocalsHold locals 2 state.types stateWords := by
    simpa only [List.length_cons, List.length_nil, Nat.zero_add] using split.2
  have sourceCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535 := by
    rw [← PureTransport.memoryCap_zero_eq layout.memoryCap]; exact cap
  have tested : wp source (processCompactWhen state)
      (CompactPost state pool base (PureTransport.erase store) locals value
        (roundWord heap.top.toNat + state.copyCost value.state ≤
          65536 * (PureTransport.erase store).memoryCap source 0))
      (PureTransport.erase store) locals (HostEnv.empty : HostEnv Unit) := by
    have globals : (PureTransport.erase store).globals.globals = heap.globals := memory.at_.globals
    simp only [processCompactWhen, List.append_assoc, List.cons_append, List.nil_append]
    refine wp_copyCostCode state compactable stateRep stateHeld ?_
    simp only [wp_constI64_cons, wp_shlI64_cons, wp_globalGet_cons, globals, Heap.globals,
      List.getElem?_cons_zero, wp_localGet_cons, Locals.get_values, baseLocal, wp_subI64_cons,
      wp_ltUI64_cons, UInt64.reduceMod]
    refine wp_iff_cons rfl ?_
    by_cases grown : UInt64.ofNat (state.copyCost value.state) <<< 2 < heap.top - base
    · simp (config := { decide := true }) only [grown, ↓reduceIte, ne_eq]
      exact wp_process_compaction_source runtime compactable memory
        (stateHeld.with_values _) baseTop baseLocal low poolBelow params positions sourceCap
        fun continuation result => by
          cases continuation with
          | Fallthrough final after =>
              obtain ⟨heap', stateWords', memory', free', above', low', high', caps', frame',
                held', base', values'⟩ := result
              simp only [wp_nil]
              exact ⟨heap', stateWords', memory', free', above', low', high', caps',
                ⟨frame'.params, frame'.length, frame'.below, frame'.below32⟩,
                held'.with_values _, base', by simp [values']⟩
          | Trap final message => exact result
          | _ => exact False.elim result
    · simp (config := { decide := true }) only [grown, ↓reduceIte, ne_eq, wp_nil]
      have topBase : (heap.top - base).toNat = heap.top.toNat - base.toNat :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr baseTop)
      have bound : heap.top.toNat - base.toNat ≤ 4 * state.copyCost value.state := by
        have notLess := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp grown)
        rw [topBase] at notLess
        have := quadruple_toNat_le (state.copyCost value.state)
        omega
      exact ⟨heap, stateWords, memory, free, above, baseTop, by omega, rfl, Frame.refl _ _,
        stateHeld.with_values _, baseLocal, by simp⟩
  exact wp_compacted_with layout profile (processCompactWhen_form compactable form)
    (processCompactWhen_closed closed) split.1 low poolBelow params positions cap tested trap next

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
  layout_instance wp_process_compact_with

end Verified.Wasi
