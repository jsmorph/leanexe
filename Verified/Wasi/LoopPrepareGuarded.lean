import Verified.Wasi.LoopPrepareCode
import Verified.Wasi.LoopAfter
import Verified.Wasi.CommandValue
import Verified.Wasi.Return

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

private theorem prepare_valid {countFits initialFits : Bool} {within : Prop} [Decidable within]
    (denied : (!(countFits && initialFits) || !decide within) ≠ true) :
    countFits = true ∧ initialFits = true ∧ within := by
  cases countFits <;> cases initialFits <;> by_cases within <;> simp_all

theorem wp_loopPrepareGuarded {World : Type} {S : List Sig} {context : List Ty} {type : Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {pool : Bytes.LiteralPool} {count : Expr S context .word} {initial : Expr S context type}
    {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {params : List Value} {heap : Heap} {store : Store World} {locals : Locals} {h base : Nat}
    {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (countSpec : CodeSpec source funs flags bounds fits sourceHost params count env slots []
      (fun i => live i || initial.uses i) pool)
    (initialSpec : CodeSpec source funs flags bounds fits sourceHost params initial env slots [] live pool)
    (countForm : Encoding.ProgramForm
      (count.code (pool := pool) h slots base (fun i => live i || initial.uses i)))
    (countClosed : Relocation.programClosed source.funcs.length
      (count.code (pool := pool) h slots base (fun i => live i || initial.uses i)) = true)
    (initialForm : Encoding.ProgramForm
      (initial.code (pool := pool) h slots (base + 1) live ++
        coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)))
    (initialClosed : Relocation.programClosed source.funcs.length
      (initial.code (pool := pool) h slots (base + 1) live ++
        coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => (live i || initial.uses i) || count.uses i) base heap
      (PureTransport.erase store) locals)
    (at_ : heap.At (PureTransport.erase store))
    (safe : pool.Safe env slots (fun i => (live i || initial.uses i) || count.uses i) heap
      (PureTransport.erase store) locals)
    (scratch : Holds.ApartFrom env slots (fun i => (live i || initial.uses i) || count.uses i)
      (PureTransport.erase store) locals ABI.scratch)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase store).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (countRoom : base + max count.width (copyWidth .word) ≤ h)
    (initialRoom : base + 1 + max initial.width (copyWidth type) ≤ h)
    (stateRoom : base + 2 + type.width ≤ h)
    (countPlace : count.placeArgs = true) (initialPlace : initial.placeArgs = true)
    (resource : (!(count.fits funs fits env && initial.fits funs fits env) || !decide
        (heap.Within (PureTransport.erase store) source
          (count.allocs funs flags bounds (slots.map Slot.mode) []
              (fun i => live i || initial.uses i) env +
            (initial.allocs funs flags bounds (slots.map Slot.mode) [] live env +
              coerceCost type (initial.mode (slots.map Slot.mode)) .owned (initial.denote funs env))))) = true →
      ∀ final : Store World, final.host = store.host → Q (.Trap final "unreachable"))
    (next : ∀ finalHeap final finalLocals words,
      After env slots (fun i => (live i || initial.uses i) || count.uses i) live base
        heap store locals (.value type) (initial.denote funs env) finalHeap final finalLocals words →
      final.host = store.host →
      finalLocals.get base = some (.i64 (count.denote funs env)) →
      finalLocals.get (base + 1) = some (.i64 0) →
      LocalsHold finalLocals (base + 2) type.types words → finalLocals.values = locals.values →
      (count.fits funs fits env = true → initial.fits funs fits env = true →
        finalHeap.top.toNat ≤ heap.top.toNat +
          (count.allocs funs flags bounds (slots.map Slot.mode) []
              (fun i => live i || initial.uses i) env +
            (initial.allocs funs flags bounds (slots.map Slot.mode) [] live env +
              coerceCost type (initial.mode (slots.map Slot.mode)) .owned (initial.denote funs env)))) →
      wp target rest Q final finalLocals targetHost) :
    wp target (loopPrepareCode h base slots pool count initial live ++ rest) Q store locals targetHost := by
  let countLive := fun i => live i || initial.uses i
  let countCharge := count.allocs funs flags bounds (slots.map Slot.mode) [] countLive env
  let initialCharge := initial.allocs funs flags bounds (slots.map Slot.mode) [] live env +
    coerceCost type (initial.mode (slots.map Slot.mode)) .owned (initial.denote funs env)
  have countCost : returnCost funs flags bounds count env slots [] countLive
      (PureTransport.erase store) locals = countCharge := by
    simp [returnCost, dyingPot_nil, coerceCost, Ty.copyCost, countCharge]
  have countSelected : ∀ i, countLive i = true → (countLive i || count.uses i) = true :=
    fun i selected => by rw [selected]; rfl
  have liveSelected : ∀ i, live i = true → countLive i = true :=
    fun i selected => by dsimp only [countLive]; rw [selected]; rfl
  have countCoerce : coerceCode h .word (count.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  let tail := [.localSet base] ++
    Relocation.program (initial.code (pool := pool) h slots (base + 1) live ++
      coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)) ++
    storeCode h (base + 2) type.types ++ [.constI64 0, .localSet (base + 1)] ++ rest
  suffices execution : wp target
      (Relocation.program (count.code (pool := pool) h slots base countLive ++
        coerceCode h .word (count.mode (slots.map Slot.mode)) .owned base) ++ tail)
      Q store locals targetHost by
    simpa only [loopPrepareCode, tail, countLive, countCoerce, List.append_nil, List.append_assoc]
      using execution
  refine wp_return runtime layout profile countSpec
    (by simpa only [countCoerce, List.append_nil, countLive] using countForm)
    (by simpa only [countCoerce, List.append_nil, countLive] using countClosed)
    positions parameters vars at_ safe cap low countRoom countPlace
    (fun failure final same => by
      apply resource ?_ final same
      by_contra denied
      obtain ⟨countFits, _, within⟩ := prepare_valid
        (within := heap.Within (PureTransport.erase store) source (countCharge + initialCharge)) denied
      have withinCount : heap.Within (PureTransport.erase store) source
          (returnCost funs flags bounds count env slots [] countLive (PureTransport.erase store) locals) := by
        apply within.mono
        rw [countCost]
        omega
      simp only [countFits, withinCount, decide_true, Bool.not_true, Bool.false_or] at failure
      exact nomatch failure) ?_
  intro countHeap countStore countLocals countWords countAfter countWorld countTop
  have countRep := countAfter.rep
  simp only [ResultTy.Rep, Ty.rep_word] at countRep
  subst countWords
  simp only [tail, List.append_assoc, List.cons_append, List.nil_append,
    List.reverse_cons, List.reverse_nil]
  have countLow : countLocals.params.length ≤ base := by rw [countAfter.frame.params]; exact low
  have countHigh : base < countLocals.positions := by rw [countAfter.frame.positions, positions]; omega
  refine wp_localSet_local (s := countLocals) (vs := locals.values) countLow
    (Locals.lt_total countHigh) ?_
  let countBound := setLocal { countLocals with values := locals.values } base (.i64 (count.denote funs env))
  have countFrame : Frame base countLocals countBound := Frame.setValues countLow le_rfl countHigh
  have countAfter' := countAfter.reframe countFrame
  have countHeld : countBound.get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same countLow (Locals.lt_total countHigh)
  obtain ⟨countSafe, _⟩ := countAfter'.pool_safe safe vars scratch countSelected poolApart
  have countVars := countAfter'.holds
  refine wp_return runtime layout profile initialSpec initialForm initialClosed
    (countAfter'.frame.positions.trans positions) (countAfter'.frame.params.trans parameters)
    (countVars.mono (Nat.le_succ base)) countAfter'.step.at_ countSafe
    (by rw [countAfter'.step.cap source]; exact cap)
    (by rw [countAfter'.frame.params]; omega) initialRoom initialPlace
    (fun failure final same => by
      apply resource ?_ final (same.trans countWorld)
      by_contra denied
      obtain ⟨countFits, initialFits, within⟩ := prepare_valid
        (within := heap.Within (PureTransport.erase store) source (countCharge + initialCharge)) denied
      have first := countTop countFits
      rw [countCost] at first
      have initialCost : returnCost funs flags bounds initial env slots [] live
          (PureTransport.erase countStore) countBound = initialCharge := by
        simp only [returnCost, dyingPot_nil, Nat.zero_add, initialCharge]
      have withinInitial : countHeap.Within (PureTransport.erase countStore) source
          (returnCost funs flags bounds initial env slots [] live
            (PureTransport.erase countStore) countBound) := by
        apply within.of_le ?_ (countAfter'.step.cap source)
        rw [initialCost]
        omega
      dsimp only [countBound] at withinInitial
      simp only [initialFits, withinInitial, decide_true, Bool.not_true, Bool.false_or] at failure
      exact nomatch failure) ?_
  intro finalHeap final initialLocals words initialAfter initialWorld initialTop
  have growth : count.fits funs fits env = true → initial.fits funs fits env = true →
      finalHeap.top.toNat ≤ heap.top.toNat +
        (count.allocs funs flags bounds (slots.map Slot.mode) []
            (fun i => live i || initial.uses i) env +
          (initial.allocs funs flags bounds (slots.map Slot.mode) [] live env +
            coerceCost type (initial.mode (slots.map Slot.mode)) .owned (initial.denote funs env))) := by
    intro countFits initialFits
    have first := countTop countFits
    have last := initialTop initialFits
    have scalar : coerceCost .word (count.mode (slots.map Slot.mode)) .owned
        (count.denote funs env) = 0 := by simp [coerceCost, Ty.copyCost]
    simp only [returnCost, dyingPot_nil, Nat.zero_add, scalar, Nat.add_zero, countLive] at first last
    omega
  have lowered := initialAfter.lower countVars liveSelected (Nat.le_succ base)
  have after := After.thenWord vars scratch countAfter' lowered countSelected liveSelected
  have initialPositions : initialLocals.positions = h := after.frame.positions.trans positions
  have initialParameters : initialLocals.params = locals.params := after.frame.params
  have countValue : initialLocals.get base = some (.i64 (count.denote funs env)) :=
    (initialAfter.frame.below base (by omega)).1.trans countHeld
  refine wp_storeCode words h (base + 2) type.types initialLocals locals.values
    initialAfter.rep.typed initialPositions (by rw [initialParameters]; omega)
    (by rw [Ty.types_length, initialPositions]; exact stateRoom) ?_
  intro stateLocals stateFrame stateHeld _
  simp only [wp_constI64_cons]
  have statePositions : stateLocals.positions = h := stateFrame.positions.trans initialPositions
  have stateParameters : stateLocals.params = locals.params := stateFrame.params.trans initialParameters
  have indexLow : stateLocals.params.length ≤ base + 1 := by rw [stateParameters]; omega
  have indexHigh : base + 1 < stateLocals.positions := by rw [statePositions]; omega
  refine wp_localSet_local (s := stateLocals) (vs := locals.values) indexLow
    (Locals.lt_total indexHigh) ?_
  let finalLocals := setLocal { stateLocals with values := locals.values } (base + 1) (.i64 0)
  have indexFrame : Frame (base + 1) stateLocals finalLocals :=
    Frame.setValues indexLow le_rfl indexHigh
  have finalAfter := after.reframe ((stateFrame.mono (by omega)).trans (indexFrame.mono (by omega)))
  have finalCount : finalLocals.get base = some (.i64 (count.denote funs env)) := by
    exact (indexFrame.below base (by omega)).1.trans
      ((stateFrame.below base (by omega)).1.trans countValue)
  have finalIndex : finalLocals.get (base + 1) = some (.i64 0) :=
    Locals.get_setLocal_same indexLow (Locals.lt_total indexHigh)
  have finalHeld : LocalsHold finalLocals (base + 2) type.types words :=
    stateHeld.keep (lo := base + 2) indexFrame.positions
      (fun j hj _ => by
        dsimp only [finalLocals]
        refine ⟨?_, ?_, ?_⟩ <;>
          rw [Locals.get_setLocal_ne (s := { stateLocals with values := locals.values })
            indexLow (by omega), Locals.get_values]) le_rfl
      (by rw [initialAfter.rep.length, statePositions]; exact stateRoom)
  exact next finalHeap final finalLocals words finalAfter (initialWorld.trans countWorld)
    finalCount finalIndex finalHeld rfl growth

end Verified.Wasi
