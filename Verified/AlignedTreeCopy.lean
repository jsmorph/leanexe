import Verified.AlignedTreeCopySlot
import LeanExe.ProofKit.AlignedReleaseTree
import Verified.TreeSlotCode

/-!
The copy of a tree under the flag: the ports of `CopyRecord.Holds.widthPushes`,
`wp_treeCopyBody`, `wp_treeCopyLoop`, `wp_treeCopyRecord`, and `wp_copyTree`.  The loop runs the
body, which reads the next index and, for a tagged shape, the width from the record's header and
copies one slot or ends the record, with `CopyInvX` as its invariant.  From an aligned heap and a
source whose regions start at multiples of 8, the copy's accesses are aligned, and it ends with an
aligned heap and a tree whose blocks start and end at multiples of 8.  `wpX_loop_ghost` is
`wp_loop_ghost` under the flag.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- `wp_loop_ghost` under the flag. -/
theorem wpX_loop_ghost {α : Type} {strict : Bool} {m : Module} {env : HostEnv α} {ps rs : Nat}
    {body rest : Program} {Q : Assertion α} {st : Store α} {s : Locals}
    (Inv : Nat → AssertionF α) (n : Nat) (hInit : Inv n st s)
    (hStep : ∀ n st s, Inv n st s →
        wpX strict m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wpX strict m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              ∃ n' < n, Inv n' st' { s' with values := s'.values.take ps ++ s.values.drop ps }
            | .Break (k+1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wpX strict m (.loop ps rs body :: rest) Q st s env := by
  cases strict
  · exact wp_loop_ghost Inv n hInit hStep
  · exact wpA_loop_ghost Inv n hInit hStep

theorem CopyRecord.Holds.widthPushesX {strict : Bool} {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {base : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hPtr : s.get (base + 1) = some (.i64 record.pointer))
    (hAl : strict = true → record.pointer.toNat % 8 = 0) :
    PushesWordX strict m host (treeCopyWidth shape base) store s
      (UInt64.ofNat record.slots.length) := by
  obtain ⟨r, hLength, -, -, -⟩ := id h.layout
  unfold treeCopyWidth
  cases hT : shape.tagged with
  | true =>
    have hBase := h.storage.base
    have hAddress := h.storage.address
    have hBelow := h.storage.below
    have hTop := hHeap.top
    intro vs rest Q hNext
    simp only [ite_true]
    refine wpX_headerLoad hPtr ?_ (fun hs => ⟨hAl hs, rfl⟩) ?_
    · rw [headerAddress_toNat (by change 16 ≤ record.pointer.toNat; omega) (by omega)]
      change record.pointer.toNat - 16 + 8 ≤ store.mem.pages * 65536
      omega
    · rw [h.width hT]
      exact hNext
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [shape.selectCode_untagged hT r, ← hLength]
    exact PushesWordX.const

/-- The loop bound pushes the width of the record being copied. -/
theorem CopyRecord.Holds.widthPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {base : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hPtr : s.get (base + 1) = some (.i64 record.pointer)) :
    PushesWord m host (treeCopyWidth shape base) store s
      (UInt64.ofNat record.slots.length) :=
  CopyRecord.Holds.widthPushesX (strict := false) h hHeap hPtr nofun

theorem wpX_treeCopyBody {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals} {Q : Assertion Unit}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s' next parents',
      CopyInvX strict shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → Q (.Break 0 store' s'))
    (hRoot : ∀ store' s', NodeOwned heap store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap store' (Node.blocks store' result (.record root)) →
      heap.top.toNat ≤ limit → CopyLocals base s0 result current.pointer s' →
      (strict = true → heap.Aligned ∧
        ∀ b ∈ Node.blocks store' result (.record root), b.1 % 8 = 0 ∧ b.2 % 8 = 0) →
      Q (.Break 1 store' s')) :
    wpX strict m (treeCopyBody shape base) Q store s host := by
  have h := hX.1
  have hCurrent := h.frames.current
  have hBase := hCurrent.storage.base
  have hAddress := hCurrent.storage.address
  have hBelow := hCurrent.storage.below
  have hTop := h.step.at_.top
  have hShort : current.slots.length ≤ 64 := by
    obtain ⟨r, hLength, -, -, -⟩ := id hCurrent.layout
    rw [hLength]
    exact shape.width_le r
  have hBound := hCurrent.bound
  have hIndexNat : (UInt64.ofNat current.next).toNat = current.next :=
    UInt64.toNat_ofNat_of_lt' (by change current.next < 18446744073709551616; omega)
  have hCountNat : (UInt64.ofNat current.slots.length).toNat = current.slots.length :=
    UInt64.toNat_ofNat_of_lt' (by change current.slots.length < 18446744073709551616; omega)
  have hCompare : (UInt64.ofNat current.next < UInt64.ofNat current.slots.length) ↔
      current.next < current.slots.length := by
    rw [UInt64.lt_iff_toNat_lt, hIndexNat, hCountNat]
  have hLow2 : s.params.length ≤ base + 2 := by omega
  have hHigh2 : base + 2 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  simp only [treeCopyBody]
  refine wpX_headerLoad hLocals.current ?_ (fun hs => ⟨hX.pointerAl hs, rfl⟩) ?_
  · rw [headerAddress_toNat (by change 8 ≤ current.pointer.toNat; omega) (by omega)]
    change current.pointer.toNat - 8 + 8 ≤ store.mem.pages * 65536
    omega
  rw [hCurrent.index]
  refine wpX_localSet_local hLow2 hHigh2 ?_
  let sIndex := setLocal s (base + 2) (.i64 (UInt64.ofNat current.next))
  have hIndexLocals : CopyLocals base s0 result current.pointer sIndex :=
    hLocals.scratch hLow2 (by omega) (by omega)
  have hIndex : sIndex.get (base + 2) = some (.i64 (UInt64.ofNat current.next)) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hLowIndex : sIndex.params.length ≤ base := hLow
  have hHighIndex : base + 6 ≤ sIndex.positions := by
    simpa only [sIndex, Locals.positions_setLocal] using hHigh
  change wpX strict m (.localGet (base + 2) :: (treeCopyWidth shape base ++ [.ltUI64,
    .iff 0 0 (treeCopySlot shape base) (treeCopyFinish shape base), .br 0])) Q store sIndex host
  simp only [wpX_localGet_cons, hIndex]
  apply hCurrent.widthPushesX h.step.at_ hIndexLocals.current hX.pointerAl
  simp only [wpX_ltUI64_cons]
  let post : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wpX strict m [.br 0] Q store' { s' with values := sIndex.values } host
    | .Break 0 store' s' => wpX strict m [.br 0] Q store' { s' with values := sIndex.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  have hAfter (heap' : Heap) (store' : Store Unit) (s' : Locals) (next : CopyRecord)
      (parents' : List CopyRecord)
      (hInv : CopyInvX strict shape heap0 initial root result limit heap' store' next parents')
      (hVars : CopyLocals base s0 result next.pointer s')
      (hWork : CopyWork.Step (current.work parents) (next.work parents')) :
      wpX strict m [] post store' s' host := by
    rw [wpX_nil]
    change wpX strict m [.br 0] Q store' { s' with values := sIndex.values } host
    have hStack : sIndex.values = s'.values := hIndexLocals.values.trans hVars.values.symm
    rw [hStack]
    simpa only [wpX_br_cons] using hNext heap' store' s' next parents' hInv hVars hWork
  by_cases hMore : current.next < current.slots.length
  · rw [ite_eq_left (hCompare.mpr hMore)]
    refine wpX_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_true, List.take_zero, List.drop_zero, List.nil_append]
    refine wpX.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wpX strict m (treeCopySlot shape base) post store sIndex host
    simpa only [List.append_nil] using wpX_treeCopySlot hm hRt (rest := []) hX hIndexLocals hIndex hMore
      hLowIndex hHighIndex hCap (hTrap.imp (Q' := post) (fun _ h => h)) hAfter
  · have hDone : current.next = current.slots.length := by omega
    rw [ite_eq_right (fun hLess => hMore (hCompare.mp hLess))]
    refine wpX_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_false, List.take_zero, List.drop_zero, List.nil_append]
    refine wpX.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wpX strict m (treeCopyFinish shape base) post store sIndex host
    simpa only [List.append_nil] using wpX_treeCopyFinish (rest := []) hX hIndexLocals hDone
      hLowIndex hHighIndex (fun store' s' next parents' hInv hVars hWork =>
        hAfter heap store' s' next parents' hInv hVars hWork)
      (fun store' s' hOwned hApart hStep hBudget hVars hRootAl =>
        hRoot store' s' hOwned hApart hStep hBudget hVars hRootAl)

theorem wp_treeCopyBody {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s' next parents',
      CopyInv shape heap0 initial root result limit heap' store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → Q (.Break 0 store' s'))
    (hRoot : ∀ store' s', NodeOwned heap store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap store' (Node.blocks store' result (.record root)) →
      heap.top.toNat ≤ limit → CopyLocals base s0 result current.pointer s' → Q (.Break 1 store' s')) :
    wp m (treeCopyBody shape base) Q store s host :=
  wpX_treeCopyBody (strict := false) hm nofun ⟨h, nofun⟩ hLocals hLow hHigh hCap hTrap
    (fun heap' store' s' next parents' hI => hNext heap' store' s' next parents' hI.1)
    (fun store' s' h1 h2 h3 h4 h5 _ => hRoot store' s' h1 h2 h3 h4 h5)
#print axioms wp_treeCopyBody

theorem wpX_treeCopyLoop {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s', NodeOwned heap' store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap' store' (Node.blocks store' result (.record root)) →
      heap'.top.toNat ≤ limit → Frame base s0 s' → s'.get base = some (.i64 result) →
      s'.values = s0.values →
      (strict = true → heap'.Aligned ∧
        ∀ b ∈ Node.blocks store' result (.record root), b.1 % 8 = 0 ∧ b.2 % 8 = 0) →
      wpX strict m rest Q store' s' host) :
    wpX strict m (.block 0 0 [.loop 0 0 (treeCopyBody shape base)] :: rest) Q store s host := by
  have h := hX.1
  let Inv : Nat → AssertionF Unit := fun n store' s' => ∃ heap' current' parents',
    CopyInvX strict shape heap0 initial root result limit heap' store' current' parents' ∧
      CopyLocals base s0 result current'.pointer s' ∧ (current'.work parents').steps = n
  let done : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wpX strict m rest Q store' { s' with values := s.values } host
    | .Break 0 store' s' => wpX strict m rest Q store' { s' with values := s.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  refine wpX_block_cons ?_
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  refine wpX.conseq (Q := done) ?_ ?_
  · intro c hc
    cases c with
    | Break k _ _ => cases k <;> exact hc
    | _ => exact hc
  refine wpX_loop_ghost Inv (current.work parents).steps ⟨heap, current, parents, hX, hLocals, rfl⟩ ?_
  rintro n store' s' ⟨heap', current', parents', hInv, hVars, hMeasure⟩
  have hLow' : s'.params.length ≤ base := by
    rw [hVars.frame.params, ← hLocals.frame.params]
    exact hLow
  have hHigh' : base + 6 ≤ s'.positions := by
    rw [hVars.frame.positions, ← hLocals.frame.positions]
    exact hHigh
  refine wpX_treeCopyBody hm hRt hInv hVars hLow' hHigh' hCap ?_ ?_ ?_
  · exact hTrap.imp (fun _ h => h)
  · intro heap'' store'' s'' next parents'' hInv' hVars' hWork
    refine ⟨(next.work parents'').steps, ?_, ?_⟩
    · rw [← hMeasure]
      exact hWork.decreases
    · simp only [List.take_zero, List.drop_zero, List.nil_append]
      have hStack : s'.values = s''.values := hVars.values.trans hVars'.values.symm
      rw [hStack]
      exact ⟨heap'', next, parents'', hInv', hVars', rfl⟩
  · intro store'' s'' hOwned hApart hStep hBudget hVars' hRootAl
    change wpX strict m rest Q store'' { s'' with values := s.values } host
    have hStack : s.values = s''.values := hLocals.values.trans hVars'.values.symm
    rw [hStack]
    exact hNext heap' store'' s'' hOwned hApart hStep hBudget hVars'.frame hVars'.result hVars'.values
      hRootAl

theorem wp_treeCopyLoop {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s', NodeOwned heap' store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap' store' (Node.blocks store' result (.record root)) →
      heap'.top.toNat ≤ limit → Frame base s0 s' → s'.get base = some (.i64 result) →
      s'.values = s0.values → wp m rest Q store' s' host) :
    wp m (.block 0 0 [.loop 0 0 (treeCopyBody shape base)] :: rest) Q store s host :=
  wpX_treeCopyLoop (strict := false) hm nofun ⟨h, nofun⟩ hLocals hLow hHigh hCap hTrap
    (fun heap' store' s' a1 a2 a3 a4 a5 a6 a7 _ => hNext heap' store' s' a1 a2 a3 a4 a5 a6 a7)
#print axioms wp_treeCopyLoop

theorem wpX_treeCopyRecord {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {src base : Nat} {source : UInt64}
    {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLayout : NodeLayout shape (.record slots)) (hSource : NodeBorrowed heap store source (.record slots))
    (hTrap : TrapOK (!decide (heap.Within store m (nodeCopyCost (.record slots)))) Q)
    (hSrc : s.get src = some (.i64 source)) (hSrcBase : src < base)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hHeapAl : strict = true → heap.Aligned)
    (hSrcAl : strict = true → ∀ r ∈ (Node.record slots).slotRegions store source, r.1 % 8 = 0)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' (Node.blocks store' ptr (.record slots)) →
      NodeOwned heap' store' ptr (.record slots) →
      (Node.blocks store' ptr (.record slots)).Pairwise regionsDisjoint → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + nodeCopyCost (.record slots) →
      (strict = true → heap'.Aligned ∧
        ∀ b ∈ Node.blocks store' ptr (.record slots), b.1 % 8 = 0 ∧ b.2 % 8 = 0) →
      wpX strict m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wpX strict m (treeCopyAllocate shape src base ++
      treeCopyBegin shape src base [.localGet src] [.constI64 0] ++
      [.localGet base, .localSet (base + 1), .block 0 0 [.loop 0 0 (treeCopyBody shape base)],
        .localGet base] ++ rest) Q store s host := by
  have hCost : allocCost (8 * slots.length) ≤ nodeCopyCost (.record slots) := by
    simp only [nodeCopyCost]
    omega
  have hHigh0 : base < s.params.length + s.locals.length := Locals.lt_total (by omega)
  rw [List.append_assoc]
  refine wpX_treeCopyNew hm hRt (shape := shape) (dst := base) (input := src) (parent := none)
    (slots := slots) (rest := [.localGet base, .localSet (base + 1),
      .block 0 0 [.loop 0 0 (treeCopyBody shape base)], .localGet base] ++ rest)
    hAt hCap (hTrap.within (fun hRoom => hRoom.mono hCost)) hLayout hSource hSrc rfl
    (by omega) (by intro pos h; cases h) hLow hHigh0 hHeapAl
    (fun hs => hSrcAl hs (source.toNat, 8 * slots.length) (by simp [Node.slotRegions])) ?_
  intro heap' store' ptr hNew hRecord hTop hAlloc
  have hInv := CopyInv.startX (limit := heap.top.toNat + nodeCopyCost (.record slots)) hSource hNew
    hRecord hTop (Nat.le_refl _) fun hs => ⟨(hAlloc hs).1, (hAlloc hs).2.1, (hAlloc hs).2.2, hSrcAl hs⟩
  let sResult := setLocal s base (.i64 ptr)
  have hResult : sResult.get base = some (.i64 ptr) := Locals.get_setLocal_same hLow hHigh0
  have hFrameResult : Frame base s sResult := Frame.set hLow (by omega) (by omega)
  have hLow1 : sResult.params.length ≤ base + 1 := by change s.params.length ≤ base + 1; omega
  have hHigh1 : base + 1 < sResult.params.length + sResult.locals.length := by
    simp only [sResult, setLocal, List.length_set]
    exact Locals.lt_total (by omega)
  let sCopy := setLocal sResult (base + 1) (.i64 ptr)
  have hFrameCurrent : Frame base sResult sCopy := Frame.set hLow1 (by omega)
    (by rw [hFrameResult.positions]; omega)
  have hVars : CopyLocals base s ptr ptr sCopy := by
    refine ⟨hFrameResult.trans hFrameCurrent, ?_, Locals.get_setLocal_same hLow1 hHigh1, rfl⟩
    rw [Locals.get_setLocal_ne hLow1 (by omega)]
    exact hResult
  change wpX strict m ([.localGet base, .localSet (base + 1),
    .block 0 0 [.loop 0 0 (treeCopyBody shape base)], .localGet base] ++ rest) Q store' sResult host
  simp only [List.cons_append, List.nil_append, wpX_localGet_cons, hResult]
  refine wpX_localSet_local hLow1 hHigh1 ?_
  refine wpX_treeCopyLoop hm hRt hInv hVars ?_ ?_ hCap hTrap ?_
  · change s.params.length ≤ base
    exact hLow
  · rw [hVars.frame.positions]
    exact hHigh
  intro heap'' store'' s' hOwned hApart hStep hBudget hFrame hGet hValues hRootAl
  simp only [wpX_localGet_cons, hGet]
  simpa only [hValues] using hNext heap'' store'' s' ptr hStep hOwned hApart hFrame hBudget hRootAl

theorem wp_treeCopyRecord {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {src base : Nat} {source : UInt64}
    {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLayout : NodeLayout shape (.record slots)) (hSource : NodeBorrowed heap store source (.record slots))
    (hTrap : TrapOK (!decide (heap.Within store m (nodeCopyCost (.record slots)))) Q)
    (hSrc : s.get src = some (.i64 source)) (hSrcBase : src < base)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' (Node.blocks store' ptr (.record slots)) →
      NodeOwned heap' store' ptr (.record slots) →
      (Node.blocks store' ptr (.record slots)).Pairwise regionsDisjoint → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + nodeCopyCost (.record slots) →
      wp m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wp m (treeCopyAllocate shape src base ++
      treeCopyBegin shape src base [.localGet src] [.constI64 0] ++
      [.localGet base, .localSet (base + 1), .block 0 0 [.loop 0 0 (treeCopyBody shape base)],
        .localGet base] ++ rest) Q store s host :=
  wpX_treeCopyRecord (strict := false) hm nofun hAt hCap hLayout hSource hTrap hSrc hSrcBase hLow
    hHigh nofun nofun
    (fun heap' store' s' ptr a1 a2 a3 a4 a5 _ => hNext heap' store' s' ptr a1 a2 a3 a4 a5)
#print axioms wp_treeCopyRecord

theorem wpX_copyTree {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {src base : Nat} {source : UInt64}
    {value : Node} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLayout : NodeLayout shape value) (hSource : NodeBorrowed heap store source value)
    (hTrap : TrapOK (!decide (heap.Within store m (nodeCopyCost value))) Q)
    (hSrc : s.get src = some (.i64 source)) (hSrcBase : src < base)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hHeapAl : strict = true → heap.Aligned)
    (hSrcAl : strict = true → ∀ r ∈ value.slotRegions store source, r.1 % 8 = 0)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' (Node.blocks store' ptr value) →
      NodeOwned heap' store' ptr value → (Node.blocks store' ptr value).Pairwise regionsDisjoint →
      Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + nodeCopyCost value →
      (strict = true → heap'.Aligned ∧
        ∀ b ∈ Node.blocks store' ptr value, b.1 % 8 = 0 ∧ b.2 % 8 = 0) →
      wpX strict m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wpX strict m (treeCopyCode shape src base ++ rest) Q store s host := by
  let post : Assertion Unit := fun cont => match cont with
    | .Fallthrough store' s' => wpX strict m rest Q store' { s' with values := s'.values.take 1 ++ s.values } host
    | .Break 0 store' s' => wpX strict m rest Q store' { s' with values := s'.values.take 1 ++ s.values } host
    | .Break (k + 1) store' s' => Q (.Break k store' s')
    | other => Q other
  cases value with
  | null =>
    have hZero : source = 0 := hSource
    subst source
    simp only [treeCopyCode, List.cons_append, List.nil_append, wpX_localGet_cons, hSrc,
      wpX_eqzI64_cons]
    refine wpX_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_true, List.drop_zero]
    refine wpX.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    change wpX strict m [.constI64 0] post store s host
    simpa only [wpX_constI64_cons, wpX_nil, post, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append] using hNext heap store s 0 (Step.refl hAt _) rfl (by simp [Node.blocks])
        (Frame.refl base s) (by simp [nodeCopyCost])
        (fun hs => ⟨hHeapAl hs, by simp [Node.blocks]⟩)
  | record slots =>
    have hNonzero := hSource.1.nonzero
    simp only [treeCopyCode, List.cons_append, List.nil_append, wpX_localGet_cons, hSrc,
      wpX_eqzI64_cons, hNonzero, ite_false]
    refine wpX_iff_cons rfl ?_
    simp (config := { decide := true }) only [ite_false, List.drop_zero]
    refine wpX.conseq (Q := post) ?_ ?_
    · intro c hc
      cases c with
      | Break k _ _ => cases k <;> exact hc
      | _ => exact hc
    have hRun := wpX_treeCopyRecord hm hRt (host := host) (rest := []) (Q := post) hAt hCap hLayout hSource
      (hTrap.imp (Q' := post) (fun _ h => h)) hSrc hSrcBase hLow hHigh hHeapAl hSrcAl
      (fun heap' store' s' ptr hStep hOwned hApart hFrame hBudget hRootAl => by
        simpa only [wpX_nil, post, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append] using
          hNext heap' store' s' ptr hStep hOwned hApart hFrame hBudget hRootAl)
    simpa only [List.append_nil] using hRun

theorem wp_copyTree {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {src base : Nat} {source : UInt64}
    {value : Node} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLayout : NodeLayout shape value) (hSource : NodeBorrowed heap store source value)
    (hTrap : TrapOK (!decide (heap.Within store m (nodeCopyCost value))) Q)
    (hSrc : s.get src = some (.i64 source)) (hSrcBase : src < base)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ heap' store' s' ptr,
      Step heap store (fun _ => True) heap' store' (Node.blocks store' ptr value) →
      NodeOwned heap' store' ptr value → (Node.blocks store' ptr value).Pairwise regionsDisjoint →
      Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + nodeCopyCost value →
      wp m rest Q store' { s' with values := .i64 ptr :: s.values } host) :
    wp m (treeCopyCode shape src base ++ rest) Q store s host :=
  wpX_copyTree (strict := false) hm nofun hAt hCap hLayout hSource hTrap hSrc hSrcBase hLow hHigh
    nofun nofun
    (fun heap' store' s' ptr a1 a2 a3 a4 a5 _ => hNext heap' store' s' ptr a1 a2 a3 a4 a5)
#print axioms wp_copyTree

end Verified
