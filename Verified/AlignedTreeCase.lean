import Verified.AlignedTreeMatch
import Verified.TreeMatchBody
import Verified.OwnedExpr
import Verified.Bytes.StaticPrefix
import Verified.TreeDispatch

/-!
The match on a tree under the flag.  The empty case releases and evaluates its branch as
`spec_treeCase_empty` does.  The node case tests the tag at the tree's pointer, whose alignment
comes from the invariant of the matched variable, opens the record, and evaluates the branch in
a context whose invariant `HoldsA.openTree` gives.  After the branch, `HoldsA.popPrefix` drops
the fields and returns the invariant of the variables that stay live.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `spec_treeCase_empty` under the flag. -/
theorem specX_treeCase_empty {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t)
    (hn : shape.hasNull = true)
    (emptySpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (empty hn) env slots paid live)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool)
    (hNil : env.get x = .nil hn) :
    CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
      live := by
  intro h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
  let e := Expr.treeCase x empty nodes
  let L0 := fun i => live i || e.uses i
  let target := e.mode (slots.map Slot.mode)
  have hx : L0 x.index = true := by simp [L0, e, Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  obtain ⟨p, rfl, hNode⟩ := hRep
  have hp : p = 0 := by
    have hb := hNode.borrow
    rw [hNil] at hb
    exact hb
  subst p
  have hGet : s.get (slots.getD x.index default).loc = some (.i64 0) := by
    have hg := hold 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hMid := (treeCase_entryLive x empty nodes live).symm
  have hEntry : ∀ i, (live i || (empty hn).uses i) = true → L0 i = true := by
    intro i hi
    simp only [L0, e, Expr.uses, dite_eq_left hn, Bool.or_eq_true] at hi ⊢
    tauto
  have hTarget : (empty hn).mode (slots.map Slot.mode) = .owned → target = .owned := by
    intro hmE
    exact recordsJoin_init _ _ (by rw [dite_eq_left hn]; exact hmE)
  have hRoomE : base + t.width + max (empty hn).width (copyWidth t) ≤ h := by
    simp only [Expr.width, dite_eq_left hn] at hRoom
    have := Nat.le_max_left (max (empty hn).width (copyWidth t))
      (argsMax fun r => shape.bindWidth r + max treeCopyScratch
        (max (nodes r).width (copyWidth t)))
    omega
  have hPlaceE : (empty hn).placeArgs = true := by
    simp only [Expr.placeArgs, dite_eq_left hn, Bool.and_eq_true] at hPlace
    exact hPlace.1
  have hBudget : TrapOK (!((empty hn).fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        (empty hn).allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t ((empty hn).mode (slots.map Slot.mode)) target
          ((empty hn).denote funs env)))) Q := by
    simpa only [trapFlag, Expr.aborts, Bool.true_or, Bool.true_and, Expr.allocs, Expr.fits,
      hNil, L0, e, target, Expr.mode, modeAt, Nat.add_assoc] using hTrap
  simp only [Expr.code, Expr.usesFast_eq]
  rw [List.append_assoc, dite_eq_left hn]
  simp only [List.append_assoc, List.cons_append, List.nil_append, wpX_localGet_cons, hGet,
    wpX_eqzI64_cons]
  refine wpX_iff_cons rfl ?_
  simp (config := { decide := true }) only [↓reduceIte]
  simp_rw [show ∀ i, (live i || decide (i = x.index) ||
    (if h : shape.hasNull = true then (empty h).uses i else false) ||
    argsAny fun r => (nodes r).uses (i + shape.bindCount r)) = L0 i from congrFun hMid]
  simp only [dite_eq_left hn]
  have hModeCode : target = recordsJoin (fun r => (nodes r).mode
      (shape.modes r (slots.getD x.index default).mode (slots.map Slot.mode)))
      ((empty hn).mode (slots.map Slot.mode)) := by
    simp only [target, e, Expr.mode, Slot.modes_getD, dite_eq_left hn]
  rw [← hModeCode]
  refine (emptySpec env slots paid live).releaseCoerced hm hRA hCopy hTarget hh hpv
    (hVars.mono (Nat.le_add_right _ _)) hAt hAl hSafe hCap (by omega) hRoomE hPlaceE hEntry
    (rest := storeCode h base t.types) (hBudget.imp (fun _ hi => hi))
    (fun heap1 store1 s1 ws a hA1 hTop => by
      have hh1 := a.frame.positions.trans hh
      rw [← List.append_nil (storeCode h base t.types)]
      refine wpX_storeCode ws h base t.types s1 s.values a.rep.typed hh1
        (by rw [a.frame.params]; exact hBase) (by rw [Ty.types_length, hh1]; omega)
        (fun s2 hF hold _ => ?_)
      rw [wpX_nil]
      change wpX strict m (loadCode h base t.types ++ rest) Q store1
        { s2 with values := s.values } host
      refine wpX_loadCode ws a.rep.typed (hF.positions.trans hh1) hold ?_
      have hLower := a.lower hVars (Nat.le_add_right _ _) (fun i hi => by simp [hi])
      have hFrame : Frame base s1 { s2 with values := s.values } := hF.trans Frame.ofValues
      have hAfter : After env slots L0 live base heap store s t target ((empty hn).denote funs env)
          heap1 store1 { s2 with values := s.values } ws :=
        ⟨hLower.step, hLower.frame.trans hFrame, hLower.holds.agree hFrame, hLower.rep,
          hLower.apart.agree hLower.holds hFrame⟩
      apply hNext heap1 store1 _ ws
      · simpa only [e, L0, target, Expr.denote, hNil, Expr.mode] using hAfter
      · intro hs
        exact ⟨HoldsA.agree hLower.holds (hA1 hs).1 hFrame,
          by simpa only [e, L0, target, Expr.denote, hNil, Expr.mode] using (hA1 hs).2⟩
      · intro hf
        have hFit : (empty hn).fits funs fits env = true := by
          simpa only [Expr.fits, hNil] using hf
        have ht := hTop hFit
        simpa only [e, L0, target, Expr.paid, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
          Expr.allocs, hNil, Expr.mode, modeAt, Nat.add_assoc] using ht)

theorem spec_treeCase_empty {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t)
    (hn : shape.hasNull = true)
    (emptySpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (empty hn) env slots paid live)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool)
    (hNil : env.get x = .nil hn) :
    CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
      live :=
  CodeSpecX.false_iff.mp (specX_treeCase_empty (strict := false) hm nofun (copyCodeX hm) x empty
    nodes hn (fun env slots paid live => CodeSpecX.false_iff.mpr (emptySpec env slots paid live))
    env slots paid live hNil)

/-- `spec_treeCase_node` under the flag. -/
theorem specX_treeCase_node {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t) (r : Fin shape.records)
    (nodeSpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (nodes r) env slots paid live)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape)
    (hValue : env.get x = .node r words arrays buffers children) :
    CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
      live := by
  intro h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
  let e := Expr.treeCase x empty nodes
  let L0 := fun i => live i || e.uses i
  let L1 := fun i => live i || (nodes r).uses (i + shape.bindCount r)
  let rootMode := (slots.getD x.index default).mode
  let fieldBase := base + t.width
  let scratch := fieldBase + shape.bindWidth r
  let boundSlots := shape.slots r fieldBase rootMode slots
  let boundEnv := Env.treeFields shape r words arrays buffers children env
  let boundPaid := List.replicate (shape.bindCount r) false ++ paid
  let boundLive := shift (shape.bindCount r) live
  let LB := fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i
  let target := e.mode (slots.map Slot.mode)
  let rootCost := x.cost (slots.map Slot.mode) L1 (.node r words arrays buffers children)
  let bodyCost := (nodes r).allocs funs flags bounds (boundSlots.map Slot.mode) boundPaid boundLive
      boundEnv +
    coerceCost t ((nodes r).mode (boundSlots.map Slot.mode)) target ((nodes r).denote funs boundEnv)
  have hNodeUses : ∀ i, (nodes r).uses (i + shape.bindCount r) = true → e.uses i = true := by
    intro i hi
    simp only [e, Expr.uses, Bool.or_eq_true]
    exact Or.inr (argsAny_true.mpr ⟨r, hi⟩)
  have hL1 : ∀ i, L1 i = true → L0 i = true := by
    intro i hi
    simp only [L0, L1, Bool.or_eq_true] at hi ⊢
    rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (hNodeUses i hi)
  have hLive : ∀ i, live i = true → L1 i = true := by intro i hi; simp [L1, hi]
  have hEntry : ∀ i, (L1 i || (Expr.var (S := S) x).uses i) = true → L0 i = true := by
    intro i hi
    simp only [Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact hL1 i hi
    · simp only [Expr.uses] at hi
      simp only [L0, e, Expr.uses, Bool.or_eq_true]
      exact Or.inr (Or.inl (Or.inl hi))
  have hx : L0 x.index = true := by simp [L0, e, Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  obtain ⟨p0, rfl, hNode0⟩ := hRep
  have hBorrow0 : NodeBorrowed heap store p0
      (.record (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
        (fun i => (children i).toNode))) := by
    have hb := hNode0.borrow
    rw [hValue] at hb
    exact hb
  have hNonzero : p0 ≠ 0 := hBorrow0.1.nonzero
  have hSlotted :
      shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
        (fun i => (children i).toNode) ≠ [] := by
    intro hEmpty
    have hl := congrArg List.length hEmpty
    rw [shape.recordSlots_length] at hl
    exact absurd hl (Nat.ne_of_gt (shape.width_pos r))
  obtain ⟨-, hTagRoom⟩ := NodeBorrowed.tagRoom hBorrow0 hAt hSlotted
  have hTagRead : shape.tagged = true →
      store.mem.read64 p0.toUInt32 = UInt64.ofNat (shape.ctorIndex r) :=
    NodeBorrowed.tag hBorrow0 (by simp [TreeShape.recordSlots])
  have hGet : s.get (slots.getD x.index default).loc = some (.i64 p0) := by
    have hg := hold 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hp0Al : strict = true → p0.toNat % 8 = 0 := by
    intro hs
    have hA := (hAl hs).2 _ x hx [.i64 p0] hold rfl
    have hN := hNode0
    rw [hValue] at hA hN
    exact hA.treePtr hN
  have hNodeRoom : base + t.width + (shape.bindWidth r +
      max treeCopyScratch (max (nodes r).width (copyWidth t))) ≤ h := by
    simp only [Expr.width] at hRoom
    have hr : shape.bindWidth r + max treeCopyScratch (max (nodes r).width (copyWidth t)) ≤
        argsMax (fun r => shape.bindWidth r + max treeCopyScratch
          (max (nodes r).width (copyWidth t))) :=
      le_argsMax (fun r => shape.bindWidth r + max treeCopyScratch
        (max (nodes r).width (copyWidth t))) r
    have hmx := Nat.le_max_right
      (max (if h : shape.hasNull = true then (empty h).width else 0) (copyWidth t))
      (argsMax fun r => shape.bindWidth r + max treeCopyScratch
        (max (nodes r).width (copyWidth t)))
    omega
  have hScratch : scratch + max treeCopyScratch (max (nodes r).width (copyWidth t)) ≤ h := by
    dsimp only [scratch, fieldBase]
    omega
  have hRootRoom : scratch + (Expr.var (S := S) x).width ≤ h := by
    have := Nat.le_max_left treeCopyScratch (max (nodes r).width (copyWidth t))
    simpa only [Expr.width, Ty.copyScratch] using (show scratch + treeCopyScratch ≤ h by omega)
  have hBodyRoom : scratch + max (nodes r).width (copyWidth t) ≤ h := by
    have := Nat.le_max_right treeCopyScratch (max (nodes r).width (copyWidth t))
    omega
  have hFieldRoom : fieldBase + shape.bindWidth r ≤ h := by
    dsimp only [scratch] at hScratch
    omega
  have hBindPos : 1 ≤ shape.bindWidth r := by
    simp only [TreeShape.bindWidth, TreeShape.bindCount]
    omega
  have hPlaceN : (nodes r).placeArgs = true := by
    simp only [Expr.placeArgs, Bool.and_eq_true, Bool.not_eq_true'] at hPlace
    simpa using argsAny_eq_false hPlace.2 r
  have hModes : boundSlots.map Slot.mode = shape.modes r rootMode (slots.map Slot.mode) :=
    shape.slots_modes_full r fieldBase rootMode slots
  have hAlloc : e.allocs funs flags bounds (slots.map Slot.mode) paid live env =
      rootCost + bodyCost := by
    simp only [e, Expr.allocs, hValue, L1, rootCost, bodyCost, boundEnv, boundPaid, boundLive,
      hModes, rootMode, target, Expr.mode, modeAt, Slot.modes_getD, Nat.add_assoc]
  have hBudget : TrapOK (!((nodes r).fits funs fits boundEnv) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live + rootCost + bodyCost))) Q := by
    simpa only [trapFlag, Expr.aborts, Bool.true_or, Bool.true_and, Expr.allocs, Expr.fits,
      hValue, L0, e, rootCost, bodyCost, target, boundEnv, boundPaid, boundLive,
      hModes, rootMode, Expr.mode, modeAt, Slot.modes_getD, Nat.add_assoc] using hTrap
  have hPotLe : dyingPot store s env slots paid L0 L1 ≤ dyingPot store s env slots paid L0 live :=
    dyingPot_mono (fun _ hi => hi) hLive
  have hRootBudget : TrapOK (!(Expr.var (S := S) x).fits funs fits env ||
      !decide (heap.Within store m (dyingPot store s env slots paid L0 L1 +
        (Expr.var x).allocs funs flags bounds (slots.map Slot.mode) paid L1 env))) Q := by
    have hB := hBudget.allocPart (d' := false)
      (P' := heap.Within store m (dyingPot store s env slots paid L0 L1 + rootCost))
      nofun (fun _ hw => hw.mono (by omega))
    simpa only [Expr.fits, Expr.allocs, hValue, rootCost, Bool.not_true] using hB
  have hMid := (treeCase_entryLive x empty nodes live).symm
  let nc : Fin shape.records → Program := fun r =>
    releaseWhere Γ slots (fun i => (live i || decide (i = x.index) ||
        (if hn : shape.hasNull = true then (empty hn).uses i else false) ||
        argsAny fun r => (nodes r).uses (i + shape.bindCount r)) &&
      !((live i || (nodes r).uses (i + shape.bindCount r)) || decide (i = x.index))) ++
    x.code h slots (base + t.width + shape.bindWidth r)
      (fun i => live i || (nodes r).uses (i + shape.bindCount r)) ++
    [.localSet (base + t.width)] ++
    treeLoadFields h (base + t.width) (shape.wordTypes r) (base + t.width + 1)
      (base + t.width + 1 + shape.words r) shape.fieldStart (shape.fields r) ++
    treeLoadHeaps (base + t.width) (shape.kinds r)
      (base + t.width + 1 + shape.words r + shape.children r)
      (base + t.width + 1 + shape.words r + shape.children r + shape.arrays r)
      (shape.fieldStart + (shape.fields r).length) ++
    (if (slots.getD x.index default).mode = .owned then
      LeanExe.Runtime.headerStore (base + t.width) 8 [.constI64 0] else []) ++
    releaseWhere (shape.context r Γ)
      (shape.slots r (base + t.width) (slots.getD x.index default).mode slots)
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
    (nodes r).code (pool := pool) h
      (shape.slots r (base + t.width) (slots.getD x.index default).mode slots)
      (base + t.width + shape.bindWidth r) (shift (shape.bindCount r) live) ++
    coerceCode h t ((nodes r).mode
        (shape.modes r (slots.getD x.index default).mode (slots.map Slot.mode)))
      (recordsJoin (fun r => (nodes r).mode
          (shape.modes r (slots.getD x.index default).mode (slots.map Slot.mode)))
        (if hn : shape.hasNull = true then (empty hn).mode (slots.map Slot.mode)
          else .borrowed))
      (base + t.width + shape.bindWidth r) ++
    storeCode h base t.types
  have hBranch : RunsBranchX strict m host (nc r) (loadCode h base t.types ++ rest) Q store s := by
    intro rest' Q' hf ht
    let nodeTail := releaseWhere (shape.context r Γ) boundSlots
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
      (nodes r).code (pool := pool) h boundSlots scratch boundLive ++
      coerceCode h t ((nodes r).mode (boundSlots.map Slot.mode)) target scratch ++
      storeCode h base t.types
    have hRun := (specX_var (S := S) (funs := funs) (flags := flags) (bounds := bounds)
      (fits := fits) (host := host) (pv := pv) (strict := strict) hCopy x env slots paid L1).released (Q := Q')
      (rest := storeCode h fieldBase [.i64] ++
        ((treeLoadFields h fieldBase (shape.wordTypes r) (fieldBase + 1)
          (fieldBase + 1 + shape.words r) shape.fieldStart (shape.fields r) ++
          treeLoadHeaps fieldBase (shape.kinds r)
            (fieldBase + 1 + shape.words r + shape.children r)
            (fieldBase + 1 + shape.words r + shape.children r + shape.arrays r)
            (shape.fieldStart + (shape.fields r).length) ++
          (if rootMode = .owned then headerStore fieldBase 8 [.constI64 0] else [])) ++
          (nodeTail ++ rest')))
      hm hRA hh hpv
      (hVars.mono (by dsimp only [scratch, fieldBase]; omega)) hAt hAl hSafe hCap
      (by dsimp only [scratch, fieldBase]; omega) hRootRoom rfl hEntry
      (hRootBudget.imp (fun st hq => ht st hq))
      (fun heap1 store1 s1 ws a hA1 hTop => by
        obtain ⟨p, rfl, hRoot⟩ := a.rep
        have hAfter := a.lower hVars (by dsimp only [scratch, fieldBase]; omega) hL1
        have aRoot : After env slots L0 L1 base heap store s (.tree shape) rootMode
            (.node r words arrays buffers children) heap1 store1 s1 [.i64 p] := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using hAfter
        have hRootNode : rootMode.node heap1 store1 p
            (Tree.node r words arrays buffers children).toNode := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using hRoot
        have hRootAl : strict = true → HoldsA env slots L1 heap1 store1 s1 ∧
            Ty.AlignedVal rootMode store1 (.tree shape) [.i64 p]
              (.node r words arrays buffers children) := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using hA1
        have hTopRoot : heap1.top.toNat ≤ heap.top.toNat +
            dyingPot store s env slots paid L0 L1 + rootCost := by
          simpa only [Expr.fits, Expr.allocs, Expr.denote, hValue, rootCost] using hTop rfl
        have hh1 := aRoot.frame.positions.trans hh
        have hRoomField1 : fieldBase + 1 ≤ s1.positions := by rw [hh1]; omega
        change wpX strict m (storeCode h fieldBase [.i64] ++ _) _ store1
          { s1 with values := [.i64 p].reverse ++ s.values } host
        refine wpX_storeCode (Q := Q') [.i64 p] h fieldBase [.i64] s1 s.values rfl hh1
          (by rw [aRoot.frame.params]; dsimp only [fieldBase]; omega) hRoomField1
          (fun s2 hF2 hold2 _ => ?_)
        have hPtr2 : ({ s2 with values := s.values } : Locals).get fieldBase = some (.i64 p) := by
          have hg := hold2 0 (by simp)
          simpa [slotIndex] using hg
        have hFrame2 : Frame base s1 { s2 with values := s.values } :=
          (hF2.mono (by dsimp only [fieldBase]; omega)).trans Frame.ofValues
        have hOpen := wpX_openTree (strict := strict) (m := m) (host := host) (Q := Q') (rest := nodeTail ++ rest')
          (by rw [Locals.positions_values, hF2.positions, hh1]) aRoot.step.at_ hRootNode hPtr2
          (fun hs => (hRootAl hs).2.treePtr hRootNode)
          (by rw [hF2.params, aRoot.frame.params]; dsimp only [fieldBase]; omega)
          (by rw [Locals.positions_values, hF2.positions, hh1]; exact hFieldRoom)
          (fun s3 hF3 hStack3 hPrefix hDetach hSubset => by
          have hOpenFrame : Frame base s1 s3 := hFrame2.trans
            (hF3.mono (by dsimp only [fieldBase]; omega))
          obtain ⟨step3, frame3, outer3, fields3, fresh3⟩ := aRoot.openTreeFields
            hOpenFrame (by dsimp only [fieldBase]; omega) hDetach hPrefix hSubset
          have hBodyAl : strict = true → HoldsA boundEnv boundSlots LB heap1
              (treeDetachStore rootMode store1 p) s3 := fun hs =>
            HoldsA.openTree aRoot (hRootAl hs).1 (hRootAl hs).2 hOpenFrame hDetach hSubset
          have hSafeCount : (shape.context r []).length = shape.bindCount r := by
            simp only [TreeShape.context_length, List.length_nil, Nat.add_zero]
          have hSafeLength : (shape.slots r fieldBase rootMode []).length =
              (shape.context r []).length := by
            rw [shape.slots_length r, hSafeCount]
          have hSafePrefix := hSafe.bindPrefixStep hVars step3 frame3 outer3 hSafeLength fresh3 hL1
            (bodyLive := LB) (fun i hi => by simpa [LB, hSafeCount, shift] using hi)
          rw [← shape.slots_append r] at hSafePrefix
          have hSafeFields := hSafePrefix.ofHEq (shape.context_append r Γ)
            (Env.treeFields_append shape r words arrays buffers children env)
          have hh3 := frame3.positions.trans hh
          have hp3 := frame3.params.trans hpv
          have hStack : s3.values = s.values := hStack3
          have hTarget : (nodes r).mode (boundSlots.map Slot.mode) = .owned →
              target = .owned := by
            intro hmN
            simp only [target, e, Expr.mode, Slot.modes_getD]
            refine recordsJoin_at _ _ r ?_
            rw [← hModes]
            exact hmN
          have hBodyBudget : TrapOK (!((nodes r).fits funs fits boundEnv) || !decide
              (heap1.Within (treeDetachStore rootMode store1 p) m
                (dyingPot (treeDetachStore rootMode store1 p) s3 boundEnv boundSlots boundPaid LB
                    boundLive +
                  (nodes r).allocs funs flags bounds (boundSlots.map Slot.mode) boundPaid boundLive
                    boundEnv +
                  coerceCost t ((nodes r).mode (boundSlots.map Slot.mode)) target
                    ((nodes r).denote funs boundEnv)))) Q := by
            have hB := hBudget.allocPart id (fun _ hw => treeCase_bodyWithin (shape := shape)
              (r := r) (mode := rootMode) (fieldBase := fieldBase) (words := words)
              (arrays := arrays) (buffers := buffers)
              (children := children) hVars step3 frame3 hL1 hLive hTopRoot hw)
            simpa only [bodyCost, boundEnv, boundSlots, boundPaid, boundLive, LB,
              Nat.add_assoc] using hB
          dsimp only [nodeTail]
          simp only [List.append_assoc]
          rw [← treeCase_releaseFields (nodes r) live]
          refine (nodeSpec boundEnv boundSlots boundPaid boundLive).releaseCoerced (Q := Q') hm hRA hCopy
            hTarget hh3 hp3 fields3 hDetach.at_ hBodyAl hSafeFields (by rw [step3.cap m]; exact hCap)
            (by rw [frame3.params]; dsimp only [scratch, fieldBase]; omega)
            hBodyRoom hPlaceN (treeCase_fieldsLive (nodes r) live)
            (rest := storeCode h base t.types ++ rest')
            (hBodyBudget.imp (fun st hq => ht st hq))
            (fun heap4 store4 s4 ws4 body hA4 hTop4 => by
              dsimp only [boundEnv, boundSlots, boundLive] at body
              rw [shape.slots_append r] at body
              have hCount : (shape.context r []).length = shape.bindCount r := by
                simp only [shape.context_length r, List.length_nil, Nat.add_zero]
              have hLength : (shape.slots r fieldBase rootMode []).length =
                  (shape.context r []).length := by
                rw [shape.slots_length r, hCount]
              have hOuterAl : strict = true → HoldsA env slots live heap4 store4 s4 := by
                intro hs
                have hA := (hA4 hs).1
                dsimp only [boundEnv, boundSlots, boundLive] at hA
                rw [shape.slots_append r] at hA
                have hA' := (hA.ofHEq (shape.context_append r Γ).symm
                  (Env.treeFields_append shape r words arrays buffers children env).symm).popPrefix
                  hLength
                exact hA'.live_mono (fun i hi => by simpa [hCount, shift] using hi)
              have body' := body.ofHEq (shape.context_append r Γ).symm
                (Env.treeFields_append shape r words arrays buffers children env).symm
              have aAll := After.bindPrefixStep hVars step3 frame3 outer3 (Frame.refl _ _)
                hLength (by simpa only [hCount] using body')
                (by dsimp only [scratch, fieldBase]; omega)
                (fun keep hr u y hm w hold length b hb =>
                  hr b (fresh3 u y hm w hold length b hb))
                (fun i hi => by simpa [hCount, shift] using hi) hL1 hLive
              have hh4 := aAll.frame.positions.trans hh
              rw [hStack]
              refine wpX_storeCode (Q := Q') ws4 h base t.types s4 s.values aAll.rep.typed hh4
                (by rw [aAll.frame.params]; exact hBase) (by
                  rw [Ty.types_length, hh4]
                  dsimp only [fieldBase] at hFieldRoom
                  omega)
                (fun s5 hF5 hold5 _ => ?_)
              refine hf store4 { s5 with values := s.values } rfl ?_
              refine wpX_loadCode ws4 aAll.rep.typed (hF5.positions.trans hh4) hold5 ?_
              have hF : Frame base s4 { s5 with values := s.values } := hF5.trans Frame.ofValues
              apply hNext heap4 store4 _ ws4
              · simpa only [e, L0, target, Expr.denote, hValue, boundEnv] using
                  aAll.reframe hF
              · intro hs
                exact ⟨HoldsA.agree aAll.holds (hOuterAl hs) hF,
                  by simpa only [e, target, Expr.denote, hValue, boundEnv] using (hA4 hs).2⟩
              · intro hfit
                have hf' : (nodes r).fits funs fits boundEnv = true := by
                  simpa only [Expr.fits, hValue, boundEnv] using hfit
                have ht4 := hTop4 hf'
                have hd := dyingPot_treeEntry (treeDetachStore rootMode store1 p) s3 env
                  shape r words arrays buffers children fieldBase rootMode slots paid L1 live
                rw [dyingPot_step hVars step3 frame3 hL1 L1 live (fun _ hi => hi)] at hd
                have hs := dyingPot_split (store := store) (s := s) (env := env) (slots := slots)
                  (paid := paid) L0 L1 live hL1 hLive
                simp only [boundEnv, boundSlots, boundPaid, boundLive] at ht4
                rw [hd] at ht4
                simp only [Expr.paid, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
                change heap4.top.toNat ≤ heap.top.toNat +
                  dyingPot store s env slots paid L0 live +
                  e.allocs funs flags bounds (slots.map Slot.mode) paid live env
                rw [hAlloc]
                dsimp only [bodyCost, boundEnv, boundSlots, boundPaid, boundLive]
                omega))
        simpa only [List.append_assoc] using hOpen)
    have hMidL0 : (fun i => live i || decide (i = x.index) ||
        (if hn : shape.hasNull = true then (empty hn).uses i else false) ||
        argsAny fun r => (nodes r).uses (i + shape.bindCount r)) = L0 := hMid
    dsimp only [nc]
    simp_rw [show ∀ i, (live i || decide (i = x.index) ||
      (if hn : shape.hasNull = true then (empty hn).uses i else false) ||
      argsAny fun r => (nodes r).uses (i + shape.bindCount r)) = L0 i from congrFun hMidL0]
    convert hRun using 1
    simp only [nodeTail, Expr.code, Expr.uses, L0, L1, fieldBase, scratch, boundSlots,
      boundLive, rootMode, target, e, Expr.mode, Slot.modes_getD, storeCode, slotIndex,
      List.append_assoc, List.cons_append, List.nil_append, nat_beq_decide,
      TreeShape.slots_modes_full]
  simp only [Expr.code, Expr.usesFast_eq]
  rw [List.append_assoc]
  by_cases hn : shape.hasNull = true
  · rw [dite_eq_left hn]
    simp only [List.cons_append, List.nil_append, wpX_localGet_cons, hGet, wpX_eqzI64_cons,
      hNonzero, ↓reduceIte]
    refine wpX_iff_cons rfl ?_
    simp (config := { decide := true }) only [↓reduceIte]
    rw [← List.append_nil (shape.dispatchCode _ _)]
    refine wpX_dispatchCode r nc hGet hTagRoom hp0Al hTagRead (hBranch.mono ?_ (fun _ hq => hq))
    intro st s' hv hw
    rw [wpX_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [← hv]
    exact hw
  · rw [dite_eq_right hn]
    exact wpX_dispatchCode r nc hGet hTagRoom hp0Al hTagRead hBranch

theorem spec_treeCase_node {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t) (r : Fin shape.records)
    (nodeSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (nodes r) env slots paid live)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape)
    (hValue : env.get x = .node r words arrays buffers children) :
    CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
      live :=
  CodeSpecX.false_iff.mp (specX_treeCase_node (strict := false) hm nofun (copyCodeX hm) x empty
    nodes r (fun env slots paid live => CodeSpecX.false_iff.mpr (nodeSpec env slots paid live)) env
    slots paid live words arrays buffers children hValue)

/-- `spec_treeCase` under the flag. -/
theorem specX_treeCase {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t)
    (emptySpec : ∀ hn env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (empty hn) env slots paid live)
    (nodeSpec : ∀ r env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (nodes r) env slots paid live) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
        live := by
  intro env slots paid live
  cases hv : env.get x with
  | nil hn =>
    exact specX_treeCase_empty hm hRA hCopy x empty nodes hn (emptySpec hn) env slots paid live hv
  | node r words arrays buffers children =>
    exact specX_treeCase_node hm hRA hCopy x empty nodes r (nodeSpec r) env slots paid live words arrays
      buffers children hv

theorem spec_treeCase {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t)
    (emptySpec : ∀ hn env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (empty hn) env slots paid live)
    (nodeSpec : ∀ r env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (nodes r) env slots paid live) :
    ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
        live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_treeCase (strict := false) hm nofun (copyCodeX hm) x empty nodes
      (fun hn env slots paid live => CodeSpecX.false_iff.mpr (emptySpec hn env slots paid live))
      (fun r env slots paid live => CodeSpecX.false_iff.mpr (nodeSpec r env slots paid live)) env
      slots paid live)

end Verified
