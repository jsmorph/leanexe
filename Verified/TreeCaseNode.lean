import Verified.TreeCaseEmpty
import Verified.ReleasedExpr
import Verified.Bytes.StaticPrefix
import Verified.TreeDispatch

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem spec_treeCase_node {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t) (r : Fin shape.records)
    (nodeSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (nodes r) env slots paid live)
    (env : Env Γ) (slots : List Slot) (paid : List Bool) (live : Nat → Bool)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (children : Fin (shape.children r) → Tree shape)
    (hValue : env.get x = .node r words arrays buffers children) :
    CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
      live := by
  intro h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
  let e := Expr.treeCase x empty nodes
  let L0 := fun i => live i || e.uses i
  let L1 := fun i => live i || (nodes r).uses (i + shape.bindCount r)
  let rootMode := (slots.getD x.index default).mode
  let fieldBase := base + t.width
  let scratch := fieldBase + shape.bindCount r
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
      (.record (shape.recordSlots r (shape.slotWords r words) (fun i => (children i).toNode))) := by
    have hb := hNode0.borrow
    rw [hValue] at hb
    exact hb
  have hNonzero : p0 ≠ 0 := hBorrow0.1.nonzero
  have hSlotted :
      shape.recordSlots r (shape.slotWords r words) (fun i => (children i).toNode) ≠ [] := by
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
  have hNodeRoom : base + t.width + (shape.bindCount r +
      max treeCopyScratch (max (nodes r).width (copyWidth t))) ≤ h := by
    simp only [Expr.width] at hRoom
    have hr : shape.bindCount r + max treeCopyScratch (max (nodes r).width (copyWidth t)) ≤
        argsMax (fun r => shape.bindCount r + max treeCopyScratch
          (max (nodes r).width (copyWidth t))) :=
      le_argsMax (fun r => shape.bindCount r + max treeCopyScratch
        (max (nodes r).width (copyWidth t))) r
    have hmx := Nat.le_max_right
      (max (if h : shape.hasNull = true then (empty h).width else 0) (copyWidth t))
      (argsMax fun r => shape.bindCount r + max treeCopyScratch
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
  have hFieldRoom : fieldBase + 1 + (shape.fields r).length ≤ h := by
    have hc := shape.words_children r
    dsimp only [scratch] at hScratch
    simp only [TreeShape.bindCount] at hScratch
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
    x.code h slots (base + t.width + shape.bindCount r)
      (fun i => live i || (nodes r).uses (i + shape.bindCount r)) ++
    [.localSet (base + t.width)] ++
    treeLoadFields h (base + t.width) (shape.wordTypes r) (base + t.width + 1)
      (base + t.width + 1 + shape.words r) shape.fieldStart (shape.fields r) ++
    (if (slots.getD x.index default).mode = .owned then
      LeanExe.Runtime.headerStore (base + t.width) 8 [.constI64 0] else []) ++
    releaseWhere (shape.context r Γ)
      (shape.slots r (base + t.width) (slots.getD x.index default).mode slots)
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
    (nodes r).code (pool := pool) h
      (shape.slots r (base + t.width) (slots.getD x.index default).mode slots)
      (base + t.width + shape.bindCount r) (shift (shape.bindCount r) live) ++
    coerceCode h t ((nodes r).mode
        (shape.modes r (slots.getD x.index default).mode (slots.map Slot.mode)))
      (recordsJoin (fun r => (nodes r).mode
          (shape.modes r (slots.getD x.index default).mode (slots.map Slot.mode)))
        (if hn : shape.hasNull = true then (empty hn).mode (slots.map Slot.mode)
          else .borrowed))
      (base + t.width + shape.bindCount r) ++
    storeCode h base t.types
  have hBranch : RunsBranch m host (nc r) (loadCode h base t.types ++ rest) Q store s := by
    intro rest' Q' hf ht
    let nodeTail := releaseWhere (shape.context r Γ) boundSlots
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
      (nodes r).code (pool := pool) h boundSlots scratch boundLive ++
      coerceCode h t ((nodes r).mode (boundSlots.map Slot.mode)) target scratch ++
      storeCode h base t.types
    have hRun := (spec_var (S := S) (funs := funs) (flags := flags) (bounds := bounds)
      (fits := fits) (host := host) (pv := pv) hm x env slots paid L1).released (Q := Q')
      (rest := storeCode h fieldBase [.i64] ++
        ((treeLoadFields h fieldBase (shape.wordTypes r) (fieldBase + 1)
          (fieldBase + 1 + shape.words r) shape.fieldStart (shape.fields r) ++
          (if rootMode = .owned then headerStore fieldBase 8 [.constI64 0] else [])) ++
          (nodeTail ++ rest')))
      hm hh hpv
      (hVars.mono (by dsimp only [scratch, fieldBase]; omega)) hAt hSafe hCap
      (by dsimp only [scratch, fieldBase]; omega) hRootRoom rfl hEntry
      (hRootBudget.imp (fun st hq => ht st hq))
      (fun heap1 store1 s1 ws a hTop => by
        obtain ⟨p, rfl, hRoot⟩ := a.rep
        have hAfter := a.lower hVars (by dsimp only [scratch, fieldBase]; omega) hL1
        have aRoot : After env slots L0 L1 base heap store s (.tree shape) rootMode
            (.node r words arrays buffers children) heap1 store1 s1 [.i64 p] := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using hAfter
        have hRootNode : rootMode.node heap1 store1 p (Tree.node r words arrays buffers children).toNode := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using hRoot
        have hTopRoot : heap1.top.toNat ≤ heap.top.toNat +
            dyingPot store s env slots paid L0 L1 + rootCost := by
          simpa only [Expr.fits, Expr.allocs, Expr.denote, hValue, rootCost] using hTop rfl
        have hh1 := aRoot.frame.positions.trans hh
        have hRoomField1 : fieldBase + 1 ≤ s1.positions := by rw [hh1]; omega
        change wp m (storeCode h fieldBase [.i64] ++ _) _ store1
          { s1 with values := [.i64 p].reverse ++ s.values } host
        refine wp_storeCode (Q := Q') [.i64 p] h fieldBase [.i64] s1 s.values rfl hh1
          (by rw [aRoot.frame.params]; dsimp only [fieldBase]; omega) hRoomField1
          (fun s2 hF2 hold2 _ => ?_)
        have hPtr2 : ({ s2 with values := s.values } : Locals).get fieldBase = some (.i64 p) := by
          have hg := hold2 0 (by simp)
          simpa [slotIndex] using hg
        have hFrame2 : Frame base s1 { s2 with values := s.values } :=
          (hF2.mono (by dsimp only [fieldBase]; omega)).trans Frame.ofValues
        have hOpen := wp_openTree (m := m) (host := host) (Q := Q') (rest := nodeTail ++ rest')
          (by rw [Locals.positions_values, hF2.positions, hh1]) aRoot.step.at_ hRootNode hPtr2
          (by rw [hF2.params, aRoot.frame.params]; dsimp only [fieldBase]; omega)
          (by rw [Locals.positions_values, hF2.positions, hh1]; exact hFieldRoom)
          (fun s3 hF3 hStack3 hPrefix hDetach hSubset => by
          have hOpenFrame : Frame base s1 s3 := hFrame2.trans
            (hF3.mono (by dsimp only [fieldBase]; omega))
          obtain ⟨step3, frame3, outer3, fields3, fresh3⟩ := aRoot.openTreeFields
            hOpenFrame (by dsimp only [fieldBase]; omega) hDetach hPrefix hSubset
          have hSafeCount : (shape.context r []).length = shape.bindCount r := by
            simp only [TreeShape.context_length, List.length_nil, Nat.add_zero]
          have hSafeLength : (shape.slots r fieldBase rootMode []).length =
              (shape.context r []).length := by
            rw [shape.slots_length r, hSafeCount]
          have hSafePrefix := hSafe.bindPrefixStep hVars step3 frame3 outer3 hSafeLength fresh3 hL1
            (bodyLive := LB) (fun i hi => by simpa [LB, hSafeCount, shift] using hi)
          rw [← shape.slots_append r] at hSafePrefix
          have hSafeFields := hSafePrefix.ofHEq (shape.context_append r Γ)
            (Env.treeFields_append shape r words children env)
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
              (children := children) hVars step3 frame3 hL1 hLive hTopRoot hw)
            simpa only [bodyCost, boundEnv, boundSlots, boundPaid, boundLive, LB,
              Nat.add_assoc] using hB
          dsimp only [nodeTail]
          simp only [List.append_assoc]
          rw [← treeCase_releaseFields (nodes r) live]
          refine (nodeSpec boundEnv boundSlots boundPaid boundLive).releaseCoerced (Q := Q') hm
            hTarget hh3 hp3 fields3 hDetach.at_ hSafeFields (by rw [step3.cap m]; exact hCap)
            (by rw [frame3.params]; dsimp only [scratch, fieldBase]; omega)
            hBodyRoom hPlaceN (treeCase_fieldsLive (nodes r) live)
            (rest := storeCode h base t.types ++ rest')
            (hBodyBudget.imp (fun st hq => ht st hq))
            (fun heap4 store4 s4 ws4 body hTop4 => by
              dsimp only [boundEnv, boundSlots, boundLive] at body
              rw [shape.slots_append r] at body
              have hCount : (shape.context r []).length = shape.bindCount r := by
                simp only [shape.context_length r, List.length_nil, Nat.add_zero]
              have hLength : (shape.slots r fieldBase rootMode []).length =
                  (shape.context r []).length := by
                rw [shape.slots_length r, hCount]
              have body' := body.ofHEq (shape.context_append r Γ).symm
                (Env.treeFields_append shape r words children env).symm
              have aAll := After.bindPrefixStep hVars step3 frame3 outer3 (Frame.refl _ _)
                hLength (by simpa only [hCount] using body')
                (by dsimp only [scratch, fieldBase]; omega)
                (fun keep hr u y hm w hold length b hb =>
                  hr b (fresh3 u y hm w hold length b hb))
                (fun i hi => by simpa [hCount, shift] using hi) hL1 hLive
              have hh4 := aAll.frame.positions.trans hh
              rw [hStack]
              refine wp_storeCode (Q := Q') ws4 h base t.types s4 s.values aAll.rep.typed hh4
                (by rw [aAll.frame.params]; exact hBase) (by
                  rw [Ty.types_length, hh4]
                  dsimp only [fieldBase] at hFieldRoom
                  omega)
                (fun s5 hF5 hold5 _ => ?_)
              refine hf store4 { s5 with values := s.values } rfl ?_
              refine wp_loadCode ws4 aAll.rep.typed (hF5.positions.trans hh4) hold5 ?_
              have hF : Frame base s4 { s5 with values := s.values } := hF5.trans Frame.ofValues
              apply hNext heap4 store4 _ ws4
              · simpa only [e, L0, target, Expr.denote, hValue, boundEnv] using
                  aAll.reframe hF
              · intro hfit
                have hf' : (nodes r).fits funs fits boundEnv = true := by
                  simpa only [Expr.fits, hValue, boundEnv] using hfit
                have ht4 := hTop4 hf'
                have hd := dyingPot_treeEntry (treeDetachStore rootMode store1 p) s3 env
                  shape r words children fieldBase rootMode slots paid L1 live
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
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, hGet, wp_eqzI64_cons,
      hNonzero, ↓reduceIte, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    simp (config := { decide := true }) only [↓reduceIte]
    rw [← List.append_nil (shape.dispatchCode _ _)]
    refine wp_dispatchCode r nc hGet hTagRoom hTagRead (hBranch.mono ?_ (fun _ hq => hq))
    intro st s' hv hw
    rw [wp_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [← hv]
    exact hw
  · rw [dite_eq_right hn]
    exact wp_dispatchCode r nc hGet hTagRoom hTagRead hBranch

end Verified
