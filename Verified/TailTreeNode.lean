import Verified.TailTreeEmpty
import Verified.TailBindPrefix
import Verified.TailAllocExpand
import Verified.TreeMatchPotential
import Verified.ReleasedExpr
import Verified.Bytes.StaticPrefix
import Verified.TreeDispatch

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem tail_treeCase_node {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : shape.hasNull = true → TailBody S params result Γ)
    (nodes : (r : Fin shape.records) → TailBody S params result (shape.context r Γ))
    (r : Fin shape.records)
    (nodeSpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (nodes r))
    (env : Env Γ) (words : Fin (shape.words r) → UInt64)
    (children : Fin (shape.children r) → Tree shape)
    (hValue : env.get x = .node r words children) :
    TailCodeSpecAt (pool := pool) m funs flags bounds fits host pv targetModes (.treeCase x empty nodes) env := by
  intro slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let outer := TailBody.treeCase x empty nodes
  let L0 := outer.uses
  let L1 := fun i => (nodes r).uses (i + shape.bindCount r)
  let rootMode := (slots.getD x.index default).mode
  let scratch := base + shape.bindCount r
  let boundSlots := shape.slots r base rootMode slots
  let boundEnv := Env.treeFields shape r words children env
  let boundPaid := List.replicate (shape.bindCount r) false ++ paid
  let LB := fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i
  let rootCost := x.cost (slots.map Slot.mode) L1 (.node r words children)
  let bodyCost := (nodes r).allocs funs flags bounds targetModes nextPaid
    (boundSlots.map Slot.mode) boundPaid boundEnv
  have hL1 : ∀ i, L1 i = true → L0 i = true := by
    intro i hi
    simp only [L0, outer, TailBody.uses, Bool.or_eq_true]
    exact Or.inr (argsAny_true.mpr ⟨r, hi⟩)
  have hEntry : ∀ i, (L1 i || (Expr.var (S := S) x).uses i) = true → L0 i = true := by
    intro i hi
    simp only [Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact hL1 i hi
    · simp only [Expr.uses] at hi
      simp only [L0, outer, TailBody.uses, Bool.or_eq_true]
      exact Or.inl (Or.inl hi)
  have hx : L0 x.index = true := by simp [L0, outer, TailBody.uses]
  obtain ⟨_, ws0, hold0, rep0⟩ := hVars.get x hx
  obtain ⟨p0, rfl, node0⟩ := rep0
  have hBorrow0 : NodeBorrowed heap store p0
      (.record (shape.recordSlots r words (fun i => (children i).toNode))) := by
    have hb := node0.borrow
    rw [hValue] at hb
    exact hb
  have hNonzero : p0 ≠ 0 := hBorrow0.1.nonzero
  have hSlotted : shape.recordSlots r words (fun i => (children i).toNode) ≠ [] := by
    intro hEmpty
    have hl := congrArg List.length hEmpty
    rw [shape.recordSlots_length] at hl
    exact absurd hl (Nat.ne_of_gt (shape.width_pos r))
  obtain ⟨-, hTagRoom⟩ := NodeBorrowed.tagRoom hBorrow0 hAt hSlotted
  have hTagRead : shape.tagged = true →
      store.mem.read64 p0.toUInt32 = UInt64.ofNat (shape.ctorIndex r) :=
    NodeBorrowed.tag hBorrow0 (by simp [TreeShape.recordSlots])
  have hGet : s.get (slots.getD x.index default).loc = some (.i64 p0) := by
    have hg := hold0 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hScratch : scratch + max treeCopyScratch ((nodes r).width targetModes) ≤ h := by
    have hr : shape.bindCount r + max treeCopyScratch ((nodes r).width targetModes) ≤
        argsMax (fun r => shape.bindCount r + max treeCopyScratch ((nodes r).width targetModes)) :=
      le_argsMax (fun r => shape.bindCount r + max treeCopyScratch
        ((nodes r).width targetModes)) r
    have := Nat.le_max_right
      (if h : shape.hasNull = true then (empty h).width targetModes else 0)
      (argsMax fun r => shape.bindCount r + max treeCopyScratch ((nodes r).width targetModes))
    simp only [TailBody.width] at hRoom
    dsimp only [scratch]
    omega
  have hRootRoom : scratch + (Expr.var (S := S) x).width ≤ h := by
    have := Nat.le_max_left treeCopyScratch ((nodes r).width targetModes)
    simpa only [Expr.width, Ty.copyScratch] using (show scratch + treeCopyScratch ≤ h by omega)
  have hBodyRoom : scratch + (nodes r).width targetModes ≤ h := by
    have := Nat.le_max_right treeCopyScratch ((nodes r).width targetModes)
    omega
  have hFieldRoom : base + 1 + (shape.fields r).length ≤ h := by
    have hc := shape.words_children r
    dsimp only [scratch] at hScratch
    simp only [TreeShape.bindCount] at hScratch
    omega
  have hModes : boundSlots.map Slot.mode = shape.modes r rootMode (slots.map Slot.mode) :=
    shape.slots_modes_full r base rootMode slots
  have hPlaceN : (nodes r).placeArgs targetModes (boundSlots.map Slot.mode) = true := by
    simp only [TailBody.placeArgs, Bool.and_eq_true, Bool.not_eq_true'] at hPlace
    have := argsAny_eq_false hPlace.2 r
    simp only [Bool.not_eq_false'] at this
    rw [hModes]
    simpa only [rootMode, Slot.modes_getD] using this
  have hPaidN : resultPaid = true →
      (nodes r).paidResult flags (boundSlots.map Slot.mode) boundPaid = true := by
    intro hp
    have hf := hPaid hp
    simp only [TailBody.paidResult, Bool.false_eq_true] at hf
  have hAlloc : outer.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env =
      rootCost + bodyCost := by
    simp only [outer, TailBody.allocs, hValue, L1, rootCost, bodyCost, boundEnv, boundPaid,
      hModes, rootMode, modeAt, Slot.modes_getD]
  have hBudget : TrapOK (!((nodes r).fits funs fits boundEnv) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 (fun _ => false) + rootCost + bodyCost))) Q := by
    simpa only [tailTrapFlag, TailBody.aborts, Bool.true_or, Bool.true_and,
      TailBody.allocs, TailBody.fits, hValue, L0, outer, rootCost, bodyCost, boundEnv, boundPaid,
      hModes, rootMode, modeAt, Slot.modes_getD, Nat.add_assoc] using hTrap
  have hPotLe : dyingPot store s env slots paid L0 L1 ≤
      dyingPot store s env slots paid L0 (fun _ => false) :=
    dyingPot_mono (fun _ hi => hi) nofun
  have hRootBudget : TrapOK (!(Expr.var (S := S) x).fits funs fits env ||
      !decide (heap.Within store m (dyingPot store s env slots paid L0 L1 +
        (Expr.var x).allocs funs flags bounds (slots.map Slot.mode) paid L1 env))) Q := by
    have hb := hBudget.allocPart (d' := false)
      (P' := heap.Within store m (dyingPot store s env slots paid L0 L1 + rootCost))
      nofun (fun _ hw => hw.mono (by omega))
    simpa only [Expr.fits, Expr.allocs, hValue, rootCost, Bool.not_true] using hb
  let labels := if shape.hasNull = true then 1 else 0
  let depth := fun r : Fin shape.records =>
    if r.val + 1 < shape.records then r.val + 1 else r.val
  let nc : Fin shape.records → Program := fun r =>
    releaseWhere Γ slots (fun i => (decide (i = x.index) ||
        (if hn : shape.hasNull = true then (empty hn).uses i else false) ||
        argsAny fun r => (nodes r).uses (i + shape.bindCount r)) &&
      !((nodes r).uses (i + shape.bindCount r) || decide (i = x.index))) ++
    x.code h slots (base + shape.bindCount r) (fun i => (nodes r).uses (i + shape.bindCount r)) ++
    [.localSet base] ++
    treeLoadFields base (base + 1) (base + 1 + shape.words r) shape.fieldStart (shape.fields r) ++
    (if (slots.getD x.index default).mode = .owned then
      LeanExe.Runtime.headerStore base 8 [.constI64 0] else []) ++
    releaseWhere (shape.context r Γ) (shape.slots r base (slots.getD x.index default).mode slots)
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
    (nodes r).code (pool := pool) targetModes h stateBase resultBase
      (shape.slots r base (slots.getD x.index default).mode slots) (base + shape.bindCount r)
      (exitLabel + labels + depth r) (nextLabel + labels + depth r)
  have hBranch : RunsTailBranch m host (nc r) (labels + depth r) Q store s := by
    intro Q' hb ht
    let nodeCode := releaseWhere (shape.context r Γ) boundSlots
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
      (nodes r).code (pool := pool) targetModes h stateBase resultBase boundSlots scratch
        (exitLabel + labels + depth r) (nextLabel + labels + depth r)
    have hRun := (spec_var (S := S) (funs := funs) (flags := flags) (bounds := bounds)
      (fits := fits) (host := host) (pv := pv) hm x env slots paid L1).released (Q := Q')
      (rest := storeCode h base [.i64] ++
        ((treeLoadFields base (base + 1) (base + 1 + shape.words r) shape.fieldStart
          (shape.fields r) ++
          (if rootMode = .owned then headerStore base 8 [.constI64 0] else [])) ++ nodeCode))
      hm hh hpv (hVars.mono (by dsimp only [scratch]; omega)) hAt hSafe hCap
      (by dsimp only [scratch]; omega) hRootRoom rfl hEntry
      (hRootBudget.imp (fun st hq => ht st hq)) (fun heap1 store1 s1 ws afterRoot hTop => by
        obtain ⟨p, rfl, root⟩ := afterRoot.rep
        have lower := afterRoot.lower hVars (by dsimp only [scratch]; omega) hL1
        have aRoot : After env slots L0 L1 base heap store s (.tree shape) rootMode
            (.node r words children) heap1 store1 s1 [.i64 p] := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using lower
        have hRoot : rootMode.node heap1 store1 p (Tree.node r words children).toNode := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using root
        have hTopRoot : heap1.top.toNat ≤ heap.top.toNat +
            dyingPot store s env slots paid L0 L1 + rootCost := by
          simpa only [Expr.fits, Expr.allocs, Expr.denote, hValue, rootCost] using hTop rfl
        have hh1 := aRoot.frame.positions.trans hh
        change wp m (storeCode h base [.i64] ++ _) _ store1
          { s1 with values := [.i64 p].reverse ++ s.values } host
        refine wp_storeCode (Q := Q') [.i64 p] h base [.i64] s1 s.values rfl hh1
          (by rw [aRoot.frame.params]; omega)
          (by simp only [List.length_cons, List.length_nil]; rw [hh1]; omega)
          (fun s2 f2 hold2 _ => ?_)
        have hPtr : ({ s2 with values := s.values } : Locals).get base = some (.i64 p) := by
          have hg := hold2 0 (by simp)
          simpa [slotIndex] using hg
        have f2' : Frame base s1 { s2 with values := s.values } := f2.trans Frame.ofValues
        have hOpen := wp_openTree (m := m) (host := host) (Q := Q') (rest := nodeCode)
          aRoot.step.at_ hRoot hPtr (by rw [f2.params, aRoot.frame.params]; omega)
          (by rw [Locals.positions_values, f2.positions, hh1]; exact hFieldRoom)
          (fun s3 f3 hStack fields detached subset => by
            have openFrame : Frame base s1 s3 := f2'.trans (f3.mono (Nat.le_succ base))
            obtain ⟨step3, frame3, outer3, fields3, fresh3⟩ := aRoot.openTreeFields
              openFrame (Nat.le_refl base) detached fields subset
            have hh3 := frame3.positions.trans hh
            have hp3 := frame3.params.trans hpv
            have hBodyBudget : TrapOK (!((nodes r).fits funs fits boundEnv) || !decide
                (heap1.Within (treeDetachStore rootMode store1 p) m
                  (dyingPot (treeDetachStore rootMode store1 p) s3 boundEnv boundSlots boundPaid
                    LB (fun _ => false) + bodyCost))) Q := by
              have hb := hBudget.allocPart id (fun _ hw => treeCase_bodyWithin (shape := shape)
                (r := r) (mode := rootMode) (fieldBase := base) (words := words)
                (children := children) (live := fun _ => false)
                hVars step3 frame3 hL1 nofun hTopRoot hw)
              simpa only [boundEnv, boundSlots, boundPaid, LB, shift_false] using hb
            have hFields : ∀ i, (nodes r).uses i = true → LB i = true := by
              intro i hi
              by_cases hlt : i < shape.bindCount r
              · simp [LB, hlt]
              · simp only [LB, shift, hlt, decide_false, Bool.false_or, ↓reduceIte, L1]
                simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt hlt)] using hi
            have safeFields : pool.Safe boundEnv boundSlots LB heap1
                (treeDetachStore rootMode store1 p) s3 := by
              have hCount : (shape.context r []).length = shape.bindCount r := by
                simp only [TreeShape.context_length, List.length_nil, Nat.add_zero]
              have hLength : (shape.slots r base rootMode []).length =
                  (shape.context r []).length := by
                rw [shape.slots_length r, hCount]
              have hs := hSafe.bindPrefixStep hVars step3 frame3 outer3 hLength fresh3 hL1
                (bodyLive := LB) (fun i hi => by simpa [hCount, LB, shift] using hi)
              rw [← shape.slots_append r base rootMode slots] at hs
              exact hs.ofHEq (shape.context_append r Γ)
                (Env.treeFields_append shape r words children env)
            dsimp only [nodeCode]
            have hRelease : (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) =
                (fun i => LB i && !(nodes r).uses i) := by
              funext i
              by_cases hlt : i < shape.bindCount r
              · simp [LB, hlt]
              · simp [LB, shift, hlt, L1, Nat.sub_add_cancel (Nat.le_of_not_gt hlt)]
            rw [hRelease]
            refine nodeSpec.released hm hh3 hp3 fields3 detached.at_ safeFields
              (by rw [step3.cap m]; exact hCap)
              (by rw [frame3.params]; exact hLow) hState (by omega)
              hBodyRoom hPlaceN hPaidN hFields (hBodyBudget.imp (fun st hq => ht st hq))
              (fun heap4 store4 s4 body hTop4 => by
                let bodySlots := body.withSlots (shape.slots_append r base rootMode slots)
                have hCount : (shape.context r []).length = shape.bindCount r := by
                  simp only [shape.context_length r, List.length_nil, Nat.add_zero]
                have hLength : (shape.slots r base rootMode []).length =
                    (shape.context r []).length := by
                  rw [shape.slots_length r, hCount]
                let body' := bodySlots.ofHEq (shape.context_append r Γ).symm
                  (Env.treeFields_append shape r words children env).symm
                let all := TailAfter.bindPrefixStep hVars step3 frame3 outer3 (Frame.refl _ _)
                  hLength body' (by omega)
                  (fun keep hr t y hm w hold length b hb =>
                    hr b (fresh3 t y hm w hold length b hb))
                  (fun i hi => by simpa [hCount, LB, shift] using hi) hL1
                have meaning : (nodes r).denote funs boundEnv = outer.denote funs env := by
                  simp only [outer, TailBody.denote, hValue, boundEnv]
                have done := hNext heap4 store4 s4 (all.congr meaning) (fun hf => by
                  have hfN : (nodes r).fits funs fits boundEnv = true := by
                    simpa only [outer, TailBody.fits, hValue, boundEnv] using hf
                  have ht4 := hTop4 hfN
                  have hd := dyingPot_treeEntry (treeDetachStore rootMode store1 p) s3 env
                    shape r words children base rootMode slots paid L1 (fun _ => false)
                  rw [dyingPot_step hVars step3 frame3 hL1 L1 (fun _ => false)
                    (fun _ hi => hi)] at hd
                  simp only [shift_false] at hd
                  have hs := dyingPot_split (store := store) (s := s) (env := env)
                    (slots := slots) (paid := paid) L0 L1 (fun _ => false) hL1 nofun
                  simp only [boundPaid] at ht4
                  rw [hd] at ht4
                  change heap4.top.toNat + tailPot targetModes nextPaid resultPaid store4
                    body.words (outer.denote funs env) ≤ _
                  rw [← meaning]
                  change heap4.top.toNat + tailPot targetModes nextPaid resultPaid store4
                    body.words ((nodes r).denote funs boundEnv) ≤ heap.top.toNat +
                      dyingPot store s env slots paid L0 (fun _ => false) +
                      outer.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode)
                        paid env
                  rw [hAlloc]
                  dsimp only [bodyCost, boundEnv, boundSlots, boundPaid]
                  omega)
                have labelEq : ((nodes r).denote funs boundEnv).elim
                    (fun _ => nextLabel + labels + depth r)
                    (fun _ => exitLabel + labels + depth r) =
                    (outer.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel) +
                      (labels + depth r) := by
                  rw [meaning]
                  cases outer.denote funs env <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
                    omega
                rw [labelEq, hStack]
                exact hb _ _ _ done))
        simpa only [List.append_assoc] using hOpen)
    dsimp only [nc]
    simp_rw [← nat_beq_decide]
    simp only [List.append_assoc]
    change wp m (releaseWhere Γ slots (fun i => L0 i && !(L1 i || i == x.index)) ++ _) Q' store s
      host
    convert hRun using 1
    simp only [nodeCode, TailBody.code, Expr.code, Expr.uses, L0, L1, outer, scratch, boundSlots,
      rootMode, storeCode, slotIndex, List.append_assoc, List.cons_append,
      List.nil_append, nat_beq_decide]
  simp only [TailBody.code, TailBody.codeWith, TailBody.usesFast_eq]
  by_cases hn : shape.hasNull = true
  · rw [dite_eq_left hn]
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, hGet, wp_eqzI64_cons,
      hNonzero, ↓reduceIte, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    simp (config := { decide := true }) only [↓reduceIte]
    refine RunsTailBranch.dispatchCode r nc (d := labels) hGet hTagRoom hTagRead hBranch _
      (fun k st s' hq => ?_) (fun _ hq => hq)
    rw [show k + labels = k + 1 by simp [labels, hn]]
    exact hq
  · rw [dite_eq_right hn]
    refine RunsTailBranch.dispatchCode r nc (d := labels) hGet hTagRoom hTagRead hBranch Q
      (fun k st s' hq => ?_) (fun _ hq => hq)
    rw [show k + labels = k by simp [labels, hn]]
    exact hq

#print axioms tail_treeCase_node

end Verified
