import Verified.TailTreeEmpty
import Verified.TailBindPrefix
import Verified.TailAllocExpand
import Verified.TreeMatchPotential
import Verified.ReleasedExpr

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem tail_treeCase_node {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : TailBody S params result Γ) (node : TailBody S params result (shape.context Γ))
    (nodeSpec : TailCodeSpec m funs flags bounds fits host pv targetModes node)
    (env : Env Γ) (words : Fin shape.words → UInt64)
    (children : Fin shape.children → Tree shape) (hValue : env.get x = .node words children) :
    TailCodeSpecAt m funs flags bounds fits host pv targetModes (.treeCase x empty node) env := by
  intro slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let outer := TailBody.treeCase x empty node
  let L0 := outer.uses
  let L1 := fun i => node.uses (i + shape.bindCount)
  let rootMode := (slots.getD x.index default).mode
  let scratch := base + shape.bindCount
  let boundSlots := shape.slots base rootMode slots
  let boundEnv := Env.treeFields shape words children env
  let boundPaid := List.replicate shape.bindCount false ++ paid
  let LB := fun i => decide (i < shape.bindCount) || shift shape.bindCount L1 i
  let rootCost := x.cost (slots.map Slot.mode) L1 (.node words children)
  let bodyCost := node.allocs funs flags bounds targetModes nextPaid
    (boundSlots.map Slot.mode) boundPaid boundEnv
  have hL1 : ∀ i, L1 i = true → L0 i = true := by
    intro i hi
    simp [L0, L1, outer, TailBody.uses, hi]
  have hEntry : ∀ i, (L1 i || (Expr.var (S := S) x).uses i) = true → L0 i = true := by
    intro i hi
    simp only [L0, L1, outer, TailBody.uses, Expr.uses, Bool.or_eq_true] at hi ⊢
    tauto
  have hx : L0 x.index = true := by simp [L0, outer, TailBody.uses]
  obtain ⟨_, ws0, hold0, rep0⟩ := hVars.get x hx
  obtain ⟨p0, rfl, node0⟩ := rep0
  have hNonzero : p0 ≠ 0 := by
    have hn := node0.borrow
    rw [hValue] at hn
    exact hn.1.nonzero
  have hGet : s.get (slots.getD x.index default).loc = some (.i64 p0) := by
    have hg := hold0 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hScratch : scratch + max treeCopyScratch (node.width targetModes) ≤ h := by
    have := Nat.le_max_right (empty.width targetModes)
      (shape.bindCount + max treeCopyScratch (node.width targetModes))
    simp only [TailBody.width] at hRoom
    dsimp only [scratch]
    omega
  have hRootRoom : scratch + (Expr.var (S := S) x).width ≤ h := by
    have := Nat.le_max_left treeCopyScratch (node.width targetModes)
    simpa only [Expr.width, Ty.copyScratch] using (show scratch + treeCopyScratch ≤ h by omega)
  have hBodyRoom : scratch + node.width targetModes ≤ h := by
    have := Nat.le_max_right treeCopyScratch (node.width targetModes)
    omega
  have hFieldRoom : base + 1 + shape.fields.length ≤ h := by
    have hc := shape.words_children
    dsimp only [scratch] at hScratch
    simp only [TreeShape.bindCount] at hScratch
    omega
  have hPlaceN : node.placeArgs targetModes (boundSlots.map Slot.mode) = true := by
    simp only [TailBody.placeArgs, Bool.and_eq_true] at hPlace
    simpa only [boundSlots, TreeShape.slots_modes_full, rootMode, Slot.modes_getD] using hPlace.2
  have hPaidN : resultPaid = true → node.paidResult flags (boundSlots.map Slot.mode) boundPaid = true := by
    intro hp
    have hf := hPaid hp
    simp only [TailBody.paidResult, Bool.false_eq_true] at hf
  have hModes : boundSlots.map Slot.mode = shape.modes rootMode (slots.map Slot.mode) :=
    shape.slots_modes_full base rootMode slots
  have hAlloc : outer.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env =
      rootCost + bodyCost := by
    simp only [outer, TailBody.allocs, hValue, L1, rootCost, bodyCost, boundEnv, boundPaid,
      hModes, rootMode, modeAt, Slot.modes_getD]
  have hBudget : TrapOK (!(node.fits funs fits boundEnv) || !decide (heap.Within store m
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
  simp only [TailBody.code, TailBody.usesFast_eq, List.append_assoc, List.cons_append,
    List.nil_append, wp_localGet_cons, hGet, wp_eqzI64_cons, hNonzero, ↓reduceIte]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp (config := { decide := true }) only [↓reduceIte]
  let nodeCode := releaseWhere (shape.context Γ) boundSlots
    (fun i => decide (i < shape.bindCount) && !node.uses i) ++
    node.code targetModes h stateBase resultBase boundSlots scratch (exitLabel + 1) (nextLabel + 1)
  let QB : Assertion Unit := fun cont => match cont with
    | .Fallthrough st' s' => wp m [] Q st'
        { s' with values := s'.values.take 0 ++ s.values.drop 0 } host
    | .Break 0 st' s' => wp m [] Q st'
        { s' with values := s'.values.take 0 ++ s.values.drop 0 } host
    | .Break (k + 1) st' s' => Q (.Break k st' s')
    | other => Q other
  simp_rw [← nat_beq_decide]
  have hRun := (spec_var (S := S) (funs := funs) (flags := flags) (bounds := bounds)
    (fits := fits) (host := host) (pv := pv) hm x env slots paid L1).released (Q := QB)
    (rest := storeCode h base [.i64] ++
      ((treeLoadFields base (base + 1) (base + 1 + shape.words) 0 shape.fields ++
        (if rootMode = .owned then headerStore base 8 [.constI64 0] else [])) ++ nodeCode))
    hm hh hpv (hVars.mono (by dsimp only [scratch]; omega)) hAt hCap
    (by dsimp only [scratch]; omega) hRootRoom rfl hEntry
    (hRootBudget.imp (fun _ hi => hi)) (fun heap1 store1 s1 ws afterRoot hTop => by
      obtain ⟨p, rfl, root⟩ := afterRoot.rep
      have lower := afterRoot.lower hVars (by dsimp only [scratch]; omega) hL1
      have aRoot : After env slots L0 L1 base heap store s (.tree shape) rootMode
          (.node words children) heap1 store1 s1 [.i64 p] := by
        simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using lower
      have hRoot : rootMode.node heap1 store1 p (Tree.node words children).toNode := by
        simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using root
      have hTopRoot : heap1.top.toNat ≤ heap.top.toNat +
          dyingPot store s env slots paid L0 L1 + rootCost := by
        simpa only [Expr.fits, Expr.allocs, Expr.denote, hValue, rootCost] using hTop rfl
      have hh1 := aRoot.frame.positions.trans hh
      change wp m (storeCode h base [.i64] ++ _) _ store1
        { s1 with values := [.i64 p].reverse ++ s.values } host
      refine wp_storeCode (Q := QB) [.i64 p] h base [.i64] s1 s.values rfl hh1
        (by rw [aRoot.frame.params]; omega)
        (by simp only [List.length_cons, List.length_nil]; rw [hh1]; omega)
        (fun s2 f2 hold2 _ => ?_)
      have hPtr : ({ s2 with values := s.values } : Locals).get base = some (.i64 p) := by
        have hg := hold2 0 (by simp)
        simpa [slotIndex] using hg
      have f2' : Frame base s1 { s2 with values := s.values } := f2.trans Frame.ofValues
      have hOpen := wp_openTree (m := m) (host := host) (Q := QB) (rest := nodeCode)
        aRoot.step.at_ hRoot hPtr (by rw [f2.params, aRoot.frame.params]; omega)
        (by rw [Locals.positions_values, f2.positions, hh1]; exact hFieldRoom)
        (fun s3 f3 hStack fields detached subset => by
          have openFrame : Frame base s1 s3 := f2'.trans (f3.mono (Nat.le_succ base))
          obtain ⟨step3, frame3, outer3, fields3, fresh3⟩ := aRoot.openTreeFields
            openFrame (Nat.le_refl base) detached fields subset
          have hh3 := frame3.positions.trans hh
          have hp3 := frame3.params.trans hpv
          have hBodyBudget : TrapOK (!(node.fits funs fits boundEnv) || !decide
              (heap1.Within (treeDetachStore rootMode store1 p) m
                (dyingPot (treeDetachStore rootMode store1 p) s3 boundEnv boundSlots boundPaid
                  LB (fun _ => false) + bodyCost))) Q := by
            have hb := hBudget.allocPart id (fun _ hw => treeCase_bodyWithin (shape := shape)
              (mode := rootMode) (fieldBase := base) (words := words) (children := children)
              (live := fun _ => false)
              hVars step3 frame3 hL1 nofun hTopRoot hw)
            simpa only [boundEnv, boundSlots, boundPaid, LB, shift_false] using hb
          have hFields : ∀ i, node.uses i = true → LB i = true := by
            intro i hi
            by_cases hlt : i < shape.bindCount
            · simp [LB, hlt]
            · simp only [LB, shift, hlt, decide_false, Bool.false_or, ↓reduceIte, L1]
              simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt hlt)] using hi
          dsimp only [nodeCode]
          have hRelease : (fun i => decide (i < shape.bindCount) && !node.uses i) =
              (fun i => LB i && !node.uses i) := by
            funext i
            by_cases hlt : i < shape.bindCount
            · simp [LB, hlt]
            · simp [LB, shift, hlt, L1, Nat.sub_add_cancel (Nat.le_of_not_gt hlt)]
          rw [hRelease]
          refine nodeSpec.released hm hh3 hp3 fields3 detached.at_
            (by rw [step3.cap m]; exact hCap)
            (by rw [frame3.params]; exact hLow) hState (by omega)
            hBodyRoom hPlaceN hPaidN hFields (hBodyBudget.imp (fun _ hi => hi))
            (fun heap4 store4 s4 body hTop4 => by
              let bodySlots := body.withSlots (shape.slots_append base rootMode slots)
              have hCount : (shape.context []).length = shape.bindCount := by
                simp only [shape.context_length, List.length_nil, Nat.add_zero]
              have hLength : (shape.slots base rootMode []).length = (shape.context []).length := by
                rw [shape.slots_length, hCount]
              let body' := bodySlots.ofHEq (shape.context_append Γ).symm
                (Env.treeFields_append shape words children env).symm
              let all := TailAfter.bindPrefixStep hVars step3 frame3 outer3 (Frame.refl _ _)
                hLength body' (by omega)
                (fun r hr t y hm w hold length b hb => hr b (fresh3 t y hm w hold length b hb))
                (fun i hi => by simpa [hCount, LB, shift] using hi) hL1
              have meaning : node.denote funs boundEnv = outer.denote funs env := by
                simp only [outer, TailBody.denote, hValue, boundEnv]
              have done := hNext heap4 store4 s4 (all.congr meaning) (fun hf => by
                have hfN : node.fits funs fits boundEnv = true := by
                  simpa only [outer, TailBody.fits, hValue, boundEnv] using hf
                have ht := hTop4 hfN
                have hd := dyingPot_treeEntry (treeDetachStore rootMode store1 p) s3 env
                  shape words children base rootMode slots paid L1 (fun _ => false)
                rw [dyingPot_step hVars step3 frame3 hL1 L1 (fun _ => false) (fun _ hi => hi)] at hd
                simp only [shift_false] at hd
                have hs := dyingPot_split (store := store) (s := s) (env := env) (slots := slots)
                  (paid := paid) L0 L1 (fun _ => false) hL1 nofun
                simp only [boundPaid] at ht
                rw [hd] at ht
                change heap4.top.toNat + tailPot targetModes nextPaid resultPaid store4 body.words
                  (outer.denote funs env) ≤ _
                rw [← meaning]
                change heap4.top.toNat + tailPot targetModes nextPaid resultPaid store4 body.words
                  (node.denote funs boundEnv) ≤ heap.top.toNat +
                    dyingPot store s env slots paid L0 (fun _ => false) +
                    outer.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env
                rw [hAlloc]
                dsimp only [bodyCost, boundEnv, boundSlots, boundPaid]
                omega)
              have labelEq : (node.denote funs boundEnv).elim
                  (fun _ => nextLabel + 1) (fun _ => exitLabel + 1) =
                  (outer.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel) + 1 := by
                rw [meaning]
                cases outer.denote funs env <;> rfl
              rw [labelEq, hStack]
              exact done))
      simpa only [List.append_assoc] using hOpen)
  convert hRun using 1 <;>
    simp only [QB, nodeCode, Expr.code, Expr.uses, TailBody.uses, L1, scratch, boundSlots,
      rootMode, storeCode, slotIndex, List.append_assoc, List.cons_append,
      List.nil_append, nat_beq_decide]
  funext cont
  cases cont <;> try rfl
  rename_i k st ls
  cases k <;> rfl

#print axioms tail_treeCase_node

end Verified
