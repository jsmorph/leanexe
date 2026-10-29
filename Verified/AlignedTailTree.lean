import Verified.AlignedTail
import Verified.AlignedTreeMatch
import Verified.TailTreeCase

/-!
The match on a tree in a tail body under the flag.  `RunsTailBranchX` is `RunsTailBranch` with
`wpX strict`, and its dispatch lemmas load the tag at the tree's pointer, whose alignment they take
as a premise.  The empty case is its original with `TailCodeSpecX.released`.  The node case takes
the pointer's alignment from the invariant of the matched variable (`Ty.AlignedVal.treePtr`),
opens the record by `wpX_openTree`, and runs the branch in the context whose invariant
`HoldsA.openTree` gives.  Each theorem is its original with these changes.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `code` runs as a branch nested in `d` blocks for the assertion `Q` of the code around them:
for every assertion `Q'` that accepts, for a break out of `k + d` blocks, what `Q` accepts for a
break out of `k`, and that accepts the traps that `Q` accepts, `code` meets `Q'`. -/
def RunsTailBranchX (strict : Bool) (m : Module) (host : HostEnv Unit) (code : Program) (d : Nat)
    (Q : Assertion Unit) (store : Store Unit) (s : Locals) : Prop :=
  ∀ Q' : Assertion Unit,
    (∀ k st s', Q (.Break k st s') → Q' (.Break (k + d) st s')) →
    (∀ st, Q (.Trap st "unreachable") → Q' (.Trap st "unreachable")) →
    wpX strict m code Q' store s host

theorem RunsTailBranchX.dispatchChain {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {tag : Program} {t : UInt64} (hTag : PushesWordX strict m host tag store s t) :
    ∀ (pairs : List (UInt64 × Program)) (d : Nat) (Q : Assertion Unit),
      RunsTailBranchX strict m host (chainPick t [] pairs) (d + chainDepth t pairs) Q store s →
      RunsTailBranchX strict m host (Verified.dispatchChain tag pairs) d Q store s
  | [], d, Q, h => by simpa [chainPick, chainDepth, Verified.dispatchChain] using h
  | [(_, code)], d, Q, h => by simpa [chainPick, chainDepth, Verified.dispatchChain] using h
  | (i, code) :: p :: more, d, Q, h => by
    intro Q' hb ht
    rw [Verified.dispatchChain]
    refine hTag s.values _ Q' ?_
    simp only [List.cons_append, List.nil_append, wpX_constI64_cons, wpX_eqI64_cons]
    apply wpX_iff_cons rfl
    rw [chainPick, chainDepth] at h
    by_cases hi : t = i
    · rw [ite_eq_left hi, ite_eq_left hi] at h
      rw [ite_eq_left hi, ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
      refine h _ (fun k st s' hq => ?_) (fun st hq => ht st hq)
      rw [show k + (d + 1) = k + d + 1 by omega]
      exact hb k st s' hq
    · rw [ite_eq_right hi, ite_eq_right hi] at h
      rw [ite_eq_right hi, ite_eq_right (by decide : ¬(0 : UInt32) ≠ 0)]
      have hRest := RunsTailBranchX.dispatchChain hTag (p :: more) (d + 1) Q
        (by rw [show d + 1 + chainDepth t (p :: more) = d + (1 + chainDepth t (p :: more)) by
          omega]; exact h)
      refine hRest _ (fun k st s' hq => ?_) (fun st hq => ht st hq)
      rw [show k + (d + 1) = k + d + 1 by omega]
      exact hb k st s' hq

/-- The tag tests of a shape, as a branch nested in `d` blocks, run the branch of record
constructor `r`, which they nest in `chainDepth` further blocks. -/
theorem RunsTailBranchX.dispatchCode {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} (r : Fin shape.records) {ptr : Nat} {p : UInt64}
    {d : Nat} {Q : Assertion Unit} (branch : Fin shape.records → Program)
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0)
    (hTag : shape.tagged = true →
      store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hBranch : RunsTailBranchX strict m host (branch r)
      (d + if r.val + 1 < shape.records then r.val + 1 else r.val) Q store s) :
    RunsTailBranchX strict m host (shape.dispatchCode ptr branch) d Q store s := by
  apply RunsTailBranchX.dispatchChain (PushesWordX.tag hPtr hRoom hAl)
  rw [shape.chainPick_tag r branch [] _ hTag, shape.chainDepth_tag r branch _ hTag]
  exact hBranch

theorem tail_treeCase_emptyX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : shape.hasNull = true → TailBody S params result Γ)
    (nodes : (r : Fin shape.records) → TailBody S params result (shape.context r Γ))
    (hn : shape.hasNull = true)
    (emptySpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (empty hn))
    (env : Env Γ) (hNil : env.get x = .nil hn) :
    TailCodeSpecAtX strict (pool := pool) m funs flags bounds fits host pv targetModes (.treeCase x empty nodes) env := by
  intro slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let outer := TailBody.treeCase x empty nodes
  let L0 := outer.uses
  have hx : L0 x.index = true := by simp [L0, outer, TailBody.uses]
  obtain ⟨_, ws, hold, rep⟩ := hVars.get x hx
  obtain ⟨p, rfl, root⟩ := rep
  have hp : p = 0 := by
    have hr := root.borrow
    rw [hNil] at hr
    exact hr
  subst p
  have hGet : s.get (slots.getD x.index default).loc = some (.i64 0) := by
    have hg := hold 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hEntry : ∀ i, (empty hn).uses i = true → L0 i = true := by
    intro i hi
    simp [L0, outer, TailBody.uses, dite_eq_left hn, hi]
  have hRoomE : base + (empty hn).width targetModes ≤ h := by
    simp only [TailBody.width, dite_eq_left hn] at hRoom
    have := Nat.le_max_left ((empty hn).width targetModes)
      (argsMax fun r => shape.bindWidth r + max treeCopyScratch ((nodes r).width targetModes))
    omega
  have hPlaceE : (empty hn).placeArgs targetModes (slots.map Slot.mode) = true := by
    simp only [TailBody.placeArgs, dite_eq_left hn, Bool.and_eq_true] at hPlace
    exact hPlace.1
  have hPaidE : resultPaid = true →
      (empty hn).paidResult flags (slots.map Slot.mode) paid = true := by
    intro hp
    have hf := hPaid hp
    simp only [TailBody.paidResult, Bool.false_eq_true] at hf
  have hBudget : TrapOK (!((empty hn).fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 (fun _ => false) +
        (empty hn).allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid
          env))) Q := by
    simpa only [tailTrapFlag, TailBody.aborts, Bool.true_or, Bool.true_and,
      TailBody.allocs, TailBody.fits, hNil, L0, outer] using hTrap
  have hValue : (empty hn).denote funs env = outer.denote funs env := by
    simp only [outer, TailBody.denote, hNil]
  simp only [TailBody.code, TailBody.codeWith, TailBody.usesFast_eq]
  rw [dite_eq_left hn]
  simp only [List.append_assoc, List.cons_append, List.nil_append, wpX_localGet_cons, hGet,
    wpX_eqzI64_cons]
  refine wpX_iff_cons rfl ?_
  simp (config := { decide := true }) only [↓reduceIte]
  simp_rw [← nat_beq_decide]
  change wpX strict m (releaseWhere Γ slots (fun i => L0 i &&
      !(if h : shape.hasNull = true then (empty h).uses i else false)) ++
    (empty hn).code (pool := pool) targetModes h stateBase resultBase slots base (exitLabel + 1)
      (nextLabel + 1)) _ store s host
  simp only [dite_eq_left hn]
  refine emptySpec.released hm hRA hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoomE hPlaceE
    hPaidE hEntry (hBudget.imp (fun _ hi => hi)) (fun heap1 store1 s1 after hAl1 hTop => ?_)
  have done := hNext heap1 store1 s1 (after.congr hValue)
    (fun hs => ⟨(hAl1 hs).1, by
      show TailAligned targetModes store1 after.words _
      rw [← hValue]; exact (hAl1 hs).2⟩) (fun hf => by
    have hfE : (empty hn).fits funs fits env = true := by
      simpa only [outer, TailBody.fits, hNil] using hf
    have ht := hTop hfE
    change heap1.top.toNat +
      tailPot targetModes nextPaid resultPaid store1 after.words (outer.denote funs env) ≤ _
    rw [← hValue]
    simpa only [outer, TailBody.allocs, hNil, L0] using ht)
  have labelEq : ((empty hn).denote funs env).elim (fun _ => nextLabel + 1)
      (fun _ => exitLabel + 1) =
      (outer.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel) + 1 := by
    rw [hValue]
    cases outer.denote funs env <;> rfl
  rw [labelEq]
  exact done

theorem tail_treeCase_nodeX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : shape.hasNull = true → TailBody S params result Γ)
    (nodes : (r : Fin shape.records) → TailBody S params result (shape.context r Γ))
    (r : Fin shape.records)
    (nodeSpec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (nodes r))
    (env : Env Γ) (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape)
    (hValue : env.get x = .node r words arrays buffers children) :
    TailCodeSpecAtX strict (pool := pool) m funs flags bounds fits host pv targetModes (.treeCase x empty nodes) env := by
  intro slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  let outer := TailBody.treeCase x empty nodes
  let L0 := outer.uses
  let L1 := fun i => (nodes r).uses (i + shape.bindCount r)
  let rootMode := (slots.getD x.index default).mode
  let scratch := base + shape.bindWidth r
  let boundSlots := shape.slots r base rootMode slots
  let boundEnv := Env.treeFields shape r words arrays buffers children env
  let boundPaid := List.replicate (shape.bindCount r) false ++ paid
  let LB := fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i
  let rootCost := x.cost (slots.map Slot.mode) L1 (.node r words arrays buffers children)
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
      (.record (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
        (fun i => (children i).toNode))) := by
    have hb := node0.borrow
    rw [hValue] at hb
    exact hb
  have hNonzero : p0 ≠ 0 := hBorrow0.1.nonzero
  have hp0Al : strict = true → p0.toNat % 8 = 0 := by
    intro hs
    have hA := (hAl hs).2 _ x hx [.i64 p0] hold0 rfl
    have hN := node0
    rw [hValue] at hA hN
    exact hA.treePtr hN
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
    have hg := hold0 0 (by simp)
    simpa [Ty.types, slotIndex] using hg
  have hScratch : scratch + max treeCopyScratch ((nodes r).width targetModes) ≤ h := by
    have hr : shape.bindWidth r + max treeCopyScratch ((nodes r).width targetModes) ≤
        argsMax (fun r => shape.bindWidth r + max treeCopyScratch ((nodes r).width targetModes)) :=
      le_argsMax (fun r => shape.bindWidth r + max treeCopyScratch
        ((nodes r).width targetModes)) r
    have := Nat.le_max_right
      (if h : shape.hasNull = true then (empty h).width targetModes else 0)
      (argsMax fun r => shape.bindWidth r + max treeCopyScratch ((nodes r).width targetModes))
    simp only [TailBody.width] at hRoom
    dsimp only [scratch]
    omega
  have hRootRoom : scratch + (Expr.var (S := S) x).width ≤ h := by
    have := Nat.le_max_left treeCopyScratch ((nodes r).width targetModes)
    simpa only [Expr.width, Ty.copyScratch] using (show scratch + treeCopyScratch ≤ h by omega)
  have hBodyRoom : scratch + (nodes r).width targetModes ≤ h := by
    have := Nat.le_max_right treeCopyScratch ((nodes r).width targetModes)
    omega
  have hFieldRoom : base + shape.bindWidth r ≤ h := by
    dsimp only [scratch] at hScratch
    omega
  have hBindPos : 1 ≤ shape.bindWidth r := by
    simp only [TreeShape.bindWidth, TreeShape.bindCount]
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
    x.code h slots (base + shape.bindWidth r) (fun i => (nodes r).uses (i + shape.bindCount r)) ++
    [.localSet base] ++
    treeLoadFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
      shape.fieldStart (shape.fields r) ++
    treeLoadHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
      (base + 1 + shape.words r + shape.children r + shape.arrays r)
      (shape.fieldStart + (shape.fields r).length) ++
    (if (slots.getD x.index default).mode = .owned then
      LeanExe.Runtime.headerStore base 8 [.constI64 0] else []) ++
    releaseWhere (shape.context r Γ) (shape.slots r base (slots.getD x.index default).mode slots)
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
    (nodes r).code (pool := pool) targetModes h stateBase resultBase
      (shape.slots r base (slots.getD x.index default).mode slots) (base + shape.bindWidth r)
      (exitLabel + labels + depth r) (nextLabel + labels + depth r)
  have hBranch : RunsTailBranchX strict m host (nc r) (labels + depth r) Q store s := by
    intro Q' hb ht
    let nodeCode := releaseWhere (shape.context r Γ) boundSlots
      (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) ++
      (nodes r).code (pool := pool) targetModes h stateBase resultBase boundSlots scratch
        (exitLabel + labels + depth r) (nextLabel + labels + depth r)
    have hRun := (specX_var (S := S) (funs := funs) (flags := flags) (bounds := bounds)
      (fits := fits) (host := host) (pv := pv) (strict := strict) hCopy x env slots paid L1).released (Q := Q')
      (rest := storeCode h base [.i64] ++
        ((treeLoadFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
          shape.fieldStart (shape.fields r) ++
          treeLoadHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
            (base + 1 + shape.words r + shape.children r + shape.arrays r)
            (shape.fieldStart + (shape.fields r).length) ++
          (if rootMode = .owned then headerStore base 8 [.constI64 0] else [])) ++ nodeCode))
      hm hRA hh hpv (hVars.mono (by dsimp only [scratch]; omega)) hAt hAl hSafe hCap
      (by dsimp only [scratch]; omega) hRootRoom rfl hEntry
      (hRootBudget.imp (fun st hq => ht st hq)) (fun heap1 store1 s1 ws afterRoot hA1 hTop => by
        obtain ⟨p, rfl, root⟩ := afterRoot.rep
        have lower := afterRoot.lower hVars (by dsimp only [scratch]; omega) hL1
        have aRoot : After env slots L0 L1 base heap store s (.tree shape) rootMode
            (.node r words arrays buffers children) heap1 store1 s1 [.i64 p] := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using lower
        have hRoot : rootMode.node heap1 store1 p
            (Tree.node r words arrays buffers children).toNode := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using root
        have hRootAl : strict = true → HoldsA env slots L1 heap1 store1 s1 ∧
            Ty.AlignedVal rootMode store1 (.tree shape) [.i64 p]
              (.node r words arrays buffers children) := by
          simpa only [Expr.mode, Expr.denote, hValue, Slot.modes_getD, rootMode] using hA1
        have hTopRoot : heap1.top.toNat ≤ heap.top.toNat +
            dyingPot store s env slots paid L0 L1 + rootCost := by
          simpa only [Expr.fits, Expr.allocs, Expr.denote, hValue, rootCost] using hTop rfl
        have hh1 := aRoot.frame.positions.trans hh
        change wpX strict m (storeCode h base [.i64] ++ _) _ store1
          { s1 with values := [.i64 p].reverse ++ s.values } host
        refine wpX_storeCode (Q := Q') [.i64 p] h base [.i64] s1 s.values rfl hh1
          (by rw [aRoot.frame.params]; omega)
          (by simp only [List.length_cons, List.length_nil]; rw [hh1]; omega)
          (fun s2 f2 hold2 _ => ?_)
        have hPtr : ({ s2 with values := s.values } : Locals).get base = some (.i64 p) := by
          have hg := hold2 0 (by simp)
          simpa [slotIndex] using hg
        have f2' : Frame base s1 { s2 with values := s.values } := f2.trans Frame.ofValues
        have hOpen := wpX_openTree (strict := strict) (m := m) (host := host) (Q := Q') (rest := nodeCode)
          (by rw [Locals.positions_values, f2.positions, hh1]) aRoot.step.at_ hRoot hPtr
          (fun hs => (hRootAl hs).2.treePtr hRoot)
          (by rw [f2.params, aRoot.frame.params]; omega)
          (by rw [Locals.positions_values, f2.positions, hh1]; exact hFieldRoom)
          (fun s3 f3 hStack fields detached subset => by
            have openFrame : Frame base s1 s3 := f2'.trans (f3.mono (Nat.le_succ base))
            obtain ⟨step3, frame3, outer3, fields3, fresh3⟩ := aRoot.openTreeFields
              openFrame (Nat.le_refl base) detached fields subset
            have hBodyAl : strict = true → HoldsA boundEnv boundSlots LB heap1
                (treeDetachStore rootMode store1 p) s3 := fun hs =>
              HoldsA.openTree aRoot (hRootAl hs).1 (hRootAl hs).2 openFrame detached subset
            have hh3 := frame3.positions.trans hh
            have hp3 := frame3.params.trans hpv
            have hBodyBudget : TrapOK (!((nodes r).fits funs fits boundEnv) || !decide
                (heap1.Within (treeDetachStore rootMode store1 p) m
                  (dyingPot (treeDetachStore rootMode store1 p) s3 boundEnv boundSlots boundPaid
                    LB (fun _ => false) + bodyCost))) Q := by
              have hb := hBudget.allocPart id (fun _ hw => treeCase_bodyWithin (shape := shape)
                (r := r) (mode := rootMode) (fieldBase := base) (words := words)
                (arrays := arrays) (buffers := buffers)
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
                (Env.treeFields_append shape r words arrays buffers children env)
            dsimp only [nodeCode]
            have hRelease : (fun i => decide (i < shape.bindCount r) && !(nodes r).uses i) =
                (fun i => LB i && !(nodes r).uses i) := by
              funext i
              by_cases hlt : i < shape.bindCount r
              · simp [LB, hlt]
              · simp [LB, shift, hlt, L1, Nat.sub_add_cancel (Nat.le_of_not_gt hlt)]
            rw [hRelease]
            refine nodeSpec.released hm hRA hh3 hp3 fields3 detached.at_ hBodyAl safeFields
              (by rw [step3.cap m]; exact hCap)
              (by rw [frame3.params]; exact hLow) hState (by omega)
              hBodyRoom hPlaceN hPaidN hFields (hBodyBudget.imp (fun st hq => ht st hq))
              (fun heap4 store4 s4 body hA4 hTop4 => by
                let bodySlots := body.withSlots (shape.slots_append r base rootMode slots)
                have hCount : (shape.context r []).length = shape.bindCount r := by
                  simp only [shape.context_length r, List.length_nil, Nat.add_zero]
                have hLength : (shape.slots r base rootMode []).length =
                    (shape.context r []).length := by
                  rw [shape.slots_length r, hCount]
                let body' := bodySlots.ofHEq (shape.context_append r Γ).symm
                  (Env.treeFields_append shape r words arrays buffers children env).symm
                let all := TailAfter.bindPrefixStep hVars step3 frame3 outer3 (Frame.refl _ _)
                  hLength body' (by omega)
                  (fun keep hr t y hm w hold length b hb =>
                    hr b (fresh3 t y hm w hold length b hb))
                  (fun i hi => by simpa [hCount, LB, shift] using hi) hL1
                have meaning : (nodes r).denote funs boundEnv = outer.denote funs env := by
                  simp only [outer, TailBody.denote, hValue, boundEnv]
                have done := hNext heap4 store4 s4 (all.congr meaning)
                  (fun hs => ⟨(hA4 hs).1, by
                    show TailAligned targetModes store4 body.words _
                    rw [← meaning]; exact (hA4 hs).2⟩) (fun hf => by
                  have hfN : (nodes r).fits funs fits boundEnv = true := by
                    simpa only [outer, TailBody.fits, hValue, boundEnv] using hf
                  have ht4 := hTop4 hfN
                  have hd := dyingPot_treeEntry (treeDetachStore rootMode store1 p) s3 env
                    shape r words arrays buffers children base rootMode slots paid L1
                    (fun _ => false)
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
    change wpX strict m (releaseWhere Γ slots (fun i => L0 i && !(L1 i || i == x.index)) ++ _) Q' store s
      host
    convert hRun using 1
    simp only [nodeCode, TailBody.code, Expr.code, Expr.uses, L0, L1, outer, scratch, boundSlots,
      rootMode, storeCode, slotIndex, List.append_assoc, List.cons_append,
      List.nil_append, nat_beq_decide]
  simp only [TailBody.code, TailBody.codeWith, TailBody.usesFast_eq]
  by_cases hn : shape.hasNull = true
  · rw [dite_eq_left hn]
    simp only [List.cons_append, List.nil_append, wpX_localGet_cons, hGet, wpX_eqzI64_cons,
      hNonzero, ↓reduceIte]
    refine wpX_iff_cons rfl ?_
    simp (config := { decide := true }) only [↓reduceIte]
    refine RunsTailBranchX.dispatchCode r nc (d := labels) hGet hTagRoom hp0Al hTagRead hBranch _
      (fun k st s' hq => ?_) (fun _ hq => hq)
    rw [show k + labels = k + 1 by simp [labels, hn]]
    exact hq
  · rw [dite_eq_right hn]
    refine RunsTailBranchX.dispatchCode r nc (d := labels) hGet hTagRoom hp0Al hTagRead hBranch Q
      (fun k st s' hq => ?_) (fun _ hq => hq)
    rw [show k + labels = k by simp [labels, hn]]
    exact hq

theorem tail_treeCase_specX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : shape.hasNull = true → TailBody S params result Γ)
    (nodes : (r : Fin shape.records) → TailBody S params result (shape.context r Γ))
    (emptySpec : ∀ hn, TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (empty hn))
    (nodeSpec : ∀ r, TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (nodes r)) :
    TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (.treeCase x empty nodes) := by
  intro env
  cases hv : env.get x with
  | nil hn => exact tail_treeCase_emptyX hm hRA targetModes x empty nodes hn (emptySpec hn) env hv
  | node r words arrays buffers children =>
    exact tail_treeCase_nodeX hm hRA hCopy targetModes x empty nodes r (nodeSpec r) env words arrays buffers
      children hv

end Verified
