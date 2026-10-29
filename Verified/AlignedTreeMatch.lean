import Verified.AlignedTreeBuild
import Verified.AlignedAccess
import Verified.TreeMatchFrame
import Verified.TreeDispatch
import Verified.AlignedCopy
import Verified.OwnedExpr

/-!
The opening of a tree record under the flag.  The tag test and the loads of the fields read
slots of the record, and the detach writes a word of its header, so each statement takes the
alignment of the record's pointer, which `Ty.AlignedVal.treePtr` gives from the tree's.
`HoldsA.openTree` states the invariant of the context of a branch: a field's regions lie in
the tree's, and the detach keeps the regions of the variables that stay live.
`CodeSpecX.released` and `CodeSpecX.releaseCoerced` release the variables that die before an
expression and then evaluate it.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `wp_ofWordCode` under the flag. -/
theorem wpX_ofWordCode {strict : Bool} {m : Module} {st : Store Unit} {env' : HostEnv Unit}
    {s : Locals} {vs : List Value} {rest : Program} {Q : Assertion Unit} (ty : ValueType)
    (w : UInt64) :
    wpX strict m (ofWordCode ty ++ rest) Q st { s with values := .i64 w :: vs } env' ↔
      wpX strict m rest Q st { s with values := typedValue ty w :: vs } env' := by
  cases strict
  · exact wp_ofWordCode ty w
  · exact wpA_ofWordCode ty w

/-- The pointer of an aligned tree record, in either mode, is a multiple of 8. -/
theorem Ty.AlignedVal.treePtr {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (h : Ty.AlignedVal mode store (.tree shape) [.i64 p]
      (Tree.node r words arrays buffers children)) :
    p.toNat % 8 = 0 := by
  cases mode
  · exact (h (p.toNat, 8 * (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)).length)
      (by simp only [Ty.regions, Ty.reads]; exact List.mem_cons_self ..)).1
  · exact h.treeRecord (by have := hNode.1.1.base; omega)

section

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool} {base : Nat}
  {heap : Heap} {store : Store Unit} {s : Locals}

theorem HoldsA.append {ps qs : List Ty} {values : Env ps} {tail : Env qs}
    {first rest : List Slot} (hLength : first.length = ps.length)
    (hFirst : HoldsA values first live heap store s)
    (hTail : HoldsA tail rest (fun i => live (ps.length + i)) heap store s) :
    HoldsA (values.append tail) (first ++ rest) live heap store s := by
  refine ⟨hFirst.1, fun t x hx => ?_⟩
  rcases x.append_cases with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · have hx' : live x.index = true := by simpa using hx
    simpa only [Var.prefix_index, slots_append_prefix x first rest hLength,
      Env.get_append_prefix] using hFirst.2 t x hx'
  · have hx' : live (ps.length + x.index) = true := by simpa using hx
    simpa only [slots_append_suffix x first rest hLength, Env.get_append_suffix] using
      hTail.2 t x hx'

theorem HoldsA.popPrefix {ps qs : List Ty} {values : Env ps} {tail : Env qs}
    {first rest : List Slot} (hLength : first.length = ps.length)
    (h : HoldsA (values.append tail) (first ++ rest) live heap store s) :
    HoldsA tail rest (fun i => live (ps.length + i)) heap store s := by
  refine ⟨h.1, fun t x hx => ?_⟩
  have hx' : live (x.suffix ps).index = true := by simpa using hx
  simpa only [slots_append_suffix x first rest hLength, Env.get_append_suffix] using
    h.2 t (x.suffix ps) hx'

theorem HoldsA.ofHEq {Δ : List Ty} {second : Env Δ} (hΓ : Γ = Δ) (h : HEq env second)
    (hA : HoldsA env slots live heap store s) : HoldsA second slots live heap store s := by
  cases hΓ
  cases h
  exact hA

end

/-- The invariant of the context of a record's branch, as `After.openTreeFields` gives its
`Holds`: the fields' regions lie in the tree's, and the detach keeps the regions of the
variables that stay live. -/
theorem HoldsA.openTree {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 : Nat → Bool} {base fieldBase : Nat} {heap0 heap : Heap}
    {store0 store : Store Unit} {s0 s s' : Locals} {shape : TreeShape} {r : Fin shape.records}
    {mode : Mode} {p : UInt64} {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (a : After env slots L0 L1 base heap0 store0 s0 (.tree shape) mode
      (.node r words arrays buffers children)
      heap store s [.i64 p])
    (hA : HoldsA env slots L1 heap store s)
    (hTree : Ty.AlignedVal mode store (.tree shape) [.i64 p]
      (.node r words arrays buffers children))
    (hFrame : Frame base s s')
    (hStep : Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
      heap (treeDetachStore mode store p) [])
    (hSubset : ∀ (t : Ty) (x : Var (shape.context r []) t) (ws : List Value),
      LocalsHold s' ((shape.slots r fieldBase mode []).getD x.index default).loc t.types ws →
      ws.length = t.width →
      ∀ b ∈ t.regions ((shape.slots r fieldBase mode []).getD x.index default).mode
        (treeDetachStore mode store p) ws
          ((Env.treeFields shape r words arrays buffers children .nil).get x),
        b ∈ (Ty.tree shape).regions mode store [.i64 p] (.node r words arrays buffers children)) :
    HoldsA (Env.treeFields shape r words arrays buffers children env)
      (shape.slots r fieldBase mode slots)
      (fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i)
      heap (treeDetachStore mode store p) s' := by
  have hParent (hm : mode = .owned) :
      block store p ∈ mode.fresh store (.tree shape) [.i64 p]
        (.node r words arrays buffers children) := by
    subst hm
    exact List.mem_cons_self
  have hKeep : ∀ (u : Ty) (y : Var Γ u), L1 y.index = true → ∀ wy,
      LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y),
        mode = .owned → regionsDisjoint c (block store p) := by
    intro u y hy wy hold length c hc hm
    exact regionsDisjoint_symm (a.apart u y hy (.inl hm) wy hold length
      (block store p) (by simpa only [Ty.regions, hm, Mode.fresh] using hParent hm) c hc)
  have hOuter := HoldsA.agree (a.holds.step hStep hKeep)
    (HoldsA.step a.holds hA hStep hA.1 hKeep) hFrame
  have hMode : ∀ i, ((shape.slots r fieldBase mode []).getD i default).mode = .owned →
      mode = .owned := by
    intro i hi
    cases mode
    · rw [shape.slots_borrowed r] at hi; exact nomatch hi
    · rfl
  let LB := fun i => decide (i < shape.bindCount r) || shift (shape.bindCount r) L1 i
  have hLength : (shape.slots r fieldBase mode []).length = (shape.context r []).length := by
    simp only [shape.slots_length r, shape.context_length r, List.length_nil, Nat.add_zero]
  have hTail : HoldsA env slots (fun i => LB ((shape.context r []).length + i))
      heap (treeDetachStore mode store p) s' := by
    apply hOuter.live_mono
    intro i hi
    simpa [LB, shape.context_length r, shift] using hi
  have hPrefix : HoldsA (Env.treeFields shape r words arrays buffers children .nil)
      (shape.slots r fieldBase mode []) LB heap (treeDetachStore mode store p) s' := by
    refine ⟨hA.1, fun t x _ ws hold length b hb => ?_⟩
    have hb' := hSubset t x ws hold length b hb
    exact ⟨(hTree b hb').1, fun hm => (hTree b hb').2 (hMode x.index hm)⟩
  have hCombined := HoldsA.append hLength hPrefix hTail
  rw [← shape.slots_append r] at hCombined
  exact hCombined.ofHEq (shape.context_append r Γ)
    (Env.treeFields_append shape r words arrays buffers children env)

/-- `wp_recordLoadCode` under the flag. -/
theorem wpX_recordLoadCode {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {ptr : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hpAl : strict = true → p.toNat % 8 = 0) :
    ∀ (i : Nat) (dsts : List Nat) (tys : List ValueType) (s : Locals),
      s.get ptr = some (.i64 p) → ptr < s.positions →
      (∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr) →
      p.toNat + 8 * (i + dsts.length) < 4294967296 →
      p.toNat + 8 * (i + dsts.length) ≤ store.mem.pages * 65536 →
      wpX strict m rest Q store (recordLoadLocals store p s.positions i dsts tys s) host →
      wpX strict m (recordLoadCode s.positions ptr i dsts tys ++ rest) Q store s host
  | _, [], _, _, _, _, _, _, _, hNext => hNext
  | i, dst :: dsts, tys, s, hPtr, hPtrLow, hDsts, hAddress, hMemory, hNext => by
    obtain ⟨hLow, hHigh, hNe⟩ := hDsts dst List.mem_cons_self
    let ty := tys.headD .i64
    let s1 := setLocal s (slotIndex s.positions dst ty)
      (typedValue ty (store.mem.read64 (slotAddress p i)))
    obtain ⟨hSlotLow, hSlotHigh⟩ := slotIndex_bounds (s := s) ty hLow hHigh
    have hFrame : Frame dst s s1 := Frame.setSlot ty hSlotLow (Nat.le_refl _) hHigh
    have hSlotNe : slotIndex s.positions dst ty ≠ ptr := by
      cases hty : ty <;> simp only [slotIndex] <;> omega
    have hPtr1 : s1.get ptr = some (.i64 p) := by
      rw [Locals.get_setLocal_ne hSlotLow hSlotNe.symm]
      exact hPtr
    have hPositions : s1.positions = s.positions := Locals.positions_setLocal _ _ _
    have hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)]
      simp only [List.length_cons] at hMemory
      omega
    change (p + UInt64.ofNat (8 * i)).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 at hRoom
    have hRest := wpX_recordLoadCode (strict := strict) (m := m) (host := host) (store := store) (ptr := ptr) (p := p)
      (rest := rest) (Q := Q) hpAl (i + 1) dsts tys.tail s1 hPtr1 (by rw [hPositions]; exact hPtrLow)
      (fun next hn => by
        rw [hFrame.params, hFrame.positions]
        exact hDsts next (List.mem_cons_of_mem _ hn))
      (by simp only [List.length_cons] at hAddress; omega)
      (by simp only [List.length_cons] at hMemory; omega)
      (by rw [hPositions]; exact hNext)
    rw [hPositions] at hRest
    have hSet := wpX_localSet_local (strict := strict) (m := m) (env := host)
      (rest := recordLoadCode s.positions ptr (i + 1) dsts tys.tail ++ rest)
      hSlotLow hSlotHigh hRest
    have hOf := (wpX_ofWordCode (strict := strict) (m := m) (st := store) (env' := host) (s := s) (vs := s.values)
      (rest := [.localSet (slotIndex s.positions dst ty)] ++
        (recordLoadCode s.positions ptr (i + 1) dsts tys.tail ++ rest)) (Q := Q) ty
      (store.mem.read64 (slotAddress p i))).mpr (by simpa only [List.cons_append,
        List.nil_append] using hSet)
    simp only [recordLoadCode, List.append_assoc, List.cons_append, List.nil_append,
      wpX_localGet_cons, hPtr, wpX_constI64_cons, wpX_addI64_cons,
      wpX_wrapI64_cons, wrap_toUInt32, wpX_load64_cons, UInt32.toNat_zero,
      Nat.add_zero, UInt32.add_zero, ite_eq_right (Nat.not_lt.mpr hRoom)]
    refine ⟨fun hs => slotAddress_mod8 (hpAl hs) i, ?_⟩
    simpa only [recordLoadCode, List.append_assoc, List.cons_append, List.nil_append,
      wpX_localGet_cons, Locals.get_values, hPtr, wpX_constI64_cons, wpX_addI64_cons,
      wpX_wrapI64_cons, wrap_toUInt32, slotAddress, wpX_load64_cons, UInt32.toNat_zero,
      Nat.add_zero, UInt32.add_zero, ite_eq_right (Nat.not_lt.mpr hRoom)] using hOf

theorem wp_recordLoadCode {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {ptr : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit} :
    ∀ (i : Nat) (dsts : List Nat) (tys : List ValueType) (s : Locals),
      s.get ptr = some (.i64 p) → ptr < s.positions →
      (∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr) →
      p.toNat + 8 * (i + dsts.length) < 4294967296 →
      p.toNat + 8 * (i + dsts.length) ≤ store.mem.pages * 65536 →
      wp m rest Q store (recordLoadLocals store p s.positions i dsts tys s) host →
      wp m (recordLoadCode s.positions ptr i dsts tys ++ rest) Q store s host :=
  wpX_recordLoadCode (strict := false) nofun

/-- `code` runs, at the store `store` and the locals `s`, as the branch of a test followed by
`rest` under `Q`: for every continuation `rest'` and assertion `Q'` that accept what `rest` and
`Q` accept after a fall-through with the stack of `s`, and that accept the traps that `Q`
accepts, `code ++ rest'` meets `Q'`.  A chain of tests nests the branch in blocks, and this form
holds at every depth. -/
def RunsBranchX (strict : Bool) (m : Module) (host : HostEnv Unit) (code rest : Program) (Q : Assertion Unit)
    (store : Store Unit) (s : Locals) : Prop :=
  ∀ (rest' : Program) (Q' : Assertion Unit),
    (∀ st s', s'.values = s.values → wpX strict m rest Q st s' host → wpX strict m rest' Q' st s' host) →
    (∀ st, Q (.Trap st "unreachable") → Q' (.Trap st "unreachable")) →
    wpX strict m (code ++ rest') Q' store s host

theorem RunsBranchX.mono {strict : Bool} {m : Module} {host : HostEnv Unit} {code rest rest2 : Program}
    {Q Q2 : Assertion Unit} {store : Store Unit} {s : Locals}
    (h : RunsBranchX strict m host code rest Q store s)
    (hf : ∀ st s', s'.values = s.values → wpX strict m rest Q st s' host → wpX strict m rest2 Q2 st s' host)
    (ht : ∀ st, Q (.Trap st "unreachable") → Q2 (.Trap st "unreachable")) :
    RunsBranchX strict m host code rest2 Q2 store s :=
  fun rest' Q' hf' ht' => h rest' Q' (fun st s' hv hw => hf' st s' hv (hf st s' hv hw))
    (fun st hq => ht' st (ht st hq))

theorem RunsBranch.mono {m : Module} {host : HostEnv Unit} {code rest rest2 : Program}
    {Q Q2 : Assertion Unit} {store : Store Unit} {s : Locals}
    (h : RunsBranch m host code rest Q store s)
    (hf : ∀ st s', s'.values = s.values → wp m rest Q st s' host → wp m rest2 Q2 st s' host)
    (ht : ∀ st, Q (.Trap st "unreachable") → Q2 (.Trap st "unreachable")) :
    RunsBranch m host code rest2 Q2 store s :=
  RunsBranchX.mono (strict := false) h hf ht
#print axioms RunsBranch.mono

/-- `wp_dispatchChain` under the flag. -/
theorem wpX_dispatchChain {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {tag : Program} {t : UInt64} (hTag : PushesWordX strict m host tag store s t) :
    ∀ (pairs : List (UInt64 × Program)) (rest : Program) (Q : Assertion Unit),
      RunsBranchX strict m host (chainPick t [] pairs) rest Q store s →
      wpX strict m (dispatchChain tag pairs ++ rest) Q store s host
  | [], rest, Q, h => by
    simpa only [chainPick, dispatchChain, List.nil_append] using
      h rest Q (fun _ _ _ hw => hw) (fun _ hq => hq)
  | [(_, code)], rest, Q, h => h rest Q (fun _ _ _ hw => hw) (fun _ hq => hq)
  | (i, code) :: p :: more, rest, Q, h => by
    rw [dispatchChain, List.append_assoc]
    apply hTag
    simp only [List.cons_append, List.nil_append, wpX_constI64_cons, wpX_eqI64_cons]
    apply wpX_iff_cons rfl
    rw [chainPick] at h
    by_cases hi : t = i
    · rw [ite_eq_left hi] at h
      rw [ite_eq_left hi, ite_eq_left (by decide : (1 : UInt32) ≠ 0), ← List.append_nil code]
      refine h [] _ (fun st s' hv hw => ?_) (fun _ hq => hq)
      rw [wpX_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      rw [← hv]
      exact hw
    · rw [ite_eq_right hi] at h
      rw [ite_eq_right hi, ite_eq_right (by decide : ¬(0 : UInt32) ≠ 0),
        ← List.append_nil (dispatchChain tag (p :: more))]
      refine wpX_dispatchChain hTag (p :: more) [] _ ?_
      intro rest' Q' hf ht
      refine h rest' Q' (fun st s' hv hw => hf st s' hv ?_) (fun st hq => ht st hq)
      rw [wpX_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      rw [← hv]
      exact hw

theorem wp_dispatchChain {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {tag : Program} {t : UInt64} (hTag : PushesWord m host tag store s t) :
    ∀ (pairs : List (UInt64 × Program)) (rest : Program) (Q : Assertion Unit),
      RunsBranch m host (chainPick t [] pairs) rest Q store s →
      wp m (dispatchChain tag pairs ++ rest) Q store s host :=
  wpX_dispatchChain (strict := false) hTag
#print axioms wp_dispatchChain

/-- The tag tests of a shape run the branch of record constructor `r` when the tag code pushes
`r`'s tag. -/
theorem wpX_dispatchCode {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {shape : TreeShape} (r : Fin shape.records) {ptr : Nat} {p : UInt64}
    {rest : Program} {Q : Assertion Unit} (branch : Fin shape.records → Program)
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAl : strict = true → p.toNat % 8 = 0)
    (hTag : shape.tagged = true →
      store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hBranch : RunsBranchX strict m host (branch r) rest Q store s) :
    wpX strict m (shape.dispatchCode ptr branch ++ rest) Q store s host := by
  apply wpX_dispatchChain (PushesWordX.tag hPtr hRoom hAl)
  rw [shape.chainPick_tag r branch [] _ hTag]
  exact hBranch

/-- The tag tests of a shape run the branch of record constructor `r` when the tag code pushes
`r`'s tag. -/
theorem wp_dispatchCode {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {shape : TreeShape} (r : Fin shape.records) {ptr : Nat} {p : UInt64}
    {rest : Program} {Q : Assertion Unit} (branch : Fin shape.records → Program)
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hTag : shape.tagged = true →
      store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hBranch : RunsBranch m host (branch r) rest Q store s) :
    wp m (shape.dispatchCode ptr branch ++ rest) Q store s host :=
  wpX_dispatchCode (strict := false) r branch hPtr hRoom nofun hTag hBranch
#print axioms wp_dispatchCode

/-- `wp_loadTree` under the flag. -/
theorem wpX_loadTree {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode}
    {p : UInt64} {h ptr fieldBase : Nat}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h)
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0)
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (hLow : s.params.length ≤ fieldBase) (hPtrLow : ptr < fieldBase)
    (hRoom : fieldBase + shape.words r + shape.children r + shape.arrays r +
      2 * shape.buffers r ≤ s.positions)
    (hNext : ∀ s', Frame fieldBase s s' → s'.values = s.values →
      s'.get ptr = some (.i64 p) →
      (∀ i, s'.get (slotIndex s.positions (fieldBase + i.val) (shape.elem r i).slotType) =
        some (typedValue (shape.elem r i).slotType (shape.slotWords r words i))) →
      (∀ i, s'.get (fieldBase + shape.words r + i.val) = some (.i64
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val))))) →
      (∀ i, s'.get (fieldBase + shape.words r + shape.children r + i.val) = some (.i64
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i))))) →
      (∀ i, s'.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val) =
          some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
            (shape.fields r).length + heapBufferSlot (shape.kinds r) i)))) ∧
        s'.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val + 1) =
          some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
            (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1))))) →
      wpX strict m rest Q store s' host) :
    wpX strict m (treeLoadFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
      shape.fieldStart (shape.fields r) ++
      treeLoadHeaps ptr (shape.kinds r) (fieldBase + shape.words r + shape.children r)
        (fieldBase + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++ rest) Q store s host := by
  subst hh
  have hStart := shape.fieldStart_tagSlots r
  have hTypes : ∀ i : Fin (shape.words r),
      (shape.wordTypes r).getD i.val .i64 = (shape.elem r i).slotType := by
    intro i
    simp [TreeShape.wordTypes, i.isLt]
  have hCount := shape.words_children r
  let arraysBase := fieldBase + shape.words r + shape.children r
  let buffersBase := fieldBase + shape.words r + shape.children r + shape.arrays r
  let fieldDsts := treeFieldLocs (shape.fields r) fieldBase (fieldBase + shape.words r)
  let heapDsts := heapLocs (shape.kinds r) arraysBase buffersBase
  let dsts := fieldDsts ++ heapDsts
  let tys := treeFieldTypes (shape.fields r) (shape.wordTypes r)
  have hFieldRange : ∀ dst ∈ fieldDsts, fieldBase ≤ dst ∧ dst < arraysBase := by
    intro dst hd
    rw [treeFieldLocs_mem] at hd
    change (fieldBase ≤ dst ∧ dst < fieldBase + shape.words r) ∨
      (fieldBase + shape.words r ≤ dst ∧
        dst < fieldBase + shape.words r + shape.children r) at hd
    dsimp only [arraysBase]
    omega
  have hHeapRange : ∀ dst ∈ heapDsts, arraysBase ≤ dst ∧ dst < s.positions := by
    intro dst hd
    have := heapLocs_mem (shape.kinds r) arraysBase buffersBase dst hd
    change (arraysBase ≤ dst ∧ dst < arraysBase + shape.arrays r) ∨
      (buffersBase ≤ dst ∧ dst < buffersBase + 2 * shape.buffers r) at this
    dsimp only [arraysBase, buffersBase] at this ⊢
    omega
  have hRange : ∀ dst ∈ dsts, fieldBase ≤ dst ∧ dst < s.positions := by
    intro dst hd
    rcases List.mem_append.mp hd with hd | hd
    · have := hFieldRange dst hd
      dsimp only [arraysBase] at this
      omega
    · have := hHeapRange dst hd
      dsimp only [arraysBase] at this
      omega
  have hDsts : ∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr := by
    intro dst hd
    have := hRange dst hd
    omega
  have hUnique : dsts.Nodup := by
    refine List.nodup_append.mpr ⟨treeFieldLocs_nodup (shape.fields r) _ _ (Or.inl (by rfl)),
      heapLocs_nodup (shape.kinds r) _ _ (Or.inl (by dsimp only [arraysBase, buffersBase]; rfl)),
      fun a ha b hb hab => ?_⟩
    have h1 := hFieldRange a ha
    have h2 := hHeapRange b hb
    omega
  have hFrame := recordLoadLocals_frame store p fieldBase shape.fieldStart dsts tys s hLow
    hRange
  have hPtr' : (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get ptr =
      some (.i64 p) := by
    rw [recordLoadLocals_get_other store p s.positions shape.fieldStart dsts tys s ptr
      (fun dst hd ty => by
        obtain ⟨hl, hh', -⟩ := hDsts dst hd
        have hb := hRange dst hd
        refine ⟨(slotIndex_bounds (s := s) ty hl hh').1, ?_⟩
        cases ty <;> simp only [slotIndex] <;> omega)]
    exact hPtr
  have hGet := recordLoadLocals_get store p shape.fieldStart dsts tys s hUnique
    (fun dst hd => ⟨(hDsts dst hd).1, (hDsts dst hd).2.1⟩)
  have hFieldLen : fieldDsts.length = (shape.fields r).length := treeFieldLocs_length _ _ _
  have hWords : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
      (slotIndex s.positions (fieldBase + i.val) (shape.elem r i).slotType) =
      some (typedValue (shape.elem r i).slotType (shape.slotWords r words i)) := by
    intro i
    have hPos := (fieldPosition false (shape.fields r) i).isLt
    have hj := hGet (fieldPosition false (shape.fields r) i).val
      (by rw [List.length_append, hFieldLen]; omega)
    rw [List.getElem_append_left (by rw [hFieldLen]; exact hPos)] at hj
    dsimp only [fieldDsts, tys] at hj
    rw [treeFieldLocs_word_get (shape.fields r) fieldBase (fieldBase + shape.words r) i,
      treeFieldTypes_word_get (shape.fields r) (shape.wordTypes r) i, hTypes i,
      treeNode_word_read hNode i] at hj
    exact hj
  have hChildren : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
      (fieldBase + shape.words r + i.val) = some (.i64
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))) := by
    intro i
    have hPos := (fieldPosition true (shape.fields r) i).isLt
    have hj := hGet (fieldPosition true (shape.fields r) i).val
      (by rw [List.length_append, hFieldLen]; omega)
    rw [List.getElem_append_left (by rw [hFieldLen]; exact hPos)] at hj
    dsimp only [fieldDsts, tys] at hj
    rw [treeFieldLocs_child_get (shape.fields r) fieldBase (fieldBase + shape.words r) i,
      treeFieldTypes_child_get (shape.fields r) (shape.wordTypes r) i] at hj
    simpa only [slotIndex, typedValue] using hj
  have hArrays : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
      (fieldBase + shape.words r + shape.children r + i.val) = some (.i64
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i)))) := by
    intro i
    have hLt := heapArraySlot_lt (shape.kinds r) (fun _ => #[]) (fun _ => .empty) i
    rw [heapSlots_length] at hLt
    have hHeapLen := heapLocs_length (shape.kinds r) arraysBase buffersBase
    have hj := hGet (fieldDsts.length + heapArraySlot (shape.kinds r) i)
      (by rw [List.length_append, hHeapLen]; omega)
    rw [List.getElem_append_right (by omega)] at hj
    simp only [Nat.add_sub_cancel_left] at hj
    rw [heapLocs_array_get (shape.kinds r) arraysBase buffersBase i (by rw [hHeapLen]; omega)]
      at hj
    have hTy : tys.getD (fieldDsts.length + heapArraySlot (shape.kinds r) i) .i64 = .i64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        dsimp only [tys]
        rw [treeFieldTypes_length, ← hFieldLen]
        omega)]
      rfl
    rw [hTy, hFieldLen, ← Nat.add_assoc] at hj
    simpa only [slotIndex, typedValue, arraysBase] using hj
  have hBuffers : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
        (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val) =
        some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i)))) ∧
      (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
        (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val + 1) =
        some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)))) := by
    intro i
    have hLt := heapBufferSlot_lt (shape.kinds r) (fun _ => #[]) (fun _ => .empty) i
    rw [heapSlots_length] at hLt
    have hHeapLen := heapLocs_length (shape.kinds r) arraysBase buffersBase
    obtain ⟨hLoc1, hLoc2⟩ := heapLocs_buffer_get (shape.kinds r) arraysBase buffersBase i
      (by rw [hHeapLen]; omega)
    have hj1 := hGet (fieldDsts.length + heapBufferSlot (shape.kinds r) i)
      (by rw [List.length_append, hHeapLen]; omega)
    have hj2 := hGet (fieldDsts.length + (heapBufferSlot (shape.kinds r) i + 1))
      (by rw [List.length_append, hHeapLen]; omega)
    rw [List.getElem_append_right (by omega)] at hj1 hj2
    simp only [Nat.add_sub_cancel_left] at hj1 hj2
    rw [hLoc1] at hj1
    rw [hLoc2] at hj2
    have hTy (k : Nat) : tys.getD (fieldDsts.length + k) .i64 = .i64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        dsimp only [tys]
        rw [treeFieldTypes_length, ← hFieldLen]
        omega)]
      rfl
    rw [hTy, hFieldLen] at hj1 hj2
    refine ⟨?_, ?_⟩
    · simpa only [slotIndex, typedValue, buffersBase, Nat.add_assoc] using hj1
    · simpa only [slotIndex, typedValue, buffersBase, Nat.add_assoc] using hj2
  have hSlots := hNode.borrow.1
  change RecordSlots heap p (shape.recordSlots r (shape.slotWords r words)
    (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)) at hSlots
  have hLength := shape.recordSlots_length r (shape.slotWords r words)
    (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)
  have hDstsLen : dsts.length = (shape.fields r).length + shape.heapWidth r := by
    dsimp only [dsts]
    rw [List.length_append, hFieldLen, heapLocs_length]
    rfl
  have hWidth : shape.width r = shape.fieldStart + dsts.length := by
    rw [hDstsLen, hStart]
    simp only [TreeShape.width]
    omega
  have hAddress : p.toNat + 8 * (shape.fieldStart + dsts.length) < 4294967296 := by
    have := hSlots.address
    rw [hLength, hWidth] at this
    exact this
  have hMemory : p.toNat + 8 * (shape.fieldStart + dsts.length) ≤ store.mem.pages * 65536 := by
    have hBelow := hSlots.below
    rw [hLength, hWidth] at hBelow
    exact hBelow.trans hAt.top
  have hPtrPos : ptr < s.positions := by omega
  rw [treeLoadFields_eq, treeLoadHeaps_eq s.positions,
    show shape.fieldStart + (shape.fields r).length = shape.fieldStart + fieldDsts.length by
      rw [hFieldLen],
    ← recordLoadCode_append _ _ _ _ _ _ [] (by
      rw [treeFieldTypes_length, treeFieldLocs_length]), List.append_nil]
  exact wpX_recordLoadCode hpAl shape.fieldStart dsts tys s hPtr hPtrPos hDsts hAddress hMemory
    (hNext _ hFrame (recordLoadLocals_values store p s.positions shape.fieldStart dsts tys s)
      hPtr' hWords hChildren hArrays hBuffers)

theorem wp_loadTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode}
    {p : UInt64} {h ptr fieldBase : Nat}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h)
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (hLow : s.params.length ≤ fieldBase) (hPtrLow : ptr < fieldBase)
    (hRoom : fieldBase + shape.words r + shape.children r + shape.arrays r +
      2 * shape.buffers r ≤ s.positions)
    (hNext : ∀ s', Frame fieldBase s s' → s'.values = s.values →
      s'.get ptr = some (.i64 p) →
      (∀ i, s'.get (slotIndex s.positions (fieldBase + i.val) (shape.elem r i).slotType) =
        some (typedValue (shape.elem r i).slotType (shape.slotWords r words i))) →
      (∀ i, s'.get (fieldBase + shape.words r + i.val) = some (.i64
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val))))) →
      (∀ i, s'.get (fieldBase + shape.words r + shape.children r + i.val) = some (.i64
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i))))) →
      (∀ i, s'.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val) =
          some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
            (shape.fields r).length + heapBufferSlot (shape.kinds r) i)))) ∧
        s'.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val + 1) =
          some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
            (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1))))) →
      wp m rest Q store s' host) :
    wp m (treeLoadFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
      shape.fieldStart (shape.fields r) ++
      treeLoadHeaps ptr (shape.kinds r) (fieldBase + shape.words r + shape.children r)
        (fieldBase + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++ rest) Q store s host :=
  wpX_loadTree (strict := false) hh hAt hPtr nofun hNode hLow hPtrLow hRoom hNext

/-- `wp_detachTree` under the flag. -/
theorem wpX_detachTree {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {ptr : Nat} {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hNode : mode.node heap store p
      (Tree.node r words arrays buffers children).toNode)
    (hPtr : s.get ptr = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0)
    (hNext : wpX strict m rest Q (treeDetachStore mode store p) s host) :
    wpX strict m ((if mode = .owned then headerStore ptr 8 [.constI64 0] else []) ++ rest)
      Q store s host := by
  cases mode
  · exact hNext
  · have hBase := hNode.1.1.base
    have hBelow := hNode.1.1.below
    have hAddress := hNode.1.1.address
    have hRoom : (p - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [headerAddress_toNat (by change 8 ≤ p.toNat; omega) (by omega)]
      change p.toNat - 8 + 8 ≤ store.mem.pages * 65536
      have := hAt.top
      omega
    exact wpX_headerStoreWord hPtr hRoom (fun hs => ⟨hpAl hs, rfl⟩) hNext

theorem wp_detachTree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {ptr : Nat} {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hNode : mode.node heap store p
      (Tree.node r words arrays buffers children).toNode)
    (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (treeDetachStore mode store p) s host) :
    wp m ((if mode = .owned then headerStore ptr 8 [.constI64 0] else []) ++ rest)
      Q store s host :=
  wpX_detachTree (strict := false) hAt hNode hPtr nofun hNext

/-- `wp_openTree` under the flag. -/
theorem wpX_openTree {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {h base : Nat}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {rest : Program} {Q : Assertion Unit} (hh : s.positions = h) (hAt : heap.At store)
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (hPtr : s.get base = some (.i64 p))
    (hpAl : strict = true → p.toNat % 8 = 0) (hLow : s.params.length ≤ base + 1)
    (hRoom : base + shape.bindWidth r ≤ s.positions)
    (hNext : ∀ s', Frame (base + 1) s s' → s'.values = s.values →
      Holds (Env.treeFields shape r words arrays buffers children .nil)
        (shape.slots r base mode [])
        (fun _ => true) (base + shape.bindWidth r) heap (treeDetachStore mode store p) s' →
      Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
        heap (treeDetachStore mode store p) [] →
      (∀ (t : Ty) (x : Var (shape.context r []) t) (ws : List Value),
        LocalsHold s' ((shape.slots r base mode []).getD x.index default).loc t.types ws →
        ws.length = t.width →
        ∀ b ∈ t.regions ((shape.slots r base mode []).getD x.index default).mode
          (treeDetachStore mode store p) ws
            ((Env.treeFields shape r words arrays buffers children .nil).get x),
          b ∈ (Ty.tree shape).regions mode store [.i64 p]
            (.node r words arrays buffers children)) →
      wpX strict m rest Q (treeDetachStore mode store p) s' host) :
    wpX strict m (treeLoadFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
      shape.fieldStart (shape.fields r) ++
      treeLoadHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
        (base + 1 + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) Q store s host := by
  obtain ⟨hAt', hHeader, hStep, hChildren, hArrays, hRecordBuffers, hApart, hReads, hRegions⟩ :=
    treeNode_detach hAt hNode
  have hRun := wpX_loadTree (strict := strict) (m := m) (host := host) (Q := Q)
    (rest := (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) hh hAt
    hPtr hpAl hNode hLow (by omega) (by simp only [TreeShape.bindWidth, TreeShape.bindCount] at hRoom; omega)
    (fun s' hFrame hStack hPtr' hWordLocals hChildLocals hArrayLocals hBufferLocals => by
    have hold := LocalsHold.treeFields hPtr' (by rw [hFrame.positions]; exact hWordLocals)
      hChildLocals hArrayLocals hBufferLocals
    have hRep := treeFields_rep (words := words) (buffers := buffers) hHeader hChildren hArrays
      (fun i => (hRecordBuffers i).rep)
    have hPrefix := Holds.treePrefix (buffers := buffers) hHeader hChildren hArrays
      (fun i => (hRecordBuffers i).rep) hApart hold
    have hPointers : ∀ i, store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)) =
        (treeDetachStore mode store p).mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)) :=
      fun i => (hReads ⟨_, shape.fieldSlot_lt r true i⟩).symm
    have hArrayPtrs : ∀ i, store.mem.read64
        (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i)) =
        (treeDetachStore mode store p).mem.read64
          (slotAddress p (shape.fieldStart + (shape.fields r).length +
            heapArraySlot (shape.kinds r) i)) :=
      fun i => (hReads ⟨_, shape.heapArraySlot_lt_width r i⟩).symm
    refine wpX_detachTree hAt hNode hPtr' hpAl
      (hNext s' hFrame hStack hPrefix hStep ?_)
    intro t x ws hLocal hLength b hr
    rw [← hRegions]
    have hRootReads : ∀ i, store.mem.read64 (slotAddress p (shape.fieldStart +
        (shape.fields r).length + heapBufferSlot (shape.kinds r) i)) =
        (treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i)) :=
      fun i => (hReads ⟨_, by have := shape.heapBufferSlot_lt_width r i; omega⟩).symm
    have hLengthReads : ∀ i, store.mem.read64 (slotAddress p (shape.fieldStart +
        (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)) =
        (treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)) :=
      fun i => (hReads ⟨_, shape.heapBufferSlot_lt_width r i⟩).symm
    have hDetachBuffers : ∀ i, RecordBuffer heap (treeDetachStore mode store p)
        ((treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i)))
        ((treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)))
        (buffers i) := fun i => by
      rw [← hRootReads, ← hLengthReads]
      exact hRecordBuffers i
    exact treeFields_variable_regions hDetachBuffers hPointers hArrayPtrs hRootReads
      hLengthReads hRep hold t x ws hLocal hLength b hr)
  simpa only [List.append_assoc] using hRun

theorem wp_openTree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {h base : Nat}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {rest : Program} {Q : Assertion Unit} (hh : s.positions = h) (hAt : heap.At store)
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (hPtr : s.get base = some (.i64 p)) (hLow : s.params.length ≤ base + 1)
    (hRoom : base + shape.bindWidth r ≤ s.positions)
    (hNext : ∀ s', Frame (base + 1) s s' → s'.values = s.values →
      Holds (Env.treeFields shape r words arrays buffers children .nil)
        (shape.slots r base mode [])
        (fun _ => true) (base + shape.bindWidth r) heap (treeDetachStore mode store p) s' →
      Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
        heap (treeDetachStore mode store p) [] →
      (∀ (t : Ty) (x : Var (shape.context r []) t) (ws : List Value),
        LocalsHold s' ((shape.slots r base mode []).getD x.index default).loc t.types ws →
        ws.length = t.width →
        ∀ b ∈ t.regions ((shape.slots r base mode []).getD x.index default).mode
          (treeDetachStore mode store p) ws
            ((Env.treeFields shape r words arrays buffers children .nil).get x),
          b ∈ (Ty.tree shape).regions mode store [.i64 p]
            (.node r words arrays buffers children)) →
      wp m rest Q (treeDetachStore mode store p) s' host) :
    wp m (treeLoadFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
      shape.fieldStart (shape.fields r) ++
      treeLoadHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
        (base + 1 + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) Q store s host :=
  wpX_openTree (strict := false) hh hAt hNode hPtr nofun hLow hRoom hNext

/-- `CodeSpec.releaseCoerced` under the flag. -/
theorem CodeSpecX.releaseCoerced {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {L0 live : Nat → Bool} {target : Mode}
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m) (hCopy : CopyCodeX strict m host)
    (spec : CodeSpecX strict (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (hTarget : e.mode (slots.map Slot.mode) = .owned → target = .owned)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv) (hVars : Holds env slots L0 base heap store s)
    (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots L0 heap store s)
    (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + max e.width (copyWidth t) ≤ h)
    (hPlace : e.placeArgs = true)
    (hEntry : ∀ i, (live i || e.uses i) = true → L0 i = true)
    {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots L0 live base heap store s t target (e.denote funs env)
        heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal target store' t ws (e.denote funs env)) →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wpX strict m (releaseWhere Γ slots (fun i => L0 i && !(live i || e.uses i)) ++
      (e.code (pool := pool) h slots base live ++
        (coerceCode h t (e.mode (slots.map Slot.mode)) target base ++ rest))) Q store s host := by
  refine wpX_releaseWhere hm hRA hVars hAt hAl (fun i hi => by
      simp only [Bool.and_eq_true] at hi; exact hi.1)
    (fun heap1 store1 released hTop1 hAl1 => ?_)
  have hLiveEq : (fun i => L0 i && !(L0 i && !(live i || e.uses i))) =
      (fun i => live i || e.uses i) := by
    funext i
    have hi := hEntry i
    cases h0 : L0 i <;> cases hl : live i <;> cases he : e.uses i <;> simp_all
  rw [hLiveEq] at released hAl1
  have hPot := dyingPot_evolves (paid := paid) hVars released hEntry
    (fun i => live i || e.uses i) live (fun _ hi => hi)
  have hPotLe : dyingPot store s env slots paid (fun i => live i || e.uses i) live ≤
      dyingPot store s env slots paid L0 live := dyingPot_mono hEntry (fun _ hi => hi)
  refine CodeSpecX.coerced hCopy spec hTarget hh hpv released.holds released.step.at_ hAl1
    (hSafe.evolves hVars released hEntry)
    (by rw [released.step.cap m]; exact hCap) hBase hRoom hPlace
    (hTrap.allocPart id (fun _ hw => hw.shift (heap1 := heap1) (store1 := store1) (c1 := 0)
      (by have ht := congrArg UInt64.toNat hTop1; omega)
      (by rw [hPot]; omega) (released.step.cap m)))
    (fun heap2 store2 s2 ws a hAl2 hTop2 => ?_)
  refine hNext heap2 store2 s2 ws
    (After.prepend hVars released a hEntry (fun i hi => by simp [hi])) hAl2 (fun hf => ?_)
  have h2 := hTop2 hf
  have h1 := congrArg UInt64.toNat hTop1
  rw [hPot] at h2
  omega

theorem CodeSpec.releaseCoerced {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {L0 live : Nat → Bool} {target : Mode}
    (hm : Runtime m) (spec : CodeSpec (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (hTarget : e.mode (slots.map Slot.mode) = .owned → target = .owned)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv) (hVars : Holds env slots L0 base heap store s)
    (hAt : heap.At store) (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + max e.width (copyWidth t) ≤ h)
    (hPlace : e.placeArgs = true)
    (hEntry : ∀ i, (live i || e.uses i) = true → L0 i = true)
    {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots L0 live base heap store s t target (e.denote funs env)
        heap' store' s' ws →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env +
        coerceCost t (e.mode (slots.map Slot.mode)) target (e.denote funs env)) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (releaseWhere Γ slots (fun i => L0 i && !(live i || e.uses i)) ++
      (e.code (pool := pool) h slots base live ++
        (coerceCode h t (e.mode (slots.map Slot.mode)) target base ++ rest))) Q store s host :=
  CodeSpecX.releaseCoerced (strict := false) hm nofun (copyCodeX hm) (CodeSpecX.false_iff.mpr spec)
    hTarget hh hpv hVars hAt nofun hSafe hCap hBase hRoom hPlace hEntry hTrap
    (fun heap' store' s' ws a1 _ a3 => hNext heap' store' s' ws a1 a3)

/-- `CodeSpec.released` under the flag. -/
theorem CodeSpecX.released {strict : Bool} {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {L0 live : Nat → Bool}
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (spec : CodeSpecX strict (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv) (hVars : Holds env slots L0 base heap store s)
    (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots L0 heap store s)
    (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + e.width ≤ h)
    (hPlace : e.placeArgs = true)
    (hEntry : ∀ i, (live i || e.uses i) = true → L0 i = true)
    {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots L0 live base heap store s t (e.mode (slots.map Slot.mode))
        (e.denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal (e.mode (slots.map Slot.mode)) store' t ws (e.denote funs env)) →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wpX strict m (releaseWhere Γ slots (fun i => L0 i && !(live i || e.uses i)) ++
      (e.code (pool := pool) h slots base live ++ rest)) Q store s host := by
  refine wpX_releaseWhere hm hRA hVars hAt hAl (fun i hi => by
      simp only [Bool.and_eq_true] at hi; exact hi.1)
    (fun heap1 store1 released hTop1 hAl1 => ?_)
  have hLiveEq : (fun i => L0 i && !(L0 i && !(live i || e.uses i))) =
      (fun i => live i || e.uses i) := by
    funext i
    have hi := hEntry i
    cases h0 : L0 i <;> cases hl : live i <;> cases he : e.uses i <;> simp_all
  rw [hLiveEq] at released hAl1
  have hPot := dyingPot_evolves (paid := paid) hVars released hEntry
    (fun i => live i || e.uses i) live (fun _ hi => hi)
  have hPotLe : dyingPot store s env slots paid (fun i => live i || e.uses i) live ≤
      dyingPot store s env slots paid L0 live := dyingPot_mono hEntry (fun _ hi => hi)
  have hBudget : TrapOK (!(e.fits funs fits env) ||
      (true && !decide (heap.Within store m (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env)))) Q := by
    simpa only [Bool.true_and] using hTrap
  refine spec h base heap1 store1 s hh hpv released.holds released.step.at_ hAl1
    (hSafe.evolves hVars released hEntry)
    (by rw [released.step.cap m]; exact hCap) hBase hRoom hPlace _ _
    (hBudget.part id (fun _ => rfl) (fun _ hw => hw.shift
      (heap1 := heap1) (store1 := store1) (c1 := 0)
      (by have ht := congrArg UInt64.toNat hTop1; omega)
      (by rw [hPot]; omega) (released.step.cap m)))
    (fun heap2 store2 s2 ws a hAl2 hTop2 => ?_)
  refine hNext heap2 store2 s2 ws
    (After.prepend hVars released a hEntry (fun i hi => by simp [hi])) hAl2 (fun hf => ?_)
  have h2 := hTop2 hf
  have h1 := congrArg UInt64.toNat hTop1
  rw [hPot] at h2
  omega

theorem CodeSpec.released {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} {e : Expr S Γ t} {env : Env Γ}
    {slots : List Slot} {paid : List Bool} {L0 live : Nat → Bool}
    (hm : Runtime m) (spec : CodeSpec (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    {h base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv) (hVars : Holds env slots L0 base heap store s)
    (hAt : heap.At store) (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ base) (hRoom : base + e.width ≤ h)
    (hPlace : e.placeArgs = true)
    (hEntry : ∀ i, (live i || e.uses i) = true → L0 i = true)
    {rest : Program} {Q : Assertion Unit}
    (hTrap : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots L0 live base heap store s t (e.mode (slots.map Slot.mode))
        (e.denote funs env) heap' store' s' ws →
      (e.fits funs fits env = true → heap'.top.toNat ≤ heap.top.toNat +
        dyingPot store s env slots paid L0 live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (releaseWhere Γ slots (fun i => L0 i && !(live i || e.uses i)) ++
      (e.code (pool := pool) h slots base live ++ rest)) Q store s host :=
  CodeSpecX.released (strict := false) hm nofun (CodeSpecX.false_iff.mpr spec) hh hpv hVars hAt
    nofun hSafe hCap hBase hRoom hPlace hEntry hTrap
    (fun heap' store' s' ws a1 _ a3 => hNext heap' store' s' ws a1 a3)

end Verified
