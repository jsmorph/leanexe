import Verified.AlignedTreeAssemble
import Verified.TreeNodeCorrect

/-!
The construction of a tree under the flag.  The parent record comes from `alloc`, whose block
starts and ends at multiples of 8 under `AllocAligned`, or from a detached header, whose block
the invariant covers.  The tree's blocks are the parent's and its fields', the fields' blocks
are aligned by `FieldsAligned`, and the stores of the assembly keep the regions of every live
variable, so the tree and the live variables are aligned when the construct ends.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `wp_treeParent` under the flag: the record's pointer and capacity are multiples of 8, and
the variables that stay live keep the invariant. -/
theorem wpX_treeParent {strict : Bool} {Γ : List Ty} {env : Env Γ} {slots : List Slot} {shape : TreeShape}
    {r : Fin shape.records} (reuse : Option (Var Γ (.treeHeader shape r))) {live : Nat → Bool}
    {base : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals} {m : Module} {host : HostEnv Unit}
    {rest : Program} {Q : Assertion Unit} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m)
    (hVars : Holds env slots (fun i => live i || optionVarUses reuse i) base heap store s)
    (hAl : strict = true →
      HoldsA env slots (fun i => live i || optionVarUses reuse i) heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base < s.positions)
    (hTrap : TrapOK (!decide (heap.Within store m (treeParentCost shape r reuse slots live))) Q)
    (hNext : ∀ heap' store' s' p,
      Step heap store (Holds.KeepDying env slots (fun i => live i || optionVarUses reuse i)
        live store s) heap' store' [block store' p] →
      Frame base s s' → Holds env slots live base heap' store' s' →
      RecordStorage (shape.width r) heap' store' p → store'.mem.read64 (p - 40).toUInt32 = 1 →
      s'.get base = some (.i64 p) → s'.values = s.values →
      (∀ j, j ≠ base → s'.get j = s.get j) →
      Holds.Apart env slots live store' s' (.treeHeader shape r) .owned [.i64 p] .unit →
      heap'.top.toNat ≤ heap.top.toNat + treeParentCost shape r reuse slots live →
      (strict = true → HoldsA env slots live heap' store' s' ∧ p.toNat % 8 = 0 ∧
        capacityAt store' p % 8 = 0) →
      wpX strict m rest Q store' s' host) :
    wpX strict m (treeParentCode shape r reuse slots base live ++ rest) Q store s host := by
  have hLive : ∀ i, live i = true → (live i || optionVarUses reuse i) = true := by
    intro i hi
    simp only [hi, Bool.true_or]
  have hAllocate (hc : treeParentCost shape r reuse slots live =
      allocCost (8 * shape.width r)) :
      wpX strict m (recordAllocate (shape.width r) base ++ rest) Q store s host := by
    refine wpX_recordAllocate hm hRt r hAt (fun hs => (hAl hs).1) hCap (by simpa only [hc] using hTrap)
      hLow (Locals.lt_total hHigh) fun heap' store' p hStep hRaw hCount hTop hNew => ?_
    have hFrame := Frame.set (v := Value.i64 p) hLow (le_refl base) hHigh
    have hLiveVars := hVars.live_mono hLive
    refine hNext heap' store' (setLocal s base (.i64 p)) p
      (hStep.mono (fun _ _ => trivial) (fun _ hb => hb)) hFrame
      ((hLiveVars.step hStep (fun _ _ _ _ _ _ _ _ => trivial)).agree hFrame)
      hRaw hCount (Locals.get_setLocal_same hLow (Locals.lt_total hHigh)) rfl
      (fun _ hj => Locals.get_setLocal_ne hLow hj) ?_ (by rw [hc]; exact hTop) ?_
    intro t x hx _ wx hold length b hb c hc
    have hb' : b = block store' p := by
      simpa only [Ty.regions, Ty.blocks, List.mem_singleton] using hb
    subst b
    have hold0 := (hLiveVars.hold_agree hFrame hx length).mp hold
    obtain ⟨hRegions, hFresh⟩ := hLiveVars.regions_after hStep hx hold0 length (fun _ _ => trivial)
    rw [hRegions] at hc
    exact regionsDisjoint_symm (hFresh c hc (block store' p) (by simp))
    intro hs
    obtain ⟨hp, hCapacity, hHeapAl⟩ := hNew hs
    exact ⟨HoldsA.agree (hLiveVars.step hStep (fun _ _ _ _ _ _ _ _ => trivial))
      (HoldsA.step hLiveVars ((hAl hs).live_mono hLive) hStep hHeapAl
        (fun _ _ _ _ _ _ _ _ => trivial)) hFrame, hp, hCapacity⟩
  cases reuse with
  | none => exact hAllocate rfl
  | some x =>
    by_cases hReuse : (slots.getD x.index default).mode = .owned ∧ live x.index = false
    · obtain ⟨hOwned, hDead⟩ := hReuse
      have hx : (live x.index || optionVarUses (some x) x.index) = true := by
        simp [optionVarUses]
      obtain ⟨_, ws, hold, hRep⟩ := hVars.get x hx
      rw [hOwned] at hRep
      obtain ⟨p, rfl, hHeader⟩ := hRep
      obtain ⟨payload, hLength, hHead, _⟩ := hHeader
      have hRaw := RecordStorage.ofHeader hHead (by simpa only [List.length_map] using hLength)
      have hAlign : strict = true → p.toNat % 8 = 0 ∧ capacityAt store p % 8 = 0 := by
        intro hs
        have hA := (hAl hs).2 _ x hx [.i64 p] hold rfl
        rw [hOwned] at hA
        obtain ⟨h1, h2⟩ := hA (block store p) (by simp [Ty.regions, Ty.blocks])
        have h2 := h2 rfl
        have hBase := hRaw.base
        simp only [block] at h1 h2
        exact ⟨by omega, by omega⟩
      have hPtr := hold.word
      have hFrame := Frame.set (v := Value.i64 p) hLow (le_refl base) hHigh
      have hStep : Step heap store
          (Holds.KeepDying env slots (fun i => live i || optionVarUses (some x) i) live store s)
          heap store [block store p] := by
        refine ⟨hAt, rfl, fun region hr _ hk => ⟨fun _ _ _ => rfl, hr, ?_⟩⟩
        intro b hb
        simp only [List.mem_singleton] at hb
        subst b
        exact hk (.treeHeader shape r) x hx hDead hOwned [.i64 p] hold rfl (block store p)
          (by simp [Ty.blocks])
      have hApart : Holds.Apart env slots live store (setLocal s base (.i64 p))
          (.treeHeader shape r) .owned [.i64 p] .unit := by
        intro t y hy _ wy hwy length b hb c hc
        have hb' : b = block store p := by
          simpa only [Ty.regions, Ty.blocks, List.mem_singleton] using hb
        subst b
        have hwy0 := ((hVars.live_mono hLive).hold_agree hFrame hy length).mp hwy
        have hNe : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
        exact hVars.2 (.treeHeader shape r) t x y hx (hLive _ hy) hNe hOwned [.i64 p] wy hold rfl
          hwy0 length (block store p) (by simp [Ty.blocks]) c hc
      simp only [treeParentCode, hOwned, hDead, and_self, ↓reduceIte, List.cons_append,
        List.nil_append, wpX_localGet_cons, hPtr]
      refine wpX_localSet_local hLow (Locals.lt_total hHigh) ?_
      exact hNext heap store (setLocal s base (.i64 p)) p hStep hFrame
        ((hVars.live_mono hLive).agree hFrame) hRaw hHead.count
        (Locals.get_setLocal_same hLow (Locals.lt_total hHigh)) rfl
        (fun _ hj => Locals.get_setLocal_ne hLow hj) hApart
        (by simp [treeParentCost, hOwned, hDead])
        (fun hs => ⟨HoldsA.agree (hVars.live_mono hLive) ((hAl hs).live_mono hLive) hFrame,
          hAlign hs⟩)
    · simpa only [treeParentCode, hReuse, ↓reduceIte] using
        hAllocate (by simp only [treeParentCost, hReuse, ↓reduceIte])

/-- `wp_finishTree` under the flag: the tree's blocks are the record's and its fields', so it is
aligned when they are. -/
theorem wpX_finishTree {strict : Bool} {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base fieldBase ptr h : Nat} {shape : TreeShape}
    {r : Fin shape.records}
    {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit} {s s1 s2 : Locals}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {ws : List Value} {p : UInt64} {m : Module} {host : HostEnv Unit}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : FieldsAfter env slots L0 L1 base heap store s
      (shape.fieldEnv r words arrays buffers children) heap1 store1 s1 ws)
    (hStep : Step heap1 store1 (Holds.KeepDying env slots L1 live store1 s1)
      heap2 store2 [block store2 p])
    (hFrame : Frame base s1 s2) (hHolds : Holds env slots live base heap2 store2 s2)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true)
    (hRaw : RecordStorage (shape.width r) heap2 store2 p)
    (hCount : store2.mem.read64 (p - 40).toUInt32 = 1)
    (hPtr : s2.get ptr = some (.i64 p)) (hStack : s2.values = s.values)
    (hh : s2.positions = h)
    (hNormal : FieldsNormal (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) .bytes ++ [])))) ws)
    (hLocals : LocalsHold s2 fieldBase (shape.fieldTypes r) ws)
    (hRootApart : Holds.Apart env slots live store2 s2 (.treeHeader shape r) .owned [.i64 p] .unit)
    (hAl2 : strict = true → HoldsA env slots live heap2 store2 s2 ∧ p.toNat % 8 = 0 ∧
      capacityAt store2 p % 8 = 0)
    (hFieldsAl : strict = true →
      FieldsAligned store1 (shape.fieldEnv r words arrays buffers children) ws)
    (hNext : ∀ store',
      After env slots L0 live base heap store s (.tree shape) .owned
        (.node r words arrays buffers children)
        heap2 store' s2 [.i64 p] →
      (strict = true → HoldsA env slots live heap2 store' s2 ∧
        Ty.AlignedVal .owned store' (.tree shape) [.i64 p] (.node r words arrays buffers children)) →
      wpX strict m rest Q store' { s2 with values := .i64 p :: s.values } host) :
    wpX strict m (shape.tagStoreCode r ptr ++
      treeStoreFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
        shape.fieldStart (shape.fields r) ++
      treeStoreHeaps ptr (shape.kinds r) (fieldBase + shape.words r + shape.children r)
        (fieldBase + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      sealRecordCode (shape.width r) ptr (shape.mask r) ++ (.localGet ptr :: rest))
      Q store2 s2 host := by
  obtain ⟨a2, hBoth, hSame, hFresh⟩ := a.advance h0 hStep hFrame hHolds hL1 hLive
  have hApart : (block store2 p ::
      (shape.fieldEnv r words arrays buffers children).blocks store2 ws).Pairwise
        regionsDisjoint := by
    refine List.pairwise_cons.mpr ⟨?_, a2.pairwise⟩
    intro b hb
    rw [hSame] at hb
    exact regionsDisjoint_symm (hFresh b hb (block store2 p) (by simp))
  have hKeepLive : ∀ (u : Ty) (x : Var Γ u), live x.index = true → ∀ wx,
      LocalsHold s2 (slots.getD x.index default).loc u.types wx → wx.length = u.width →
      ∀ c ∈ u.regions (slots.getD x.index default).mode store2 wx (env.get x),
        regionsDisjoint c (block store2 p) := by
    intro u x hx wx hold length c hc
    exact regionsDisjoint_symm (hRootApart u x hx (Or.inl rfl) wx hold length
      (block store2 p) (by simp [Ty.regions, Ty.blocks]) c hc)
  refine wpX_assembleTree hh hRaw hStep.at_ hPtr (fun hs => (hAl2 hs).2.1) hCount a2.rep hNormal hLocals hApart
    fun store3 hAt3 hRep hBlocks hWrite => ?_
  have hWhole := hBoth.transBoth hWrite
    (keep := Holds.KeepDying env slots L0 live store s)
    (fun r hr => ⟨hr, fun hApart => hApart (block store2 p)
      (List.mem_append_right _ (by simp))⟩)
  have hAfter : After env slots L0 live base heap store s (.tree shape) .owned
      (.node r words arrays buffers children) heap2 store3 s2 [.i64 p] := by
    refine ⟨?_, a2.frame, hHolds.step hWrite hKeepLive, hRep, ?_⟩
    · change Step heap store (Holds.KeepDying env slots L0 live store s) heap2 store3
        ((Ty.tree shape).blocks store3 [.i64 p] (.node r words arrays buffers children))
      apply hWhole.mono (fun _ hr => hr)
      intro b hb
      have hb := hBlocks.mem_iff.mp hb
      apply List.mem_append_left []
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ hb
    · intro u x hx _ wx hold length b hb c hc
      change b ∈ (Ty.tree shape).blocks store3 [.i64 p]
        (.node r words arrays buffers children) at hb
      have hb := hBlocks.mem_iff.mp hb
      have hRegions := (hHolds.regions_after hWrite hx hold length
        (hKeepLive u x hx wx hold length)).1
      rw [hRegions] at hc
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hRootApart u x hx (Or.inl rfl) wx hold length (block store2 p)
          (by simp [Ty.regions, Ty.blocks]) c hc
      · exact a2.apart u x hx wx hold length b hb c hc
  have hAlign : strict = true → HoldsA env slots live heap2 store3 s2 ∧
      Ty.AlignedVal .owned store3 (.tree shape) [.i64 p] (.node r words arrays buffers children) := by
    intro hs
    obtain ⟨hA2, hp, hCapacity⟩ := hAl2 hs
    refine ⟨HoldsA.step hHolds hA2 hWrite hA2.1 hKeepLive, fun b hb => ?_⟩
    change b ∈ (Ty.tree shape).blocks store3 [.i64 p] (.node r words arrays buffers children) at hb
    rcases List.mem_cons.mp (hBlocks.mem_iff.mp hb) with rfl | hb
    · have hBase := hRaw.base
      simp only [block]
      exact ⟨by omega, fun _ => by omega⟩
    · rw [hSame] at hb
      exact ⟨(hFieldsAl hs b hb).1, fun _ => (hFieldsAl hs b hb).2⟩
  rw [wpX_localGet_cons, hPtr]
  simpa only [hStack] using hNext store3 hAfter hAlign

/-- `spec_treeNode` under the flag. -/
theorem specX_treeNode {strict : Bool} {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    {r : Fin shape.records} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hRt : strict = true → AllocAligned m)
    (hCopy : CopyCodeX strict m host)
    (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (wordSpec : ∀ i env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (words i) env slots paid live)
    (arraySpec : ∀ i env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (arrays i) env slots paid live)
    (bufferSpec : ∀ i env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (buffers i) env slots paid live)
    (childSpec : ∀ i env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (children i) env slots paid live) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
        (Expr.treeNode r reuse words arrays buffers children) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom hPlace
    rest Q hTrap hNext
  let e := Expr.treeNode r reuse words arrays buffers children
  let ps : List Ty := tysOfFn (shape.words r) (shape.wordTy r) ++
    (List.replicate (shape.children r) (.tree shape) ++
      (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
        (List.replicate (shape.buffers r) .bytes ++ [])))
  let args := treeArgs words children arrays buffers
  let kept := fun k => live k || optionVarUses reuse k
  let L := fieldLive args.get kept
  let cost := argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args.get env)
  have hLen : ps.length =
      shape.words r + shape.children r + shape.arrays r + shape.buffers r := by
    simp [ps, tysOfFn_length, Nat.add_assoc]
  have hIn : L 0 = fun i => live i || e.uses i :=
    treeNode_entryLive reuse words arrays buffers children live
  have hEnd : L ps.length = kept := funext (fieldLive_end args.get kept)
  have hVars0 : Holds env slots (L 0) base heap store s := by rw [hIn]; exact hVars
  have hKept : ∀ i, kept i = true → L 0 i = true := by
    intro i hi
    simp only [L, fieldLive_zero, hi, Bool.true_or]
  have hLive : ∀ i, live i = true → kept i = true := by
    intro i hi
    simp only [kept, hi, Bool.true_or]
  have hSplit := dyingPot_split (store := store) (s := s) (env := env) (slots := slots)
    (paid := paid) (L 0) kept live hKept hLive
  have hCost : cost + treeParentCost shape r reuse slots live =
      e.allocs funs flags bounds (slots.map Slot.mode) paid live env :=
    treeNode_fieldCost reuse words arrays buffers children funs flags bounds slots paid live env
  have hWidthSum : (ps.map Ty.width).sum =
      shape.words r + shape.children r + shape.arrays r + 2 * shape.buffers r :=
    treeArgs_widths shape r
  have hArgsSpec : ∀ i live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (args.get i) env slots paid live :=
    treeArgs_forall (fun {t} _ (value : Expr S Γ t) => ∀ live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv value env slots paid live) words
      children arrays buffers
      (fun i => wordSpec i env slots paid) (fun i => childSpec i env slots paid)
      (fun i => arraySpec i env slots paid) (fun i => bufferSpec i env slots paid)
  simp only [Expr.placeArgs, Bool.and_eq_true, Bool.not_eq_true'] at hPlace
  have hArgsPlace : ∀ i, (args.get i).placeArgs = true :=
    treeArgs_forall (fun {t} _ (value : Expr S Γ t) => value.placeArgs = true) words children
      arrays buffers
      (fun i => by simpa using argsAny_eq_false hPlace.1.1.1 i)
      (fun i => by simpa using argsAny_eq_false hPlace.1.1.2 i)
      (fun i => by simpa using argsAny_eq_false hPlace.1.2 i)
      (fun i => by simpa using argsAny_eq_false hPlace.2 i)
  have hArgsD : ∀ i, (!(args.get i).fits funs fits env) = true →
      (!(e.fits funs fits env)) = true := by
    apply treeArgs_forall (fun {t} _ (value : Expr S Γ t) =>
      (!(value.fits funs fits env)) = true → (!(e.fits funs fits env)) = true) words children
      arrays buffers
    · intro i hi
      have hf : (words i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (words j).fits funs fits env) i hf,
        Bool.false_and, Bool.and_false, Bool.not_false]
    · intro i hi
      have hf : (children i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (children j).fits funs fits env) i hf,
        Bool.false_and, Bool.and_false, Bool.not_false]
    · intro i hi
      have hf : (arrays i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (arrays j).fits funs fits env) i hf,
        Bool.false_and, Bool.and_false, Bool.not_false]
    · intro i hi
      have hf : (buffers i).fits funs fits env = false := by simpa using hi
      simp only [e, Expr.fits, argsAll_false (fun j => (buffers j).fits funs fits env) i hf,
        Bool.and_false, Bool.not_false]
  have hWidths : ∀ i,
      base + shape.bindWidth r + max (args.get i).width (copyWidth (ps.get i)) ≤ h := by
    simp only [Expr.width] at hRoom
    let W := argsMax fun j => (words j).width
    let C := argsMax fun j => max (children j).width (copyWidth (.tree shape))
    let A := argsMax fun j => max (arrays j).width (copyWidth (shape.arrayTy r j))
    let B := argsMax fun j => max (buffers j).width (copyWidth .bytes)
    have hW := Nat.le_max_left W (max C (max A B))
    have hCAB := Nat.le_max_right W (max C (max A B))
    have hC := Nat.le_max_left C (max A B)
    have hAB := Nat.le_max_right C (max A B)
    have hA := Nat.le_max_left A B
    apply treeArgs_forall (fun {t} _ (value : Expr S Γ t) =>
      base + shape.bindWidth r + max value.width (copyWidth t) ≤ h) words children arrays buffers
    · intro i
      have hi := le_argsMax (fun j => (words j).width) i
      have hCopy : copyWidth (shape.wordTy r i) = 0 := by
        simp only [copyWidth, TreeShape.wordTy, Ty.scalar, ↓reduceIte]
      rw [hCopy, Nat.max_zero]
      omega
    · intro i
      have hi := le_argsMax (fun j => max (children j).width (copyWidth (.tree shape))) i
      omega
    · intro i
      have hi := le_argsMax (fun j => max (arrays j).width (copyWidth (shape.arrayTy r j))) i
      omega
    · intro i
      have hi := le_argsMax (fun j => max (buffers j).width (copyWidth .bytes)) i
      have hB := Nat.le_max_right A B
      omega
  have hParentRoom : base < h := by
    have hb : 1 ≤ shape.bindWidth r := by
      simp only [TreeShape.bindWidth, TreeShape.bindCount]
      omega
    simp only [Expr.width] at hRoom
    omega
  have hValues : (Env.ofFn fun i => (args.get i).denote funs env) =
      shape.fieldEnv r (fun i => (words i).denote funs env) (fun i => (arrays i).denote funs env)
        (fun i => (buffers i).denote funs env) (fun i => (children i).denote funs env) :=
    (Args.denote_eq_ofFn funs env args).symm.trans
      (treeArgs_denote funs env words children arrays buffers)
  have hBudget : TrapOK (!(e.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid (L 0) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env))) Q := by
    simpa only [trapFlag, Expr.aborts, Bool.true_or, Bool.true_and, hIn] using hTrap
  rw [treeNode_code_eq]
  simp only [List.append_assoc]
  have hRun := fieldsMixed_specX hm hRA hCopy ps args.get L
    (fieldLive_step args.get kept) (fun i => hArgsSpec i (L (i.val + 1))) hArgsPlace hArgsD
    (fieldBase := base + 1) (scratch := base + shape.bindWidth r) (by omega)
    (by rw [hWidthSum]; simp only [TreeShape.bindWidth, TreeShape.bindCount]; omega) hWidths
    heap store s hh hpv hBase hVars0 hAt (by rw [hIn]; exact hAl) (by rw [hIn]; exact hSafe) hCap
    (treeParentCode shape r reuse slots base live ++ (shape.tagStoreCode r base ++
      (treeStoreFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
        shape.fieldStart (shape.fields r) ++
        (treeStoreHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
          (base + 1 + shape.words r + shape.children r + shape.arrays r)
          (shape.fieldStart + (shape.fields r).length) ++
          (sealRecordCode (shape.width r) base (shape.mask r) ++ (.localGet base :: rest)))))) Q
    (hBudget.allocPart id (fun _ hw => hw.mono (by rw [hEnd, hSplit, ← hCost]; omega)))
    (fun heap1 store1 s1 ws aFields hAlFields hFrameFields holdFields hNormalFields hTopFields => by
      rw [hEnd] at aFields hAlFields hTopFields
      rw [hValues] at aFields hAlFields
      rw [treeArgs_types] at holdFields
      let sField : Locals := { s1 with values := s.values }
      have a := aFields.reframe (Frame.ofValues (values := s.values))
      refine wpX_treeParent reuse hm hRt a.holds (fun hs => (hAlFields hs).1.values s.values)
        a.step.at_ (by rw [a.step.cap m]; exact hCap)
        (by rw [a.frame.params]; exact hBase) (by rw [a.frame.positions, hh]; exact hParentRoom)
        (hBudget.allocPart (d' := false) nofun (fun hd hw => hw.shift
          (by simpa only [Nat.add_assoc] using hTopFields hd)
          (by rw [hSplit, ← hCost]; omega) (a.step.cap m)))
        fun heap2 store2 s2 p hRootStep hRootFrame hRootHolds hRaw hCount hPtr hStack hOther hApart
          hTopRoot hAlRoot => ?_
      have holdFields2 : LocalsHold s2 (base + 1) (shape.fieldTypes r) ws := by
        intro k hk
        have hold := holdFields k hk
        rw [hRootFrame.positions, hOther _ (by
          cases (shape.fieldTypes r).getD k .i64 <;> simp only [slotIndex] <;> omega)]
        exact hold
      have hFinish := wpX_finishTree (strict := strict) (m := m) (host := host) (Q := Q) (rest := rest)
        hVars0 a hRootStep hRootFrame hRootHolds hKept hLive hRaw hCount hPtr
        hStack (hRootFrame.positions.trans (a.frame.positions.trans hh)) hNormalFields holdFields2
        hApart hAlRoot (fun hs => (hAlFields hs).2)
        (fun store3 hAfter hAlAfter => by
          refine hNext heap2 store3 s2 [.i64 p]
            (by
              have hNorm := normalFamily_eq (α := fun i => Array (shape.arrayElem r i).denote)
                (fun i => (arrays i).denote funs env)
              simpa only [hIn, e, Expr.mode, Expr.denote, normalFamily_eq, hNorm] using hAfter)
            (fun hs => by
              have hNorm := normalFamily_eq (α := fun i => Array (shape.arrayElem r i).denote)
                (fun i => (arrays i).denote funs env)
              simpa only [e, Expr.mode, Expr.denote, normalFamily_eq, hNorm] using hAlAfter hs)
            fun hf => ?_
          have hd : (!(e.fits funs fits env)) = false := by simpa only [Bool.not_eq_false'] using hf
          have hTop1 := hTopFields hd
          change heap2.top.toNat ≤ heap.top.toNat +
            dyingPot store s env slots paid (fun i => live i || e.uses i) live +
              e.allocs funs flags bounds (slots.map Slot.mode) paid live env
          rw [← hIn, hSplit, ← hCost]
          omega)
      simpa only [List.append_assoc] using hFinish)
  simpa only [ps, args, L, kept, List.append_assoc, List.cons_append, List.nil_append] using hRun

end Verified
