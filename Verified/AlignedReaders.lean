import Verified.AlignedScalar
import Verified.AlignedAccess
import LeanExe.ProofKit.AlignedFree

/-!
The readers under the flag: a variable, the size and bytes of a buffer, a bound test against an
array's size, an array's element, and a component of a tuple.  Each is its original in
`VarCorrect.lean` or `ExprCorrect.lean` with the changes of `AlignedScalar.lean`.  The loads of
an array's length and words are at its pointer, which `HoldsA` makes a multiple of 8.

The copy of an owned variable that stays live runs `copyCode`, whose flagged form is
`CopyCodeX`: from an aligned heap and an aligned value, the copy's accesses are aligned and it
leaves an aligned heap and an aligned owned value.  `specX_var` takes it as a premise, as
`specX_size` takes `ReadReleaseX`, and `copyCodeX` in `Verified/AlignedCopy.lean` proves it for
every runtime.  The code of the other readers is free of 64-bit accesses and calls except for the
loads, so `wpX_append_free` carries the original lemmas about `loadCode` and the buffer read.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem loadCode_free (h : Nat) : (loc : Nat) → (tys : List ValueType) →
    freeCode (loadCode h loc tys) = true
  | _, [] => rfl
  | loc, _ :: tys => by simp [loadCode, freeCode, freeInst, loadCode_free h (loc + 1) tys]

/-- `wp_loadCode` under the flag. -/
theorem wpX_loadCode {α : Type} {strict : Bool} {m : Module} {Q : Assertion α} {store : Store α}
    {host : HostEnv α} (vals : List Value) {h loc : Nat} {tys : List ValueType} {s : Locals}
    {rest : Program} (hw : vals.length = tys.length) (hh : s.positions = h)
    (hold : LocalsHold s loc tys vals)
    (hk : wpX strict m rest Q store { s with values := vals.reverse ++ s.values } host) :
    wpX strict m (loadCode h loc tys ++ rest) Q store s host := by
  refine wpX_append_free (loadCode_free h loc tys) ?_
  have := wp_loadCode (m := m) (host := host) (rest := [])
    (Q := ThenX strict m rest Q host) vals hw hh hold (wp_nil.mpr hk)
  rwa [List.append_nil] at this

/-- `Bytes.wp_get` under the flag. -/
theorem Bytes.wpX_get {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {root length index : UInt64} {bytes : LeanExe.Bytes}
    {rootSlot lengthSlot indexSlot : Nat} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (h : Bytes.Rep heap store root length bytes)
    (hRoot : s.get rootSlot = some (.i64 root))
    (hLength : s.get lengthSlot = some (.i64 length))
    (hIndex : s.get indexSlot = some (.i64 index))
    (hNext : wpX strict m rest Q store { s with values := .i64 (bytes.get index) :: s.values }
      host) :
    wpX strict m (Bytes.getCode rootSlot lengthSlot indexSlot ++ rest) Q store s host := by
  refine wpX_append_free rfl ?_
  have := Bytes.wp_get (m := m) (host := host) (rest := [])
    (Q := ThenX strict m rest Q host) hHeap h hRoot hLength hIndex (wp_nil.mpr hNext)
  rwa [List.append_nil] at this

theorem wpX_scaleCode {strict : Bool} {m : Module} {st : Store Unit} {env' : HostEnv Unit}
    {s : Locals} {vs : List Value} {rest : Program} {Q : Assertion Unit} (k : Nat) (x : UInt64) :
    wpX strict m (scaleCode k ++ rest) Q st { s with values := .i64 x :: vs } env' ↔
      wpX strict m rest Q st { s with values := .i64 (x * wordCount k) :: vs } env' := by
  unfold scaleCode
  split
  · next hk => subst hk; simp [wordCount]
  · simp

theorem wp_scaleCode {st : Store Unit} {env' : HostEnv Unit} {s : Locals} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (k : Nat) (x : UInt64) :
    wp m (scaleCode k ++ rest) Q st { s with values := .i64 x :: vs } env' ↔
      wp m rest Q st { s with values := .i64 (x * wordCount k) :: vs } env' :=
  wpX_scaleCode (strict := false) k x

/-- `wp_loadWordsCode` under the flag. -/
theorem wpX_loadWordsCode {strict : Bool} {m : Module} {store : Store Unit} {env' : HostEnv Unit}
    {ptr w0 flag : Nat} {p w : UInt64} {ws : Array UInt64} {rest : Program} {Q : Assertion Unit}
    (b : Bool) (hA : b = true → UInt64Array.At store p ws)
    (hp : strict = true → b = true → p.toNat % 8 = 0)
    (j : Nat) (tys : List ValueType) (s : Locals) (vals : List UInt64)
    (hP : s.get ptr = some (.i64 p)) (hW : s.get w0 = some (.i64 w))
    (hF : s.get flag = some (.i64 (boolWord b))) (hl : vals.length = tys.length)
    (hT : b = true → w.toNat + j + tys.length ≤ ws.size ∧
      ∀ i, i < vals.length → ws[w.toNat + j + i]! = vals[i]!)
    (hZ : b = false → vals = List.replicate tys.length 0)
    (hk : wpX strict m rest Q store
      { s with values := (List.zipWith typedValue tys vals).reverse ++ s.values } env') :
    wpX strict m (loadWordsCode ptr w0 flag j tys ++ rest) Q store s env' := by
  cases strict
  · exact wp_loadWordsCode b hA j tys s vals hP hW hF hl hT hZ hk
  · exact wpA_loadWordsCode b hA (hp rfl) j tys s vals hP hW hF hl hT hZ hk

/-- The flagged `wp_copyCode`: the copy of a value of type `t` whose words locals `src` on hold,
which from an aligned heap and an aligned value leaves an aligned heap and an aligned owned
copy. -/
def CopyCodeX (strict : Bool) (m : Module) (host : HostEnv Unit) : Prop :=
  ∀ (t : Ty) {heap : Heap} {store : Store Unit} {s : Locals} {h src base : Nat} {mode : Mode}
    {ws : List Value} {v : t.denote} {rest : Program} {Q : Assertion Unit},
    heap.At store → store.memoryCap m 0 ≤ 65535 →
    TrapOK (!decide (heap.Within store m (t.copyCost v))) Q → s.positions = h →
    t.Rep mode heap store ws v → LocalsHold s src t.types ws → src + t.width ≤ base →
    s.params.length ≤ base → base + t.copyScratch ≤ s.positions →
    (strict = true → heap.Aligned ∧ Ty.AlignedVal mode store t ws v) →
    (∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ws' : List Value),
      Step heap store (fun _ => True) heap' store' (t.blocks store' ws' v) →
      t.Rep .owned heap' store' ws' v → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + t.copyCost v →
      (strict = true → heap'.Aligned ∧ Ty.AlignedVal .owned store' t ws' v) →
      wpX strict m rest Q store' { s' with values := ws'.reverse ++ s.values } host) →
    wpX strict m (copyCode h t src base ++ rest) Q store s host

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value} {strict : Bool}

/-- A variable: a copy when it is owned and stays live, and its own words otherwise. -/
theorem specX_var (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {tTy : Ty}
    (x : Var Γ' tTy) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.var (S := S) x) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ hCap hBase hRoom _
      rest Q hTrap hNext
  have hx : (fun i => live i || (Expr.var (S := S) x).uses i) x.index = true := by
    simp [Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  have hl := hRep.length
  have hMode : (Expr.var (S := S) x).mode (slots.map Slot.mode) =
      (slots.getD x.index default).mode := Slot.modes_getD slots x.index
  have hLiveIn : ∀ i, live i = true → (live i || (Expr.var (S := S) x).uses i) = true :=
    fun i h => by simp [h]
  have hAlX : strict = true → Ty.AlignedVal (slots.getD x.index default).mode store tTy ws
      (env.get x) := fun hs => (hAl hs).2 _ x hx ws hold hl
  by_cases hCopy' : (slots.getD x.index default).mode = .owned ∧ live x.index = true
  · obtain ⟨hOwned, hLiveX⟩ := hCopy'
    simp only [Expr.code, Var.code, hOwned, hLiveX, and_self, ↓reduceIte]
    have hc : (Expr.var (S := S) x).allocs funs flags bounds (slots.map Slot.mode) paid live env =
        tTy.copyCost (env.get x) := by
      simp only [Expr.allocs, Var.cost, modeAt, Slot.modes_getD, hOwned, hLiveX, and_self,
        ↓reduceIte]
    have hT : TrapOK (false || (true && !decide (heap.Within store m (tTy.copyCost (env.get x)))))
        Q := hTrap.part nofun (fun _ => by simp [Slot.any_owned hOwned])
      fun _ hw => hw.mono (by rw [hc]; omega)
    refine hCopy tTy hAt hCap hT hh hRep hold hBelow hBase
      (by rw [hh]; simpa [Expr.width] using hRoom) (fun hs => ⟨(hAl hs).1, hAlX hs⟩)
      fun heap' store' s' ws' hStep hRep' hF hTop hAl' => ?_
    have hHolds := (hVars.live_mono hLiveIn).step hStep (fun _ _ _ _ _ _ _ _ => trivial)
    refine hNext heap' store' s' ws' ⟨?_, hF, hHolds.frame hF le_rfl, ?_, ?_⟩
      (fun hs => ⟨HoldsA.agree hHolds (HoldsA.step (hVars.live_mono hLiveIn)
          ((hAl hs).live_mono hLiveIn) hStep (hAl' hs).1 fun _ _ _ _ _ _ _ _ => trivial) hF,
        by rw [hMode, hOwned]; exact (hAl' hs).2⟩)
      (fun _ => top_unpaid_le (by simp [Expr.paid, hLiveX]) (by rw [hc]; exact hTop))
    · rw [hMode, hOwned]
      exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · rw [hMode, hOwned]; exact hRep'
    · rw [hMode, hOwned]
      intro u y hy _ wy hwy hly b hb c hc
      have hwy' := ((hVars.live_mono hLiveIn).hold_agree hF hy hly).mp
        hwy
      obtain ⟨hSame, hFresh⟩ := (hVars.live_mono hLiveIn).regions_after hStep hy hwy' hly
        fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · simp only [Expr.code, Var.code, hCopy', ↓reduceIte]
    by_cases hOwned : (slots.getD x.index default).mode = .owned
    · have hDead : live x.index = false := by
        cases h : live x.index
        · rfl
        · exact absurd ⟨hOwned, h⟩ hCopy'
      refine wpX_loadCode ws hRep.typed hh hold (hNext heap store s ws ⟨?_, Frame.refl base s,
        hVars.live_mono hLiveIn, ?_, ?_⟩
        (fun hs => ⟨(hAl hs).live_mono hLiveIn, by rw [hMode]; exact hAlX hs⟩)
        fun _ => top_move x hold hl hOwned hDead)
      · rw [hMode, hOwned]
        exact ⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr,
          fun b hb => hk tTy x hx hDead hOwned ws hold hl b hb⟩⟩
      · rw [hMode]; exact hRep
      · rw [hMode, hOwned]
        intro u y hy _ wy hwy hly b hb c hc
        have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
        exact hVars.2 tTy u x y hx (hLiveIn _ hy) hne hOwned ws wy hold hl hwy hly b hb c hc
    · have hBorrowed : (slots.getD x.index default).mode = .borrowed := by
        cases h : (slots.getD x.index default).mode
        · rfl
        · exact absurd h hOwned
      refine wpX_loadCode ws hRep.typed hh hold (hNext heap store s ws (After.refl hAt hVars hLiveIn
        (by rw [hMode]; exact hRep) (by rw [hMode, hBorrowed]; rfl) ?_)
        (fun hs => ⟨(hAl hs).live_mono hLiveIn, by rw [hMode]; exact hAlX hs⟩)
        fun _ => top_unpaid_le
          (by simp only [Expr.paid, modeAt, Slot.modes_getD, hBorrowed]; rfl)
          (Nat.le_add_right _ _))
      rw [hMode]
      intro u y hy hm wy hwy hly b hb c hc
      rcases hm with hm | hm
      · exact absurd hm hOwned
      · have hne : y.index ≠ x.index := fun he => by
          rw [he] at hm; exact hOwned hm
        rw [hm] at hc
        exact regionsDisjoint_symm
          (hVars.2 u tTy y x (hLiveIn _ hy) hx hne hm wy ws hwy hly hold hl c hc b hb)

theorem specX_bytesSize (hRel : ReadReleaseX strict m host) {Γ' : List Ty} (x : Var Γ' .bytes) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.bytesSize (S := S) x) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  obtain ⟨_, _, hold, root, length, rfl, hBytes⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hLength : s.get ((slots.getD x.index default).loc + 1) = some (.i64 length) := by
    simpa [Ty.types, slotIndex] using hold 1 (by simp)
  simp only [Expr.code, List.cons_append, List.nil_append,
    wpX_localGet_cons, hLength]
  refine hRel x hVars hAt hAl fun heap' store' ev hTop hAl' => ?_
  exact hNext heap' store' s [.i64 length]
    (After.ofScalar rfl ev.step rfl ev.frame ev.holds (by
      simp only [Ty.rep_word, Expr.denote, hBytes.size_eq]))
    (fun hs => ⟨hAl' hs, Ty.AlignedVal.scalar rfl⟩)
    fun _ => top_unpaid_le rfl (by rw [hTop]; omega)

theorem specX_bytesGet (hRel : ReadReleaseX strict m host) {Γ' : List Ty} (x : Var Γ' .bytes)
    {index : Expr S Γ' .word}
    (indexSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv index env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.bytesGet x index) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
    hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hIndexWidth : index.width ≤ max index.width 1 := Nat.le_max_left ..
  have hScratch : 1 ≤ max index.width 1 := Nat.le_max_right ..
  simp only [Expr.placeArgs] at hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hIn : ∀ k, ((live k || k == x.index) || index.uses k) = true →
      (live k || (Expr.bytesGet x index).uses k) = true := fun k hk => by
    simp only [Expr.uses]; exact live_assoc _ _ _ hk
  have hD : dyingPot store s env slots paid (fun k => (live k || k == x.index) || index.uses k)
      (fun k => live k || k == x.index) ≤
        dyingPot store s env slots paid (fun k => live k || (Expr.bytesGet x index).uses k) live :=
    dyingPot_mono hIn fun k hk => by simp [hk]
  refine indexSpec env slots paid (fun k => live k || k == x.index) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase
    (by omega) hPlace _ _
    (hTrap.part id id fun _ hw => hw.mono (by dsimp only; simp only [Expr.allocs]; omega))
    fun heap1 store1 s1 ws1 a1 hAl1 hTop1 => ?_
  have hValue := a1.rep
  simp only [Ty.rep_word] at hValue
  subst hValue
  have e1 := a1.toEvolves rfl
  obtain ⟨hBelow, _, hold, root, length, rfl, hBytes⟩ := e1.holds.1 _ x (by simp)
  have hRoot : s1.get (slots.getD x.index default).loc = some (.i64 root) := by
    simpa [Ty.types, slotIndex] using hold 0 (by simp)
  have hLength : s1.get ((slots.getD x.index default).loc + 1) = some (.i64 length) := by
    simpa [Ty.types, slotIndex] using hold 1 (by simp)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    rw [e1.frame.params]; exact hBase
  have hHigh : base < s1.positions := by rw [e1.frame.positions, hh]; omega
  refine wpX_localSet_local hLow (Locals.lt_total hHigh) ?_
  let s1a := setLocal { s1 with values := s.values } base (.i64 (index.denote funs env))
  have hIndex : s1a.get base = some (.i64 (index.denote funs env)) :=
    Locals.get_setLocal_same hLow (Locals.lt_total hHigh)
  have hRoot' : s1a.get (slots.getD x.index default).loc = some (.i64 root) := by
    rw [Locals.get_setLocal_ne hLow (by change _ + 2 ≤ base at hBelow; omega), Locals.get_values]
    exact hRoot
  have hLength' : s1a.get ((slots.getD x.index default).loc + 1) = some (.i64 length) := by
    rw [Locals.get_setLocal_ne hLow (by change _ + 2 ≤ base at hBelow; omega), Locals.get_values]
    exact hLength
  have f1 : Frame base s1 s1a := Frame.setValues hLow le_rfl hHigh
  have hFrame : Frame base s s1a := e1.frame.trans f1
  have hVars1 := e1.holds.agree f1
  have hAlA : strict = true → HoldsA env slots (fun k => live k || k == x.index) heap1 store1 s1a :=
    fun hs => HoldsA.agree e1.holds (hAl1 hs).1 f1
  show wpX strict m _ Q store1 s1a host
  refine Bytes.wpX_get e1.step.at_ hBytes hRoot' hLength' hIndex ?_
  refine hRel x hVars1 e1.step.at_ hAlA fun heap2 store2 e2 hTop2 hAl2 => ?_
  have e12 := Evolves.trans (hVars.live_mono hIn) ⟨e1.step, hFrame, hVars1⟩ e2
    (fun k hk => by simp [hk]) fun k hk => by simp [hk]
  exact hNext heap2 store2 s1a [.i64 ((env.get x).get (index.denote funs env))]
    ((After.ofScalar (t := .word) (mode := .borrowed) rfl e12.step rfl e12.frame e12.holds
      rfl).liveIn hIn)
    (fun hs => ⟨hAl2 hs, Ty.AlignedVal.scalar rfl⟩)
    fun hd => by rw [hTop2]; exact top_part rfl hD (hTop1 hd)

theorem specX_leSize (hm : Runtime m) (hRel : ReadReleaseX strict m host)
    (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {e : Elem}
    (x : Var Γ' (.array e)) (i : Var Γ' .word) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.leSize (S := S) x i) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
    hPlace rest Q hTrap hNext
  obtain ⟨_, _, _, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hValue := Expr.leSizeExpand_denote x i funs env hRep.array_size_lt
  have hCmp : CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.leSizeExpand x i) env slots paid live :=
    specX_cmp .le (specX_var hCopy i) (specX_size hm hRel x) env slots paid live
  simp only [CodeSpecX, trapFlag, Expr.leSizeExpand_uses, Expr.leSizeExpand_width,
    Expr.leSizeExpand_placeArgs, Expr.leSizeExpand_aborts, Expr.leSizeExpand_allocs,
    Expr.leSizeExpand_fits, Expr.leSizeExpand_mode, Expr.leSizeExpand_paid,
    Expr.leSizeExpand_code, hValue] at hCmp
  exact hCmp h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom hPlace rest Q hTrap
    hNext

/-- A read of an array variable: the position in local `base`, a comparison of it with the
array's size as a flag in local `base + 1`, the position of the element's first word in local
`base`, the loads of its words under the flag, and the release of the variable when it is owned and
dies there.  The length and the words are loaded at the array's pointer, which `HoldsA` makes a
multiple of 8. -/
theorem specX_get (hRel : ReadReleaseX strict m host) {Γ' : List Ty} {e : Elem}
    (x : Var Γ' (.array e)) {i : Expr S Γ' .word}
    (iSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv i env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.get x i) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi : i.width ≤ max i.width 2 := Nat.le_max_left ..
  have h2 : 2 ≤ max i.width 2 := Nat.le_max_right ..
  simp only [Expr.placeArgs] at hPlace
  simp only [Expr.code, getCode, List.append_assoc, List.cons_append,
    List.nil_append]
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.get x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  have hD : dyingPot store s env slots paid (fun k => (live k || k == x.index) || i.uses k)
      (fun k => live k || k == x.index) ≤
        dyingPot store s env slots paid (fun k => live k || (Expr.get x i).uses k) live :=
    dyingPot_mono hIn fun k h => by simp [h]
  refine iSpec env slots paid (fun k => live k || k == x.index) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase
    (by omega) hPlace _ _
    (hTrap.part id id fun _ hw => hw.mono (by dsimp only; simp only [Expr.allocs]; omega))
    fun heap1 store1 s1 ws1 a1 hAl1 hTop1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  obtain ⟨hBelowX, wx, holdx, hRepx⟩ := e1.holds.1 _ x (by simp)
  obtain ⟨ptr, rfl, hBx⟩ := hRepx
  have hPtrAl : strict = true → ptr.toNat % 8 = 0 := fun hs =>
    Ty.AlignedVal.array hBx ((hAl1 hs).1.2 _ x (by simp) [.i64 ptr] holdx rfl)
  have hA := hBx.borrow.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hk := e.width_pos
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  simp only [Ty.width] at hBelowX
  have hPtr1 : s1.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word holdx
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHigh1 : base < s1.positions := by rw [hh1]; omega
  refine wpX_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  let s1a := setLocal { s1 with values := s.values } base (.i64 (i.denote funs env))
  have hK : s1a.get base = some (.i64 (i.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hP : s1a.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]
    exact hPtr1
  show wpX strict m _ Q store1 s1a host
  simp only [wpX_localGet_cons, Locals.get_values, hK, hP, wpX_wrapI64_cons, wpX_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wpX_divCode hk,
    words_div hk hnk]
  refine ⟨fun hs => UInt64.toUInt32_mod8 (hPtrAl hs), ?_⟩
  simp only [wpX_ltUI64_cons, wpX_extendUI32_cons]
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  set b := decide ((i.denote funs env).toNat < (env.get x).size) with hb
  have hFlag : UInt64.ofNat (if i.denote funs env < UInt64.ofNat (env.get x).size then (1 : UInt32)
      else 0).toNat = boolWord b := by
    by_cases hc : (i.denote funs env).toNat < (env.get x).size
    · simp [hb, hc, hLess.mpr hc, boolWord]
    · simp [hb, hc, (not_congr hLess).mpr hc, boolWord]
  rw [hFlag]
  have hLowB : ({ s1a with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s1.params.length ≤ base + 1; rw [hp1]; omega
  have hHighB : base + 1 < ({ s1a with values := s.values } : Locals).positions := by
    simp only [s1a, Locals.positions_setLocal, Locals.positions_values, hh1]; omega
  refine wpX_localSet_local hLowB (Locals.lt_total hHighB) ?_
  let s1b := setLocal { s1a with values := s.values } (base + 1) (.i64 (boolWord b))
  have hFb : s1b.get (base + 1) = some (.i64 (boolWord b)) :=
    Locals.get_setLocal_same hLowB (Locals.lt_total hHighB)
  have hKb : s1b.get base = some (.i64 (i.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hK
  have hPb : s1b.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hP
  show wpX strict m _ Q store1 s1b host
  simp only [wpX_localGet_cons, hKb]
  rw [wpX_scaleCode]
  have hLowC : ({ s1b with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHighC : base < ({ s1b with values := s.values } : Locals).positions := by
    simp only [s1b, s1a, Locals.positions_setLocal, Locals.positions_values, hh1]; omega
  refine wpX_localSet_local hLowC (Locals.lt_total hHighC) ?_
  let s1c := setLocal { s1b with values := s.values } base
    (.i64 (i.denote funs env * wordCount e.width))
  have hWc : s1c.get base = some (.i64 (i.denote funs env * wordCount e.width)) :=
    Locals.get_setLocal_same hLowC (Locals.lt_total hHighC)
  have hFc : s1c.get (base + 1) = some (.i64 (boolWord b)) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hFb
  have hPc : s1c.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hPb
  have f1 : Frame base s1 s1c :=
    ((Frame.setValues (s := s1) (vs := s.values) hLow1 le_rfl hHigh1).trans
      (Frame.setValues (s := s1a) (vs := s.values) hLowB (by omega)
        (by simpa [s1a, Locals.positions_setLocal, Locals.positions_values] using hHighB))).trans
      (Frame.setValues (s := s1b) (vs := s.values) hLowC le_rfl
        (by simpa [s1b, s1a, Locals.positions_setLocal, Locals.positions_values] using hHighC))
  have hFrame : Frame base s s1c := e1.frame.trans f1
  have hVars1 : Holds env slots (fun k => live k || k == x.index) base heap1 store1 s1c :=
    e1.holds.agree f1
  have hAlC : strict = true → HoldsA env slots (fun k => live k || k == x.index) heap1 store1 s1c :=
    fun hs => HoldsA.agree e1.holds (hAl1 hs).1 f1
  have hsc : s1c.values = s.values := rfl
  show wpX strict m _ Q store1 s1c host
  refine wpX_loadWordsCode (ws := e.words (env.get x)) b (fun _ => hA) (fun hs _ => hPtrAl hs) 0
    e.types s1c (e.toWords (env.get x)[(i.denote funs env).toNat]!) hPc hWc hFc
    (by rw [e.toWords_length, e.types_length]) (fun hbt => ?_) (fun hbf => ?_) ?_
  · have hc : (i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbt
    have hw : (i.denote funs env * wordCount e.width).toNat =
        (i.denote funs env).toNat * e.width := by
      have hs := words_scale (i := (i.denote funs env).toNat) hk
        (lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hc)) hnk)
      rw [UInt64.ofNat_toNat] at hs
      rw [hs, UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 18446744073709551616 from rfl]
          have := Nat.mul_le_mul_right e.width (Nat.le_of_lt hc); omega)]
    rw [hw, e.types_length, Elem.words_size]
    refine ⟨by
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
        rw [Nat.succ_mul] at this; omega,
      fun j hj => ?_⟩
    rw [e.toWords_length] at hj
    rw [Nat.add_zero, Elem.words_getElem! e _ hc hj, getElem!_pos (env.get x) _ hc]
  · have hc : ¬(i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbf
    rw [getElem!_neg (env.get x) _ hc, e.toWords_default, e.types_length]
  · rw [e.values_typed, hsc]
    refine hRel x hVars1 e1.step.at_ hAlC fun heap2 store2 e2 hTop2 hAl2 => ?_
    have e12 := Evolves.trans (hVars.live_mono hIn) ⟨e1.step, hFrame, hVars1⟩ e2
      (fun k h => by simp [h]) fun k h => by simp [h]
    exact hNext heap2 store2 s1c (e.values (env.get x)[(i.denote funs env).toNat]!)
      ((After.ofScalar (t := .elem e) (mode := .borrowed) rfl e12.step rfl e12.frame e12.holds
        rfl).liveIn hIn)
      (fun hs => ⟨hAl2 hs, Ty.AlignedVal.scalar rfl⟩)
      fun hd => by rw [hTop2]; exact top_part rfl hD (hTop1 hd)

/-- A component of a tuple variable: the loads of the words that hold it. -/
theorem specX_proj {Γ' : List Ty} {e e' : Elem} (x : Var Γ' (.elem e)) (p : Path e e') :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.proj (S := S) x p) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hRep' : ws = e.values (env.get x) := hRep
  subst hRep'
  simp only [Expr.code]
  exact wpX_loadCode _ (by rw [e'.values_length, e'.types_length]) hh (p.holds hold)
    (hNext heap store s _ (After.refl hAt hVars (by intro i h; simp [Expr.uses, h]) rfl rfl
      (Holds.Apart.ofScalar rfl))
      (fun hs => ⟨(hAl hs).live_mono (by intro i h; simp [Expr.uses, h]),
        Ty.AlignedVal.scalar rfl⟩)
      fun _ => Nat.le_add_right _ _)

/-- A component of a tuple variable: the loads of the words that hold it. -/
theorem spec_proj {Γ' : List Ty} {e e' : Elem} (x : Var Γ' (.elem e)) (p : Path e e') :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.proj (S := S) x p) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_proj (strict := false) x p env slots paid live)

end Cases

end Verified
