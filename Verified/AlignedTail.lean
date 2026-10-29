import Verified.AlignedEnv
import Verified.AlignedLoops
import Verified.AlignedCopy
import Verified.TailCorrect

/-!
The tail loop's body under the flag.  `TailAligned` is the alignment of a tail body's outcome: the
next state's values, each aligned in its parameter's mode, or the owned result.
`TailCodeSpecAtX strict` is `TailCodeSpecAt` with `wpX strict` for `wp`, `HoldsA` of the
variables the body uses as a premise under `strict = true`, and, for the continuation, an aligned
heap and an aligned outcome.  `TailCodeSpecX.false_iff` states that at `strict = false` it is
`TailCodeSpec`.  `Tail.wpX_loop_indexed`, `tail_ret_specX`, and `TailCodeSpecX.released` are
their originals with these changes.
-/

namespace Verified.Tail

open Wasm LeanExe.ProofKit

variable {ι α : Type}

theorem wpX_loop_indexed {strict : Bool} {Inv : ι → AssertionF α} {rank : ι → Nat}
    {m : Module} {body rest : Program} {Q : Assertion α} {host : HostEnv α}
    {store : Store α} {s : Locals} {ps rs : Nat} {initial : ι}
    (hInit : Inv initial store s)
    (hStep : ∀ state store s, Inv state store s →
      wpX strict m body (fun cont => match cont with
        | .Fallthrough store' s' =>
          wpX strict m rest Q store' { s' with values := s'.values.take rs ++ s.values.drop ps } host
        | .Break 0 store' s' =>
          ∃ next, Inv next store' { s' with values := s'.values.take ps ++ s.values.drop ps } ∧
            rank next < rank state
        | .Break (k + 1) store' s' => Q (.Break k store' s')
        | other => Q other) store s host) :
    wpX strict m (.loop ps rs body :: rest) Q store s host := by
  refine wpX_loop_cons (fun store s => ∃ state, Inv state store s)
    (invariantRank Inv rank) ⟨initial, hInit⟩ ?_
  intro store s hi
  obtain ⟨state, hInv, hRank⟩ := invariantRank_spec (rank := rank) hi
  refine wpX.conseq ?_ (hStep state store s hInv)
  intro cont hc
  cases cont with
  | Break k store' s' =>
    cases k with
    | zero =>
      obtain ⟨next, hn, hlt⟩ := hc
      exact ⟨⟨next, hn⟩, Nat.lt_of_le_of_lt (invariantRank_le hn) (hRank ▸ hlt)⟩
    | succ k => exact hc
  | _ => exact hc

end Verified.Tail

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The alignment of a tail body's outcome: the next state's values, each in its parameter's
mode, or the owned result. -/
def TailAligned {params : List Ty} {result : Ty} (modes : List Mode) (store : Store Unit)
    (words : List Value) : Sum (Env params) result.denote → Prop
  | .inl state => Env.AlignedVals store (paramMode params modes) words state
  | .inr value => Ty.AlignedVal .owned store result words value

def TailCodeSpecAtX (strict : Bool) {S : List Sig} {Γ params : List Ty} {result : Ty}
    (m : Module) (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (host : HostEnv Unit) (pv : List Value) (targetModes : List Mode)
    (body : TailBody S params result Γ) (env : Env Γ)
    (pool : Bytes.LiteralPool) : Prop :=
  ∀ (slots : List Slot) (paid : List Bool) (nextPaid : List Bool) (resultPaid : Bool)
    (h stateBase resultBase base exitLabel nextLabel : Nat)
    (heap : Heap) (store : Store Unit) (s : Locals),
    s.positions = h → s.params = pv →
    Holds env slots body.uses base heap store s → heap.At store →
    (strict = true → HoldsA env slots body.uses heap store s) →
    pool.Safe env slots body.uses heap store s → store.memoryCap m 0 ≤ 65535 →
    s.params.length ≤ stateBase → stateBase + widthSum params ≤ resultBase →
    resultBase + result.width ≤ base → base + body.width targetModes ≤ h →
    body.placeArgs targetModes (slots.map Slot.mode) = true →
    (resultPaid = true → body.paidResult flags (slots.map Slot.mode) paid = true) →
    ∀ (Q : Assertion Unit),
    TrapOK (tailTrapFlag m body targetModes slots heap store
      (dyingPot store s env slots paid body.uses (fun _ => false) +
        body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env)
      (body.fits funs fits env)) Q →
    (∀ heap' store' s' (after : TailAfter env slots body.uses targetModes stateBase resultBase
        heap store s (body.denote funs env) heap' store' s'),
      (strict = true → heap'.Aligned ∧
        TailAligned targetModes store' after.words (body.denote funs env)) →
      (body.fits funs fits env = true →
        heap'.top.toNat + tailPot targetModes nextPaid resultPaid store' after.words
            (body.denote funs env) ≤
          heap.top.toNat + dyingPot store s env slots paid body.uses (fun _ => false) +
            body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel)) store'
        { s' with values := s.values })) →
    wpX strict m (body.code (pool := pool) targetModes h stateBase resultBase slots base exitLabel nextLabel) Q store s host

def TailCodeSpecX (strict : Bool) {S : List Sig} {Γ params : List Ty} {result : Ty}
    (m : Module) (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (host : HostEnv Unit) (pv : List Value) (targetModes : List Mode)
    (body : TailBody S params result Γ)
    (pool : Bytes.LiteralPool) : Prop :=
  ∀ env, TailCodeSpecAtX strict (pool := pool) m funs flags bounds fits host pv targetModes body env

/-- At `strict = false`, `TailCodeSpecAtX` is `TailCodeSpecAt`. -/
theorem TailCodeSpecAtX.false_iff {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} {targetModes : List Mode} {body : TailBody S params result Γ}
    {env : Env Γ} {pool : Bytes.LiteralPool} :
    TailCodeSpecAtX false m funs flags bounds fits host pv targetModes body env pool ↔
      TailCodeSpecAt m funs flags bounds fits host pv targetModes body env pool := by
  constructor
  · intro hX slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      hNext
    exact hX slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt nofun hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      fun heap' store' s' after _ hb => hNext heap' store' s' after hb
  · intro hC slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt _ hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      hNext
    exact hC slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      fun heap' store' s' after hb => hNext heap' store' s' after nofun hb

/-- At `strict = false`, `TailCodeSpecX` is `TailCodeSpec`. -/
theorem TailCodeSpecX.false_iff {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} {targetModes : List Mode} {body : TailBody S params result Γ}
    {pool : Bytes.LiteralPool} :
    TailCodeSpecX false m funs flags bounds fits host pv targetModes body pool ↔
      TailCodeSpec m funs flags bounds fits host pv targetModes body pool := by
  constructor
  · intro hX env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      hNext
    exact hX env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt nofun hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      fun heap' store' s' after _ hb => hNext heap' store' s' after hb
  · intro hC env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt _ hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      hNext
    exact hC env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
      heap store s hh hpv hVars hAt hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap
      fun heap' store' s' after hb => hNext heap' store' s' after nofun hb

theorem tail_ret_specX {strict : Bool} {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (_hm : Runtime m)
    (hCopy : CopyCodeX strict m host) (targetModes : List Mode)
    (value : Expr S Γ result)
    (valueSpec : ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv value env slots paid live) :
    TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes (.ret (params := params) value) := by
  intro env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel heap
    store s hh hpv hVars hAt hAl hSafe hCap hLow hState hResult hRoom hPlace hPaid Q hTrap hNext
  have hWidth : value.width ≤ max value.width (copyWidth result) := Nat.le_max_left ..
  have hCopyWidth : copyWidth result ≤ max value.width (copyWidth result) := Nat.le_max_right ..
  simp only [TailBody.width] at hRoom
  simp only [TailBody.placeArgs] at hPlace
  simp only [TailBody.paidResult] at hPaid
  simp only [tailTrapFlag, TailBody.aborts, TailBody.fits, TailBody.allocs, TailBody.uses] at hTrap
  simp only [TailBody.code, TailBody.codeWith, List.append_assoc]
  refine valueSpec env slots paid (fun _ => false) h base heap store s hh hpv
    (by simpa [TailBody.uses] using hVars) hAt
    (fun hs => by simpa [TailBody.uses] using hAl hs)
    (hSafe.mono fun i hi => by simpa [TailBody.uses] using hi) hCap
    (by omega) (by omega) hPlace _ _
    (hTrap.part id (fun ha => by
      simp only [Bool.or_eq_true] at ha ⊢
      tauto) fun _ hw => hw.mono (by simp only [Bool.false_or]; omega))
    fun heap1 store1 s1 ws1 after1 hAl1 hTop1 => ?_
  have after1' : After env slots value.uses (fun _ => false) base heap store s result
      (value.mode (slots.map Slot.mode)) (value.denote funs env) heap1 store1 s1 ws1 := by
    simpa only [Bool.false_or] using after1
  refine After.coerceX hCopy after1' hAl1 (fun _ => rfl) (Nat.le_refl _)
    (by rw [after1'.frame.params]; omega) (after1'.frame.positions.trans hh) (by omega)
    (by rw [after1'.step.cap m]; exact hCap)
    (fun hs _ hScalar => hTrap.alloc (by simp [hScalar]) fun hd hw =>
      hw.of_le (by
        have ht := hTop1 (fits_of_not hd)
        simp only [Bool.false_or] at ht
        simp only [coerceCost, hs, and_self, ↓reduceIte]
        omega) (after1'.step.cap m))
    fun heap2 store2 s2 ws2 after2 hTop2 hSame2 hAl2 => ?_
  refine wpX_storeCode ws2 h resultBase result.types s2 s.values after2.rep.typed
    (after2.frame.positions.trans hh) (by rw [after2.frame.params]; omega)
    (by rw [Ty.types_length, after2.frame.positions, hh]; omega) fun s3 frame3 hold3 _ => ?_
  rw [wpX_br_cons]
  refine hNext heap2 store2 s3
    ⟨ws2, after2.step,
      (after2.frame.mono (by omega)).trans (frame3.mono (by omega)), after2.rep, hold3⟩
    (fun hs => ⟨(hAl2 hs).1.1, (hAl2 hs).2⟩) ?_
  intro hf
  have ht := hTop1 hf
  simp only [Bool.false_or] at ht
  have hPot := pot_keep (P := resultPaid)
    (Q := value.paid flags (slots.map Slot.mode) paid (fun _ => false))
    (a := result.pot store2 ws2 (value.denote funs env))
    (b := result.pot store1 ws1 (value.denote funs env)) hPaid fun hp => by
      obtain ⟨rfl, rfl⟩ := hSame2 (Expr.mode_of_paid value (hPaid hp))
      rfl
  simp only [TailBody.fits, TailBody.uses, TailBody.allocs, TailBody.denote, tailPot]
  omega

theorem tail_ret_spec {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m) (targetModes : List Mode)
    (value : Expr S Γ result)
    (valueSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv value env slots paid live) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.ret (params := params) value) :=
  TailCodeSpecX.false_iff.mp (tail_ret_specX (strict := false) hm (copyCodeX hm) targetModes value
    (fun env slots paid live => CodeSpecX.false_iff.mpr (valueSpec env slots paid live)))
#print axioms tail_ret_spec

theorem TailCodeSpecX.released {strict : Bool} {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} {targetModes : List Mode}
    {body : TailBody S params result Γ} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m)
    (spec : TailCodeSpecX strict (pool := pool) m funs flags bounds fits host pv targetModes body)
    {env : Env Γ} {slots : List Slot} {paid nextPaid : List Bool} {resultPaid : Bool}
    {L0 : Nat → Bool} {h stateBase resultBase base exitLabel nextLabel : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots L0 base heap store s) (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots L0 heap store s)
    (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hLow : s.params.length ≤ stateBase)
    (hState : stateBase + widthSum params ≤ resultBase)
    (hResult : resultBase + result.width ≤ base)
    (hRoom : base + body.width targetModes ≤ h)
    (hPlace : body.placeArgs targetModes (slots.map Slot.mode) = true)
    (hPaid : resultPaid = true → body.paidResult flags (slots.map Slot.mode) paid = true)
    (hEntry : ∀ i, body.uses i = true → L0 i = true) {Q : Assertion Unit}
    (hTrap : TrapOK (!(body.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 (fun _ => false) +
        body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env))) Q)
    (hNext : ∀ heap' store' s'
      (after : TailAfter env slots L0 targetModes stateBase resultBase heap store s
        (body.denote funs env) heap' store' s'),
      (strict = true → heap'.Aligned ∧
        TailAligned targetModes store' after.words (body.denote funs env)) →
      (body.fits funs fits env = true → heap'.top.toNat +
        tailPot targetModes nextPaid resultPaid store' after.words (body.denote funs env) ≤
          heap.top.toNat + dyingPot store s env slots paid L0 (fun _ => false) +
            body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel))
        store' { s' with values := s.values })) :
    wpX strict m (releaseWhere Γ slots (fun i => L0 i && !body.uses i) ++
      body.code (pool := pool) targetModes h stateBase resultBase slots base exitLabel nextLabel)
      Q store s host := by
  refine wpX_releaseWhere hm hRA hVars hAt hAl (fun i hi => by
      simp only [Bool.and_eq_true] at hi; exact hi.1)
    (fun heap1 store1 released hTop1 hAl1 => ?_)
  have hLiveEq : (fun i => L0 i && !(L0 i && !body.uses i)) = body.uses := by
    funext i
    have hi := hEntry i
    cases h0 : L0 i <;> cases hb : body.uses i <;> simp_all
  rw [hLiveEq] at released hAl1
  have hPot := dyingPot_evolves (paid := paid) hVars released hEntry
    body.uses (fun _ => false) (fun _ hi => hi)
  have hPotLe : dyingPot store s env slots paid body.uses (fun _ => false) ≤
      dyingPot store s env slots paid L0 (fun _ => false) :=
    dyingPot_mono hEntry nofun
  have hBudget : TrapOK (!(body.fits funs fits env) ||
      (true && !decide (heap.Within store m
        (dyingPot store s env slots paid L0 (fun _ => false) +
          body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env)))) Q := by
    simpa only [Bool.true_and] using hTrap
  refine spec env slots paid nextPaid resultPaid h stateBase resultBase base exitLabel nextLabel
    heap1 store1 s hh hpv released.holds released.step.at_ hAl1
    (hSafe.evolves hVars released hEntry)
    (by rw [released.step.cap m]; exact hCap) hLow hState hResult hRoom hPlace hPaid _
    (hBudget.part id (fun _ => rfl) (fun _ hw => hw.shift
      (heap1 := heap1) (store1 := store1) (c1 := 0)
      (by have ht := congrArg UInt64.toNat hTop1; omega)
      (by rw [hPot]; omega) (released.step.cap m)))
    (fun heap2 store2 s2 after hAl2 hTop2 => ?_)
  refine hNext heap2 store2 s2 (TailAfter.prepend hVars released after hEntry (by omega)) hAl2
    (fun hf => ?_)
  have h2 := hTop2 hf
  have h1 := congrArg UInt64.toNat hTop1
  rw [hPot] at h2
  change heap2.top.toNat +
    tailPot targetModes nextPaid resultPaid store2 after.words (body.denote funs env) ≤ _
  omega

theorem TailCodeSpec.released {S : List Sig} {Γ params : List Ty} {result : Ty} {m : Module}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool}
    {host : HostEnv Unit} {pv : List Value} {targetModes : List Mode}
    {body : TailBody S params result Γ} (hm : Runtime m)
    (spec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes body)
    {env : Env Γ} {slots : List Slot} {paid nextPaid : List Bool} {resultPaid : Bool}
    {L0 : Nat → Bool} {h stateBase resultBase base exitLabel nextLabel : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots L0 base heap store s) (hAt : heap.At store)
    (hSafe : pool.Safe env slots L0 heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hLow : s.params.length ≤ stateBase)
    (hState : stateBase + widthSum params ≤ resultBase)
    (hResult : resultBase + result.width ≤ base)
    (hRoom : base + body.width targetModes ≤ h)
    (hPlace : body.placeArgs targetModes (slots.map Slot.mode) = true)
    (hPaid : resultPaid = true → body.paidResult flags (slots.map Slot.mode) paid = true)
    (hEntry : ∀ i, body.uses i = true → L0 i = true) {Q : Assertion Unit}
    (hTrap : TrapOK (!(body.fits funs fits env) || !decide (heap.Within store m
      (dyingPot store s env slots paid L0 (fun _ => false) +
        body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env))) Q)
    (hNext : ∀ heap' store' s'
      (after : TailAfter env slots L0 targetModes stateBase resultBase heap store s
        (body.denote funs env) heap' store' s'),
      (body.fits funs fits env = true → heap'.top.toNat +
        tailPot targetModes nextPaid resultPaid store' after.words (body.denote funs env) ≤
          heap.top.toNat + dyingPot store s env slots paid L0 (fun _ => false) +
            body.allocs funs flags bounds targetModes nextPaid (slots.map Slot.mode) paid env) →
      Q (.Break ((body.denote funs env).elim (fun _ => nextLabel) (fun _ => exitLabel))
        store' { s' with values := s.values })) :
    wp m (releaseWhere Γ slots (fun i => L0 i && !body.uses i) ++
      body.code (pool := pool) targetModes h stateBase resultBase slots base exitLabel nextLabel)
      Q store s host :=
  TailCodeSpecX.released (strict := false) hm nofun (TailCodeSpecX.false_iff.mpr spec) hh hpv hVars
    hAt nofun hSafe hCap hLow hState hResult hRoom hPlace hPaid hEntry hTrap
    (fun heap' store' s' after _ a2 => hNext heap' store' s' after a2)
#print axioms TailCodeSpec.released

end Verified
