import Verified.ExprSpec
import Verified.ArgsCorrect
import Verified.VarCorrect
import Verified.Float32Correct
import Verified.TreeNodeCorrect
import Verified.TreeCaseCorrect
import Verified.ListFoldCorrect
import Verified.Bytes.Get
import Verified.BytesBuildCorrect
import Verified.BytesLiteralCorrect
import Verified.LiteralCoverage
import Verified.LiteralCoverageFacts

/-! Correctness of expression code and ordinary function templates. -/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit}
  {pv : List Value}

/-- The release of a variable that a reader reads, when it is owned and dies there,
which leaves `top`. -/
theorem read_release (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    {vals : List Value} {rest : Program} {Q : Assertion Unit} {t : Ty} (x : Var Γ t)
    (hVars : Holds env slots (fun k => live k || k == x.index) base heap store s)
    (hAt : heap.At store)
    (hNext : ∀ heap' store', Evolves env slots (fun k => live k || k == x.index) live base heap
      store s heap' store' s → heap'.top = heap.top →
      wp m rest Q store' { s with values := vals } host) :
    wp m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode t (slots.getD x.index default).loc else []) ++ rest) Q store
      { s with values := vals } host := by
  have hCode : (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode t (slots.getD x.index default).loc else []) =
      (if live x.index = false then [x.index] else []).flatMap (releaseVar Γ slots) := by
    cases live x.index <;> simp [releaseVar, x.getElem?_index]
  rw [hCode]
  refine wp_releaseVars hm _ (by split <;> simp) (hVars.agree Frame.ofValues) hAt
    (by split <;> simp) fun heap' store' e hTop => hNext heap' store' ?_ hTop
  have e' := e.mono (live' := live) fun k h => by
    split
    · next hx =>
      have hne : k ≠ x.index := fun he => by rw [he, hx] at h; exact nomatch h
      simp [h, hne]
    · simp [h]
  exact ⟨e'.step, e'.frame.values.trans Frame.ofValues,
    e'.holds.agree Frame.ofValues⟩

/-- The size of an array variable: the load of its length word, then the release of the variable
when it is owned and dies there. -/
theorem spec_size (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e)) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.size (S := S) x) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt _ _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  obtain ⟨ptr, rfl, hB⟩ := hRep
  have hA := hB.borrow.values
  have hLength := hA.lengthBound
  have hPtr : s.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word hold
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  simp only [Expr.code, Var.sizeCode, Expr.usesFast_eq, List.append_assoc, List.cons_append,
    List.nil_append]
  simp only [wp_localGet_cons, hPtr, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode e.width_pos,
    words_div e.width_pos hnk]
  refine read_release hm x hVars hAt fun heap' store' ev hTop => ?_
  exact hNext heap' store' s [.i64 (env.get x).size.toUInt64]
    (After.ofScalar rfl ev.step rfl ev.frame ev.holds rfl)
    fun _ => top_unpaid_le rfl (by rw [hTop]; omega)

/-- A `let` binding: the value's code, the store of its words from local `base` on, the release
of the value when it is owned and the body does not use it, and the body's code. -/
theorem spec_letE (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy} {buy : Bool}
    (valueSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv value env
        slots paid live)
    (bodySpec : ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        body env slots paid live) :
    ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        (Expr.letE value body) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
  have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 1)) || value.uses i) = true →
      (live i || (Expr.letE value body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  -- The variables that die in the `let` die in the value or in the body.
  have hSplitL : dyingPot store s env slots paid
      (fun i => live i || (Expr.letE value body).uses i) live =
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 1) || value.uses i)
          (fun i => live i || body.uses (i + 1)) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 1)) live := by
    rw [dyingPot_split _ (fun i => live i || body.uses (i + 1)) _
      (fun i h => hV i (by simp [h])) (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      simp only [Expr.uses]
      cases live i <;> cases value.uses i <;> cases body.uses (i + 1) <;> rfl) fun _ => rfl
  refine valueSpec env slots paid (fun i => live i || body.uses (i + 1)) h (base + sTy.width) heap
    store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt (hSafe.mono hV) hCap (by omega) (by omega) hPlace.1 _
        _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by rw [hSplitL]; simp only [Expr.allocs]; omega))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.positions = h := a1.frame.positions.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (Nat.le_add_right _ _) fun i h => by simp [h]
  refine wp_storeCode ws1 h base sTy.types s1 s.values a1.rep.typed hh1 (by rw [hp1]; omega)
    (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold _ => ?_
  have f2 : Frame base s1 { s2 with values := s.values } := hF2.trans Frame.ofValues
  have hp2 : s2.params = s.params := hF2.params.trans hp1
  have hh2 : ({ s2 with values := s.values } : Locals).positions = h := f2.positions.trans hh1
  have hold' : LocalsHold { s2 with values := s.values } base sTy.types ws1 := hold
  -- The body's context: the value as variable 0, in the locals from `base` on.
  have hVarsB : Holds (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) (base + sTy.width) heap1 store1
      { s2 with values := s.values } :=
    Holds.push ((a1'.holds.agree f2).live_mono fun i h => by
        simpa using h)
      hold' a1.rep ((a1'.apart.agree a1'.holds f2).live_mono
        fun i h => by simpa using h)
  have hSafeB : pool.Safe (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) heap1 store1
      { s2 with values := s.values } :=
    (hSafe.mono hV).bind (hVars.live_mono hV) a1'
      (fun i hi => by simp [hi]) (fun i hi => by simpa using hi) f2 hold'
  have hRelease : (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
      releaseCode sTy base else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (sTy :: Γ') (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) := by
    cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;> simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letE value body).fits funs fits env = true → value.fits funs fits env = true :=
    fun hd => by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.1
  have hd3 : (Expr.letE value body).fits funs fits env = true →
      body.fits funs fits (.cons (value.denote funs env) env) = true := fun hd => by
    simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.2
  refine wp_releaseVars hm _ (by split <;> simp) hVarsB a1.step.at_ (by split <;> simp)
    fun heap2 store2 e2 hTop2 => ?_
  have e2' := e2.mono (live' := fun i => shift 1 live i || body.uses i) fun i h => by
    cases i with
    | zero =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | succ k => split <;> simpa using h
  -- The body's dying variables: the value's variable, whose potential is the value's when paid,
  -- and the others, whose potential the value's code and the release keep.
  have hDb : dyingPot store2 { s2 with values := s.values } (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) :: paid)
      (fun i => shift 1 live i || body.uses i) (shift 1 live) ≤
        (if value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) = true then
          sTy.pot store1 ws1 (value.denote funs env) else 0) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 1)) live := by
    rw [dyingPot_evolves hVarsB e2' (fun i h => by
      simp only [Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp [h]) _ _ fun _ h => h,
      dyingPot_cons]
    have hTail : dyingPot store1 { s2 with values := s.values } env slots paid
        (fun i => shift 1 live (i + 1) || body.uses (i + 1)) (fun i => shift 1 live (i + 1)) =
          dyingPot store s env slots paid (fun i => live i || body.uses (i + 1)) live := by
      rw [dyingPot_congr (L0' := fun i => live i || body.uses (i + 1)) (L1' := live)
        (fun i => by simp [shift]) (fun i => by simp [shift])]
      exact dyingPot_step (hVars.live_mono hV) a1'.step (a1'.frame.trans f2)
        (fun i h => by simp [h]) _ _ fun _ h => h
    rw [hTail, hold'.read_eq (by rw [a1.rep.length, Ty.types_length])]
    refine Nat.add_le_add_right ?_ _
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      simp only [hc.1.2, ↓reduceIte, le_refl]
    · exact Nat.zero_le _
  have hbuys : (Expr.letE value body).buysIn buy funs flags (slots.map Slot.mode) paid live env =
      body.buysIn buy funs flags ((⟨base, value.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
        (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) ::
          paid) (shift 1 live) (.cons (value.denote funs env) env) :=
    rfl
  refine bodySpec _ _
    (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) :: paid)
    (shift 1 live) h (base + sTy.width) heap2 store2
    { s2 with values := s.values } hh2 (hp2.trans hpv) e2'.holds e2'.step.at_
    (hSafeB.evolves hVarsB e2' (fun i hi => live_right _ _ _ hi))
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s2.params.length ≤ base + sTy.width; rw [hp2]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := value.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        have h1 := hTop1 (hd1 (fits_of_not hd)); have := congrArg UInt64.toNat hTop2
        dsimp only at h1
        refine hw.of_le ?_ (by rw [e2'.step.cap m, a1.step.cap m])
        rw [hSplitL, hbuys]
        simp only [Expr.allocs, List.map_cons]
        omega)
    fun heap3 store3 s3 ws3 aB hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  exact hNext heap3 store3 s3 ws3
    ((After.bind (hVars.live_mono hV) a1' f2 hold' aB' (fun i h => by simpa using h)
      (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV) fun hd => by
      have h1 := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      dsimp only at h1
      have hpot : (if (Expr.letE value body).paidIn buy flags (slots.map Slot.mode) paid live = true
            then tTy.pot store3 ws3 ((Expr.letE value body).denote funs env) else 0) =
          (if body.paidIn buy flags ((⟨base, value.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
              (value.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 1)) ::
                paid) (shift 1 live) = true then
            tTy.pot store3 ws3 (body.denote funs (.cons (value.denote funs env) env)) else 0) :=
        rfl
      rw [hpot, hbuys, hSplitL]
      simp only [Expr.allocs, List.map_cons] at h3 ⊢
      omega

/-- The regions of the first of two values in a row, which the second's code keeps. -/
theorem After.seq_regions {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base : Nat} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals} {t u : Ty} {m1 m2 : Mode}
    {v1 : t.denote} {v2 : u.denote} {ws1 ws2 vs : List Value}
    (a1 : After env slots L0 L1 base heap store s t m1 v1 heap1 store1 s1 ws1)
    (a2 : After env slots L1 live base heap1 store1 { s1 with values := vs } u m2 v2 heap2
      store2 s2 ws2) :
    t.regions m1 store2 ws1 v1 = t.regions m1 store1 ws1 v1 := by
  have hKeep1 : ∀ c ∈ t.regions m1 store1 ws1 v1,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vs } c := by
    intro c hc w x hx _ hm wx hwx hlx b hb
    have hb' : b ∈ w.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hm]; exact hb
    exact a1.apart w x hx (Or.inr hm) wx hwx hlx c hc b hb'
  exact (a1.rep.step a2.step hKeep1).2.1

/-- The bound of a pair from those of its components and their coercions: a paid pair's
potential is the sum of its components', each paid or 0. -/
theorem pair_top {T0 T1' T1 T2' T2 D1 D2 A1 C1 A2 C2 P1 P2 P1' P2' : Nat} {p1 p2 pp : Bool}
    (hF : T1' + (if p1 = true then P1' else 0) ≤ T0 + D1 + A1) (hC1 : T1 ≤ T1' + C1)
    (hS : T2' + (if p2 = true then P2' else 0) ≤ T1 + D2 + A2) (hC2 : T2 ≤ T2' + C2)
    (h1 : pp = true → (p1 = true ∧ P1 = P1') ∨ P1 = 0)
    (h2 : pp = true → (p2 = true ∧ P2 = P2') ∨ P2 = 0) :
    T2 + (if pp = true then P1 + P2 else 0) ≤ T0 + (D1 + D2) + (A1 + C1 + A2 + C2) := by
  cases pp with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega
  | true =>
    simp only [↓reduceIte]
    have e1 : P1 ≤ (if p1 = true then P1' else 0) := by
      rcases h1 rfl with ⟨hp1, rfl⟩ | h1
      · simp [hp1]
      · omega
    have e2 : P2 ≤ (if p2 = true then P2' else 0) := by
      rcases h2 rfl with ⟨hp2, rfl⟩ | h2
      · simp [hp2]
      · omega
    omega

/-- A binding of a pair's components: the pair's code, the stores of its components' words, the
release of each component that is owned and that the body does not use, and the body's code. -/
theorem spec_letPair (hm : Runtime m) {Γ' : List Ty} {sTy tTy uTy : Ty}
    {e : Expr S Γ' (.pair sTy tTy)} {body : Expr S (tTy :: sTy :: Γ') uTy} {buy : Bool}
    (eSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv e env slots paid live)
    (bodySpec : ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        body env slots paid live) :
    ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        (Expr.letPair e body) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hER : e.width ≤ max e.width body.width := Nat.le_max_left ..
  have hBR : body.width ≤ max e.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 2)) || e.uses i) = true →
      (live i || (Expr.letPair e body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  -- The variables that die in the binding die in the pair or in the body.
  have hSplitL : dyingPot store s env slots paid
      (fun i => live i || (Expr.letPair e body).uses i) live =
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 2) || e.uses i)
          (fun i => live i || body.uses (i + 2)) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 2)) live := by
    rw [dyingPot_split _ (fun i => live i || body.uses (i + 2)) _
      (fun i h => hV i (by simp [h])) (fun i h => by simp [h])]
    congr 1
    exact dyingPot_congr (fun i => by
      simp only [Expr.uses]
      cases live i <;> cases e.uses i <;> cases body.uses (i + 2) <;> rfl) fun _ => rfl
  refine eSpec env slots paid _ h
    (base + sTy.width + tTy.width) heap store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt (hSafe.mono hV)
        hCap
    (by omega) (by omega) hPlace.1
    _ _ (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by rw [hSplitL]; simp only [Expr.allocs]; omega))
    fun heap1 store1 s1 ws a1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.positions = h := a1.frame.positions.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (by omega) fun i h => by simp [h]
  obtain ⟨wf, wsec, rfl, hRf, hRs, hDisj⟩ := a1.rep
  have hlf := hRf.length
  have hls := hRs.length
  rw [List.reverse_append, List.append_assoc]
  refine wp_storeCode wsec h (base + sTy.width) tTy.types s1 (wf.reverse ++ s.values) hRs.typed
    hh1 (by rw [hp1]; omega) (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold2 _ => ?_
  have hh2 : s2.positions = h := hF2.positions.trans hh1
  refine wp_storeCode wf h base sTy.types s2 s.values hRf.typed hh2 (by rw [hF2.params, hp1]; omega)
    (by rw [Ty.types_length, hh2]; omega) fun s3 hF3 hold1 habove3 => ?_
  have hold1' : LocalsHold { s3 with values := s.values } base sTy.types wf := hold1
  have hold2' : LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types wsec :=
    hold2.keep hF3.positions habove3 (by rw [Ty.types_length]) (by rw [hls, hh2]; omega)
  have f3 : Frame base s1 { s3 with values := s.values } :=
    (hF2.mono (by omega)).trans (hF3.trans Frame.ofValues)
  have hp3 : s3.params = s.params := hF3.params.trans (hF2.params.trans hp1)
  -- The body's context: the second component as variable 0 and the first as variable 1.
  have hVars1 := (a1'.holds.agree f3)
  have hApart := a1'.apart.agree a1'.holds f3
  have hVarsB : Holds (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || shift 2 live i || body.uses i)
      (base + sTy.width + tTy.width) heap1 store1 { s3 with values := s.values } := by
    refine Holds.push (Holds.push (hVars1.live_mono fun i h => by simpa using h) hold1' hRf
      ((hApart.fst hlf).live_mono fun i h => by simpa using h)) hold2' hRs ?_
    refine Holds.Apart.push ((hApart.snd hlf).live_mono fun i h => by simpa using h) hold1' hlf
      fun hmo b hb c hc => ?_
    have hmo' : e.mode (slots.map Slot.mode) = .owned := by simpa using hmo
    rw [hmo'] at hb hc hDisj
    exact regionsDisjoint_symm (hDisj rfl c hc b hb)
  have hSafeB : pool.Safe
      (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || shift 2 live i || body.uses i)
      heap1 store1 { s3 with values := s.values } :=
    (hSafe.mono hV).bind2 (hVars.live_mono hV) a1'
      (fun i hi => by simp [hi]) (fun i hi => by simpa [shift] using hi)
      f3 hRf hRs hold1' hold2'
  have hRelease : ∀ rest' : Program,
      (if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 1 = false then
        releaseCode sTy base else []) ++
      ((if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
        releaseCode tTy (base + sTy.width) else []) ++ rest') =
      ((if body.uses 1 = false then [1] else []) ++
        (if body.uses 0 = false then [0] else [])).flatMap
        (releaseVar (tTy :: sTy :: Γ') (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
          ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)) ++ rest' := by
    intro rest'
    cases body.uses 1 <;> cases body.uses 0 <;> cases e.mode (slots.map Slot.mode) <;>
      simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letPair e body).fits funs fits env = true → e.fits funs fits env = true :=
    fun hd => by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.1
  have hd3 : (Expr.letPair e body).fits funs fits env = true →
      body.fits funs fits (.cons (e.denote funs env).2 (.cons (e.denote funs env).1 env)) = true :=
    fun hd => by simp only [Expr.fits, Bool.and_eq_true] at hd; exact hd.2
  refine wp_releaseVars hm _ (by split <;> split <;> simp) hVarsB a1.step.at_
    (by split <;> split <;> simp) fun heap2 store2 e2 hTop2 => ?_
  have e2' := e2.mono (live' := fun i => shift 2 live i || body.uses i) fun i h => by
    match i with
    | 0 =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | 1 =>
      have h1 : body.uses 1 = true := by simpa [shift] using h
      simp [h1]
    | k + 2 => split <;> split <;> simpa using h
  -- The body's dying variables: the components, paid when the pair is, whose potential is the
  -- pair's, and the others, whose potential the pair's code and the releases keep.
  have hPotE : (Ty.pair sTy tTy).pot store1 (wf ++ wsec) (e.denote funs env) =
      sTy.pot store1 wf (e.denote funs env).1 + tTy.pot store1 wsec (e.denote funs env).2 := by
    simp only [Ty.pot, List.take_left' hlf, List.drop_left' hlf]
  have hDb : dyingPot store2 { s3 with values := s.values }
      (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
        e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) :: paid)
      (fun i => shift 2 live i || body.uses i) (shift 2 live) ≤
        (if e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
          then (Ty.pair sTy tTy).pot store1 (wf ++ wsec) (e.denote funs env) else 0) +
        dyingPot store s env slots paid (fun i => live i || body.uses (i + 2)) live := by
    rw [dyingPot_evolves hVarsB e2' (fun i h => by
      simp only [Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp [h]) _ _ fun _ h => h,
      dyingPot_cons, dyingPot_cons]
    rw [dyingPot_congr (L0' := fun i => live i || body.uses (i + 2)) (L1' := live)
      (fun i => by simp [shift]) (fun i => by simp [shift])]
    rw [dyingPot_step (hVars.live_mono hV) a1'.step (a1'.frame.trans f3)
      (fun i h => by simp [h]) _ _ fun _ h => h]
    dsimp only
    rw [hold2'.read_eq (by rw [hls, Ty.types_length]), hold1'.read_eq (by rw [hlf, Ty.types_length]),
      hPotE]
    by_cases hpp : e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
    · rw [ite_eq_left hpp]
      split <;> split <;> omega
    · simp only [hpp, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hbuys : (Expr.letPair e body).buysIn buy funs flags (slots.map Slot.mode) paid live env =
      body.buysIn buy funs flags ((⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
          ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
        (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
          e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
            paid) (shift 2 live)
        (.cons (e.denote funs env).2 (.cons (e.denote funs env).1 env)) :=
    rfl
  refine bodySpec _ _
    (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
      e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) :: paid)
    (shift 2 live) h (base + sTy.width + tTy.width)
    heap2 store2
    { s3 with values := s.values } (f3.positions.trans hh1) (hp3.trans hpv) e2'.holds e2'.step.at_
    (hSafeB.evolves hVarsB e2' (fun i hi => live_right _ _ _ hi))
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := e.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body2 _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        have h1 := hTop1 (hd1 (fits_of_not hd)); have := congrArg UInt64.toNat hTop2
        have hDb' := hDb
        refine hw.of_le ?_ (by rw [e2'.step.cap m, a1.step.cap m])
        rw [hSplitL, hbuys]
        simp only [Expr.allocs, List.map_cons]
        by_cases hpp :
            e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
        · rw [ite_eq_left hpp] at h1 hDb'; omega
        · rw [ite_eq_right hpp] at h1 hDb'; omega)
    fun heap3 store3 s4 ws4 aB hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  have hNew : ∀ r, (∀ b ∈ (e.mode (slots.map Slot.mode)).fresh store1 (.pair sTy tTy) (wf ++ wsec)
      (e.denote funs env), regionsDisjoint r b) →
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types w →
        w.length = tTy.width →
        ∀ b ∈ tTy.blocks store1 w (e.denote funs env).2, regionsDisjoint r b) ∧
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } base sTy.types w → w.length = sTy.width →
        ∀ b ∈ sTy.blocks store1 w (e.denote funs env).1, regionsDisjoint r b) := by
    intro r hFresh
    rw [Mode.fresh_pair hlf] at hFresh
    refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo w hw hlw b hb => ?_⟩
    · obtain rfl := LocalsHold.unique hw hold2' (hlw.trans hls.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_right _ hb)
    · obtain rfl := LocalsHold.unique hw hold1' (hlw.trans hlf.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_left _ hb)
  exact hNext heap3 store3 s4 ws4
    ((After.bind2 (hVars.live_mono hV) a1' f3 aB' (by omega) hNew
      (fun i h => by simpa using h) (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV)
    fun hd => by
      have h1 := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      have hDb' := hDb
      have hpot : (if (Expr.letPair e body).paidIn buy flags (slots.map Slot.mode) paid live = true
            then uTy.pot store3 ws4 ((Expr.letPair e body).denote funs env) else 0) =
          (if body.paidIn buy flags ((⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
              ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots).map Slot.mode)
              (e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
                e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) ::
                  paid) (shift 2 live) = true then
            uTy.pot store3 ws4 (body.denote funs
              (.cons (e.denote funs env).2 (.cons (e.denote funs env).1 env))) else 0) :=
        rfl
      rw [hpot, hbuys, hSplitL]
      simp only [List.map_cons] at h3 ⊢
      simp only [Expr.allocs]
      by_cases hpp :
          e.paid flags (slots.map Slot.mode) paid (fun i => live i || body.uses (i + 2)) = true
      · rw [ite_eq_left hpp] at h1 hDb'; omega
      · rw [ite_eq_right hpp] at h1 hDb'; omega

/-- A paid loop state is held in owned mode. -/
theorem Expr.statePaid_mode {Γ : List Ty} {t : Ty} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t} {cond : Expr S (t :: Γ) .bool}
    {body : Expr S (t :: .word :: Γ) t} (h : Expr.statePaid flags modes paid live init cond body = true) :
    (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)) = .owned := by
  simp only [Expr.statePaid, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- The body of a loop whose state is paid gives a value paid as `Expr.bodyPaid` states. -/
theorem Expr.statePaid_body {Γ : List Ty} {t : Ty} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t} {cond : Expr S (t :: Γ) .bool}
    {body : Expr S (t :: .word :: Γ) t} (h : Expr.statePaid flags modes paid live init cond body = true) :
    body.paidIn (Expr.statePaid flags modes paid live init cond body) flags
      (((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))) ::
        .borrowed :: modes) (Expr.statePaid flags modes paid live init cond body :: false :: paid)
      (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) = true := by
  rw [h]
  simp only [Expr.statePaid, Bool.and_eq_true] at h
  simpa only [Expr.paidIn, ↓reduceIte] using h.2

/-- In a loop's body, no paid variable dies other than the state: the index is unpaid, and the outer
variables that the body uses stay live. -/
theorem loop_body_dies {live c b : Nat → Bool} {paid : List Bool} :
    ∀ i, (fun j => shift 2 (fun i => live i || c (i + 1) || b (i + 2)) j || b j) (i + 1) = true →
      (shift 2 fun i => live i || c (i + 1) || b (i + 2)) (i + 1) = false →
      paidAt (false :: paid) i = false
  | 0, _, _ => rfl
  | k + 1, h0, h1 => by
    have hk : ¬ k + 1 + 1 < 2 := by omega
    have hs : k + 1 + 1 - 2 = k := by omega
    have hb : b (k + 1 + 1) = b (k + 2) := rfl
    simp only [shift, hk, hs, ↓reduceIte, hb] at h0 h1
    revert h0 h1
    cases live k <;> cases c (k + 1) <;> cases b (k + 2) <;> simp

/-- The potential of a loop's first state: that of a paid initial value, which the coercion keeps,
or the credit. -/
theorem loop_entry_pot {ps ip : Bool} {P0 P1 C : Nat} (h1 : ps = true → ip = true → P1 = P0)
    (h2 : ps = true → ip = false → P1 ≤ C) :
    (if ps = true then P1 else 0) ≤
      (if ip = true then P0 else 0) + (if (ps && !ip) = true then C else 0) := by
  cases ps <;> cases ip <;> simp_all

/-- A pass of a loop: the body's bound with the state's potential among its dying variables, and
the coercion of its value, which keeps a paid value's potential. -/
theorem loop_body_pot {ps bp : Bool} {top6 top6' top2 D B Y K P6 P6' Pi : Nat}
    (hbp : ps = true → bp = true) (hsame : ps = true → P6' = P6)
    (hB : top6 + (if bp = true then P6 else 0) ≤ top2 + D + B + Y)
    (hD : D ≤ (if ps = true then Pi else 0)) (hK : top6' ≤ top6 + K) :
    top6' + (if ps = true then P6' else 0) ≤ top2 + (if ps = true then Pi else 0) + B + K + Y := by
  cases ps
  · simp only [Bool.false_eq_true, ↓reduceIte] at hD ⊢
    split at hB <;> omega
  · obtain rfl := hbp rfl
    rw [hsame rfl]
    simp only [↓reduceIte] at hB hD ⊢
    omega

/-- The body of a loop at the state's flag `ps`, which holds only when the state is paid, gives a
value paid as `Expr.bodyPaid` states. -/
theorem Expr.statePaid_body_of {Γ : List Ty} {t : Ty} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t} {cond : Expr S (t :: Γ) .bool}
    {body : Expr S (t :: .word :: Γ) t} {ps : Bool}
    (hpsS : ps = true → Expr.statePaid flags modes paid live init cond body = true)
    (h : ps = true) :
    body.paidIn ps flags (((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))) ::
        .borrowed :: modes) (ps :: false :: paid)
      (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) = true := by
  subst h
  have h2 := Expr.statePaid_body (hpsS rfl)
  rwa [hpsS rfl] at h2

/-- A request of at least 8 and at most `8 * k` bytes, within `2 ^ 32`, takes at most `8 * k`
bytes. -/
theorem allocSize_le_mul {bytes : UInt64} {k : Nat} (h8 : 8 ≤ bytes.toNat)
    (hb : bytes.toNat ≤ 4294967296) (h : bytes.toNat ≤ 8 * k) :
    (allocSize bytes).toNat ≤ 8 * k := by
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · simp only [UInt64.reduceToNat]; omega
  · rw [hRound]; omega

/-- `Var.roomCost` of an array that is copied: a copy at the new length. -/
theorem Var.roomCost_copy {Γ : List Ty} {e : Elem} (x : Var Γ (.array e)) {modes : List Mode}
    (paid : List Bool) {live : Nat → Bool} (xs : Array e.denote) (ext : Nat)
    (h : ¬(modeAt modes x.index = .owned ∧ live x.index = false)) :
    x.roomCost modes paid live xs ext = allocCost ((xs.size * e.width + ext + 1) * 8) := by
  simp only [Var.roomCost, ite_eq_right h]

/-- `Var.roomCost` of an owned array that dies: for a paid one, a header and four times the added
bytes, and for an unpaid one, a block of twice the new length's bytes and twice the added bytes. -/
theorem Var.roomCost_move {Γ : List Ty} {e : Elem} (x : Var Γ (.array e)) {modes : List Mode}
    (paid : List Bool) {live : Nat → Bool} (xs : Array e.denote) (ext : Nat)
    (h : modeAt modes x.index = .owned ∧ live x.index = false) :
    x.roomCost modes paid live xs ext =
      if paidAt paid x.index then allocCost (32 * ext)
      else allocCost (16 * (xs.size * e.width + ext + 1)) + 16 * ext := by
  simp only [Var.roomCost, ite_eq_left h]

/-! The arithmetic of a growth with the potential `4u ∸ 2c`, for an array of `n` words in a block
of capacity `c` that grows to `t` words.  A move requests `r`, twice the capacity or the new
length's bytes, which the allocator rounds to `A`, a multiple of 8. -/

theorem room_inplace_paid {n t c : Nat} (hnt : n ≤ t) :
    4 * (8 * (t + 1)) - 2 * c ≤ (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) := by omega

theorem room_inplace_unpaid {n t c : Nat} (hc : 8 * (n + 1) ≤ c) (hnt : n ≤ t) :
    4 * (8 * (t + 1)) - 2 * c ≤ 48 + 16 * (t + 1) + 16 * (t - n) := by omega

theorem room_alloc_paid {n t c r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A) (hAr7 : A ≤ r + 7)
    (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1))) :
    48 + A ≤ (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem room_alloc_unpaid {n t c r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A) (hAr7 : A ≤ r + 7)
    (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1))) :
    48 + A ≤ 48 + 16 * (t + 1) + 16 * (t - n) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem room_move_paid {top top' n t c c' r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A)
    (hAr7 : A ≤ r + 7) (hc : 8 * (n + 1) ≤ c) (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1)))
    (hshape : (top' = top ∧ r ≤ c') ∨ (top' = top + 48 + A ∧ c' = A)) :
    top' + (4 * (8 * (t + 1)) - 2 * c') ≤
      top + (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases hshape with ⟨rfl, h'⟩ | ⟨rfl, rfl⟩ <;> omega

theorem room_move_unpaid {top top' n t c c' r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A)
    (hAr7 : A ≤ r + 7) (hc : 8 * (n + 1) ≤ c) (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1)))
    (hshape : (top' = top ∧ r ≤ c') ∨ (top' = top + 48 + A ∧ c' = A)) :
    top' + (4 * (8 * (t + 1)) - 2 * c') ≤ top + (48 + 16 * (t + 1) + 16 * (t - n)) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases hshape with ⟨rfl, h'⟩ | ⟨rfl, rfl⟩ <;> omega

/-- A block of more than `2 ^ 31` bytes below `top` leaves no room for either charge. -/
theorem room_huge {top n t c : Nat} (hroom : c < 8 * (t + 1)) (hnt : 8 * (n + 1) ≤ c)
    (hc : 4294967296 < 2 * c) (htop : c ≤ top) :
    4294901760 < top + (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) ∧
      4294901760 < top + (48 + 16 * (t + 1) + 16 * (t - n)) := by
  omega

/-- A new length of `2 ^ 29` words or more leaves no room for any charge. -/
theorem room_long {n t c : Nat} (ht : 536870912 ≤ t) (hnt : n ≤ t) (hc : c < 4294967296) :
    4294901760 < (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) ∧
      4294901760 < 48 + 16 * (t + 1) + 16 * (t - n) ∧ 4294901760 < 48 + (t + 1) * 8 := by
  omega

/-- The rounded byte count of an allocation is a multiple of 8 within 7 of the request. -/
theorem allocSize_round {bytes : UInt64} (h : bytes.toNat ≤ 4294967296) (h8 : 8 ≤ bytes.toNat) :
    (allocSize bytes).toNat % 8 = 0 ∧ bytes.toNat ≤ (allocSize bytes).toNat ∧
      (allocSize bytes).toNat ≤ bytes.toNat + 7 := by
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · rename_i hs
    rw [UInt64.lt_iff_toNat_lt, hRound] at hs
    simp only [UInt64.reduceToNat] at hs
    omega
  · rw [hRound]; omega

end Cases

/-- A run that may trap as `a` allows may trap as any `a'` that `a` implies. -/
theorem _root_.Wasm.Runs.of_imp {α : Type} {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {P : Store α → List Value → Prop} {a a' : Bool}
    (h : Runs a env m id initial args P) (himp : a = true → a' = true) :
    Runs a' env m id initial args P := by
  cases a
  · exact h.weaken
  · rw [himp rfl]; exact h

/-- The frames at the next depth: one fewer, below the limit. -/
theorem framesAt_succ {d : UInt64} (h : d < depthLimit) : framesAt d = framesAt (d + 1) + 1 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  simp only [depthLimit, UInt64.reduceToNat] at this
  have hd1 : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  simp only [framesAt, depthLimit, UInt64.reduceToNat, hd1]; omega

theorem framesAt_eq_zero {d : UInt64} (h : ¬d < depthLimit) : framesAt d = 0 := by
  have := UInt64.not_lt.mp h
  have := UInt64.le_iff_toNat_le.mp this
  simp only [depthLimit, UInt64.reduceToNat] at this
  simp only [framesAt, depthLimit, UInt64.reduceToNat]; omega

end Verified
