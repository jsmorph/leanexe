import LeanExe.Native.Proof.Constructs

/-!
The simulation of `block`, `iff`, and `loop`.
-/

namespace LeanExe.Native

open Wasm LClight LeanExe.ProofKit

theorem execOne_zero {α : Type} (m : Module) (st : Store α) (sl : Locals) (env : HostEnv α)
    (inst : Instruction) : execOne 0 m st sl inst env = .OutOfFuel := by
  simp only [execOne.eq_def]

/-- Talos's result for a `block` or `iff` from its body's `r`, with `ra` kept values over
`below`. -/
def blockResult {α : Type} (ra : Nat) (below : List Value) : Continuation α → Continuation α
  | .Fallthrough r' s' =>
      .Fallthrough r' { params := s'.params, locals := s'.locals, values := s'.values.take ra ++ below }
  | .Break 0 r' s' =>
      .Fallthrough r' { params := s'.params, locals := s'.locals, values := s'.values.take ra ++ below }
  | .Break (k + 1) r' s' => .Break k r' s'
  | other => other

theorem execOne_block {α : Type} (m : Module) (st : Store α) (sl : Locals) (env : HostEnv α)
    (f pa ra : Nat) (body : Program) (pts rts : List ValueType) :
    execOne (f + 1) m st sl (.block pa ra body pts rts) env =
      blockResult ra (sl.values.drop pa) (exec f m st sl body env) := by
  simp only [execOne.eq_def]
  cases exec f m st sl body env with
  | Break k r' s' => cases k <;> rfl
  | _ => rfl

theorem execOne_iff {α : Type} (m : Module) (st : Store α) (sl : Locals) (env : HostEnv α)
    (f pa ra : Nat) (thn els : Program) (pts rts : List ValueType) (x : UInt32) (vs : List Value)
    (hvs : sl.values = .i32 x :: vs) :
    execOne (f + 1) m st sl (.iff pa ra thn els pts rts) env =
      blockResult ra (vs.drop pa)
        (exec f m st { params := sl.params, locals := sl.locals, values := vs }
          (if x ≠ 0 then thn else els) env) := by
  simp only [execOne.eq_def, hvs]
  cases exec f m st { params := sl.params, locals := sl.locals, values := vs }
      (if x ≠ 0 then thn else els) env with
  | Break k r' s' => cases k <;> rfl
  | _ => rfl

theorem blockTypeOk_inv {pa ra : Nat} {pts rts : List ValueType} {r : Option VT}
    (h : blockTypeOk pa ra pts rts = true) (hr : (rts.head?).mapM VT.ofValueType = some r) :
    pa = 0 ∧ ra = r.toList.length := by
  simp only [blockTypeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hpa, -⟩, hra⟩, hlen⟩, -⟩ := h
  refine ⟨hpa, ?_⟩
  match rts, hlen, hr with
  | [], hlen, hr => simp at hr; subst hr; simp at hlen; simp [hlen]
  | [vt], hlen, hr =>
      simp [Option.mapM] at hr
      obtain ⟨t, -, rfl⟩ := hr
      simp at hlen; simp [hlen]
  | _ :: _ :: _, hlen, _ => simp at hlen; omega

theorem callees_seq_break (s0 : statement) : callees (seq s0 .Sbreak) = callees s0 := by
  cases s0 <;> simp [seq, callees]

theorem callees_wrap (s0 d : statement) {k : ident} (h : k ∈ callees s0) :
    k ∈ callees (.Ssequence (wrapLoop s0) d) := by
  have : callees (.Ssequence (wrapLoop s0) d) = callees s0 ++ callees d := by
    simp [wrapLoop, callees, callees_seq_break]
  rw [this]
  exact List.mem_append_left _ h

theorem LabelsOk.push {L : List Label} (hL : LabelsOk L) {b : Nat} (hb : curBase L ≤ b)
    (isLoop : Bool) (r : Option VT) : LabelsOk ({ isLoop, base := b, result := r } :: L) := by
  intro k l hl
  cases k with
  | zero => simp at hl; subst hl; exact Nat.le_refl _
  | succ k => simp at hl; exact Nat.le_trans (hL k l hl) hb

theorem stack_after {le le' : temp_env} {r : Option VT} {σb : List VT} {vs below : List Value}
    (hs : (r.isSome → ∃ v, vs.head? = some v ∧ ∀ t, r = some t →
        t.has v = true ∧ le'[slotId σb.length t]? = some (cval v)))
    (hbelow : StackRel le σb below) (hf : Frame σb.length le le') :
    StackRel le' (r.toList ++ σb) (vs.take r.toList.length ++ below) := by
  cases r with
  | none => exact hbelow.frame hf
  | some t =>
      obtain ⟨v, hv, hvt⟩ := hs rfl
      obtain ⟨ht, hl⟩ := hvt t rfl
      cases vs with
      | nil => simp at hv
      | cons w ws =>
          simp at hv; subst hv
          exact ⟨ht, hl, hbelow.frame hf⟩

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- A `block` or `iff` construct's loop from its body's outcome. -/
theorem construct_of_body {L : List Label} {σb : List VT} {r : Option VT} {α : Type}
    {rb : Continuation α} {s0 : statement} {le : temp_env} {m : mem} {below : List Value}
    (hbase : curBase L ≤ σb.length) (hbelow : StackRel le σb below)
    (h : Outcome A X E c ({ isLoop := false, base := σb.length, result := r } :: L)
      (some (r.toList ++ σb)) rb s0 le m) :
    ConstructOutcome A X E c L (r.toList ++ σb) (blockResult r.toList.length below rb)
      (wrapLoop s0) le m := by
  cases rb with
  | Fallthrough st' sl' =>
      obtain ⟨σ'', hσ, -, t, le', m', hx, hinv, hf⟩ := h
      cases hσ
      obtain ⟨t', hW⟩ := exec_wrap_exit hx (.inl rfl)
      refine ⟨by simp; omega, t', le', m', hW, ?_, hf.mono hbase⟩
      refine { stack := stack_after ?_ hbelow hf, locals := hinv.locals, store := hinv.store,
               status := hinv.status, brk := hinv.brk, lim := hinv.lim }
      intro hr
      cases r with
      | none => simp at hr
      | some t =>
          obtain ⟨v, vr, hv, ht, hl, -⟩ := hinv.stack.cons_inv
          exact ⟨v, by rw [hv]; rfl, fun t' e => by cases e; exact ⟨ht, hl⟩⟩
  | Break k st' sl' =>
      obtain ⟨t, le', m', out, hx, hrel, hf⟩ := h
      cases k with
      | zero =>
          obtain ⟨l, hl, h0, -, hkept⟩ := hrel.target
          simp at hl; subst hl
          have hout : out = .Out_break := by simpa using h0 rfl
          subst hout
          obtain ⟨t', hW⟩ := exec_wrap_exit hx (.inr rfl)
          have hf0 := hf _ rfl
          refine ⟨by simp; omega, t', le', m', hW, ?_, hf0.mono hbase⟩
          refine { stack := stack_after ?_ hbelow hf0, locals := hrel.locals, store := hrel.store,
                   status := hrel.status, brk := hrel.brk, lim := hrel.lim }
          intro hr
          cases r with
          | none => simp at hr
          | some t0 =>
              obtain ⟨v, hv, ht, hs⟩ := hkept rfl t0 rfl
              exact ⟨v, hv, fun t' e => by cases e; exact ⟨ht, hs⟩⟩
      | succ k =>
          have hout := hrel.outer (by omega)
          subst hout
          obtain ⟨t', hW⟩ := exec_wrap_exit hx (.inr rfl)
          obtain ⟨l, hl, -, hfin, hkept⟩ := hrel.target
          simp at hl
          refine ⟨t', le', m', hW, ?_, fun l' hl' => hf l' (by simpa using hl')⟩
          exact { target := ⟨l, hl, hfin, hkept⟩, brk := hrel.brk, small := hrel.small,
                  locals := hrel.locals, store := hrel.store, status := hrel.status, lim := hrel.lim }
  | Return st' vs =>
      obtain ⟨t, le', m', out, hx, hrel, hg, hs⟩ := h
      obtain ⟨rv, rfl⟩ := ReturnRel.isReturn hrel
      exact ⟨_, le', m', _, exec_wrap_return hx, hrel, hg, hs⟩
  | Trap st' msg =>
      obtain ⟨t, le', m', hx, hg, hs, hc⟩ := h
      have : ∃ rv, trapOut c.result = .Out_return rv := by
        cases c.result <;> exact ⟨_, rfl⟩
      obtain ⟨rv, e⟩ := this
      refine ⟨E0 ++ t, le', m', ?_, hg, hs, hc⟩
      rw [e] at hx ⊢
      exact exec_wrap_return hx
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h
  | Throwing _ _ _ _ => exact h

theorem sim_block {CallOk : Nat → Prop} {f : Nat} (hP : ProgSim A X E mod c CallOk f)
    (pa ra : Nat) (body : Program) (pts rts : List ValueType) :
    InstrSimL A X E mod c CallOk (f + 1) (.block pa ra body pts rts) := by
  intro L σ n s σ' n' htr hbase hL hcalls α st sl le m env hal hinv
  simp [trInstr, Option.bind_eq_some_iff] at htr
  obtain ⟨hbt, r, hr, parent, hp, s0, n1, hbody, rfl, rfl, rfl⟩ := htr
  obtain ⟨rfl, rfl⟩ := blockTypeOk_inv hbt hr
  rw [execOne_block]
  apply ConstructOutcome.toOutcome hp
  have ho := hP ({ isLoop := false, base := σ.length, result := r } :: L) σ (r.toList ++ σ) n body
    s0 n1 hbody (Nat.le_refl _) (hL.push hbase false r)
    (fun k hk => hcalls k (callees_wrap _ _ hk)) st sl le m env
    (fun hc => by have h1 := hal hc; simp only [AlignedOne] at h1; exact h1) hinv
  exact construct_of_body hbase hinv.stack ho

/-- The C conditional picks the branch that Talos picks. -/
theorem Outcome.ite {L : List Label} {σ' : Option (List VT)} {α : Type} {r : Continuation α}
    {cond : expr} {s1 s2 : statement} {le : temp_env} {m : mem} {x : UInt32}
    (hc : eval_expr A E.ge empty_env le m cond (.Vint x)) (hty : typeof cond = tuint)
    (h : Outcome A X E c L σ' r (if x ≠ 0 then s1 else s2) le m) :
    Outcome A X E c L σ' r (.Sifthenelse cond s1 s2) le m := by
  have hb : bool_val (.Vint x) (typeof cond) m = some (decide (x ≠ 0)) := by
    rw [hty]; exact bool_uint m x
  have lift : ∀ {t le' m' out}, exec_stmt A X E.ge empty_env le m (if x ≠ 0 then s1 else s2)
      t le' m' out → exec_stmt A X E.ge empty_env le m (.Sifthenelse cond s1 s2) t le' m' out := by
    intro t le' m' out hx
    by_cases hx0 : x ≠ 0
    · rw [ite_eq_left hx0] at hx
      exact .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc (by rw [hb]; simp [hx0]) hx
    · rw [ite_eq_right hx0] at hx
      exact .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc (by rw [hb]; simp [hx0]) hx
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ'', h', hb', t, le', m', hx, hinv, hf⟩ := h
      exact ⟨σ'', h', hb', t, le', m', lift hx, hinv, hf⟩
  | Break k st' sl' =>
      obtain ⟨t, le', m', out, hx, hrel, hf⟩ := h
      exact ⟨t, le', m', out, lift hx, hrel, hf⟩
  | Return st' vs =>
      obtain ⟨t, le', m', out, hx, hrel, hg, hs⟩ := h
      exact ⟨t, le', m', out, lift hx, hrel, hg, hs⟩
  | Trap st' msg =>
      obtain ⟨t, le', m', hx, hg, hs, hc'⟩ := h
      exact ⟨t, le', m', lift hx, hg, hs, hc'⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h
  | Throwing _ _ _ _ => exact h

theorem callees_wrap_ite (cond : expr) (s1 s2 d : statement) {k : ident}
    (h : k ∈ callees s1 ∨ k ∈ callees s2) :
    k ∈ callees (.Ssequence (wrapLoop (.Sifthenelse cond s1 s2)) d) :=
  callees_wrap _ _ (by simp only [callees, List.mem_append]; exact h)

theorem sim_iff {CallOk : Nat → Prop} {f : Nat} (hP : ProgSim A X E mod c CallOk f)
    (pa ra : Nat) (thn els : Program) (pts rts : List ValueType) :
    InstrSimL A X E mod c CallOk (f + 1) (.iff pa ra thn els pts rts) := by
  intro L σ n s σ' n' htr hbase hL hcalls α st sl le m env hal hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at htr
  obtain ⟨hbt, r, hr, parent, hp, _, ⟨hb, rfl⟩, rfl, s1, n1, h1, s2, n2, h2, rfl, rfl, rfl⟩ := htr
  obtain ⟨rfl, rfl⟩ := blockTypeOk_inv hbt hr
  obtain ⟨x, vs, hvs, hx, hrest⟩ := pop1_i32 hinv.stack
  have halB : c.alignedAccess = true →
      AlignedExec f mod st { sl with values := vs } (if x ≠ 0 then thn else els) env := fun hc => by
    have h1 := hal hc
    simp only [AlignedOne, hvs] at h1
    exact h1
  rw [execOne_iff _ _ _ _ _ _ _ _ _ _ _ x vs hvs]
  apply ConstructOutcome.toOutcome hp
  have hinv' : Inv E c σr st { params := sl.params, locals := sl.locals, values := vs } le m :=
    { stack := hrest, locals := hinv.locals, store := hinv.store, status := hinv.status,
      brk := hinv.brk, lim := hinv.lim }
  apply construct_of_body hb hrest
  refine Outcome.ite (.eval_Etempvar _ _ _ hx) rfl ?_
  by_cases hx0 : x ≠ 0
  · rw [ite_eq_left hx0, ite_eq_left hx0]
    exact hP ({ isLoop := false, base := σr.length, result := r } :: L) σr (r.toList ++ σr) n thn
      s1 n1 h1 (Nat.le_refl _) (hL.push hb false r)
      (fun k hk => hcalls k (callees_wrap_ite _ _ _ _ (.inl hk))) st _ le m env
      (fun hc => by have h1 := halB hc; rwa [ite_eq_left hx0] at h1) hinv'
  · rw [ite_eq_right hx0, ite_eq_right hx0]
    exact hP ({ isLoop := false, base := σr.length, result := r } :: L) σr (r.toList ++ σr) n1 els
      s2 n2 h2 (Nat.le_refl _) (hL.push hb false r)
      (fun k hk => hcalls k (callees_wrap_ite _ _ _ _ (.inr hk))) st _ le m env
      (fun hc => by have h1 := halB hc; rwa [ite_eq_right hx0] at h1) hinv'

/-- A loop that runs its body once more after the body continued. -/
theorem ConstructOutcome.again {L : List Label} {σ : List VT} {σ' : List VT} (hL : LabelsOk L)
    (hbase : curBase L ≤ σ.length) {α : Type} {r : Continuation α} {s0 : statement}
    {le le' : temp_env} {m m' : mem} {t1 : trace}
    (h1 : exec_stmt A X E.ge empty_env le m s0 t1 le' m' .Out_continue)
    (hf : Frame σ.length le le')
    (h : ConstructOutcome A X E c L σ' r (wrapLoop s0) le' m') :
    ConstructOutcome A X E c L σ' r (wrapLoop s0) le m := by
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨hb, t, le'', m'', hx, hinv, hf2⟩ := h
      obtain ⟨t', hW⟩ := exec_wrap_continue h1 hx
      exact ⟨hb, t', le'', m'', hW, hinv, (hf.mono hbase).trans hf2⟩
  | Break k st' sl' =>
      obtain ⟨t, le'', m'', hx, hpb, hf2⟩ := h
      obtain ⟨t', hW⟩ := exec_wrap_continue h1 hx
      exact ⟨t', le'', m'', hW, hpb, fun l hl =>
        (hf.mono (Nat.le_trans (hL k l hl) hbase)).trans (hf2 l hl)⟩
  | Return st' vs =>
      obtain ⟨t, le'', m'', out, hx, hrel, hg, hs⟩ := h
      obtain ⟨t', hW⟩ := exec_wrap_continue h1 hx
      exact ⟨t', le'', m'', out, hW, hrel, hg, hs⟩
  | Trap st' msg =>
      obtain ⟨t, le'', m'', hx, hg, hs, hc⟩ := h
      obtain ⟨t', hW⟩ := exec_wrap_continue h1 hx
      exact ⟨t', le'', m'', hW, hg, hs, hc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h
  | Throwing _ _ _ _ => exact h

theorem sim_loop {CallOk : Nat → Prop} {F : Nat} (hP : ∀ g, g < F → ProgSim A X E mod c CallOk g)
    (pa ra : Nat) (body : Program) (pts rts : List ValueType) :
    InstrSimL A X E mod c CallOk F (.loop pa ra body pts rts) := by
  intro L σ n s σ' n' htr hbase hL hcalls α st sl le m env hal hinv
  simp [trInstr, Option.bind_eq_some_iff] at htr
  obtain ⟨hbt, r, hr, parent, hp, s0, n1, hbody, rfl, rfl, rfl⟩ := htr
  obtain ⟨rfl, rfl⟩ := blockTypeOk_inv hbt hr
  apply ConstructOutcome.toOutcome hp
  let L' : List Label := { isLoop := true, base := σ.length, result := none } :: L
  have hL' : LabelsOk L' := hL.push hbase true none
  have hc' : ∀ k, funId k ∈ callees s0 → CallOk k := fun k hk => hcalls k (callees_wrap _ _ hk)
  suffices key : ∀ g, g ≤ F → ∀ (st : Store α) (sl : Locals) (le : temp_env) (m : mem),
      (c.alignedAccess = true → AlignedOne g mod st sl (.loop 0 r.toList.length body pts rts) env) →
      Inv E c σ st sl le m →
      ConstructOutcome A X E c L (r.toList ++ σ)
        (execOne g mod st sl (.loop 0 r.toList.length body pts rts) env) (wrapLoop s0) le m from
    key F (Nat.le_refl _) st sl le m hal hinv
  intro g
  induction g with
  | zero => intro _ st sl le m _ _; rw [execOne_zero]; trivial
  | succ g ih =>
      intro hg st sl le m hal hinv
      have halb : c.alignedAccess = true → AlignedExec g mod st sl body env := fun hc => by
        have h1 := hal hc
        simp only [AlignedOne] at h1
        exact h1.1
      rw [execOne_loop_succ g mod st sl env 0 r.toList.length body pts rts]
      have ho := hP g (by omega) L' σ (r.toList ++ σ) n body s0 n1 hbody (Nat.le_refl _) hL' hc'
        st sl le m env halb hinv
      cases hres : exec g mod st sl body env with
      | Fallthrough st' sl' =>
          rw [hres] at ho
          obtain ⟨σ'', hσ, -, t, le', m', hx, hinv', hf⟩ := ho
          cases hσ
          obtain ⟨t', hW⟩ := exec_wrap_exit hx (.inl rfl)
          refine ⟨by simp; omega, t', le', m', hW, ?_, hf.mono hbase⟩
          refine { stack := stack_after ?_ hinv.stack hf, locals := hinv'.locals,
                   store := hinv'.store, status := hinv'.status, brk := hinv'.brk, lim := hinv'.lim }
          intro hr'
          cases r with
          | none => simp at hr'
          | some t0 =>
              obtain ⟨v, vr, hv, ht, hl, -⟩ := hinv'.stack.cons_inv
              exact ⟨v, by rw [hv]; rfl, fun t' e => by cases e; exact ⟨ht, hl⟩⟩
      | Break k st' sl' =>
          rw [hres] at ho
          obtain ⟨t, le', m', out, hx, hrel, hf⟩ := ho
          cases k with
          | zero =>
              obtain ⟨l, hl, h0, -, -⟩ := hrel.target
              simp [L'] at hl; subst hl
              have hout : out = .Out_continue := by simpa using h0 rfl
              subst hout
              have hf0 : Frame σ.length le le' := hf _ rfl
              have hinv'' : Inv E c σ st'
                  { params := sl'.params, locals := sl'.locals,
                    values := sl'.values.take 0 ++ sl.values.drop 0 } le' m' :=
                { stack := by simpa using hinv.stack.frame hf0, locals := hrel.locals,
                  store := hrel.store, status := hrel.status, brk := hrel.brk, lim := hrel.lim }
              exact ConstructOutcome.again hL hbase hx hf0
                (ih (by omega) st' _ le' m' (fun hc => by
                  have h1 := hal hc
                  simp only [AlignedOne, hres] at h1
                  exact h1.2) hinv'')
          | succ k =>
              have hout := hrel.outer (by omega)
              subst hout
              obtain ⟨t', hW⟩ := exec_wrap_exit hx (.inr rfl)
              obtain ⟨l, hl, -, hfin, hkept⟩ := hrel.target
              simp [L'] at hl
              refine ⟨t', le', m', hW, ?_, fun l' hl' => hf l' (by simpa [L'] using hl')⟩
              exact { target := ⟨l, hl, hfin, hkept⟩, brk := hrel.brk, small := hrel.small,
                      locals := hrel.locals, store := hrel.store, status := hrel.status, lim := hrel.lim }
      | Return st' vs =>
          rw [hres] at ho
          obtain ⟨t, le', m', out, hx, hrel, hg', hs⟩ := ho
          obtain ⟨rv, rfl⟩ := ReturnRel.isReturn hrel
          exact ⟨_, le', m', _, exec_wrap_return hx, hrel, hg', hs⟩
      | Trap st' msg =>
          rw [hres] at ho
          obtain ⟨t, le', m', hx, hg', hs, hc⟩ := ho
          have : ∃ rv, trapOut c.result = .Out_return rv := by
            cases c.result <;> exact ⟨_, rfl⟩
          obtain ⟨rv, e⟩ := this
          refine ⟨E0 ++ t, le', m', ?_, hg', hs, hc⟩
          rw [e] at hx ⊢
          exact exec_wrap_return hx
      | Invalid _ => trivial
      | OutOfFuel => trivial
      | ReturnCall _ _ _ => rw [hres] at ho; exact ho.elim
      | Throwing _ _ _ _ => rw [hres] at ho; exact ho.elim

end

end LeanExe.Native
