import Verified.AlignedArgs

/-!
Calls under the flag.  `FunSpecX strict` is `FunSpec` together, under `strict = true`, with
`FunAligned`: a run of the function from an aligned heap and aligned arguments makes only aligned
64-bit accesses (`RunsA`) and returns, beside what `FunSpec.runs` states, an aligned owned value in
an aligned heap.  `FunPost strict` is the postcondition of `FunSpec.runs` with that conjunct
under `strict = true`, and `RunsX strict` is `Runs` at `strict = false` and `RunsA` at
`strict = true`, so that `FunSpecX.runs` and `wpX_call_runs` serve both values of the flag.
`CallsAtX` is `CallsAt` with `FunSpecX`; the function level proves it as it proves `CallsAt`.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `Runs` at `strict = false`, and `RunsA` at `strict = true`. -/
def RunsX {α : Type} (strict aborts : Bool) (env : HostEnv α) (m : Module) (id : Nat)
    (initial : Store α) (args : List Value) (P : Store α → List Value → Prop) : Prop :=
  match strict with
  | false => Runs aborts env m id initial args P
  | true => RunsA aborts env m id initial args P

/-- `wp_call_runs` under the flag. -/
theorem wpX_call_runs {α : Type} {strict aborts : Bool} {env : HostEnv α} {m : Module} {id : Nat}
    {st : Store α} {s : Locals} {rest : Program} {Q : Assertion α}
    {Post : Store α → List Value → Prop}
    (hRun : RunsX strict aborts env m id st s.values Post) (hTrap : TrapOK aborts Q)
    (hPost : ∀ st' vs, Post st' vs → wpX strict m rest Q st' { s with values := vs } env) :
    wpX strict m (.call id :: rest) Q st s env := by
  cases strict
  · exact wp_call_runs hRun hTrap hPost
  · exact wpA_call_runs hRun hTrap hPost

/-- The postcondition of `FunSpec.runs`, with the alignment of the heap and of the value under
`strict = true`. -/
def FunPost (strict : Bool) (g : Sig) (F : Env g.params → g.result.denote) (pf : List Bool)
    (rf : Bool) (A : Env g.params → Nat) (Fi : Env g.params → Bool) (heap : Heap)
    (store : Store Unit) (ws : List Value) (args : Env g.params) (rest : List Value)
    (final : Store Unit) (values : List Value) : Prop :=
  ∃ out, values = out ++ rest ∧ ∃ heap' : Heap, heap'.At final ∧
    g.result.Rep .owned heap' final out.reverse (F args) ∧
    final.memoryCaps = store.memoryCaps ∧
    (∀ r, heap.Region r → 0 < r.2 → Apart store (Env.moves store g.mode ws args) r →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
      heap'.Region r ∧
      ∀ b ∈ g.result.blocks final out.reverse (F args), regionsDisjoint r b) ∧
    ((g.depth && !Fi args) = false →
      heap'.top.toNat + (if rf then g.result.pot final out.reverse (F args) else 0) ≤
        heap.top.toNat + Env.argPot store (g.paidSel pf) ws args + A args) ∧
    (strict = true → heap'.Aligned ∧ Ty.AlignedVal .owned final g.result out.reverse (F args))

/-- The aligned runs of the function that `FunSpec` describes: from an aligned heap and aligned
arguments, every run makes only aligned 64-bit accesses and ends as `FunPost true` states. -/
def FunAligned (m : Module) (g : Sig) (idx : Nat) (F : Env g.params → g.result.denote)
    (pf : List Bool) (rf : Bool) (A : Env g.params → Nat) (Fi : Env g.params → Bool)
    (D : UInt64 → Prop) (pool : Bytes.LiteralPool) : Prop :=
  ∀ (host : HostEnv Unit) {heap : Heap} {store : Store Unit} {ws : List Value}
    {args : Env g.params}, heap.At store →
    @Bytes.LiteralPool.Input (Env g.params) (Env.represent g.params g.modes) pool heap store ws
      args →
    Env.Rep g.mode heap store ws args →
    Separate store (Env.moves store g.mode ws args) (Env.reads store g.mode ws args) →
    store.memoryCap m 0 ≤ 65535 → heap.Aligned → Env.AlignedVals store g.mode ws args →
    ∀ {d : UInt64}, (g.depth = true → D d) → ∀ rest : List Value,
    RunsA ((g.depth && !Fi args) ||
        ((g.aborts || g.depth) &&
          !decide (heap.Within store m (Env.argPot store (g.paidSel pf) ws args + A args))))
      host m idx store (ws.reverse ++ ((if g.depth then [.i64 d] else []) ++ rest))
      (FunPost true g F pf rf A Fi heap store ws args rest)

/-- `FunSpec` under the flag. -/
def FunSpecX (strict : Bool) (m : Module) (g : Sig) (idx : Nat)
    (F : Env g.params → g.result.denote) (pf : List Bool) (rf : Bool) (A : Env g.params → Nat)
    (Fi : Env g.params → Bool) (D : UInt64 → Prop) (pool : Bytes.LiteralPool) : Prop :=
  FunSpec m g idx F pf rf A Fi D pool ∧ (strict = true → FunAligned m g idx F pf rf A Fi D pool)

/-- `CallsAt` under the flag. -/
def CallsAtX (strict : Bool) {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (fits : Fits S) (d0 : UInt64) (pool : Bytes.LiteralPool) : Prop :=
  ∀ {g : Sig} (f : FVar S g), FunSpecX strict m g f.callIndex (funs.get f) (flags.params f)
    (flags.result f) (bounds.get f) (fits.get f) (fun d => d = d0 + 1) pool

theorem CallsAtX.false_iff {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {d0 : UInt64} {pool : Bytes.LiteralPool} :
    CallsAtX false m funs flags bounds fits d0 pool ↔ CallsAt m funs flags bounds fits d0 pool :=
  ⟨fun h _ f => (h f).1, fun h _ f => ⟨h f, nofun⟩⟩

/-- `FunSpec.runs` under the flag. -/
theorem FunSpecX.runs {strict : Bool} {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} {pool : Bytes.LiteralPool}
    (hF : FunSpecX strict m g idx F pf rf A Fi D pool) (hm : Runtime m) (host : HostEnv Unit)
    {heap : Heap} {store : Store Unit} {ws : List Value} {args : Env g.params}
    (hAt : heap.At store)
    (hInput : @Bytes.LiteralPool.Input (Env g.params) (Env.represent g.params g.modes)
      pool heap store ws args)
    (hRep : Env.Rep g.mode heap store ws args)
    (hSep : Separate store (Env.moves store g.mode ws args) (Env.reads store g.mode ws args))
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hAl : strict = true → heap.Aligned ∧ Env.AlignedVals store g.mode ws args)
    {d : UInt64} (hd : g.depth = true → D d) (rest : List Value) :
    RunsX strict ((g.depth && !Fi args) ||
        ((g.aborts || g.depth) &&
          !decide (heap.Within store m (Env.argPot store (g.paidSel pf) ws args + A args))))
      host m idx store (ws.reverse ++ ((if g.depth then [.i64 d] else []) ++ rest))
      (FunPost strict g F pf rf A Fi heap store ws args rest) := by
  cases strict
  · exact (hF.1.runs hm host hAt hInput hRep hSep hCap hd rest).mono
      fun _ _ ⟨out, h1, heap', h2, h3, h4, h5, h6⟩ => ⟨out, h1, heap', h2, h3, h4, h5, h6, nofun⟩
  · exact hF.2 rfl host hAt hInput hRep hSep hCap (hAl rfl).1 (hAl rfl).2 hd rest

/-- `wp_depthCode` under the flag. -/
theorem wpX_depthCode {strict : Bool} {m : Module} {host : HostEnv Unit} {Q : Assertion Unit}
    {store : Store Unit} {s : Locals} {rest : Program} (depth : Bool) {d0 : UInt64}
    (hd : depth = true → s.params.head? = some (.i64 d0))
    (h : wpX strict m rest Q store
      { s with values := (if depth then [.i64 (d0 + 1)] else []) ++ s.values } host) :
    wpX strict m ((if depth then [.localGet 0, .constI64 1, .addI64] else []) ++ rest) Q store s
      host := by
  cases depth
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at h ⊢
    exact h
  · have h0 : s.get 0 = some (.i64 d0) := by
      have := hd rfl
      cases hp : s.params with
      | nil => rw [hp] at this; exact nomatch this
      | cons v vs =>
        rw [hp] at this
        simp only [List.head?_cons, Option.some.injEq] at this
        simp [Locals.get, hp, this]
    simp only [↓reduceIte, List.cons_append, List.nil_append, wpX_localGet_cons, h0,
      wpX_constI64_cons, wpX_addI64_cons] at h ⊢
    exact h

/-- The code before a call's arguments: the call depth after the frame's, from local 0, when the
callee's code takes it. -/
theorem wp_depthCode {m : Module} {host : HostEnv Unit} {Q : Assertion Unit} {store : Store Unit}
    {s : Locals} {rest : Program} (depth : Bool) {d0 : UInt64}
    (hd : depth = true → s.params.head? = some (.i64 d0))
    (h : wp m rest Q store { s with values := (if depth then [.i64 (d0 + 1)] else []) ++ s.values }
      host) :
    wp m ((if depth then [.localGet 0, .constI64 1, .addI64] else []) ++ rest) Q store s host :=
  wpX_depthCode (strict := false) depth hd h

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value} {strict : Bool}

/-- A call: the arguments, the callee, whose theorem `Calls` gives, and the release of the owned
variables that the arguments use and that die at the call, other than those that the call
consumes. -/
theorem specX_call (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hCopy : CopyCodeX strict m host) {d0 : UInt64}
    (hCalls : CallsAtX strict m funs flags bounds fits d0 pool)
    {sig : Sig}
    {Γ' : List Ty} (g : FVar S sig)
    (args : (i : Fin sig.params.length) → Expr S Γ' (sig.params.get i))
    (argsSpec : ∀ i env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (args i) env
        slots paid live)
    (hDepth : (Expr.call g args).depthCalls = true → pv.head? = some (.i64 d0)) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.call g args) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hRoom' : ∀ i : Fin sig.params.length, base + (if sig.mode i = .owned then
      copyWidth (sig.params.get i)
      else (args i).width) ≤ h := fun i =>
    (Nat.add_le_add_left (le_argsMax (fun i => if sig.mode i = .owned then
      copyWidth (sig.params.get i) else (args i).width) i) base).trans hRoom
  simp only [Expr.placeArgs, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hPlace
  obtain ⟨⟨hA, hV⟩, hB⟩ := hPlace
  have hPlace1 : ∀ i, (sig.params.get i).scalar = false → sig.mode i = .borrowed →
      (args i).isPlace = true := fun i hs _ => by
    cases hi : (args i).isPlace with
    | true => rfl
    | false =>
      have := le_argsAny (fun i => !(sig.params.get i).scalar && !(args i).isPlace) i
        (by simp only [hs, hi, Bool.not_false, Bool.and_self])
      rw [hA] at this
      exact nomatch this
  have hVar : ∀ i : Fin sig.params.length, sig.mode i = .owned → ∃ x, args i = .var x :=
      fun i hmo => by
    refine Expr.exists_var (args i) ?_
    cases hi : (args i).varIndex?.isNone with
    | false => rfl
    | true =>
      have := le_argsAny (fun i => sig.mode i == .owned && (args i).varIndex?.isNone) i
        (by simp [hmo, hi])
      rw [hV] at this
      exact nomatch this
  have hPlace2 : ∀ i, (args i).placeArgs = true := fun i => by
    cases hi : (args i).placeArgs with
    | true => rfl
    | false =>
      have := le_argsAny (fun i => !(args i).placeArgs) i (by simp [hi])
      rw [hB] at this
      exact nomatch this
  have hMoved := callMoves_moved slots live args hVar
  have hAllocs : (Expr.call g args).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      argsSum (argCost funs flags bounds (slots.map Slot.mode) paid
        (fun i => live i || argsAny fun j => (args j).uses i)
        (fun i => (live i || argsAny fun j => (args j).uses i) &&
          !(argsAny fun j => callMoves slots live args j && (args j).uses i)) sig.mode args env) +
        callCredits funs flags (slots.map Slot.mode) paid live g args env +
        bounds.get g (Env.ofFn fun i => (args i).denote funs env) := by
    simp only [Expr.allocs, callMovesAt_eq]; rfl
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine wpX_depthCode sig.depth (fun hd => by
    rw [hpv]; exact hDepth (by simp [Expr.depthCalls, hd])) ?_
  refine args_specX hCopy (paid := paid) (all := fun i => live i || argsAny fun j => (args j).uses i)
    (kept := fun i => (live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) sig.mode args argsSpec
    (fun i k h => by
      simp only [Bool.or_eq_true]
      exact Or.inr (le_argsAny (fun j => (args j).uses k) i h))
    (fun k h => by simp only [Bool.and_eq_true] at h; exact h.1)
    (fun i hmo => ?_) hPlace1 (fun i hmo => ?_) hPlace2
    (fun i h => by
      simp only [Bool.not_eq_true'] at h
      simp only [Expr.fits, Bool.not_eq_true', Bool.and_eq_false_iff]
      exact Or.inl (argsAll_false _ i h))
    (fun i h => by
      simp only [Bool.or_eq_true] at h
      simp only [Expr.aborts, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (Or.inr (le_argsAny (fun j => (args j).aborts || sig.mode j == .owned) i
          (by simpa only [Bool.or_eq_true] using h)))
      · exact Or.inr h) heap store
    { s with values := (if sig.depth then [.i64 (d0 + 1)] else []) ++ s.values } hh hpv hVars hAt (fun hs => (hAl hs).values _)
    (hSafe.values _) hCap hBase hRoom' _ _
    (hTrap.part id id fun _ hw => hw.mono (by rw [hAllocs]; omega))
    fun heap1 store1 s1 ws1 F hStep1 hF1 hH1 hRep1 hAlArgs hSep1 hX1 hY1 hTop1 hPot1 => ?_
  · -- An owned parameter holds arrays.
    have := paramMode_owned hmo
    exact this
  · obtain ⟨x, hx⟩ := hVar i hmo
    refine ⟨x, hx, fun hkx => ?_⟩
    have hux : (args i).uses x.index = true := by rw [hx]; simp [Expr.uses]
    have hAll : (argsAny fun j => (args j).uses x.index) = true := le_argsAny _ i hux
    simp only [hAll, Bool.or_true, Bool.true_and, Bool.not_eq_false'] at hkx
    obtain ⟨j, y, hy, hyx, -, hmy, -, hOthers⟩ := hMoved _ hkx
    have hji : j = i := by
      by_contra hne
      have := hOthers i (Ne.symm hne) (paramMode_owned hmo)
      rw [hux] at this
      exact nomatch this
    subst hji
    exact ⟨hmy, hOthers⟩
  -- The callee, from the arguments' state, above the next call depth when its code takes it.
  replace hF1 : Frame base s s1 := hF1.values
  simp only [Holds.keepDying_values] at hX1
  obtain ⟨hStatic1, hStaticFresh⟩ := hSafe.static.step hStep1 (fun _ _ => trivial)
  have hInput : @Bytes.LiteralPool.Input (Env sig.params) (Env.represent sig.params sig.modes)
      pool heap1 store1 ws1 (Env.ofFn fun i => (args i).denote funs env) := by
    refine ⟨hStatic1, fun region hRegion => hX1 region (hStaticFresh region hRegion) ?_⟩
    exact (hSafe.apart region hRegion).mono fun k hk _ => by
      obtain ⟨i, hi⟩ := argsAny_true.mp hk
      simp only [Bool.and_eq_true] at hi
      exact ⟨by simp only [Expr.uses, Bool.or_eq_true]; exact Or.inr (le_argsAny _ i hi.1.2), rfl⟩
  have hRun := FunSpecX.runs (hCalls g) hm host hStep1.at_ hInput hRep1 hSep1
    (by rw [hStep1.cap m]; exact hCap) (fun hs => ⟨(hAlArgs hs).1.1, (hAlArgs hs).2⟩) (d := d0 + 1) (fun _ => rfl) s.values
  have hPArgs : Env.argPot store1 (sig.paidSel (flags.params g)) ws1
        (Env.ofFn fun i => (args i).denote funs env) ≤
      dyingPot store s env slots paid (fun i => live i || (Expr.call g args).uses i) live +
        callCredits funs flags (slots.map Slot.mode) paid live g args env := by
    simpa only [callCredits, Expr.uses] using
      args_pot_le_credits (pf := flags.params g) (slots := slots) (live := live)
        (paid := paid) (env := env) (s := s) (ws := ws1) (funs := funs) (base := base)
        args hVar hVars hStep1 (fun sel hsel => by
          simpa only [Expr.paramPot_values] using hPot1 sel hsel)
  have hsd : (Expr.call g args).fits funs fits env = true →
      (sig.depth && !fits.get g (Env.ofFn fun i => (args i).denote funs env)) = false :=
    fun hf => by
      simp only [Expr.fits, Bool.and_eq_true] at hf
      cases hdep : sig.depth
      · rfl
      · simp only [hdep, ↓reduceIte] at hf; simp [hf.2]
  refine wpX_call_runs hRun (hTrap.of_imp fun h => by
    cases hfc : (Expr.call g args).fits funs fits env
    · simp [trapFlag]
    · simp only [hsd hfc, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at h
      obtain ⟨ha, hw⟩ := h
      have hab : ((Expr.call g args).aborts || slots.any (·.mode == .owned)) = true := by
        simp only [Bool.or_eq_true] at ha
        simp only [Expr.aborts, Bool.or_eq_true]; exact Or.inl (Or.inl (Or.inl ha))
      simp only [trapFlag, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not]
      refine ⟨hab, fun hW => hw ?_⟩
      rw [hAllocs] at hW
      have := hPArgs
      exact hW.shift (hTop1 (by simp [hfc])) (by omega) (hStep1.cap m)) fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, hTopC, hAlC⟩ := hPost
  have hRep : sig.result.Rep ((Expr.call g args).mode (slots.map Slot.mode)) heap' st'
      out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := by
    simp only [Expr.mode]
    split
    · exact Ty.Rep.borrow hOwned
    · exact hOwned
  have hStepC : Step heap1 store1
      (Apart store1 (Env.moves store1 sig.mode ws1 (Env.ofFn fun i => (args i).denote funs env))) heap'
      st' (((Expr.call g args).mode (slots.map Slot.mode)).fresh st' sig.result out.reverse
        (funs.get g (Env.ofFn fun i => (args i).denote funs env))) :=
    ⟨hAt', hCaps, fun r hr hpos hA => by
      obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos hA
      exact ⟨hb, hreg, fun b hb' => hout b (Mode.fresh_sub hb')⟩⟩
  -- The variables live after the call: those that its arguments use, other than the moved ones.
  have hKeptAll : ∀ i, ((live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) = true →
      (live i || argsAny fun j => (args j).uses i) = true :=
    fun i h => by simp only [Bool.and_eq_true] at h; exact h.1
  have hMovedDie : ∀ i, (argsAny fun j => sig.mode j == .owned && (args j).uses i &&
      !((live i || argsAny fun j => (args j).uses i) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses i))) = true →
      (live i || argsAny fun j => (args j).uses i) = true ∧
        ((live i || argsAny fun j => (args j).uses i) &&
          !(argsAny fun j => callMoves slots live args j && (args j).uses i)) = false := by
    intro i h
    obtain ⟨j, hj⟩ := argsAny_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hj
    refine ⟨?_, hj.2⟩
    simp only [Bool.or_eq_true]
    exact Or.inr (le_argsAny (fun j => (args j).uses i) j hj.1.2)
  have hKeepC : ∀ (u : Ty) (y : Var Γ' u),
      ((live y.index || argsAny fun j => (args j).uses y.index) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses y.index)) = true →
      ∀ wy, LocalsHold s1 (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        Apart store1 (Env.moves store1 sig.mode ws1 (Env.ofFn fun i => (args i).denote funs env)) c := by
    exact args_moves_apart_kept sig.mode args
      (fun i k hi => by simp only [Bool.or_eq_true]; exact Or.inr (le_argsAny _ i hi))
      hKeptAll hVars hStep1 hF1 hX1
  have aCall : After env slots (fun i => live i || (Expr.call g args).uses i)
      (fun i => (live i || argsAny fun j => (args j).uses i) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses i)) base heap store s
      sig.result ((Expr.call g args).mode (slots.map Slot.mode))
      (funs.get g (Env.ofFn fun i => (args i).denote funs env)) heap' st' s1 out.reverse := by
    refine ⟨hStep1.trans hStepC fun r hr => ⟨trivial, fun hF => hX1 r hF
        (hr.mono fun i h _ => hMovedDie i h)⟩, hF1,
      (hH1.live_mono hKeptAll).step hStepC hKeepC, hRep, ?_⟩
    intro u y hy _ wy hwy hly b hb c hc
    obtain ⟨hSame, hFresh⟩ := (hH1.live_mono hKeptAll).regions_after hStepC hy hwy hly
      (hKeepC u y hy wy hwy hly)
    rw [hSame] at hc
    have hb' : b ∈ ((Expr.call g args).mode (slots.map Slot.mode)).fresh st' sig.result
        out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := by
      simp only [Expr.mode] at hb ⊢
      cases hsc : sig.result.scalar
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hb ⊢
        exact hb
      · simp only [hsc, ↓reduceIte] at hb
        rw [Ty.regions_scalar _ hsc] at hb
        exact nomatch hb
    exact regionsDisjoint_symm (hFresh c hc b hb')
  have hResAl : strict = true → Ty.AlignedVal ((Expr.call g args).mode (slots.map Slot.mode)) st'
      sig.result out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := fun hs => by
    simp only [Expr.mode]
    split
    · exact Ty.AlignedVal.borrowOf hOwned (hAlC hs).2
    · exact (hAlC hs).2
  refine After.releaseX hm hRA (s1 := s1) (live := live)
    (sel := fun i => ((live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) && !live i) hVars aCall
    (fun hs => ⟨HoldsA.after hVars (hAl hs) aCall hKeptAll (hAlC hs).1, hResAl hs⟩)
    hKeptAll (fun i h => by simp only [Bool.and_eq_true] at h ⊢; exact h.1) (fun i h => ?_)
    fun heap2 store2 a2 hTopR hReg hAl2 => ?_
  · have hk : (argsAny fun j => callMoves slots live args j && (args j).uses i) = false := by
      cases hm' : argsAny fun j => callMoves slots live args j && (args j).uses i with
      | false => rfl
      | true =>
        obtain ⟨_, _, _, _, _, _, hl, _⟩ := hMoved i hm'
        rw [hl] at h
        exact nomatch h
    simp [h, hk]
  · refine (by simpa using hNext heap2 store2 s1 out.reverse a2 hAl2 ·) fun hd => ?_
    have := hTop1 (by simp [hd]); have := hTopC (hsd hd); have := congrArg UInt64.toNat hTopR
    have := hPArgs
    -- A paid call returns a paid result, whose regions the release keeps.
    have := pot_keep (P := (Expr.call g args).paid flags (slots.map Slot.mode) paid live)
      (Q := flags.result g) (a := sig.result.pot store2 out.reverse
        (funs.get g (Env.ofFn fun i => (args i).denote funs env)))
      (b := sig.result.pot st' out.reverse
        (funs.get g (Env.ofFn fun i => (args i).denote funs env)))
      (fun h => by simp only [Expr.paid, Bool.and_eq_true] at h; exact h.2) fun h => by
        simp only [Expr.paid, Bool.and_eq_true, Bool.not_eq_true'] at h
        exact Ty.pot_of_regions (by simp [Expr.mode, h.1]) hReg
    rw [hAllocs]
    show _ + (if (Expr.call g args).paid flags (slots.map Slot.mode) paid live = true then
      sig.result.pot store2 out.reverse
        (funs.get g (Env.ofFn fun i => (args i).denote funs env)) else 0) ≤ _
    omega

end Cases

end Verified
