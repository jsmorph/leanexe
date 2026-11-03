import LeanExe.WGSL.EventsAgree

/-!
With the oracle that returns the initial buffers' words, the event semantics computes what the
semantics of `Semantics.lean` computes: the same values, variables, and outcome, and writes equal
to the recorded stores.  With `Module.invokeE_det`, an invocation whose reads return the initial
words ends exactly when `Module.invoke` succeeds and writes its stores.
-/

namespace LeanExe.WGSL

/-- An invocation's shape in a context. -/
def Context.shape (ctx : Context) : Shape := ⟨ctx.gid, ctx.inputs.map (·.size), ctx.outputSize⟩

/-- The oracle whose reads return the initial buffers' words. -/
def inputOracle (inputs : List (Array UInt32)) : Oracle :=
  fun _ b i => (inputs[b]?.bind (·[i]?)).getD 0

/-- The `Run` of `Semantics.lean` for a local state after the events `evs`. -/
def Local.toRun (l : Local) (evs : List Event) : Run := ⟨l.env, writesOf evs, l.returned⟩

/-- The run of `Semantics.lean` that a result corresponds to. -/
def Res.toRun (r : Res Local) : Option Run := r.2.map fun l => l.toRun r.1

@[simp] theorem Local.toRun_env (l : Local) (evs : List Event) : (l.toRun evs).env = l.env := rfl

@[simp] theorem Local.toRun_returned (l : Local) (evs : List Event) :
    (l.toRun evs).returned = l.returned := rfl

theorem Local.toRun_congr (l : Local) {evs evs' : List Event} (h : writesOf evs' = writesOf evs) :
    l.toRun evs' = l.toRun evs := by
  simp [Local.toRun, h]

theorem Res.andThen_snd (r : Res α) (k : List Event → α → Res β) :
    (r.andThen k).2 = r.2.bind fun x => (k r.1 x).2 := by
  rcases r with ⟨e, _ | x⟩ <;> rfl

theorem Res.andThen_toRun (r : Res α) (k : List Event → α → Res Local) :
    (r.andThen k).toRun = r.2.bind fun x => (k r.1 x).toRun := by
  rcases r with ⟨e, _ | x⟩ <;> rfl

theorem Res.toRun_bind (r : Res Local) (f : Run → Option Run) :
    (r.2.bind fun l => f (l.toRun r.1)) = r.toRun.bind f := by
  rcases r with ⟨e, _ | x⟩ <;> rfl

theorem Res.andThen_writes {r : Res α} {k : List Event → α → Res β} {evs : List Event}
    (hr : writesOf r.1 = writesOf evs)
    (hk : ∀ e1 x, writesOf e1 = writesOf evs → writesOf (k e1 x).1 = writesOf evs) :
    writesOf (r.andThen k).1 = writesOf evs := by
  rcases r with ⟨e1, _ | x⟩
  · exact hr
  · exact hk e1 x hr

/-- An expression's evaluation adds no write. -/
theorem Expr.evalE_writes (s : Shape) (o : Oracle) (env : Env) :
    ∀ (e : Expr) (evs : List Event), writesOf (e.evalE s o env evs).1 = writesOf evs := by
  intro e
  induction e with
  | lit _ | bool _ | var _ | gidX | fst _ | snd _ | length _ => intro evs; rfl
  | vec2 a b iha ihb | min a b iha ihb =>
      intro evs
      exact Res.andThen_writes (iha evs) fun e1 _ h1 =>
        Res.andThen_writes ((ihb e1).trans h1) fun _ _ h2 => h2
  | not a ih | toF32 a ih | toU32 a ih | sqrt a ih | round a ih | abs a ih =>
      intro evs
      exact Res.andThen_writes (ih evs) fun _ _ h1 => h1
  | bin op a b iha ihb =>
      intro evs
      cases op
      case and | or =>
        refine Res.andThen_writes (iha evs) fun e1 x h1 => ?_
        cases x with
        | bool v =>
            cases v
            all_goals first
              | exact h1
              | exact Res.andThen_writes ((ihb e1).trans h1) fun _ _ h2 => h2
        | _ => exact h1
      all_goals exact Res.andThen_writes (iha evs) fun e1 _ h1 =>
        Res.andThen_writes ((ihb e1).trans h1) fun _ _ h2 => h2
  | select f t c ihf iht ihc =>
      intro evs
      exact Res.andThen_writes (ihf evs) fun e1 _ h1 =>
        Res.andThen_writes ((iht e1).trans h1) fun e2 _ h2 =>
          Res.andThen_writes ((ihc e2).trans h2) fun _ _ h3 => h3
  | index b p ih =>
      intro evs
      refine Res.andThen_writes (ih evs) fun e1 x h1 => ?_
      cases x with
      | u32 i =>
          rcases s.sizes[b]? with _ | n
          · exact h1
          · by_cases hi : i.toNat < n <;> simp [hi, h1]
      | _ => exact h1

/-- With the input oracle, an expression's value is that of `Expr.eval`. -/
theorem Expr.evalE_input (ctx : Context) (env : Env) : ∀ (e : Expr) (evs : List Event),
    (e.evalE ctx.shape (inputOracle ctx.inputs) env evs).2 = e.eval ctx env := by
  intro e
  induction e with
  | lit _ | bool _ | var _ | gidX | fst _ | snd _ => intro evs; rfl
  | length b => intro evs; simp [Expr.evalE, Expr.eval, Context.shape, Option.map_map,
      Function.comp_def]
  | vec2 a b iha ihb | min a b iha ihb =>
      intro evs
      simp only [Expr.evalE, Expr.eval, Res.andThen_snd, iha, ihb]
      rcases Expr.eval ctx env a with _ | x <;> rcases Expr.eval ctx env b with _ | y <;>
        simp only [Option.bind_none, Option.bind_some] <;> (try cases x) <;> (try cases y) <;> rfl
  | not a ih | toF32 a ih | toU32 a ih | sqrt a ih | round a ih | abs a ih =>
      intro evs
      simp only [Expr.evalE, Expr.eval, Res.andThen_snd, ih]
      rcases Expr.eval ctx env a with _ | x <;> simp only [Option.bind_none, Option.bind_some] <;>
        (try cases x) <;> rfl
  | bin op a b iha ihb =>
      intro evs
      cases op
      case and | or =>
        simp only [Expr.evalE, Expr.eval, Res.andThen_snd, iha]
        rcases Expr.eval ctx env a with _ | x
        · rfl
        · simp only [Option.bind_some]
          cases x with
          | bool v =>
              cases v <;> simp only [Res.andThen_snd, ihb] <;>
                rcases Expr.eval ctx env b with _ | y <;> simp only [Option.bind_none,
                  Option.bind_some] <;> (try cases y) <;> rfl
          | _ => rfl
      all_goals
        simp only [Expr.evalE, Expr.eval, Res.andThen_snd, iha, ihb]
        rfl
  | select f t c ihf iht ihc =>
      intro evs
      simp only [Expr.evalE, Expr.eval, Res.andThen_snd, ihf, iht, ihc]
      rcases Expr.eval ctx env f with _ | fv <;> rcases Expr.eval ctx env t with _ | tv <;>
        rcases Expr.eval ctx env c with _ | cv <;>
        simp only [Option.bind_none, Option.bind_some] <;> (try cases cv) <;> rfl
  | index b p ih =>
      intro evs
      simp only [Expr.evalE, Expr.eval, Res.andThen_snd, ih]
      have hs : ctx.shape.sizes[b]? = (ctx.inputs[b]?).map (·.size) := by simp [Context.shape]
      rw [hs]
      rcases Expr.eval ctx env p with _ | x
      · rcases ctx.inputs[b]? with _ | buf <;> rfl
      · simp only [Option.bind_some]
        rcases hbuf : ctx.inputs[b]? with _ | buf
        · cases x <;> rfl
        · cases x with
          | u32 i =>
              by_cases hi : i.toNat < buf.size
              · simp [hi, inputOracle, hbuf]
              · simp [hi]
          | _ => rfl

/-- `loopRunsE` computes `loopRuns` when its test and body do. -/
theorem loopRunsE_input {testE : Local → List Event → Res Bool}
    {bodyE : Local → List Event → Res Local} {test : Run → Option Bool} {body : Run → Option Run}
    (ht : ∀ l evs, (testE l evs).2 = test (l.toRun evs) ∧
      writesOf (testE l evs).1 = writesOf evs)
    (hb : ∀ l evs, (bodyE l evs).toRun = body (l.toRun evs)) :
    ∀ fuel l evs, (loopRunsE testE bodyE fuel l evs).toRun = loopRuns test body fuel (l.toRun evs)
  | 0, _, _ => rfl
  | fuel + 1, l, evs => by
      simp only [loopRunsE, loopRuns, Local.toRun_returned]
      by_cases hr : l.returned
      · simp [hr, Res.toRun]
      · simp only [hr, Bool.false_eq_true, ↓reduceIte, Res.andThen_toRun, (ht l evs).1]
        rcases test (l.toRun evs) with _ | c
        · rfl
        · simp only [Option.bind_some]
          cases c
          · simp [Res.toRun, Local.toRun_congr l (ht l evs).2]
          · simp only [↓reduceIte, Res.andThen_toRun, loopRunsE_input ht hb fuel, Res.toRun_bind,
              hb, Local.toRun_congr l (ht l evs).2]
            all_goals rfl

mutual
  /-- With the input oracle, a statement's event run computes `Stmt.exec`. -/
  theorem Stmt.execE_input (ctx : Context) : ∀ (st : Stmt) (l : Local) (evs : List Event),
      (Stmt.execE ctx.shape (inputOracle ctx.inputs) l evs st).toRun =
        Stmt.exec ctx (l.toRun evs) st
    | .let_ n ty e, l, evs | .var n ty e, l, evs => by
        simp only [Stmt.execE, Stmt.exec, Res.andThen_toRun, Expr.evalE_input, Local.toRun_env]
        rcases Expr.eval ctx l.env e with _ | v
        · rfl
        · simp only [Option.bind_some]
          by_cases h1 : ty.holds v = true <;> by_cases h2 : l.env.find n = none <;>
            simp [Res.toRun, Local.toRun, Expr.evalE_writes, h1, h2]
    | .assign n e, l, evs => by
        simp only [Stmt.execE, Stmt.exec, Res.andThen_toRun, Expr.evalE_input, Local.toRun_env]
        rcases Expr.eval ctx l.env e with _ | v
        · rfl
        · simp only [Option.bind_some]
          rcases l.env.find n with _ | ⟨old, _ | _⟩
          · rfl
          · rfl
          · by_cases hc : old.sameType v = true <;>
              simp [Res.toRun, Local.toRun, Expr.evalE_writes, hc]
    | .store b p e, l, evs => by
        simp only [Stmt.execE, Stmt.exec, Res.andThen_toRun, Expr.evalE_input, Local.toRun_env]
        rcases Expr.eval ctx l.env p with _ | x
        · rfl
        · simp only [Option.bind_some]
          rcases Expr.eval ctx l.env e with _ | y
          · cases x <;> rfl
          · simp only [Option.bind_some]
            cases x with
            | u32 i =>
                cases y with
                | u32 v =>
                    by_cases hc : b = ctx.inputs.length ∧ i.toNat < ctx.outputSize
                    · simp [Context.shape, hc, Res.toRun, Local.toRun, Expr.evalE_writes]
                    · simp [Context.shape, hc, Res.toRun]
                | _ => rfl
            | _ => cases y <;> rfl
    | .ite c ts es, l, evs => by
        simp only [Stmt.execE, Stmt.exec, Res.andThen_toRun, Expr.evalE_input, Local.toRun_env,
          Option.bind_eq_bind]
        rcases Expr.eval ctx l.env c with _ | x
        · rfl
        · simp only [Option.bind_some]
          cases x with
          | bool cv =>
              have hw := Expr.evalE_writes ctx.shape (inputOracle ctx.inputs) l.env c evs
              cases cv <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
                rw [← Local.toRun_congr l hw] <;>
                first
                  | rw [← Stmt.execListE_input ctx es]
                  | rw [← Stmt.execListE_input ctx ts]
              all_goals
                rcases Stmt.execListE ctx.shape (inputOracle ctx.inputs) l _ _ with
                  ⟨e2, _ | inner⟩ <;> rfl
          | _ => rfl
    | .while_ c body, l, evs => by
        simp only [Stmt.execE, Stmt.exec]
        refine loopRunsE_input (fun l evs => ⟨?_, ?_⟩) (fun l evs => ?_) loopBound l evs
        · simp only [Res.andThen_snd, Expr.evalE_input, Local.toRun_env]
          rcases Expr.eval ctx l.env c with _ | x
          · rfl
          · cases x <;> rfl
        · exact Res.andThen_writes (Expr.evalE_writes _ _ l.env c evs) fun _ _ h => h
        · simp only [Res.andThen_toRun]
          simp only [← Stmt.execListE_input ctx body l evs, Res.toRun]
          rcases Stmt.execListE ctx.shape (inputOracle ctx.inputs) l evs body with ⟨e, _ | inner⟩
          · rfl
          · rfl
    | .ret, l, evs => rfl

  /-- With the input oracle, a statement list's event run computes `Stmt.execList`. -/
  theorem Stmt.execListE_input (ctx : Context) : ∀ (sts : List Stmt) (l : Local) (evs : List Event),
      (Stmt.execListE ctx.shape (inputOracle ctx.inputs) l evs sts).toRun =
        Stmt.execList ctx (l.toRun evs) sts
    | [], l, evs => rfl
    | st :: rest, l, evs => by
        simp only [Stmt.execListE, Stmt.execList, Local.toRun_returned]
        by_cases hr : l.returned
        · simp [hr, Res.toRun]
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, Res.andThen_toRun,
            Stmt.execListE_input ctx rest]
          have ih := Stmt.execE_input ctx st l evs
          rcases hR : Stmt.execE ctx.shape (inputOracle ctx.inputs) l evs st with ⟨e1, _ | l1⟩ <;>
            rw [hR] at ih <;> rw [← ih] <;> rfl
end

/-- With the input oracle, an invocation ends exactly when `Module.invoke` succeeds, and its
writes are the stores of `Module.invoke`. -/
theorem Module.invokeE_input (m : Module) (inputs : List (Array UInt32)) (outputSize : Nat)
    (gid : UInt32) :
    m.invoke inputs outputSize gid =
      if (m.invokeE (inputs.map (·.size)) outputSize (inputOracle inputs) gid).2 then
        some (writesOf (m.invokeE (inputs.map (·.size)) outputSize (inputOracle inputs) gid).1)
      else none := by
  have h := Stmt.execListE_input { gid, inputs, outputSize } m.body
    { env := [], returned := false } []
  simp only [Context.shape] at h
  unfold Module.invokeE Module.invoke
  simp only [List.length_map]
  split
  · have h0 : Local.toRun { env := [], returned := false } [] = ⟨[], [], false⟩ := rfl
    rw [h0] at h
    rw [← h]
    rcases Stmt.execListE { gid, sizes := inputs.map (·.size), outputSize } (inputOracle inputs)
      { env := [], returned := false } [] m.body with ⟨e, _ | l⟩ <;> rfl
  · rfl

/-- An invocation whose reads return the initial buffers' words has the events and outcome of
the input oracle. -/
theorem Module.invokeE_agree (m : Module) (inputs : List (Array UInt32)) (outputSize : Nat)
    (o : Oracle) (gid : UInt32)
    (hr : ∀ (k b i : Nat) (w : UInt32),
      (m.invokeE (inputs.map (·.size)) outputSize o gid).1[k]? = some (.read b i w) →
        inputs[b]?.bind (·[i]?) = some w) :
    m.invokeE (inputs.map (·.size)) outputSize o gid =
      m.invokeE (inputs.map (·.size)) outputSize (inputOracle inputs) gid :=
  ((m.invokeE_det _ _ o gid).2 (inputOracle inputs) fun k b i w hk => by
    simp [inputOracle, hr k b i w hk]).symm

/-- The reads of an invocation with the input oracle return the initial buffers' words. -/
theorem Module.invokeE_input_reads (m : Module) (inputs : List (Array UInt32)) (outputSize : Nat)
    (gid : UInt32) (k b i : Nat) (w : UInt32)
    (hk : (m.invokeE (inputs.map (·.size)) outputSize (inputOracle inputs) gid).1[k]? =
      some (.read b i w)) :
    inputs[b]?.bind (·[i]?) = some w := by
  obtain ⟨hw, n, hn, hi⟩ := (m.invokeE_det _ _ _ gid).1.read k b i w hk
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
  obtain ⟨buf, hbuf, rfl⟩ := hn
  subst hw
  simp [inputOracle, hbuf, hi]

end LeanExe.WGSL
