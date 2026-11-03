import LeanExe.WGSL.Events

/-!
Properties of the event semantics of `Events.lean` under every oracle.  A result's events extend
the events before it, its reads lie within their buffers, and its writes lie within the output.
A result is determined by the values its reads return: another oracle that gives those reads the
same values gives the same result, whether the invocation ends or stops.
-/

namespace LeanExe.WGSL

def Event.write? : Event → Option (Nat × UInt32)
  | .write i v => some (i, v)
  | .read .. => none

/-- The writes among events, in the form in which `Run.writes` records stores. -/
def writesOf (evs : List Event) : List (Nat × UInt32) := evs.filterMap Event.write?

@[simp] theorem writesOf_nil : writesOf [] = [] := rfl

@[simp] theorem writesOf_append (a b : List Event) :
    writesOf (a ++ b) = writesOf a ++ writesOf b := by
  simp [writesOf]

@[simp] theorem writesOf_read (b i : Nat) (v : UInt32) : writesOf [.read b i v] = [] := rfl

@[simp] theorem writesOf_write (i : Nat) (v : UInt32) : writesOf [.write i v] = [(i, v)] := rfl

/-- Oracle `o` gives every read of `evs` the value that the read returned. -/
def Answers (o : Oracle) (evs : List Event) : Prop :=
  ∀ (k b i : Nat) (w : UInt32), evs[k]? = some (.read b i w) → o k b i = w

/-- Each read of `evs` returned the value of oracle `o` and lies within its buffer, and each write
lies within the output. -/
structure Good (s : Shape) (o : Oracle) (evs : List Event) : Prop where
  read : ∀ (k b i : Nat) (w : UInt32), evs[k]? = some (.read b i w) →
    o k b i = w ∧ ∃ n, s.sizes[b]? = some n ∧ i < n
  write : ∀ (k i : Nat) (w : UInt32), evs[k]? = some (Event.write i w) → i < s.outputSize

theorem getElem?_append_some {l : List α} (new : List α) {k : Nat} {a : α} (h : l[k]? = some a) :
    (l ++ new)[k]? = some a := by
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hk, h]

theorem getElem?_append_singleton {l : List α} {a b : α} {k : Nat} (h : (l ++ [a])[k]? = some b) :
    l[k]? = some b ∨ (k = l.length ∧ a = b) := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · left
    rwa [List.getElem?_append_left hk] at h
  · right
    rw [List.getElem?_append_right hk] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = l.length + j := ⟨k - l.length, by omega⟩
    cases j <;> simp at h ⊢
    exact h

theorem Answers.of_prefix {o : Oracle} {evs evs' : List Event} (h : Answers o evs')
    (hp : ∃ new, evs' = evs ++ new) : Answers o evs := by
  obtain ⟨new, rfl⟩ := hp
  exact fun k b i w hk => h k b i w (getElem?_append_some new hk)

theorem Good.nil (s : Shape) (o : Oracle) : Good s o [] :=
  ⟨fun _ _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩

theorem Good.append_read {s : Shape} {o : Oracle} {evs : List Event} {b i n : Nat}
    (h : Good s o evs) (hb : s.sizes[b]? = some n) (hi : i < n) :
    Good s o (evs ++ [.read b i (o evs.length b i)]) := by
  refine ⟨fun k b' i' w hk => ?_, fun k i' w hk => ?_⟩
  · rcases getElem?_append_singleton hk with hk | ⟨rfl, he⟩
    · exact h.read k b' i' w hk
    · cases he
      exact ⟨rfl, n, hb, hi⟩
  · rcases getElem?_append_singleton hk with hk | ⟨-, he⟩
    · exact h.write k i' w hk
    · cases he

theorem Good.append_write {s : Shape} {o : Oracle} {evs : List Event} {i : Nat} {v : UInt32}
    (h : Good s o evs) (hi : i < s.outputSize) : Good s o (evs ++ [.write i v]) := by
  refine ⟨fun k b' i' w hk => ?_, fun k i' w hk => ?_⟩
  · rcases getElem?_append_singleton hk with hk | ⟨-, he⟩
    · exact h.read k b' i' w hk
    · cases he
  · rcases getElem?_append_singleton hk with hk | ⟨-, he⟩
    · exact h.write k i' w hk
    · cases he
      exact hi

/-- Events `evs'` extend `evs` and keep `Good`. -/
structure Ext (s : Shape) (o : Oracle) (evs evs' : List Event) : Prop where
  ext : ∃ new, evs' = evs ++ new
  good : Good s o evs → Good s o evs'

theorem Ext.refl (s : Shape) (o : Oracle) (evs : List Event) : Ext s o evs evs :=
  ⟨⟨[], by simp⟩, id⟩

theorem Ext.trans {s : Shape} {o : Oracle} {a b c : List Event} (h1 : Ext s o a b)
    (h2 : Ext s o b c) : Ext s o a c := by
  obtain ⟨n1, rfl⟩ := h1.ext
  obtain ⟨n2, rfl⟩ := h2.ext
  exact ⟨⟨n1 ++ n2, by simp⟩, h2.good ∘ h1.good⟩

/-- A computation from the events `evs`, as a function of the oracle, whose result under `o`
extends `evs`, keeps `Good`, and is the result under any oracle that gives its reads the same
values. -/
def Det (s : Shape) (o : Oracle) (evs : List Event) (f : Oracle → Res α) : Prop :=
  Ext s o evs (f o).1 ∧ ∀ o', Answers o' (f o).1 → f o' = f o

theorem Det.pure (s : Shape) (o : Oracle) (evs : List Event) (x : Option α) :
    Det s o evs fun _ => (evs, x) :=
  ⟨Ext.refl s o evs, fun _ _ => rfl⟩

theorem Det.andThen {s : Shape} {o : Oracle} {evs : List Event} {f : Oracle → Res α}
    {k : Oracle → List Event → α → Res β} (hf : Det s o evs f)
    (hk : ∀ e1 x, Det s o e1 fun o => k o e1 x) : Det s o evs fun o => (f o).andThen (k o) := by
  obtain ⟨xf, yf⟩ := hf
  show Ext s o evs ((f o).andThen (k o)).1 ∧
    ∀ o', Answers o' ((f o).andThen (k o)).1 → (f o').andThen (k o') = (f o).andThen (k o)
  rcases hfo : f o with ⟨e1, _ | x⟩
  · simp only [hfo] at xf yf
    refine ⟨by simpa [Res.andThen] using xf, fun o' h => ?_⟩
    simp only [Res.andThen] at h
    simp only [yf o' h, Res.andThen]
  · simp only [hfo] at xf yf
    obtain ⟨xk, yk⟩ := hk e1 x
    refine ⟨by simpa [Res.andThen] using xf.trans xk, fun o' h => ?_⟩
    simp only [Res.andThen] at h ⊢
    simp only [yf o' (h.of_prefix xk.ext), yk o' h]

theorem Det.ite {s : Shape} {o : Oracle} {evs : List Event} {c : Prop} [Decidable c]
    {f g : Oracle → Res α} (hf : c → Det s o evs f) (hg : ¬c → Det s o evs g) :
    Det s o evs fun o => if c then f o else g o := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using hf h
  · simpa only [h, ↓reduceIte] using hg h

theorem Det.read {s : Shape} {o : Oracle} (evs : List Event) {b i n : Nat}
    (hb : s.sizes[b]? = some n) (hi : i < n) :
    Det s o evs fun o =>
      (evs ++ [.read b i (o evs.length b i)], some (Value.u32 (o evs.length b i))) :=
  ⟨⟨⟨_, rfl⟩, fun h => h.append_read hb hi⟩, fun o' h => by
    have : o' evs.length b i = o evs.length b i := h _ _ _ _ (by simp)
    simp only [this]⟩

theorem Det.write {s : Shape} {o : Oracle} (evs : List Event) {i : Nat} (v : UInt32)
    (hi : i < s.outputSize) (x : Option α) : Det s o evs fun _ => (evs ++ [.write i v], x) :=
  ⟨⟨⟨_, rfl⟩, fun h => h.append_write hi⟩, fun _ _ => rfl⟩

/-- An expression's evaluation is determined by the values of its reads. -/
theorem Expr.evalE_det (s : Shape) (o : Oracle) (env : Env) :
    ∀ (e : Expr) (evs : List Event), Det s o evs fun o => e.evalE s o env evs := by
  intro e
  induction e with
  | lit _ | bool _ | var _ | gidX | fst _ | snd _ | length _ =>
      intro evs
      exact Det.pure s o evs _
  | vec2 a b iha ihb | min a b iha ihb =>
      intro evs
      simp only [Expr.evalE]
      exact Det.andThen (iha evs) fun e1 _ => Det.andThen (ihb e1) fun e2 _ => Det.pure s o e2 _
  | not a ih | toF32 a ih | toU32 a ih | sqrt a ih | round a ih | abs a ih =>
      intro evs
      simp only [Expr.evalE]
      exact Det.andThen (ih evs) fun e1 _ => Det.pure s o e1 _
  | bin op a b iha ihb =>
      intro evs
      cases op
      case and | or =>
        simp only [Expr.evalE]
        refine Det.andThen (iha evs) fun e1 x => ?_
        cases x with
        | bool v =>
            cases v
            all_goals first
              | exact Det.pure s o e1 _
              | exact Det.andThen (ihb e1) fun e2 _ => Det.pure s o e2 _
        | _ => exact Det.pure s o e1 _
      all_goals
        simp only [Expr.evalE]
        exact Det.andThen (iha evs) fun e1 _ => Det.andThen (ihb e1) fun e2 _ => Det.pure s o e2 _
  | select f t c ihf iht ihc =>
      intro evs
      simp only [Expr.evalE]
      exact Det.andThen (ihf evs) fun e1 _ => Det.andThen (iht e1) fun e2 _ =>
        Det.andThen (ihc e2) fun e3 _ => Det.pure s o e3 _
  | index b p ih =>
      intro evs
      simp only [Expr.evalE]
      refine Det.andThen (ih evs) fun e1 x => ?_
      rcases hb : s.sizes[b]? with _ | n
      · cases x <;> exact Det.pure s o e1 _
      · cases x with
        | u32 i => exact Det.ite (fun hi => Det.read e1 hb hi) (fun _ => Det.pure s o e1 _)
        | _ => exact Det.pure s o e1 _

/-- A loop's runs are determined by the values of their reads when its test and body are. -/
theorem loopRunsE_det (s : Shape) (o : Oracle) (test : Oracle → Local → List Event → Res Bool)
    (body : Oracle → Local → List Event → Res Local)
    (ht : ∀ l evs, Det s o evs fun o => test o l evs)
    (hb : ∀ l evs, Det s o evs fun o => body o l evs) :
    ∀ fuel l evs, Det s o evs fun o => loopRunsE (test o) (body o) fuel l evs := by
  intro fuel
  induction fuel with
  | zero => intro l evs; exact Det.pure s o evs _
  | succ fuel ih =>
      intro l evs
      simp only [loopRunsE]
      refine Det.ite (fun _ => Det.pure s o evs _) (fun _ => ?_)
      refine Det.andThen (ht l evs) fun e1 c => ?_
      exact Det.ite (fun _ => Det.andThen (hb l e1) fun e2 l2 => ih l2 e2)
        (fun _ => Det.pure s o e1 _)

mutual
  /-- A statement's run is determined by the values of its reads. -/
  theorem Stmt.execE_det (s : Shape) (o : Oracle) : ∀ (st : Stmt) (l : Local) (evs : List Event),
      Det s o evs fun o => Stmt.execE s o l evs st
    | .let_ n ty e, l, evs | .var n ty e, l, evs | .assign n e, l, evs => by
        simp only [Stmt.execE]
        exact Det.andThen (Expr.evalE_det s o l.env e evs) fun e1 _ => Det.pure s o e1 _
    | .store b p e, l, evs => by
        simp only [Stmt.execE]
        refine Det.andThen (Expr.evalE_det s o l.env p evs) fun e1 x =>
          Det.andThen (Expr.evalE_det s o l.env e e1) fun e2 y => ?_
        cases x with
        | u32 i =>
            cases y with
            | u32 v =>
                exact Det.ite (fun hc => Det.write e2 v hc.2 _) (fun _ => Det.pure s o e2 _)
            | _ => exact Det.pure s o e2 _
        | _ => cases y <;> exact Det.pure s o e2 _
    | .ite c ts es, l, evs => by
        simp only [Stmt.execE]
        refine Det.andThen (Expr.evalE_det s o l.env c evs) fun e1 x => ?_
        cases x with
        | bool cv =>
            exact Det.andThen
              (Det.ite (fun _ => Stmt.execListE_det s o ts l e1)
                (fun _ => Stmt.execListE_det s o es l e1))
              fun e2 _ => Det.pure s o e2 _
        | _ => exact Det.pure s o e1 _
    | .while_ c body, l, evs => by
        simp only [Stmt.execE]
        refine loopRunsE_det s o _ _ (fun l evs => ?_) (fun l evs => ?_) loopBound l evs
        · exact Det.andThen (Expr.evalE_det s o l.env c evs) fun e1 _ => Det.pure s o e1 _
        · exact Det.andThen (Stmt.execListE_det s o body l evs) fun e1 _ => Det.pure s o e1 _
    | .ret, l, evs => Det.pure s o evs _

  /-- A statement list's run is determined by the values of its reads. -/
  theorem Stmt.execListE_det (s : Shape) (o : Oracle) :
      ∀ (sts : List Stmt) (l : Local) (evs : List Event),
        Det s o evs fun o => Stmt.execListE s o l evs sts
    | [], l, evs => Det.pure s o evs _
    | st :: rest, l, evs => by
        simp only [Stmt.execListE]
        exact Det.ite (fun _ => Det.pure s o evs _) (fun _ =>
          Det.andThen (Stmt.execE_det s o st l evs) fun e1 l1 => Stmt.execListE_det s o rest l1 e1)
end

/-- An invocation's events keep `Good`, and any oracle that gives its reads the same values gives
the same events and outcome. -/
theorem Module.invokeE_det (m : Module) (sizes : List Nat) (outputSize : Nat) (o : Oracle)
    (gid : UInt32) :
    Good ⟨gid, sizes, outputSize⟩ o (m.invokeE sizes outputSize o gid).1 ∧
      ∀ o', Answers o' (m.invokeE sizes outputSize o gid).1 →
        m.invokeE sizes outputSize o' gid = m.invokeE sizes outputSize o gid := by
  unfold Module.invokeE
  split
  · obtain ⟨x, y⟩ := Stmt.execListE_det ⟨gid, sizes, outputSize⟩ o m.body
      { env := [], returned := false } []
    exact ⟨x.good (Good.nil _ _), fun o' h => by simp only [y o' h]⟩
  · exact ⟨Good.nil _ _, fun _ _ => rfl⟩

end LeanExe.WGSL
