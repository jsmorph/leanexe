import LeanExe.PTX.Semantics
import LeanExe.ProofKit.Writes

/-!
Properties of a thread's run under every oracle.  A result's events extend the events before it,
its loads lie within their input buffers, and its stores lie within the output.  A result is
determined by the values its loads return: another oracle that gives those loads the same values
gives the same result, whether the thread ends or stops.
-/

namespace LeanExe.PTX

def Event.write? : Event → Option (Nat × UInt64)
  | .write i v => some (i, v)
  | .read .. => none

/-- The stores among events. -/
def writesOf (evs : List Event) : List (Nat × UInt64) := evs.filterMap Event.write?

@[simp] theorem writesOf_nil : writesOf [] = [] := rfl

@[simp] theorem writesOf_append (a b : List Event) :
    writesOf (a ++ b) = writesOf a ++ writesOf b := by
  simp [writesOf]

/-- Oracle `o` gives every read of `evs` the value that the read returned. -/
def Answers (o : Oracle) (evs : List Event) : Prop :=
  ∀ (k b i : Nat) (w : UInt64), evs[k]? = some (.read b i w) → o k b i = w

/-- Each read of `evs` returned the value of oracle `o` and lies within its input buffer, and each
write lies within the output. -/
structure Good (s : Shape) (o : Oracle) (evs : List Event) : Prop where
  read : ∀ (k b i : Nat) (w : UInt64), evs[k]? = some (.read b i w) →
    o k b i = w ∧ ∃ n, s.sizes[b]? = some n ∧ i < n
  write : ∀ (k i : Nat) (w : UInt64), evs[k]? = some (Event.write i w) → i < s.outputSize

theorem Answers.of_prefix {o : Oracle} {evs evs' : List Event} (h : Answers o evs')
    (hp : ∃ new, evs' = evs ++ new) : Answers o evs := by
  obtain ⟨new, rfl⟩ := hp
  exact fun k b i w hk => h k b i w (getElem?_append_some new hk)

theorem Good.nil (s : Shape) (o : Oracle) : Good s o [] :=
  ⟨fun _ _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩

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

/-- A load at word `k` of input buffer `j`, whose result is any function of the loaded value. -/
theorem Det.read {s : Shape} {o : Oracle} (evs : List Event) {j k n : Nat}
    (hj : s.sizes[j]? = some n) (hk : k < n) (f : UInt64 → Option α) :
    Det s o evs fun o => (evs ++ [.read j k (o evs.length j k)], f (o evs.length j k)) := by
  refine ⟨⟨⟨_, rfl⟩, fun h => ⟨fun p b i w hp => ?_, fun p i w hp => ?_⟩⟩, fun o' h => ?_⟩
  · rcases getElem?_append_singleton hp with hp | ⟨rfl, he⟩
    · exact h.read p b i w hp
    · cases he
      exact ⟨rfl, n, hj, hk⟩
  · rcases getElem?_append_singleton hp with hp | ⟨-, he⟩
    · exact h.write p i w hp
    · cases he
  · have : o' evs.length j k = o evs.length j k := h _ _ _ _ (by simp)
    simp only [this]

/-- A store of word `k` of the output. -/
theorem Det.write {s : Shape} {o : Oracle} (evs : List Event) {k : Nat} (v : UInt64)
    (hk : k < s.outputSize) (x : Option α) : Det s o evs fun _ => (evs ++ [.write k v], x) := by
  refine ⟨⟨⟨_, rfl⟩, fun h => ⟨fun p b i w hp => ?_, fun p i w hp => ?_⟩⟩, fun _ _ => rfl⟩
  · rcases getElem?_append_singleton hp with hp | ⟨-, he⟩
    · exact h.read p b i w hp
    · cases he
  · rcases getElem?_append_singleton hp with hp | ⟨-, he⟩
    · exact h.write p i w hp
    · cases he
      exact hk

theorem wordAt_lt {size : Nat} {off imm : UInt64} {k : Nat} (h : wordAt size off imm = some k) :
    k < size := by
  simp only [wordAt] at h
  split at h
  · cases h
    omega
  · cases h

/-- An instruction's result is determined by the value of its load. -/
theorem Instr.exec_det (s : Shape) (o : Oracle) (l : Local) (evs : List Event) (i : Instr) :
    Det s o evs fun o => i.exec s o l evs := by
  cases i with
  | ld d a imm =>
      simp only [Instr.exec]
      rcases l.r64 a with _ | (_ | ⟨j, off⟩) <;> (try dsimp only)
      · exact Det.pure s o evs _
      · exact Det.pure s o evs _
      · rcases hj : s.sizes[j]? with _ | size <;> (try dsimp only)
        · exact Det.pure s o evs _
        · rcases hk : wordAt size off imm with _ | k <;> (try dsimp only)
          · exact Det.pure s o evs _
          · exact Det.read evs hj (wordAt_lt hk) fun v => some (l.set64 d (.word v))
  | st a imm v =>
      simp only [Instr.exec]
      rcases l.r64 a with _ | (_ | ⟨j, off⟩) <;> rcases l.word v with _ | x <;> (try dsimp only)
      all_goals try exact Det.pure s o evs _
      by_cases hj : j = s.sizes.length
      · simp only [hj, ↓reduceIte]
        rcases hk : wordAt s.outputSize off imm with _ | k
        · exact Det.pure s o evs _
        · exact Det.write evs x (wordAt_lt hk) _
      · simp only [hj, ↓reduceIte]
        exact Det.pure s o evs _
  | _ => exact Det.pure s o evs _

/-- A loop's runs are determined by the values of their loads when its condition and body are. -/
theorem loopRuns_det (s : Shape) (o : Oracle) (cond body : Oracle → Local → List Event → Res Local)
    (p : Nat) (hc : ∀ l evs, Det s o evs fun o => cond o l evs)
    (hb : ∀ l evs, Det s o evs fun o => body o l evs) :
    ∀ fuel l evs, Det s o evs fun o => loopRuns (cond o) (body o) p fuel l evs := by
  intro fuel
  induction fuel with
  | zero => intro l evs; exact Det.pure s o evs _
  | succ fuel ih =>
      intro l evs
      simp only [loopRuns]
      by_cases hr : l.returned
      · simp only [hr, ↓reduceIte]
        exact Det.pure s o evs _
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        refine Det.andThen (hc l evs) fun e1 l1 => ?_
        by_cases hr1 : l1.returned
        · simp only [hr1, ↓reduceIte]
          exact Det.pure s o e1 _
        · simp only [hr1, Bool.false_eq_true, ↓reduceIte]
          rcases l1.rp p with _ | (_ | _)
          · exact Det.pure s o e1 _
          · exact Det.pure s o e1 _
          · exact Det.andThen (hb l1 e1) fun e2 l2 => ih l2 e2

mutual
  /-- A statement's run is determined by the values of its loads. -/
  theorem Stmt.exec_det (s : Shape) (o : Oracle) : ∀ (st : Stmt) (l : Local) (evs : List Event),
      Det s o evs fun o => Stmt.exec s o l evs st
    | .instr none i, l, evs => Instr.exec_det s o l evs i
    | .instr (some g) i, l, evs => by
        simp only [Stmt.exec]
        rcases g.holds l with _ | (_ | _)
        · exact Det.pure s o evs _
        · exact Det.pure s o evs _
        · exact Instr.exec_det s o l evs i
    | .ite p ts es, l, evs => by
        simp only [Stmt.exec]
        rcases l.rp p with _ | (_ | _)
        · exact Det.pure s o evs _
        · exact Stmt.execList_det s o es l evs
        · exact Stmt.execList_det s o ts l evs
    | .while_ cond p body, l, evs => by
        simp only [Stmt.exec]
        exact loopRuns_det s o (fun o l evs => Stmt.execList s o l evs cond)
          (fun o l evs => Stmt.execList s o l evs body) p
          (fun l evs => Stmt.execList_det s o cond l evs)
          (fun l evs => Stmt.execList_det s o body l evs) loopBound l evs
    | .ret, l, evs => Det.pure s o evs _

  /-- A statement list's run is determined by the values of its loads. -/
  theorem Stmt.execList_det (s : Shape) (o : Oracle) :
      ∀ (sts : List Stmt) (l : Local) (evs : List Event),
        Det s o evs fun o => Stmt.execList s o l evs sts
    | [], l, evs => Det.pure s o evs _
    | st :: rest, l, evs => by
        simp only [Stmt.execList]
        by_cases hr : l.returned
        · simp only [hr, ↓reduceIte]
          exact Det.pure s o evs _
        · simp only [hr, Bool.false_eq_true, ↓reduceIte]
          exact Det.andThen (Stmt.exec_det s o st l evs) fun e1 l1 =>
            Stmt.execList_det s o rest l1 e1
end

/-- A thread's events keep `Good`, and any oracle that gives its loads the same values gives the
same events and outcome. -/
theorem Module.invoke_det (m : Module) (sizes : List Nat) (outputSize block : Nat) (o : Oracle)
    (g : Nat) :
    Good (threadShape sizes outputSize block g) o (m.invoke sizes outputSize block o g).1 ∧
      ∀ o', Answers o' (m.invoke sizes outputSize block o g).1 →
        m.invoke sizes outputSize block o' g = m.invoke sizes outputSize block o g := by
  unfold Module.invoke
  split
  · obtain ⟨x, y⟩ := Stmt.execList_det (threadShape sizes outputSize block g) o m.body
      Local.initial []
    exact ⟨x.good (Good.nil _ _), fun o' h => by simp only [y o' h]⟩
  · exact ⟨Good.nil _ _, fun _ _ => rfl⟩

end LeanExe.PTX
