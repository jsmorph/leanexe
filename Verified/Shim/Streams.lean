module

public import Verified.Shim.Footprint

@[expose] public section

/-!
Runs that make no flat call.  `StreamTrace T` states that the WASI trace `T` holds no flat call,
and `StreamAction a` that the action `a` contains none, through every continuation.  An `Exec` or
`Prefix` run of such an action has such a trace (`Exec.streamTrace`, `Prefix.streamTrace`).  For
such a trace, the images that `Images` admits read none of the open flags, the layout, the
launch, and the earlier layer events (`Images.streams`), each layer event is a `read` or a
`write` (`Images.streamCalls`), and an `Exec` or `Prefix` run under `linuxHost F L I R` is one
under `linuxHost F' L' I' R` when the layouts agree on the guest's byte 0, the timespec, and the
`statx` record (`Exec.streams`, `Prefix.streams`), since such a run uses only the host's stream
relations and its exits, which read the layout only through `WritesWithin`.
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi Verified.Wasi

/-- The WASI trace `T` holds no flat call. -/
def StreamTrace (T : List Wasi.Event) : Prop :=
  ∀ e ∈ T, ∀ call args reply, e ≠ .sys call args reply

/-- The action makes no flat call, through every continuation. -/
def StreamAction : {α : Type} → Action α → Prop
  | _, .pure _ => True
  | _, .read _ next => ∀ r, StreamAction (next r)
  | _, .write _ _ next => ∀ r, StreamAction (next r)
  | _, .exit _ => True
  | _, .loop _ _ _ step next => (∀ i s, StreamAction (step i s)) ∧ ∀ s, StreamAction (next s)
  | _, .sys .. => False

theorem StreamTrace.nil : StreamTrace [] := fun _ h => nomatch h

theorem StreamTrace.cons {e : Wasi.Event} {T : List Wasi.Event}
    (he : ∀ call args reply, e ≠ .sys call args reply) (hT : StreamTrace T) :
    StreamTrace (e :: T) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact he
  · exact hT x hx

theorem StreamTrace.append {T T' : List Wasi.Event} (h : StreamTrace T) (h' : StreamTrace T') :
    StreamTrace (T ++ T') := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem StreamTrace.of_cons {e : Wasi.Event} {T : List Wasi.Event} (h : StreamTrace (e :: T)) :
    StreamTrace T := fun x hx => h x (List.mem_cons_of_mem e hx)

theorem StreamTrace.of_append_left {T T' : List Wasi.Event} (h : StreamTrace (T ++ T')) :
    StreamTrace T := fun x hx => h x (List.mem_append_left T' hx)

theorem StreamTrace.of_append_right {T T' : List Wasi.Event} (h : StreamTrace (T ++ T')) :
    StreamTrace T' := fun x hx => h x (List.mem_append_right T hx)

theorem StreamAction.bind {α β : Type} :
    ∀ (a : Action α) {f : α → Action β}, StreamAction a → (∀ x, StreamAction (f x)) →
      StreamAction (a.bind f)
  | .pure v, _, _, hf => hf v
  | .read _ next, _, ha, hf => fun r => StreamAction.bind (next r) (ha r) hf
  | .write _ _ next, _, ha, hf => fun r => StreamAction.bind (next r) (ha r) hf
  | .exit _, _, _, _ => trivial
  | .loop _ _ _ _ next, _, ha, hf => ⟨ha.1, fun s => StreamAction.bind (next s) (ha.2 s) hf⟩
  | .sys .., _, ha, _ => ha.elim

theorem StreamAction.resumeLoop {σ α : Type} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {next : σ → Action α} (hs : ∀ i s, StreamAction (step i s))
    (hn : ∀ s, StreamAction (next s)) :
    ∀ remaining index state, StreamAction (LeanExe.Wasi.resumeLoop test step next remaining index
      state)
  | 0, _, state => hn state
  | remaining + 1, index, state => by
    simp only [LeanExe.Wasi.resumeLoop]
    split
    · exact StreamAction.bind _ (hs _ _) fun s =>
        StreamAction.resumeLoop hs hn remaining (index + 1) s
    · exact hn state

/-- An `Exec` run of an action without flat calls has a trace without flat calls. -/
theorem Exec.streamTrace {World : Type} {host : Host World} {α : Type} {action : Action α}
    {world final : World} {trace : List Wasi.Event} {outcome : Outcome α}
    (h : Exec host action world trace outcome final) (ha : StreamAction action) :
    StreamTrace trace := by
  refine Exec.rec
    (motive_1 := fun {α} action _ trace _ _ _ => StreamAction action → StreamTrace trace)
    (motive_2 := fun {α σ} _ _ _ _ step next _ trace _ _ _ =>
      (∀ i s, StreamAction (step i s)) → (∀ s, StreamAction (next s)) → StreamTrace trace)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h ha
  · intro _ _ _ _
    exact StreamTrace.nil
  · intro _ _ _ _ _ _ _ _ _ ih ha
    exact ih (ha _)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih ha
    exact .cons (fun _ _ _ h => nomatch h) (ih (ha _))
  · intro _ _ _ _ _ _ _ _ _ _
    exact .cons (fun _ _ _ h => nomatch h) .nil
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih ha
    exact .cons (fun _ _ _ h => nomatch h) (ih (ha _))
  · intro _ _ _ _ _ _ _ _ _ _
    exact .cons (fun _ _ _ h => nomatch h) .nil
  · intro _ _ _ _ _ _
    exact .cons (fun _ _ _ h => nomatch h) .nil
  · intro _ _ _ _ _ _ _
    exact .cons (fun _ _ _ h => nomatch h) .nil
  · intro _ _ _ _ _ _ _ _ _ _ _ _ ih ha
    exact ih ha.1 ha.2
  · intro _ _ _ _ _ _ _ _ _ _ _ ha
    exact ha.elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha
    exact ha.elim
  · intro _ _ _ _ _ _ _ _ _ _ ha
    exact ha.elim
  · intro _ _ _ _ _ _ _ _ _ _ _ _ ih hs hn
    exact ih (hn _)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih hs hn
    exact ih (hn _)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ hs hn
    exact (ih₁ (hs _ _)).append (ih₂ hs hn)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih hs hn
    exact ih (hs _ _)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih hs hn
    exact ih (hs _ _)

/-- A `Prefix` run of an action whose continuation `next` makes no flat call has a trace without
flat calls and a residual whose continuation `next` makes none. -/
theorem Prefix.streamTrace_bind {World : Type} {host : Host World} {α : Type} {action : Action α}
    {world final : World} {trace : List Wasi.Event} {residual : Action α}
    (h : Prefix host action world trace residual final) :
    ∀ {β : Type} (next : α → Action β), StreamAction (action.bind next) →
      StreamTrace trace ∧ StreamAction (residual.bind next) := by
  induction h with
  | refl => exact fun _ ha => ⟨.nil, ha⟩
  | read_reject => exact fun _ ha => ⟨.nil, ha _⟩
  | read_return => exact fun _ ha => ⟨.cons (fun _ _ _ h => nomatch h) .nil, ha _⟩
  | write_return => exact fun _ ha => ⟨.cons (fun _ _ _ h => nomatch h) .nil, ha _⟩
  | loop =>
    intro _ next ha
    refine ⟨.nil, ?_⟩
    rw [resumeLoop_bind]
    exact StreamAction.resumeLoop ha.1 ha.2 _ _ _
  | bind _ ih =>
    intro _ next ha
    rw [Action.bind_assoc] at ha ⊢
    exact ih _ ha
  | trans _ _ ih₁ ih₂ =>
    intro _ next ha
    obtain ⟨t₁, a₁⟩ := ih₁ next ha
    obtain ⟨t₂, a₂⟩ := ih₂ next a₁
    exact ⟨t₁.append t₂, a₂⟩
  | sys_reject => exact fun _ ha => ha.elim
  | sys_return => exact fun _ ha => ha.elim

/-- A `Prefix` run of an action without flat calls has a trace without flat calls. -/
theorem Prefix.streamTrace {World : Type} {host : Host World} {α : Type} {action : Action α}
    {world final : World} {trace : List Wasi.Event} {residual : Action α}
    (h : Prefix host action world trace residual final) (ha : StreamAction action) :
    StreamTrace trace :=
  (Prefix.streamTrace_bind h Action.pure (by rw [Action.bind_pure]; exact ha)).1

/-- For a trace without flat calls, the images do not depend on the open flags, the layout, the
launch, or the earlier layer events. -/
theorem Images.streams {F F' : OpenFlags} {L L' : ShimLayout} {I I' : Launch}
    {events : List Linux.Event} {T : List Wasi.Event} {ls : List Linux.Event}
    (h : Images F L I events T ls) (hT : StreamTrace T) (events' : List Linux.Event) :
    Images F' L' I' events' T ls := by
  induction h generalizing events' with
  | nil => exact .nil
  | @cons events e l es ls image _ ih =>
    refine .cons ?_ (ih hT.of_cons _)
    have he := hT e (List.mem_cons_self ..)
    cases e with
    | read => exact image
    | write => exact image
    | exit => exact image
    | exitTrap => exact image
    | sys call args reply => exact absurd rfl (he call args reply)

/-- For a trace without flat calls, every layer event of the images is a `read` or a `write`. -/
theorem Images.streamCalls {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {T : List Wasi.Event} {ls : List Linux.Event}
    (h : Images F L I events T ls) (hT : StreamTrace T) :
    ∀ x ∈ ls, x.call = Linux.readCall ∨ x.call = Linux.writeCall := by
  induction h with
  | nil => exact fun _ hx => nomatch hx
  | @cons events e l es ls image _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have he := hT e (List.mem_cons_self ..)
      cases e with
      | read =>
        obtain ⟨y, _, rfl, hy, _⟩ := image
        obtain rfl := List.mem_singleton.mp hx
        exact .inl hy
      | write =>
        obtain ⟨y, _, rfl, hy, _⟩ := image
        obtain rfl := List.mem_singleton.mp hx
        exact .inr hy
      | exit =>
        change l = [] at image
        subst image
        exact nomatch hx
      | exitTrap =>
        change l = [] at image
        subst image
        exact nomatch hx
      | sys call args reply => exact absurd rfl (he call args reply)
    · exact ih hT.of_cons x hx

/-- A `read` or `write` step of `linuxHost` under one choice of open flags, layout, and launch is
one under another whose layout has the same guest's byte 0, timespec, and `statx` record. -/
theorem shimStep_streams {F F' : OpenFlags} {L L' : ShimLayout} {I I' : Launch}
    {R : Linux.Replies} (hbase : L'.base = L.base) (htime : L'.timespec = L.timespec)
    (hstatx : L'.statx = L.statx) {w w' : LinuxWorld} {e : Wasi.Event}
    (he : ∀ call args reply, e ≠ .sys call args reply)
    (h : ShimStep F L I R w e w') : ShimStep F' L' I' R w e w' := by
  obtain ⟨l, image, carried, within, rfl⟩ := h
  have hw : ∀ x, WritesWithin L (2 ^ 32) x → WritesWithin L' (2 ^ 32) x := by
    intro x hx g hg
    have hoff : L'.offset g.1 = L.offset g.1 := by simp only [ShimLayout.offset, hbase]
    rw [hoff, htime, hstatx]
    exact hx g hg
  refine ⟨l, ?_, carried, fun x hx => hw x (within x hx), rfl⟩
  cases e with
  | read => exact image
  | write => exact image
  | exit => exact image
  | exitTrap => exact image
  | sys call args reply => exact absurd rfl (he call args reply)

/-- An `Exec` run without flat calls under `linuxHost F L I R` is one under `linuxHost F' L' I' R`
when the layouts have the same guest's byte 0, timespec, and `statx` record. -/
theorem Exec.streams {F F' : OpenFlags} {L L' : ShimLayout} {I I' : Launch} {R : Linux.Replies}
    (hbase : L'.base = L.base) (htime : L'.timespec = L.timespec) (hstatx : L'.statx = L.statx)
    {α : Type}
    {action : Action α} {world final : LinuxWorld} {trace : List Wasi.Event}
    {outcome : Outcome α} (h : Exec (linuxHost F L I R) action world trace outcome final)
    (hT : StreamTrace trace) : Exec (linuxHost F' L' I' R) action world trace outcome final := by
  have step := @shimStep_streams F F' L L' I I' R hbase htime hstatx
  refine Exec.rec
    (motive_1 := fun {α} action world trace outcome final _ =>
      StreamTrace trace → Exec (linuxHost F' L' I' R) action world trace outcome final)
    (motive_2 := fun {α σ} remaining index state test step next world trace outcome final _ =>
      StreamTrace trace → LoopExec (linuxHost F' L' I' R) remaining index state test step next
        world trace outcome final)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h hT
  · intro _ world value _
    exact .pure world value
  · intro _ _ _ _ _ _ _ hCapacity _ ih hT
    exact .read_reject hCapacity (ih hT)
  · intro _ _ _ _ _ _ _ _ _ _ _ hCapacity hHost hRange hPrefix _ ih hT
    exact .read_return hCapacity (step (fun _ _ _ h => nomatch h) hHost) hRange hPrefix
      (ih hT.of_cons)
  · intro _ _ _ _ _ _ _ hCapacity hHost _
    exact .read_trap hCapacity (step (fun _ _ _ h => nomatch h) hHost)
  · intro _ _ _ _ _ _ _ _ _ _ _ hHost _ ih hT
    exact .write_return (step (fun _ _ _ h => nomatch h) hHost) (ih hT.of_cons)
  · intro _ _ _ _ _ _ _ _ hHost _
    exact .write_trap (step (fun _ _ _ h => nomatch h) hHost)
  · intro _ _ _ _ hHost _
    exact .exit hHost
  · intro _ _ _ _ _ hHost _
    exact .exitTrap hHost
  · intro _ _ _ _ _ _ _ _ _ _ _ _ ih hT
    exact .loop (ih hT)
  · intro _ _ _ _ _ _ _ _ hFits _ ih hT
    exact .sys_reject hFits (ih hT)
  · intro _ call args _ _ _ _ _ _ errno committed _ _ _ _ hT
    exact absurd rfl (hT _ (List.mem_cons_self ..) call args (.returned errno committed))
  · intro _ call args _ _ _ message committed _ _ hT
    exact absurd rfl (hT _ (List.mem_cons_self ..) call args (.trapped message committed))
  · intro _ _ _ _ _ _ _ _ _ _ _ _ ih hT
    exact .zero (ih hT)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ hTest _ ih hT
    exact .stop hTest (ih hT)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTest _ _ ih₁ ih₂ hT
    exact .next hTest (ih₁ hT.of_append_left) (ih₂ hT.of_append_right)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ hTest _ ih hT
    exact .exit hTest (ih hT)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ hTest _ ih hT
    exact .trap hTest (ih hT)

/-- A `Prefix` run without flat calls under `linuxHost F L I R` is one under
`linuxHost F' L' I' R` when the layouts have the same guest's byte 0, timespec, and `statx`
record. -/
theorem Prefix.streams {F F' : OpenFlags} {L L' : ShimLayout} {I I' : Launch} {R : Linux.Replies}
    (hbase : L'.base = L.base) (htime : L'.timespec = L.timespec) (hstatx : L'.statx = L.statx)
    {α : Type}
    {action residual : Action α} {world final : LinuxWorld} {trace : List Wasi.Event}
    (h : Prefix (linuxHost F L I R) action world trace residual final) (hT : StreamTrace trace) :
    Prefix (linuxHost F' L' I' R) action world trace residual final := by
  have step := @shimStep_streams F F' L L' I I' R hbase htime hstatx
  induction h with
  | refl => exact .refl _ _
  | read_reject hCapacity => exact .read_reject hCapacity
  | read_return hCapacity hHost hRange hPrefix =>
    exact .read_return hCapacity (step (fun _ _ _ h => nomatch h) hHost) hRange hPrefix
  | write_return hHost => exact .write_return (step (fun _ _ _ h => nomatch h) hHost)
  | loop => exact .loop
  | bind _ ih => exact .bind (ih hT)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hT.of_append_left) (ih₂ hT.of_append_right)
  | sys_reject hFits => exact .sys_reject hFits
  | sys_return _ _ =>
    exact absurd rfl (hT _ (List.mem_singleton_self _) _ _ (.returned _ _))

end Verified.Shim
