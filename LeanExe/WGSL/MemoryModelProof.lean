import LeanExe.WGSL.EventsInput
import LeanExe.WGSL.MemoryModel

/-!
A race-free dispatch under the memory model of `MemoryModel.lean`.  In every consistent execution
each read of an invocation returns the input word, so each invocation runs as it does with the
initial buffers: it ends, and it writes the stores of `Module.invoke`.  The execution has no data
race, and each read after the dispatch returns the word of `Module.dispatch`'s output.  A
consistent execution exists.
-/

namespace LeanExe.WGSL

theorem byteOf_ext {a b : UInt32} (h : ∀ k, byteOf k a = byteOf k b) : a = b := by
  have h0 : a.toNat % 256 = b.toNat % 256 := by simpa [byteOf] using h ⟨0, by omega⟩
  have h1 : a.toNat / 256 % 256 = b.toNat / 256 % 256 := by simpa [byteOf] using h ⟨1, by omega⟩
  have h2 : a.toNat / 65536 % 256 = b.toNat / 65536 % 256 := by
    simpa [byteOf] using h ⟨2, by omega⟩
  have h3 : a.toNat / 16777216 % 256 = b.toNat / 16777216 % 256 := by
    simpa [byteOf] using h ⟨3, by omega⟩
  have ha := UInt32.toNat_lt a
  have hb := UInt32.toNat_lt b
  exact UInt32.toNat_inj.mp (by omega)

/-! ### The writes of a dispatch -/

theorem Module.dispatch_apply {m : Module} {inputs : List (Array UInt32)} {output : Array UInt32}
    (W : Nat → List (Nat × UInt32)) :
    ∀ count, (∀ g, g < count → m.invoke inputs output.size (UInt32.ofNat g) = some (W g)) →
      m.dispatch inputs output count =
        some (applyWrites output ((List.range count).flatMap W)) := by
  intro count
  induction count with
  | zero => intro _; rfl
  | succ n ih =>
      intro hW
      unfold Module.dispatch at ih ⊢
      rw [List.range_succ, List.foldlM_append, ih fun g hg => hW g (by omega)]
      simp [hW n (by omega), applyWrites, List.foldl_append]

theorem Module.dispatch_steps {m : Module} {inputs : List (Array UInt32)} {output : Array UInt32} :
    ∀ {count : Nat} {out : Array UInt32}, m.dispatch inputs output count = some out →
      ∀ g, g < count → (m.invoke inputs output.size (UInt32.ofNat g)).isSome
  | 0, _, _, g, hg => absurd hg (by omega)
  | n + 1, out, h, g, hg => by
      unfold Module.dispatch at h
      rw [List.range_succ, List.foldlM_append] at h
      simp only [Option.bind_eq_bind] at h
      obtain ⟨s, hs, hn⟩ := Option.bind_eq_some_iff.mp h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | rfl
      · exact Module.dispatch_steps hs g hg
      · simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind] at hn
        cases hi : m.invoke inputs output.size (UInt32.ofNat g)
        · simp [hi] at hn
        · rfl

theorem mem_writesOf {evs : List Event} {p i : Nat} {w : UInt32}
    (h : evs[p]? = some (Event.write i w)) : (i, w) ∈ writesOf evs :=
  List.mem_filterMap.mpr ⟨_, List.mem_iff_getElem?.mpr ⟨p, h⟩, rfl⟩

theorem writesOf_mem {evs : List Event} {w : Nat × UInt32} (h : w ∈ writesOf evs) :
    ∃ p : Nat, evs[p]? = some (Event.write w.1 w.2) := by
  obtain ⟨e, he, hw⟩ := List.mem_filterMap.mp h
  cases e with
  | read => cases hw
  | write j v =>
      cases hw
      exact List.mem_iff_getElem?.mp he

theorem lastVal_no_write {evs : List Event} {i : Nat}
    (h : ∀ (p : Nat) (w : UInt32), evs[p]? ≠ some (Event.write i w)) (v : UInt32) :
    lastVal (writesOf evs) i v = v :=
  lastVal_of_forall (fun w hw hi => by
    obtain ⟨p, hp⟩ := writesOf_mem hw
    exact h p w.2 (hi ▸ hp)) v

/-- The last write to word `i` among events: its position, and its value as `lastVal`. -/
theorem last_write {i : Nat} : ∀ (evs : List Event) (v : UInt32),
    (∃ (p : Nat) (w : UInt32), evs[p]? = some (Event.write i w)) →
      ∃ pm : Nat, evs[pm]? = some (Event.write i (lastVal (writesOf evs) i v)) ∧
        ∀ (q : Nat) (w : UInt32), evs[q]? = some (Event.write i w) → q ≤ pm
  | [], _, ⟨_, _, h⟩ => by simp at h
  | e :: rest, v, hex => by
      have hcons : lastVal (writesOf (e :: rest)) i v = lastVal (writesOf rest) i
          (match e with
            | .write j w => if j = i then w else v
            | .read .. => v) := by
        cases e <;> rfl
      rw [hcons]
      by_cases hr : ∃ (p : Nat) (w : UInt32), rest[p]? = some (Event.write i w)
      · obtain ⟨pm, h1, h2⟩ := last_write rest _ hr
        refine ⟨pm + 1, by simpa using h1, fun q w hq => ?_⟩
        cases q with
        | zero => omega
        | succ q =>
            have := h2 q w (by simpa using hq)
            omega
      · obtain ⟨p, w0, hp⟩ := hex
        cases p with
        | succ p => exact absurd ⟨p, w0, by simpa using hp⟩ hr
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst hp
            refine ⟨0, ?_, fun q w hq => ?_⟩
            · simp [lastVal_no_write (fun p w hp => hr ⟨p, w, hp⟩)]
            · cases q with
              | zero => exact Nat.le_refl 0
              | succ q => exact absurd ⟨q, w, by simpa using hq⟩ hr

/-- Word `i` of a race-free dispatch's output, for events whose writes are the stores of
`Module.invoke`: the last write to `i` of the one invocation that writes `i`, or the initial word
when no invocation writes `i`. -/
theorem Dispatch.output_word (d : Dispatch) {out : Array UInt32}
    (h : d.module.dispatch d.inputs d.output d.count = some out)
    (hr : d.module.RaceFree d.inputs d.output.size d.count) (evs : Nat → List Event)
    (hW : ∀ g, g < d.count →
      d.module.invoke d.inputs d.output.size (UInt32.ofNat g) = some (writesOf (evs g)))
    {i : Nat} (hi : i < d.output.size) :
    (∃ (g0 pm : Nat) (v : UInt32), g0 < d.count ∧ (evs g0)[pm]? = some (Event.write i v) ∧
        out[i]? = some v ∧ ∀ (g p : Nat) (w : UInt32), g < d.count →
          (evs g)[p]? = some (Event.write i w) → g = g0 ∧ p ≤ pm) ∨
      ((∀ (g p : Nat) (w : UInt32), g < d.count → (evs g)[p]? ≠ some (Event.write i w)) ∧
        out[i]? = some d.output[i]) := by
  have hout := Module.dispatch_apply (fun g => writesOf (evs g)) d.count hW
  rw [h, Option.some.injEq] at hout
  have hget : (applyWrites d.output ((List.range d.count).flatMap fun g => writesOf (evs g)))[i]? =
      some (lastVal ((List.range d.count).flatMap fun g => writesOf (evs g)) i d.output[i]) :=
    setAll_get hi _
  rw [← hout] at hget
  by_cases hex : ∃ (g0 p : Nat) (w : UInt32), g0 < d.count ∧ (evs g0)[p]? = some (Event.write i w)
  · obtain ⟨g0, p0, w0, hg0, hp0⟩ := hex
    have huniq : ∀ (g p : Nat) (w : UInt32), g < d.count →
        (evs g)[p]? = some (Event.write i w) → g = g0 := by
      intro g p w hg hp
      by_cases hne : g = g0
      · exact hne
      · exact (hr g g0 hg hg0 hne _ _ (hW g hg) (hW g0 hg0) _ (mem_writesOf hp) _
          (mem_writesOf hp0) rfl).elim
    obtain ⟨pm, hpm, hmax⟩ := last_write (evs g0) d.output[i] ⟨p0, w0, hp0⟩
    refine Or.inl ⟨g0, pm, _, hg0, hpm, ?_, fun g p w hg hp => ?_⟩
    · rw [hget, lastVal_flatMap _ i g0 d.count (fun g hg hne w hw hwi => by
          obtain ⟨p, hp⟩ := writesOf_mem hw
          exact hne (huniq g p w.2 hg (hwi ▸ hp))) _ d.count (Nat.le_refl _)]
      simp [hg0]
    · have hg := huniq g p w hg hp
      subst hg
      exact ⟨rfl, hmax p w hp⟩
  · refine Or.inr ⟨fun g p w hg hp => hex ⟨g, p, w, hg, hp⟩, ?_⟩
    rw [hget, lastVal_flatMap _ i d.count d.count (fun g hg _ w hw hwi => by
        obtain ⟨p, hp⟩ := writesOf_mem hw
        exact hex ⟨g, p, w.2, hg, hwi ▸ hp⟩) _ d.count (Nat.le_refl _)]
    simp

/-! ### Accesses -/

theorem Dispatch.access_inv {d : Dispatch} {E : Execution} {g p : Nat} {a : Access}
    (h : d.access E (.inv g p) = some a) :
    g < d.count ∧ ∃ e, (d.events (E.oracle g) g).1[p]? = some e ∧
      a = e.access d.inputs.length := by
  simp only [Dispatch.access] at h
  split at h
  · rename_i hg
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hg, e, he, rfl⟩
  · cases h

theorem Dispatch.access_inv_of {d : Dispatch} {E : Execution} {g p : Nat} {e : Event}
    (hg : g < d.count) (he : (d.events (E.oracle g) g).1[p]? = some e) :
    d.access E (.inv g p) = some (e.access d.inputs.length) := by
  simp [Dispatch.access, hg, he]

theorem Dispatch.access_init {d : Dispatch} {E : Execution} {loc : Loc} {a : Access}
    (h : d.access E (.init loc) = some a) : a.loc = loc ∧ a.write = true := by
  obtain ⟨b, i⟩ := loc
  simp only [Dispatch.access, Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem Dispatch.access_init_input {d : Dispatch} {E : Execution} {b i : Nat}
    {buf : Array UInt32} (hb : d.inputs[b]? = some buf) (hi : i < buf.size) :
    d.access E (.init (b, i)) = some ⟨(b, i), buf[i], true⟩ := by
  have hlt : b < d.inputs.length := (List.getElem?_eq_some_iff.mp hb).1
  simp [Dispatch.access, Dispatch.buffers, List.getElem?_append_left hlt, hb, hi]

theorem Dispatch.access_init_output {d : Dispatch} {E : Execution} {i : Nat}
    (hi : i < d.output.size) :
    d.access E (.init (d.inputs.length, i)) = some ⟨(d.inputs.length, i), d.output[i], true⟩ := by
  simp [Dispatch.access, Dispatch.buffers, hi]

theorem Dispatch.access_obs {d : Dispatch} {E : Execution} {i : Nat} {a : Access}
    (h : d.access E (.obs i) = some a) :
    i < d.output.size ∧ a = ⟨(d.inputs.length, i), E.observed i, false⟩ := by
  simp only [Dispatch.access] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

theorem Dispatch.access_before {d : Dispatch} {E : Execution} {n : Nat} {a : Access}
    (h : d.access E (.before n) = some a) : a.write = true := by
  simp only [Dispatch.access, Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem Dispatch.access_after {d : Dispatch} {E : Execution} {n : Nat} {a : Access}
    (h : d.access E (.after n) = some a) : a.write = true := by
  simp only [Dispatch.access, Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem Dispatch.read_bounds {d : Dispatch} {o : Oracle} {g p b i : Nat} {w : UInt32}
    (h : (d.events o g).1[p]? = some (Event.read b i w)) :
    ∃ buf, d.inputs[b]? = some buf ∧ i < buf.size := by
  unfold Dispatch.events at h
  obtain ⟨-, n, hn, hi⟩ := (d.module.invokeE_det _ _ o _).1.read p b i w h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
  obtain ⟨buf, hbuf, rfl⟩ := hn
  exact ⟨buf, hbuf, hi⟩

theorem Dispatch.read_binding {d : Dispatch} {o : Oracle} {g p b i : Nat} {w : UInt32}
    (h : (d.events o g).1[p]? = some (Event.read b i w)) : b < d.inputs.length := by
  obtain ⟨buf, hbuf, -⟩ := Dispatch.read_bounds h
  exact (List.getElem?_eq_some_iff.mp hbuf).1

/-- A write is visible-to a read when every other write to the location is location-ordered
before the write or after the read. -/
theorem Dispatch.Consistent.visible {d : Dispatch} {E : Execution} (hE : d.Consistent E)
    {k : Fin 4} {x y : Op} {ax ay : Access} (hx : d.access E x = some ax)
    (hy : d.access E y = some ay) (hxw : ax.write = true) (hyw : ay.write = false)
    (hloc : ax.loc = ay.loc) (hxy : E.lo k x y)
    (hz : ∀ z az, z ≠ x → d.access E z = some az → az.write = true → az.loc = ax.loc →
      E.lo k z x ∨ E.lo k y z) :
    d.VisibleTo E k x y :=
  ⟨ax, ay, hx, hy, hxw, hyw, hloc, hxy, fun z az hne haz hw hl ⟨h1, h2⟩ => by
    rcases hz z az hne haz hw hl with h | h
    · exact hE.acyclic k x (.tail (.single h1) h)
    · exact hE.acyclic k z (.tail (.single h2) h)⟩

/-- In a consistent execution, a read of an invocation returns the input word. -/
theorem Dispatch.Consistent.read_input {d : Dispatch} {E : Execution} (hE : d.Consistent E)
    {g p b i : Nat} {w : UInt32} (hg : g < d.count)
    (hp : (d.events (E.oracle g) g).1[p]? = some (Event.read b i w)) :
    d.inputs[b]?.bind (·[i]?) = some w := by
  obtain ⟨buf, hbuf, hi⟩ := Dispatch.read_bounds hp
  have hb := Dispatch.read_binding hp
  have hx : d.access E (.init (b, i)) = some ⟨(b, i), buf[i], true⟩ :=
    Dispatch.access_init_input hbuf hi
  have hy : d.access E (.inv g p) = some ⟨(b, i), w, false⟩ := Dispatch.access_inv_of hg hp
  have hv : ∀ k, byteOf k w = byteOf k buf[i] := fun k =>
    hE.value k _ _ _ _ (hE.visible hx hy rfl rfl rfl
      (hE.phase k _ _ _ _ hx hy rfl (by simp [Op.phase]) (Or.inl rfl))
      fun z az hne haz hw hl => by
        cases z with
        | before n => exact Or.inl (hE.phase k _ _ _ _ haz hx hl (by simp [Op.phase]) (Or.inl hw))
        | init loc =>
            obtain ⟨hloc, -⟩ := Dispatch.access_init haz
            exact absurd (by rw [← hloc, hl]) hne
        | inv g' p' =>
            obtain ⟨-, e, -, rfl⟩ := Dispatch.access_inv haz
            cases e with
            | read => cases hw
            | write j v =>
                simp only [Event.access, Prod.mk.injEq] at hl
                omega
        | obs i' => cases (Dispatch.access_obs haz).2 ▸ hw
        | after n =>
            exact Or.inr (hE.phase k _ _ _ _ hy haz (hl ▸ rfl) (by simp [Op.phase]) (Or.inr hw)))
      hx hy
  rw [byteOf_ext hv]
  simp [hbuf, hi]

/-! ### The theorems -/

/-- In every consistent execution of a race-free dispatch that `Module.dispatch` computes, every
invocation runs as it does with the initial buffers and ends, there is no data race, and the
reads after the dispatch return the words of `Module.dispatch`'s output. -/
theorem Dispatch.executions (d : Dispatch) {out : Array UInt32}
    (h : d.module.dispatch d.inputs d.output d.count = some out)
    (hr : d.module.RaceFree d.inputs d.output.size d.count) (E : Execution)
    (hE : d.Consistent E) :
    (∀ g, g < d.count → d.events (E.oracle g) g = d.events (inputOracle d.inputs) g ∧
      (d.events (E.oracle g) g).2 = true) ∧
      d.NoDataRace E ∧ ∀ i, i < d.output.size → out[i]? = some (E.observed i) := by
  have hagree : ∀ g, g < d.count → d.events (E.oracle g) g = d.events (inputOracle d.inputs) g :=
    fun g hg => d.module.invokeE_agree _ _ _ _ fun p b i w hp => hE.read_input hg hp
  have hinv : ∀ g, g < d.count → (d.events (E.oracle g) g).2 = true ∧
      d.module.invoke d.inputs d.output.size (UInt32.ofNat g) =
        some (writesOf (d.events (E.oracle g) g).1) := by
    intro g hg
    rw [hagree g hg]
    have hs := Module.dispatch_steps h g hg
    have he := d.module.invokeE_input d.inputs d.output.size (UInt32.ofNat g)
    unfold Dispatch.events
    cases hc : (d.module.invokeE (d.inputs.map (·.size)) d.output.size (inputOracle d.inputs)
        (UInt32.ofNat g)).2
    · rw [he, hc] at hs
      simp at hs
    · exact ⟨rfl, by rw [he, hc]; rfl⟩
  refine ⟨fun g hg => ⟨hagree g hg, (hinv g hg).1⟩, ?_, ?_⟩
  · intro k x y ax ay hne hph hx hy hloc hw
    rcases Nat.lt_trichotomy x.phase y.phase with hlt | heq | hgt
    · exact Or.inl (hE.phase k x y ax ay hx hy hloc hlt hw)
    · have h2 : x.phase = 2 ∧ y.phase = 2 := by omega
      obtain ⟨g, p, rfl⟩ : ∃ g p, x = .inv g p := by
        cases x <;> simp [Op.phase] at h2 ⊢
      obtain ⟨g', q, rfl⟩ : ∃ g p, y = .inv g p := by
        cases y <;> simp [Op.phase] at h2 ⊢
      by_cases hgg : g = g'
      · subst hgg
        have hpq : p ≠ q := fun hpq => hne (by rw [hpq])
        rcases Nat.lt_or_gt_of_ne hpq with hpq | hpq
        · exact Or.inl (hE.program k g p q ax ay hx hy hloc hpq)
        · exact Or.inr (hE.program k g q p ay ax hy hx hloc.symm hpq)
      · exfalso
        obtain ⟨hg, e, he, rfl⟩ := Dispatch.access_inv hx
        obtain ⟨hg', e', he', rfl⟩ := Dispatch.access_inv hy
        cases e with
        | read b i v =>
            have hb := Dispatch.read_binding he
            cases e' with
            | read => simp [Event.access] at hw
            | write j v' =>
                simp only [Event.access, Prod.mk.injEq] at hloc
                omega
        | write j v =>
            cases e' with
            | read b i v' =>
                have hb := Dispatch.read_binding he'
                simp only [Event.access, Prod.mk.injEq] at hloc
                omega
            | write j' v' =>
                simp only [Event.access, Prod.mk.injEq] at hloc
                exact hr g g' hg hg' hgg _ _ (hinv g hg).2 (hinv g' hg').2 _ (mem_writesOf he) _
                  (mem_writesOf he') hloc.2
    · exact Or.inr (hE.phase k y x ay ax hy hx hloc.symm hgt hw.symm)
  · intro i hi
    have hy : d.access E (.obs i) = some ⟨(d.inputs.length, i), E.observed i, false⟩ := by
      simp [Dispatch.access, hi]
    rcases d.output_word h hr (fun g => (d.events (E.oracle g) g).1) (fun g hg => (hinv g hg).2)
        hi with ⟨g0, pm, v, hg0, hpm, hout, huniq⟩ | ⟨hnone, hout⟩
    · have hx : d.access E (.inv g0 pm) = some ⟨(d.inputs.length, i), v, true⟩ :=
        Dispatch.access_inv_of hg0 hpm
      have hv : ∀ k, byteOf k (E.observed i) = byteOf k v := fun k =>
        hE.value k _ _ _ _ (hE.visible hx hy rfl rfl rfl
          (hE.phase k _ _ _ _ hx hy rfl (by simp [Op.phase]) (Or.inl rfl))
          fun z az hne haz hw hl => by
            cases z with
            | before n =>
                exact Or.inl (hE.phase k _ _ _ _ haz hx hl (by simp [Op.phase]) (Or.inl hw))
            | init loc =>
                exact Or.inl (hE.phase k _ _ _ _ haz hx hl (by simp [Op.phase]) (Or.inl hw))
            | inv g p =>
                obtain ⟨hg, e, he, rfl⟩ := Dispatch.access_inv haz
                cases e with
                | read => cases hw
                | write j w =>
                    simp only [Event.access, Prod.mk.injEq] at hl
                    obtain ⟨-, rfl⟩ := hl
                    obtain ⟨rfl, hle⟩ := huniq g p w hg he
                    have hp : p ≠ pm := fun hp => hne (by rw [hp])
                    exact Or.inl (hE.program k g p pm _ _ haz hx rfl (by omega))
            | obs i' => cases (Dispatch.access_obs haz).2 ▸ hw
            | after n => exact Or.inr (hE.phase k _ _ _ _ hy haz (hl ▸ rfl) (by simp [Op.phase])
                (Or.inr hw)))
          hx hy
      rw [hout, byteOf_ext hv]
    · have hx := Dispatch.access_init_output (E := E) hi
      have hv : ∀ k, byteOf k (E.observed i) = byteOf k d.output[i] := fun k =>
        hE.value k _ _ _ _ (hE.visible hx hy rfl rfl rfl
          (hE.phase k _ _ _ _ hx hy rfl (by simp [Op.phase]) (Or.inl rfl))
          fun z az hne haz hw hl => by
            cases z with
            | before n =>
                exact Or.inl (hE.phase k _ _ _ _ haz hx hl (by simp [Op.phase]) (Or.inl hw))
            | init loc =>
                obtain ⟨hloc, -⟩ := Dispatch.access_init haz
                exact absurd (by rw [← hloc, hl]) hne
            | inv g p =>
                obtain ⟨hg, e, he, rfl⟩ := Dispatch.access_inv haz
                cases e with
                | read => cases hw
                | write j w =>
                    simp only [Event.access, Prod.mk.injEq] at hl
                    obtain ⟨-, rfl⟩ := hl
                    exact absurd he (hnone g p w hg)
            | obs i' => cases (Dispatch.access_obs haz).2 ▸ hw
            | after n => exact Or.inr (hE.phase k _ _ _ _ hy haz (hl ▸ rfl) (by simp [Op.phase])
                (Or.inr hw)))
          hx hy
      rw [hout, byteOf_ext hv]

/-- The rank of an operation in the location order of `Dispatch.execution_exists`. -/
def Op.rank : Op → Nat × Nat × Nat
  | .before n => (0, n, 0)
  | .init _ => (1, 0, 0)
  | .inv g p => (2, g, p)
  | .obs _ => (3, 0, 0)
  | .after n => (4, n, 0)

/-- The lexicographic order of ranks. -/
def Op.Below (x y : Op) : Prop :=
  x.rank.1 < y.rank.1 ∨ (x.rank.1 = y.rank.1 ∧ (x.rank.2.1 < y.rank.2.1 ∨
    (x.rank.2.1 = y.rank.2.1 ∧ x.rank.2.2 < y.rank.2.2)))

theorem Op.Below.trans {x y z : Op} (h1 : x.Below y) (h2 : y.Below z) : x.Below z := by
  unfold Op.Below at *
  omega

theorem Op.Below.irrefl (x : Op) : ¬x.Below x := by
  unfold Op.Below
  omega

theorem Op.Below.of_transGen {x y : Op} (h : Relation.TransGen Op.Below x y) : x.Below y := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact ih.trans h

theorem Op.Below.of_phase {x y : Op} (h : x.phase < y.phase) : x.Below y := by
  left
  cases x <;> cases y <;> simp_all [Op.phase, Op.rank]

/-- A race-free dispatch that `Module.dispatch` computes has a consistent execution. -/
theorem Dispatch.execution_exists (d : Dispatch) {out : Array UInt32}
    (h : d.module.dispatch d.inputs d.output d.count = some out)
    (hr : d.module.RaceFree d.inputs d.output.size d.count) :
    ∃ E, d.Consistent E := by
  have hinv : ∀ g, g < d.count → d.module.invoke d.inputs d.output.size (UInt32.ofNat g) =
      some (writesOf (d.events (inputOracle d.inputs) g).1) := by
    intro g hg
    have hs := Module.dispatch_steps h g hg
    have he := d.module.invokeE_input d.inputs d.output.size (UInt32.ofNat g)
    unfold Dispatch.events
    cases hc : (d.module.invokeE (d.inputs.map (·.size)) d.output.size (inputOracle d.inputs)
        (UInt32.ofNat g)).2
    · rw [he, hc] at hs
      simp at hs
    · rw [he, hc]
      rfl
  let E : Execution :=
    { oracle := fun _ => inputOracle d.inputs, before := fun _ => none, after := fun _ => none,
      lo := fun _ => Op.Below, observed := fun i => out[i]! }
  refine ⟨E, ⟨fun k x y ax ay _ _ _ hph _ => Op.Below.of_phase hph,
    fun k g p q a b _ _ _ hpq => Or.inr ⟨rfl, Or.inr ⟨rfl, hpq⟩⟩,
    fun k x hx => Op.Below.irrefl x (Op.Below.of_transGen hx), ?_⟩⟩
  intro k x y ax ay hvis hx hy
  obtain ⟨ax', ay', hx', hy', hxw, hyw, hloc, hxy, hnot⟩ := hvis
  rw [hx] at hx'
  rw [hy] at hy'
  cases hx'
  cases hy'
  suffices hval : ay.value = ax.value by rw [hval]
  cases y with
  | before n => simp [Dispatch.access, E] at hy
  | after n => simp [Dispatch.access, E] at hy
  | init loc => rw [(Dispatch.access_init hy).2] at hyw; cases hyw
  | inv g p =>
      obtain ⟨hg, e, he, rfl⟩ := Dispatch.access_inv hy
      cases e with
      | write => cases hyw
      | read b i w =>
          have hb := Dispatch.read_binding he
          have hw := d.module.invokeE_input_reads d.inputs d.output.size (UInt32.ofNat g) p b i w he
          cases x with
          | before n => simp [Dispatch.access, E] at hx
          | after n => simp [Dispatch.access, E] at hx
          | init loc =>
              obtain ⟨b', i'⟩ := loc
              have hl := (Dispatch.access_init hx).1
              simp only [Event.access] at hloc
              rw [hl] at hloc
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc.symm
              obtain ⟨buf, hbuf, hi⟩ := Dispatch.read_bounds he
              rw [Dispatch.access_init_input hbuf hi] at hx
              cases hx
              have hw' : buf[i]? = some w := by simpa [hbuf] using hw
              rw [getElem?_pos buf i hi] at hw'
              exact (Option.some.inj hw').symm
          | inv g' p' =>
              obtain ⟨-, e', -, rfl⟩ := Dispatch.access_inv hx
              cases e' with
              | read => cases hxw
              | write j v =>
                  simp only [Event.access, Prod.mk.injEq] at hloc
                  omega
          | obs i' => cases (Dispatch.access_obs hx).2 ▸ hxw
  | obs i =>
      obtain ⟨hi, rfl⟩ := Dispatch.access_obs hy
      rcases d.output_word h hr (fun g => (d.events (inputOracle d.inputs) g).1) hinv hi with
        ⟨g0, pm, v, hg0, hpm, hout, huniq⟩ | ⟨hnone, hout⟩
      · have hW : d.access E (.inv g0 pm) = some ⟨(d.inputs.length, i), v, true⟩ :=
          Dispatch.access_inv_of (e := Event.write i v) hg0 hpm
        have hxW : x = .inv g0 pm := by
          refine Decidable.byContradiction fun hne => ?_
          refine hnot (.inv g0 pm) _ (Ne.symm hne) hW rfl (by rw [hloc]) ⟨?_, ?_⟩
          · cases x with
            | before n => simp [Dispatch.access, E] at hx
            | after n => simp [Dispatch.access, E] at hx
            | init loc => exact Op.Below.of_phase (by simp [Op.phase])
            | obs i' => cases (Dispatch.access_obs hx).2 ▸ hxw
            | inv g p =>
                obtain ⟨hg, e, he, rfl⟩ := Dispatch.access_inv hx
                cases e with
                | read => cases hxw
                | write j w =>
                    simp only [Event.access, Prod.mk.injEq] at hloc
                    obtain ⟨-, rfl⟩ := hloc
                    obtain ⟨rfl, hle⟩ := huniq g p w hg he
                    have hp : p ≠ pm := fun hp => hne (by rw [hp])
                    exact Or.inr ⟨rfl, Or.inr ⟨rfl, by simp only [Op.rank]; omega⟩⟩
          · exact Op.Below.of_phase (by simp [Op.phase])
        subst hxW
        rw [hW] at hx
        cases hx
        show out[i]! = v
        simp [getElem!_def, hout]
      · cases x with
        | before n => simp [Dispatch.access, E] at hx
        | after n => simp [Dispatch.access, E] at hx
        | obs i' => cases (Dispatch.access_obs hx).2 ▸ hxw
        | inv g p =>
            obtain ⟨hg, e, he, rfl⟩ := Dispatch.access_inv hx
            cases e with
            | read => cases hxw
            | write j w =>
                simp only [Event.access, Prod.mk.injEq] at hloc
                obtain ⟨-, rfl⟩ := hloc
                exact absurd he (hnone g p w hg)
        | init loc =>
            have hl := (Dispatch.access_init hx).1
            rw [hloc] at hl
            subst hl
            rw [Dispatch.access_init_output hi] at hx
            cases hx
            show out[i]! = d.output[i]
            simp [getElem!_def, hout]

end LeanExe.WGSL

#print axioms LeanExe.WGSL.Dispatch.executions
#print axioms LeanExe.WGSL.Dispatch.execution_exists
