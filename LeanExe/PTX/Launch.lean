import LeanExe.PTX.MemoryModel

/-!
A race-free launch under the memory model of `MemoryModel.lean`.  In every consistent execution
each load of a thread returns the input word, so each thread runs as it does with the input oracle:
it ends, and it stores what `Launch.seq` applies.  No access of a thread is in a data race, and the
copy back reads the words of `Launch.seq`'s output.  A consistent execution exists.
-/

namespace LeanExe.PTX

theorem byteOf_ext {a b : UInt64} (h : ∀ k, byteOf k a = byteOf k b) : a = b := by
  have h0 : a.toNat % 256 = b.toNat % 256 := by simpa [byteOf] using h ⟨0, by omega⟩
  have h1 : a.toNat / 256 % 256 = b.toNat / 256 % 256 := by simpa [byteOf] using h ⟨1, by omega⟩
  have h2 : a.toNat / 65536 % 256 = b.toNat / 65536 % 256 := by
    simpa [byteOf] using h ⟨2, by omega⟩
  have h3 : a.toNat / 16777216 % 256 = b.toNat / 16777216 % 256 := by
    simpa [byteOf] using h ⟨3, by omega⟩
  have h4 : a.toNat / 4294967296 % 256 = b.toNat / 4294967296 % 256 := by
    simpa [byteOf] using h ⟨4, by omega⟩
  have h5 : a.toNat / 1099511627776 % 256 = b.toNat / 1099511627776 % 256 := by
    simpa [byteOf] using h ⟨5, by omega⟩
  have h6 : a.toNat / 281474976710656 % 256 = b.toNat / 281474976710656 % 256 := by
    simpa [byteOf] using h ⟨6, by omega⟩
  have h7 : a.toNat / 72057594037927936 % 256 = b.toNat / 72057594037927936 % 256 := by
    simpa [byteOf] using h ⟨7, by omega⟩
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  exact UInt64.toNat_inj.mp (by omega)

/-! ### The stores of a launch -/

theorem mem_writesOf {evs : List Event} {p i : Nat} {w : UInt64}
    (h : evs[p]? = some (Event.write i w)) : (i, w) ∈ writesOf evs :=
  List.mem_filterMap.mpr ⟨Event.write i w, List.mem_iff_getElem?.mpr ⟨p, h⟩, rfl⟩

theorem writesOf_mem {evs : List Event} {w : Nat × UInt64} (h : w ∈ writesOf evs) :
    ∃ p : Nat, evs[p]? = some (Event.write w.1 w.2) := by
  obtain ⟨e, he, hw⟩ := List.mem_filterMap.mp h
  cases e with
  | read => cases hw
  | write j v =>
      cases hw
      exact List.mem_iff_getElem?.mp he

theorem lastVal_no_write {evs : List Event} {i : Nat}
    (h : ∀ (p : Nat) (w : UInt64), evs[p]? ≠ some (Event.write i w)) (v : UInt64) :
    lastVal (writesOf evs) i v = v :=
  lastVal_of_forall (fun w hw hi => by
    obtain ⟨p, hp⟩ := writesOf_mem hw
    exact h p w.2 (hi ▸ hp)) v

/-- The last store to word `i` among events: its position, and its value as `lastVal`. -/
theorem last_write {i : Nat} : ∀ (evs : List Event) (v : UInt64),
    (∃ (p : Nat) (w : UInt64), evs[p]? = some (Event.write i w)) →
      ∃ pm : Nat, evs[pm]? = some (Event.write i (lastVal (writesOf evs) i v)) ∧
        ∀ (q : Nat) (w : UInt64), evs[q]? = some (Event.write i w) → q ≤ pm
  | [], _, ⟨_, _, h⟩ => by simp at h
  | e :: rest, v, hex => by
      have hcons : lastVal (writesOf (e :: rest)) i v = lastVal (writesOf rest) i
          (match e with
            | .write j w => if j = i then w else v
            | .read .. => v) := by
        cases e <;> rfl
      rw [hcons]
      by_cases hr : ∃ (p : Nat) (w : UInt64), rest[p]? = some (Event.write i w)
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

/-- When the sequential run reaches the end, every thread ended and the output is the initial
output after every thread's stores. -/
theorem Launch.seq_eq (L : Launch) {out : Array UInt64} (h : L.seq = some out) :
    (∀ g, g < L.threads → (L.events (inputOracle L.inputs) g).2 = true) ∧
      out = setAll L.output ((List.range L.threads).flatMap fun g =>
        writesOf (L.events (inputOracle L.inputs) g).1) := by
  unfold Launch.seq at h
  suffices ∀ n out, (List.range n).foldlM (fun out g =>
      let r := L.events (inputOracle L.inputs) g
      if r.2 then some (setAll out (writesOf r.1)) else none) L.output = some out →
      (∀ g, g < n → (L.events (inputOracle L.inputs) g).2 = true) ∧
        out = setAll L.output ((List.range n).flatMap fun g =>
          writesOf (L.events (inputOracle L.inputs) g).1) from this _ _ h
  intro n
  induction n with
  | zero =>
      intro out h
      simp only [List.range_zero, List.foldlM_nil] at h
      cases h
      exact ⟨fun g hg => absurd hg (by omega), rfl⟩
  | succ n ih =>
      intro out h
      rw [List.range_succ, List.foldlM_append] at h
      simp only [Option.bind_eq_bind] at h
      obtain ⟨s, hs, hn⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ih1, ih2⟩ := ih s hs
      simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind] at hn
      by_cases he : (L.events (inputOracle L.inputs) n).2 = true
      · simp only [he, ↓reduceIte, Option.bind_some, Option.pure_def, Option.some.injEq] at hn
        subst hn
        refine ⟨fun g hg => ?_, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | rfl
          · exact ih1 g hg
          · exact he
        · rw [ih2, setAll_append, List.range_succ, List.flatMap_append]
          simp
      · simp [he] at hn

/-- When every thread, run with the input oracle, ends with events `evs g`, the sequential run
reaches the end with every thread's stores applied. -/
theorem Launch.seq_some (L : Launch) (evs : Nat → List Event)
    (h : ∀ g, g < L.threads → L.events (inputOracle L.inputs) g = (evs g, true)) :
    L.seq = some (setAll L.output ((List.range L.threads).flatMap fun g => writesOf (evs g))) := by
  unfold Launch.seq
  suffices ∀ n, n ≤ L.threads → (List.range n).foldlM (fun out g =>
      let r := L.events (inputOracle L.inputs) g
      if r.2 then some (setAll out (writesOf r.1)) else none) L.output =
        some (setAll L.output ((List.range n).flatMap fun g => writesOf (evs g))) from
    this _ (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      simp [h n (by omega), setAll_append, List.flatMap_append]

/-- Word `i` of a race-free launch's output: the last store to `i` of the one thread that stores to
`i`, or the initial word when no thread stores to `i`. -/
theorem Launch.output_word (L : Launch) {out : Array UInt64} (h : L.seq = some out)
    (hr : L.RaceFree) {i : Nat} (hi : i < L.output.size) :
    (∃ (g0 pm : Nat) (v : UInt64), g0 < L.threads ∧
        (L.events (inputOracle L.inputs) g0).1[pm]? = some (Event.write i v) ∧
        out[i]? = some v ∧ ∀ (g p : Nat) (w : UInt64), g < L.threads →
          (L.events (inputOracle L.inputs) g).1[p]? = some (Event.write i w) → g = g0 ∧ p ≤ pm) ∨
      ((∀ (g p : Nat) (w : UInt64), g < L.threads →
          (L.events (inputOracle L.inputs) g).1[p]? ≠ some (Event.write i w)) ∧
        out[i]? = some L.output[i]) := by
  obtain ⟨-, hout⟩ := L.seq_eq h
  have hget := setAll_get hi ((List.range L.threads).flatMap fun g =>
    writesOf (L.events (inputOracle L.inputs) g).1)
  rw [← hout] at hget
  by_cases hex : ∃ (g0 p : Nat) (w : UInt64), g0 < L.threads ∧
      (L.events (inputOracle L.inputs) g0).1[p]? = some (Event.write i w)
  · obtain ⟨g0, p0, w0, hg0, hp0⟩ := hex
    have huniq : ∀ (g p : Nat) (w : UInt64), g < L.threads →
        (L.events (inputOracle L.inputs) g).1[p]? = some (Event.write i w) → g = g0 := by
      intro g p w hg hp
      by_cases hne : g = g0
      · exact hne
      · exact absurd (List.mem_iff_getElem?.mpr ⟨p0, hp0⟩)
          (hr g g0 hg hg0 hne i w w0 (List.mem_iff_getElem?.mpr ⟨p, hp⟩))
    obtain ⟨pm, hpm, hmax⟩ := last_write (L.events (inputOracle L.inputs) g0).1 L.output[i]
      ⟨p0, w0, hp0⟩
    refine Or.inl ⟨g0, pm, _, hg0, hpm, ?_, fun g p w hg hp => ?_⟩
    · rw [hget, lastVal_flatMap _ i g0 L.threads (fun g hg hne w hw hwi => by
          obtain ⟨p, hp⟩ := writesOf_mem hw
          exact hne (huniq g p w.2 hg (hwi ▸ hp))) _ L.threads (Nat.le_refl _)]
      simp [hg0]
    · have hg := huniq g p w hg hp
      subst hg
      exact ⟨rfl, hmax p w hp⟩
  · refine Or.inr ⟨fun g p w hg hp => hex ⟨g, p, w, hg, hp⟩, ?_⟩
    rw [hget, lastVal_flatMap _ i L.threads L.threads (fun g hg _ w hw hwi => by
        obtain ⟨p, hp⟩ := writesOf_mem hw
        exact hex ⟨g, p, w.2, hg, hwi ▸ hp⟩) _ L.threads (Nat.le_refl _)]
    simp

/-! ### Accesses -/

theorem Launch.access_inv {L : Launch} {E : Execution} {g p : Nat} {a : Access}
    (h : L.access E (.inv g p) = some a) :
    g < L.threads ∧ ∃ e, (L.events (E.oracle g) g).1[p]? = some e ∧
      a = e.access L.inputs.length := by
  simp only [Launch.access] at h
  split at h
  · rename_i hg
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hg, e, he, rfl⟩
  · cases h

theorem Launch.access_inv_of {L : Launch} {E : Execution} {g p : Nat} {e : Event}
    (hg : g < L.threads) (he : (L.events (E.oracle g) g).1[p]? = some e) :
    L.access E (.inv g p) = some (e.access L.inputs.length) := by
  simp [Launch.access, hg, he]

theorem Launch.access_init {L : Launch} {E : Execution} {loc : Loc} {a : Access}
    (h : L.access E (.init loc) = some a) :
    ∃ v, (L.buffers[loc.1]?.bind (·[loc.2]?)) = some v ∧ a = .word loc true v := by
  obtain ⟨b, i⟩ := loc
  simp only [Launch.access, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact ⟨v, hv, rfl⟩

theorem Launch.access_init_input {L : Launch} {E : Execution} {b i : Nat}
    {buf : Array UInt64} (hb : L.inputs[b]? = some buf) (hi : i < buf.size) :
    L.access E (.init (b, i)) = some (.word (b, i) true buf[i]) := by
  have hlt : b < L.inputs.length := (List.getElem?_eq_some_iff.mp hb).1
  simp [Launch.access, Launch.buffers, List.getElem?_append_left hlt, hb, hi]

theorem Launch.access_init_output {L : Launch} {E : Execution} {i : Nat}
    (hi : i < L.output.size) :
    L.access E (.init (L.inputs.length, i)) =
      some (.word (L.inputs.length, i) true L.output[i]) := by
  simp [Launch.access, Launch.buffers, hi]

theorem Launch.access_obs {L : Launch} {E : Execution} {i : Nat} {a : Access}
    (h : L.access E (.obs i) = some a) :
    i < L.output.size ∧ a = .word (L.inputs.length, i) false (E.observed i) := by
  simp only [Launch.access] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

theorem Launch.access_before {L : Launch} {E : Execution} {n : Nat} {a : Access}
    (h : L.access E (.before n) = some a) : a.write = true := by
  simp only [Launch.access, Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem Launch.access_after {L : Launch} {E : Execution} {n : Nat} {a : Access}
    (h : L.access E (.after n) = some a) : a.write = true := by
  simp only [Launch.access, Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem Launch.read_bounds {L : Launch} {o : Oracle} {g p b i : Nat} {w : UInt64}
    (h : (L.events o g).1[p]? = some (.read b i w)) :
    ∃ buf, L.inputs[b]? = some buf ∧ i < buf.size := by
  unfold Launch.events at h
  obtain ⟨-, n, hn, hi⟩ := (L.module.invoke_det _ _ _ o _).1.read p b i w h
  simp only [threadShape, List.getElem?_map, Option.map_eq_some_iff] at hn
  obtain ⟨buf, hbuf, rfl⟩ := hn
  exact ⟨buf, hbuf, hi⟩

theorem Launch.read_buffer {L : Launch} {o : Oracle} {g p b i : Nat} {w : UInt64}
    (h : (L.events o g).1[p]? = some (.read b i w)) : b < L.inputs.length := by
  obtain ⟨buf, hbuf, -⟩ := Launch.read_bounds h
  exact (List.getElem?_eq_some_iff.mp hbuf).1

theorem Launch.cause_phase {L : Launch} {E : Execution} {x y : Op} {ax ay : Access}
    (hx : L.access E x = some ax) (hy : L.access E y = some ay) (hloc : ax.loc = ay.loc)
    (h : x.phase < y.phase) : L.Cause E x y :=
  ⟨ax, ay, hx, hy, hloc, Or.inl h⟩

theorem Launch.cause_program {L : Launch} {E : Execution} {g p q : Nat} {ax ay : Access}
    (hx : L.access E (.inv g p) = some ax) (hy : L.access E (.inv g q) = some ay)
    (hloc : ax.loc = ay.loc) (h : p < q) : L.Cause E (.inv g p) (.inv g q) :=
  ⟨ax, ay, hx, hy, hloc, Or.inr ⟨g, p, q, rfl, rfl, h⟩⟩

theorem Access.word_bytes (loc : Loc) (write : Bool) (v : UInt64) (k : Fin 8) :
    ((Access.word loc write v).bytes k).isSome = true := rfl

/-- In a consistent execution, a load of a thread returns the input word. -/
theorem Launch.Consistent.read_input {L : Launch} {E : Execution} (hE : L.Consistent E)
    {g p b i : Nat} {w : UInt64} (hg : g < L.threads)
    (hp : (L.events (E.oracle g) g).1[p]? = some (.read b i w)) :
    L.inputs[b]?.bind (·[i]?) = some w := by
  obtain ⟨buf, hbuf, hi⟩ := Launch.read_bounds hp
  have hb := Launch.read_buffer hp
  have hx : L.access E (.init (b, i)) = some (.word (b, i) true buf[i]) :=
    Launch.access_init_input hbuf hi
  have hy : L.access E (.inv g p) = some (.word (b, i) false w) := Launch.access_inv_of hg hp
  have hv : ∀ k, byteOf k w = byteOf k buf[i] := by
    intro k
    obtain ⟨ax, hax, hw, hloc, hbytes⟩ := hE.reads k _ _ hy rfl (Access.word_bytes _ _ _ k)
    have hks : (ax.bytes k).isSome = true := by rw [hbytes]; rfl
    rcases hW : E.rf k (.inv g p) with n | loc | ⟨g', p'⟩ | i' | n <;> rw [hW] at hax
    · exfalso
      have hc := hE.coherence k _ _ _ _ hax hx hw rfl hks rfl
        (Launch.cause_phase hax hx hloc (by simp [Op.phase]))
      exact hE.causality_write k _ _ _ _ hx hy rfl rfl rfl rfl
        (Launch.cause_phase hx hy rfl (by simp [Op.phase])) (hW ▸ hc)
    · obtain ⟨v, hv, rfl⟩ := Launch.access_init hax
      simp only [Access.word] at hloc hbytes
      subst hloc
      have hv' : buf[i] = v := by
        simpa [Launch.buffers, List.getElem?_append_left hb, hbuf, hi] using hv
      subst hv'
      simp only [Option.some.injEq] at hbytes
      exact hbytes.symm
    · exfalso
      obtain ⟨-, e, -, rfl⟩ := Launch.access_inv hax
      cases e with
      | read => cases hw
      | write j v =>
          simp only [Event.access, Access.word, Prod.mk.injEq] at hloc
          omega
    · exfalso
      rw [(Launch.access_obs hax).2] at hw
      cases hw
    · exfalso
      exact hE.causality_read k _ _ hy rfl rfl _
        (Launch.cause_phase hy hax hloc.symm (by simp [Op.phase])) hW
  rw [byteOf_ext hv]
  simp [hbuf, hi]

/-! ### The theorems -/

/-- In every consistent execution of a race-free launch whose sequential run reaches the end,
every thread runs as it does with the input oracle and ends, no access of a thread is in a data
race, and the copy back reads the words of `Launch.seq`'s output. -/
theorem Launch.executions (L : Launch) {out : Array UInt64} (h : L.seq = some out)
    (hr : L.RaceFree) (E : Execution) (hE : L.Consistent E) :
    (∀ g, g < L.threads → L.events (E.oracle g) g = L.events (inputOracle L.inputs) g ∧
      (L.events (E.oracle g) g).2 = true) ∧
      L.NoDataRace E ∧ ∀ i, i < L.output.size → out[i]? = some (E.observed i) := by
  have hagree : ∀ g, g < L.threads →
      L.events (E.oracle g) g = L.events (inputOracle L.inputs) g := by
    intro g hg
    unfold Launch.events
    exact ((L.module.invoke_det _ _ _ (E.oracle g) g).2 (inputOracle L.inputs)
      fun k b i w hk => by simp [inputOracle, hE.read_input hg hk]).symm
  obtain ⟨hend, -⟩ := L.seq_eq h
  refine ⟨fun g hg => ⟨hagree g hg, (hagree g hg) ▸ hend g hg⟩, ?_, ?_⟩
  · intro x y ax ay hne hph hx hy hloc hw
    rcases Nat.lt_trichotomy x.phase y.phase with hlt | heq | hgt
    · exact Or.inl (Launch.cause_phase hx hy hloc hlt)
    · have h2 : x.phase = 2 ∧ y.phase = 2 := by omega
      obtain ⟨g, p, rfl⟩ : ∃ g p, x = .inv g p := by
        cases x <;> simp [Op.phase] at h2 ⊢
      obtain ⟨g', q, rfl⟩ : ∃ g p, y = .inv g p := by
        cases y <;> simp [Op.phase] at h2 ⊢
      by_cases hgg : g = g'
      · subst hgg
        have hpq : p ≠ q := fun hpq => hne (by rw [hpq])
        rcases Nat.lt_or_gt_of_ne hpq with hpq | hpq
        · exact Or.inl (Launch.cause_program hx hy hloc hpq)
        · exact Or.inr (Launch.cause_program hy hx hloc.symm hpq)
      · exfalso
        obtain ⟨hg, e, he, rfl⟩ := Launch.access_inv hx
        obtain ⟨hg', e', he', rfl⟩ := Launch.access_inv hy
        cases e with
        | read b i v =>
            have hb := Launch.read_buffer he
            cases e' with
            | read => simp [Event.access, Access.word] at hw
            | write j v' =>
                simp only [Event.access, Access.word, Prod.mk.injEq] at hloc
                omega
        | write j v =>
            cases e' with
            | read b i v' =>
                have hb := Launch.read_buffer he'
                simp only [Event.access, Access.word, Prod.mk.injEq] at hloc
                omega
            | write j' v' =>
                simp only [Event.access, Access.word, Prod.mk.injEq] at hloc
                rw [hagree g hg] at he
                rw [hagree g' hg'] at he'
                rw [← hloc.2] at he'
                exact hr g g' hg hg' hgg j v v' (List.mem_iff_getElem?.mpr ⟨_, he⟩)
                  (List.mem_iff_getElem?.mpr ⟨_, he'⟩)
    · exact Or.inr (Launch.cause_phase hy hx hloc.symm hgt)
  · intro i hi
    have hy : L.access E (.obs i) = some (.word (L.inputs.length, i) false (E.observed i)) := by
      simp [Launch.access, hi]
    have hinit := Launch.access_init_output (E := E) hi
    rcases L.output_word h hr hi with ⟨g0, pm, v, hg0, hpm, hout, huniq⟩ | ⟨hnone, hout⟩
    · rw [← hagree g0 hg0] at hpm
      have hx : L.access E (.inv g0 pm) = some (.word (L.inputs.length, i) true v) :=
        Launch.access_inv_of (e := .write i v) hg0 hpm
      have hv : ∀ k, byteOf k (E.observed i) = byteOf k v := by
        intro k
        obtain ⟨ax, hax, hw, hloc, hbytes⟩ := hE.reads k _ _ hy rfl (Access.word_bytes _ _ _ k)
        have hks : (ax.bytes k).isSome = true := by rw [hbytes]; rfl
        have hxy : L.Cause E (.inv g0 pm) (.obs i) :=
          Launch.cause_phase hx hy rfl (by simp [Op.phase])
        rcases hW : E.rf k (.obs i) with n | loc | ⟨g, p⟩ | i' | n <;> rw [hW] at hax
        · exfalso
          have hc := hE.coherence k _ _ _ _ hax hx hw rfl hks rfl
            (Launch.cause_phase hax hx hloc (by simp [Op.phase]))
          exact hE.causality_write k _ _ _ _ hx hy rfl rfl rfl rfl hxy (hW ▸ hc)
        · exfalso
          obtain ⟨v', -, rfl⟩ := Launch.access_init hax
          have hc := hE.coherence k _ _ _ _ hax hx rfl rfl rfl rfl
            (Launch.cause_phase hax hx hloc (by simp [Op.phase]))
          exact hE.causality_write k _ _ _ _ hx hy rfl rfl rfl rfl hxy (hW ▸ hc)
        · obtain ⟨hg, e, he, rfl⟩ := Launch.access_inv hax
          cases e with
          | read => cases hw
          | write j w =>
              simp only [Event.access, Access.word, Prod.mk.injEq] at hloc
              obtain ⟨-, rfl⟩ := hloc
              have he' := he
              rw [hagree g hg] at he'
              obtain ⟨rfl, hle⟩ := huniq g p w hg he'
              rcases Nat.lt_or_ge p pm with hlt | hge
              · exfalso
                have hc := hE.coherence k _ _ _ _ hax hx rfl rfl rfl rfl
                  (Launch.cause_program hax hx rfl hlt)
                exact hE.causality_write k _ _ _ _ hx hy rfl rfl rfl rfl hxy (hW ▸ hc)
              · obtain rfl : p = pm := by omega
                rw [he] at hpm
                cases hpm
                simp only [Event.access, Access.word, Option.some.injEq] at hbytes
                exact hbytes.symm
        · exfalso
          rw [(Launch.access_obs hax).2] at hw
          cases hw
        · exfalso
          exact hE.causality_read k _ _ hy rfl rfl _
            (Launch.cause_phase hy hax hloc.symm (by simp [Op.phase])) hW
      rw [hout, byteOf_ext hv]
    · have hv : ∀ k, byteOf k (E.observed i) = byteOf k L.output[i] := by
        intro k
        obtain ⟨ax, hax, hw, hloc, hbytes⟩ := hE.reads k _ _ hy rfl (Access.word_bytes _ _ _ k)
        have hks : (ax.bytes k).isSome = true := by rw [hbytes]; rfl
        rcases hW : E.rf k (.obs i) with n | loc | ⟨g, p⟩ | i' | n <;> rw [hW] at hax
        · exfalso
          have hc := hE.coherence k _ _ _ _ hax hinit hw rfl hks rfl
            (Launch.cause_phase hax hinit hloc (by simp [Op.phase]))
          exact hE.causality_write k _ _ _ _ hinit hy rfl rfl rfl rfl
            (Launch.cause_phase hinit hy rfl (by simp [Op.phase])) (hW ▸ hc)
        · obtain ⟨v', hv', rfl⟩ := Launch.access_init hax
          simp only [Access.word] at hloc hbytes
          subst hloc
          have hv'' : L.output[i] = v' := by simpa [Launch.buffers, hi] using hv'
          subst hv''
          simp only [Option.some.injEq] at hbytes
          exact hbytes.symm
        · exfalso
          obtain ⟨hg, e, he, rfl⟩ := Launch.access_inv hax
          cases e with
          | read => cases hw
          | write j w =>
              simp only [Event.access, Access.word, Prod.mk.injEq] at hloc
              obtain ⟨-, rfl⟩ := hloc
              rw [hagree g hg] at he
              exact hnone g p w hg he
        · exfalso
          rw [(Launch.access_obs hax).2] at hw
          cases hw
        · exfalso
          exact hE.causality_read k _ _ hy rfl rfl _
            (Launch.cause_phase hy hax hloc.symm (by simp [Op.phase])) hW
      rw [hout, byteOf_ext hv]

/-- The rank of an operation in the coherence order of `Launch.execution_exists`. -/
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

theorem Op.Below.of_phase {x y : Op} (h : x.phase < y.phase) : x.Below y := by
  left
  cases x <;> cases y <;> simp_all [Op.phase, Op.rank]

theorem Op.rank_fst (x : Op) : x.rank.1 = x.phase := by cases x <;> rfl

/-- A race-free launch whose sequential run reaches the end has a consistent execution. -/
theorem Launch.execution_exists (L : Launch) {out : Array UInt64} (h : L.seq = some out)
    (hr : L.RaceFree) : ∃ E, L.Consistent E := by
  let base : Execution :=
    { oracle := fun _ => inputOracle L.inputs, before := fun _ => none, after := fun _ => none,
      co := fun _ => Op.Below, rf := fun _ _ => .init (0, 0), observed := fun i => out[i]! }
  have hdes : ∀ i, ∃ W : Op, i < L.output.size → ∃ v,
      L.access base W = some (.word (L.inputs.length, i) true v) ∧ out[i]? = some v ∧
      ∀ z az, L.access base z = some az → az.write = true → az.loc = (L.inputs.length, i) →
        z = W ∨ z.Below W := by
    intro i
    by_cases hi : i < L.output.size
    · rcases L.output_word h hr hi with ⟨g0, pm, v, hg0, hpm, hout, huniq⟩ | ⟨hnone, hout⟩
      · refine ⟨.inv g0 pm, fun _ => ⟨v, Launch.access_inv_of (e := .write i v) hg0 hpm, hout,
          fun z az hz hw hl => ?_⟩⟩
        cases z with
        | before n => simp [Launch.access, base] at hz
        | after n => simp [Launch.access, base] at hz
        | init loc => exact Or.inr (Op.Below.of_phase (by simp [Op.phase]))
        | obs i' => rw [(Launch.access_obs hz).2] at hw; cases hw
        | inv g p =>
            obtain ⟨hg, e, he, rfl⟩ := Launch.access_inv hz
            cases e with
            | read => cases hw
            | write j w =>
                simp only [Event.access, Access.word, Prod.mk.injEq] at hl
                obtain ⟨-, rfl⟩ := hl
                obtain ⟨rfl, hle⟩ := huniq g p w hg he
                rcases Nat.lt_or_ge p pm with hlt | hge
                · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, hlt⟩⟩)
                · exact Or.inl (by rw [show p = pm by omega])
      · refine ⟨.init (L.inputs.length, i), fun _ => ⟨L.output[i], Launch.access_init_output hi,
          hout, fun z az hz hw hl => ?_⟩⟩
        cases z with
        | before n => simp [Launch.access, base] at hz
        | after n => simp [Launch.access, base] at hz
        | init loc =>
            obtain ⟨v, -, rfl⟩ := Launch.access_init hz
            simp only [Access.word] at hl
            exact Or.inl (by rw [hl])
        | obs i' => rw [(Launch.access_obs hz).2] at hw; cases hw
        | inv g p =>
            obtain ⟨hg, e, he, rfl⟩ := Launch.access_inv hz
            cases e with
            | read => cases hw
            | write j w =>
                simp only [Event.access, Access.word, Prod.mk.injEq] at hl
                obtain ⟨-, rfl⟩ := hl
                exact absurd he (hnone g p w hg)
    · exact ⟨.init (0, 0), fun h => absurd h hi⟩
  obtain ⟨W, hW⟩ : ∃ W : Nat → Op, ∀ i, i < L.output.size → ∃ v,
      L.access base (W i) = some (.word (L.inputs.length, i) true v) ∧ out[i]? = some v ∧
      ∀ z az, L.access base z = some az → az.write = true → az.loc = (L.inputs.length, i) →
        z = W i ∨ z.Below (W i) :=
    ⟨fun i => Classical.choose (hdes i), fun i => Classical.choose_spec (hdes i)⟩
  let rf : Fin 8 → Op → Op := fun _ r => match r with
    | .inv g p => match (L.events (inputOracle L.inputs) g).1[p]? with
      | some (.read b i _) => .init (b, i)
      | _ => .init (0, 0)
    | .obs i => W i
    | _ => .init (0, 0)
  let E : Execution := { base with rf := rf }
  have hacc : ∀ x, L.access E x = L.access base x := fun x => by cases x <;> rfl
  have hrfInv : ∀ k g p, ∃ loc, E.rf k (.inv g p) = .init loc := by
    intro k g p
    show ∃ loc, (match (L.events (inputOracle L.inputs) g).1[p]? with
      | some (.read b i _) => Op.init (b, i)
      | _ => .init (0, 0)) = .init loc
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have hrfRead : ∀ k g p b i v, (L.events (inputOracle L.inputs) g).1[p]? = some (.read b i v) →
      E.rf k (.inv g p) = .init (b, i) := by
    intro k g p b i v he
    show (match (L.events (inputOracle L.inputs) g).1[p]? with
      | some (.read b i _) => Op.init (b, i)
      | _ => .init (0, 0)) = _
    rw [he]
  have hWphase : ∀ i, i < L.output.size → (W i).phase ≤ 2 := by
    intro i hi
    obtain ⟨v, hv, -⟩ := hW i hi
    cases hWi : W i with
    | before n => rw [hWi] at hv; simp [Launch.access, base] at hv
    | after n => rw [hWi] at hv; simp [Launch.access, base] at hv
    | obs i' =>
        rw [hWi] at hv
        obtain ⟨-, h⟩ := Launch.access_obs hv
        have := congrArg Access.write h
        simp [Access.word] at this
    | init => simp [Op.phase]
    | inv => simp [Op.phase]
  refine ⟨E, ⟨fun k y ay hy hw hk => ?_, fun _ x => Op.Below.irrefl x,
    fun _ _ _ _ h1 h2 => h1.trans h2, fun k w w' aw aw' hw hw' _ _ _ _ hc => ?_,
    fun k r ar hr hrw _ w hc => ?_, fun k w r aw ar hw hr hww hrw _ _ hc => ?_⟩⟩
  · -- reads
    rw [hacc] at hy
    cases y with
    | before n => simp [Launch.access, base] at hy
    | after n => simp [Launch.access, base] at hy
    | init loc =>
        obtain ⟨v, -, rfl⟩ := Launch.access_init hy
        cases hw
    | inv g p =>
        obtain ⟨hg, e, he, rfl⟩ := Launch.access_inv hy
        cases e with
        | write => cases hw
        | read b i v =>
            obtain ⟨buf, hbuf, hi⟩ := Launch.read_bounds he
            have hval : v = buf[i] := by
              obtain ⟨hv, -⟩ := (L.module.invoke_det _ _ _ (inputOracle L.inputs) g).1.read
                p b i v he
              rw [← hv]
              simp [inputOracle, hbuf, hi]
            refine ⟨.word (b, i) true buf[i], ?_, rfl, rfl, ?_⟩
            · rw [hrfRead k g p b i v he, hacc]
              exact Launch.access_init_input hbuf hi
            · simp [Event.access, Access.word, hval]
    | obs i =>
        obtain ⟨hi, rfl⟩ := Launch.access_obs hy
        obtain ⟨v, hv, hout, -⟩ := hW i hi
        refine ⟨.word (L.inputs.length, i) true v, ?_, rfl, rfl, ?_⟩
        · show L.access E (W i) = _
          rw [hacc]
          exact hv
        · have : out[i]! = v := by simp [getElem!_def, hout]
          simp [Access.word, base, this]
  · -- coherence
    obtain ⟨ax, ay, -, -, -, hph | ⟨g, p, q, rfl, rfl, hpq⟩⟩ := hc
    · exact Op.Below.of_phase hph
    · exact Or.inr ⟨rfl, Or.inr ⟨rfl, hpq⟩⟩
  · -- the first rule of causality
    obtain ⟨ax, ay, -, -, -, hord⟩ := hc
    intro hrfw
    rw [hacc] at hr
    cases r with
    | before n => simp [Launch.access, base] at hr
    | after n => simp [Launch.access, base] at hr
    | init loc =>
        obtain ⟨v, -, rfl⟩ := Launch.access_init hr
        cases hrw
    | inv g p =>
        obtain ⟨loc, hl⟩ := hrfInv k g p
        rw [hl] at hrfw
        subst hrfw
        rcases hord with hph | ⟨_, _, _, -, h2, -⟩
        · simp [Op.phase] at hph
        · cases h2
    | obs i =>
        obtain ⟨hi, -⟩ := Launch.access_obs hr
        have hp := hWphase i hi
        change W i = w at hrfw
        subst hrfw
        have h3 : (Op.obs i).phase = 3 := rfl
        rcases hord with hph | ⟨_, _, _, h1, -, -⟩
        · omega
        · cases h1
  · -- the second rule of causality
    intro hco
    rw [hacc] at hw hr
    obtain ⟨ax, ay, hx', hy', hloc, -⟩ := hc
    rw [hacc, hw] at hx'
    rw [hacc, hr] at hy'
    cases hx'
    cases hy'
    cases r with
    | before n => simp [Launch.access, base] at hr
    | after n => simp [Launch.access, base] at hr
    | init loc =>
        obtain ⟨v, -, rfl⟩ := Launch.access_init hr
        cases hrw
    | inv g p =>
        obtain ⟨hg, e, he, rfl⟩ := Launch.access_inv hr
        cases e with
        | write => cases hrw
        | read b i v =>
            have hb := Launch.read_buffer he
            rw [hrfRead k g p b i v he] at hco
            cases w with
            | before n => simp [Launch.access, base] at hw
            | after n => simp [Launch.access, base] at hw
            | obs i' =>
                rw [(Launch.access_obs hw).2] at hww
                cases hww
            | init loc =>
                obtain ⟨v', -, rfl⟩ := Launch.access_init hw
                simp only [Event.access, Access.word] at hloc
                subst hloc
                exact Op.Below.irrefl _ hco
            | inv g' p' =>
                obtain ⟨-, e', -, rfl⟩ := Launch.access_inv hw
                cases e' with
                | read => cases hww
                | write j v' =>
                    simp only [Event.access, Access.word, Prod.mk.injEq] at hloc
                    omega
    | obs i =>
        obtain ⟨hi, rfl⟩ := Launch.access_obs hr
        obtain ⟨v, hv, -, hmax⟩ := hW i hi
        change (W i).Below w at hco
        rcases hmax w aw hw hww hloc with rfl | hlt
        · exact Op.Below.irrefl _ hco
        · exact Op.Below.irrefl _ (hco.trans hlt)

theorem get_head (a : UInt64) (xs : Array UInt64) : (#[a] ++ xs)[0]? = some a := by
  rw [Array.getElem?_append_left (by simp)]
  rfl

theorem get_tail (a : UInt64) (xs : Array UInt64) (k : Nat) : (#[a] ++ xs)[k + 1]? = xs[k]? := by
  rw [Array.getElem?_append_right (by simp)]
  simp

/-- `mad.wide.u32` of `%ctaid.x`, `%ntid.x`, and the widened `%tid.x` gives the thread's index. -/
theorem index_eq {block g : Nat} (hb : 0 < block) (hb32 : block < 2 ^ 32)
    (hq : g / block < 2 ^ 32) (hg : g < 2 ^ 60) :
    (UInt32.ofNat (g / block)).toUInt64 * (UInt32.ofNat block).toUInt64 +
      (UInt32.ofNat (g % block)).toUInt64 = UInt64.ofNat g := by
  apply UInt64.toNat_inj.mp
  have hm := Nat.mod_lt g hb
  have h1 : (UInt32.ofNat (g / block)).toUInt64.toNat = g / block := by
    simp [Nat.mod_eq_of_lt hq]
  have h2 : (UInt32.ofNat block).toUInt64.toNat = block := by simp [Nat.mod_eq_of_lt hb32]
  have h3 : (UInt32.ofNat (g % block)).toUInt64.toNat = g % block := by
    simp [Nat.mod_eq_of_lt (show g % block < 2 ^ 32 by omega)]
  have hle : g / block * block ≤ g := Nat.div_mul_le_self g block
  rw [UInt64.toNat_add, UInt64.toNat_mul, h1, h2, h3, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show g / block * block < 2 ^ 64 by omega), Nat.div_add_mod' g block]

end LeanExe.PTX

#print axioms LeanExe.PTX.Launch.executions
#print axioms LeanExe.PTX.Launch.execution_exists
