import Library.Regex.ScanProof

/-! The matcher computes the specification: `matchWith_eq` states that `matchWith pat pn msg n` is
`Spec.answer` for the first `pn` words of `pat`, read as the compiled code reads them, and the
first `n` bytes of `msg`.  The pass over the pattern follows `Spec.run` by `scan_run`, the follow
table and the masks then hold `Next` and `Class` of the decoded expression, and `runInput_bit`
and `lang_iff_steps` give the answer for the input. -/

namespace Library.Regex.Proof

open Library.Regex Library.Regex.Bits Library.Regex.Spec Library.Regex.Glushkov
  Library.Regex.RunProof Library.Regex.ScanProof

/-- A loop that applies `f` to the values `g j` in order is a fold over them. -/
theorem loop_foldl {α : Type} (n : UInt64) (init : α) (f : α → UInt64 → α) (g : Nat → UInt64) :
    LeanExe.loop n init (fun j s => f s (g j.toNat)) =
      ((List.range n.toNat).map g).foldl f init := by
  refine LeanExe.IR.loop_induction
    (P := fun k s => s = ((List.range k).map g).foldl f init) rfl ?_
  intro k s hk ih
  rw [ih, toNat_ofNat_lt hk (UInt64.toNat_lt n).le, List.range_succ, List.map_append,
    List.foldl_append]
  rfl

/-- Two words share a bit exactly when their conjunction is not zero. -/
theorem and_ne_zero (a b : UInt64) :
    (a &&& b != 0) = true ↔ ∃ q, bit a q = true ∧ bit b q = true := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : a &&& b = 0 := ext fun q => by
      rw [bit_and, bit_zero]
      cases ha : bit a q
      · rfl
      · simpa [ha] using hne q ha
    simp [this] at h
  · rintro ⟨q, ha, hb⟩
    have hq : bit (a &&& b) q = true := by rw [bit_and, ha, hb]; rfl
    simp only [bne_iff_ne, ne_eq]
    intro h
    rw [h, bit_zero] at hq
    exact absurd hq Bool.false_ne_true

theorem bit_one (q : Nat) : bit (1 : UInt64) q = (q == 0) := by
  have := bit_one_shiftLeft (p := 0) (by decide) q
  rwa [show (1 : UInt64) <<< (0 : UInt64) = 1 from rfl] at this

/-- The positions of an expression of at most 63 positions are below 64. -/
theorem range_lt {r : Re} {q : Nat} (hr : r.positions ≤ 63) (h : InRange r 0 q) : q < 64 := by
  simp only [InRange] at h; omega

theorem matchWith_eq (pat msg : Array UInt64) (pn n : UInt64) (hpn : 3 * pn.toNat < 2 ^ 64) :
    matchWith pat pn msg n =
      answer ((List.range pn.toNat).map (fun j => pat[j]!))
        ((List.range n.toNat).map (Library.Bytes.byteAt msg)) := by
  set W := (List.range pn.toNat).map (fun j => pat[j]!) with hW
  set input := (List.range n.toNat).map (Library.Bytes.byteAt msg) with hinput
  have hscan : scan pat pn = W.foldl scanStep
      ⟨true, 0, 0, 0, LeanExe.build (3 * UInt64.ofNat pn.toNat) (fun _ => 0),
        LeanExe.build 64 (fun _ => 0), LeanExe.build 256 (fun _ => 0)⟩ := by
    rw [scan, UInt64.ofNat_toNat]
    exact loop_foldl pn _ scanStep (fun j => pat[j]!)
  obtain ⟨hsome, hnone⟩ := scan_run hpn W [] _ (init_corr hpn) (by simp [hW]) (by simp [hW, total])
  simp only [List.reverse_nil] at hsome hnone
  unfold matchWith answer decode
  simp only [show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl]
  rw [hscan]
  generalize W.foldl scanStep _ = s at hsome hnone
  -- The test that the program makes before it runs the input.
  have hfail : ∀ st : List Re, (st = [] ∨ 2 ≤ st.length) → Corr pn.toNat s st.reverse →
      (!(s.valid && s.skip == 0 && s.depth == 1)) = true := by
    intro st hst hc
    have : (s.depth == 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := hc.depth
      rw [h, List.length_reverse] at this
      rcases hst with rfl | hst
      · simp at this
      · simp at this; omega
    simp [this]
  cases hrun : run W [] with
  | none =>
    have hf := hnone hrun
    have hc : (!(s.valid && s.skip == 0 && s.depth == 1)) = true := by
      cases hv : s.valid
      · simp
      · have : s.skip ≠ 0 := fun h => hf ⟨hv, h⟩
        simp [this]
    simp [hc]
  | some st =>
    have hc := hsome st hrun
    rcases st with _ | ⟨r, _ | ⟨r2, rest⟩⟩
    · simp [hfail [] (Or.inl rfl) hc]
    · simp only [List.reverse_singleton] at hc
      have hcount : s.count.toNat = r.positions := by rw [hc.count]; simp [total]
      have hok : (!(s.valid && s.skip == 0 && s.depth == 1)) = false := by
        have hd : s.depth = 1 := UInt64.toNat_inj.mp (by rw [hc.depth]; rfl)
        simp [hc.valid, hc.skip, hd]
      simp only [hok, Bool.false_eq_true, ↓reduceIte]
      by_cases hpos : 63 < r.positions
      · have : 63 < s.count := by rw [UInt64.lt_iff_toNat_lt, hcount]; simpa using hpos
        simp [this, hpos]
      · have hle : ¬ 63 < s.count := by rw [UInt64.lt_iff_toNat_lt, hcount]; simpa using hpos
        have hr : r.positions ≤ 63 := by omega
        simp only [hle, hpos, ↓reduceIte]
        -- The entry of the expression and the follow table with the start's first positions.
        have hoff : off [r] 0 = 0 := rfl
        obtain ⟨he0, he1, he2⟩ := hc.entries 0 (by simp)
        simp only [List.getElem_singleton, show off [r] 0 = 0 from rfl, Nat.mul_zero,
          Nat.zero_add] at he0 he1 he2
        have hF : ∀ p, p < 64 → ∀ q, bit (s.follow.set! 0 s.stack[1]!)[p]! q = true ↔
            Automaton.Next r p q := by
          intro p hp q
          by_cases hp0 : p = 0
          · subst hp0
            rw [get_set_self (by rw [hc.followSize]; decide), he1]
            simp only [Automaton.Next, ↓reduceIte]
            exact ⟨fun h => h.2, fun h => ⟨range_lt hr (first_range h), h⟩⟩
          · rw [get_set_ne (Ne.symm hp0), hc.follow p hp q]
            simp only [Automaton.Next, hp0, ↓reduceIte]
            constructor
            · rintro ⟨_, e, he, h⟩
              have : e = 0 := by simpa using he
              subst this
              simpa [hoff] using h
            · intro h
              exact ⟨range_lt hr (follow_range h).2, 0, by simp, by simpa [hoff] using h⟩
        have hcount63 : s.count.toNat ≤ 63 := by rw [hcount]; exact hr
        have hM : ∀ (c : UInt8) q, bit (masks s.sets s.count)[c.toNat]! q = true ↔
            Class r 0 q c := by
          intro c q
          rw [masks_bit s.sets hcount63 c.toNat_lt]
          constructor
          · rintro ⟨i, hi, rfl, hin⟩
            have := (hc.sets (i + 1) (by omega) (by simp [total]; omega)
              (by omega) c).1 hin
            obtain ⟨e, he, h⟩ := this
            have : e = 0 := by simpa using he
            subst this
            simpa [hoff] using h
          · intro h
            have hq := class_range h
            simp only [InRange] at hq
            refine ⟨q - 1, by omega, by omega, ?_⟩
            rw [show q - 1 + 1 = q by omega]
            exact (hc.sets q (by omega) (by simp [total]; omega) (by omega) c).2
              ⟨0, by simp, by simpa [hoff] using h⟩
        have hstates : ∀ p q, Automaton.Next r p q → q < 64 := by
          intro p q h
          unfold Automaton.Next at h
          split at h
          · exact range_lt hr (first_range h)
          · exact range_lt hr (follow_range h).2
        have hrun := runInput_bit r (s.follow.set! 0 s.stack[1]!) (masks s.sets s.count) msg n
          hF hM hstates
        have haccept : ∀ q, bit (s.stack[2]! ||| (if s.stack[0]! == 1 then 1 else 0)) q = true ↔
            Automaton.Final r q := by
          intro q
          rw [bit_or, Bool.or_eq_true, he2, he0, flag_eq_one]
          unfold Automaton.Final
          by_cases hq : q = 0
          · subst hq
            have : ¬ Last r 0 0 := fun h => by have := last_range h; simp [InRange] at this
            cases nullable r <;> simp [this, bit_one, bit_zero]
          · simp only [hq, ↓reduceIte]
            cases hn : nullable r
            · simp only [Bool.false_eq_true, ↓reduceIte, bit_zero, or_false]
              exact ⟨fun h => h.2, fun h => ⟨range_lt hr (last_range h), h⟩⟩
            · simp only [↓reduceIte, bit_one, beq_iff_eq, hq, or_false]
              exact ⟨fun h => h.2, fun h => ⟨range_lt hr (last_range h), h⟩⟩
        have hiff : (runInput (steps (s.follow.set! 0 s.stack[1]!)) (masks s.sets s.count) msg n &&&
            (s.stack[2]! ||| (if s.stack[0]! == 1 then 1 else 0)) != 0) = true ↔
            input ∈ r.lang := by
          rw [and_ne_zero, Automaton.lang_iff_steps]
          constructor
          · rintro ⟨q, h1, h2⟩
            exact ⟨q, (hrun q).1 h1, (haccept q).1 h2⟩
          · rintro ⟨q, h1, h2⟩
            exact ⟨q, (hrun q).2 h1, (haccept q).2 h2⟩
        by_cases hin : input ∈ r.lang
        · simp only [hiff.2 hin, hin, ↓reduceIte]
        · have : (runInput (steps (s.follow.set! 0 s.stack[1]!)) (masks s.sets s.count) msg n &&&
              (s.stack[2]! ||| (if s.stack[0]! == 1 then 1 else 0)) != 0) = false := by
            cases h : (runInput (steps (s.follow.set! 0 s.stack[1]!)) (masks s.sets s.count)
              msg n &&&
              (s.stack[2]! ||| (if s.stack[0]! == 1 then 1 else 0)) != 0)
            · rfl
            · exact absurd (hiff.1 h) hin
          simp only [this, hin, Bool.false_eq_true, ↓reduceIte]
    · simp [hfail (r :: r2 :: rest) (Or.inr (by simp)) hc]

#print axioms matchWith_eq

end Library.Regex.Proof
