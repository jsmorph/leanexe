import Demos.Screening.Isolation

/-!
The theorems of `screen` over its input array.  For a valid input, `screen_cover` states that
every time of the window at which the Kepler trajectories lie within `D + P` lies in a returned
interval (I1), `screen_sound` states the same for any trajectories within the padding of the
Kepler trajectories and the threshold `D` (S1), `screen_certain` that a certain interval holds a
close approach (I2), `screen_apsides` and `screen_path` that statuses 1 and 2 exclude the pair for
all time (F1 and F2), and `screen_path_close` that path verdict 2 finds two path points within
`D + P`.  `screen_invalid` states that status 4 marks the inputs that `valid` rejects.
-/

namespace Demos.Screening

open LeanExe.ProofKit LeanExe.Dialect Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

/-- The orbit of the elements from index `b` of an input. -/
noncomputable def orbitIn (xs : Array Float) (b : UInt64) : Orbit :=
  orbitOf (rd xs b) (rd xs (b + 1)) (rd xs (b + 2)) (rd xs (b + 3)) (rd xs (b + 4))
    (rd xs (b + 5)) (rd xs (b + 6))

/-- The gravitational parameter of an input. -/
noncomputable def muIn (xs : Array Float) : ℝ := val (rd xs 15)

/-- The threshold `D + P` of an input. -/
noncomputable def threshold (xs : Array Float) : ℝ := val (rd xs 18) + val (rd xs 19)

/-- The separation of the Kepler trajectories of an input at `t` minutes. -/
noncomputable def separation (xs : Array Float) (t : ℝ) : ℝ :=
  sepAt (muIn xs) (orbitIn xs 1) (orbitIn xs 8) t

/-- `t` lies in a returned interval: the interval with the ends at indices `5 + 3j` and
`6 + 3j` of the output, whose certainty is at index `7 + 3j`. -/
def Returned (out : Array Float) (t : ℝ) : Prop :=
  ∃ j, 7 + 3 * j < out.size ∧ val out[5 + 3 * j]! ≤ t ∧ t ≤ val out[6 + 3 * j]!

/-! ### The facts of a valid input -/

theorem val_one : val 1.0 = 1 := one_value.2

/-- The facts that `valid` establishes. -/
structure Facts (xs : Array Float) : Prop where
  v1 : (orbitIn xs 1).Valid
  v2 : (orbitIn xs 8).Valid
  d : 0 ≤ val (rd xs 18)
  p : 0 ≤ val (rd xs 19)
  t0 : Finite (rd xs 16).toBits
  t1 : Finite (rd xs 17).toBits
  capPath : (rd xs 22).toUInt64.toNat ≤ 1048576
  cap : (rd xs 24).toUInt64.toNat ≤ 1048576

theorem allFinite_spec {xs : Array Float} (h : allFinite xs = true) :
    ∀ i < xs.size.toUInt64.toNat, Finite (rd xs (UInt64.ofNat i)).toBits := by
  have key := loop_induction (n := xs.size.toUInt64) (init := true)
    (f := fun i ok => ok && finite (rd xs i))
    (fun k ok => ok = true → ∀ i < k, Finite (rd xs (UInt64.ofNat i)).toBits)
    (fun _ i hi => absurd hi (Nat.not_lt_zero i))
    (fun k ok _ ih hk i hi => by
      simp only [Bool.and_eq_true] at hk
      by_cases hik : i < k
      · exact ih hk.1 i hik
      · have : i = k := by omega
        subst this
        exact (finite_iff _).mp hk.2)
  exact key h

theorem lit_zero_finite : Finite (0.0 : Float).toBits := by
  have hb : (0.0 : Float).toBits = 0 := by decide +kernel
  rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel

theorem pos_of_lt {x : Float} (hx : Finite x.toBits) (h : 0.0 < x) : 0 < val x := by
  have := (lt_iff_value lit_zero_finite hx).mp h
  rwa [show value (0.0 : Float).toBits = 0 from val_zero] at this

theorem nonneg_of_le {x : Float} (hx : Finite x.toBits) (h : 0.0 ≤ x) : 0 ≤ val x := by
  have := (le_iff_value lit_zero_finite hx).mp h
  rwa [show value (0.0 : Float).toBits = 0 from val_zero] at this

theorem lt_one_of_lt {x : Float} (hx : Finite x.toBits) (h : x < 1.0) : val x < 1 := by
  have := (lt_iff_value hx one_value.1).mp h
  rwa [show value (1.0 : Float).toBits = 1 from val_one] at this

theorem valid_facts {xs : Array Float} (h : valid xs = true) : Facts xs := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsz, hfin⟩, -⟩, ho1⟩, ho2⟩, -⟩, -⟩, -⟩, -⟩, hd⟩, hp⟩, -⟩, -⟩, hcp⟩, -⟩,
    hc⟩ := h
  have fin := allFinite_spec hfin
  rw [hsz] at fin
  have f : ∀ i < 25, Finite (rd xs (UInt64.ofNat i)).toBits := fun i hi => fin i (by simpa using hi)
  simp only [orbitOk, Bool.and_eq_true, decide_eq_true_eq] at ho1 ho2
  simp only [isWhole, Bool.and_eq_true, decide_eq_true_eq] at hc hcp
  have u1 : ∀ x : UInt64, x ≤ 1048576 → x.toNat ≤ 1048576 := fun x hx => by
    have := UInt64.le_iff_toNat_le.mp hx
    simpa using this
  exact ⟨⟨pos_of_lt (f 1 (by norm_num)) ho1.1.1, nonneg_of_le (f 2 (by norm_num)) ho1.1.2,
      lt_one_of_lt (f 2 (by norm_num)) ho1.2⟩,
    ⟨pos_of_lt (f 8 (by norm_num)) ho2.1.1, nonneg_of_le (f 9 (by norm_num)) ho2.1.2,
      lt_one_of_lt (f 9 (by norm_num)) ho2.2⟩,
    nonneg_of_le (f 18 (by norm_num)) hd, nonneg_of_le (f 19 (by norm_num)) hp,
    f 16 (by norm_num), f 17 (by norm_num), u1 _ hcp.2, u1 _ hc.2⟩

/-! ### The output -/

theorem append_get_right {α : Type} [Inhabited α] (a b : Array α) (k : Nat) (hk : k < b.size) :
    (a ++ b)[a.size + k]! = b[k]! := by
  rw [getElem!_pos (a ++ b) (a.size + k) (by simp; omega), getElem!_pos b k hk]
  simp [Array.getElem_append_right]

theorem append_get_left {α : Type} [Inhabited α] (a b : Array α) (k : Nat) (hk : k < a.size) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos a k hk]
  simp [Array.getElem_append_left hk]

/-- The isolation's output: its size, its status and verdict fields, and its intervals. -/
theorem isolationOutput_spec {xs : Array Float} (F : Facts xs) {o1 o2 : Obj} {thr : Interval}
    (e1 : Encl o1 (muIn xs) (orbitIn xs 1)) (e2 : Encl o2 (muIn xs) (orbitIn xs 8))
    (ht : Encloses thr (threshold xs)) (p : PathSearch) :
    let out := isolationOutput Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) xs p
    (out[0]!.toBits = (0 : UInt64).toFloat.toBits ∨ out[0]!.toBits = (3 : UInt64).toFloat.toBits) ∧
      out[2]! = p.verdict.toFloat ∧
      (∀ t, val (rd xs 16) ≤ t → t ≤ val (rd xs 17) → separation xs t ≤ threshold xs →
        Returned out t) ∧
      ∀ j, 7 + 3 * j < out.size → out[7 + 3 * j]! = 1.0 →
        ∃ t, val out[5 + 3 * j]! ≤ t ∧ t ≤ val out[6 + 3 * j]! ∧
          separation xs t ≤ threshold xs := by
  intro out
  have hT : 0 ≤ threshold xs := add_nonneg F.d F.p
  have I := isolate_inv F.v1 F.v2 e1 e2 ht F.t0 F.t1 (levels := (rd xs 23).toUInt64) F.cap
  simp only [out, isolationOutput]
  generalize isolate Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) (rd xs 16) (rd xs 17)
    (rd xs 23).toUInt64 (rd xs 24).toUInt64 = s at I ⊢
  obtain ⟨fsz, fkeep, fcov⟩ := finalSpans_spec F.v1 F.v2 e1 e2 ht hT I.size I.fin
  generalize finalSpans Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) s.cells = found
    at fsz fkeep fcov ⊢
  obtain ⟨msz, mkeep, mcov⟩ := merge_spec (T := threshold xs) (mu := muIn xs)
    (orb1 := orbitIn xs 1) (orb2 := orbitIn xs 8) (by have := I.size; omega) fkeep
  generalize merge found = ivs at msz mkeep mcov ⊢
  obtain ⟨tsz, tget⟩ := triples_spec ivs (by have := I.size; omega)
  generalize hh : (#[s.status.toFloat, ivs.size.toUInt64.toFloat, p.verdict.toFloat,
    (p.tests + s.tests + s.cells.size.toUInt64).toFloat, s.levels.toFloat] : Array Float) = head
  have hs : head.size = 5 := by rw [← hh]; rfl
  have h0 : head[0]! = s.status.toFloat := by rw [← hh]; rfl
  have h2 : head[2]! = p.verdict.toFloat := by rw [← hh]; rfl
  have osz : (head ++ triples ivs).size = 5 + 3 * ivs.size := by simp [hs, tsz]
  have lo : ∀ j < ivs.size, (head ++ triples ivs)[5 + 3 * j]! = ivs[j]!.lo := fun j hj => by
    rw [← hs, append_get_right _ _ _ (by omega)]; exact (tget j hj).1
  have hi : ∀ j < ivs.size, (head ++ triples ivs)[6 + 3 * j]! = ivs[j]!.hi := fun j hj => by
    rw [show 6 + 3 * j = head.size + (3 * j + 1) by omega, append_get_right _ _ _ (by omega)]
    exact (tget j hj).2.1
  have ce : ∀ j < ivs.size, (head ++ triples ivs)[7 + 3 * j]! = ivs[j]!.certain.toFloat :=
    fun j hj => by
      rw [show 7 + 3 * j = head.size + (3 * j + 2) by omega, append_get_right _ _ _ (by omega)]
      exact (tget j hj).2.2
  refine ⟨?_, ?_, fun t a b c => ?_, fun j hj hf => ?_⟩
  · rw [append_get_left _ _ 0 (by omega), h0]
    rcases I.status with h | h <;> rw [h] <;> simp
  · rw [append_get_left _ _ 2 (by omega), h2]
  · obtain ⟨i, hi', hm⟩ := I.cover t a b c
    obtain ⟨k, hk, hmk⟩ := fcov t ⟨i, hi', hm⟩ c
    obtain ⟨j, hj, hmj⟩ := mcov t ⟨k, hk, hmk⟩
    exact ⟨j, by omega, by rw [lo j hj]; exact hmj.1, by rw [hi j hj]; exact hmj.2⟩
  · have hj' : j < ivs.size := by omega
    have K := mkeep j hj'
    rw [ce j hj'] at hf
    have h1 : ivs[j]!.certain = 1 := by
      rcases K.flag with h | h
      · rw [h] at hf; exact absurd (congrArg Float.toBits hf) (by decide +kernel)
      · exact h
    obtain ⟨t, hm, hs'⟩ := K.certain h1
    exact ⟨t, by rw [lo j hj']; exact hm.1, by rw [hi j hj']; exact hm.2, hs'⟩

/-! ### The theorems of `screen` -/

theorem lit5_get0 (a b c d e : Float) : (#[a, b, c, d, e] : Array Float)[0]! = a := rfl

theorem lit5_get2 (a b c d e : Float) : (#[a, b, c, d, e] : Array Float)[2]! = c := rfl

theorem lit5_size (a b c d e : Float) : (#[a, b, c, d, e] : Array Float).size = 5 := rfl

section Screen

variable {xs : Array Float}

theorem encl1 : Encl (objectAt Trig.invPi Trig.halfPi xs 1) (muIn xs) (orbitIn xs 1) :=
  object_encl _ _ _ _ _ _ _ _

theorem encl8 : Encl (objectAt Trig.invPi Trig.halfPi xs 8) (muIn xs) (orbitIn xs 8) :=
  object_encl _ _ _ _ _ _ _ _

theorem encl_thr :
    Encloses (add (point (rd xs 18)) (point (rd xs 19))) (threshold xs) :=
  encloses_add (encloses_point _) (encloses_point _)

/-- **I1.**  For a valid input, every time of the window at which the Kepler trajectories lie
within `D + P` lies in a returned interval. -/
theorem screen_cover (hv : valid xs = true) {t : ℝ} (ht0 : val (rd xs 16) ≤ t)
    (ht1 : t ≤ val (rd xs 17)) (hc : separation xs t ≤ threshold xs) : Returned (screen xs) t := by
  have F := valid_facts hv
  have e1 := encl1 (xs := xs)
  have e2 := encl8 (xs := xs)
  have ht := encl_thr (xs := xs)
  have hT : 0 ≤ threshold xs := add_nonneg F.d F.p
  unfold screen screenWith
  rw [ite_eq_left hv]
  dsimp only
  generalize objectAt Trig.invPi Trig.halfPi xs 1 = o1 at e1 ⊢
  generalize objectAt Trig.invPi Trig.halfPi xs 8 = o2 at e2 ⊢
  generalize add (point (rd xs 18)) (point (rd xs 19)) = thr at ht ⊢
  split_ifs with ha hp
  · simp only [Bool.and_eq_true] at ha
    exact absurd hc (not_le.mpr (apsidesExclude_sound e1 e2 F.v1 F.v2 ht ha.2
      ((orbitIn xs 1).anomaly (muIn xs) t) ((orbitIn xs 8).anomaly (muIn xs) t)))
  · exact absurd hc (not_le.mpr (pathFilter_sound e1 e2 ht hT F.capPath (beq_iff_eq.mp hp)
      ((orbitIn xs 1).anomaly (muIn xs) t) ((orbitIn xs 8).anomaly (muIn xs) t)))
  · exact (isolationOutput_spec F e1 e2 ht _).2.2.1 t ht0 ht1 hc

/-- **S1.**  For a valid input and trajectories `ρ₁` and `ρ₂` that stay within `δ₁` and `δ₂` of
the Kepler trajectories during the window, with `δ₁ + δ₂ ≤ P`, every time of the window at which
`ρ₁` and `ρ₂` lie within `D` lies in a returned interval. -/
theorem screen_sound (hv : valid xs = true) {ρ1 ρ2 : ℝ → ℝ × ℝ × ℝ} {δ1 δ2 : ℝ}
    (hδ : δ1 + δ2 ≤ val (rd xs 19))
    (h1 : ∀ t, val (rd xs 16) ≤ t → t ≤ val (rd xs 17) →
      dist3 (ρ1 t) ((orbitIn xs 1).position (muIn xs) t) ≤ δ1)
    (h2 : ∀ t, val (rd xs 16) ≤ t → t ≤ val (rd xs 17) →
      dist3 (ρ2 t) ((orbitIn xs 8).position (muIn xs) t) ≤ δ2)
    {t : ℝ} (ht0 : val (rd xs 16) ≤ t) (ht1 : t ≤ val (rd xs 17))
    (hc : dist3 (ρ1 t) (ρ2 t) ≤ val (rd xs 18)) : Returned (screen xs) t := by
  apply screen_cover hv ht0 ht1
  unfold separation sepAt threshold
  have a := dist3_triangle ((orbitIn xs 1).position (muIn xs) t) (ρ1 t)
    ((orbitIn xs 8).position (muIn xs) t)
  have b := dist3_triangle (ρ1 t) (ρ2 t) ((orbitIn xs 8).position (muIn xs) t)
  rw [dist3_comm ((orbitIn xs 1).position (muIn xs) t) (ρ1 t)] at a
  linarith [h1 t ht0 ht1, h2 t ht0 ht1]

/-- **I2.**  For a valid input, a returned interval marked certain holds a time at which the Kepler
trajectories lie within `D + P`. -/
theorem screen_certain (hv : valid xs = true) {j : Nat} (hj : 7 + 3 * j < (screen xs).size)
    (hf : (screen xs)[7 + 3 * j]! = 1.0) :
    ∃ t, val (screen xs)[5 + 3 * j]! ≤ t ∧ t ≤ val (screen xs)[6 + 3 * j]! ∧
      separation xs t ≤ threshold xs := by
  have F := valid_facts hv
  have e1 := encl1 (xs := xs)
  have e2 := encl8 (xs := xs)
  have ht := encl_thr (xs := xs)
  revert hj hf
  unfold screen screenWith
  rw [ite_eq_left hv]
  dsimp only
  generalize objectAt Trig.invPi Trig.halfPi xs 1 = o1 at e1 ⊢
  generalize objectAt Trig.invPi Trig.halfPi xs 8 = o2 at e2 ⊢
  generalize add (point (rd xs 18)) (point (rd xs 19)) = thr at ht ⊢
  split_ifs
  · intro hj; rw [lit5_size] at hj; omega
  · intro hj; rw [lit5_size] at hj; omega
  · exact (isolationOutput_spec F e1 e2 ht _).2.2.2 j

/-- **F1.**  For a valid input with status 1, the Kepler trajectories lie farther than `D + P`
apart at every time. -/
theorem screen_apsides (hv : valid xs = true) (h : (screen xs)[0]! = 1.0) (t : ℝ) :
    threshold xs < separation xs t := by
  have F := valid_facts hv
  have e1 := encl1 (xs := xs)
  have e2 := encl8 (xs := xs)
  have ht := encl_thr (xs := xs)
  revert h
  unfold screen screenWith
  rw [ite_eq_left hv]
  dsimp only
  generalize objectAt Trig.invPi Trig.halfPi xs 1 = o1 at e1 ⊢
  generalize objectAt Trig.invPi Trig.halfPi xs 8 = o2 at e2 ⊢
  generalize add (point (rd xs 18)) (point (rd xs 19)) = thr at ht ⊢
  split_ifs with ha
  · intro _
    simp only [Bool.and_eq_true] at ha
    exact apsidesExclude_sound e1 e2 F.v1 F.v2 ht ha.2 _ _
  · intro h
    rw [lit5_get0] at h
    exact absurd (congrArg Float.toBits h) (by decide +kernel)
  · intro h
    rcases (isolationOutput_spec F e1 e2 ht _).1 with s | s <;> rw [h] at s <;>
      exact absurd s (by decide +kernel)

/-- **F2.**  For a valid input with status 2, the Kepler trajectories lie farther than `D + P`
apart at every time. -/
theorem screen_path (hv : valid xs = true) (h : (screen xs)[0]! = 2.0) (t : ℝ) :
    threshold xs < separation xs t := by
  have F := valid_facts hv
  have e1 := encl1 (xs := xs)
  have e2 := encl8 (xs := xs)
  have ht := encl_thr (xs := xs)
  have hT : 0 ≤ threshold xs := add_nonneg F.d F.p
  revert h
  unfold screen screenWith
  rw [ite_eq_left hv]
  dsimp only
  generalize objectAt Trig.invPi Trig.halfPi xs 1 = o1 at e1 ⊢
  generalize objectAt Trig.invPi Trig.halfPi xs 8 = o2 at e2 ⊢
  generalize add (point (rd xs 18)) (point (rd xs 19)) = thr at ht ⊢
  split_ifs with ha hp
  · intro h
    rw [lit5_get0] at h
    exact absurd (congrArg Float.toBits h) (by decide +kernel)
  · intro _
    exact pathFilter_sound e1 e2 ht hT F.capPath (beq_iff_eq.mp hp) _ _
  · intro h
    rcases (isolationOutput_spec F e1 e2 ht _).1 with s | s <;> rw [h] at s <;>
      exact absurd s (by decide +kernel)

/-- **F2.**  For a valid input with path verdict 2, some point of each path lies within `D + P` of
some point of the other. -/
theorem screen_path_close (hv : valid xs = true) (h : (screen xs)[2]! = 2.0) :
    ∃ E1 E2, dist3 ((orbitIn xs 1).path E1) ((orbitIn xs 8).path E2) ≤ threshold xs := by
  have F := valid_facts hv
  have e1 := encl1 (xs := xs)
  have e2 := encl8 (xs := xs)
  have ht := encl_thr (xs := xs)
  have hT : 0 ≤ threshold xs := add_nonneg F.d F.p
  revert h
  unfold screen screenWith
  rw [ite_eq_left hv]
  dsimp only
  generalize objectAt Trig.invPi Trig.halfPi xs 1 = o1 at e1 ⊢
  generalize objectAt Trig.invPi Trig.halfPi xs 8 = o2 at e2 ⊢
  generalize add (point (rd xs 18)) (point (rd xs 19)) = thr at ht ⊢
  split_ifs with ha hp
  · intro h
    rw [lit5_get2] at h
    exact absurd (congrArg Float.toBits h) (by decide +kernel)
  · intro h
    rw [lit5_get2] at h
    exact absurd (congrArg Float.toBits h) (by decide +kernel)
  · intro h
    rw [(isolationOutput_spec F e1 e2 ht _).2.1] at h
    have inv := pathFilter_inv e1 e2 ht hT (levels := (rd xs 21).toUInt64) F.capPath
    have hv2 : (pathFilter Trig.invPi Trig.halfPi o1 o2 (mul thr thr) (rd xs 21).toUInt64
        (rd xs 22).toUInt64).verdict = 2 := by
      rcases inv.range with r | r | r | r | r <;> rw [r] at h ⊢ <;>
        first | rfl | exact absurd (congrArg Float.toBits h) (by decide +kernel)
    exact pathFilter_close e1 e2 ht hT F.capPath hv2

/-- Status 4 marks exactly the inputs that `valid` rejects. -/
theorem screen_invalid : (screen xs)[0]! = 4.0 ↔ valid xs = false := by
  constructor
  · intro h
    by_contra hv
    have hv' : valid xs = true := by simpa using hv
    have F := valid_facts hv'
    have e1 := encl1 (xs := xs)
    have e2 := encl8 (xs := xs)
    have ht := encl_thr (xs := xs)
    revert h
    unfold screen screenWith
    rw [ite_eq_left hv']
    dsimp only
    generalize objectAt Trig.invPi Trig.halfPi xs 1 = o1 at e1 ⊢
    generalize objectAt Trig.invPi Trig.halfPi xs 8 = o2 at e2 ⊢
    generalize add (point (rd xs 18)) (point (rd xs 19)) = thr at ht ⊢
    split_ifs
    · intro h
      rw [lit5_get0] at h
      exact absurd (congrArg Float.toBits h) (by decide +kernel)
    · intro h
      rw [lit5_get0] at h
      exact absurd (congrArg Float.toBits h) (by decide +kernel)
    · intro h
      rcases (isolationOutput_spec F e1 e2 ht _).1 with s | s <;> rw [h] at s <;>
        exact absurd s (by decide +kernel)
  · intro h
    unfold screen screenWith
    rw [ite_eq_right (by simp [h])]
    rfl

/-- **S1** for statuses 1 and 2.  For a valid input with status 1 or 2, trajectories within the
padding of the Kepler trajectories lie farther than `D` apart at every time of the window. -/
theorem screen_excluded (hv : valid xs = true) (hs : (screen xs).size = 5)
    {ρ1 ρ2 : ℝ → ℝ × ℝ × ℝ} {δ1 δ2 : ℝ} (hδ : δ1 + δ2 ≤ val (rd xs 19))
    (h1 : ∀ t, val (rd xs 16) ≤ t → t ≤ val (rd xs 17) →
      dist3 (ρ1 t) ((orbitIn xs 1).position (muIn xs) t) ≤ δ1)
    (h2 : ∀ t, val (rd xs 16) ≤ t → t ≤ val (rd xs 17) →
      dist3 (ρ2 t) ((orbitIn xs 8).position (muIn xs) t) ≤ δ2)
    {t : ℝ} (ht0 : val (rd xs 16) ≤ t) (ht1 : t ≤ val (rd xs 17)) :
    val (rd xs 18) < dist3 (ρ1 t) (ρ2 t) := by
  by_contra hc
  obtain ⟨j, hj, -⟩ := screen_sound hv hδ h1 h2 ht0 ht1 (not_lt.mp hc)
  omega

end Screen

end Demos.Screening
