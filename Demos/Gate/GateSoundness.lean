import Demos.Gate.GateProgram
import Demos.Gate.Soundness
import Demos.Gate.Mahalanobis

/-!
Soundness of the gate.  `gate_sound` states that an accepted result of `gate` belongs to a
positive definite covariance, that its interval contains the squared Mahalanobis distance of the
real values, and that its verdict compares that distance with the threshold.  The proof follows the elimination: after
step `k`, each accepted entry of the interval matrix contains the entry of `Model.elimA`, each
entry of the right-hand side the entry of `Model.elimR`, and the sum `Model.quad`, and every pivot
so far is positive.
-/

namespace Demos.Gate

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-- The real matrix of the `d × d` values of `s` in row-major order, and zero outside. -/
noncomputable def matOf (s : Array Float) (d : ℕ) : ℕ → ℕ → ℝ :=
  fun i j => if i < d ∧ j < d then value (s[i * d + j]!).toBits else 0

/-- The real vector of the values of `nu`. -/
noncomputable def vecOf (nu : Array Float) : ℕ → ℝ := fun i => value (nu[i]!).toBits

/-! ### Checks of the input -/

theorem ofNat_toNat {k : ℕ} (h : k < 2 ^ 64) : (UInt64.ofNat k).toNat = k :=
  UInt64.toNat_ofNat_of_lt' h

theorem toNat_lt64 (n : UInt64) : n.toNat < 2 ^ 64 := n.toNat_lt_size

theorem allFinite_sound {xs : Array Float} {n : UInt64} (h : allFinite xs n = true) :
    ∀ i < n.toNat, Finite (xs[i]!).toBits := by
  unfold allFinite at h
  refine LeanExe.Dialect.loop_induction (n := n) (init := true)
    (P := fun k (ok : Bool) => ok = true → ∀ i < k, Finite (xs[i]!).toBits)
    (fun _ i hi => absurd hi (Nat.not_lt_zero i)) ?_ h
  intro k ok hk ih hs i hi
  have hk' : (UInt64.ofNat k).toNat = k := ofNat_toNat (by have := toNat_lt64 n; omega)
  simp only [Bool.and_eq_true] at hs
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
  · exact ih hs.1 i hi
  · rw [hk'] at hs
    rw [hi]
    exact (finite_iff _).mp hs.2

theorem div_mod_index {t d : ℕ} (hd : 0 < d) (ht : t < d * d) :
    t / d < d ∧ t % d < d ∧ t / d * d + t % d = t := by
  refine ⟨Nat.div_lt_of_lt_mul ht, Nat.mod_lt _ hd, ?_⟩
  rw [Nat.mul_comm]
  exact Nat.div_add_mod t d

theorem index_div {i j d : ℕ} (hj : j < d) : (i * d + j) / d = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]

theorem index_mod {i j d : ℕ} (hj : j < d) : (i * d + j) % d = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem symmetric_sound {s : Array Float} {d : UInt64} (hd : d.toNat ≤ 64)
    (hfin : ∀ t < d.toNat * d.toNat, Finite (s[t]!).toBits) (h : symmetric s d = true) :
    Model.Symm (matOf s d.toNat) := by
  have hdd : (d * d).toNat = d.toNat * d.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by nlinarith)]
  have key : ∀ t < d.toNat * d.toNat,
      value (s[t]!).toBits = value (s[t % d.toNat * d.toNat + t / d.toNat]!).toBits := by
    unfold symmetric at h
    rw [← hdd]
    refine LeanExe.Dialect.loop_induction (n := d * d) (init := true)
      (P := fun k (ok : Bool) => ok = true → ∀ t < k,
        value (s[t]!).toBits = value (s[t % d.toNat * d.toNat + t / d.toNat]!).toBits)
      (fun _ i hi => absurd hi (Nat.not_lt_zero i)) ?_ h
    intro k ok hk ih hs t ht
    have hk' : (UInt64.ofNat k).toNat = k := ofNat_toNat (by have := toNat_lt64 (d * d); omega)
    have hdpos : 0 < d.toNat := by
      rcases Nat.eq_zero_or_pos d.toNat with h0 | h0
      · rw [hdd, h0] at hk; omega
      · exact h0
    have hk2 : k < d.toNat * d.toNat := by rw [← hdd]; exact hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
    · exact ih hs.1.1 t ht
    · rw [ht]
      have hidx : (UInt64.ofNat k % d * d + UInt64.ofNat k / d).toNat =
          k % d.toNat * d.toNat + k / d.toNat := by
        have hm := Nat.mod_lt k hdpos
        have hq := Nat.div_lt_of_lt_mul hk2
        rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, UInt64.toNat_div, hk',
          Nat.mod_eq_of_lt (a := k % d.toNat * d.toNat) (by nlinarith),
          Nat.mod_eq_of_lt (by nlinarith)]
      rw [hk', hidx] at hs
      obtain ⟨⟨-, h1⟩, h2⟩ := hs
      obtain ⟨hq, hm, -⟩ := div_mod_index hdpos hk2
      have f1 := hfin k hk2
      have f2 := hfin (k % d.toNat * d.toNat + k / d.toNat) (by nlinarith)
      exact le_antisymm ((le_iff_value f1 f2).mp h1) ((le_iff_value f2 f1).mp h2)
  intro i j
  unfold matOf
  by_cases hij : i < d.toNat ∧ j < d.toNat
  · rw [ite_eq_left hij, ite_eq_left ⟨hij.2, hij.1⟩]
    have := key (i * d.toNat + j) (by nlinarith)
    rwa [index_mod hij.2, index_div hij.2] at this
  · rw [ite_eq_right hij, ite_eq_right fun h => hij ⟨h.2, h.1⟩]

/-! ### The elimination -/

theorem elimA_succ_of_not {S : ℕ → ℕ → ℝ} {k i j : ℕ} (h : ¬ (k < i ∧ k < j)) :
    Model.elimA S (k + 1) i j = Model.elimA S k i j := by
  simp only [Model.elimA, ite_eq_right h]

theorem elimR_succ_of_not {S : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {k i : ℕ} (h : ¬ k < i) :
    Model.elimR S ν (k + 1) i = Model.elimR S ν k i := by
  simp only [Model.elimR, ite_eq_right h]

theorem quad_nonneg {S : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} :
    ∀ {k : ℕ}, (∀ m < k, 0 < Model.elimA S m m m) → 0 ≤ Model.quad S ν k
  | 0, _ => le_rfl
  | k + 1, h => by
    simp only [Model.quad]
    have := h k (by omega)
    have := quad_nonneg (S := S) (ν := ν) (k := k) fun m hm => h m (by omega)
    have : 0 ≤ Model.elimR S ν k k * Model.elimR S ν k k / Model.elimA S k k k :=
      div_nonneg (mul_self_nonneg _) (h k (by omega)).le
    linarith

/-- The word index `i·d + j` of two words below `d ≤ 64`. -/
theorem word_index {I J d : UInt64} (hd : d.toNat ≤ 64) (hi : I.toNat < d.toNat)
    (hj : J.toNat < d.toNat) : (I * d + J).toNat = I.toNat * d.toNat + J.toNat := by
  have : I.toNat * d.toNat < 4096 := by nlinarith
  rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- After `k` steps, each accepted entry of the state contains the entry of the real
elimination, and the pivots so far are positive. -/
def ElimInv (S : ℕ → ℕ → ℝ) (ν : ℕ → ℝ) (d k : ℕ) (e : Elim) : Prop :=
  e.status = 0 → e.a.size = d * d ∧ e.r.size = d ∧
    (∀ t < d * d, Encloses e.a[t]! (Model.elimA S k (t / d) (t % d))) ∧
    (∀ i < d, Encloses e.r[i]! (Model.elimR S ν k i)) ∧
    Encloses e.acc (Model.quad S ν k) ∧ ∀ m < k, 0 < Model.elimA S m m m

theorem elimStep_inv {S : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {d : UInt64} {k : ℕ} (hd : d.toNat ≤ 64)
    (hk : k < d.toNat) {e : Elim} (he : ElimInv S ν d.toNat k e) :
    ElimInv S ν d.toNat (k + 1) (elimStep d (UInt64.ofNat k) e) := by
  intro hs
  have hk' : (UInt64.ofNat k).toNat = k := ofNat_toNat (by omega)
  have hdpos : 0 < d.toNat := by omega
  have hdd : (d * d).toNat = d.toNat * d.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by nlinarith)]
  unfold elimStep at hs ⊢
  by_cases g1 : (e.status == 0) = true
  · rw [ite_eq_left g1] at hs ⊢
    obtain ⟨hsa, hsr, ha, hr, hacc, hpiv⟩ := he (beq_iff_eq.mp g1)
    simp only at hs ⊢
    have hpi : (UInt64.ofNat k * d + UInt64.ofNat k).toNat = k * d.toNat + k := by
      rw [word_index hd (by rw [hk']; exact hk) (by rw [hk']; exact hk), hk']
    rw [hpi] at hs ⊢
    by_cases g2 : ((e.a[k * d.toNat + k]!).status == 0 && 0.0 < (e.a[k * d.toNat + k]!).lo) = true
    · rw [ite_eq_left g2] at hs ⊢
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g2
      set p := e.a[k * d.toNat + k]! with hp_def
      have hp : Encloses p (Model.elimA S k k k) := by
        have := ha (k * d.toNat + k) (by nlinarith)
        rwa [index_div hk, index_mod hk] at this
      have hpc := hp g2.1
      have hpos : 0 < Model.elimA S k k k := by
        have := (lt_iff_value Conjunction.lit_zero.1 hpc.2.1).mp g2.2
        rw [lit_zero_value] at this
        exact lt_of_lt_of_le this hpc.2.2.2.1
      refine ⟨by rw [LeanExe.Dialect.build_size, hdd], by rw [LeanExe.Dialect.build_size], ?_, ?_,
        ?_, ?_⟩
      · intro t ht
        rw [LeanExe.Dialect.build_get (by rw [hdd]; exact ht)]
        have htn : (UInt64.ofNat t).toNat = t := ofNat_toNat (by nlinarith)
        obtain ⟨hq, hm, hqm⟩ := div_mod_index hdpos ht
        have hI : (UInt64.ofNat t / d).toNat = t / d.toNat := by rw [UInt64.toNat_div, htn]
        have hJ : (UInt64.ofNat t % d).toNat = t % d.toNat := by rw [UInt64.toNat_mod, htn]
        have hik : (UInt64.ofNat t / d * d + UInt64.ofNat k).toNat = t / d.toNat * d.toNat + k := by
          rw [word_index hd (by rw [hI]; exact hq) (by rw [hk']; exact hk), hI, hk']
        have hjk : (UInt64.ofNat t % d * d + UInt64.ofNat k).toNat = t % d.toNat * d.toNat + k := by
          rw [word_index hd (by rw [hJ]; exact hm) (by rw [hk']; exact hk), hJ, hk']
        rw [hik, hjk, htn]
        by_cases g3 : (UInt64.ofNat k < UInt64.ofNat t / d && UInt64.ofNat k < UInt64.ofNat t % d) = true
        · rw [ite_eq_left g3]
          simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hk', hI,
            hJ] at g3
          rw [Model.elimA_succ g3.1 g3.2]
          have h1 := ha t ht
          have h2 := ha (t / d.toNat * d.toNat + k) (by nlinarith)
          have h3 := ha (t % d.toNat * d.toNat + k) (by nlinarith)
          rw [index_div hk, index_mod hk] at h2 h3
          exact encloses_sub h1 (encloses_mul (encloses_div h2 hp) h3)
        · rw [ite_eq_right g3]
          have g3' : ¬ (k < t / d.toNat ∧ k < t % d.toNat) := by
            intro hc
            apply g3
            simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hk', hI, hJ]
            exact hc
          rw [elimA_succ_of_not g3']
          exact ha t ht
      · intro i hi
        rw [LeanExe.Dialect.build_get hi]
        have hin : (UInt64.ofNat i).toNat = i := ofNat_toNat (by omega)
        have hik : (UInt64.ofNat i * d + UInt64.ofNat k).toNat = i * d.toNat + k := by
          rw [word_index hd (by rw [hin]; exact hi) (by rw [hk']; exact hk), hin, hk']
        rw [hik, hin, hk']
        by_cases g3 : UInt64.ofNat k < UInt64.ofNat i
        · rw [ite_eq_left g3]
          have g3' : k < i := by rw [UInt64.lt_iff_toNat_lt, hk', hin] at g3; exact g3
          rw [Model.elimR_succ g3']
          have h2 := ha (i * d.toNat + k) (by nlinarith)
          rw [index_div hk, index_mod hk] at h2
          exact encloses_sub (hr i hi) (encloses_mul (encloses_div h2 hp) (hr k hk))
        · rw [ite_eq_right g3]
          have g3' : ¬ k < i := by rw [UInt64.lt_iff_toNat_lt, hk', hin] at g3; exact g3
          rw [elimR_succ_of_not g3']
          exact hr i hi
      · simp only [Model.quad]
        rw [hk']
        exact encloses_add hacc (encloses_div (encloses_sq (hr k hk)) hp)
      · intro m hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
        · exact hpiv m hm
        · rw [hm]
          exact hpos
    · rw [ite_eq_right g2] at hs
      exact absurd hs (by simp)
  · rw [ite_eq_right g1] at hs
    exact absurd hs (by simpa using g1)

theorem eliminate_inv {s nu : Array Float} {d : UInt64} (hd : d.toNat ≤ 64) :
    ElimInv (matOf s d.toNat) (vecOf nu) d.toNat d.toNat (eliminate s nu d) := by
  have hdd : (d * d).toNat = d.toNat * d.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by nlinarith)]
  unfold eliminate
  refine LeanExe.Dialect.loop_induction
    (P := fun k e => ElimInv (matOf s d.toNat) (vecOf nu) d.toNat k e) ?_
    fun k e hk he => elimStep_inv hd hk he
  intro _
  refine ⟨by rw [LeanExe.Dialect.build_size, hdd], by rw [LeanExe.Dialect.build_size], ?_, ?_, ?_,
    fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  · intro t ht
    have hdpos : 0 < d.toNat := by
      rcases Nat.eq_zero_or_pos d.toNat with h0 | h0
      · rw [h0] at ht; omega
      · exact h0
    rw [LeanExe.Dialect.build_get (by rw [hdd]; exact ht)]
    have htn : (UInt64.ofNat t).toNat = t := ofNat_toNat (by nlinarith)
    obtain ⟨hq, hm, hqm⟩ := div_mod_index hdpos ht
    simp only [Model.elimA, matOf, ite_eq_left (And.intro hq hm), hqm, htn]
    exact encloses_point _
  · intro i hi
    rw [LeanExe.Dialect.build_get hi]
    have hin : (UInt64.ofNat i).toNat = i := ofNat_toNat (by omega)
    simp only [Model.elimR, vecOf, hin]
    exact encloses_point _
  · simp only [Model.quad]
    exact encloses_lit Conjunction.lit_zero

/-! ### The gate -/

/-- The real covariance of `s` as a `d × d` matrix. -/
noncomputable def covariance (s : Array Float) (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Model.toMatrix d (matOf s d)

/-- The real innovation of `nu`. -/
noncomputable def innovation (nu : Array Float) : Fin nu.size → ℝ := fun i => vecOf nu i

/-- An accepted result of `gate` belongs to `d = nu.size` from 1 to 64, `d·d` values of `s`, and
a finite threshold `γ ≥ 0`.  The real covariance is positive definite, `[lo, hi]` contains the
squared Mahalanobis distance of the real innovation, and verdict 1 implies that the distance is at
most `γ` and verdict 2 that it exceeds `γ`. -/
theorem gate_sound {nu s : Array Float} {g : Float} (hsz : nu.size < 2 ^ 64 ∧ s.size < 2 ^ 64)
    (h : (gate nu s g).status = 0) :
    1 ≤ nu.size ∧ nu.size ≤ 64 ∧ s.size = nu.size * nu.size ∧ Finite g.toBits ∧
      0 ≤ value g.toBits ∧ (covariance s nu.size).PosDef ∧
      Finite (gate nu s g).lo.toBits ∧ Finite (gate nu s g).hi.toBits ∧
      value (gate nu s g).lo.toBits ≤ Model.mahalanobis (covariance s nu.size) (innovation nu) ∧
      Model.mahalanobis (covariance s nu.size) (innovation nu) ≤ value (gate nu s g).hi.toBits ∧
      ((gate nu s g).verdict = 1 →
        Model.mahalanobis (covariance s nu.size) (innovation nu) ≤ value g.toBits) ∧
      ((gate nu s g).verdict = 2 →
        value g.toBits < Model.mahalanobis (covariance s nu.size) (innovation nu)) := by
  unfold gate at h ⊢
  simp only at h ⊢
  have hdn : nu.size.toUInt64.toNat = nu.size := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hsz.1]
  by_cases g1 : 1 ≤ nu.size.toUInt64 ∧ nu.size.toUInt64 ≤ 64 ∧
      s.size.toUInt64 = nu.size.toUInt64 * nu.size.toUInt64
  · rw [ite_eq_left g1] at h ⊢
    obtain ⟨g1a, g1b, g1c⟩ := g1
    set d := nu.size.toUInt64 with hd_def
    have hd1 : 1 ≤ nu.size := by have := UInt64.le_iff_toNat_le.mp g1a; simpa [hdn] using this
    have hd2 : nu.size ≤ 64 := by have := UInt64.le_iff_toNat_le.mp g1b; simpa [hdn] using this
    have hd64 : d.toNat ≤ 64 := by rw [hdn]; exact hd2
    have hss : s.size = nu.size * nu.size := by
      have := congrArg UInt64.toNat g1c
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hsz.2, UInt64.toNat_mul, hdn,
        Nat.mod_eq_of_lt (by nlinarith)] at this
      exact this
    by_cases g2 : (finite g && 0.0 ≤ g && allFinite nu d && allFinite s (d * d) &&
        symmetric s d) = true
    · rw [ite_eq_left g2] at h ⊢
      simp only [Bool.and_eq_true] at g2
      obtain ⟨⟨⟨⟨gf, gnn⟩, -⟩, gs⟩, gsym⟩ := g2
      have fg := (finite_iff g).mp gf
      have hg0 : 0 ≤ value g.toBits := by
        have := (le_iff_value Conjunction.lit_zero.1 fg).mp (of_decide_eq_true gnn)
        rwa [lit_zero_value] at this
      have hdd : (d * d).toNat = d.toNat * d.toNat := by
        rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by nlinarith)]
      have hfin := allFinite_sound gs
      rw [hdd] at hfin
      have hsym := symmetric_sound hd64 hfin gsym
      rw [hdn] at hsym
      by_cases g3 : ((eliminate s nu d).status == 0 && (eliminate s nu d).acc.status == 0) = true
      · rw [ite_eq_left g3] at h ⊢
        simp only [Bool.and_eq_true, beq_iff_eq] at g3
        obtain ⟨-, -, -, -, hacc, hpiv⟩ := eliminate_inv (s := s) (nu := nu) hd64 g3.1
        rw [hdn] at hacc hpiv
        have hpd := Model.posDef_of_pivots hsym hpiv
        have hM0 : 0 ≤ Model.quad (matOf s nu.size) (vecOf nu) nu.size := quad_nonneg hpiv
        have hc := hacc g3.2
        have hmeq : Model.mahalanobis (covariance s nu.size) (innovation nu) =
            Model.quad (matOf s nu.size) (vecOf nu) nu.size :=
          Model.mahalanobis_eq hsym hpiv (vecOf nu)
        rw [hmeq]
        by_cases g4 : ((clamp (eliminate s nu d).acc 0.0 (eliminate s nu d).acc.hi).status == 0) = true
        · rw [ite_eq_left g4] at h ⊢
          have hq := (clamp_sound (beq_iff_eq.mp g4)).2 _ hc (by rw [lit_zero_value]; exact hM0)
            hc.2.2.2.2
          simp only
          refine ⟨hd1, hd2, hss, fg, hg0, hpd, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2, ?_, ?_⟩
          · intro hv
            by_cases g5 : (clamp (eliminate s nu d).acc 0.0 (eliminate s nu d).acc.hi).hi ≤ g
            · exact hq.2.2.2.2.trans ((le_iff_value hq.2.2.1 fg).mp g5)
            · rw [ite_eq_right g5] at hv
              by_cases g6 : g < (clamp (eliminate s nu d).acc 0.0 (eliminate s nu d).acc.hi).lo
              · rw [ite_eq_left g6] at hv; exact absurd hv (by decide)
              · rw [ite_eq_right g6] at hv; exact absurd hv (by decide)
          · intro hv
            by_cases g5 : (clamp (eliminate s nu d).acc 0.0 (eliminate s nu d).acc.hi).hi ≤ g
            · rw [ite_eq_left g5] at hv; exact absurd hv (by decide)
            · rw [ite_eq_right g5] at hv
              by_cases g6 : g < (clamp (eliminate s nu d).acc 0.0 (eliminate s nu d).acc.hi).lo
              · exact lt_of_lt_of_le ((lt_iff_value fg hq.2.1).mp g6) hq.2.2.2.1
              · rw [ite_eq_right g6] at hv; exact absurd hv (by decide)
        · rw [ite_eq_right g4] at h
          exact absurd h (by decide)
      · rw [ite_eq_right g3] at h
        exact absurd h (by decide)
    · rw [ite_eq_right g2] at h
      exact absurd h (by decide)
  · rw [ite_eq_right g1] at h
    exact absurd h (by decide)

#print axioms gate_sound

end Demos.Gate
