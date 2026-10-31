import Library.HashTables.LinearProbing.Program
import Library.HashTables.LinearProbing.Spec
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas

/-! The proof that the hash table computes the outputs of the list of keys.  Slots are numbers below
`m`.  `adv m r d` is the slot `d` steps after slot `r`, and `dist m a b` is the number of steps from
slot `a` to slot `b`, both without `%`, so that `omega` decides their arithmetic.  `Good` states the
invariant of the table: the occupied slots hold a permutation of the keys, at least one slot is
empty, and every slot that the search for an occupied slot's key passes, from the key's home slot
to the slot before it, is occupied.  `probe_spec` shows that a search ends at the slot of its key
or at an empty slot, `CloseInv` states the invariant of Algorithm R, whose one exception is the
empty slot `j` on the path of a key not yet inspected, and `close_spec` shows that the deletion
restores `Good`. -/

namespace Library.HashTables.LinearProbing

open LeanExe.Dialect

/-! ### Slots -/

/-- The slot `d` steps after slot `r`, for `r < m` and `d ≤ m`. -/
def adv (m r d : Nat) : Nat := if r + d < m then r + d else r + d - m

/-- The number of steps from slot `a` to slot `b`. -/
def dist (m a b : Nat) : Nat := if a ≤ b then b - a else b + m - a

theorem adv_lt {m r d : Nat} (hr : r < m) (hd : d < m) : adv m r d < m := by
  unfold adv; split_ifs <;> omega

theorem dist_lt {m a b : Nat} (ha : a < m) (hb : b < m) : dist m a b < m := by
  unfold dist; split_ifs <;> omega

theorem adv_dist {m r s : Nat} (hr : r < m) (hs : s < m) : adv m r (dist m r s) = s := by
  unfold adv dist; split_ifs <;> omega

theorem dist_adv {m r d : Nat} (hr : r < m) (hd : d < m) : dist m r (adv m r d) = d := by
  unfold adv dist; split_ifs <;> omega

theorem adv_zero {m r : Nat} (hr : r < m) : adv m r 0 = r := by
  unfold adv; split_ifs <;> omega

theorem adv_inj {m r d e : Nat} (hd : d < m) (he : e < m)
    (h : adv m r d = adv m r e) : d = e := by
  unfold adv at h; split_ifs at h <;> omega

theorem adv_adv {m r d e : Nat} (hr : r < m) (hde : d + e ≤ m) :
    adv m (adv m r d) e = adv m r (d + e) := by
  unfold adv; split_ifs <;> omega

theorem dist_eq_zero {m a b : Nat} (ha : a < m) : dist m a b = 0 ↔ a = b := by
  unfold dist; split_ifs <;> omega

/-- The distance between two slots after `j`. -/
theorem dist_advs {m j b a : Nat} (hba : b ≤ a) (ha : a < m) :
    dist m (adv m j b) (adv m j a) = a - b := by
  unfold adv dist; split_ifs <;> omega

/-- A slot `p` no farther before `s` than `r` lies on the path from `r` to `s`. -/
theorem dist_add {m r p s : Nat} (hr : r < m) (hp : p < m)
    (h : dist m p s ≤ dist m r s) : dist m r p + dist m p s = dist m r s := by
  unfold dist at *; split_ifs at * <;> omega

theorem mod_two {x m : Nat} (h : x < 2 * m) : x % m = if x < m then x else x - m := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem dist_eq_mod {m a b : Nat} (ha : a < m) (hb : b < m) : (b + m - a) % m = dist m a b := by
  rw [mod_two (by omega)]; unfold dist; split_ifs <;> omega

/-! ### The table -/

/-- Slot `s` of the table `t` is occupied. -/
def occ (t : Array UInt64) (s : Nat) : Prop := 0 < t[2 * s]!

/-- The key of slot `s`. -/
def keyAt (t : Array UInt64) (s : Nat) : UInt64 := t[2 * s + 1]!

/-- The home slot of key `k`. -/
def home (m : Nat) (k : UInt64) : Nat := k.toNat % m

/-- The keys of the occupied slots, in the order of the slots. -/
def tableKeys (m : Nat) (t : Array UInt64) : List UInt64 :=
  (List.range m).filterMap fun s => if (0 : UInt64) < t[2 * s]! then some t[2 * s + 1]! else none

theorem filterMap_fill {α : Type} (m i : Nat) (k : α) (f g : Nat → Option α) (hi : i < m)
    (hf : f i = none) (hg : g i = some k) (hfg : ∀ s, s < m → s ≠ i → f s = g s) :
    ((List.range m).filterMap g).Perm (k :: (List.range m).filterMap f) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.filterMap_append, List.filterMap_append]
    by_cases him : i < m
    · have hl : f m = g m := hfg m (by omega) (by omega)
      simp only [List.filterMap_cons, List.filterMap_nil, hl]
      exact (ih him fun s hs hsi => hfg s (by omega) hsi).append_right _
    · have hm : i = m := by omega
      subst hm
      have heq : (List.range i).filterMap f = (List.range i).filterMap g :=
        List.filterMap_congr fun s hs => hfg s (by simp at hs; omega) (by simp at hs; omega)
      simp only [List.filterMap_cons, List.filterMap_nil, hf, hg, heq, List.append_nil]
      exact List.perm_append_singleton _ _

theorem filterMap_length_ge {α : Type} (m h : Nat) (g : Nat → Option α)
    (hg : ∀ s, s < m → s ≠ h → (g s).isSome) : m ≤ ((List.range m).filterMap g).length + 1 := by
  suffices hs : ∀ m, (∀ s, s < m → s ≠ h → (g s).isSome) →
      m ≤ ((List.range m).filterMap g).length + (if h < m then 1 else 0) by
    have := hs m hg; split at this <;> omega
  intro m
  induction m with
  | zero => intro _; exact Nat.zero_le _
  | succ m ih =>
    intro hg
    rw [List.range_succ, List.filterMap_append, List.length_append]
    have := ih fun s hs hsh => hg s (by omega) hsh
    by_cases hm : m = h
    · have h1 : ¬ h < m := by omega
      have h2 : h < m + 1 := by omega
      rw [ite_eq_right h1] at this
      rw [ite_eq_left h2]
      omega
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hg m (by omega) hm)
      have hl : (List.filterMap g [m]).length = 1 := by simp [hv]
      rw [hl]
      split_ifs at this ⊢ <;> omega

theorem tableKeys_congr {m : Nat} {t u : Array UInt64}
    (h : ∀ s, s < m → t[2 * s]! = u[2 * s]! ∧ t[2 * s + 1]! = u[2 * s + 1]!) :
    tableKeys m t = tableKeys m u :=
  List.filterMap_congr fun s hs => by
    obtain ⟨h1, h2⟩ := h s (by simpa using hs)
    rw [h1, h2]

/-- Filling the empty slot `i` with the key `k` adds `k` to the keys. -/
theorem tableKeys_fill {m i : Nat} {t u : Array UInt64} {k : UInt64} (hi : i < m)
    (ht : ¬ occ t i) (hu : occ u i) (hk : keyAt u i = k)
    (h : ∀ s, s < m → s ≠ i → t[2 * s]! = u[2 * s]! ∧ t[2 * s + 1]! = u[2 * s + 1]!) :
    (tableKeys m u).Perm (k :: tableKeys m t) := by
  unfold tableKeys
  apply filterMap_fill m i k _ _ hi
  · simp only [occ] at ht; simp [ht]
  · simp only [occ, keyAt] at hu hk; simp [hu, hk]
  · intro s hsm hs
    obtain ⟨h1, h2⟩ := h s hsm hs
    simp only [h1, h2]

theorem tableKeys_empty {m : Nat} {t : Array UInt64} (h : ∀ s, s < m → ¬ occ t s) :
    tableKeys m t = [] := by
  unfold tableKeys
  rw [List.filterMap_eq_nil_iff]
  intro s hs
  have := h s (by simpa using hs)
  simp only [occ] at this
  simp [this]

theorem mem_tableKeys {m : Nat} {t : Array UInt64} {k : UInt64} :
    k ∈ tableKeys m t ↔ ∃ s, s < m ∧ occ t s ∧ keyAt t s = k := by
  simp only [tableKeys, List.mem_filterMap, List.mem_range, occ, keyAt]
  constructor
  · rintro ⟨s, hs, h⟩
    split at h
    · exact ⟨s, hs, ‹_›, Option.some.inj h⟩
    · simp at h
  · rintro ⟨s, hs, ho, hk⟩
    exact ⟨s, hs, by rw [ite_eq_left ho, hk]⟩

theorem filterMap_length_all {α : Type} (m : Nat) (g : Nat → Option α)
    (hg : ∀ s, s < m → (g s).isSome) : m ≤ ((List.range m).filterMap g).length := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.filterMap_append, List.length_append]
    have := ih fun s hs => hg s (by omega)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hg m (by omega))
    simp [hv]
    omega

/-- All slots occupied gives at least `m` keys. -/
theorem tableKeys_length_all {m : Nat} {t : Array UInt64} (hocc : ∀ s, s < m → occ t s) :
    m ≤ (tableKeys m t).length :=
  filterMap_length_all m _ fun s hs => by
    have := hocc s hs
    simp only [occ] at this
    simp [this]

/-- All but at most one slot occupied gives at least `m - 1` keys. -/
theorem tableKeys_length_ge {m h : Nat} {t : Array UInt64}
    (hocc : ∀ s, s < m → s ≠ h → occ t s) : m ≤ (tableKeys m t).length + 1 :=
  filterMap_length_ge m h _ fun s hs hsh => by
    have := hocc s hs hsh
    simp only [occ] at this
    simp [this]

/-! ### The invariant -/

/-- The table `t` of `m` slots holds the keys `keys`: the occupied slots hold a permutation of the
keys, which are distinct, at least one slot is empty, and the slots from the home slot of an
occupied slot's key up to the slot before it are occupied. -/
structure Good (m : Nat) (t : Array UInt64) (keys : List UInt64) : Prop where
  size : t.size = 2 * m
  perm : (tableKeys m t).Perm keys
  nodup : keys.Nodup
  room : keys = [] ∨ keys.length + 1 ≤ m
  reach : ∀ s, s < m → occ t s → ∀ d, d < dist m (home m (keyAt t s)) s →
    occ t (adv m (home m (keyAt t s)) d)

theorem Good.free {m : Nat} {t : Array UInt64} {keys : List UInt64} (hg : Good m t keys)
    (hm : 0 < m) : ∃ e, e < m ∧ ¬ occ t e := by
  by_contra hall
  push Not at hall
  have h1 := tableKeys_length_all (t := t) fun s hs => hall s hs
  have hl := hg.perm.length_eq
  rcases hg.room with h | h
  · rw [h, List.length_nil] at hl; omega
  · omega

/-! ### Words -/

theorem twice {s : UInt64} (h : s.toNat < 2 ^ 63) :
    (s + s).toNat = 2 * s.toNat ∧ (s + s + 1).toNat = 2 * s.toNat + 1 := by
  constructor <;> simp only [UInt64.toNat_add, UInt64.reduceToNat] <;> omega

theorem sub_one {f : UInt64} (h : 0 < f.toNat) : (f - 1).toNat = f.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.reduceToNat]; omega))]
  simp only [UInt64.reduceToNat]

theorem next_toNat {M s : UInt64} (hm : M.toNat < 2 ^ 63) (hs : s.toNat < M.toNat) :
    (next M s).toNat = adv M.toNat s.toNat 1 := by
  have h1 : (s + 1).toNat = s.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  unfold next adv
  by_cases h : s + 1 < M
  · have h' := UInt64.lt_iff_toNat_lt.mp h
    rw [h1] at h'
    rw [ite_eq_left h, ite_eq_left h', h1]
  · have h' : ¬ s.toNat + 1 < M.toNat := fun h' =>
      h (UInt64.lt_iff_toNat_lt.mpr (by rw [h1]; exact h'))
    rw [ite_eq_right h, ite_eq_right h']
    simp only [UInt64.reduceToNat]
    omega

theorem gap_toNat {M a b : UInt64} (hm : M.toNat < 2 ^ 63) (ha : a.toNat < M.toNat)
    (hb : b.toNat < M.toNat) : (gap M a b).toNat = dist M.toNat a.toNat b.toNat := by
  unfold gap
  have h1 : (b + M).toNat = b.toNat + M.toNat := by
    simp only [UInt64.toNat_add]; omega
  have h2 : a ≤ b + M := UInt64.le_iff_toNat_le.mpr (by rw [h1]; omega)
  rw [UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ h2, h1]
  exact dist_eq_mod ha hb

theorem home_lt {m : Nat} (k : UInt64) (hm : 0 < m) : home m k < m := Nat.mod_lt _ hm

/-! ### Searching -/

/-- From the slot `d` steps after `r`, the search for `k` passes slots that hold other keys and
ends, within the slots of the table, at an empty slot or at the slot of `k`. -/
theorem probe_spec (M k : UInt64) (t : Array UInt64) (hm : M.toNat < 2 ^ 63) (r : Nat)
    (hr : r < M.toNat) (hfree : ∃ e, e < M.toNat ∧ ¬ occ t e) (d : Nat) (hd : d ≤ M.toNat)
    (s fuel : UInt64) (hs : s.toNat = adv M.toNat r d) (hf : fuel.toNat = M.toNat - d)
    (hpass : ∀ d', d' < d → occ t (adv M.toNat r d') ∧ keyAt t (adv M.toNat r d') ≠ k) :
    ∃ e, d ≤ e ∧ e < M.toNat ∧ (probe M k s fuel t).toNat = adv M.toNat r e ∧
      (∀ d', d' < e → occ t (adv M.toNat r d') ∧ keyAt t (adv M.toNat r d') ≠ k) ∧
      (¬ occ t (adv M.toNat r e) ∨ keyAt t (adv M.toNat r e) = k) := by
  have hdm : d < M.toNat := by
    rcases Nat.lt_or_ge d M.toNat with h | h
    · exact h
    · obtain ⟨e, he, hne⟩ := hfree
      have := (hpass (dist M.toNat r e) (by have := dist_lt hr he; omega)).1
      rw [adv_dist hr he] at this
      exact absurd this hne
  have hsm : s.toNat < M.toNat := by rw [hs]; exact adv_lt hr hdm
  obtain ⟨h2, h21⟩ := twice (show s.toNat < 2 ^ 63 by omega)
  have hf0 : 0 < fuel := UInt64.lt_iff_toNat_lt.mpr (by simp only [UInt64.reduceToNat]; omega)
  rw [probe]
  by_cases ho : 0 < t[(s + s).toNat]!
  · rw [ite_eq_left (show 0 < fuel ∧ 0 < t[(s + s).toNat]! from ⟨hf0, ho⟩)]
    have hocc : occ t (adv M.toNat r d) := by rw [← hs]; unfold occ; rw [← h2]; exact ho
    by_cases hk : t[(s + s + 1).toNat]! = k
    · rw [ite_eq_left hk]
      refine ⟨d, le_refl _, hdm, hs, hpass, Or.inr ?_⟩
      rw [← hs]; unfold keyAt; rw [← h21]; exact hk
    · rw [ite_eq_right hk]
      have hkey : keyAt t (adv M.toNat r d) ≠ k := by rw [← hs]; unfold keyAt; rw [← h21]; exact hk
      obtain ⟨e, hde, hem, heq, hp, hend⟩ := probe_spec M k t hm r hr hfree (d + 1) (by omega)
        (next M s) (fuel - 1) (by rw [next_toNat hm hsm, hs, adv_adv hr (by omega)])
        (by rw [sub_one (by omega), hf]; omega)
        (fun d' hd' => by
          rcases Nat.lt_or_ge d' d with h | h
          · exact hpass d' h
          · rw [show d' = d by omega]; exact ⟨hocc, hkey⟩)
      exact ⟨e, by omega, hem, heq, hp, hend⟩
  · rw [ite_eq_right (show ¬ (0 < fuel ∧ 0 < t[(s + s).toNat]!) from fun h => ho h.2)]
    refine ⟨d, le_refl _, hdm, hs, hpass, Or.inl ?_⟩
    rw [← hs]; unfold occ; rw [← h2]; exact ho
termination_by M.toNat - d
decreasing_by omega

/-- The search for `k` ends at slot `adv m (home m k) e`, after occupied slots.  That slot is
occupied exactly when `k` is a key, and then it holds `k`. -/
theorem slot_spec (M k : UInt64) (t : Array UInt64) (keys : List UInt64)
    (hm : M.toNat < 2 ^ 63) (hm0 : 0 < M.toNat) (hg : Good M.toNat t keys) :
    ∃ e, e < M.toNat ∧ (slot M k t).toNat = adv M.toNat (home M.toNat k) e ∧
      (∀ d', d' < e → occ t (adv M.toNat (home M.toNat k) d')) ∧
      (occ t (adv M.toNat (home M.toNat k) e) ↔ k ∈ keys) ∧
      (occ t (adv M.toNat (home M.toNat k) e) → keyAt t (adv M.toNat (home M.toNat k) e) = k) := by
  have hr := home_lt (m := M.toNat) k hm0
  obtain ⟨e, -, hem, heq, hp, hend⟩ := probe_spec M k t hm (home M.toNat k) hr (hg.free hm0) 0
    (Nat.zero_le _) (k % M) M (by rw [adv_zero hr, UInt64.toNat_mod]; rfl) (by omega)
    (fun _ h => absurd h (Nat.not_lt_zero _))
  have hkey : occ t (adv M.toNat (home M.toNat k) e) →
      keyAt t (adv M.toNat (home M.toNat k) e) = k := fun ho => hend.resolve_left (not_not.mpr ho)
  refine ⟨e, hem, heq, fun d' hd' => (hp d' hd').1, ⟨fun ho => ?_, fun hk => ?_⟩, hkey⟩
  · exact hg.perm.mem_iff.mp (mem_tableKeys.mpr ⟨_, adv_lt hr hem, ho, hkey ho⟩)
  · obtain ⟨j, hj, hoj, hkj⟩ := mem_tableKeys.mp (hg.perm.mem_iff.mpr hk)
    have hreach := hg.reach j hj hoj
    rw [hkj] at hreach
    by_contra hno
    rcases Nat.lt_trichotomy e (dist M.toNat (home M.toNat k) j) with h | h | h
    · exact hno (hreach e h)
    · rw [h, adv_dist hr hj] at hno; exact hno hoj
    · have := (hp _ h).2
      rw [adv_dist hr hj] at this
      exact this hkj

/-! ### Insertion -/

/-- Writing the key `k` into the empty slot where its search ends keeps `Good`. -/
theorem insert_good {m : Nat} {t : Array UInt64} {keys : List UInt64} {k : UInt64} {e : Nat}
    (hg : Good m t keys) (he : e < m) (hpath : ∀ d', d' < e → occ t (adv m (home m k) d'))
    (hfree : ¬ occ t (adv m (home m k) e)) (hk : k ∉ keys) (hroom : keys.length + 2 ≤ m) :
    Good m ((t.set! (2 * adv m (home m k) e) 1).set! (2 * adv m (home m k) e + 1) k)
      (k :: keys) := by
  have hm0 : 0 < m := by omega
  have hr := home_lt (m := m) k hm0
  have hi := adv_lt hr he
  generalize hI : adv m (home m k) e = i at hfree hi ⊢
  have hsz := hg.size
  have hu : ∀ x, ((t.set! (2 * i) 1).set! (2 * i + 1) k)[x]! =
      if x = 2 * i + 1 then k else if x = 2 * i then 1 else t[x]! := by
    intro x
    rw [get_set _ _ _ x (by simp; omega), get_set _ _ _ x (by omega)]
  have hocc : occ ((t.set! (2 * i) 1).set! (2 * i + 1) k) i := by
    have h1 : ¬ (2 * i = 2 * i + 1) := by omega
    unfold occ; rw [hu, ite_eq_right h1, ite_eq_left rfl]; decide
  have hkey : keyAt ((t.set! (2 * i) 1).set! (2 * i + 1) k) i = k := by
    unfold keyAt; rw [hu, ite_eq_left rfl]
  have hsame : ∀ p, p ≠ i → ((t.set! (2 * i) 1).set! (2 * i + 1) k)[2 * p]! = t[2 * p]! ∧
      ((t.set! (2 * i) 1).set! (2 * i + 1) k)[2 * p + 1]! = t[2 * p + 1]! := by
    intro p hp
    have h1 : ¬ (2 * p = 2 * i + 1) := by omega
    have h2 : ¬ (2 * p = 2 * i) := by omega
    have h3 : ¬ (2 * p + 1 = 2 * i + 1) := by omega
    have h4 : ¬ (2 * p + 1 = 2 * i) := by omega
    rw [hu, hu, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    exact ⟨rfl, rfl⟩
  have hmono : ∀ p, occ t p → occ ((t.set! (2 * i) 1).set! (2 * i + 1) k) p := by
    intro p hp
    by_cases hpi : p = i
    · rw [hpi]; exact hocc
    · unfold occ; rw [(hsame p hpi).1]; exact hp
  refine ⟨by simp; omega, ?_, List.nodup_cons.mpr ⟨hk, hg.nodup⟩, Or.inr (by simp; omega), ?_⟩
  · exact (tableKeys_fill hi hfree hocc hkey fun s _ hs => ⟨(hsame s hs).1.symm, (hsame s hs).2.symm⟩).trans
      (hg.perm.cons k)
  · intro s hs ho d hd
    by_cases hsi : s = i
    · rw [hsi, hkey] at hd ⊢
      rw [← hI, dist_adv hr he] at hd
      exact hmono _ (hpath d hd)
    · have hot : occ t s := by unfold occ at ho ⊢; rw [(hsame s hsi).1] at ho; exact ho
      have hks : keyAt ((t.set! (2 * i) 1).set! (2 * i + 1) k) s = keyAt t s := (hsame s hsi).2
      rw [hks] at hd ⊢
      exact hmono _ (hg.reach s hs hot d hd)

/-! ### Deletion -/

/-- The invariant of Algorithm R, after it started at slot `j0`: the empty slot `j` is `b` slots
after `j0`, and the next slot to inspect is `a` slots after `j0`.  The other slots up to `a` are
occupied, and every slot on the path of an occupied slot's key is occupied, except the empty slot
`j` on the path of a key at least `a - b` slots after `j`, which Algorithm R has not inspected. -/
structure CloseInv (m : Nat) (t : Array UInt64) (j0 b a : Nat) : Prop where
  size : t.size = 2 * m
  ba : b < a
  am : a < m
  hole : ¬ occ t (adv m j0 b)
  window : ∀ a', a' < a → a' ≠ b → occ t (adv m j0 a')
  reach : ∀ s, s < m → occ t s → ∀ d, d < dist m (home m (keyAt t s)) s →
    occ t (adv m (home m (keyAt t s)) d) ∨
      (adv m (home m (keyAt t s)) d = adv m j0 b ∧ a - b ≤ dist m (adv m j0 b) s)

theorem dist_from_adv {m r s d : Nat} (hr : r < m) (hs : s < m) (hd : d ≤ dist m r s) :
    dist m (adv m r d) s = dist m r s - d := by
  have := dist_lt hr hs
  unfold adv dist at *; split_ifs at * <;> omega

theorem slot_after {m j0 b a s : Nat} (hj0 : j0 < m) (hba : b ≤ a) (ham : a < m) (hs : s < m)
    (h : dist m (adv m j0 b) s = a - b) : s = adv m j0 a := by
  have h1 := adv_dist (adv_lt (d := b) hj0 (by omega)) hs
  rw [h, adv_adv (d := b) (e := a - b) hj0 (by omega), Nat.add_sub_cancel' hba] at h1
  exact h1.symm

/-- Algorithm R, from a state that meets `CloseInv`, ends with a table that meets `Good`. -/
theorem close_spec (M : UInt64) (hm : M.toNat < 2 ^ 63) (j0 : Nat) (hj0 : j0 < M.toNat)
    (keys : List UInt64) (hnodup : keys.Nodup) (hlen : keys.length + 2 ≤ M.toNat)
    (b a : Nat) (t : Array UInt64) (hinv : CloseInv M.toNat t j0 b a)
    (hperm : (tableKeys M.toNat t).Perm keys)
    (j i fuel : UInt64) (hj : j.toNat = adv M.toNat j0 b) (hi : i.toNat = adv M.toNat j0 a)
    (hf : fuel.toNat = M.toNat + 1 - a) :
    Good M.toNat (close M j i fuel t) keys := by
  have hm0 : 0 < M.toNat := by omega
  have hba := hinv.ba
  have ham := hinv.am
  have hjm : j.toNat < M.toNat := by rw [hj]; exact adv_lt hj0 (by omega)
  have him : i.toNat < M.toNat := by rw [hi]; exact adv_lt hj0 ham
  obtain ⟨hi2, hi21⟩ := twice (show i.toNat < 2 ^ 63 by omega)
  obtain ⟨hj2, hj21⟩ := twice (show j.toNat < 2 ^ 63 by omega)
  have hf0 : 0 < fuel := UInt64.lt_iff_toNat_lt.mpr (by simp only [UInt64.reduceToNat]; omega)
  have hdji : dist M.toNat j.toNat i.toNat = a - b := by
    rw [hj, hi]; exact dist_advs (Nat.le_of_lt hba) ham
  have hji : j.toNat ≠ i.toNat := fun h => by
    rw [h, (dist_eq_zero him).mpr rfl] at hdji; omega
  have hsz := hinv.size
  rw [close]
  by_cases ho : 0 < t[(i + i).toNat]!
  · rw [ite_eq_left (show 0 < fuel ∧ 0 < t[(i + i).toNat]! from ⟨hf0, ho⟩)]
    have hoi : occ t i.toNat := by unfold occ; rw [← hi2]; exact ho
    have ha1 : a + 1 < M.toNat := by
      by_contra hc
      have hall : ∀ s, s < M.toNat → s ≠ j.toNat → occ t s := by
        intro s hs hsj
        have hd := dist_lt hj0 hs
        have hs' : adv M.toNat j0 (dist M.toNat j0 s) = s := adv_dist hj0 hs
        by_cases hda : dist M.toNat j0 s = a
        · rw [← hs', hda, ← hi]; exact hoi
        · rw [← hs']
          exact hinv.window _ (by omega) fun hdb => hsj (by rw [hj, ← hdb, hs'])
      have := tableKeys_length_ge hall
      have := hperm.length_eq
      omega
    have hnext : (next M i).toNat = adv M.toNat j0 (a + 1) := by
      rw [next_toNat hm him, hi, adv_adv hj0 (by omega)]
    have hf1 : (fuel - 1).toNat = M.toNat + 1 - (a + 1) := by rw [sub_one (by omega), hf]; omega
    have hK := home_lt (m := M.toNat) (keyAt t i.toNat) hm0
    have hcond : gap M (t[(i + i + 1).toNat]! % M) i < gap M j i ↔
        dist M.toNat (home M.toNat (keyAt t i.toNat)) i.toNat < a - b := by
      have hmod : (t[(i + i + 1).toNat]! % M).toNat = home M.toNat (keyAt t i.toNat) := by
        rw [UInt64.toNat_mod, hi21]; rfl
      rw [UInt64.lt_iff_toNat_lt, gap_toNat hm (by rw [hmod]; exact hK) him,
        gap_toNat hm hjm him, hmod, hdji]
    by_cases hc : gap M (t[(i + i + 1).toNat]! % M) i < gap M j i
    · rw [ite_eq_left hc]
      have hc' := hcond.mp hc
      refine close_spec M hm j0 hj0 keys hnodup hlen b (a + 1) t ?_ hperm j (next M i) (fuel - 1)
        hj hnext hf1
      refine ⟨hsz, by omega, ha1, hinv.hole, fun a' ha' hab => ?_, ?_⟩
      · rcases Nat.lt_or_ge a' a with h | h
        · exact hinv.window a' h hab
        · rw [show a' = a by omega, ← hi]; exact hoi
      · intro s hs hos d hd
        rcases hinv.reach s hs hos d hd with h | ⟨hp, hle⟩
        · exact Or.inl h
        · refine Or.inr ⟨hp, ?_⟩
          by_contra hlt
          have hds : dist M.toNat (adv M.toNat j0 b) s = a - b := by omega
          have hsi : s = i.toNat := by rw [hi]; exact slot_after hj0 (by omega) ham hs hds
          rw [hsi] at hd hp
          have hr := home_lt (m := M.toNat) (keyAt t i.toNat) hm0
          have h1 := dist_from_adv hr him (Nat.le_of_lt hd)
          rw [hp, ← hj, hdji] at h1
          omega
    · rw [ite_eq_right hc]
      have hc' : a - b ≤ dist M.toNat (home M.toNat (keyAt t i.toNat)) i.toNat := by
        have := mt hcond.mpr hc; omega
      have hu : ∀ x, (move j i t)[x]! = if x = 2 * i.toNat then 0 else
          if x = 2 * j.toNat then 1 else if x = 2 * j.toNat + 1 then t[2 * i.toNat + 1]! else t[x]! := by
        intro x
        unfold move
        rw [hi2, hj2, hj21, hi21, get_set _ _ _ x (by simp; omega), get_set _ _ _ x (by simp; omega),
          get_set _ _ _ x (by omega)]
      have hsize : (move j i t).size = 2 * M.toNat := by unfold move; simp; omega
      have hnoti : ¬ occ (move j i t) i.toNat := by
        unfold occ; rw [hu, ite_eq_left rfl]; decide
      have hoccj : occ (move j i t) j.toNat := by
        have h1 : ¬ (2 * j.toNat = 2 * i.toNat) := by omega
        unfold occ; rw [hu, ite_eq_right h1, ite_eq_left rfl]; decide
      have hkeyj : keyAt (move j i t) j.toNat = keyAt t i.toNat := by
        have h1 : ¬ (2 * j.toNat + 1 = 2 * i.toNat) := by omega
        have h2 : ¬ (2 * j.toNat + 1 = 2 * j.toNat) := by omega
        unfold keyAt; rw [hu, ite_eq_right h1, ite_eq_right h2, ite_eq_left rfl]
      have hsame : ∀ p, p ≠ i.toNat → p ≠ j.toNat → (move j i t)[2 * p]! = t[2 * p]! ∧
          (move j i t)[2 * p + 1]! = t[2 * p + 1]! := by
        intro p hpi hpj
        have h1 : ¬ (2 * p = 2 * i.toNat) := by omega
        have h2 : ¬ (2 * p = 2 * j.toNat) := by omega
        have h3 : ¬ (2 * p = 2 * j.toNat + 1) := by omega
        have h4 : ¬ (2 * p + 1 = 2 * i.toNat) := by omega
        have h5 : ¬ (2 * p + 1 = 2 * j.toNat) := by omega
        have h6 : ¬ (2 * p + 1 = 2 * j.toNat + 1) := by omega
        rw [hu, hu, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
          ite_eq_right h5, ite_eq_right h6]
        exact ⟨rfl, rfl⟩
      have hoccu : ∀ p, p < M.toNat → p ≠ i.toNat → occ t p → occ (move j i t) p := by
        intro p _ hpi hp
        by_cases hpj : p = j.toNat
        · rw [hpj]; exact hoccj
        · unfold occ; rw [(hsame p hpi hpj).1]; exact hp
      -- the words of the table
      have hperm' : (tableKeys M.toNat (move j i t)).Perm keys := by
        have hw : ∀ x, (t.set! (2 * i.toNat) 0)[x]! = if x = 2 * i.toNat then 0 else t[x]! :=
          fun x => get_set _ _ _ x (by omega)
        have hwi : ¬ occ (t.set! (2 * i.toNat) 0) i.toNat := by
          unfold occ; rw [hw, ite_eq_left rfl]; decide
        have hwj : ¬ occ (t.set! (2 * i.toNat) 0) j.toNat := by
          have h1 : ¬ (2 * j.toNat = 2 * i.toNat) := by omega
          have := hinv.hole
          rw [← hj] at this
          unfold occ at this ⊢; rw [hw, ite_eq_right h1]; exact this
        have p1 := tableKeys_fill (u := t) him hwi hoi rfl fun s _ hs => by
          have h1 : ¬ (2 * s = 2 * i.toNat) := by omega
          have h2 : ¬ (2 * s + 1 = 2 * i.toNat) := by omega
          rw [hw, hw, ite_eq_right h1, ite_eq_right h2]; exact ⟨rfl, rfl⟩
        have p2 := tableKeys_fill (u := move j i t) hjm hwj hoccj hkeyj fun s _ hs => by
          by_cases hsi : s = i.toNat
          · have h1 : ¬ (2 * i.toNat + 1 = 2 * i.toNat) := by omega
            have h3 : ¬ (2 * i.toNat + 1 = 2 * j.toNat) := by omega
            have h4 : ¬ (2 * i.toNat + 1 = 2 * j.toNat + 1) := by omega
            rw [hsi, hw, hw, hu, hu, ite_eq_left rfl, ite_eq_right h1, ite_eq_left rfl,
              ite_eq_right h1, ite_eq_right h3, ite_eq_right h4]
            exact ⟨rfl, rfl⟩
          · have h1 : ¬ (2 * s = 2 * i.toNat) := by omega
            have h2 : ¬ (2 * s + 1 = 2 * i.toNat) := by omega
            rw [hw, hw, ite_eq_right h1, ite_eq_right h2, (hsame s hsi hs).1, (hsame s hsi hs).2]
            exact ⟨rfl, rfl⟩
        exact p2.trans (p1.symm.trans hperm)
      refine close_spec M hm j0 hj0 keys hnodup hlen a (a + 1) (move j i t) ?_ hperm' i (next M i)
        (fuel - 1) hi hnext hf1
      refine ⟨hsize, by omega, ha1, by rw [← hi]; exact hnoti, fun a' ha' hab => ?_, ?_⟩
      · have ha'a : a' < a := by omega
        have hne : adv M.toNat j0 a' ≠ i.toNat := fun h => by
          rw [hi] at h; exact hab (adv_inj (by omega) ham h)
        by_cases hab' : a' = b
        · rw [hab', ← hj]; exact hoccj
        · exact hoccu _ (adv_lt hj0 (by omega)) hne (hinv.window a' ha'a hab')
      · intro s hs hos d hd
        by_cases hsj : s = j.toNat
        · -- the key that moved to slot j
          rw [hsj, hkeyj] at hd ⊢
          left
          have hr := home_lt (m := M.toNat) (keyAt t i.toNat) hm0
          have hadd := dist_add (s := i.toNat) hr hjm (by rw [hdji]; exact hc')
          rw [hdji] at hadd
          have hdi : d < dist M.toNat (home M.toNat (keyAt t i.toNat)) i.toNat := by omega
          have hq := adv_lt hr (show d < M.toNat by have := dist_lt hr hjm; omega)
          have hdq := dist_adv hr (show d < M.toNat by have := dist_lt hr hjm; omega)
          have hqj : adv M.toNat (home M.toNat (keyAt t i.toNat)) d ≠ j.toNat := fun h => by
            rw [h] at hdq; omega
          have hqi : adv M.toNat (home M.toNat (keyAt t i.toNat)) d ≠ i.toNat := fun h => by
            rw [h] at hdq; omega
          rcases hinv.reach i.toNat him hoi d hdi with h | ⟨h, -⟩
          · exact hoccu _ hq hqi h
          · rw [← hj] at h; exact absurd h hqj
        · have hsi : s ≠ i.toNat := fun h => by rw [h] at hos; exact hnoti hos
          have hot : occ t s := by unfold occ at hos ⊢; rw [(hsame s hsi hsj).1] at hos; exact hos
          have hks : keyAt (move j i t) s = keyAt t s := (hsame s hsi hsj).2
          rw [hks] at hd ⊢
          have hr := home_lt (m := M.toNat) (keyAt t s) hm0
          have hq := adv_lt hr (show d < M.toNat by have := dist_lt hr hs; omega)
          rcases hinv.reach s hs hot d hd with h | ⟨h, -⟩
          · by_cases hqi : adv M.toNat (home M.toNat (keyAt t s)) d = i.toNat
            · right
              refine ⟨by rw [hqi, hi], ?_⟩
              have : dist M.toNat (adv M.toNat j0 a) s ≠ 0 := fun h0 => by
                rw [← hi] at h0; exact hsi ((dist_eq_zero him).mp h0).symm
              omega
            · exact Or.inl (hoccu _ hq hqi h)
          · left; rw [h, ← hj]; exact hoccj
  · rw [ite_eq_right (show ¬ (0 < fuel ∧ 0 < t[(i + i).toNat]!) from fun h => ho h.2)]
    have hnoi : ¬ occ t i.toNat := by unfold occ; rw [← hi2]; exact ho
    refine ⟨hsz, hperm, hnodup, Or.inr (by omega), ?_⟩
    intro s hs hos d hd
    have hr := home_lt (m := M.toNat) (keyAt t s) hm0
    rcases hinv.reach s hs hos d hd with h | ⟨hp, hle⟩
    · exact h
    · exfalso
      rw [← hj] at hp hle
      have hdl := dist_lt hr hs
      have hdm : d < M.toNat := by omega
      have hdq : dist M.toNat (home M.toNat (keyAt t s)) j.toNat = d := by rw [← hp]; exact dist_adv hr hdm
      have hjs := dist_from_adv hr hs (Nat.le_of_lt hd)
      rw [hp] at hjs
      rcases Nat.lt_or_ge (a - b) (dist M.toNat j.toNat s) with hlt | hge
      · have hd' : d + (a - b) < dist M.toNat (home M.toNat (keyAt t s)) s := by omega
        have hq : adv M.toNat (home M.toNat (keyAt t s)) (d + (a - b)) = i.toNat := by
          rw [← adv_adv (d := d) (e := a - b) hr (by omega), hp, hj,
            adv_adv (d := b) (e := a - b) hj0 (by omega),
            Nat.add_sub_cancel' (Nat.le_of_lt hba), ← hi]
        rcases hinv.reach s hs hos _ hd' with h | ⟨h, -⟩
        · rw [hq] at h; exact hnoi h
        · rw [hq, ← hj] at h; exact hji h.symm
      · have hsi : s = i.toNat := by
          rw [hi]; exact slot_after hj0 (Nat.le_of_lt hba) ham hs (by rw [← hj]; omega)
        rw [hsi] at hos; exact hnoi hos
termination_by M.toNat - a
decreasing_by all_goals omega

/-- A deletion of a key of the table empties its slot and runs Algorithm R from the next slot. -/
theorem delete_good (M k : UInt64) (t : Array UInt64) (keys : List UInt64)
    (hm : M.toNat < 2 ^ 63) (hg : Good M.toNat t keys) (hk : k ∈ keys) :
    Good M.toNat (close M (slot M k t) (next M (slot M k t)) M
      (t.set! (slot M k t + slot M k t).toNat 0)) (keys.erase k) := by
  have hlen1 : keys.length + 1 ≤ M.toNat := by
    rcases hg.room with h | h
    · rw [h] at hk; simp at hk
    · exact h
  have hpos : 0 < keys.length := List.length_pos_of_mem hk
  have hm0 : 0 < M.toNat := by omega
  have hr := home_lt (m := M.toNat) k hm0
  obtain ⟨e, he, hs, -, hiff, hkey⟩ := slot_spec M k t keys hm hm0 hg
  have hj0 := adv_lt hr he
  have hocc := hiff.mpr hk
  have hk0 := hkey hocc
  generalize hJ : adv M.toNat (home M.toNat k) e = j0 at hj0 hocc hk0 hs
  obtain ⟨hs2, -⟩ := twice (show (slot M k t).toNat < 2 ^ 63 by omega)
  rw [hs2, hs]
  have hsz := hg.size
  have hw : ∀ x, (t.set! (2 * j0) 0)[x]! = if x = 2 * j0 then 0 else t[x]! :=
    fun x => get_set _ _ _ x (by omega)
  have hhole : ¬ occ (t.set! (2 * j0) 0) j0 := by unfold occ; rw [hw, ite_eq_left rfl]; decide
  have hsame : ∀ p, p ≠ j0 → (t.set! (2 * j0) 0)[2 * p]! = t[2 * p]! ∧
      (t.set! (2 * j0) 0)[2 * p + 1]! = t[2 * p + 1]! := by
    intro p hp
    have h1 : ¬ (2 * p = 2 * j0) := by omega
    have h2 : ¬ (2 * p + 1 = 2 * j0) := by omega
    rw [hw, hw, ite_eq_right h1, ite_eq_right h2]
    exact ⟨rfl, rfl⟩
  have hfill := tableKeys_fill (u := t) hj0 hhole hocc hk0 fun p _ hp => ⟨(hsame p hp).1, (hsame p hp).2⟩
  have hperm : (tableKeys M.toNat (t.set! (2 * j0) 0)).Perm (keys.erase k) := by
    have := (hg.perm.symm.trans hfill).erase k
    rw [List.erase_cons_head] at this
    exact this.symm
  refine close_spec M hm j0 hj0 (keys.erase k) (hg.nodup.erase k)
    (by rw [List.length_erase_of_mem hk]; omega) 0 1 (t.set! (2 * j0) 0) ?_ hperm (slot M k t)
    (next M (slot M k t)) M (by rw [hs, adv_zero hj0])
    (by rw [next_toNat hm (by rw [hs]; exact hj0), hs]) (by omega)
  refine ⟨by simp; omega, by omega, by omega, by rw [adv_zero hj0]; exact hhole,
    fun a' ha' hab => absurd ha' (by omega), ?_⟩
  intro s hs' hos d hd
  have hsj : s ≠ j0 := fun h => by rw [h] at hos; exact hhole hos
  have hot : occ t s := by unfold occ at hos ⊢; rw [(hsame s hsj).1] at hos; exact hos
  have hks : keyAt (t.set! (2 * j0) 0) s = keyAt t s := (hsame s hsj).2
  rw [hks] at hd ⊢
  have hq := hg.reach s hs' hot d hd
  by_cases hqj : adv M.toNat (home M.toNat (keyAt t s)) d = j0
  · right
    refine ⟨by rw [hqj, adv_zero hj0], ?_⟩
    rw [adv_zero hj0]
    have : dist M.toNat j0 s ≠ 0 := fun h0 => hsj ((dist_eq_zero hj0).mp h0).symm
    omega
  · left; unfold occ at hq ⊢; rw [(hsame _ hqj).1]; exact hq

/-! ### The loop -/

/-- One operation of the list of keys on the keys and the outputs. -/
def specStep (m : Nat) (st : List UInt64 × List UInt64) (o : UInt64 × UInt64) :
    List UInt64 × List UInt64 :=
  if o.1 = 0 then
    if o.2 ∈ st.1 ∨ m ≤ st.1.length + 1 then (st.1, st.2 ++ [0]) else (o.2 :: st.1, st.2 ++ [1])
  else if o.1 = 1 then (st.1, st.2 ++ [if o.2 ∈ st.1 then 1 else 0])
  else if o.2 ∈ st.1 then (st.1.erase o.2, st.2 ++ [1]) else (st.1, st.2 ++ [0])

theorem runOps_eq (m : Nat) (ops : List (UInt64 × UInt64)) (keys out : List UInt64) :
    runOps m ops keys out = (ops.foldl (specStep m) (keys, out)).2 := by
  induction ops generalizing keys out with
  | nil => rfl
  | cons o rest ih =>
    obtain ⟨op, k⟩ := o
    simp only [runOps, List.foldl_cons, specStep]
    split_ifs <;> exact ih _ _

/-- The state of the loop, the outputs, the number of keys, and the table, agrees with the state of
the list of keys. -/
def Agrees (m : Nat) (s : Array UInt64 × UInt64 × Array UInt64)
    (st : List UInt64 × List UInt64) : Prop :=
  Good m s.2.2 st.1 ∧ s.2.1.toNat = st.1.length ∧ s.1.toList = st.2

/-- The slot where the search for `k` ends is occupied exactly when `k` is a key. -/
theorem present_iff (M k : UInt64) (t : Array UInt64) (keys : List UInt64)
    (hm : M.toNat < 2 ^ 63) (hg : Good M.toNat t keys) :
    0 < t[(slot M k t + slot M k t).toNat]! ↔ k ∈ keys := by
  by_cases hm0 : M.toNat = 0
  · have hk : keys = [] := by
      have := hg.perm
      rw [show tableKeys M.toNat t = [] by simp [tableKeys, hm0]] at this
      exact List.nil_perm.mp this
    have hz : t[(slot M k t + slot M k t).toNat]! = 0 := by
      rw [getElem!_neg t _ (by have := hg.size; omega)]; rfl
    rw [hz, hk]
    simp
  · obtain ⟨e, he, hs, -, hiff, -⟩ := slot_spec M k t keys hm (by omega) hg
    have hr := home_lt (m := M.toNat) k (by omega)
    obtain ⟨hs2, -⟩ := twice (show (slot M k t).toNat < 2 ^ 63 by
      rw [hs]; have := adv_lt hr he; omega)
    rw [hs2, hs]
    exact hiff

/-- One operation keeps the agreement. -/
theorem step_agrees (M op k : UInt64) (o t : Array UInt64) (n : UInt64) (keys out : List UInt64)
    (hm : M.toNat < 2 ^ 63) (hA : Agrees M.toNat (o, n, t) (keys, out)) :
    Agrees M.toNat (step M op k (o, n, t)) (specStep M.toNat (keys, out) (op, k)) := by
  obtain ⟨hg, hn, hout⟩ := hA
  dsimp only at hg hn hout
  have hlen : keys.length ≤ M.toNat := by
    rcases hg.room with h | h
    · simp [h]
    · omega
  have hn1 : (n + 1).toNat = keys.length + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  have hfull : M ≤ n + 1 ↔ M.toNat ≤ keys.length + 1 := by rw [UInt64.le_iff_toNat_le, hn1]
  have hpres := present_iff M k t keys hm hg
  unfold step specStep Agrees
  dsimp only
  by_cases h0 : op = 0
  · subst h0
    by_cases hc : k ∈ keys ∨ M.toNat ≤ keys.length + 1
    · have hc' : 0 < t[(slot M k t + slot M k t).toNat]! ∨ M ≤ n + 1 := by rwa [hpres, hfull]
      simp only [hc, hc', ↓reduceIte]
      exact ⟨hg, hn, by rw [Array.toList_push, hout]⟩
    · have hc' : ¬ (0 < t[(slot M k t + slot M k t).toNat]! ∨ M ≤ n + 1) := by
        rwa [hpres, hfull]
      simp only [hc, hc', ↓reduceIte]
      have hk : k ∉ keys := fun h => hc (Or.inl h)
      have hroom : keys.length + 2 ≤ M.toNat := by omega
      have hm0 : 0 < M.toNat := by omega
      have hr := home_lt (m := M.toNat) k hm0
      obtain ⟨e, he, hs, hpath, hiff, -⟩ := slot_spec M k t keys hm hm0 hg
      obtain ⟨hs2, hs21⟩ := twice (show (slot M k t).toNat < 2 ^ 63 by
        rw [hs]; have := adv_lt hr he; omega)
      rw [hs2, hs21, hs]
      refine ⟨insert_good hg he hpath (fun h => hk (hiff.mp h)) hk hroom, by rw [hn1]; rfl,
        by rw [Array.toList_push, hout]⟩
  · by_cases h1 : op = 1
    · subst h1
      have h10 : ¬ ((1 : UInt64) = 0) := by decide
      simp only [h10, ↓reduceIte, hpres]
      exact ⟨hg, hn, by rw [Array.toList_push, hout]⟩
    · by_cases hk : k ∈ keys
      · have hk' : 0 < t[(slot M k t + slot M k t).toNat]! := hpres.mpr hk
        simp only [h0, h1, hk, hk', ↓reduceIte]
        refine ⟨delete_good M k t keys hm hg hk, ?_, by rw [Array.toList_push, hout]⟩
        rw [sub_one (by have := List.length_pos_of_mem hk; omega), hn, List.length_erase_of_mem hk]
      · have hk' : ¬ 0 < t[(slot M k t + slot M k t).toNat]! := fun h => hk (hpres.mp h)
        simp only [h0, h1, hk, hk', ↓reduceIte]
        exact ⟨hg, hn, by rw [Array.toList_push, hout]⟩

theorem hashTable_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) (hm : slots xs < 2 ^ 63) :
    hashTable xs = expected xs := by
  have hS : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold hashTable expected
  by_cases h0 : xs.size.toUInt64 = 0
  · rw [ite_eq_left h0]
    have hz : xs.size = 0 := by rw [← hS, h0]; rfl
    simp [operations, hz, runOps]
  · rw [ite_eq_right h0]
    have hpos : 0 < xs.size := by
      by_contra hc
      exact h0 (by rw [show xs.size = 0 by omega]; rfl)
    have hN : ((xs.size.toUInt64 - 1) / 2).toNat = (xs.size - 1) / 2 := by
      rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr
        (by rw [hS]; simp only [UInt64.reduceToNat]; omega)), hS]
      simp only [UInt64.reduceToNat]
    have hM : xs[(0 : UInt64).toNat]!.toNat = slots xs := by simp only [UInt64.reduceToNat]; rfl
    have hMm : xs[(0 : UInt64).toNat]!.toNat < 2 ^ 63 := by rw [hM]; exact hm
    have hMM : (xs[(0 : UInt64).toNat]! + xs[(0 : UInt64).toNat]!).toNat =
        2 * xs[(0 : UInt64).toNat]!.toNat := (twice hMm).1
    have h := loop_induction (n := (xs.size.toUInt64 - 1) / 2)
      (init := ((#[] : Array UInt64), (0 : UInt64),
        LeanExe.build (xs[(0 : UInt64).toNat]! + xs[(0 : UInt64).toNat]!) fun _ => (0 : UInt64)))
      (f := fun e s => step xs[(0 : UInt64).toNat]! xs[(e + e + 1).toNat]! xs[(e + e + 2).toNat]! s)
      (P := fun k s => Agrees xs[(0 : UInt64).toNat]!.toNat s
        (((operations xs).take k).foldl (specStep xs[(0 : UInt64).toNat]!.toNat) ([], [])))
      (by
        have hz : ∀ x : Nat, (LeanExe.build (xs[(0 : UInt64).toNat]! + xs[(0 : UInt64).toNat]!)
            fun _ => (0 : UInt64))[x]! = 0 := by
          intro x
          by_cases hx : x < (xs[(0 : UInt64).toNat]! + xs[(0 : UInt64).toNat]!).toNat
          · rw [build_get hx]
          · rw [build_get_out hx]; rfl
        have hno : ∀ s, ¬ occ (LeanExe.build (xs[(0 : UInt64).toNat]! + xs[(0 : UInt64).toNat]!)
            fun _ => (0 : UInt64)) s := by
          intro s; unfold occ; rw [hz]; decide
        refine ⟨⟨?_, ?_, List.nodup_nil, Or.inl rfl, fun s _ ho => absurd ho (hno s)⟩, rfl, rfl⟩
        · dsimp only; rw [build_size, hMM]
        · dsimp only; rw [tableKeys_empty fun s _ => hno s]; simp)
      (by
        intro k s hk hA
        rw [hN] at hk
        have hkk : (UInt64.ofNat k).toNat = k :=
          UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
        have h1 : (UInt64.ofNat k + UInt64.ofNat k + 1).toNat = 2 * k + 1 := by
          simp only [UInt64.toNat_add, hkk, UInt64.reduceToNat]; omega
        have h2 : (UInt64.ofNat k + UInt64.ofNat k + 2).toNat = 2 * k + 2 := by
          simp only [UInt64.toNat_add, hkk, UInt64.reduceToNat]; omega
        have htake : (operations xs).take (k + 1) =
            (operations xs).take k ++ [(xs[2 * k + 1]!, xs[2 * k + 2]!)] := by
          rw [List.take_add_one]
          simp [operations, hk]
        rw [h1, h2, htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
        generalize ((operations xs).take k).foldl (specStep xs[(0 : UInt64).toNat]!.toNat)
          ([], []) = st at hA
        obtain ⟨keys, out⟩ := st
        obtain ⟨o, n, t⟩ := s
        exact step_agrees _ _ _ o t n keys out hMm hA)
    rw [hN, List.take_of_length_le (by simp [operations])] at h
    obtain ⟨-, -, hout⟩ := h
    rw [runOps_eq, ← hM, ← hout, Array.toArray_toList]

end Library.HashTables.LinearProbing
