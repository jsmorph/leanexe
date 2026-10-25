import Library.Regex.Spec

/-! Glushkov's theorem for the regular expressions of `Library.Regex.Spec`.  The sets of bytes of
an expression are its positions, numbered `k + 1` to `k + r.positions` from an offset `k` in the
order of the expression.  `First`, `Last`, and `Follow` give the positions that may begin a word,
end it, and come after a given position, and `Class` the bytes of each position.  `glushkov`
states that a word is in the language exactly when it is empty and the expression is nullable,
or when its first byte is in the set of a first position from which `Accepts` reads the rest:
each later byte in the set of a position that may follow the one before, and the last position
one that may end a word.  The matcher of `Library.Regex.Program` runs this automaton on sets of
positions. -/

namespace Library.Regex.Glushkov

open Library.Regex.Spec
open scoped Computability

/-- Whether the language of an expression holds the empty word. -/
def nullable : Re → Bool
  | .empty => false
  | .eps => true
  | .cls _ => false
  | .cat a b => nullable a && nullable b
  | .alt a b => nullable a || nullable b
  | .star _ => true

/-- `First r k q`: position `q` may hold the first byte of a word of `r`, numbered from `k`. -/
def First : Re → Nat → Nat → Prop
  | .empty, _, _ | .eps, _, _ => False
  | .cls _, k, q => q = k + 1
  | .cat a b, k, q => First a k q ∨ (nullable a = true ∧ First b (k + a.positions) q)
  | .alt a b, k, q => First a k q ∨ First b (k + a.positions) q
  | .star a, k, q => First a k q

/-- `Last r k q`: position `q` may hold the last byte of a word of `r`. -/
def Last : Re → Nat → Nat → Prop
  | .empty, _, _ | .eps, _, _ => False
  | .cls _, k, q => q = k + 1
  | .cat a b, k, q => Last b (k + a.positions) q ∨ (nullable b = true ∧ Last a k q)
  | .alt a b, k, q => Last a k q ∨ Last b (k + a.positions) q
  | .star a, k, q => Last a k q

/-- `Follow r k p q`: position `q` may hold the byte after the byte of position `p`. -/
def Follow : Re → Nat → Nat → Nat → Prop
  | .empty, _, _, _ | .eps, _, _, _ | .cls _, _, _, _ => False
  | .cat a b, k, p, q =>
    Follow a k p q ∨ Follow b (k + a.positions) p q ∨ (Last a k p ∧ First b (k + a.positions) q)
  | .alt a b, k, p, q => Follow a k p q ∨ Follow b (k + a.positions) p q
  | .star a, k, p, q => Follow a k p q ∨ (Last a k p ∧ First a k q)

/-- `Class r k q c`: byte `c` is in the set of position `q`. -/
def Class : Re → Nat → Nat → UInt8 → Prop
  | .empty, _, _, _ | .eps, _, _, _ => False
  | .cls f, k, q, c => q = k + 1 ∧ f c = true
  | .cat a b, k, q, c | .alt a b, k, q, c => Class a k q c ∨ Class b (k + a.positions) q c
  | .star a, k, q, c => Class a k q c

/-- `Accepts r k p w`: the automaton reads `w` from position `p` and stops at a last position. -/
def Accepts (r : Re) (k : Nat) : Nat → List UInt8 → Prop
  | p, [] => Last r k p
  | p, c :: w => ∃ q, Follow r k p q ∧ Class r k q c ∧ Accepts r k q w

/-- The words that the automaton of `r` accepts from its start. -/
def Matches (r : Re) (k : Nat) (w : List UInt8) : Prop :=
  (w = [] ∧ nullable r = true) ∨
    ∃ c w', w = c :: w' ∧ ∃ p, First r k p ∧ Class r k p c ∧ Accepts r k p w'

/-- The positions of `r` numbered from `k`. -/
def InRange (r : Re) (k q : Nat) : Prop := k < q ∧ q ≤ k + r.positions

theorem first_range : ∀ {r : Re} {k q : Nat}, First r k q → InRange r k q
  | .empty, _, _, h | .eps, _, _, h => h.elim
  | .cls _, k, q, h => by simp only [First] at h; simp only [InRange, Re.positions]; omega
  | .cat _ _, _, _, h => by
    rcases h with h | ⟨_, h⟩ <;>
      · have := first_range h; simp only [InRange, Re.positions] at this ⊢; omega
  | .alt _ _, _, _, h => by
    rcases h with h | h <;>
      · have := first_range h; simp only [InRange, Re.positions] at this ⊢; omega
  | .star a, _, _, h => by
    have := first_range (r := a) h; simp only [InRange, Re.positions] at this ⊢; omega

theorem last_range : ∀ {r : Re} {k q : Nat}, Last r k q → InRange r k q
  | .empty, _, _, h | .eps, _, _, h => h.elim
  | .cls _, k, q, h => by simp only [Last] at h; simp only [InRange, Re.positions]; omega
  | .cat _ _, _, _, h => by
    rcases h with h | ⟨_, h⟩ <;>
      · have := last_range h; simp only [InRange, Re.positions] at this ⊢; omega
  | .alt _ _, _, _, h => by
    rcases h with h | h <;>
      · have := last_range h; simp only [InRange, Re.positions] at this ⊢; omega
  | .star a, _, _, h => by
    have := last_range (r := a) h; simp only [InRange, Re.positions] at this ⊢; omega

theorem class_range : ∀ {r : Re} {k q : Nat} {c : UInt8}, Class r k q c → InRange r k q
  | .empty, _, _, _, h | .eps, _, _, _, h => h.elim
  | .cls _, k, q, _, h => by
    simp only [Class] at h; simp only [InRange, Re.positions]; omega
  | .cat _ _, _, _, _, h | .alt _ _, _, _, _, h => by
    rcases h with h | h <;>
      · have := class_range h; simp only [InRange, Re.positions] at this ⊢; omega
  | .star a, _, _, _, h => by
    have := class_range (r := a) h; simp only [InRange, Re.positions] at this ⊢; omega

theorem follow_range : ∀ {r : Re} {k p q : Nat}, Follow r k p q → InRange r k p ∧ InRange r k q
  | .empty, _, _, _, h | .eps, _, _, _, h | .cls _, _, _, _, h => h.elim
  | .cat _ _, _, _, _, h => by
    rcases h with h | h | ⟨h, h'⟩
    · have := follow_range h; simp only [InRange, Re.positions] at this ⊢; omega
    · have := follow_range h; simp only [InRange, Re.positions] at this ⊢; omega
    · have := last_range h; have := first_range h'
      simp only [InRange, Re.positions] at *; omega
  | .alt _ _, _, _, _, h => by
    rcases h with h | h <;>
      · have := follow_range h; simp only [InRange, Re.positions] at this ⊢; omega
  | .star a, _, _, _, h => by
    rcases h with h | ⟨h, h'⟩
    · have := follow_range (r := a) h; simp only [InRange, Re.positions] at this ⊢; omega
    · have := last_range (r := a) h; have := first_range (r := a) h'
      simp only [InRange, Re.positions] at *; omega

theorem not_range_right {a b : Re} {k p : Nat} (h : InRange a k p) :
    ¬ InRange b (k + a.positions) p := by
  simp only [InRange] at h ⊢; omega

theorem not_range_left {a b : Re} {k p : Nat} (h : InRange b (k + a.positions) p) :
    ¬ InRange a k p := by
  simp only [InRange] at h ⊢; omega

/-- The set of a position of `a` in `cat a b` or `alt a b` is its set in `a`. -/
theorem class_left {a b : Re} {k q : Nat} {c : UInt8} (hq : InRange a k q) :
    (Class a k q c ∨ Class b (k + a.positions) q c) ↔ Class a k q c :=
  ⟨fun h => h.elim id fun h => absurd (class_range h) (not_range_right hq), Or.inl⟩

/-- The set of a position of `b` in `cat a b` or `alt a b` is its set in `b`. -/
theorem class_right {a b : Re} {k q : Nat} {c : UInt8} (hq : InRange b (k + a.positions) q) :
    (Class a k q c ∨ Class b (k + a.positions) q c) ↔ Class b (k + a.positions) q c :=
  ⟨fun h => h.elim (fun h => absurd (class_range h) (not_range_left hq)) id, Or.inr⟩

/-- Reading from a position of `b` in `cat a b` is reading in `b`. -/
theorem accepts_cat_right {a b : Re} {k : Nat} :
    ∀ (w : List UInt8) {p : Nat}, InRange b (k + a.positions) p →
      (Accepts (.cat a b) k p w ↔ Accepts b (k + a.positions) p w)
  | [], p, hp => by
    show (Last b _ p ∨ (nullable b = true ∧ Last a k p)) ↔ Last b _ p
    exact ⟨fun h => h.elim id fun h => absurd (last_range h.2) (not_range_left hp), Or.inl⟩
  | c :: w, p, hp => by
    show (∃ q, Follow (.cat a b) k p q ∧ Class (.cat a b) k q c ∧ Accepts (.cat a b) k q w) ↔
      ∃ q, Follow b _ p q ∧ Class b _ q c ∧ Accepts b _ q w
    constructor
    · rintro ⟨q, hf, hc, hw⟩
      rcases hf with hf | hf | ⟨hl, _⟩
      · exact absurd (follow_range hf).1 (not_range_left hp)
      · have hq := (follow_range hf).2
        exact ⟨q, hf, (class_right hq).1 hc, (accepts_cat_right w hq).1 hw⟩
      · exact absurd (last_range hl) (not_range_left hp)
    · rintro ⟨q, hf, hc, hw⟩
      have hq := (follow_range hf).2
      exact ⟨q, Or.inr (Or.inl hf), (class_right hq).2 hc, (accepts_cat_right w hq).2 hw⟩

/-- Reading from a position of `a` in `alt a b` is reading in `a`. -/
theorem accepts_alt_left {a b : Re} {k : Nat} :
    ∀ (w : List UInt8) {p : Nat}, InRange a k p →
      (Accepts (.alt a b) k p w ↔ Accepts a k p w)
  | [], p, hp => by
    show (Last a k p ∨ Last b _ p) ↔ Last a k p
    exact ⟨fun h => h.elim id fun h => absurd (last_range h) (not_range_right hp), Or.inl⟩
  | c :: w, p, hp => by
    show (∃ q, Follow (.alt a b) k p q ∧ Class (.alt a b) k q c ∧ Accepts (.alt a b) k q w) ↔
      ∃ q, Follow a k p q ∧ Class a k q c ∧ Accepts a k q w
    constructor
    · rintro ⟨q, hf, hc, hw⟩
      rcases hf with hf | hf
      · have hq := (follow_range hf).2
        exact ⟨q, hf, (class_left hq).1 hc, (accepts_alt_left w hq).1 hw⟩
      · exact absurd (follow_range hf).1 (not_range_right hp)
    · rintro ⟨q, hf, hc, hw⟩
      have hq := (follow_range hf).2
      exact ⟨q, Or.inl hf, (class_left hq).2 hc, (accepts_alt_left w hq).2 hw⟩

/-- Reading from a position of `b` in `alt a b` is reading in `b`. -/
theorem accepts_alt_right {a b : Re} {k : Nat} :
    ∀ (w : List UInt8) {p : Nat}, InRange b (k + a.positions) p →
      (Accepts (.alt a b) k p w ↔ Accepts b (k + a.positions) p w)
  | [], p, hp => by
    show (Last a k p ∨ Last b _ p) ↔ Last b _ p
    exact ⟨fun h => h.elim (fun h => absurd (last_range h) (not_range_left hp)) id, Or.inr⟩
  | c :: w, p, hp => by
    show (∃ q, Follow (.alt a b) k p q ∧ Class (.alt a b) k q c ∧ Accepts (.alt a b) k q w) ↔
      ∃ q, Follow b _ p q ∧ Class b _ q c ∧ Accepts b _ q w
    constructor
    · rintro ⟨q, hf, hc, hw⟩
      rcases hf with hf | hf
      · exact absurd (follow_range hf).1 (not_range_left hp)
      · have hq := (follow_range hf).2
        exact ⟨q, hf, (class_right hq).1 hc, (accepts_alt_right w hq).1 hw⟩
    · rintro ⟨q, hf, hc, hw⟩
      have hq := (follow_range hf).2
      exact ⟨q, Or.inr hf, (class_right hq).2 hc, (accepts_alt_right w hq).2 hw⟩

/-- Reading from a position of `a` in `cat a b` is reading a word of `a` to one of its last
positions, followed by a word of `b`. -/
theorem accepts_cat_left {a b : Re} {k : Nat}
    (hb : ∀ w, w ∈ b.lang ↔ Matches b (k + a.positions) w) :
    ∀ (w : List UInt8) {p : Nat}, InRange a k p →
      (Accepts (.cat a b) k p w ↔ ∃ u v, w = u ++ v ∧ Accepts a k p u ∧ v ∈ b.lang)
  | [], p, hp => by
    show (Last b _ p ∨ (nullable b = true ∧ Last a k p)) ↔ _
    constructor
    · rintro (h | ⟨hn, hl⟩)
      · exact absurd (last_range h) (not_range_right hp)
      · exact ⟨[], [], rfl, hl, (hb []).2 (Or.inl ⟨rfl, hn⟩)⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv.symm
      rcases (hb []).1 hv with ⟨_, hn⟩ | ⟨_, _, h, _⟩
      · exact Or.inr ⟨hn, hu⟩
      · exact absurd h.symm (List.cons_ne_nil _ _)
  | c :: w, p, hp => by
    show (∃ q, Follow (.cat a b) k p q ∧ Class (.cat a b) k q c ∧ Accepts (.cat a b) k q w) ↔ _
    constructor
    · rintro ⟨q, hf, hc, hw⟩
      rcases hf with hf | hf | ⟨hl, hfb⟩
      · have hq := (follow_range hf).2
        obtain ⟨u, v, rfl, hu, hv⟩ := (accepts_cat_left hb w hq).1 hw
        exact ⟨c :: u, v, rfl, ⟨q, hf, (class_left hq).1 hc, hu⟩, hv⟩
      · exact absurd (follow_range hf).1 (not_range_right hp)
      · have hq := first_range hfb
        refine ⟨[], c :: w, rfl, hl, (hb _).2 (Or.inr ⟨c, w, rfl, q, hfb, ?_, ?_⟩)⟩
        · exact (class_right hq).1 hc
        · exact (accepts_cat_right w hq).1 hw
    · rintro ⟨u, v, huv, hu, hv⟩
      cases u with
      | nil =>
        simp only [List.nil_append] at huv
        subst huv
        rcases (hb _).1 hv with ⟨h, _⟩ | ⟨c', w', h, q, hfb, hc, hw⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          have hq := first_range hfb
          exact ⟨q, Or.inr (Or.inr ⟨hu, hfb⟩), (class_right hq).2 hc,
            (accepts_cat_right _ hq).2 hw⟩
      | cons c' u =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj huv
        obtain ⟨q, hf, hc, hu⟩ := hu
        have hq := (follow_range hf).2
        exact ⟨q, Or.inl hf, (class_left hq).2 hc, (accepts_cat_left hb _ hq).2 ⟨u, v, rfl, hu, hv⟩⟩

/-- A word of `l∗` that is not empty begins with a word of `l` that is not empty. -/
theorem kstar_cons {l : Language UInt8} {c : UInt8} {w : List UInt8} (h : c :: w ∈ l∗) :
    ∃ x y, c :: x ∈ l ∧ y ∈ l∗ ∧ w = x ++ y := by
  obtain ⟨L, hL, hmem⟩ := Language.mem_kstar.mp h
  induction L with
  | nil => exact absurd hL (by simp)
  | cons x rest ih =>
    cases x with
    | nil => exact ih (by simpa using hL) fun y hy => hmem y (List.mem_cons_of_mem _ hy)
    | cons c' x =>
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hL
      obtain ⟨rfl, rfl⟩ := hL
      exact ⟨x, rest.flatten, hmem _ List.mem_cons_self,
        Language.mem_kstar.mpr ⟨rest, rfl, fun y hy => hmem y (List.mem_cons_of_mem _ hy)⟩, rfl⟩

/-- A word of `l` followed by a word of `l∗` is a word of `l∗`. -/
theorem append_kstar {l : Language UInt8} {x y : List UInt8} (hx : x ∈ l) (hy : y ∈ l∗) :
    x ++ y ∈ l∗ := by
  obtain ⟨L, rfl, hmem⟩ := Language.mem_kstar.mp hy
  exact Language.mem_kstar.mpr ⟨x :: L, by simp, fun z hz => by
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact hmem z hz⟩

/-- Reading from a position of `a` in `star a` is reading a word of `a` to one of its last
positions, followed by a word of `a.lang∗`. -/
theorem accepts_star {a : Re} {k : Nat} (ha : ∀ w, w ∈ a.lang ↔ Matches a k w) :
    ∀ (w : List UInt8) {p : Nat}, InRange a k p →
      (Accepts (.star a) k p w ↔ ∃ u v, w = u ++ v ∧ Accepts a k p u ∧ v ∈ a.lang∗)
  | [], p, _ => by
    show Last a k p ↔ _
    constructor
    · intro h
      exact ⟨[], [], rfl, h, Language.nil_mem_kstar _⟩
    · rintro ⟨u, v, huv, hu, _⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv.symm
      exact hu
  | c :: w, p, hp => by
    show (∃ q, Follow (.star a) k p q ∧ Class a k q c ∧ Accepts (.star a) k q w) ↔ _
    constructor
    · rintro ⟨q, hf, hc, hw⟩
      have hq := class_range hc
      obtain ⟨u, v, rfl, hu, hv⟩ := (accepts_star ha w hq).1 hw
      rcases hf with hf | ⟨hl, hfa⟩
      · exact ⟨c :: u, v, rfl, ⟨q, hf, hc, hu⟩, hv⟩
      · refine ⟨[], c :: (u ++ v), rfl, hl, ?_⟩
        exact append_kstar ((ha _).2 (Or.inr ⟨c, u, rfl, q, hfa, hc, hu⟩)) hv
    · rintro ⟨u, v, huv, hu, hv⟩
      cases u with
      | nil =>
        simp only [List.nil_append] at huv
        subst huv
        obtain ⟨x, y, hx, hy, rfl⟩ := kstar_cons hv
        rcases (ha _).1 hx with ⟨h, _⟩ | ⟨c', x', h, q, hfa, hc, hx'⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨q, Or.inr ⟨hu, hfa⟩, hc,
            (accepts_star ha _ (first_range hfa)).2 ⟨x, y, rfl, hx', hy⟩⟩
      | cons c' u =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj huv
        obtain ⟨q, hf, hc, hu⟩ := hu
        exact ⟨q, Or.inl hf, hc,
          (accepts_star ha _ (follow_range hf).2).2 ⟨u, v, rfl, hu, hv⟩⟩

/-- Glushkov's theorem: a word is in the language of `r` exactly when the position automaton of
`r` accepts it, with positions numbered from any offset `k`. -/
theorem glushkov : ∀ (r : Re) (k : Nat) (w : List UInt8), w ∈ r.lang ↔ Matches r k w
  | .empty, k, w => by
    show w ∈ (0 : Language UInt8) ↔ Matches .empty k w
    simp only [Matches, nullable, First]
    simp [Language.notMem_zero]
  | .eps, k, w => by
    show w ∈ (1 : Language UInt8) ↔ Matches .eps k w
    simp only [Matches, nullable, First, Language.mem_one]
    simp
  | .cls f, k, w => by
    show w ∈ {w | ∃ b, f b = true ∧ w = [b]} ↔ Matches (.cls f) k w
    simp only [Matches, nullable, First, Class, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Or.inr ⟨b, [], rfl, k + 1, rfl, ⟨rfl, hb⟩, (rfl : k + 1 = k + 1)⟩
    · rintro (⟨_, h⟩ | ⟨c, w', rfl, p, rfl, ⟨_, hc⟩, hw⟩)
      · exact absurd h Bool.false_ne_true
      · cases w' with
        | nil => exact ⟨c, hc, rfl⟩
        | cons _ _ => obtain ⟨_, h, _⟩ := hw; exact h.elim
  | .cat a b, k, w => by
    have iha := glushkov a k
    have ihb := glushkov b (k + a.positions)
    show w ∈ a.lang * b.lang ↔ Matches (.cat a b) k w
    rw [Language.mem_mul]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      rcases (iha u).1 hu with ⟨rfl, hna⟩ | ⟨c, u', rfl, p, hfa, hc, hu'⟩
      · rcases (ihb v).1 hv with ⟨rfl, hnb⟩ | ⟨c, v', rfl, q, hfb, hc, hv'⟩
        · exact Or.inl ⟨rfl, by simp [nullable, hna, hnb]⟩
        · have hq := first_range hfb
          exact Or.inr ⟨c, v', rfl, q, Or.inr ⟨hna, hfb⟩, (class_right hq).2 hc,
            (accepts_cat_right v' hq).2 hv'⟩
      · have hp := first_range hfa
        exact Or.inr ⟨c, u' ++ v, rfl, p, Or.inl hfa, (class_left hp).2 hc,
          (accepts_cat_left ihb _ hp).2 ⟨u', v, rfl, hu', hv⟩⟩
    · rintro (⟨rfl, hn⟩ | ⟨c, w', rfl, p, hf, hc, hw⟩)
      · simp only [nullable, Bool.and_eq_true] at hn
        exact ⟨[], (iha []).2 (Or.inl ⟨rfl, hn.1⟩), [], (ihb []).2 (Or.inl ⟨rfl, hn.2⟩), rfl⟩
      · rcases hf with hfa | ⟨hna, hfb⟩
        · have hp := first_range hfa
          obtain ⟨u, v, rfl, hu, hv⟩ := (accepts_cat_left ihb w' hp).1 hw
          exact ⟨c :: u, (iha _).2 (Or.inr ⟨c, u, rfl, p, hfa, (class_left hp).1 hc, hu⟩), v, hv,
            rfl⟩
        · have hp := first_range hfb
          exact ⟨[], (iha []).2 (Or.inl ⟨rfl, hna⟩), c :: w',
            (ihb _).2 (Or.inr ⟨c, w', rfl, p, hfb, (class_right hp).1 hc,
              (accepts_cat_right w' hp).1 hw⟩), rfl⟩
  | .alt a b, k, w => by
    have iha := glushkov a k
    have ihb := glushkov b (k + a.positions)
    show w ∈ a.lang + b.lang ↔ Matches (.alt a b) k w
    rw [Language.mem_add, iha, ihb]
    simp only [Matches, nullable, Bool.or_eq_true]
    constructor
    · rintro ((⟨rfl, hn⟩ | ⟨c, w', rfl, p, hf, hc, hw⟩) | (⟨rfl, hn⟩ | ⟨c, w', rfl, p, hf, hc, hw⟩))
      · exact Or.inl ⟨rfl, Or.inl hn⟩
      · have hp := first_range hf
        exact Or.inr ⟨c, w', rfl, p, Or.inl hf, (class_left hp).2 hc,
          (accepts_alt_left w' hp).2 hw⟩
      · exact Or.inl ⟨rfl, Or.inr hn⟩
      · have hp := first_range hf
        exact Or.inr ⟨c, w', rfl, p, Or.inr hf, (class_right hp).2 hc,
          (accepts_alt_right w' hp).2 hw⟩
    · rintro (⟨rfl, hn | hn⟩ | ⟨c, w', rfl, p, hf | hf, hc, hw⟩)
      · exact Or.inl (Or.inl ⟨rfl, hn⟩)
      · exact Or.inr (Or.inl ⟨rfl, hn⟩)
      · have hp := first_range hf
        exact Or.inl (Or.inr ⟨c, w', rfl, p, hf, (class_left hp).1 hc,
          (accepts_alt_left w' hp).1 hw⟩)
      · have hp := first_range hf
        exact Or.inr (Or.inr ⟨c, w', rfl, p, hf, (class_right hp).1 hc,
          (accepts_alt_right w' hp).1 hw⟩)
  | .star a, k, w => by
    have iha := glushkov a k
    show w ∈ a.lang∗ ↔ Matches (.star a) k w
    constructor
    · intro hw
      cases w with
      | nil => exact Or.inl ⟨rfl, rfl⟩
      | cons c w =>
        obtain ⟨x, y, hx, hy, rfl⟩ := kstar_cons hw
        rcases (iha _).1 hx with ⟨h, _⟩ | ⟨c', x', h, p, hf, hc, hx'⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact Or.inr ⟨c, x ++ y, rfl, p, hf, hc,
            (accepts_star iha _ (first_range hf)).2 ⟨x, y, rfl, hx', hy⟩⟩
    · rintro (⟨rfl, _⟩ | ⟨c, w', rfl, p, hf, hc, hw⟩)
      · exact Language.nil_mem_kstar _
      · obtain ⟨u, v, rfl, hu, hv⟩ := (accepts_star iha w' (first_range hf)).1 hw
        exact append_kstar ((iha _).2 (Or.inr ⟨c, u, rfl, p, hf, hc, hu⟩)) hv

#print axioms glushkov

end Library.Regex.Glushkov
