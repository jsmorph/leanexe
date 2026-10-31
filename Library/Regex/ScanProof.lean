import Library.Regex.RunProof

/-! The invariant of the pass `scan` over the pattern words.  For the stack of expressions that
`Spec.run` builds, listed from the bottom, entry `e` of the program's stack holds the
nullability and the `First` and `Last` positions below 64 of expression `e`, whose positions
start after those of the expressions below it.  The follow table holds `Follow` of every
expression on the stack, and the sets hold `Class`.  `scan_run` follows `Spec.run` word by word:
when it succeeds, the program's state holds the invariant for the resulting stack, and when it
fails, the program's state is invalid or still reading the words of a set. -/

namespace Library.Regex.ScanProof

open Library.Regex Library.Regex.Bits Library.Regex.Spec Library.Regex.Glushkov
  Library.Regex.RunProof

theorem get_set_self {a : Array UInt64} {i : Nat} (h : i < a.size) (v : UInt64) :
    (a.set! i v)[i]! = v := by
  simp [h]

theorem get_set_ne {a : Array UInt64} {i j : Nat} (hij : i ≠ j) (v : UInt64) :
    (a.set! i v)[j]! = a[j]! := by
  by_cases hj : j < a.size
  · simp [hj, hij]
  · simp [hj]

theorem size_set (a : Array UInt64) (i : Nat) (v : UInt64) : (a.set! i v).size = a.size := by
  simp

/-- `addFollow` adds `next` to the follow set of each position of `last`. -/
theorem addFollow_get {follow : Array UInt64} (hf : follow.size = 64) (last next : UInt64) :
    (addFollow follow last next).size = 64 ∧ ∀ p, p < 64 →
      (addFollow follow last next)[p]! = follow[p]! ||| (if bit last p then next else 0) := by
  have h := LeanExe.Dialect.loop_induction (n := 64) (init := follow)
    (f := fun q f => if (last >>> q) &&& 1 == 1 then f.set! q.toNat (f[q.toNat]! ||| next) else f)
    (P := fun k f => f.size = 64 ∧ ∀ p, p < 64 →
      f[p]! = follow[p]! ||| (if p < k ∧ bit last p = true then next else 0))
    ⟨hf, fun p _ => by simp⟩
    (by
      intro k f hk ⟨hsize, hget⟩
      have hk64 : k < 64 := by simpa using hk
      have hkt : (UInt64.ofNat k).toNat = k := toNat_ofNat_lt hk64 (by decide)
      rw [shiftRight_and_one (by omega), hkt]
      by_cases hb : bit last k = true
      · simp only [hb, ↓reduceIte]
        refine ⟨by rw [size_set, hsize], fun p hp => ?_⟩
        by_cases hpk : p = k
        · subst hpk
          rw [get_set_self (by omega), hget p hp]
          simp [hb]
        · rw [get_set_ne (Ne.symm hpk), hget p hp]
          have : (p < k + 1 ∧ bit last p = true) ↔ (p < k ∧ bit last p = true) :=
            ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩
          simp only [this]
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hsize, fun p hp => ?_⟩
        rw [hget p hp]
        by_cases hpk : p = k
        · subst hpk; simp [hb]
        · have : (p < k + 1 ∧ bit last p = true) ↔ (p < k ∧ bit last p = true) :=
            ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩
          simp only [this])
  refine ⟨h.1, fun p hp => ?_⟩
  have := h.2 p hp
  simp only [show (64 : UInt64).toNat = 64 from rfl] at this
  rw [addFollow, this]
  simp [hp]

/-- The bits of a follow set after `addFollow`. -/
theorem addFollow_bit {follow : Array UInt64} (hf : follow.size = 64) (last next : UInt64)
    {p : Nat} (hp : p < 64) (q : Nat) :
    bit (addFollow follow last next)[p]! q = true ↔
      bit follow[p]! q = true ∨ (bit last p = true ∧ bit next q = true) := by
  rw [(addFollow_get hf last next).2 p hp, bit_or, Bool.or_eq_true]
  by_cases hb : bit last p = true <;> simp [hb, bit_zero]

/-- The positions of the expressions below entry `e` of the stack `es`, listed from the bottom. -/
def off (es : List Re) (e : Nat) : Nat := ((es.take e).map Re.positions).sum

/-- The positions of all the expressions of the stack `es`. -/
def total (es : List Re) : Nat := (es.map Re.positions).sum

theorem total_append (es t : List Re) : total (es ++ t) = total es + total t := by
  simp [total]

theorem off_append {es : List Re} {e : Nat} (h : e ≤ es.length) (t : List Re) :
    off (es ++ t) e = off es e := by
  simp [off, List.take_append_of_le_length h]

theorem off_length (es : List Re) : off es es.length = total es := by
  simp [off, total]

/-- Entry `e` of the program's stack holds the nullability and the first and last positions
below 64 of `r`, numbered from `k`. -/
def EntryHolds (stack : Array UInt64) (r : Re) (k e : Nat) : Prop :=
  stack[3 * e]! = (if nullable r then 1 else 0) ∧
    (∀ q, bit stack[3 * e + 1]! q = true ↔ q < 64 ∧ First r k q) ∧
    (∀ q, bit stack[3 * e + 2]! q = true ↔ q < 64 ∧ Last r k q)

/-- The program's state after a whole number of expressions of a pattern of `pn` words, for the
stack `es` of those expressions listed from the bottom. -/
structure Corr (pn : Nat) (s : Scan) (es : List Re) : Prop where
  valid : s.valid = true
  skip : s.skip = 0
  depth : s.depth.toNat = es.length
  count : s.count.toNat = total es
  stackSize : s.stack.size = 3 * pn
  followSize : s.follow.size = 64
  setsSize : s.sets.size = 256
  entries : ∀ e (h : e < es.length), EntryHolds s.stack es[e] (off es e) e
  follow : ∀ p, p < 64 → ∀ q, bit s.follow[p]! q = true ↔
    q < 64 ∧ ∃ e, ∃ h : e < es.length, Follow es[e] (off es e) p q
  sets : ∀ p, 1 ≤ p → p ≤ total es → p < 64 → ∀ c : UInt8,
    inSet s.sets p c.toNat = true ↔ ∃ e, ∃ h : e < es.length, Class es[e] (off es e) p c

/-- `push` writes the entry `(e, f, l)` above the others and leaves the rest of the state. -/
theorem push_stack {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} (hsize : s.stack.size = 3 * pn)
    (hd : s.depth.toNat < pn) (e f l : UInt64) :
    (push s e f l).stack.size = 3 * pn ∧
      (push s e f l).depth.toNat = s.depth.toNat + 1 ∧
      (push s e f l).stack[3 * s.depth.toNat]! = e ∧
      (push s e f l).stack[3 * s.depth.toNat + 1]! = f ∧
      (push s e f l).stack[3 * s.depth.toNat + 2]! = l ∧
      (∀ x, x < 3 * s.depth.toNat → (push s e f l).stack[x]! = s.stack[x]!) ∧
      (push s e f l).valid = s.valid ∧ (push s e f l).count = s.count ∧
      (push s e f l).skip = s.skip ∧ (push s e f l).follow = s.follow ∧
      (push s e f l).sets = s.sets := by
  have hi : (3 * s.depth).toNat = 3 * s.depth.toNat := by
    rw [UInt64.toNat_mul, show (3 : UInt64).toNat = 3 from rfl]; omega
  have hi1 : (3 * s.depth + 1).toNat = 3 * s.depth.toNat + 1 := by
    rw [UInt64.toNat_add, hi, UInt64.toNat_one]; omega
  have hi2 : (3 * s.depth + 2).toNat = 3 * s.depth.toNat + 2 := by
    rw [UInt64.toNat_add, hi, show (2 : UInt64).toNat = 2 from rfl]; omega
  simp only [push, hi, hi1, hi2]
  refine ⟨by simp [hsize], by rw [UInt64.toNat_add, UInt64.toNat_one]; omega, ?_, ?_, ?_, ?_,
    (by first | rfl | trivial), (by first | rfl | trivial),
    (by first | rfl | trivial), (by first | rfl | trivial),
    (by first | rfl | trivial)⟩
  · rw [get_set_ne (by omega), get_set_ne (by omega), get_set_self (by omega)]
  · rw [get_set_ne (by omega), get_set_self (by simp; omega)]
  · rw [get_set_self (by simp; omega)]
  · intro x hx
    rw [get_set_ne (by omega), get_set_ne (by omega), get_set_ne (by omega)]

/-- `combine` writes the entry `(e, f, l)` in place of the top two, extends the follow sets, and
leaves the rest of the state. -/
theorem combine_stack {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan}
    (hsize : s.stack.size = 3 * pn) (h2 : 2 ≤ s.depth.toNat) (hd : s.depth.toNat ≤ pn)
    (e f l la nx : UInt64) :
    (combine s e f l la nx).stack.size = 3 * pn ∧
      (combine s e f l la nx).depth.toNat = s.depth.toNat - 1 ∧
      (combine s e f l la nx).stack[3 * (s.depth.toNat - 2)]! = e ∧
      (combine s e f l la nx).stack[3 * (s.depth.toNat - 2) + 1]! = f ∧
      (combine s e f l la nx).stack[3 * (s.depth.toNat - 2) + 2]! = l ∧
      (∀ x, x < 3 * (s.depth.toNat - 2) → (combine s e f l la nx).stack[x]! = s.stack[x]!) ∧
      (combine s e f l la nx).valid = s.valid ∧ (combine s e f l la nx).count = s.count ∧
      (combine s e f l la nx).skip = s.skip ∧
      (combine s e f l la nx).follow = addFollow s.follow la nx ∧
      (combine s e f l la nx).sets = s.sets := by
  have hsub : (s.depth - 2).toNat = s.depth.toNat - 2 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using h2)]; rfl
  have hi : (3 * (s.depth - 2)).toNat = 3 * (s.depth.toNat - 2) := by
    rw [UInt64.toNat_mul, hsub, show (3 : UInt64).toNat = 3 from rfl]; omega
  have hi1 : (3 * (s.depth - 2) + 1).toNat = 3 * (s.depth.toNat - 2) + 1 := by
    rw [UInt64.toNat_add, hi, UInt64.toNat_one]; omega
  have hi2 : (3 * (s.depth - 2) + 2).toNat = 3 * (s.depth.toNat - 2) + 2 := by
    rw [UInt64.toNat_add, hi, show (2 : UInt64).toNat = 2 from rfl]; omega
  simp only [combine, hi, hi1, hi2]
  refine ⟨by simp [hsize], ?_, ?_, ?_, ?_, ?_, (by first | rfl | trivial),
    (by first | rfl | trivial), (by first | rfl | trivial), (by first | rfl | trivial),
    (by first | rfl | trivial)⟩
  · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; rfl
  · rw [get_set_ne (by omega), get_set_ne (by omega), get_set_self (by omega)]
  · rw [get_set_ne (by omega), get_set_self (by simp; omega)]
  · rw [get_set_self (by simp; omega)]
  · intro x hx
    rw [get_set_ne (by omega), get_set_ne (by omega), get_set_ne (by omega)]

/-- The program's initial state holds the invariant for the empty stack. -/
theorem init_corr {pn : Nat} (hpn : 3 * pn < 2 ^ 64) :
    Corr pn ⟨true, 0, 0, 0, LeanExe.build (3 * UInt64.ofNat pn) (fun _ => 0),
      LeanExe.build 64 (fun _ => 0), LeanExe.build 256 (fun _ => 0)⟩ [] where
  valid := rfl
  skip := rfl
  depth := rfl
  count := rfl
  stackSize := by
    rw [LeanExe.Dialect.build_size, UInt64.toNat_mul, show (3 : UInt64).toNat = 3 from rfl,
      toNat_ofNat_lt (by omega : pn < 2 ^ 64) (le_refl _)]
    omega
  followSize := by rw [LeanExe.Dialect.build_size]; rfl
  setsSize := by rw [LeanExe.Dialect.build_size]; rfl
  entries := fun e h => absurd h (by simp)
  follow := fun p hp q => by
    rw [LeanExe.Dialect.build_get (by simpa using hp), bit_zero]
    simp
  sets := fun p hp1 hp _ => by simp [total] at hp; omega

/-- An entry of `es ++ [r]` is an entry of `es`, with the same offset, or `r`, at offset
`total es`. -/
theorem exists_append_single {es : List Re} {r : Re} {P : Re → Nat → Prop} :
    (∃ e, ∃ h : e < (es ++ [r]).length, P (es ++ [r])[e] (off (es ++ [r]) e)) ↔
      (∃ e, ∃ h : e < es.length, P es[e] (off es e)) ∨ P r (total es) := by
  constructor
  · rintro ⟨e, he, hp⟩
    simp only [List.length_append, List.length_singleton] at he
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · left
      refine ⟨e, he, ?_⟩
      rwa [List.getElem_append_left he, off_append he.le] at hp
    · right
      rwa [List.getElem_concat_length rfl, off_append le_rfl, off_length] at hp
  · rintro (⟨e, he, hp⟩ | hp)
    · refine ⟨e, by simp; omega, ?_⟩
      rwa [List.getElem_append_left he, off_append he.le]
    · refine ⟨es.length, by simp, ?_⟩
      rwa [List.getElem_concat_length rfl, off_append le_rfl, off_length]

/-- Pushing an expression without positions, such as `empty` or `eps`, preserves the invariant. -/
theorem push_corr {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} {es : List Re}
    (hc : Corr pn s es) (hlen : es.length < pn) (r : Re) (hpos : r.positions = 0)
    (hF : ∀ k q, ¬ First r k q) (hL : ∀ k q, ¬ Last r k q)
    (hFo : ∀ k p q, ¬ Follow r k p q) (hC : ∀ k p c, ¬ Class r k p c) :
    Corr pn (push s (if nullable r then 1 else 0) 0 0) (es ++ [r]) := by
  obtain ⟨hsize, hdepth, h0, h1, h2, hkeep, hvalid, hcount, hskip, hfollow, hsets⟩ :=
    push_stack hpn hc.stackSize (by rw [hc.depth]; exact hlen) (if nullable r then 1 else 0) 0 0
  rw [hc.depth] at hdepth h0 h1 h2 hkeep
  have htotal : total (es ++ [r]) = total es := by simp [total, hpos]
  refine ⟨by rw [hvalid, hc.valid], by rw [hskip, hc.skip], by simp [hdepth], ?_, hsize,
    by rw [hfollow, hc.followSize], by rw [hsets, hc.setsSize], ?_, ?_, ?_⟩
  · rw [hcount, hc.count, htotal]
  · intro e he
    simp only [List.length_append, List.length_singleton] at he
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · obtain ⟨he0, he1, he2⟩ := hc.entries e he
      rw [List.getElem_append_left he, off_append he.le]
      refine ⟨by rw [hkeep _ (by omega), he0], fun q => ?_, fun q => ?_⟩
      · rw [hkeep _ (by omega), he1]
      · rw [hkeep _ (by omega), he2]
    · rw [List.getElem_concat_length rfl]
      refine ⟨h0, fun q => ?_, fun q => ?_⟩
      · rw [h1, bit_zero]; simp [hF]
      · rw [h2, bit_zero]; simp [hL]
  · intro p hp q
    rw [hfollow, hc.follow p hp q, exists_append_single (P := fun r k => Follow r k p q)]
    simp [hFo]
  · intro p hp1 hp hp64 c
    rw [htotal] at hp
    rw [hsets, hc.sets p hp1 hp hp64 c, exists_append_single (P := fun r k => Class r k p c)]
    simp [hC]

/-- Word 0 pushes `empty`. -/
theorem step_empty {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} {es : List Re}
    (hc : Corr pn s es) (hlen : es.length < pn) : Corr pn (scanStep s 0) (es ++ [.empty]) := by
  have : scanStep s 0 = push s (if nullable .empty then 1 else 0) 0 0 := by
    simp [scanStep, hc.valid, hc.skip, nullable]
  rw [this]
  exact push_corr hpn hc hlen .empty rfl (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h)
    (fun _ _ _ h => h)

/-- Word 1 pushes `eps`. -/
theorem step_eps {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} {es : List Re}
    (hc : Corr pn s es) (hlen : es.length < pn) : Corr pn (scanStep s 1) (es ++ [.eps]) := by
  have : scanStep s 1 = push s (if nullable .eps then 1 else 0) 0 0 := by
    simp [scanStep, hc.valid, hc.skip, nullable]
  rw [this]
  exact push_corr hpn hc hlen .eps rfl (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h)
    (fun _ _ _ h => h)

/-- An entry of `es ++ [a, b]` is an entry of `es`, or `a` at offset `total es`, or `b` after
it. -/
theorem exists_append_pair {es : List Re} {a b : Re} {P : Re → Nat → Prop} :
    (∃ e, ∃ h : e < (es ++ [a, b]).length, P (es ++ [a, b])[e] (off (es ++ [a, b]) e)) ↔
      (∃ e, ∃ h : e < es.length, P es[e] (off es e)) ∨ P a (total es) ∨
        P b (total es + a.positions) := by
  have h := exists_append_single (es := es ++ [a]) (r := b) (P := P)
  rw [List.append_assoc, List.singleton_append] at h
  rw [h, exists_append_single (es := es) (r := a) (P := P), total_append]
  simp [total, or_assoc]

/-- Bit `q` of the entry word `if n then 1 else 0` tested against 1. -/
theorem flag_eq_one (n : Bool) : ((if n then (1 : UInt64) else 0) == 1) = n := by
  cases n <;> decide

theorem flag_and (n m : Bool) :
    ((if n then (1 : UInt64) else 0) &&& (if m then 1 else 0)) = if (n && m) then 1 else 0 := by
  cases n <;> cases m <;> decide

theorem flag_or (n m : Bool) :
    ((if n then (1 : UInt64) else 0) ||| (if m then 1 else 0)) = if (n || m) then 1 else 0 := by
  cases n <;> cases m <;> decide

/-- The indices of the top two entries of the stack. -/
theorem top_two_indices {s : Scan} {pn : Nat} (hpn : 3 * pn < 2 ^ 64) (h2 : 2 ≤ s.depth.toNat)
    (hd : s.depth.toNat ≤ pn) (j : UInt64) (hj : j.toNat < 6) :
    (3 * (s.depth - 2) + j).toNat = 3 * (s.depth.toNat - 2) + j.toNat := by
  have hsub : (s.depth - 2).toNat = s.depth.toNat - 2 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using h2)]; rfl
  rw [UInt64.toNat_add, UInt64.toNat_mul, hsub, show (3 : UInt64).toNat = 3 from rfl]
  omega

theorem top_two_index {s : Scan} {pn : Nat} (hpn : 3 * pn < 2 ^ 64) (h2 : 2 ≤ s.depth.toNat)
    (hd : s.depth.toNat ≤ pn) : (3 * (s.depth - 2)).toNat = 3 * (s.depth.toNat - 2) := by
  have hsub : (s.depth - 2).toNat = s.depth.toNat - 2 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using h2)]; rfl
  rw [UInt64.toNat_mul, hsub, show (3 : UInt64).toNat = 3 from rfl]
  omega

/-- Word 3 replaces the top two expressions `a` and `b` by `cat a b`. -/
theorem step_cat {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} {es : List Re} {a b : Re}
    (hc : Corr pn s (es ++ [a, b])) (hlen : (es ++ [a, b]).length ≤ pn) :
    Corr pn (scanStep s 3) (es ++ [.cat a b]) := by
  have hd : s.depth.toNat = es.length + 2 := by rw [hc.depth]; simp
  have h2 : 2 ≤ s.depth.toNat := by omega
  have hdp : s.depth.toNat ≤ pn := by rw [hc.depth]; exact hlen
  have hn2 : ¬ s.depth < 2 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
  have ha := hc.entries es.length (by simp)
  have hb := hc.entries (es.length + 1) (by simp)
  have hla : (es ++ [a, b])[es.length]'(by simp) = a := by simp
  have hlb : (es ++ [a, b])[es.length + 1]'(by simp) = b := by simp
  have hoa : off (es ++ [a, b]) es.length = total es := by rw [off_append le_rfl, off_length]
  have hob : off (es ++ [a, b]) (es.length + 1) = total es + a.positions := by
    rw [show es ++ [a, b] = (es ++ [a]) ++ [b] by simp, off_append (by simp),
      show es.length + 1 = (es ++ [a]).length by simp, off_length, total_append]
    simp [total]
  rw [hla, hoa] at ha
  rw [hlb, hob] at hb
  unfold EntryHolds at hb
  rw [show 3 * (es.length + 1) = 3 * es.length + 3 by omega] at hb
  obtain ⟨ea, fa, la⟩ := ha
  obtain ⟨eb, fb, lb⟩ := hb
  have hstep : scanStep s 3 = combine s
      (s.stack[3 * es.length]! &&& s.stack[3 * es.length + 3]!)
      (s.stack[3 * es.length + 1]! ||| (if s.stack[3 * es.length]! == 1
        then s.stack[3 * es.length + 4]! else 0))
      (s.stack[3 * es.length + 5]! ||| (if s.stack[3 * es.length + 3]! == 1
        then s.stack[3 * es.length + 2]! else 0))
      s.stack[3 * es.length + 2]! s.stack[3 * es.length + 4]! := by
    have i0 := top_two_index hpn h2 hdp
    have i1 : (3 * (s.depth - 2) + 1).toNat = 3 * (s.depth.toNat - 2) + 1 :=
      top_two_indices hpn h2 hdp 1 (by decide)
    have i2 : (3 * (s.depth - 2) + 2).toNat = 3 * (s.depth.toNat - 2) + 2 :=
      top_two_indices hpn h2 hdp 2 (by decide)
    have i3 : (3 * (s.depth - 2) + 3).toNat = 3 * (s.depth.toNat - 2) + 3 :=
      top_two_indices hpn h2 hdp 3 (by decide)
    have i4 : (3 * (s.depth - 2) + 4).toNat = 3 * (s.depth.toNat - 2) + 4 :=
      top_two_indices hpn h2 hdp 4 (by decide)
    have i5 : (3 * (s.depth - 2) + 5).toNat = 3 * (s.depth.toNat - 2) + 5 :=
      top_two_indices hpn h2 hdp 5 (by decide)
    simp (config := { decide := true }) only [scanStep, hc.valid, hc.skip, hn2, ↓reduceIte]
    rw [i0, i1, i2, i3, i4, i5, hd]
    simp
  rw [hstep]
  obtain ⟨hsize, hdepth, h0, h1, h2', hkeep, hvalid, hcount, hskip, hfollow, hsets⟩ :=
    combine_stack hpn hc.stackSize h2 hdp
      (s.stack[3 * es.length]! &&& s.stack[3 * es.length + 3]!)
      (s.stack[3 * es.length + 1]! ||| (if s.stack[3 * es.length]! == 1
        then s.stack[3 * es.length + 4]! else 0))
      (s.stack[3 * es.length + 5]! ||| (if s.stack[3 * es.length + 3]! == 1
        then s.stack[3 * es.length + 2]! else 0))
      s.stack[3 * es.length + 2]! s.stack[3 * es.length + 4]!
  rw [hd, show es.length + 2 - 2 = es.length by omega] at h0 h1 h2' hkeep
  rw [hd] at hdepth
  have htotal : total (es ++ [.cat a b]) = total (es ++ [a, b]) := by
    simp [total, Re.positions]
  refine ⟨by rw [hvalid, hc.valid], by rw [hskip, hc.skip], by rw [hdepth]; simp, ?_,
    hsize, by rw [hfollow]; exact (addFollow_get hc.followSize _ _).1,
    by rw [hsets, hc.setsSize], ?_, ?_, ?_⟩
  · rw [hcount, hc.count, htotal]
  · intro e he
    simp only [List.length_append, List.length_singleton] at he
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · obtain ⟨he0, he1, he2⟩ := hc.entries e (by simp; omega)
      rw [List.getElem_append_left he, off_append he.le]
      simp only [List.getElem_append_left he, off_append he.le] at he0 he1 he2
      refine ⟨by rw [hkeep _ (by omega), he0], fun q => ?_, fun q => ?_⟩
      · rw [hkeep _ (by omega), he1]
      · rw [hkeep _ (by omega), he2]
    · rw [List.getElem_concat_length rfl, off_append le_rfl, off_length]
      refine ⟨?_, fun q => ?_, fun q => ?_⟩
      · rw [h0, ea, eb, flag_and]; rfl
      · rw [h1, bit_or, ea, flag_eq_one, Bool.or_eq_true]
        cases hna : nullable a
        · simp [bit_zero, fa, First, hna]
        · simp [fa, fb, First, hna, and_or_left]
      · rw [h2', bit_or, eb, flag_eq_one, Bool.or_eq_true]
        cases hnb : nullable b
        · simp [bit_zero, lb, Last, hnb]
        · simp only [lb, la, Last, hnb, ↓reduceIte, true_and]
          constructor
          · rintro (⟨hq, h⟩ | ⟨hq, h⟩)
            · exact ⟨hq, Or.inl h⟩
            · exact ⟨hq, Or.inr h⟩
          · rintro ⟨hq, h | h⟩
            · exact Or.inl ⟨hq, h⟩
            · exact Or.inr ⟨hq, h⟩
  · intro p hp q
    rw [hfollow, addFollow_bit hc.followSize _ _ hp, hc.follow p hp q,
      exists_append_pair (P := fun r k => Follow r k p q),
      exists_append_single (P := fun r k => Follow r k p q), la, fb]
    simp only [Follow]
    constructor
    · rintro (⟨hq, h | h | h⟩ | ⟨⟨_, hl⟩, ⟨hq, hf⟩⟩)
      · exact ⟨hq, Or.inl h⟩
      · exact ⟨hq, Or.inr (Or.inl h)⟩
      · exact ⟨hq, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨hq, Or.inr (Or.inr (Or.inr ⟨hl, hf⟩))⟩
    · rintro ⟨hq, h | h | h | ⟨hl, hf⟩⟩
      · exact Or.inl ⟨hq, Or.inl h⟩
      · exact Or.inl ⟨hq, Or.inr (Or.inl h)⟩
      · exact Or.inl ⟨hq, Or.inr (Or.inr h)⟩
      · exact Or.inr ⟨⟨hp, hl⟩, ⟨hq, hf⟩⟩
  · intro p hp1 hp hp64 c
    rw [htotal] at hp
    rw [hsets, hc.sets p hp1 hp hp64 c, exists_append_pair (P := fun r k => Class r k p c),
      exists_append_single (P := fun r k => Class r k p c)]
    simp only [Class]

/-- Word 4 replaces the top two expressions `a` and `b` by `alt a b`. -/
theorem step_alt {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} {es : List Re} {a b : Re}
    (hc : Corr pn s (es ++ [a, b])) (hlen : (es ++ [a, b]).length ≤ pn) :
    Corr pn (scanStep s 4) (es ++ [.alt a b]) := by
  have hd : s.depth.toNat = es.length + 2 := by rw [hc.depth]; simp
  have h2 : 2 ≤ s.depth.toNat := by omega
  have hdp : s.depth.toNat ≤ pn := by rw [hc.depth]; exact hlen
  have hn2 : ¬ s.depth < 2 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
  have ha := hc.entries es.length (by simp)
  have hb := hc.entries (es.length + 1) (by simp)
  have hla : (es ++ [a, b])[es.length]'(by simp) = a := by simp
  have hlb : (es ++ [a, b])[es.length + 1]'(by simp) = b := by simp
  have hoa : off (es ++ [a, b]) es.length = total es := by rw [off_append le_rfl, off_length]
  have hob : off (es ++ [a, b]) (es.length + 1) = total es + a.positions := by
    rw [show es ++ [a, b] = (es ++ [a]) ++ [b] by simp, off_append (by simp),
      show es.length + 1 = (es ++ [a]).length by simp, off_length, total_append]
    simp [total]
  rw [hla, hoa] at ha
  rw [hlb, hob] at hb
  unfold EntryHolds at hb
  rw [show 3 * (es.length + 1) = 3 * es.length + 3 by omega] at hb
  obtain ⟨ea, fa, la⟩ := ha
  obtain ⟨eb, fb, lb⟩ := hb
  have hstep : scanStep s 4 = combine s
      (s.stack[3 * es.length]! ||| s.stack[3 * es.length + 3]!)
      (s.stack[3 * es.length + 1]! ||| s.stack[3 * es.length + 4]!)
      (s.stack[3 * es.length + 2]! ||| s.stack[3 * es.length + 5]!) 0 0 := by
    have i0 := top_two_index hpn h2 hdp
    have i1 : (3 * (s.depth - 2) + 1).toNat = 3 * (s.depth.toNat - 2) + 1 :=
      top_two_indices hpn h2 hdp 1 (by decide)
    have i2 : (3 * (s.depth - 2) + 2).toNat = 3 * (s.depth.toNat - 2) + 2 :=
      top_two_indices hpn h2 hdp 2 (by decide)
    have i3 : (3 * (s.depth - 2) + 3).toNat = 3 * (s.depth.toNat - 2) + 3 :=
      top_two_indices hpn h2 hdp 3 (by decide)
    have i4 : (3 * (s.depth - 2) + 4).toNat = 3 * (s.depth.toNat - 2) + 4 :=
      top_two_indices hpn h2 hdp 4 (by decide)
    have i5 : (3 * (s.depth - 2) + 5).toNat = 3 * (s.depth.toNat - 2) + 5 :=
      top_two_indices hpn h2 hdp 5 (by decide)
    simp (config := { decide := true }) only [scanStep, hc.valid, hc.skip, hn2, ↓reduceIte]
    rw [i0, i1, i2, i3, i4, i5, hd]
    simp
  rw [hstep]
  obtain ⟨hsize, hdepth, h0, h1, h2', hkeep, hvalid, hcount, hskip, hfollow, hsets⟩ :=
    combine_stack hpn hc.stackSize h2 hdp
      (s.stack[3 * es.length]! ||| s.stack[3 * es.length + 3]!)
      (s.stack[3 * es.length + 1]! ||| s.stack[3 * es.length + 4]!)
      (s.stack[3 * es.length + 2]! ||| s.stack[3 * es.length + 5]!) 0 0
  rw [hd, show es.length + 2 - 2 = es.length by omega] at h0 h1 h2' hkeep
  rw [hd] at hdepth
  have htotal : total (es ++ [.alt a b]) = total (es ++ [a, b]) := by
    simp [total, Re.positions]
  refine ⟨by rw [hvalid, hc.valid], by rw [hskip, hc.skip], by rw [hdepth]; simp, ?_,
    hsize, by rw [hfollow]; exact (addFollow_get hc.followSize _ _).1,
    by rw [hsets, hc.setsSize], ?_, ?_, ?_⟩
  · rw [hcount, hc.count, htotal]
  · intro e he
    simp only [List.length_append, List.length_singleton] at he
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · obtain ⟨he0, he1, he2⟩ := hc.entries e (by simp; omega)
      rw [List.getElem_append_left he, off_append he.le]
      simp only [List.getElem_append_left he, off_append he.le] at he0 he1 he2
      refine ⟨by rw [hkeep _ (by omega), he0], fun q => ?_, fun q => ?_⟩
      · rw [hkeep _ (by omega), he1]
      · rw [hkeep _ (by omega), he2]
    · rw [List.getElem_concat_length rfl, off_append le_rfl, off_length]
      refine ⟨?_, fun q => ?_, fun q => ?_⟩
      · rw [h0, ea, eb, flag_or]; rfl
      · rw [h1, bit_or, Bool.or_eq_true, fa, fb]
        simp only [First]
        constructor
        · rintro (⟨hq, h⟩ | ⟨hq, h⟩)
          · exact ⟨hq, Or.inl h⟩
          · exact ⟨hq, Or.inr h⟩
        · rintro ⟨hq, h | h⟩
          · exact Or.inl ⟨hq, h⟩
          · exact Or.inr ⟨hq, h⟩
      · rw [h2', bit_or, Bool.or_eq_true, la, lb]
        simp only [Last]
        constructor
        · rintro (⟨hq, h⟩ | ⟨hq, h⟩)
          · exact ⟨hq, Or.inl h⟩
          · exact ⟨hq, Or.inr h⟩
        · rintro ⟨hq, h | h⟩
          · exact Or.inl ⟨hq, h⟩
          · exact Or.inr ⟨hq, h⟩
  · intro p hp q
    rw [hfollow, addFollow_bit hc.followSize _ _ hp, hc.follow p hp q,
      exists_append_pair (P := fun r k => Follow r k p q),
      exists_append_single (P := fun r k => Follow r k p q), bit_zero]
    simp only [Follow, Bool.false_eq_true, false_and, or_false]
  · intro p hp1 hp hp64 c
    rw [htotal] at hp
    rw [hsets, hc.sets p hp1 hp hp64 c, exists_append_pair (P := fun r k => Class r k p c),
      exists_append_single (P := fun r k => Class r k p c)]
    simp only [Class]

/-- Word 5 replaces the top expression `a` by `star a`. -/
theorem step_star {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} {es : List Re} {a : Re}
    (hc : Corr pn s (es ++ [a])) (hlen : (es ++ [a]).length ≤ pn) :
    Corr pn (scanStep s 5) (es ++ [.star a]) := by
  have hd : s.depth.toNat = es.length + 1 := by rw [hc.depth]; simp
  have hdp : s.depth.toNat ≤ pn := by rw [hc.depth]; exact hlen
  have hn0 : (s.depth == 0) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj]; simp; omega
  have hsub : (s.depth - 1).toNat = es.length := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
    simp; omega
  have i0 : (3 * (s.depth - 1)).toNat = 3 * es.length := by
    rw [UInt64.toNat_mul, hsub, show (3 : UInt64).toNat = 3 from rfl]; omega
  have i1 : (3 * (s.depth - 1) + 1).toNat = 3 * es.length + 1 := by
    rw [UInt64.toNat_add, i0, UInt64.toNat_one]; omega
  have i2 : (3 * (s.depth - 1) + 2).toNat = 3 * es.length + 2 := by
    rw [UInt64.toNat_add, i0, show (2 : UInt64).toNat = 2 from rfl]; omega
  have ha := hc.entries es.length (by simp)
  rw [List.getElem_concat_length rfl, off_append le_rfl, off_length] at ha
  obtain ⟨ea, fa, la⟩ := ha
  have hstep : scanStep s 5 = { s with
      stack := s.stack.set! (3 * es.length) 1
      follow := addFollow s.follow s.stack[3 * es.length + 2]! s.stack[3 * es.length + 1]! } := by
    simp (config := { decide := true }) only [scanStep, hc.valid, hc.skip, hn0, ↓reduceIte]
    rw [i0, i1, i2]
  rw [hstep]
  have htotal : total (es ++ [.star a]) = total (es ++ [a]) := by simp [total, Re.positions]
  refine ⟨hc.valid, hc.skip, by rw [hd]; simp, by rw [hc.count, htotal], by simp [hc.stackSize],
    (addFollow_get hc.followSize _ _).1, hc.setsSize, ?_, ?_, ?_⟩
  · intro e he
    simp only [List.length_append, List.length_singleton] at he
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · obtain ⟨he0, he1, he2⟩ := hc.entries e (by simp; omega)
      simp only [List.getElem_append_left he, off_append he.le] at he0 he1 he2
      rw [List.getElem_append_left he, off_append he.le]
      refine ⟨?_, fun q => ?_, fun q => ?_⟩
      · rw [get_set_ne (by omega), he0]
      · rw [get_set_ne (by omega), he1]
      · rw [get_set_ne (by omega), he2]
    · rw [List.getElem_concat_length rfl, off_append le_rfl, off_length]
      refine ⟨?_, fun q => ?_, fun q => ?_⟩
      · rw [get_set_self (by rw [hc.stackSize]; omega)]; rfl
      · rw [get_set_ne (by omega), fa]; rfl
      · rw [get_set_ne (by omega), la]; rfl
  · intro p hp q
    rw [addFollow_bit hc.followSize _ _ hp, hc.follow p hp q,
      exists_append_single (P := fun r k => Follow r k p q),
      exists_append_single (P := fun r k => Follow r k p q), la, fa]
    simp only [Follow]
    constructor
    · rintro (⟨hq, h | h⟩ | ⟨⟨_, hl⟩, ⟨hq, hf⟩⟩)
      · exact ⟨hq, Or.inl h⟩
      · exact ⟨hq, Or.inr (Or.inl h)⟩
      · exact ⟨hq, Or.inr (Or.inr ⟨hl, hf⟩)⟩
    · rintro ⟨hq, h | h | ⟨hl, hf⟩⟩
      · exact Or.inl ⟨hq, Or.inl h⟩
      · exact Or.inl ⟨hq, Or.inr h⟩
      · exact Or.inr ⟨⟨hp, hl⟩, ⟨hq, hf⟩⟩
  · intro p hp1 hp hp64 c
    rw [htotal] at hp
    rw [hc.sets p hp1 hp hp64 c, exists_append_single (P := fun r k => Class r k p c),
      exists_append_single (P := fun r k => Class r k p c)]
    simp only [Class]

/-- Each expression's positions lie below the total of the stack. -/
theorem off_add_le {es : List Re} {e : Nat} (h : e < es.length) :
    off es e + es[e].positions ≤ total es := by
  have : off es (e + 1) = off es e + es[e].positions := by
    unfold off
    rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append,
      List.sum_append]
    simp
  have hle : off es (e + 1) ≤ total es := by
    simp only [off, total]
    exact List.Sublist.sum_le_sum ((List.take_sublist _ _).map _) (by simp)
  omega

/-- A position whose set an expression of the stack names is at most the total. -/
theorem class_le_total {es : List Re} {e p : Nat} {c : UInt8} (h : e < es.length)
    (hc : Class es[e] (off es e) p c) : p ≤ total es := by
  have := class_range hc
  have := off_add_le h
  simp only [InRange] at *
  omega

/-- The word of a set that holds byte `b`. -/
def pick (w0 w1 w2 w3 : UInt64) (j : Nat) : UInt64 :=
  match j with
  | 0 => w0
  | 1 => w1
  | 2 => w2
  | _ => w3

theorem byteSet_eq (w0 w1 w2 w3 : UInt64) (b : UInt8) :
    byteSet w0 w1 w2 w3 b = bit (pick w0 w1 w2 w3 (b.toNat / 64)) (b.toNat % 64) := by
  have hm : (b.toNat % 64).toUInt64.toNat = b.toNat % 64 := by
    have : b.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have key : ∀ w : UInt64, ((w >>> (b.toNat % 64).toUInt64) &&& 1 == 1) = bit w (b.toNat % 64) :=
    fun w => by rw [shiftRight_and_one (by rw [hm]; exact Nat.mod_lt _ (by decide)), hm]
  have hb : b.toNat < 256 := b.toNat_lt
  unfold byteSet pick
  rcases (by omega : b.toNat / 64 = 0 ∨ b.toNat / 64 = 1 ∨ b.toNat / 64 = 2 ∨ b.toNat / 64 = 3)
    with h | h | h | h <;> simp only [h, key]

/-- A word of a set is stored at its index when the set's position is below 64. -/
theorem step_word {t : Scan} {w : UInt64} (hv : t.valid = true) (hs : t.skip ≠ 0) :
    scanStep t w = { t with
      sets := if t.count ≤ 63 then t.sets.set! (4 * t.count + (4 - t.skip)).toNat w else t.sets
      skip := t.skip - 1 } := by
  simp [scanStep, hv, hs]

/-- The state `u` after `j` of the four words of a set from the state `t` that word 2 left: the
words `0` to `j - 1` are stored at `4 c` to `4 c + j - 1` when the position `c` is below 64, and
the rest of the state is `t`'s. -/
structure FillState (t u : Scan) (w0 w1 w2 w3 : UInt64) (j : Nat) : Prop where
  valid : u.valid = t.valid
  count : u.count = t.count
  depth : u.depth = t.depth
  stack : u.stack = t.stack
  follow : u.follow = t.follow
  skip : u.skip.toNat = 4 - j
  size : u.sets.size = t.sets.size
  sets : ∀ x, u.sets[x]! = if t.count ≤ 63 ∧ 4 * t.count.toNat ≤ x ∧ x < 4 * t.count.toNat + j
    then pick w0 w1 w2 w3 (x - 4 * t.count.toNat) else t.sets[x]!

theorem fill_step {t u : Scan} {w0 w1 w2 w3 : UInt64} {j : Nat} (hv : t.valid = true)
    (hsize : t.sets.size = 256) (h : FillState t u w0 w1 w2 w3 j) (hj : j < 4) :
    FillState t (scanStep u (pick w0 w1 w2 w3 j)) w0 w1 w2 w3 (j + 1) := by
  have hskip : u.skip ≠ 0 := by
    intro h0; have := h.skip; rw [h0] at this; simp at this; omega
  rw [step_word (by rw [h.valid, hv]) hskip]
  have hk : (4 - u.skip).toNat = j := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h.skip]; simp), h.skip]
    simp; omega
  refine ⟨h.valid, h.count, h.depth, h.stack, h.follow, ?_, ?_, fun x => ?_⟩
  · rw [UInt64.toNat_sub_of_le _ _
      (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_one, h.skip]; omega),
      h.skip, UInt64.toNat_one]; omega
  · dsimp only
    split <;> simp [h.size]
  · dsimp only
    rw [h.count]
    by_cases hc : t.count ≤ 63
    · have hc63 : t.count.toNat ≤ 63 := by rwa [UInt64.le_iff_toNat_le] at hc
      have hidx : (4 * t.count + (4 - u.skip)).toNat = 4 * t.count.toNat + j := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, hk, show (4 : UInt64).toNat = 4 from rfl]
        omega
      simp only [hc, ↓reduceIte, hidx]
      by_cases hx : x = 4 * t.count.toNat + j
      · subst hx
        have hsz : 4 * t.count.toNat + j < u.sets.size := by
          rw [h.size, hsize]; omega
        rw [get_set_self hsz]
        simp
      · rw [get_set_ne (Ne.symm hx), h.sets x]
        by_cases hr : 4 * t.count.toNat ≤ x ∧ x < 4 * t.count.toNat + j
        · simp [hc, hr, show x < 4 * t.count.toNat + (j + 1) by omega]
        · have : ¬ (4 * t.count.toNat ≤ x ∧ x < 4 * t.count.toNat + (j + 1)) := by omega
          simp [hc, hr, this]
    · simp only [hc, ↓reduceIte]
      rw [h.sets x]
      simp [hc]

/-- Word 2 and the four words that follow push the set of bytes that they hold. -/
theorem step_set {pn : Nat} (hpn : 3 * pn < 2 ^ 64) {s : Scan} {es : List Re}
    (hc : Corr pn s es) (hlen : es.length < pn) (htot : total es < pn) (w0 w1 w2 w3 : UInt64) :
    Corr pn ([2, w0, w1, w2, w3].foldl scanStep s) (es ++ [.cls (byteSet w0 w1 w2 w3)]) := by
  have hct : (s.count + 1).toNat = total es + 1 := by
    rw [UInt64.toNat_add, hc.count, UInt64.toNat_one]; omega
  have h1 : scanStep s 2 = push { s with count := s.count + 1, skip := 4 } 0
      (if s.count + 1 ≤ 63 then 1 <<< (s.count + 1) else 0)
      (if s.count + 1 ≤ 63 then 1 <<< (s.count + 1) else 0) := by
    simp (config := { decide := true }) only [scanStep, hc.valid, hc.skip, ↓reduceIte]
  obtain ⟨hsize, hdepth, he0, he1, he2, hkeep, hvalid, hcount, hskip, hfollow, hsets⟩ :=
    push_stack hpn (s := { s with count := s.count + 1, skip := 4 }) hc.stackSize
      (by show s.depth.toNat < pn; rw [hc.depth]; exact hlen) 0
      (if s.count + 1 ≤ 63 then 1 <<< (s.count + 1) else 0)
      (if s.count + 1 ≤ 63 then 1 <<< (s.count + 1) else 0)
  generalize ht : push { s with count := s.count + 1, skip := 4 } 0
      (if s.count + 1 ≤ 63 then 1 <<< (s.count + 1) else 0)
      (if s.count + 1 ≤ 63 then 1 <<< (s.count + 1) else 0) = t at *
  simp only at hdepth he0 he1 he2 hkeep hvalid hcount hskip hfollow hsets
  rw [hc.depth] at hdepth he0 he1 he2 hkeep
  rw [hc.valid] at hvalid
  have hts : t.sets.size = 256 := by rw [hsets, hc.setsSize]
  have f0 : FillState t t w0 w1 w2 w3 0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, by rw [hskip]; rfl, rfl, fun x => by simp⟩
  have f1 := fill_step hvalid hts f0 (by decide)
  have f2 := fill_step hvalid hts f1 (by decide)
  have f3 := fill_step hvalid hts f2 (by decide)
  have f4 := fill_step hvalid hts f3 (by decide)
  simp only [pick] at f1 f2 f3 f4
  have hfold : [2, w0, w1, w2, w3].foldl scanStep s =
      scanStep (scanStep (scanStep (scanStep t w0) w1) w2) w3 := by
    simp only [List.foldl_cons, List.foldl_nil, h1]
  rw [hfold]
  generalize scanStep (scanStep (scanStep (scanStep t w0) w1) w2) w3 = u at f4
  have hcount' : u.count.toNat = total es + 1 := by rw [f4.count, hcount, hct]
  have htotal : total (es ++ [.cls (byteSet w0 w1 w2 w3)]) = total es + 1 := by
    simp [total, Re.positions]
  refine ⟨by rw [f4.valid, hvalid],
    by have := f4.skip; simp at this; exact UInt64.toNat_inj.mp this,
    by rw [f4.depth, hdepth]; simp, by rw [hcount', htotal], by rw [f4.stack, hsize],
    by rw [f4.follow, hfollow, hc.followSize], by rw [f4.size, hsets, hc.setsSize], ?_, ?_, ?_⟩
  · intro e he
    rw [f4.stack]
    simp only [List.length_append, List.length_singleton] at he
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · obtain ⟨he0, he1, he2⟩ := hc.entries e he
      rw [List.getElem_append_left he, off_append he.le]
      refine ⟨by rw [hkeep _ (by omega), he0], fun q => ?_, fun q => ?_⟩
      · rw [hkeep _ (by omega), he1]
      · rw [hkeep _ (by omega), he2]
    · rw [List.getElem_concat_length rfl, off_append le_rfl, off_length]
      have hbits : ∀ q, bit (if s.count + 1 ≤ 63 then 1 <<< (s.count + 1) else 0) q = true ↔
          q < 64 ∧ q = total es + 1 := by
        intro q
        by_cases h63 : s.count + 1 ≤ 63
        · have : (s.count + 1).toNat ≤ 63 := by rwa [UInt64.le_iff_toNat_le] at h63
          simp only [h63, ↓reduceIte]
          rw [bit_one_shiftLeft (by omega), hct]
          constructor
          · intro h; have := beq_iff_eq.mp h; omega
          · rintro ⟨_, rfl⟩; simp
        · have : 63 < (s.count + 1).toNat := by
            rw [UInt64.le_iff_toNat_le] at h63; simpa using h63
          simp only [h63, ↓reduceIte]
          rw [bit_zero]
          constructor
          · intro h; exact absurd h Bool.false_ne_true
          · rintro ⟨hq, rfl⟩; omega
      refine ⟨by rw [he0]; rfl, fun q => ?_, fun q => ?_⟩
      · rw [he1, hbits]; simp [First]
      · rw [he2, hbits]; simp [Last]
  · intro p hp q
    rw [f4.follow, hfollow, hc.follow p hp q, exists_append_single (P := fun r k => Follow r k p q)]
    simp [Follow]
  · intro p hp1 hp hp64 c
    rw [htotal] at hp
    rw [exists_append_single (P := fun r k => Class r k p c)]
    rcases Nat.lt_or_ge p (total es + 1) with hlt | hge
    · -- An old position: its words are unchanged.
      have hold : inSet u.sets p c.toNat = inSet s.sets p c.toNat := by
        unfold inSet
        rw [f4.sets, ← hsets]
        have : ¬ (t.count ≤ 63 ∧ 4 * t.count.toNat ≤ 4 * p + c.toNat / 64 ∧
            4 * p + c.toNat / 64 < 4 * t.count.toNat + 4) := by
          rw [hcount, hct]
          have := Nat.div_lt_of_lt_mul (show c.toNat < 64 * 4 by have := c.toNat_lt; omega)
          omega
        simp only [this, ↓reduceIte]
      rw [hold, hc.sets p hp1 (by omega) hp64 c]
      simp only [Class]
      constructor
      · exact Or.inl
      · rintro (h | ⟨h, _⟩)
        · exact h
        · omega
    · -- The new position: its words are those of the set.
      have hp' : p = total es + 1 := by omega
      subst hp'
      have h63 : t.count ≤ 63 := by
        rw [UInt64.le_iff_toNat_le, hcount, hct]; simp; omega
      have hnew : inSet u.sets (total es + 1) c.toNat = byteSet w0 w1 w2 w3 c := by
        unfold inSet
        rw [f4.sets, hcount, hct, byteSet_eq]
        have hdiv : c.toNat / 64 < 4 :=
          Nat.div_lt_of_lt_mul (show c.toNat < 64 * 4 by have := c.toNat_lt; omega)
        have hin : s.count + 1 ≤ 63 ∧ 4 * (total es + 1) ≤ 4 * (total es + 1) + c.toNat / 64 ∧
            4 * (total es + 1) + c.toNat / 64 < 4 * (total es + 1) + 4 :=
          ⟨by rw [← hcount]; exact h63, by omega, by omega⟩
        simp only [hin, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
      rw [hnew]
      simp only [Class]
      constructor
      · intro h; exact Or.inr ⟨by simp, h⟩
      · rintro (⟨e, he, hce⟩ | ⟨_, h⟩)
        · have := class_le_total he hce; omega
        · exact h

/-- An invalid state stays as it is. -/
theorem invalid_fixed : ∀ (ws : List UInt64) (s : Scan), s.valid = false → ws.foldl scanStep s = s
  | [], _, _ => rfl
  | w :: ws, s, h => by
    rw [List.foldl_cons, show scanStep s w = s by simp [scanStep, h]]
    exact invalid_fixed ws s h

/-- Fewer words than the set still needs leave the state valid and still reading the set. -/
theorem skip_words : ∀ (ws : List UInt64) (u : Scan), u.valid = true → ws.length < u.skip.toNat →
    (ws.foldl scanStep u).valid = true ∧ (ws.foldl scanStep u).skip.toNat = u.skip.toNat - ws.length
  | [], _, hv, _ => ⟨hv, by simp⟩
  | w :: ws, u, hv, hl => by
    have hs : u.skip ≠ 0 := by
      intro h; rw [h] at hl; simp at hl
    rw [List.foldl_cons, step_word hv hs]
    have hl' : ws.length < (u.skip - 1).toNat := by
      rw [UInt64.toNat_sub_of_le _ _
          (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_one]; simp at hl; omega),
        UInt64.toNat_one]
      simp at hl; omega
    obtain ⟨h1, h2⟩ := skip_words ws { u with
      sets := if u.count ≤ 63 then u.sets.set! (4 * u.count + (4 - u.skip)).toNat w else u.sets
      skip := u.skip - 1 } hv hl'
    refine ⟨h1, ?_⟩
    rw [h2, UInt64.toNat_sub_of_le _ _
        (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_one]; simp at hl; omega),
      UInt64.toNat_one]
    simp; omega

/-- The program's pass follows `Spec.run`: when the run succeeds, the state holds the invariant
for the stack it builds, and when it fails, the state is invalid or still reading a set. -/
theorem scan_run {pn : Nat} (hpn : 3 * pn < 2 ^ 64) :
    ∀ (ws : List UInt64) (es : List Re) (s : Scan), Corr pn s es →
      es.length + ws.length ≤ pn → total es + ws.length ≤ pn →
      (∀ st, Spec.run ws es.reverse = some st → Corr pn (ws.foldl scanStep s) st.reverse) ∧
      (Spec.run ws es.reverse = none →
        ¬ ((ws.foldl scanStep s).valid = true ∧ (ws.foldl scanStep s).skip = 0))
  | [], es, s, hc, _, _ => by
    refine ⟨fun st h => ?_, fun h => ?_⟩
    · simp only [Spec.run, Option.some.injEq] at h
      subst h
      simpa using hc
    · simp [Spec.run] at h
  | op :: rest, es, s, hc, hl, ht => by
    simp only [List.length_cons] at hl ht
    have fail : ∀ s', scanStep s op = s' → s'.valid = false →
        ¬ (((op :: rest).foldl scanStep s).valid = true ∧
          ((op :: rest).foldl scanStep s).skip = 0) := by
      intro s' hs' hv
      rw [List.foldl_cons, hs', invalid_fixed rest s' hv, hv]
      simp
    by_cases h0 : op = 0
    · subst h0
      have htot : total (es ++ [Re.empty]) = total es := by simp [total, Re.positions]
      have ih := scan_run hpn rest (es ++ [Re.empty]) _ (step_empty hpn hc (by omega))
        (by simp; omega) (by rw [htot]; omega)
      unfold Spec.run
      simp (config := { decide := true }) only [↓reduceIte, List.foldl_cons]
      rw [show (Re.empty :: es.reverse) = (es ++ [Re.empty]).reverse by simp]
      exact ih
    by_cases h1 : op = 1
    · subst h1
      have htot : total (es ++ [Re.eps]) = total es := by simp [total, Re.positions]
      have ih := scan_run hpn rest (es ++ [Re.eps]) _ (step_eps hpn hc (by omega))
        (by simp; omega) (by rw [htot]; omega)
      unfold Spec.run
      simp (config := { decide := true }) only [↓reduceIte, List.foldl_cons]
      rw [show (Re.eps :: es.reverse) = (es ++ [Re.eps]).reverse by simp]
      exact ih
    -- The state that an invalid word or a missing operand leaves.
    have invalid : ∀ (hstep : scanStep s op = { s with valid := false }),
        ¬ (((op :: rest).foldl scanStep s).valid = true ∧
          ((op :: rest).foldl scanStep s).skip = 0) :=
      fun hstep => fail _ hstep rfl
    have hdepth := hc.depth
    by_cases h2 : op = 2
    · subst h2
      have short : ∀ ws : List UInt64, ws.length < 4 →
          ¬ ((((2 : UInt64) :: ws).foldl scanStep s).valid = true ∧
            (((2 : UInt64) :: ws).foldl scanStep s).skip = 0) := by
        intro ws hws ⟨hv, hs⟩
        rw [List.foldl_cons] at hv hs
        have h1 : (scanStep s 2).valid = true ∧ (scanStep s 2).skip = 4 := by
          simp (config := { decide := true }) [scanStep, hc.valid, hc.skip, push]
        obtain ⟨_, hs'⟩ := skip_words ws (scanStep s 2) h1.1 (by rw [h1.2]; simp; omega)
        rw [hs, h1.2] at hs'
        simp at hs'
        omega
      rcases rest with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest'⟩⟩⟩⟩
      all_goals try (unfold Spec.run; simp (config := { decide := true }) only [↓reduceIte]
                     exact ⟨fun st h => absurd h (by simp), fun _ => short _ (by simp)⟩)
      have htot : total (es ++ [Re.cls (byteSet w0 w1 w2 w3)]) = total es + 1 := by
        simp [total, Re.positions]
      simp only [List.length_cons] at hl ht
      have ih := scan_run hpn rest' (es ++ [Re.cls (byteSet w0 w1 w2 w3)]) _
        (step_set hpn hc (by omega) (by omega) w0 w1 w2 w3) (by simp; omega)
        (by rw [htot]; omega)
      unfold Spec.run
      simp (config := { decide := true }) only [↓reduceIte]
      rw [show (Re.cls (byteSet w0 w1 w2 w3) :: es.reverse) =
        (es ++ [Re.cls (byteSet w0 w1 w2 w3)]).reverse by simp]
      exact ih
    by_cases h5 : op = 5
    · subst h5
      rcases hrev : es.reverse with _ | ⟨a, r⟩
      · have hes : es = [] := by simpa using hrev
        subst hes
        unfold Spec.run
        simp (config := { decide := true }) only [↓reduceIte]
        refine ⟨fun st h => absurd h (by simp), fun _ => invalid ?_⟩
        have : s.depth = 0 := UInt64.toNat_inj.mp (by rw [hdepth]; rfl)
        simp (config := { decide := true }) [scanStep, hc.valid, hc.skip, this]
      · have hes : es = r.reverse ++ [a] := by
          rw [← List.reverse_reverse es, hrev]; simp
        subst hes
        have hstar := step_star hpn hc (by omega)
        have htot : total (r.reverse ++ [Re.star a]) = total (r.reverse ++ [a]) := by
          simp [total, Re.positions]
        have ih := scan_run hpn rest (r.reverse ++ [Re.star a]) _ hstar (by simp at hl ⊢; omega)
          (by rw [htot]; omega)
        unfold Spec.run
        simp (config := { decide := true }) only [↓reduceIte, List.foldl_cons]
        rw [show (Re.star a :: r) = (r.reverse ++ [Re.star a]).reverse by simp]
        exact ih
    by_cases h34 : op = 3 ∨ op = 4
    · rcases hrev : es.reverse with _ | ⟨b, _ | ⟨a, r⟩⟩
      · have hes : es = [] := by simpa using hrev
        subst hes
        have hd2 : s.depth < 2 := by rw [UInt64.lt_iff_toNat_lt, hdepth]; simp
        rcases h34 with rfl | rfl <;>
        · unfold Spec.run
          simp (config := { decide := true }) only [↓reduceIte]
          refine ⟨fun st h => absurd h (by simp), fun _ => invalid ?_⟩
          simp (config := { decide := true }) [scanStep, hc.valid, hc.skip, hd2]
      · have hes : es = [b] := by rw [← List.reverse_reverse es, hrev]; simp
        subst hes
        have hd2 : s.depth < 2 := by rw [UInt64.lt_iff_toNat_lt, hdepth]; simp
        rcases h34 with rfl | rfl <;>
        · unfold Spec.run
          simp (config := { decide := true }) only [↓reduceIte]
          refine ⟨fun st h => absurd h (by simp), fun _ => invalid ?_⟩
          simp (config := { decide := true }) [scanStep, hc.valid, hc.skip, hd2]
      · have hes : es = r.reverse ++ [a, b] := by
          rw [← List.reverse_reverse es, hrev]; simp
        subst hes
        rcases h34 with rfl | rfl
        · have hcat := step_cat hpn hc (by omega)
          have htot : total (r.reverse ++ [Re.cat a b]) = total (r.reverse ++ [a, b]) := by
            simp [total, Re.positions]
          have ih := scan_run hpn rest (r.reverse ++ [Re.cat a b]) _ hcat
            (by simp at hl ⊢; omega) (by rw [htot]; omega)
          unfold Spec.run
          simp (config := { decide := true }) only [↓reduceIte, List.foldl_cons]
          rw [show (Re.cat a b :: r) = (r.reverse ++ [Re.cat a b]).reverse by simp]
          exact ih
        · have halt := step_alt hpn hc (by omega)
          have htot : total (r.reverse ++ [Re.alt a b]) = total (r.reverse ++ [a, b]) := by
            simp [total, Re.positions]
          have ih := scan_run hpn rest (r.reverse ++ [Re.alt a b]) _ halt
            (by simp at hl ⊢; omega) (by rw [htot]; omega)
          unfold Spec.run
          simp (config := { decide := true }) only [↓reduceIte, List.foldl_cons]
          rw [show (Re.alt a b :: r) = (r.reverse ++ [Re.alt a b]).reverse by simp]
          exact ih
    -- Any other word is invalid.
    have h3 : op ≠ 3 := fun h => h34 (Or.inl h)
    have h4 : op ≠ 4 := fun h => h34 (Or.inr h)
    unfold Spec.run
    simp only [beq_iff_eq, h0, h1, h2, h3, h4, h5, ↓reduceIte]
    refine ⟨fun st h => absurd h (by simp), fun _ => invalid ?_⟩
    simp [scanStep, hc.valid, hc.skip, h0, h1, h2, h3, h4, h5]

#print axioms addFollow_bit
#print axioms scan_run
#print axioms step_set
#print axioms fill_step
#print axioms off_add_le
#print axioms byteSet_eq
#print axioms step_cat
#print axioms step_alt
#print axioms step_star
#print axioms step_empty
#print axioms step_eps
#print axioms init_corr
#print axioms combine_stack
#print axioms push_stack

end Library.Regex.ScanProof
