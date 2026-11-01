import Library.Combinatorics.DancingLinks.BuildInit
import Library.Combinatorics.DancingLinks.Cover

/-! Adding a node at the bottom of a column, the write of step X1 for each nonzero word.
`append` performs the writes of the program for a new node `p` of item `c`, above every node of
the column, and `col_append` shows that the column of `c` then holds `insert p Q`.  The writes
touch only the words of `p`, of the header `c`, and of the column's last node, so `append_frame`
keeps every other column. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- The writes of step X1 for a new node `p` of item `c`: `TOP(p) = c`, `ULINK(p)` the old last
node, `DLINK(p) = c`, `DLINK` of the old last node and `ULINK(c)` set to `p`, and `LEN(c)` one
more. -/
def append (t : Array UInt64) (c p : Nat) : Array UInt64 :=
  (((((t.set! (3 * p) (UInt64.ofNat c)).set! (3 * p + 1) t[3 * c + 1]!).set! (3 * p + 2)
    (UInt64.ofNat c)).set! (3 * W t (3 * c + 1) + 2) (UInt64.ofNat p)).set! (3 * c + 1)
    (UInt64.ofNat p)).set! (3 * c) (t[3 * c]! + 1)

theorem append_size (t : Array UInt64) (c p : Nat) : (append t c p).size = t.size := by
  simp [append]

theorem append_get {t : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q) {p : Nat}
    (hps : 3 * p + 2 < t.size) (k : Nat) :
    (append t c p)[k]! =
      if k = 3 * c then t[3 * c]! + 1
      else if k = 3 * c + 1 then UInt64.ofNat p
      else if k = 3 * prv c Q c + 2 then UInt64.ofNat p
      else if k = 3 * p + 2 then UInt64.ofNat c
      else if k = 3 * p + 1 then t[3 * c + 1]!
      else if k = 3 * p then UInt64.ofNat c
      else t[k]! := by
  have hc := h.size c (mem_insert_self c Q)
  have hu := h.size _ (prv_mem_insert c Q c)
  unfold append
  rw [h.up c (mem_insert_self c Q)]
  rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by omega)]

theorem col_append {t : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q) {p : Nat}
    (hp : ∀ y ∈ insert c Q, y < p) (hps : 3 * p + 2 < t.size) (hts : t.size < 2 ^ 62) :
    Col (append t c p) c (insert p Q) := by
  have hp64 : p < 2 ^ 64 := by omega
  have hA := h.above
  have hget := append_get h hps
  have hpc : c < p := hp c (mem_insert_self c Q)
  have hpQ : p ∉ Q := fun hm => Nat.lt_irrefl p (hp p (mem_insert_of_mem hm))
  set u := prv c Q c with hu
  have huI : u ∈ insert c Q := prv_mem_insert c Q c
  have hup : u < p := hp u huI
  have hc64 : c < 2 ^ 64 := by omega
  have hofc : (UInt64.ofNat c).toNat = c := UInt64.toNat_ofNat_of_lt' hc64
  have hofp : (UInt64.ofNat p).toNat = p := UInt64.toNat_ofNat_of_lt' hp64
  have hcard : Q.card + 1 < 2 ^ 64 := by
    have hsub : insert c Q ⊆ range t.size := fun y hy => mem_range.mpr (by
      have := h.size y hy; omega)
    have := card_le_card hsub
    rw [card_insert_of_notMem (fun hm => Nat.lt_irrefl _ (hA _ hm)), card_range] at this
    omega
  have hAp : Above c (insert p Q) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hpc
    · exact hA y hy
  refine ⟨hAp, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [append_size]
    rcases mem_insert.mp hy with rfl | hy
    · exact h.size _ (mem_insert_self _ _)
    · rcases mem_insert.mp hy with rfl | hy
      · exact hps
      · exact h.size _ (mem_insert_of_mem hy)
  · rw [W, hget, ite_eq_left rfl, card_insert_of_notMem hpQ, UInt64.toNat_add]
    have := h.len
    rw [W] at this
    rw [this, UInt64.toNat_one]
    omega
  · intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, hofc]
    · have hqc := hA q hq
      have hqp : q < p := hp q (mem_insert_of_mem hq)
      rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ← W]
      exact h.top q hq
  · intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · -- The header: its successor changes only when the column is empty.
      by_cases hyu : y = u
      · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by rw [← hyu]),
          hofp, nxt_insert_max hA hp (mem_insert_self _ _)]
        have : nxt y Q y = y := by
          rw [show nxt y Q y = nxt y Q u by rw [hyu]]
          exact nxt_prv_head y Q
        rw [ite_eq_left this]
      · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ← W,
          h.down _ (mem_insert_self _ _), nxt_insert_max hA hp (mem_insert_self _ _)]
        have : nxt y Q y ≠ y := by
          intro he
          have := prv_nxt_head hA
          rw [he] at this
          exact hyu (by rw [hu]; exact this.symm)
        rw [ite_eq_right this]
    · rcases mem_insert.mp hy with rfl | hy
      · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left rfl, hofc, nxt_insert_max_self hp]
      · have hyc := hA y hy
        have hyp : y < p := hp y (mem_insert_of_mem hy)
        have hyI : y ∈ insert c Q := mem_insert_of_mem hy
        by_cases hyu : y = u
        · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by rw [hyu]),
            hofp, nxt_insert_max hA hp hyI]
          have : nxt c Q y = c := by rw [hyu, hu]; exact nxt_prv_head c Q
          rw [ite_eq_left this]
        · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ← W,
            h.down y hyI, nxt_insert_max hA hp hyI]
          have : nxt c Q y ≠ c := by
            intro he
            have := prv_nxt' hA hyI
            rw [he] at this
            exact hyu (by rw [hu]; exact this.symm)
          rw [ite_eq_right this]
  · intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · rw [W, hget, ite_eq_right (by omega), ite_eq_left rfl, hofp, prv_insert_max_head hp]
    · rcases mem_insert.mp hy with rfl | hy
      · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl, ← W, h.up _ (mem_insert_self _ _),
          prv_insert_max_self hp]
      · have hyc := hA y hy
        have hyp : y < p := hp y (mem_insert_of_mem hy)
        rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ← W,
          h.up y (mem_insert_of_mem hy), prv_insert_max hA hp hy]

/-- The writes of `append` touch only the words of the header, the new node, and the column's last
node. -/
theorem append_frame {t : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q) {p : Nat}
    (hps : 3 * p + 2 < t.size) (k : Nat)
    (hk : ∀ y, (y = c ∨ y = p ∨ y = prv c Q c) → ∀ r < 3, k ≠ 3 * y + r) :
    (append t c p)[k]! = t[k]! := by
  rw [append_get h hps]
  have h1 := hk c (Or.inl rfl)
  have h2 := hk p (Or.inr (Or.inl rfl))
  have h3 := hk _ (Or.inr (Or.inr rfl))
  rw [ite_eq_right (by have := h1 0 (by omega); omega), ite_eq_right (by have := h1 1 (by omega); omega),
    ite_eq_right (by have := h3 2 (by omega); omega), ite_eq_right (by have := h2 2 (by omega); omega),
    ite_eq_right (by have := h2 1 (by omega); omega), ite_eq_right (by have := h2 0 (by omega); omega)]

end Library.Combinatorics.DancingLinks
