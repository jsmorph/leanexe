import Project.Smalltalk.MarkMemory
import Init.Data.List.Nat.Range
import Init.Data.List.Perm

namespace Project.Smalltalk.Worklist
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.MarkMemory

theorem handles_length {cap : Nat} {nodes : List UInt64} (distinct : nodes.Nodup)
    (bounds : ∀ h ∈ nodes, Handle cap h) : nodes.length ≤ cap := by
  have subset : nodes ⊆ (List.range' 1 cap).map UInt64.ofNat := by
    intro h mem
    have hh := bounds h mem
    apply List.mem_map.mpr
    refine ⟨h.toNat, ?_, UInt64.ofNat_toNat⟩
    rw [List.mem_range'_1]
    exact ⟨hh.1, by have := hh.2; omega⟩
  have bound := distinct.length_le_of_subset subset
  simpa using bound

structure Represents (s : Array UInt64) (cap : Nat) (queue : List UInt64) : Prop where
  count : (read s 18).toNat = queue.length
  bound : queue.length ≤ cap
  words : ∀ i, i < queue.length → read s (24 + 8 * read s 14 + UInt64.ofNat i) = queue[i]!

theorem enqueue_represents {s : Array UInt64} {cap : Nat} {h : UInt64} {queue : List UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (q : Represents s cap queue) (room : queue.length < cap) :
    Represents (markReady s h) cap (queue ++ [h]) := by
  have space : (read s 18).toNat < cap := by rw [q.count]; exact room
  have capEq : read (markReady s h) 14 = read s 14 := by
    rw [markReady_register hs hh space (show (14 : UInt64).toNat < 24 by decide)]
    simp
  constructor
  · rw [markReady_register hs hh space (show (18 : UInt64).toNat < 24 by decide)]
    simp only [ite_true, List.length_append, List.length_singleton]
    rw [successor_toNat (i := read s 18) (by have := hs.2.1; omega), q.count]
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro i hi
    have ib : i ≤ queue.length := by
      have bound := hi
      simp only [List.length_append, List.length_singleton] at bound
      omega
    have iw : (UInt64.ofNat i).toNat = i :=
      UInt64.toNat_ofNat_of_lt' (by change i < 18446744073709551616; have := hs.2.1; omega)
    have wordEq : UInt64.ofNat i = read s 18 ↔ i = queue.length := by
      rw [← UInt64.toNat_inj, iw, q.count]
    rw [capEq, markReady_work hs hh space (m := UInt64.ofNat i) (by rw [iw]; omega)]
    simp only [wordEq]
    by_cases last : i = queue.length
    · subst i
      simp only [ite_true]
      rw [getElem!_pos (queue ++ [h]) queue.length hi, List.getElem_append_right (by omega)]
      simp
    · have old : i < queue.length := by omega
      simp only [last, ite_false]
      rw [q.words i old, getElem!_pos queue i old, getElem!_pos (queue ++ [h]) i hi,
        List.getElem_append_left old]

theorem enqueue_room {cap : Nat} {done queue : List UInt64} {h : UInt64}
    (distinct : (done ++ queue).Nodup) (bounds : ∀ g ∈ done ++ queue, Handle cap g)
    (hh : Handle cap h) (fresh : h ∉ done ++ queue) : queue.length < cap := by
  have unique : (h :: (done ++ queue)).Nodup := List.nodup_cons.mpr ⟨fresh, distinct⟩
  have all : ∀ g ∈ h :: (done ++ queue), Handle cap g := by
    intro g mem
    rcases List.mem_cons.mp mem with same | old
    · subst g; exact hh
    · exact bounds g old
  have bound := handles_length unique all
  simp only [List.length_cons, List.length_append] at bound
  omega

theorem pop_represents {s : Array UInt64} {cap : Nat} {queue : List UInt64} {h : UInt64}
    (hs : Shape s cap) (q : Represents s cap (queue ++ [h])) :
    Represents (write s 18 (read s 18 - 1)) cap queue := by
  have count : (read s 18).toNat = queue.length + 1 := by simpa using q.count
  have positive : (1 : UInt64) ≤ read s 18 := by
    simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat]
    omega
  constructor
  · rw [read_write_same _ _ _ (register_bound hs (show (18 : UInt64).toNat < 24 by decide)),
      UInt64.toNat_sub_of_le _ _ positive]
    simp only [UInt64.reduceToNat]
    omega
  · have bound := q.bound
    simp only [List.length_append, List.length_singleton] at bound
    omega
  · intro i hi
    have iw : (UInt64.ofNat i).toNat = i := by
      apply UInt64.toNat_ofNat_of_lt'
      change i < 18446744073709551616
      have := hs.2.1
      have := q.bound
      simp only [List.length_append, List.length_singleton] at this
      omega
    rw [read_write_other _ 18 14 _ (by decide)]
    rw [read_write_other _ 18 _ _ (Ne.symm (work_index_not_register
      (n := UInt64.ofNat i) hs (by rw [iw]; have := q.bound; simp at this; omega) (by decide)))]
    have all : i < (queue ++ [h]).length := by simp; omega
    rw [q.words i all, getElem!_pos (queue ++ [h]) i all, List.getElem_append_left hi,
      getElem!_pos queue i hi]

theorem top_word {s : Array UInt64} {cap : Nat} {queue : List UInt64} {h : UInt64}
    (hs : Shape s cap) (q : Represents s cap (queue ++ [h])) :
    read s (24 + 8 * read s 14 + read s 18 - 1) = h := by
  have count : (read s 18).toNat = queue.length + 1 := by simpa using q.count
  have bound : (read s 18).toNat ≤ cap := by rw [q.count]; exact q.bound
  have topNat := work_index_toNat hs bound
  have positive : (1 : UInt64) ≤ 24 + 8 * read s 14 + read s 18 := by
    rw [UInt64.le_iff_toNat_le, topNat]
    simp only [UInt64.reduceToNat]
    omega
  have iw : (UInt64.ofNat queue.length).toNat = queue.length := by
    apply UInt64.toNat_ofNat_of_lt'
    change queue.length < 18446744073709551616
    have := hs.2.1
    omega
  have addr : 24 + 8 * read s 14 + read s 18 - 1 = 24 + 8 * read s 14 + UInt64.ofNat queue.length := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ positive, topNat,
      work_index_toNat (n := UInt64.ofNat queue.length) hs (by rw [iw]; omega), iw]
    simp only [UInt64.reduceToNat]
    omega
  rw [addr, q.words queue.length (by simp), getElem!_pos (queue ++ [h]) queue.length (by simp),
    List.getElem_append_right (by omega)]
  simp

end Project.Smalltalk.Worklist
