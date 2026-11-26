module

public import Demos.RandomChoice.CommandProof
public import Library.Numerics.Decimal.Int64Text.Inverse

@[expose] public section

/-! The output of the WASI command and the count of `picks_count`.  `outputOf n ws` is the text
that `main` writes for the K accepted words `ws`: the lines of their picks.  A run whose events meet
`Meets` with status 0 writes `outputOf N ws` to standard output, for the arguments N and K that it
read and the K-tuple `ws` of the first K accepted words that its passes drew (`meets_output`).
`renderSpec` is injective (`renderSpec_inj`), since the digits of a value hold no byte 10 and
determine the value.  For every K and every sequence `o` of K values in [1, N], the K-tuples of
accepted words that `main` turns into the lines of `o` are therefore those whose picks are `o`, and
`picks_count` counts them: `⌊2^64 / N⌋^K` of them (`output_count`).  No K-tuple of accepted words
gives a sequence with a value outside [1, N] (`output_count_outside`). -/

namespace Demos.RandomChoice

open LeanExe LeanExe.Wasi Library.Numerics.Decimal.Int64Text

/-- The text that `main` writes for the accepted words `ws`: the lines of their picks. -/
def outputOf (n : UInt64) {K : Nat} (ws : Fin K → UInt64) : List UInt8 :=
  (renderSpec (List.ofFn fun i => pickSpec (n, ws i)).toArray).data.data.toList

/-! ## The lines determine the values -/

/-- The bytes of the digits of `v`. -/
def digitBytes (v : UInt64) : List UInt8 := (digitWords v.toNat).map UInt64.toUInt8

theorem renderSpec_bytes (values : List UInt64) :
    (renderSpec values.toArray).data.data.toList =
      values.flatMap fun v => digitBytes v ++ [10] := by
  rw [renderSpec_toList, textWords, List.map_flatMap]
  refine congrArg (fun f => List.flatMap f values) (funext fun v => ?_)
  rw [lineWords, List.map_append, digitBytes]
  rfl

theorem digitBytes_no_newline (v : UInt64) : (10 : UInt8) ∉ digitBytes v := by
  intro h
  obtain ⟨w, hw, he⟩ := List.mem_map.mp h
  have hd := (isDigitWord_iff w).mp ((digitWords_facts v.toNat).1 w hw)
  have h10 : w.toUInt8.toNat = 10 := by rw [he]; rfl
  rw [UInt64.toNat_toUInt8] at h10
  omega

theorem digitBytes_inj {a b : UInt64} (h : digitBytes a = digitBytes b) : a = b := by
  have hwords : ∀ v : UInt64, (digitBytes v).map UInt8.toUInt64 = digitWords v.toNat := by
    intro v
    rw [digitBytes, List.map_map]
    conv_rhs => rw [← List.map_id (digitWords v.toNat)]
    apply List.map_congr_left
    intro w hw
    have hd := (isDigitWord_iff w).mp ((digitWords_facts v.toNat).1 w hw)
    apply UInt64.toNat_inj.mp
    simp only [Function.comp_apply, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, id]
    omega
  have hw : digitWords a.toNat = digitWords b.toNat := by rw [← hwords, h, hwords]
  apply UInt64.toNat_inj.mp
  rw [← (digitWords_facts a.toNat).2.1, hw, (digitWords_facts b.toNat).2.1]

/-- Two lists without the byte `c`, each followed by `c`, are equal when the lists that start with
them are. -/
theorem split_line {c : UInt8} :
    ∀ {p q r s : List UInt8}, c ∉ p → c ∉ q → p ++ c :: r = q ++ c :: s → p = q ∧ r = s
  | [], [], _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], y :: q, _, _, _, hq, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hq
  | x :: p, [], _, _, hp, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hp
  | x :: p, y :: q, r, s, hp, hq, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h1, h2⟩ := split_line (fun m => hp (List.mem_cons_of_mem _ m))
      (fun m => hq (List.mem_cons_of_mem _ m)) h
    exact ⟨by rw [h1], h2⟩

/-- The lines of two lists of values are equal only when the lists are. -/
theorem renderSpec_inj : ∀ {a b : List UInt64},
    (renderSpec a.toArray).data.data.toList = (renderSpec b.toArray).data.data.toList → a = b
  | [], [], _ => rfl
  | [], y :: b, h => by
    simp [renderSpec_bytes] at h
  | x :: a, [], h => by
    simp [renderSpec_bytes] at h
  | x :: a, y :: b, h => by
    simp only [renderSpec_bytes, List.flatMap_cons, List.append_assoc, List.singleton_append] at h
    obtain ⟨hd, hr⟩ := split_line (digitBytes_no_newline x) (digitBytes_no_newline y) h
    rw [digitBytes_inj hd,
      renderSpec_inj (a := a) (b := b) (by rw [renderSpec_bytes, renderSpec_bytes]; exact hr)]

/-! ## The count -/

/-- For every K and every sequence `o` of K values in [1, N], exactly `⌊2^64 / N⌋^K` K-tuples `ws`
of accepted words have `outputOf N ws` equal to the lines of `o`. -/
theorem output_count (n : UInt64) (K : Nat) (o : Fin K → UInt64)
    (ho : ∀ i, 1 ≤ (o i).toNat ∧ (o i).toNat ≤ n.toNat) :
    (Finset.univ.filter fun ws : Fin K → UInt64 =>
      (∀ i, accepts n (ws i) = true) ∧
        outputOf n ws = (renderSpec (List.ofFn o).toArray).data.data.toList).card =
      (2 ^ 64 / n.toNat) ^ K := by
  rw [← picks_count n K o ho]
  congr 1
  ext ws
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hacc, hout⟩
    have hfun := List.ofFn_inj.mp (renderSpec_inj hout)
    exact fun i => ⟨hacc i, congrFun hfun i⟩
  · intro h
    refine ⟨fun i => (h i).1, ?_⟩
    have hfun : (fun i => pickSpec (n, ws i)) = o := funext fun i => (h i).2
    unfold outputOf
    rw [hfun]

/-- For every sequence `o` of K values with a value outside [1, N], no K-tuple `ws` of accepted words
has `outputOf N ws` equal to the lines of `o`. -/
theorem output_count_outside (n : UInt64) (K : Nat) (o : Fin K → UInt64)
    (ho : ∃ i, ¬(1 ≤ (o i).toNat ∧ (o i).toNat ≤ n.toNat)) :
    (Finset.univ.filter fun ws : Fin K → UInt64 =>
      (∀ i, accepts n (ws i) = true) ∧
        outputOf n ws = (renderSpec (List.ofFn o).toArray).data.data.toList).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ws - ⟨hacc, hout⟩
  obtain ⟨i, hi⟩ := ho
  have hfun := List.ofFn_inj.mp (renderSpec_inj hout)
  have hpick := congrFun hfun i
  have hacc' := hacc i
  have hn : n ≠ 0 := by
    intro e
    subst e
    simp [accepts] at hacc'
  have hpos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with e | e
    · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hn
    · exact e
  have hmod : (ws i).toNat % n.toNat < n.toNat := Nat.mod_lt _ hpos
  have hlt : n.toNat < 2 ^ 64 := n.toNat_lt
  have hsz : UInt64.size = 2 ^ 64 := rfl
  simp only [pickSpec, hacc', ↓reduceIte] at hpick
  rw [← hpick, UInt64.toNat_ofNat_of_lt' (by omega)] at hi
  omega

/-! ## The text of a run -/

/-- The first K picks of the accepted words of `ws` are the picks of the K-tuple of the first K
accepted words. -/
theorem first_picks (n : UInt64) (K : Nat) (ws : List UInt64) (hK : K ≤ (accepted n ws).length) :
    ∃ chosen : Fin K → UInt64, (∀ i, accepts n (chosen i) = true) ∧
      List.ofFn chosen = (ws.filter fun w => accepts n w).take K ∧
      (renderSpec ((accepted n ws).take K).toArray).data.data.toList = outputOf n chosen := by
  have hacc : accepted n ws = (ws.filter fun w => accepts n w).map fun w => pickSpec (n, w) := by
    rw [← valuesOf_eq_accepted]
    rfl
  have hlen : K ≤ (ws.filter fun w => accepts n w).length := by
    rw [hacc, List.length_map] at hK
    exact hK
  refine ⟨fun i => (ws.filter fun w => accepts n w)[i.val]'(Nat.lt_of_lt_of_le i.isLt hlen),
    fun i => ?_, ?_, ?_⟩
  · have hmem : (ws.filter fun w => accepts n w)[i.val]'(Nat.lt_of_lt_of_le i.isLt hlen) ∈
        ws.filter fun w => accepts n w := List.getElem_mem _
    exact (List.mem_filter.mp hmem).2
  · apply List.ext_getElem
    · simp
      omega
    · intro j h1 h2
      simp
  · have hlist : (accepted n ws).take K = List.ofFn fun i : Fin K =>
        pickSpec (n, (ws.filter fun w => accepts n w)[i.val]'(Nat.lt_of_lt_of_le i.isLt hlen)) := by
      rw [hacc, ← List.map_take]
      apply List.ext_getElem
      · simp
        omega
      · intro j h1 h2
        simp
    unfold outputOf
    rw [hlist]

/-- The events of a run of `args` write nothing: they are `args_sizes_get` and `args_get`. -/
theorem args_writes {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {outcome : Outcome ArgsResult}
    (run : Exec host args world trace outcome final) :
    Verified.Shim.committedWrites 1 trace = [] := by
  have quiet : ∀ (call : Call) (sent : List Arg) (reply : Transfer (List Bytes)),
      call ≠ Call.fdWrite → Verified.Shim.eventWrites 1 (.sys call sent reply) = [] := by
    intro call sent reply ne
    cases reply <;> simp [Verified.Shim.eventWrites, ne]
  unfold args at run
  cases run with
  | sys_reject fits => exact absurd (by decide) fits
  | sys_trap =>
    rw [committedWrites_cons, quiet _ _ _ (by decide)]
    rfl
  | sys_return _ _ next =>
    beta_reduce at next
    rw [committedWrites_cons, quiet _ _ _ (by decide), List.nil_append]
    split at next
    · cases next
      rfl
    · split at next
      · cases next
        rfl
      · cases next with
        | sys_reject fits => exact absurd (by decide) fits
        | sys_trap =>
          rw [committedWrites_cons, quiet _ _ _ (by decide)]
          rfl
        | sys_return _ _ next =>
          beta_reduce at next
          rw [committedWrites_cons, quiet _ _ _ (by decide), List.nil_append]
          split at next <;> cases next <;> rfl

/-- A run whose events meet `Meets` with status 0 read the arguments N and K, both nonzero, with
`args`, and its events wrote `outputOf N chosen` to standard output for the K-tuple `chosen` of the
first K accepted words that its passes drew. -/
theorem meets_output {World : Type} {host : Host World} {world : World} {events : List Event}
    (meets : Meets host world events 0) :
    ∃ (a : ArgsResult) (pre rest : List Event) (middle : World) (bytes : List UInt8)
      (chosen : Fin (parseSpec (a.bytes, 2)).toNat → UInt64),
      events = pre ++ rest ∧ Exec host args world pre (.returned a) middle ∧ a.errno = 0 ∧
      parseSpec (a.bytes, 1) ≠ 0 ∧ parseSpec (a.bytes, 2) ≠ 0 ∧
      Rounds (parseSpec (a.bytes, 1)) (parseSpec (a.bytes, 2))
        (passes (parseSpec (a.bytes, 2))).toNat rest bytes 0 ∧
      (∀ i, accepts (parseSpec (a.bytes, 1)) (chosen i) = true) ∧
      List.ofFn chosen = ((RandomHistogram.words bytes).filter fun w =>
        accepts (parseSpec (a.bytes, 1)) w).take (parseSpec (a.bytes, 2)).toNat ∧
      Verified.Shim.committedWrites 1 events = outputOf (parseSpec (a.bytes, 1)) chosen := by
  obtain ⟨a, pre, rest, middle, hevents, hargs, herrno, hrefused, hruns⟩ := meets
  have hz : a.errno = 0 := by
    by_contra h
    exact h (herrno h).1.symm
  have hn : parseSpec (a.bytes, 1) ≠ 0 := fun e => absurd (hrefused hz (.inl e)).1 (by decide)
  have hk : parseSpec (a.bytes, 2) ≠ 0 := fun e => absurd (hrefused hz (.inr e)).1 (by decide)
  obtain ⟨bytes, rounds, hzero, -⟩ := hruns hz hn hk
  obtain ⟨hwritten, hle⟩ := hzero rfl
  obtain ⟨chosen, hacc, hfirst, htext⟩ := first_picks _ _ _ hle
  refine ⟨a, pre, rest, middle, bytes, chosen, hevents, hargs, hz, hn, hk, rounds, hacc, hfirst, ?_⟩
  rw [hevents, committedWrites_append, args_writes hargs, List.nil_append]
  exact hwritten.trans htext

end Demos.RandomChoice
