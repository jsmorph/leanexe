module

public import Demos.Scheme.Corpus
public import Demos.Scheme.Semantics.Outcome

@[expose] public section

/-! The reference semantics gives every program of the corpus its expected outcome, by the
kernel's evaluation of each run for at most 20,000 rules.  The kernel keeps every reduction of a
declaration until it finishes the declaration, so the check takes the corpus in chunks of ten
programs, one declaration each, which keeps its memory near a tenth of a check of the whole
corpus. -/

namespace Demos.Scheme.Semantics.CorpusCheck

open Demos.Scheme.Corpus Demos.Scheme.Semantics Numeric

/-- The reference semantics meets the case: its run ends within `n` rules with the expected
bytes. -/
def meets (n : Nat) (c : Case) : Bool := outcome fixnum n (bytes c.src) == some c.expected

/-- The `k`-th chunk of ten programs of the corpus. -/
def chunk (k : Nat) : List Case := (Corpus.all.drop (10 * k)).take 10

set_option maxRecDepth 20000 in
theorem chunks_cover : Corpus.all = (List.range 11).flatMap chunk := rfl

theorem chunk_0 : (chunk 0).all (meets 20000) = true := by decide +kernel
theorem chunk_1 : (chunk 1).all (meets 20000) = true := by decide +kernel
theorem chunk_2 : (chunk 2).all (meets 20000) = true := by decide +kernel
theorem chunk_3 : (chunk 3).all (meets 20000) = true := by decide +kernel
theorem chunk_4 : (chunk 4).all (meets 20000) = true := by decide +kernel
theorem chunk_5 : (chunk 5).all (meets 20000) = true := by decide +kernel
theorem chunk_6 : (chunk 6).all (meets 20000) = true := by decide +kernel
theorem chunk_7 : (chunk 7).all (meets 20000) = true := by decide +kernel
theorem chunk_8 : (chunk 8).all (meets 20000) = true := by decide +kernel
theorem chunk_9 : (chunk 9).all (meets 20000) = true := by decide +kernel
theorem chunk_10 : (chunk 10).all (meets 20000) = true := by decide +kernel

theorem corpus_outcomes : ∀ c ∈ Corpus.all, meets 20000 c = true := by
  intro c hc
  rw [chunks_cover, List.mem_flatMap] at hc
  obtain ⟨k, hk, hc⟩ := hc
  match k, List.mem_range.mp hk with
  | 0, _ => exact List.all_eq_true.mp chunk_0 c hc
  | 1, _ => exact List.all_eq_true.mp chunk_1 c hc
  | 2, _ => exact List.all_eq_true.mp chunk_2 c hc
  | 3, _ => exact List.all_eq_true.mp chunk_3 c hc
  | 4, _ => exact List.all_eq_true.mp chunk_4 c hc
  | 5, _ => exact List.all_eq_true.mp chunk_5 c hc
  | 6, _ => exact List.all_eq_true.mp chunk_6 c hc
  | 7, _ => exact List.all_eq_true.mp chunk_7 c hc
  | 8, _ => exact List.all_eq_true.mp chunk_8 c hc
  | 9, _ => exact List.all_eq_true.mp chunk_9 c hc
  | 10, _ => exact List.all_eq_true.mp chunk_10 c hc
  | _ + 11, h => omega

#print axioms corpus_outcomes

end Demos.Scheme.Semantics.CorpusCheck
