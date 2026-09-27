import Project.EulerCertificate.VectorsSpec

namespace Project.EulerCertificate.Vectors
open Project.EulerCertificate.Flux (Vector)

noncomputable def listSum {α : Type} (items : List α) (term : α → Fin 4 → ℝ)
    (i : Fin 4) : ℝ := (items.map (fun item => term item i)).sum

theorem foldl_valid {α : Type} (items : List α) (term : α → Vector)
    (realTerm : α → Fin 4 → ℝ)
    (ht : ∀ item ∈ items, Valid (term item) (realTerm item))
    (acc : Vector) (x : Fin 4 → ℝ) (ha : Valid acc x) :
    Valid (items.foldl (fun a item => add a (term item)) acc)
      (fun i => x i + listSum items realTerm i) := by
  induction items generalizing acc x with
  | nil => simpa [listSum] using ha
  | cons item items ih =>
    have hs := ha.add (ht item (by simp))
    have htail := ih (fun q hq => ht q (by simp [hq]))
      (add acc (term item)) (fun i => x i + realTerm item i) hs
    simpa only [List.foldl_cons, listSum, List.map_cons, List.sum_cons, add_assoc] using htail

#print axioms foldl_valid
end Project.EulerCertificate.Vectors
