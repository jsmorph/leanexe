import Project.EulerCertificate.BoundaryFace
import Project.EulerCertificate.VectorsFold
import Project.EulerReconstructed.GridBalance

namespace Project.EulerCertificate.Boundary
open Project.EulerRiemann.Traversal (Cell Indexed asGrid)
open Project.EulerRiemann.Conservation (clamp clamp_current normalComponent)
open Project.EulerReconstructed.Conservation (lineReferenceFlux gridReferenceFlux)

theorem prefix_indices {n : Nat} (grid : Array Cell) (hg : Indexed n grid) :
    (grid.extract 0 n).toList.map Cell.index = List.range n := by
  have hsize : n ≤ grid.size := by rw [hg.1]; nlinarith
  apply List.ext_getElem
  · simp [min_eq_left hsize]
  · intro k hk hk'
    simp only [List.getElem_map, Array.getElem_toList, Array.getElem_extract,
      Nat.zero_add, List.getElem_range]
    exact hg.2 _ _

theorem prefix_index_lt {n : Nat} (grid : Array Cell) (hg : Indexed n grid)
    (cell : Cell) (hc : cell ∈ (grid.extract 0 n).toList) : cell.index < n := by
  have hm : cell.index ∈ (grid.extract 0 n).toList.map Cell.index :=
    List.mem_map.mpr ⟨cell, hc, rfl⟩
  rw [prefix_indices grid hg] at hm
  exact List.mem_range.mp hm

theorem prefix_sum {n : Nat} (hn : 0 < n) (trials : Nat) (axis : Bool)
    (grid : Array Cell) (hg : Indexed n grid) (i : Fin 4) :
    Vectors.listSum (grid.extract 0 n).toList
      (fun cell => lineReferenceFlux hn trials axis (asGrid n grid)
        (clamp hn cell.index) ∘ normalComponent axis) i =
      gridReferenceFlux hn trials axis (asGrid n grid) i := by
  let f := fun k => lineReferenceFlux hn trials axis (asGrid n grid)
    (clamp hn k) (normalComponent axis i)
  change ((grid.extract 0 n).toList.map (fun cell => f cell.index)).sum = _
  have he := List.map_map (l := (grid.extract 0 n).toList) (g := f) (f := Cell.index)
  simp only [Function.comp_def] at he
  rw [← he, prefix_indices grid hg]
  simpa only [List.toFinset_range, gridReferenceFlux, f] using
    (List.sum_toFinset f (List.nodup_range (n := n))).symm

theorem sum_valid {n : Nat} (hn : 0 < n) (trials : Nat) (axis : Bool)
    (grid : Array Cell) (hg : Indexed n grid) :
    Vectors.Valid (sum n trials axis grid) (gridReferenceFlux hn trials axis (asGrid n grid)) := by
  have ht : ∀ cell ∈ (grid.extract 0 n).toList,
      Vectors.Valid (line n trials axis grid cell.index)
        (fun i => lineReferenceFlux hn trials axis (asGrid n grid)
          (clamp hn cell.index) (normalComponent axis i)) := by
    intro cell hc
    let index : Fin n := ⟨cell.index, prefix_index_lt grid hg cell hc⟩
    rw [show clamp hn cell.index = index from clamp_current hn index]
    exact line_valid hn trials axis grid index
  have h := Vectors.foldl_valid (grid.extract 0 n).toList (line n trials axis grid ∘ Cell.index)
    (fun cell i => lineReferenceFlux hn trials axis (asGrid n grid)
      (clamp hn cell.index) (normalComponent axis i)) ht
    Vectors.zero (fun _ => 0) Vectors.zero_valid
  unfold sum
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList]
  intro i
  have hp := prefix_sum hn trials axis grid hg i
  simp only [Function.comp_def] at hp
  simpa only [Function.comp_def, zero_add, hp] using h i

#print axioms prefix_indices
#print axioms sum_valid
end Project.EulerCertificate.Boundary
