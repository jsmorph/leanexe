import LeanExe.WGSL.Accumulate

namespace LeanExe.WGSL.Dot

/-- A dot product observes only the input coordinates used by its prefix. -/
theorem congr_buffers {s p config a b row col k result}
    (h : Dot s p config a b row col k result) (a' b' : WordBuffer)
    (ha : ∀ i, i < k → a (row*config.inner+i) = a' (row*config.inner+i))
    (hb : ∀ i, i < k → b (i*config.cols+col) = b' (i*config.cols+col)) :
    Dot s p config a' b' row col k result := by
  induction h with
  | zero => exact .zero
  | @next k acc result previous update ih =>
      apply Dot.next (ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)))
      simpa only [ha k (by omega), hb k (by omega)] using update

#print axioms congr_buffers
end LeanExe.WGSL.Dot
