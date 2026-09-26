import Project.Lidar.IntervalShader
import Project.Lidar.QueryGeometry

namespace Project.Lidar.IntervalQuery
open LeanExe.WGSL

/-- Inputs for one of the four resident beam lanes. -/
def lane (input : UInt.Input) (i : Nat) : UInt.Input := { input with direction := i }

/-- The summary sees the resident per-beam results, with the same parameters. -/
def results (kernel : UInt.Expr) (input : UInt.Input) : UInt.Input :=
  ⟨fun i => if i < 4 then kernel.eval32 (lane input i) else 0, input.params, 0⟩

def Hit (input : UInt.Input) (boxes : List Interval.RealRect) (t : ℝ) : Prop :=
  QueryGeometry.Hit input (fun i => Interval.Hits boxes (input.params 0) (input.params 1) i) t

theorem lane_bounded (input : UInt.Input) (bounded : input.Bounded 4095)
    (i : Nat) (hi : i < 4) : (lane input i).Bounded 4095 :=
  ⟨bounded.1,bounded.2.1,by dsimp [lane]; omega⟩

theorem ofRects_hit (boxes : List LeanExe.Examples.Lidar.Rect) (x y i : Nat) (t : ℝ) :
    Interval.Hits (boxes.map Interval.ofRect) x y i t ↔
      ∃ b ∈ boxes, Oblique.GeometricHit b x y i t := by
  simp [Interval.Hits, List.mem_map, Interval.ofRect_hit]

theorem kernel_first (input : UInt.Input) (bounded : input.Bounded 4095)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b)
    (inner : Bool) :
    let kernel := if inner then LidarInterval.inner else LidarInterval.outer
    let boxes := (Shader.boxes input).map
      (Interval.ofRect ∘ (if inner then LeanExe.Examples.LidarInterval.inner else LeanExe.Examples.LidarInterval.outer))
    ∀ i, i < 4 → Continuous.FirstHit
      (fun ticks => Interval.Hits boxes (input.params 0) (input.params 1) i (ticks/60))
      (input.params 2) ((results kernel input).scene i) := by
  intro kernel boxes i hi
  have hb := lane_bounded input bounded i hi
  cases inner
  · have h := IntervalShader.outer_first (lane input i) hb hi domain
    simpa [kernel, boxes, results, hi, lane, Interval.Hits, List.mem_map, Interval.ofRect_hit, Function.comp_def, Shader.boxes, Lidar.boxAt] using h
  · have h := IntervalShader.inner_first (lane input i) hb hi domain
    simpa [kernel, boxes, results, hi, lane, Interval.Hits, List.mem_map, Interval.ofRect_hit, Function.comp_def, Shader.boxes, Lidar.boxAt] using h

theorem nearest_first (input : UInt.Input) (bounded : input.Bounded 4095)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b)
    (inner : Bool) :
    let kernel := if inner then LidarInterval.inner else LidarInterval.outer
    let boxes := (Shader.boxes input).map
      (Interval.ofRect ∘ (if inner then LeanExe.Examples.LidarInterval.inner else LeanExe.Examples.LidarInterval.outer))
    Continuous.FirstHit (fun ticks => Hit input boxes (ticks/60))
      (input.params 2) (Summary.nearest (results kernel input)) := by
  let kernel := if inner then LidarInterval.inner else LidarInterval.outer
  let boxes := (Shader.boxes input).map
    (Interval.ofRect ∘ (if inner then LeanExe.Examples.LidarInterval.inner else LeanExe.Examples.LidarInterval.outer))
  exact QueryGeometry.nearest_first (results kernel input)
    (fun i ticks => Interval.Hits boxes (input.params 0) (input.params 1) i (ticks/60))
    (kernel_first input bounded domain inner)

theorem results_bounded (input : UInt.Input) (bounded : input.Bounded 4095)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b)
    (inner : Bool) :
    (results (if inner then LidarInterval.inner else LidarInterval.outer) input).Bounded 4096 := by
  refine ⟨?_,fun i => Nat.le_trans (bounded.2.1 i) (by decide),by change 0 ≤ 4096; omega⟩
  intro i
  by_cases hi : i < 4
  · have h := (kernel_first input bounded domain inner i hi).1
    have hr := bounded.2.1 2
    dsimp [results] at h ⊢
    omega
  · simp [results,hi]

theorem hit_four (input : UInt.Input) (boxes : List Interval.RealRect) (t : ℝ) :
    Hit input boxes t ↔
      (Summary.requested (input.params 3) 0 = true ∧ Interval.Hits boxes (input.params 0) (input.params 1) 0 t) ∨
      (Summary.requested (input.params 3) 1 = true ∧ Interval.Hits boxes (input.params 0) (input.params 1) 1 t) ∨
      (Summary.requested (input.params 3) 2 = true ∧ Interval.Hits boxes (input.params 0) (input.params 1) 2 t) ∨
      (Summary.requested (input.params 3) 3 = true ∧ Interval.Hits boxes (input.params 0) (input.params 1) 3 t) := by
  constructor
  · rintro ⟨i,hi,selected,hit⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp [selected,hit]
  · intro h
    rcases h with h | h | h | h
    · exact ⟨0,by decide,h⟩
    · exact ⟨1,by decide,h⟩
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩

theorem closed_hit (input : UInt.Input) (boxes : List Interval.RealRect) :
    IsClosed {t | Hit input boxes t} := by
  have closed (i : Nat) : IsClosed {t | Summary.requested (input.params 3) i = true ∧
      Interval.Hits boxes (input.params 0) (input.params 1) i t} := by
    by_cases h : Summary.requested (input.params 3) i = true
    · simpa [h] using Interval.closed_hits boxes (input.params 0) (input.params 1) i
    · simp [h]
  convert (closed 0).union ((closed 1).union ((closed 2).union (closed 3))) using 1
  ext t
  exact hit_four input boxes t

theorem hit_mono (input : UInt.Input) {small large : List Interval.RealRect}
    (enclosed : List.Forall₂ Interval.Enclosed small large) :
    ∀ t, Hit input small t → Hit input large t := by
  rintro t ⟨i,hi,selected,hit⟩
  exact ⟨i,hi,selected,Interval.hits_mono enclosed _ _ _ t hit⟩

/-- The output contract deliberately leaves the outer-hit/inner-miss case
uncertain. A certified hit includes a physical-distance error bound. -/
def Result (actual : ℝ → Prop) (range lower upper : Nat) : Prop :=
  (range < lower → ∀ t, 0 ≤ t → t ≤ (range : ℝ)/60 → ¬actual t) ∧
  (upper ≤ range → ∃ distance, Interval.First actual range distance ∧
    (lower : ℝ)/60 ≤ distance ∧ distance ≤ (upper : ℝ)/60 ∧
    |((lower : ℝ)+upper)/120-distance| ≤ ((upper : ℝ)-lower)/120)

theorem correct (input : UInt.Input) (bounded : input.Bounded 4095)
    (domain : ∀ b ∈ Shader.boxes input, LeanExe.Examples.LidarInterval.Domain b)
    (actual : List Interval.RealRect)
    (approx : List.Forall₂ Interval.Approx (Shader.boxes input) actual) :
    Result (Hit input actual) (input.params 2)
      (Summary.nearest (results LidarInterval.outer input))
      (Summary.nearest (results LidarInterval.inner input)) := by
  obtain ⟨inside,outside⟩ := Interval.scene_enclosure domain approx
  exact ⟨Interval.certified_miss _ _ _ _ (hit_mono input outside)
      (nearest_first input bounded domain false),
    Interval.certified_hit _ _ _ _ _ _ (closed_hit input actual)
      (hit_mono input inside) (hit_mono input outside)
      (nearest_first input bounded domain false) (nearest_first input bounded domain true)⟩

#print axioms correct
#print axioms results_bounded
end Project.Lidar.IntervalQuery
