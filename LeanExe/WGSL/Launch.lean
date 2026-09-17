import LeanExe.WGSL.Dispatch

namespace LeanExe.WGSL.Dispatch

def width (config : GemmConfig) : Nat := config.dispatchX * config.workgroupX
def height (config : GemmConfig) : Nat := config.dispatchY * config.workgroupY

/-- Enumerate the complete two-dimensional dispatch, including edge padding.
The fixed list order names invocations; it does not constrain step scheduling. -/
def initial (config : GemmConfig) : List Thread :=
  (List.range (height config * width config)).map
    (fun n => ⟨n / width config, n % width config, .entry⟩)

theorem initial_invariant (s p config buffers) : Invariant s p config buffers (initial config) := by
  intro thread member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  trivial

theorem decode_injective {width a b : Nat}
    (h : (a / width, a % width) = (b / width, b % width)) : a = b := by
  have hd := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  change a / width = b / width at hd
  change a % width = b % width at hm
  have ha := Nat.div_add_mod a width
  have hb := Nat.div_add_mod b width
  rw [hd, hm] at ha
  omega

theorem initial_unique (config : GemmConfig) : ((initial config).map Thread.coordinate).Nodup := by
  simp only [initial, List.map_map, List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact List.nodup_range.imp (fun h equal => h (decode_injective equal))

theorem extent (kernel : CheckedGemm) :
    kernel.ast.config.cols ≤ width kernel.ast.config ∧
      kernel.ast.config.rows ≤ height kernel.ast.config := by
  rcases kernel.valid with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hx, hy, _⟩
  exact ⟨Index.ceilDiv_covers _ _ hx, Index.ceilDiv_covers _ _ hy⟩

theorem initial_covers (kernel : CheckedGemm) {row col : Nat}
    (hr : row < kernel.ast.config.rows) (hc : col < kernel.ast.config.cols) :
    (⟨row, col, .entry⟩ : Thread) ∈ initial kernel.ast.config := by
  have hr' := Nat.lt_of_lt_of_le hr (extent kernel).2
  have hc' := Nat.lt_of_lt_of_le hc (extent kernel).1
  have hw : 0 < width kernel.ast.config := Nat.zero_lt_of_lt hc'
  apply List.mem_map.mpr
  refine ⟨row * width kernel.ast.config + col,
    List.mem_range.mpr (Index.linear_lt hr' hc'), ?_⟩
  have div : (row * width kernel.ast.config + col) / width kernel.ast.config = row := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hc']
    simp
  have mod : (row * width kernel.ast.config + col) % width kernel.ast.config = col := by
    simp [Nat.mod_eq_of_lt hc']
  simp only [div, mod]

/-- The largest dispatched coordinate is representable by global_invocation_id
u32 components even when the last workgroup extends beyond the matrix. -/
theorem extent_u32 (kernel : CheckedGemm) :
    width kernel.ast.config < 4294967296 ∧ height kernel.ast.config < 4294967296 := by
  rcases kernel.valid with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hx, hy, _, dx, dy⟩
  have wx := Nat.mul_le_mul dx hx
  have wy := Nat.mul_le_mul dy hy
  change kernel.ast.config.dispatchX * kernel.ast.config.workgroupX < _ ∧
    kernel.ast.config.dispatchY * kernel.ast.config.workgroupY < _
  omega

theorem launch_finishes {s p c buffers} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config) (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c) :
    ∃ final, Steps (Step s p kernel.ast.config buffers) (initial kernel.ast.config) final ∧
      Finished final :=
  finishes kernel hb hc he ht (initial_invariant s p kernel.ast.config buffers)

theorem launch_safe {s p buffers final} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (run : Steps (Step s p kernel.ast.config buffers) (initial kernel.ast.config) final) :
    ∀ thread ∈ final, ∀ err, thread.state ≠ .error err := by
  have hi := (run.preserves kernel hb (initial_invariant s p kernel.ast.config buffers)).1
  intro thread member err equal
  have inv := hi thread member
  rw [equal] at inv
  exact inv

theorem reachable_unique {s p buffers final} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (run : Steps (Step s p kernel.ast.config buffers) (initial kernel.ast.config) final) :
    (final.map Thread.coordinate).Nodup := by
  rw [(run.preserves kernel hb (initial_invariant s p kernel.ast.config buffers)).2]
  exact initial_unique _

theorem reachable_writes_disjoint {s p buffers final} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (run : Steps (Step s p kernel.ast.config buffers) (initial kernel.ast.config) final) :
    final.Pairwise (fun t u => ∀ w v, t.state = .done (some w) →
      u.state = .done (some v) → w.address ≠ v.address) := by
  have hu := reachable_unique kernel hb run
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hu
  have hi := (run.preserves kernel hb (initial_invariant s p kernel.ast.config buffers)).1
  exact hu.imp_of_mem (fun ht hu different w v htw huw =>
    writes_disjoint hi ht hu htw huw different)

/-- Completion of any interleaving produces a dot-product store for every
active output coordinate. Padding has no output store, by the same invariant. -/
theorem completed_cell {s p buffers final row col} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (run : Steps (Step s p kernel.ast.config buffers) (initial kernel.ast.config) final)
    (done : Finished final) (hr : row < kernel.ast.config.rows)
    (hc : col < kernel.ast.config.cols) :
    ∃ thread ∈ final, ∃ write, thread.coordinate = (row, col) ∧
      thread.state = .done (some write) ∧ write.address = row * kernel.ast.config.cols + col ∧
      Dot s p kernel.ast.config buffers.a buffers.b row col kernel.ast.config.inner write.value := by
  obtain ⟨hi, coords⟩ := run.preserves kernel hb (initial_invariant s p kernel.ast.config buffers)
  have member : (row, col) ∈ final.map Thread.coordinate := by
    rw [coords]
    exact List.mem_map.mpr ⟨_, initial_covers kernel hr hc, rfl⟩
  obtain ⟨thread, member, coordinate⟩ := List.mem_map.mp member
  obtain ⟨write, hw⟩ := done thread member
  have inv := hi thread member
  have row_eq : thread.row = row := congrArg Prod.fst coordinate
  have col_eq : thread.col = col := congrArg Prod.snd coordinate
  rw [hw] at inv
  cases write with
  | none => exact False.elim (inv ⟨row_eq ▸ hr, col_eq ▸ hc⟩)
  | some write =>
      refine ⟨thread, member, write, coordinate, hw, ?_, ?_⟩
      · simpa only [row_eq, col_eq] using inv.2.2.1
      · simpa only [row_eq, col_eq] using inv.2.2.2

#print axioms initial_unique
#print axioms initial_covers
#print axioms extent_u32
#print axioms launch_finishes
#print axioms launch_safe
#print axioms reachable_writes_disjoint
#print axioms completed_cell

end LeanExe.WGSL.Dispatch
