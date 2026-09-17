import LeanExe.WGSL.Parse

namespace LeanExe.WGSL.Index

/-- Shared row-major access bound for A, B and C. -/
theorem linear_lt {rows stride row col : Nat} (hr : row < rows) (hc : col < stride) :
    row * stride + col < rows * stride := by
  have h := Nat.add_lt_add_left hc (row * stride)
  have hmul := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hr)
  simp only [Nat.succ_mul] at hmul
  exact Nat.lt_of_lt_of_le h hmul

/-- Two active invocations cannot name the same output element. This is an
indexing theorem; connecting it to concurrent executions is a later obligation. -/
theorem linear_injective {cols r₁ r₂ c₁ c₂ : Nat}
    (hc₁ : c₁ < cols) (hc₂ : c₂ < cols)
    (h : r₁ * cols + c₁ = r₂ * cols + c₂) : r₁ = r₂ ∧ c₁ = c₂ := by
  have hp : 0 < cols := Nat.zero_lt_of_lt hc₁
  have hd := congrArg (fun x => x / cols) h
  have hm := congrArg (fun x => x % cols) h
  have div₁ : (r₁ * cols + c₁) / cols = r₁ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hc₁]
    simp
  have div₂ : (r₂ * cols + c₂) / cols = r₂ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hc₂]
    simp
  rw [div₁, div₂] at hd
  simpa [Nat.mod_eq_of_lt hc₁, Nat.mod_eq_of_lt hc₂] using And.intro hd hm

/-- A rounded-up dispatch covers the requested extent, including partial tiles. -/
theorem ceilDiv_covers (n size : Nat) (hs : 0 < size) : n ≤ ceilDiv n size * size := by
  have hm := Nat.mod_lt (n + size - 1) hs
  have hd := Nat.mod_add_div (n + size - 1) size
  rw [Nat.mul_comm size] at hd
  unfold ceilDiv
  omega

/-- Every active coordinate has a dispatched workgroup/local-coordinate pair. -/
theorem invocation_covered {n size coordinate : Nat} (hs : 0 < size)
    (hc : coordinate < n) :
    coordinate / size < ceilDiv n size ∧ coordinate % size < size ∧
      coordinate / size * size + coordinate % size = coordinate := by
  refine ⟨(Nat.div_lt_iff_lt_mul hs).2 ?_, Nat.mod_lt _ hs, ?_⟩
  · exact Nat.lt_of_lt_of_le hc (ceilDiv_covers n size hs)
  · simpa [Nat.mul_comm] using Nat.div_add_mod coordinate size

/-- Each intermediate integer product and complete index is below the u32
modulus. Inputs to the arithmetic are separately required to be representable. -/
theorem word_index {row stride col : Nat}
    (hr : row < 4294967296) (hs : stride < 4294967296) (hc : col < 4294967296)
    (hi : row * stride + col < 4294967296) :
    (UInt32.ofNat row * UInt32.ofNat stride + UInt32.ofNat col).toNat =
      row * stride + col := by
  have hp : row * stride < 4294967296 := by omega
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat']
  change (row % 4294967296 * (stride % 4294967296) % 4294967296 +
    col % 4294967296) % 4294967296 = row * stride + col
  simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hi]

structure CellBounds (config : GemmConfig) (row col k : Nat) : Prop where
  a : row * config.inner + k < config.elementsA
  b : k * config.cols + col < config.elementsB
  c : row * config.cols + col < config.elementsC
  a_u32 : row * config.inner + k < 4294967296
  b_u32 : k * config.cols + col < 4294967296
  c_u32 : row * config.cols + col < 4294967296
  increment : k + 1 < 4294967296

theorem cell_bounds (kernel : CheckedGemm) {row col k : Nat}
    (hr : row < kernel.ast.config.rows) (hc : col < kernel.ast.config.cols)
    (hk : k < kernel.ast.config.inner) : CellBounds kernel.ast.config row col k := by
  rcases kernel.valid with ⟨_, _, _, _, _, hinner, ha, hb, hcBound, _⟩
  have a := linear_lt hr hk
  have b := linear_lt hk hc
  have c := linear_lt hr hc
  simp only [GemmConfig.elementsA, GemmConfig.elementsB, GemmConfig.elementsC] at ha hb hcBound
  exact ⟨a, b, c, by omega, by omega, by omega, by omega⟩

theorem checked_word_indices (kernel : CheckedGemm) {row col k : Nat}
    (hr : row < kernel.ast.config.rows) (hc : col < kernel.ast.config.cols)
    (hk : k < kernel.ast.config.inner) :
    (UInt32.ofNat row * UInt32.ofNat kernel.ast.config.inner + UInt32.ofNat k).toNat =
      row * kernel.ast.config.inner + k ∧
    (UInt32.ofNat k * UInt32.ofNat kernel.ast.config.cols + UInt32.ofNat col).toNat =
      k * kernel.ast.config.cols + col ∧
    (UInt32.ofNat row * UInt32.ofNat kernel.ast.config.cols + UInt32.ofNat col).toNat =
      row * kernel.ast.config.cols + col := by
  have bounds := cell_bounds kernel hr hc hk
  rcases kernel.valid with ⟨_, _, _, hm, hn, hinner, _⟩
  exact ⟨word_index (by omega) (by omega) (by omega) bounds.a_u32,
    word_index (by omega) (by omega) (by omega) bounds.b_u32,
    word_index (by omega) (by omega) (by omega) bounds.c_u32⟩

/-- The natural-number loop measure strictly decreases on every active step. -/
theorem loop_progress {inner k : Nat} (hk : k < inner) :
    inner - (k + 1) < inner - k := by omega

#print axioms linear_lt
#print axioms linear_injective
#print axioms invocation_covered
#print axioms word_index
#print axioms cell_bounds
#print axioms checked_word_indices
#print axioms loop_progress

end LeanExe.WGSL.Index
