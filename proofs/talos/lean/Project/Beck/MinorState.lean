import Project.Beck.MinorIdentity

namespace Project.Beck.MinorState

open Matrix

structure Blocks (ι : Type*) where
  leading : Matrix ι ι ℤ
  top : ι → ℕ → ℤ
  left : ℕ → ι → ℤ
  rest : ℕ → ℕ → ℤ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bordered (blocks : Blocks ι) (row col : ℕ) : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) ℤ :=
  fromBlocks blocks.leading (fun i _ => blocks.top i col)
    (fun _ j => blocks.left row j) (fun _ _ => blocks.rest row col)

def minor (blocks : Blocks ι) (row col : ℕ) : ℤ := (bordered blocks row col).det

def extend (blocks : Blocks ι) (row col : ℕ) : Blocks (ι ⊕ Fin 1) where
  leading := bordered blocks row col
  top := fun i c => Sum.elim (fun j => blocks.top j c) (fun _ => blocks.rest row c) i
  left := fun r j => Sum.elim (blocks.left r) (fun _ => blocks.rest r col) j
  rest := blocks.rest

def doubleBorder (blocks : Blocks ι) (row col otherRow otherCol : ℕ) :
    Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) ℤ :=
  fromBlocks blocks.leading
    (fun i j => blocks.top i (if j = 0 then col else otherCol))
    (fun i j => blocks.left (if i = 0 then row else otherRow) j)
    (fun i j => blocks.rest (if i = 0 then row else otherRow) (if j = 0 then col else otherCol))

def appendEquiv (ι : Type*) : (ι ⊕ Fin 1) ⊕ Fin 1 ≃ ι ⊕ Fin 2 :=
  (Equiv.sumAssoc ι (Fin 1) (Fin 1)).trans
    (Equiv.sumCongr (Equiv.refl ι) finSumFinEquiv)

omit [Fintype ι] [DecidableEq ι] in
theorem bordered_extend (blocks : Blocks ι) (row col otherRow otherCol : ℕ) :
    bordered (extend blocks row col) otherRow otherCol =
      (doubleBorder blocks row col otherRow otherCol).submatrix (appendEquiv ι) (appendEquiv ι) := by
  ext i j
  have singleton (k : Fin 1) : k = 0 := Subsingleton.elim _ _
  have first : finSumFinEquiv (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 1) = 0 := rfl
  have second : finSumFinEquiv (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1) = 1 := rfl
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    simp [bordered, extend, doubleBorder, appendEquiv, submatrix, fromBlocks,
      singleton, first, second]

theorem extend_minor (blocks : Blocks ι) (row col otherRow otherCol : ℕ) :
    minor (extend blocks row col) otherRow otherCol =
      (doubleBorder blocks row col otherRow otherCol).det := by
  rw [minor, bordered_extend, det_submatrix_equiv_self]

theorem condensation (blocks : Blocks ι) (row col otherRow otherCol : ℕ)
    (nonzero : blocks.leading.det ≠ 0) :
    blocks.leading.det * minor (extend blocks row col) otherRow otherCol =
      minor blocks row col * minor blocks otherRow otherCol -
        minor blocks otherRow col * minor blocks row otherCol := by
  rw [extend_minor]
  have identity := MinorIdentity.integer_condensation blocks.leading
    (fun i (j : Fin 2) => blocks.top i (if j = 0 then col else otherCol))
    (fun (i : Fin 2) j => blocks.left (if i = 0 then row else otherRow) j)
    (fun (i j : Fin 2) => blocks.rest (if i = 0 then row else otherRow)
      (if j = 0 then col else otherCol)) nonzero
  simpa [MinorIdentity.border, minor, bordered, doubleBorder, mul_comm] using identity

theorem divides (blocks : Blocks ι) (row col otherRow otherCol : ℕ)
    (nonzero : blocks.leading.det ≠ 0) :
    blocks.leading.det ∣ minor blocks row col * minor blocks otherRow otherCol -
      minor blocks otherRow col * minor blocks row otherCol :=
  ⟨minor (extend blocks row col) otherRow otherCol,
    (condensation blocks row col otherRow otherCol nonzero).symm⟩

def swap (blocks : Blocks ι) (first second : ℕ) : Blocks ι where
  leading := blocks.leading
  top := blocks.top
  left := fun row => blocks.left (Equiv.swap first second row)
  rest := fun row => blocks.rest (Equiv.swap first second row)

theorem swap_minor (blocks : Blocks ι) (first second row col : ℕ) :
    minor (swap blocks first second) row col = minor blocks (Equiv.swap first second row) col := rfl

def initial (matrix : ℕ → ℕ → ℤ) : Blocks (Fin 0) where
  leading := fun i => Fin.elim0 i
  top := fun i => Fin.elim0 i
  left := fun _ i => Fin.elim0 i
  rest := matrix

theorem initial_det (matrix : ℕ → ℕ → ℤ) : (initial matrix).leading.det = 1 := by
  simp [Matrix.det_isEmpty]

theorem initial_minor (matrix : ℕ → ℕ → ℤ) (row col : ℕ) :
    minor (initial matrix) row col = matrix row col := by
  let e : Fin 0 ⊕ Fin 1 ≃ Fin 1 := Equiv.emptySum (Fin 0) (Fin 1)
  have equal : bordered (initial matrix) row col =
      (Matrix.of fun (_ _ : Fin 1) => matrix row col).submatrix e e := by
    ext i j
    rcases i with i | i
    · exact Fin.elim0 i
    rcases j with j | j
    · exact Fin.elim0 j
    rfl
  rw [minor, equal, det_submatrix_equiv_self, det_fin_one]
  rfl

#print axioms condensation
#print axioms initial_minor

end Project.Beck.MinorState
