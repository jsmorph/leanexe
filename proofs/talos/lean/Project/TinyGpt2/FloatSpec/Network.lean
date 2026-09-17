import Project.TinyGpt2.FloatSpec.Primitives

namespace Project.TinyGpt2.FloatSpec.Correspondence

theorem row_project (w : Array UInt64) (offset : Nat) (x : Row) :
    row (project4 w offset x) = apply4 (matrix w offset) (row x) := by
  funext j
  fin_cases j
  · exact dot4_eq w offset x (0 : Fin 4)
  · exact dot4_eq w offset x (1 : Fin 4)
  · exact dot4_eq w offset x (2 : Fin 4)
  · exact dot4_eq w offset x (3 : Fin 4)

theorem context_project (w : Array UInt64) (offset : Nat) (x : Context) :
    context (projectContext w offset x) = fun i => apply4 (matrix w offset) (context x i) := by
  funext i; fin_cases i <;> exact row_project w offset _

theorem context_select (x : Context) (i : Fin 4) :
    row (contextRow x (positionWord i)) = context x i := by
  fin_cases i <;> rfl

theorem context_normalize (w : Array UInt64) (offset : Nat) (x : Context) :
    context ⟨norm w offset x.r0,norm w offset x.r1,norm w offset x.r2,norm w offset x.r3⟩ =
      fun i => normalize (normalization w offset) (context x i) := by
  funext i; fin_cases i <;> exact row_norm w offset _

theorem embedding_eq (w : Array UInt64) (tokens : Tokens) (i : Fin 4) :
    row (Project.TinyGpt2.embedding w (tokenWord (tokens i)) (positionWord i)) =
      FloatSpec.embedding (parameters w) tokens i := by
  simp only [Project.TinyGpt2.embedding, row_add, row_load, tokenWord_nat, positionWord_nat]
  funext j
  simp [FloatSpec.embedding, parameters, FloatSpec.add, vector, matrix, Nat.mul_comm]

theorem expanded_eq (w : Array UInt64) (x : Row) :
    wide (expandRow w x) = FloatSpec.add (apply4 (parameters w).expand (row x)) (parameters w).expandBias := by
  funext j
  have h := congrArg (fun v => Wasm.IEEE64.add v w[Layout.expandBias+j.val]!) (dot4_eq w Layout.expand x j)
  fin_cases j <;> simpa [wide, expandRow, addRows, loadRow, FloatSpec.add, apply4,
    parameters, vector, Layout.expandBias] using h

theorem contracted_eq (w : Array UInt64) (x : WideRow) :
    row (contractRow w x) = FloatSpec.add (apply8 (parameters w).contract (wide x)) (parameters w).contractBias := by
  funext j
  have h := congrArg (fun v => Wasm.IEEE64.add v w[Layout.contractBias+j.val]!) (dot8_eq w Layout.contract x j)
  fin_cases j <;> simpa [row, vector4, contractRow, addRows, loadRow, FloatSpec.add, apply8,
    parameters, vector, Layout.contractBias] using h

theorem activated_eq (x : WideRow) :
    wide ⟨activate x.low,activate x.high⟩ = fun i => FloatSpec.gelu (wide x i) := by
  funext i; fin_cases i <;> exact (gelu_eq _).symm

theorem attended_eq (last : Fin 4) (q : Row) (k v : Context) :
    row (attentionRow (positionWord last+1) q k v) = FloatSpec.attended last (row q) (context k) (context v) := by
  funext j
  fin_cases last <;> fin_cases j <;>
    simp [row, vector4, attentionRow, headProbabilities, attentionScore, weightedValue,
      FloatSpec.attended, FloatSpec.softmax, FloatSpec.dot4, sum4, context, positionWord,
      Project.SoftmaxWide.compute, Project.Softmax.rowMaximum, Project.Softmax.activeScore,
      Project.SoftmaxWide.weight, Project.Softmax.probability, Project.Softmax.total,
      FloatSpec.maximum, Project.Softmax.maximum, Affine.dot4, Affine.dot2, exp_eq]

/-- Universal bit equality: arbitrary packed parameter words, every four-byte
context and each valid position. There is no error tolerance or real reference. -/
theorem hidden_eq (w : Array UInt64) (tokens : Tokens) (last : Fin 4) :
    row (Project.TinyGpt2.hidden w (tokenWord (tokens 0)) (tokenWord (tokens 1))
      (tokenWord (tokens 2)) (tokenWord (tokens 3)) (positionWord last)) =
      FloatSpec.hidden (parameters w) tokens last := by
  let e : Context := ⟨Project.TinyGpt2.embedding w (tokenWord (tokens 0)) 0,
    Project.TinyGpt2.embedding w (tokenWord (tokens 1)) 1,
    Project.TinyGpt2.embedding w (tokenWord (tokens 2)) 2,
    Project.TinyGpt2.embedding w (tokenWord (tokens 3)) 3⟩
  have he : context e = FloatSpec.embedding (parameters w) tokens := by
    funext i; fin_cases i <;> exact embedding_eq w tokens _
  let n : Context := ⟨norm w Layout.norm1 e.r0,norm w Layout.norm1 e.r1,
    norm w Layout.norm1 e.r2,norm w Layout.norm1 e.r3⟩
  have hn : context n = fun i => normalize (parameters w).norm1 (FloatSpec.embedding (parameters w) tokens i) := by
    rw [show context n = fun i => normalize (normalization w Layout.norm1) (context e i) from context_normalize w Layout.norm1 e, he]
    rfl
  change row (norm w Layout.normFinal (addRows
    (addRows (contextRow e (positionWord last))
      (addRows (project4 w Layout.attention (attentionRow (positionWord last+1)
        (project4 w Layout.query (contextRow n (positionWord last)))
        (projectContext w Layout.key n) (projectContext w Layout.value n))) (loadRow w Layout.attentionBias)))
    (contractRow w (let a := expandRow w (norm w Layout.norm2
      (addRows (contextRow e (positionWord last))
        (addRows (project4 w Layout.attention (attentionRow (positionWord last+1)
          (project4 w Layout.query (contextRow n (positionWord last)))
          (projectContext w Layout.key n) (projectContext w Layout.value n))) (loadRow w Layout.attentionBias))))
      WideRow.mk (activate a.low) (activate a.high))))) = _
  simp only [row_norm, row_add, row_project, row_load, contracted_eq, activated_eq,
    expanded_eq, attended_eq, context_select, context_project, he, hn]
  rfl

#print axioms hidden_eq
end Project.TinyGpt2.FloatSpec.Correspondence
