import Project.TinyGpt2.AttentionRows

namespace Project.TinyGpt2

def embeddedContext (w : Array UInt64) (tokens : Fin 4 → UInt64) : Context :=
  ⟨embedding w (tokens 0) 0, embedding w (tokens 1) 1,
    embedding w (tokens 2) 2, embedding w (tokens 3) 3⟩

def residualRow (w : Array UInt64) (n : UInt64) (x : Row) (rows : Context) : Row :=
  let normalized := normContext w Layout.norm1 rows
  let attended := attentionRow n (project4 w Layout.query (norm w Layout.norm1 x))
    (projectContext w Layout.key normalized) (projectContext w Layout.value normalized)
  addRows x (addRows (project4 w Layout.attention attended) (loadRow w Layout.attentionBias))

def activatedRow (w : Array UInt64) (x : Row) : WideRow :=
  let expanded := expandRow w (norm w Layout.norm2 x)
  ⟨activate expanded.low, activate expanded.high⟩

theorem embeddedContext_rows (w : Array UInt64) (tokens : Fin 4 → UInt64) (i : Fin 4) :
    contextRows (embeddedContext w tokens) i = embedding w (tokens i) (UInt64.ofNat i.val) := by
  fin_cases i <;> rfl

theorem hidden_runtime_stages (w : Array UInt64) (tokens : Fin 4 → UInt64) (position : Fin 4) :
    let rows := embeddedContext w tokens
    let r1 := residualRow w (UInt64.ofNat (position.val+1)) (contextRows rows position) rows
    hidden w (tokens 0) (tokens 1) (tokens 2) (tokens 3) (UInt64.ofNat position.val) =
      norm w Layout.normFinal (addRows r1 (contractRow w (activatedRow w r1))) := by
  fin_cases position <;> rfl

end Project.TinyGpt2
