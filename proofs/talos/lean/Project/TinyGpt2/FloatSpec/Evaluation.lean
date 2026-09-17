import Project.TinyGpt2.FloatSpec.Algorithm

/-! A finite table evaluator for the function-valued specification. Caching
changes evaluation cost only; `hidden_eq` proves equality of every output word. -/
namespace Project.TinyGpt2.FloatSpec.Evaluation

structure Table (n : Nat) (α : Type) where
  values : Array α
  size : values.size = n

def Table.get (t : Table n α) (i : Fin n) : α :=
  t.values[i.val]'(by simpa only [t.size] using i.isLt)

def cache (f : Fin n → α) : Table n α := ⟨Array.ofFn f, Array.size_ofFn⟩

@[simp] theorem cache_eq (f : Fin n → α) : (cache f).get = f := by
  funext i
  simp [cache, Table.get]

def hidden (p : Parameters) (tokens : Tokens) (last : Fin 4) : Table 4 UInt64 :=
  let embedded := cache (fun position => cache (embedding p tokens position))
  let normalized := cache (fun position => cache (normalize p.norm1 (embedded.get position).get))
  let query := cache (apply4 p.query (normalized.get last).get)
  let keys := cache (fun position => cache (apply4 p.key (normalized.get position).get))
  let values := cache (fun position => cache (apply4 p.value (normalized.get position).get))
  let attended := cache (attended last query.get (fun i => (keys.get i).get) (fun i => (values.get i).get))
  let attention := cache (add (apply4 p.attention attended.get) p.attentionBias)
  let residual1 := cache (add (embedded.get last).get attention.get)
  let normalized2 := cache (normalize p.norm2 residual1.get)
  let expanded := cache (add (apply4 p.expand normalized2.get) p.expandBias)
  let activated := cache (fun i => gelu (expanded.get i))
  let residual2 := cache (add residual1.get (add (apply8 p.contract activated.get) p.contractBias))
  cache (normalize p.normFinal residual2.get)

theorem hidden_eq (p : Parameters) (tokens : Tokens) (last : Fin 4) :
    (hidden p tokens last).get = FloatSpec.hidden p tokens last := by
  simp only [hidden, cache_eq, FloatSpec.hidden]

#print axioms hidden_eq
end Project.TinyGpt2.FloatSpec.Evaluation
