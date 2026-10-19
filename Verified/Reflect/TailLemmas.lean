import Verified.TailSource

namespace Verified.Reflect

theorem tail_ite_fixed {α β : Type} (meaning : α → β) (P : Prop) [Decidable P]
    {yes no : Sum α β} {Y N : β}
    (hy : Y = yes.elim meaning id) (hn : N = no.elim meaning id) :
    (if P then Y else N) = (if P then yes else no).elim meaning id := by
  by_cases hp : P <;> simp [hp, hy, hn]

theorem tail_dite_fixed {α β : Type} (meaning : α → β) (P : Prop) [Decidable P]
    {yes : P → Sum α β} {no : ¬P → Sum α β} {Y : P → β} {N : ¬P → β}
    (hy : ∀ h, Y h = (yes h).elim meaning id) (hn : ∀ h, N h = (no h).elim meaning id) :
    (if h : P then Y h else N h) = (if h : P then yes h else no h).elim meaning id := by
  by_cases hp : P <;> simp [hp, hy, hn]

theorem tail_let_fixed {α β γ : Type} (meaning : α → β) (value : γ)
    (body : γ → β) (step : γ → Sum α β)
    (fixed : ∀ value, body value = (step value).elim meaning id) :
    (let value := value; body value) = (let value := value; step value).elim meaning id :=
  fixed value

theorem tail_letPair_fixed {α β γ δ : Type} (meaning : α → β) (value : γ × δ)
    (body : γ → δ → β) (step : γ → δ → Sum α β)
    (fixed : ∀ first second, body first second = (step first second).elim meaning id) :
    (let (first, second) := value; body first second) =
      (let (first, second) := value; step first second).elim meaning id :=
  fixed value.1 value.2

variable {S : List Sig} {Γ params : List Ty} {result : Ty} {funs : Funs S} {env : Env Γ}

theorem tail_ret_eq {β : Type} (ψ : β → result.denote) {value : Expr S Γ result} {V : β}
    (hv : value.denote funs env = ψ V) :
    (TailBody.ret (params := params) value).denote funs env = .inr (ψ V) := by
  simp [TailBody.denote, hv]

theorem tail_next_eq {α : Type} (φ : α → Env params)
    (args : (i : Fin params.length) → Expr S Γ (params.get i)) {state : α}
    (ha : Env.ofFn (fun i => (args i).denote funs env) = φ state) :
    (TailBody.next (result := result) args).denote funs env = .inl (φ state) := by
  simp [TailBody.denote, ha]

theorem tail_ite_eq {α β : Type} (φ : α → Env params) (ψ : β → result.denote)
    {cond : Expr S Γ .bool} {yes no : TailBody S params result Γ}
    {C : Bool} {Y N : Sum α β}
    (hc : cond.denote funs env = C) (hy : yes.denote funs env = Sum.map φ ψ Y)
    (hn : no.denote funs env = Sum.map φ ψ N) :
    (TailBody.ite cond yes no).denote funs env = Sum.map φ ψ (if C then Y else N) := by
  cases C <;> simp [TailBody.denote, hc, hy, hn]

theorem tail_ite_decide_eq {α β : Type} (φ : α → Env params) (ψ : β → result.denote)
    {cond : Expr S Γ .bool} {yes no : TailBody S params result Γ}
    (P : Prop) [Decidable P] {Y N : Sum α β}
    (hc : cond.denote funs env = decide P) (hy : yes.denote funs env = Sum.map φ ψ Y)
    (hn : no.denote funs env = Sum.map φ ψ N) :
    (TailBody.ite cond yes no).denote funs env = Sum.map φ ψ (if P then Y else N) := by
  by_cases hp : P <;> simp [TailBody.denote, hc, hy, hn, hp]

theorem tail_let_eq {α β γ : Type} {t : Ty} (φ : α → Env params)
    (ψ : β → result.denote) (flatten : γ → t.denote)
    {value : Expr S Γ t} {body : TailBody S params result (t :: Γ)} {V : γ}
    (step : γ → Sum α β) (hv : value.denote funs env = flatten V)
    (hb : ∀ v, body.denote funs (.cons (flatten v) env) = Sum.map φ ψ (step v)) :
    (TailBody.letE value body).denote funs env = Sum.map φ ψ (step V) := by
  simp [TailBody.denote, hv, hb]

theorem tail_letPair_eq {α β γ δ : Type} {s t : Ty} (φ : α → Env params)
    (ψ : β → result.denote) (flattenFirst : γ → s.denote) (flattenSecond : δ → t.denote)
    {value : Expr S Γ (.pair s t)} {body : TailBody S params result (t :: s :: Γ)} {V : γ × δ}
    (step : γ → δ → Sum α β)
    (hv : value.denote funs env = (flattenFirst V.1, flattenSecond V.2))
    (hb : ∀ first second, body.denote funs (.cons (flattenSecond second)
      (.cons (flattenFirst first) env)) = Sum.map φ ψ (step first second)) :
    (TailBody.letPair value body).denote funs env = Sum.map φ ψ (step V.1 V.2) := by
  simp [TailBody.denote, hv, hb]

end Verified.Reflect
