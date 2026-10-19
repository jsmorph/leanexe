import Verified.TailCompile
import Verified.Bound

namespace Verified

def TailBody.grows (flags : Flags S) : {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.grows flags
  | _, .next args => argsAny fun i => (args i).grows flags
  | _, .ite cond yes no => cond.grows flags || yes.grows flags || no.grows flags
  | _, .letE value body | _, .letPair value body => value.grows flags || body.grows flags

def tailCredits {params : List Ty} {result : Ty} (funs : Funs S)
    (targetModes : List Mode) (targetPaid : List Bool)
    (modes : List Mode) (paid : List Bool) {Γ : List Ty}
    (args : (i : Fin params.length) → Expr S Γ (params.get i)) (env : Env Γ) : Nat :=
  let g := tailSig params result targetModes
  argsSum fun i =>
    if g.paidSel targetPaid i &&
        !(callMovesAt modes (fun _ => false) (g := g) args i && (args i).paidVar paid) then
      (params.get i).credit ((args i).denote funs env)
    else 0

def TailBody.allocs (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (targetModes : List Mode) (targetPaid : List Bool) :
    {Γ : List Ty} → TailBody S params result Γ → List Mode → List Bool → Env Γ → Nat
  | _, .ret value, modes, paid, env =>
    value.allocs funs flags bounds modes paid (fun _ => false) env +
      coerceCost result (value.mode modes) .owned (value.denote funs env)
  | _, .next args, modes, paid, env =>
    let g := tailSig params result targetModes
    let all := fun i => argsAny fun j => (args j).uses i
    let kept := fun i =>
      all i && !(argsAny fun j => callMovesAt modes (fun _ => false) (g := g) args j &&
        (args j).uses i)
    (argsSum fun i =>
      if (params.get i).scalar then (args i).allocs funs flags bounds modes paid all env
      else if paramMode params targetModes i = .owned then (args i).ownedCost modes kept env
      else 0) + tailCredits (result := result) funs targetModes targetPaid modes paid args env
  | _, .ite cond yes no, modes, paid, env =>
    cond.allocs funs flags bounds modes paid (fun i => yes.uses i || no.uses i) env +
      if cond.denote funs env then yes.allocs funs flags bounds targetModes targetPaid modes paid env
      else no.allocs funs flags bounds targetModes targetPaid modes paid env
  | _, .letE value body, modes, paid, env =>
    value.allocs funs flags bounds modes paid (fun i => body.uses (i + 1)) env +
      body.allocs funs flags bounds targetModes targetPaid (value.mode modes :: modes)
        (value.paid flags modes paid (fun i => body.uses (i + 1)) :: paid)
        (.cons (value.denote funs env) env)
  | _, .letPair value body, modes, paid, env =>
    let mode := value.mode modes
    let pair := value.denote funs env
    value.allocs funs flags bounds modes paid (fun i => body.uses (i + 2)) env +
      body.allocs funs flags bounds targetModes targetPaid (mode :: mode :: modes)
        (false :: false :: paid) (.cons pair.2 (.cons pair.1 env))

def TailBody.fits (funs : Funs S) (fits : Fits S) :
    {Γ : List Ty} → TailBody S params result Γ → Env Γ → Bool
  | _, .ret value, env => value.fits funs fits env
  | _, .next args, env => argsAll fun i => (args i).fits funs fits env
  | _, .ite cond yes no, env =>
    cond.fits funs fits env &&
      if cond.denote funs env then yes.fits funs fits env else no.fits funs fits env
  | _, .letE value body, env =>
    value.fits funs fits env && body.fits funs fits (.cons (value.denote funs env) env)
  | _, .letPair value body, env =>
    let pair := value.denote funs env
    value.fits funs fits env && body.fits funs fits (.cons pair.2 (.cons pair.1 env))

theorem TailBody.fits_of_depthCalls (funs : Funs S) (fits : Fits S)
    (body : TailBody S params result Γ) :
    body.depthCalls = false → ∀ env, body.fits funs fits env = true := by
  induction body with
  | ret value => exact value.fits_of_depthCalls funs fits
  | next args =>
    intro hd env
    exact argsAll_true fun i => (args i).fits_of_depthCalls funs fits (argsAny_eq_false hd i) env
  | _ => intro hd env; simp_all [TailBody.depthCalls, TailBody.fits,
      Bool.or_eq_false_iff, Expr.fits_of_depthCalls]

def TailFunc.paidParams (func : TailFunc S) (flags : Flags S) : List Bool :=
  paramFlags func.params func.modes (func.body.grows flags)

def TailFunc.bound (func : TailFunc S) (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (state : Env func.params) : Nat :=
  let paid := func.paidParams flags
  Tail.costAt (func.body.denote funs)
    (func.body.allocs funs flags bounds func.modes paid (entryModes func.params func.modes) paid)
    (func.rank funs state + 1) state

def TailFunc.fits (func : TailFunc S) (funs : Funs S) (fits : Fits S)
    (state : Env func.params) : Bool :=
  Tail.fitsAt (func.body.denote funs) (func.body.fits funs fits) (func.rank funs state + 1) state

theorem TailFunc.bound_eq (func : TailFunc S) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (decreases : func.Decreases funs) (state : Env func.params) :
    func.bound funs flags bounds state =
      func.body.allocs funs flags bounds func.modes (func.paidParams flags)
        (entryModes func.params func.modes) (func.paidParams flags) state +
        (func.body.denote funs state).elim (func.bound funs flags bounds) (fun _ => 0) :=
  Tail.costAt_rank_eq _ _ decreases _ state

theorem TailFunc.fits_eq (func : TailFunc S) (funs : Funs S) (fits : Fits S)
    (decreases : func.Decreases funs) (state : Env func.params) :
    func.fits funs fits state = (func.body.fits funs fits state &&
      (func.body.denote funs state).elim (func.fits funs fits) (fun _ => true)) :=
  Tail.fitsAt_rank_eq _ _ decreases _ state

def TailFunc.boundAt (func : TailFunc S) (funs : Funs S) (flags : Flags S)
    (rest : Nat → Bounds S) : Nat → Env func.params → Nat
  | 0 => fun _ => 0
  | k + 1 => func.bound funs flags (rest k)

def TailFunc.fitsAt (func : TailFunc S) (funs : Funs S) (rest : Nat → Fits S) :
    Nat → Env func.params → Bool
  | 0 => fun _ => false
  | k + 1 => func.fits funs (rest k)

#print axioms TailBody.fits_of_depthCalls
#print axioms TailFunc.bound_eq
#print axioms TailFunc.fits_eq

end Verified
