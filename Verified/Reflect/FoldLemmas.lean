import Verified.Reflect.BoundLemmas
import Verified.Reflect.FitsLemmas
import Verified.ArrayFold

namespace Verified

theorem nat_fold_map (n : Nat) (φ : α → β)
    (f : (i : Nat) → i < n → α → α) (g : (i : Nat) → i < n → β → β)
    (init : α) (h : ∀ i hi a, g i hi (φ a) = φ (f i hi a)) :
    Nat.fold n g (φ init) = φ (Nat.fold n f init) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ih _ _ (fun i hi a => h i (by omega) a)]
    exact h _ _ _

theorem loopCost_eq_fold {α : Type} (cost : UInt64 → α → Nat)
    (step : UInt64 → α → α) (n : Nat) (i : UInt64) (s : α) (spent : Nat) :
    spent + loopCost (fun _ => 0) (fun _ => true) cost step n i s =
      (Nat.fold n (fun k _ (state : Nat × α) =>
        (state.1 + cost (i + UInt64.ofNat k) state.2,
          step (i + UInt64.ofNat k) state.2)) (spent, s)).1 := by
  induction n generalizing i s spent with
  | zero => simp [loopCost]
  | succ n ih =>
    have hf := Nat.fold_add (n := 1) (m := n)
      (fun k _ (state : Nat × α) =>
        (state.1 + cost (i + UInt64.ofNat k) state.2,
          step (i + UInt64.ofNat k) state.2)) (spent, s)
    rw [show n + 1 = 1 + n by omega, hf]
    simpa [Nat.one_add, loopCost, Nat.fold_succ, UInt64.ofNat_add, UInt64.add_assoc,
      UInt64.add_comm, Nat.add_assoc]
      using ih (i + 1) (step i s) (spent + cost i s)

/-- The allocation charge along a word-counted array fold, before the initial state's copy and
credit.  The natural index occurs only in this bound calculation. -/
def foldCost (xs : Array α) (init : β) (step : β → α → β)
    (cost : UInt64 → β → α → Nat) : Nat :=
  (Nat.fold xs.size.toUInt64.toNat (fun k hk (state : Nat × β) =>
    let value := xs[k]'(hk.trans_le (by exact Nat.mod_le _ _))
    (state.1 + cost (UInt64.ofNat k) state.2 value, step state.2 value)) (0, init)).1

theorem foldCost_zero (xs : Array α) (init : β) (step : β → α → β) :
    foldCost xs init step (fun _ _ _ => 0) = 0 := by
  have h := nat_fold_map xs.size.toUInt64.toNat (fun s : β => ((0 : Nat), s))
    (fun k hk s => step s (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _))))
    (fun k hk (state : Nat × β) =>
      (state.1 + 0, step state.2 (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _)))))
    init (by intro k hk s; rfl)
  exact congrArg Prod.fst h

theorem foldCost_eq_loop (xs : Array α) (init : β) (step : β → α → β)
    (cost : UInt64 → β → α → Nat) (φ : β → γ)
    (body : UInt64 → γ → γ) (charge : UInt64 → γ → Nat)
    (hb : ∀ k (hk : k < xs.size.toUInt64.toNat) s,
      body (UInt64.ofNat k) (φ s) =
        φ (step s (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _)))))
    (hc : ∀ k (hk : k < xs.size.toUInt64.toNat) s,
      charge (UInt64.ofNat k) (φ s) =
        cost (UInt64.ofNat k) s (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _)))) :
    loopCost (fun _ => 0) (fun _ => true) charge body xs.size.toUInt64.toNat 0 (φ init) =
      foldCost xs init step cost := by
  rw [← Nat.zero_add (loopCost ..), loopCost_eq_fold]
  have h := nat_fold_map xs.size.toUInt64.toNat
    (fun state : Nat × β => (state.1, φ state.2))
    (fun k hk (state : Nat × β) =>
      let value := xs[k]'(hk.trans_le (by exact Nat.mod_le _ _))
      (state.1 + cost (UInt64.ofNat k) state.2 value, step state.2 value))
    (fun k _ (state : Nat × γ) =>
      (state.1 + charge (0 + UInt64.ofNat k) state.2,
        body (0 + UInt64.ofNat k) state.2)) (0, init)
    (by intro k hk state; simp only [UInt64.zero_add, hb k hk, hc k hk])
  exact congrArg Prod.fst h

theorem loopFits_eq_fold {α : Type} (fits : UInt64 → α → Bool)
    (step : UInt64 → α → α) (n : Nat) (i : UInt64) (s : α) (valid : Bool) :
    (valid && loopFits (fun _ => true) (fun _ => true) fits step n i s) =
      (Nat.fold n (fun k _ (state : Bool × α) =>
        (state.1 && fits (i + UInt64.ofNat k) state.2,
          step (i + UInt64.ofNat k) state.2)) (valid, s)).1 := by
  induction n generalizing i s valid with
  | zero => simp [loopFits]
  | succ n ih =>
    have hf := Nat.fold_add (n := 1) (m := n)
      (fun k _ (state : Bool × α) =>
        (state.1 && fits (i + UInt64.ofNat k) state.2,
          step (i + UInt64.ofNat k) state.2)) (valid, s)
    rw [show n + 1 = 1 + n by omega, hf]
    simpa [Nat.one_add, loopFits, Nat.fold_succ, UInt64.ofNat_add, UInt64.add_assoc,
      UInt64.add_comm, Bool.and_assoc]
      using ih (i + 1) (step i s) (valid && fits i s)

def foldFits (xs : Array α) (init : β) (step : β → α → β)
    (fits : UInt64 → β → α → Bool) : Bool :=
  (Nat.fold xs.size.toUInt64.toNat (fun k hk (state : Bool × β) =>
    let value := xs[k]'(hk.trans_le (by exact Nat.mod_le _ _))
    (state.1 && fits (UInt64.ofNat k) state.2 value, step state.2 value)) (true, init)).1

theorem foldFits_true (xs : Array α) (init : β) (step : β → α → β) :
    foldFits xs init step (fun _ _ _ => true) = true := by
  have h := nat_fold_map xs.size.toUInt64.toNat (fun s : β => (true, s))
    (fun k hk s => step s (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _))))
    (fun k hk (state : Bool × β) =>
      (state.1 && true, step state.2 (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _)))))
    init (by intro k hk s; rfl)
  exact congrArg Prod.fst h

theorem foldFits_eq_loop (xs : Array α) (init : β) (step : β → α → β)
    (fits : UInt64 → β → α → Bool) (φ : β → γ)
    (body : UInt64 → γ → γ) (valid : UInt64 → γ → Bool)
    (hb : ∀ k (hk : k < xs.size.toUInt64.toNat) s,
      body (UInt64.ofNat k) (φ s) =
        φ (step s (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _)))))
    (hf : ∀ k (hk : k < xs.size.toUInt64.toNat) s,
      valid (UInt64.ofNat k) (φ s) =
        fits (UInt64.ofNat k) s (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _)))) :
    loopFits (fun _ => true) (fun _ => true) valid body xs.size.toUInt64.toNat 0 (φ init) =
      foldFits xs init step fits := by
  rw [← Bool.true_and (loopFits ..), loopFits_eq_fold]
  have h := nat_fold_map xs.size.toUInt64.toNat
    (fun state : Bool × β => (state.1, φ state.2))
    (fun k hk (state : Bool × β) =>
      let value := xs[k]'(hk.trans_le (by exact Nat.mod_le _ _))
      (state.1 && fits (UInt64.ofNat k) state.2 value, step state.2 value))
    (fun k _ (state : Bool × γ) =>
      (state.1 && valid (0 + UInt64.ofNat k) state.2,
        body (0 + UInt64.ofNat k) state.2)) (true, init)
    (by intro k hk state; simp only [UInt64.zero_add, hb k hk, hf k hk])
  exact congrArg Prod.fst h

end Verified

namespace Verified.Reflect

variable {S : List Sig} {Γ : List Ty} {funs : Funs S} {flags : Flags S}
  {bounds : Bounds S} {modes : List Mode} {paid : List Bool} {live : Nat → Bool} {env : Env Γ}

/-- The bound of a fold with the state's flag `ps`, as `loopAllocWith` states it. -/
theorem fold_flat_with {e : Elem} {t : Ty} {α β : Type} (φ : β → t.denote)
    (ψ : α → e.denote) (xs : Array α) (I : β) (F : β → α → β)
    {x : Var Γ (.array e)} {init : Expr S Γ t}
    {body : Expr S (.elem e :: t :: .word :: Γ) t}
    {all : Nat → Bool} {M : Mode} (ps : Bool) {IA KA CR : Nat}
    {BA : UInt64 → β → α → Nat}
    (hall : all = fun i => live i || false || (Expr.foldStep x body).uses (i + 2))
    (hM : (init.mode modes).join
      (body.mode (.borrowed :: .borrowed :: .borrowed :: modes)) = M)
    (hx : env.get x = xs.map ψ) (hi : init.denote funs env = φ I)
    (hb : ∀ i s v, body.denote funs (.cons (ψ v) (.cons (φ s) (.cons i env))) = φ (F s v))
    (hia : init.allocs funs flags bounds modes paid all env = IA)
    (hka : coerceCost t (init.mode modes) M (φ I) = KA)
    (hcr : (if (ps && !init.paid flags modes paid all) = true then t.credit (φ I) else 0) = CR)
    (hba : ∀ i s v, body.allocs funs flags bounds (.borrowed :: M :: .borrowed :: modes)
        (false :: ps :: false :: paid) (shift 1 (shift 2 all))
        (.cons (ψ v) (.cons (φ s) (.cons i env))) +
        coerceCost t (body.mode (.borrowed :: M :: .borrowed :: modes)) M (φ (F s v)) =
      BA i s v)
    (hby : ∀ (i : UInt64) (s : t.denote), (if ps = true then (Expr.foldStep x body).buys funs flags
        (M :: .borrowed :: modes) (ps :: false :: paid) (shift 2 all) (.cons s (.cons i env))
      else 0) = 0) :
    loopAllocWith ps funs flags modes paid live (.size x) init (.bool true) (Expr.foldStep x body)
        (fun _ _ => 0) (fun live env => init.allocs funs flags bounds modes paid live env)
        (fun _ _ _ _ => 0)
        (fun modes paid live env =>
          body.allocs funs flags bounds (.borrowed :: modes) (false :: paid) (shift 1 live)
            (.cons ((env.get (.there (.there x)))[(env.get (.there .here)).toNat]!) env)) env =
      IA + KA + CR + foldCost xs I F BA := by
  subst hall hM hia hka hcr
  show _ + _ + _ + _ + loopCost _ _ _ _ _ 0 (init.denote funs env) = _
  rw [hi]
  simp only [Expr.denote, Env.get, hx, Array.size_map, Nat.zero_add]
  congr 1
  apply foldCost_eq_loop xs I F BA φ
  · intro k hk s
    have hk64 : k < UInt64.size := hk.trans xs.size.toUInt64.toNat_lt_size
    have hkxs : k < xs.size := hk.trans_le (by exact Nat.mod_le _ _)
    simpa only [Expr.foldStep, Expr.denote, Env.get, hx,
      UInt64.toNat_ofNat_of_lt' hk64,
      getElem!_pos (xs.map ψ) k (by simpa using hkxs), Array.getElem_map]
      using hb (UInt64.ofNat k) s xs[k]
  · intro k hk s
    have hk64 : k < UInt64.size := hk.trans xs.size.toUInt64.toNat_lt_size
    have hkxs : k < xs.size := hk.trans_le (by exact Nat.mod_le _ _)
    have hz := hby (UInt64.ofNat k) (φ s)
    simp only [Expr.foldStep, Expr.mode, Expr.denote, Expr.uses, Env.get, hx,
      UInt64.toNat_ofNat_of_lt' hk64,
      getElem!_pos (xs.map ψ) k (by simpa using hkxs), Array.getElem_map, hb] at hz
    simpa only [Expr.foldStep, Expr.mode, Expr.denote, Expr.uses, Env.get, hx,
      UInt64.toNat_ofNat_of_lt' hk64,
      getElem!_pos (xs.map ψ) k (by simpa using hkxs), Array.getElem_map, hb, hz, Nat.add_zero]
      using hba (UInt64.ofNat k) s xs[k]

theorem fold_flat_bound {e : Elem} {t : Ty} {α β : Type} (φ : β → t.denote)
    (ψ : α → e.denote) (xs : Array α) (I : β) (F : β → α → β)
    {x : Var Γ (.array e)} {init : Expr S Γ t}
    {body : Expr S (.elem e :: t :: .word :: Γ) t}
    {all : Nat → Bool} {M : Mode} {ps : Bool} {IA KA CR : Nat}
    {BA : UInt64 → β → α → Nat}
    (hall : all = fun i => live i || false || (Expr.foldStep x body).uses (i + 2))
    (hM : (init.mode modes).join
      (body.mode (.borrowed :: .borrowed :: .borrowed :: modes)) = M)
    (hps : Expr.statePaid flags modes paid live init (.bool true) (Expr.foldStep x body) = ps)
    (hpair : (ps && t.isPair) = false)
    (hx : env.get x = xs.map ψ) (hi : init.denote funs env = φ I)
    (hb : ∀ i s v, body.denote funs (.cons (ψ v) (.cons (φ s) (.cons i env))) = φ (F s v))
    (hia : init.allocs funs flags bounds modes paid all env = IA)
    (hka : coerceCost t (init.mode modes) M (φ I) = KA)
    (hcr : (if (ps && !init.paid flags modes paid all) = true then t.credit (φ I) else 0) = CR)
    (hba : ∀ i s v, body.allocs funs flags bounds (.borrowed :: M :: .borrowed :: modes)
        (false :: ps :: false :: paid) (shift 1 (shift 2 all))
        (.cons (ψ v) (.cons (φ s) (.cons i env))) +
        coerceCost t (body.mode (.borrowed :: M :: .borrowed :: modes)) M (φ (F s v)) =
      BA i s v)
    (hby : ∀ (i : UInt64) (s : t.denote), (if ps = true then (Expr.foldStep x body).buys funs flags
        (M :: .borrowed :: modes) (ps :: false :: paid) (shift 2 all) (.cons s (.cons i env))
      else 0) = 0) :
    (Expr.fold x init body).allocs funs flags bounds modes paid live env =
      IA + KA + CR + foldCost xs I F BA := by
  subst hps
  simp only [Expr.allocs]
  rw [loopAlloc_of_not_min hpair]
  exact fold_flat_with φ ψ xs I F _ hall hM hx hi hb hia hka hcr hba hby

/-- The bound of a fold whose state is a paid pair: the smaller of the bounds with an unpaid and a
paid state. -/
theorem fold_min_flat_bound {e : Elem} {t : Ty} {α β : Type} (φ : β → t.denote)
    (ψ : α → e.denote) (xs : Array α) (I : β) (F : β → α → β)
    {x : Var Γ (.array e)} {init : Expr S Γ t}
    {body : Expr S (.elem e :: t :: .word :: Γ) t}
    {all : Nat → Bool} {M : Mode} {IA KA CR : Nat}
    {BA0 BA1 : UInt64 → β → α → Nat}
    (hall : all = fun i => live i || false || (Expr.foldStep x body).uses (i + 2))
    (hM : (init.mode modes).join
      (body.mode (.borrowed :: .borrowed :: .borrowed :: modes)) = M)
    (hps : Expr.statePaid flags modes paid live init (.bool true) (Expr.foldStep x body) = true)
    (hpair : t.isPair = true)
    (hx : env.get x = xs.map ψ) (hi : init.denote funs env = φ I)
    (hb : ∀ i s v, body.denote funs (.cons (ψ v) (.cons (φ s) (.cons i env))) = φ (F s v))
    (hia : init.allocs funs flags bounds modes paid all env = IA)
    (hka : coerceCost t (init.mode modes) M (φ I) = KA)
    (hcr : (if (true && !init.paid flags modes paid all) = true then t.credit (φ I) else 0) = CR)
    (hba0 : ∀ i s v, body.allocs funs flags bounds (.borrowed :: M :: .borrowed :: modes)
        (false :: false :: false :: paid) (shift 1 (shift 2 all))
        (.cons (ψ v) (.cons (φ s) (.cons i env))) +
        coerceCost t (body.mode (.borrowed :: M :: .borrowed :: modes)) M (φ (F s v)) =
      BA0 i s v)
    (hba1 : ∀ i s v, body.allocs funs flags bounds (.borrowed :: M :: .borrowed :: modes)
        (false :: true :: false :: paid) (shift 1 (shift 2 all))
        (.cons (ψ v) (.cons (φ s) (.cons i env))) +
        coerceCost t (body.mode (.borrowed :: M :: .borrowed :: modes)) M (φ (F s v)) =
      BA1 i s v)
    (hby : ∀ (i : UInt64) (s : t.denote), (if true = true then (Expr.foldStep x body).buys funs
        flags (M :: .borrowed :: modes) (true :: false :: paid) (shift 2 all) (.cons s (.cons i env))
      else 0) = 0) :
    (Expr.fold x init body).allocs funs flags bounds modes paid live env =
      min (IA + KA + foldCost xs I F BA0) (IA + KA + CR + foldCost xs I F BA1) := by
  simp only [Expr.allocs]
  rw [loopAlloc_of_min (by rw [hps, hpair]; rfl),
    fold_flat_with φ ψ xs I F false hall hM hx hi hb hia hka (CR := 0) rfl hba0 (fun _ _ => rfl),
    fold_flat_with φ ψ xs I F true hall hM hx hi hb hia hka hcr hba1 hby, Nat.add_zero]

theorem fold_flat_fits {e : Elem} {t : Ty} {α β : Type} (φ : β → t.denote)
    (ψ : α → e.denote) (xs : Array α) (I : β) (F : β → α → β)
    {fits : Fits S} {x : Var Γ (.array e)} {init : Expr S Γ t}
    {body : Expr S (.elem e :: t :: .word :: Γ) t} {IF : Bool}
    {BF : UInt64 → β → α → Bool}
    (hx : env.get x = xs.map ψ) (hi : init.denote funs env = φ I)
    (hb : ∀ i s v, body.denote funs (.cons (ψ v) (.cons (φ s) (.cons i env))) = φ (F s v))
    (hif : init.fits funs fits env = IF)
    (hbf : ∀ i s v, body.fits funs fits (.cons (ψ v) (.cons (φ s) (.cons i env))) = BF i s v) :
    (Expr.fold x init body).fits funs fits env = (IF && foldFits xs I F BF) := by
  simp only [Expr.fits, hif, hi, hx, Array.size_map]
  congr 1
  apply foldFits_eq_loop xs I F BF φ
  · intro k hk s
    have hk64 : k < UInt64.size := hk.trans xs.size.toUInt64.toNat_lt_size
    have hkxs : k < xs.size := hk.trans_le (by exact Nat.mod_le _ _)
    simpa only [UInt64.toNat_ofNat_of_lt' hk64,
      getElem!_pos (xs.map ψ) k (by simpa using hkxs), Array.getElem_map]
      using hb (UInt64.ofNat k) s xs[k]
  · intro k hk s
    have hk64 : k < UInt64.size := hk.trans xs.size.toUInt64.toNat_lt_size
    have hkxs : k < xs.size := hk.trans_le (by exact Nat.mod_le _ _)
    simpa only [UInt64.toNat_ofNat_of_lt' hk64,
      getElem!_pos (xs.map ψ) k (by simpa using hkxs), Array.getElem_map]
      using hbf (UInt64.ofNat k) s xs[k]

#print axioms fold_flat_bound
#print axioms fold_min_flat_bound
#print axioms fold_flat_fits
#print axioms Verified.foldCost_eq_loop
#print axioms Verified.foldFits_eq_loop

end Verified.Reflect
