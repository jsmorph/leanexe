import LeanExe.M7.Bound

/-!
The static bound of `LeanExe/M7/Bound.lean` bounds the cost of every run.  `costOne_le` and
`costExec_le` follow the recursion of `costOne` and `costExec` on the fuel and on the code: a
straight-line form costs what `costI` charges, an `if` costs its taken branch, at most the larger
of the two, a block its body, and a call the callee's run, which the bounds of the called
functions bound at every smaller fuel; a loop has no static bound.  `costRun_le_staticCost` gives,
for a module that imports nothing, that `staticCost m k` bounds `costRun` of function `k` at every
fuel, store, and argument list.
-/

namespace LeanExe.M7

open Wasm

variable {α : Type}

theorem costI_plain {callee : Nat → Option Nat} {fs : Nat → Option Function} {ar : List Nat}
    {inst : Instruction} (h : plainForm inst = true) :
    costI callee fs ar inst = some (instrSize (fun _ => none) ar 0 inst).1 := by
  rw [costI.eq_def]
  split <;> simp_all [plainForm]

theorem costOne_iff_le {f pa ra t e : Nat} {m : Module} {st : Store α} {s : Locals}
    {ar : List Nat} {thn els : Program} {pt rt : List ValueType} {env : HostEnv α}
    (ht : ∀ vs, costExec f m st { s with values := vs } (ra :: ar) thn env ≤ t)
    (he : ∀ vs, costExec f m st { s with values := vs } (ra :: ar) els env ≤ e) :
    costOne (f + 1) m st s ar (.iff pa ra thn els pt rt) env ≤ 3 + max (t + 1) e := by
  cases hv : s.values with
  | nil =>
      rw [costOne.eq_def]
      simp only [hv]
      omega
  | cons v vs =>
      cases v with
      | i32 c =>
          rw [costOne_iff hv]
          have := ht vs
          have := he vs
          split <;> omega
      | _ =>
          rw [costOne.eq_def]
          simp only [hv]
          omega

/-- The bounds `callee` bound the runs of the functions that they name at every fuel below
`F`. -/
def CostsOk (F : Nat) (m : Module) (env : HostEnv α) (callee : Nat → Option Nat) : Prop :=
  ∀ j c, callee j = some c → ∀ g < F, ∀ (st : Store α) (vs : List Value),
    costRun g m j st vs env ≤ c

theorem CostsOk.mono {F G : Nat} {m : Module} {env : HostEnv α} {callee : Nat → Option Nat}
    (h : CostsOk F m env callee) (hle : G ≤ F) : CostsOk G m env callee :=
  fun j c hj g hg => h j c hj g (by omega)

mutual

theorem costOne_le {m : Module} {env : HostEnv α} (hm : m.imports = []) :
    ∀ (F : Nat) (callee : Nat → Option Nat), CostsOk F m env callee →
      ∀ (inst : Instruction) (ar : List Nat) (st : Store α) (s : Locals) (c : Nat),
        costI callee (fun j => m.funcs[j]?) ar inst = some c → costOne F m st s ar inst env ≤ c
  | 0, _, _, _, _, _, _, _, _ => by
      rw [costOne.eq_def]
      exact Nat.zero_le _
  | f + 1, callee, hcl, inst, ar, st, s, c, h => by
      by_cases hp : plainForm inst = true
      · rw [costOne_plain hp]
        rw [costI_plain hp] at h
        cases h
        exact Nat.le_refl _
      · cases inst <;> simp only [plainForm, Bool.false_eq_true, not_true_eq_false,
          not_false_eq_true] at hp
        case block pa ra body pt rt =>
          rw [costOne_block]
          simp only [costI] at h
          exact costExec_le hm f callee (hcl.mono (Nat.le_succ f)) body (ra :: ar) st s c h
        case loop =>
          simp [costI] at h
        case iff pa ra thn els pt rt =>
          simp only [costI] at h
          cases ht : costL callee (fun j => m.funcs[j]?) (ra :: ar) thn with
          | none => simp [ht] at h
          | some t =>
              cases he : costL callee (fun j => m.funcs[j]?) (ra :: ar) els with
              | none => simp [ht, he] at h
              | some e =>
                  simp only [ht, he, Option.some.injEq] at h
                  subst h
                  exact costOne_iff_le
                    (fun vs => costExec_le hm f callee (hcl.mono (Nat.le_succ f)) thn (ra :: ar)
                      st _ t ht)
                    (fun vs => costExec_le hm f callee (hcl.mono (Nat.le_succ f)) els (ra :: ar)
                      st _ e he)
        case call k =>
          simp only [costI] at h
          cases hg : m.funcs[k]? with
          | none => simp [hg] at h
          | some g =>
              cases hc' : callee k with
              | none => simp [hg, hc'] at h
              | some c' =>
                  simp only [hg, hc', Option.some.injEq] at h
                  subst h
                  rw [costOne_call]
                  have hcc : callCost m k = 4 * g.params.length + 1 + 4 * g.results.length := by
                    simp [callCost, hm, hg]
                  have := hcl k c' hc' f (Nat.lt_succ_self f) st s.values
                  omega
        case divUI64 =>
          simp only [costI, Option.some.injEq] at h
          subst h
          exact Nat.le_of_eq costOne_divUI64
        case remUI64 =>
          simp only [costI, Option.some.injEq] at h
          subst h
          exact Nat.le_of_eq costOne_remUI64
termination_by F _ _ _ _ _ _ _ _ => (F, 0)
decreasing_by all_goals (apply Prod.Lex.left; omega)

theorem costExec_le {m : Module} {env : HostEnv α} (hm : m.imports = []) :
    ∀ (F : Nat) (callee : Nat → Option Nat), CostsOk F m env callee →
      ∀ (p : Program) (ar : List Nat) (st : Store α) (s : Locals) (c : Nat),
        costL callee (fun j => m.funcs[j]?) ar p = some c → costExec F m st s ar p env ≤ c
  | F, callee, hcl, p, ar, st, s, c, h => by
      induction p generalizing st s c with
      | nil =>
          rw [costExec_nil]
          exact Nat.zero_le _
      | cons i rest ih =>
          simp only [costL] at h
          cases hc1 : costI callee (fun j => m.funcs[j]?) ar i with
          | none => simp [hc1] at h
          | some c1 =>
              cases hd : costL callee (fun j => m.funcs[j]?) ar rest with
              | none => simp [hc1, hd] at h
              | some d =>
                  simp only [hc1, hd, Option.some.injEq] at h
                  subst h
                  rw [costExec_cons]
                  have h1 := costOne_le hm F callee hcl i ar st s c1 hc1
                  split
                  · rename_i st' s' _
                    have h2 := ih st' s' d hd
                    omega
                  · omega
termination_by F _ _ _ _ _ _ _ _ => (F, 1)
decreasing_by all_goals (apply Prod.Lex.right; omega)

end

/-- `costOf m d k` bounds the cost of every run of function `k` of `m`, which imports nothing. -/
theorem costRun_le_costOf {m : Module} {env : HostEnv α} (hm : m.imports = []) :
    ∀ (d k c : Nat), costOf m d k = some c →
      ∀ (F : Nat) (st : Store α) (vs : List Value), costRun F m k st vs env ≤ c
  | 0, k, c, h => by simp [costOf] at h
  | d + 1, k, c, h => by
      intro F st vs
      simp only [costOf] at h
      cases hk : m.funcs[k]? with
      | none => simp [hk] at h
      | some f =>
          rw [hk] at h
          simp only [costF] at h
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [costRun_some (f := f) (by simp [hm]) (by simp [hm, hk])]
          have := costExec_le (env := env) hm F (costOf m d)
            (fun j c' hj g _ st' vs' => costRun_le_costOf hm d j c' hj g st' vs') f.body
            [f.results.length] st (f.toLocals (vs.take f.numParams).reverse) b hb
          omega

/-- `staticCost m k` bounds the cost of every run of function `k` of `m`, which imports
nothing. -/
theorem costRun_le_staticCost {m : Module} {k c : Nat} {env : HostEnv α} (hm : m.imports = [])
    (h : staticCost m k = some c) (F : Nat) (st : Store α) (vs : List Value) :
    costRun F m k st vs env ≤ c :=
  costRun_le_costOf hm _ k c h F st vs

end LeanExe.M7
