import Interpreter.Wasm.Syntax

/-!
The calls of a module's functions, which the code generators of the AArch64 and Cortex-M7 back
ends share: the functions that an instruction list calls, the functions that calls reach from one
function, the targets of those calls, the lookup of a function with its index, and the numbers of
parameters and results of the functions that a list of targets names.  `callNeed` gives the
largest of a bound over the functions that a body calls, from which each back end bounds the stack
of a call.  The definitions depend only on the syntax of Wasm modules.
-/

namespace LeanExe.CallGraph

open Wasm

mutual
/-- The indices of the functions that `ins` calls. -/
def callsOf : Instruction → List Nat
  | .call k => [k]
  | .block _ _ body _ _ => callsIn body
  | .loop _ _ body _ _ => callsIn body
  | .iff _ _ thn els _ _ => callsIn thn ++ callsIn els
  | _ => []

/-- The indices of the functions that the instructions `is` call. -/
def callsIn : List Instruction → List Nat
  | [] => []
  | i :: rest => callsOf i ++ callsIn rest
end

/-- The functions of `m` that calls reach from those of `todo`, after those of `done`, each
once, within `fuel` steps. -/
def reachable (m : Module) : Nat → List Nat → List Nat → List Nat
  | 0, done, _ => done
  | _ + 1, done, [] => done
  | fuel + 1, done, j :: todo =>
      if j ∈ done then reachable m fuel done todo
      else reachable m fuel (done ++ [j])
        (todo ++ ((m.funcs[j]?).map fun f => callsIn f.body).getD [])

/-- The functions that calls reach from function `k` of `m`, `k` first. -/
def reachFrom (m : Module) (k : Nat) : List Nat :=
  reachable m (1 + (m.funcs.map fun f => (callsIn f.body).length).sum) [] [k]

/-- The functions that the calls of the functions that calls reach from function `k` of `m`
name. -/
def callTargets (m : Module) (k : Nat) : List Nat :=
  (reachFrom m k).flatMap fun j => ((m.funcs[j]?).map fun f => callsIn f.body).getD []

/-- Function `j` of `m` with its index. -/
def funcOf (m : Module) (j : Nat) : Except String (Nat × Function) :=
  match m.funcs[j]? with
  | some f => pure (j, f)
  | none => throw s!"no function {j}"

/-- The numbers of parameters and results of the functions of `fs` that `targets` names, by
index. -/
def sigIn (targets : List Nat) (fs : List (Nat × Function)) (k : Nat) : Option (Nat × Nat) :=
  if k ∈ targets then
    (fs.find? (·.1 = k)).map fun (_, f) => (f.params.length, f.results.length)
  else none

theorem mapM_funcOf {m : Module} : ∀ {ks : List Nat} {fs : List (Nat × Function)},
    ks.mapM (funcOf m) = .ok fs → ∀ x ∈ fs, m.funcs[x.1]? = some x.2
  | [], fs, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp
  | j :: ks, fs, h => by
      rw [List.mapM_cons] at h
      cases h1 : funcOf m j with
      | error e => simp [h1, bind, Except.bind] at h
      | ok y =>
          cases h2 : ks.mapM (funcOf m) with
          | error e => simp [h1, h2, bind, Except.bind] at h
          | ok ys =>
              simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
              subst h
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · unfold funcOf at h1
                split at h1
                · rename_i f hf
                  simp only [pure, Except.pure, Except.ok.injEq] at h1
                  subst h1
                  exact hf
                · simp [throw, throwThe, MonadExceptOf.throw] at h1
              · exact mapM_funcOf h2 x hx

theorem mem_reachable (m : Module) {x : Nat} :
    ∀ (fuel : Nat) (done todo : List Nat), x ∈ done → x ∈ reachable m fuel done todo
  | 0, _, _, h => by simpa only [reachable] using h
  | _ + 1, _, [], h => by simpa only [reachable] using h
  | fuel + 1, done, j :: todo, h => by
      simp only [reachable]
      split
      · exact mem_reachable m fuel done todo h
      · exact mem_reachable m fuel _ _ (List.mem_append_left _ h)

theorem mem_reachFrom (m : Module) (k : Nat) : k ∈ reachFrom m k := by
  unfold reachFrom
  rw [Nat.add_comm]
  simp only [reachable]
  rw [ite_eq_right List.not_mem_nil]
  exact mem_reachable m _ _ _ (by simp)

/-- The functions that the body of function `k` of `m` calls lie among `callTargets m k`. -/
theorem callsIn_callTargets {m : Module} {k : Nat} {f : Function} (hk : m.funcs[k]? = some f)
    {j : Nat} (hj : j ∈ callsIn f.body) : j ∈ callTargets m k := by
  unfold callTargets
  exact List.mem_flatMap.mpr ⟨k, mem_reachFrom m k, by simpa [hk] using hj⟩

theorem foldr_max_le : ∀ {l : List Nat} {c : Nat}, (∀ x ∈ l, x ≤ c) → l.foldr max 0 ≤ c
  | [], _, _ => Nat.zero_le _
  | x :: _, _, h => Nat.max_le.mpr ⟨h x List.mem_cons_self,
      foldr_max_le fun y hy => h y (List.mem_cons_of_mem x hy)⟩

theorem le_foldr_max : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.foldr max 0
  | y :: _, _, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right y _)

/-- The largest of `need j` over the functions `j` that the calls of `body` name, or 0. -/
def callNeed (need : Nat → Nat) (body : List Instruction) : Nat :=
  ((callsIn body).map need).foldr max 0

theorem le_callNeed {need : Nat → Nat} {body : List Instruction} {j : Nat}
    (h : j ∈ callsIn body) : need j ≤ callNeed need body :=
  le_foldr_max (List.mem_map_of_mem h)

theorem callNeed_mono {need need' : Nat → Nat} (h : ∀ j, need j ≤ need' j)
    (body : List Instruction) : callNeed need body ≤ callNeed need' body :=
  foldr_max_le fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact Nat.le_trans (h j) (le_callNeed hj)

end LeanExe.CallGraph
