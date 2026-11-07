import Interpreter.Wasm.Syntax

/-!
The calls of a module's functions, which the code generators of the AArch64 and Cortex-M7 back
ends share: the functions that an instruction list calls, the functions that calls reach from one
function, the targets of those calls, the lookup of a function with its index, and the numbers of
parameters and results of the functions that a list of targets names.  `callNeed` gives the
largest of a bound over the functions that a body calls, and `stackNeedOf` bounds the stack of a
call from the size of each function's frame, which each back end gives.  The definitions depend
only on the syntax of Wasm modules.
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
once, within `fuel` steps.  A step drops the functions at the front of `todo` that `done` holds,
adds the next one to `done`, and appends the functions that it calls to `todo`, so that each step
adds a function. -/
def reachable (m : Module) : Nat → List Nat → List Nat → List Nat
  | 0, done, _ => done
  | fuel + 1, done, todo =>
      match todo.dropWhile (fun j => decide (j ∈ done)) with
      | [] => done
      | j :: rest => reachable m fuel (done ++ [j])
          (rest ++ ((m.funcs[j]?).map fun f => callsIn f.body).getD [])

/-- The functions that calls reach from function `k` of `m`, `k` first.  The fuel, the number of
the module's functions plus one, suffices when every call names a function of `m`, since each step
adds a function, and the kernel's evaluation of the fuel reads no function's body. -/
def reachFrom (m : Module) (k : Nat) : List Nat :=
  reachable m (m.funcs.length + 1) [] [k]

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

/-- The indices of the functions that `funcOf` finds are those of the list. -/
theorem mapM_funcOf_mem {m : Module} : ∀ {ks : List Nat} {fs : List (Nat × Function)},
    ks.mapM (funcOf m) = .ok fs → ∀ x ∈ fs, x.1 ∈ ks
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
                · simp only [pure, Except.pure, Except.ok.injEq] at h1
                  subst h1
                  exact List.mem_cons_self
                · simp [throw, throwThe, MonadExceptOf.throw] at h1
              · exact List.mem_cons_of_mem _ (mapM_funcOf_mem h2 x hx)

/-- The first of the functions that `funcOf` finds is that of the first index. -/
theorem mapM_funcOf_cons {m : Module} {j : Nat} {ks : List Nat} {fs : List (Nat × Function)}
    (h : (j :: ks).mapM (funcOf m) = .ok fs) :
    ∃ f rest, m.funcs[j]? = some f ∧ fs = (j, f) :: rest := by
  rw [List.mapM_cons] at h
  cases h1 : funcOf m j with
  | error e => simp [h1, bind, Except.bind] at h
  | ok y =>
      cases h2 : ks.mapM (funcOf m) with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok ys =>
          simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
          subst h
          unfold funcOf at h1
          split at h1
          · rename_i f hf
            simp only [pure, Except.pure, Except.ok.injEq] at h1
            subst h1
            exact ⟨f, ys, hf, rfl⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h1

/-- `reachable` keeps the functions already found, first. -/
theorem reachable_prefix (m : Module) :
    ∀ (fuel : Nat) (done todo : List Nat), ∃ rest, reachable m fuel done todo = done ++ rest
  | 0, done, _ => ⟨[], by simp [reachable]⟩
  | fuel + 1, done, todo => by
      simp only [reachable]
      split
      · exact ⟨[], by simp⟩
      · rename_i j _ _
        obtain ⟨rest, h⟩ := reachable_prefix m fuel (done ++ [j]) _
        exact ⟨j :: rest, by rw [h, List.append_assoc, List.singleton_append]⟩

/-- `reachFrom m k` starts with `k`. -/
theorem reachFrom_cons (m : Module) (k : Nat) : ∃ rest, reachFrom m k = k :: rest := by
  unfold reachFrom
  simp only [reachable, List.not_mem_nil, decide_false, List.dropWhile_cons_of_neg,
    Bool.false_eq_true, not_false_eq_true]
  obtain ⟨rest, h⟩ := reachable_prefix m m.funcs.length ([] ++ [k])
    ([] ++ ((m.funcs[k]?).map fun f => callsIn f.body).getD [])
  exact ⟨rest, by rw [h]; rfl⟩

theorem mem_reachable (m : Module) {x : Nat} :
    ∀ (fuel : Nat) (done todo : List Nat), x ∈ done → x ∈ reachable m fuel done todo
  | 0, _, _, h => by simpa only [reachable] using h
  | fuel + 1, done, todo, h => by
      simp only [reachable]
      split
      · exact h
      · exact mem_reachable m fuel _ _ (List.mem_append_left _ h)

theorem mem_reachFrom (m : Module) (k : Nat) : k ∈ reachFrom m k := by
  obtain ⟨rest, h⟩ := reachFrom_cons m k
  rw [h]
  exact List.mem_cons_self

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

/-! ## A bound of the stack -/

/-- `n` bounds the bytes of stack that a call of a function uses, when the function's frame has
`fs` bytes, its body is `body`, and `need` bounds the stack of the calls in the body: `n` is at
least the frame plus `callNeed`, or at least 2^64, which bounds nothing. -/
def NeedOk (need : Nat → Nat) (fs : Nat) (body : List Instruction) (n : Nat) : Prop :=
  2 ^ 64 ≤ n ∨ fs + callNeed need body ≤ n

/-- A count below 2^64 and below `fs` plus `callNeed` lies below `n`. -/
theorem NeedOk.lt {need : Nat → Nat} {fs : Nat} {body : List Instruction} {n d : Nat}
    (h : NeedOk need fs body n) (hd : d < 2 ^ 64) (hlt : d < fs + callNeed need body) : d < n := by
  rcases h with h | h <;> omega

/-- A bound on the bytes of stack that a call of function `k` of `m` uses, following calls `d`
deep, when the frame of function `f` has `frame f` bytes: at depth 0, 2^64, which bounds nothing,
and otherwise the function's frame plus `callNeed` of the bounds at depth `d - 1`, at most 2^64,
or 0 when `m` has no function `k`. -/
def stackNeedOf (m : Module) (frame : Function → Nat) : Nat → Nat → Nat
  | 0, _ => 2 ^ 64
  | d + 1, k =>
      match m.funcs[k]? with
      | some f => min (2 ^ 64) (frame f + callNeed (stackNeedOf m frame d) f.body)
      | none => 0

theorem stackNeedOf_zero (m : Module) (frame : Function → Nat) (k : Nat) :
    stackNeedOf m frame 0 k = 2 ^ 64 := rfl

theorem stackNeedOf_some {m : Module} {frame : Function → Nat} {k : Nat} {f : Function}
    (hk : m.funcs[k]? = some f) (d : Nat) :
    stackNeedOf m frame (d + 1) k =
      min (2 ^ 64) (frame f + callNeed (stackNeedOf m frame d) f.body) := by
  simp only [stackNeedOf.eq_2, hk]

theorem stackNeedOf_none {m : Module} {frame : Function → Nat} {k : Nat}
    (hk : m.funcs[k]? = none) (d : Nat) : stackNeedOf m frame (d + 1) k = 0 := by
  simp only [stackNeedOf.eq_2, hk]

theorem stackNeedOf_succ_le (m : Module) (frame : Function → Nat) :
    ∀ d k, stackNeedOf m frame (d + 1) k ≤ stackNeedOf m frame d k
  | 0, k => by
      cases hk : m.funcs[k]? with
      | none => simp only [stackNeedOf_none hk 0, Nat.zero_le]
      | some f =>
          rw [stackNeedOf_some hk 0, stackNeedOf_zero]
          exact Nat.min_le_left _ _
  | d + 1, k => by
      cases hk : m.funcs[k]? with
      | none => simp only [stackNeedOf_none hk (d + 1), stackNeedOf_none hk d, Nat.le_refl]
      | some f =>
          have h := callNeed_mono (stackNeedOf_succ_le m frame d) f.body
          rw [stackNeedOf_some hk (d + 1), stackNeedOf_some hk d, Nat.min_def, Nat.min_def]
          split <;> split <;> omega

/-- `stackNeedOf` at every depth satisfies `NeedOk` for every function of `m`. -/
theorem stackNeedOf_ok {m : Module} {frame : Function → Nat} {k : Nat} {f : Function}
    (hk : m.funcs[k]? = some f) :
    ∀ d, NeedOk (stackNeedOf m frame d) (frame f) f.body (stackNeedOf m frame d k)
  | 0 => .inl (Nat.le_of_eq (stackNeedOf_zero m frame k).symm)
  | d + 1 => by
      have h := callNeed_mono (stackNeedOf_succ_le m frame d) f.body
      unfold NeedOk
      rw [stackNeedOf_some hk d, Nat.min_def]
      split <;> omega

/-- `stackNeedOf` of a function whose body calls no function is at most its frame. -/
theorem stackNeedOf_of_nil {m : Module} {frame : Function → Nat} {k : Nat} {f : Function}
    (hk : m.funcs[k]? = some f) (hc : callsIn f.body = []) (d : Nat) :
    stackNeedOf m frame (d + 1) k ≤ frame f := by
  rw [stackNeedOf_some hk d, callNeed, hc, List.map_nil, List.foldr_nil, Nat.add_zero]
  exact Nat.min_le_right _ _

end LeanExe.CallGraph
