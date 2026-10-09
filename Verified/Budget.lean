import Verified.Correct

/-! The compiler's correctness theorem with the allocation bound: the code of an expression traps
only through a call of a function whose code takes the call depth, or when `top` cannot rise by
the expression's bound, `Expr.allocs`, within the memory cap, and it raises `top` by at most that
bound. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The traps that the code of `e` may have from `heap` at `store`: any, when it calls a function
whose code takes the call depth, and otherwise those of allocation, when it may allocate and `top`
cannot rise by `bound` within the cap. -/
abbrev trapFlag {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (e : Expr S Γ t)
    (slots : List Slot) (heap : Heap) (store : Store Unit) (bound : Nat) : Bool :=
  e.depthCalls ||
    ((e.aborts || slots.any (·.mode == .owned)) && !decide (heap.Within store m bound))

/-- `CodeSpec` with the allocation bound: the code may trap only as `trapFlag` allows for the
bound `e.allocs`, and, when it takes no call depth, it raises `top` by at most that bound. -/
def CodeSpecB {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (bounds : Bounds S) (host : HostEnv Unit) (pv : List Value) (e : Expr S Γ t) (env : Env Γ)
    (slots : List Slot) (live : Nat → Bool) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.half = h → s.params = pv →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (trapFlag m e slots heap store (e.allocs funs bounds (slots.map Slot.mode) live env))
      Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      (e.depthCalls = false →
        heap'.top.toNat ≤ heap.top.toNat + e.allocs funs bounds (slots.map Slot.mode) live env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (e.code h slots base live ++ rest) Q store s host

/-- The allowance of a part of an expression from that of the whole: the part calls a function
whose code takes the call depth only when the whole does, may allocate only when the whole may,
and, when the whole takes no call depth, has room for its bound when the whole has room for its
own. -/
theorem _root_.Wasm.TrapOK.part {Q : Assertion Unit} {d d' a a' : Bool} {P P' : Prop}
    [Decidable P] [Decidable P'] (h : TrapOK (d || (a && !decide P)) Q)
    (hd : d' = true → d = true) (ha : a' = true → a = true) (hP : d = false → P → P') :
    TrapOK (d' || (a' && !decide P')) Q := by
  cases hdv : d
  · have hd' : d' = false := by cases d' <;> simp_all
    refine h.of_imp fun h' => ?_
    simp only [hd', Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h'
    simp only [hdv, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨ha h'.1, fun hp => h'.2 (hP hdv hp)⟩
  · exact TrapOK.any (by simpa [hdv] using h)

/-- Room for `total` before a step that raises `top` by at most `c1` leaves room for any `c2`
with `c1 + c2 ≤ total` after it. -/
theorem _root_.LeanExe.Pipeline.Heap.Within.shift {heap heap1 : Heap} {store store1 : Store Unit}
    {m : Module} {total c1 c2 : Nat} (h : heap.Within store m total)
    (hTop : heap1.top.toNat ≤ heap.top.toNat + c1) (hc : c1 + c2 ≤ total)
    (hCaps : store1.memoryCap m 0 = store.memoryCap m 0) : heap1.Within store1 m c2 := by
  unfold Heap.Within at *; rw [hCaps]; omega

/-- Closes a fact that a part's call-depth or allocation flag implies the whole's. -/
macro "flag_tac" : tactic =>
  `(tactic| (
    intro h
    simp only [Expr.depthCalls, Expr.aborts, Bool.or_eq_true] at h ⊢
    first | (simp [h]; done) | tauto))

/-- The bytes of a call's argument `i`: those of its code when it holds no arrays, those of its
owned code when its parameter is owned, and none for a borrowed place. -/
def argCost {S : List Sig} {Γ : List Ty} (funs : Funs S) (bounds : Bounds S) (modesL : List Mode)
    (all kept : Nat → Bool) {ps : List Ty} (modes : Nat → Mode)
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (env : Env Γ) (i : Fin ps.length) : Nat :=
  if (ps.get i).scalar then (args i).allocs funs bounds modesL all env
  else if modes i = .owned then (args i).ownedCost modesL kept env else 0

/-- `ImplementsA` with the allocation bound `bound`: the call traps only when `aborts` holds and
`top` cannot rise by `bound x` within the cap, and it raises `top` by at most `bound x`. -/
def ImplementsB {α β : Type} [Represent α] [Represent β] (aborts : Bool) (m : Module) (entry : Nat)
    (f : α → β) (bound : α → Nat) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 →
    Runs (aborts && !decide (heap.Within store m (bound x))) env m entry store params.reverse
      fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ Represent.outside final values.reverse (f x) r) ∧
        heap'.top.toNat ≤ heap.top.toNat + bound x

/-- `FunSpec` with the allocation bound `A`: a function whose code takes no call depth is
`ImplementsB` for `A`, and one whose code takes it is as `FunSpec` states. -/
def FunSpecB (m : Module) (g : Sig) (idx : Nat) (F : Env g.params → g.result.denote)
    (A : Env g.params → Nat) (D : UInt64 → Prop) : Prop :=
  (g.depth = false →
    @ImplementsB _ _ (Env.represent g.params g.modes) (Ty.represent g.result) g.aborts m idx F A) ∧
  (g.depth = true → ∀ d, D d →
    @ImplementsA _ _ (Env.represent (.word :: g.params) (.borrowed :: g.modes))
      (Ty.represent g.result) true m idx (depthMeaning F) (fun env _ _ => env.depthOf = d)
      (fun _ _ _ _ _ => True)) ∧
  ∃ fn, m.funcs[idx]? = some fn ∧ fn.numParams = (if g.depth then 1 else 0) + widthSum g.params

/-- `Calls` with the bounds `bounds`. -/
def CallsB {S : List Sig} (m : Module) (funs : Funs S) (bounds : Bounds S) : Prop :=
  ∀ {g : Sig} (f : FVar S g), FunSpecB m g f.callIndex (funs.get f) (bounds.get f) (fun _ => True)

/-- `CallsAt` with the bounds `bounds`. -/
def CallsAtB {S : List Sig} (m : Module) (funs : Funs S) (bounds : Bounds S) (d0 : UInt64) :
    Prop :=
  ∀ {g : Sig} (f : FVar S g), FunSpecB m g f.callIndex (funs.get f) (bounds.get f)
    (fun d => d = d0 + 1)

theorem CallsB.at {S : List Sig} {m : Module} {funs : Funs S} {bounds : Bounds S}
    (h : CallsB m funs bounds) (d0 : UInt64) : CallsAtB m funs bounds d0 :=
  fun f => ⟨(h f).1, fun hd d _ => (h f).2.1 hd d trivial, (h f).2.2⟩

/-- `callMoves` reads only the slots' modes. -/
theorem callMovesAt_eq {S : List Sig} {Γ : List Ty} {g : Sig} (slots : List Slot)
    (live : Nat → Bool) (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) :
    callMovesAt (slots.map Slot.mode) live args = callMoves slots live args := by
  funext i
  cases hv : (args i).varIndex? <;> simp only [callMovesAt, callMoves, hv, modeAt, Slot.modes_getD]

/-- A call of the function that `FunSpec` describes, from the words `ws` of its arguments above,
when its code takes the call depth, a depth `d` that `D` admits: the call returns words that
represent its value and changes the heap and store only as `ImplementsA` allows, or traps when the
function may trap and `top` cannot rise by its bound, or its code takes the depth. -/
theorem FunSpecB.runs {m : Module} {g : Sig} {idx : Nat} {F : Env g.params → g.result.denote}
    {A : Env g.params → Nat} {D : UInt64 → Prop} (hF : FunSpecB m g idx F A D) (hm : Runtime m)
    (host : HostEnv Unit)
    {heap : Heap} {store : Store Unit} {ws : List Value} {args : Env g.params}
    (hAt : heap.At store) (hRep : Env.Rep g.mode heap store ws args)
    (hSep : Separate store (Env.moves g.mode ws args) (Env.reads g.mode ws args))
    (hCap : store.memoryCap m 0 ≤ 65535) {d : UInt64} (hd : g.depth = true → D d)
    (rest : List Value) :
    Runs ((g.aborts && !decide (heap.Within store m (A args))) || g.depth) host m idx store
      (ws.reverse ++ ((if g.depth then [.i64 d] else []) ++ rest))
      fun final values => ∃ out, values = out ++ rest ∧ ∃ heap' : Heap, heap'.At final ∧
        g.result.Rep .owned heap' final out.reverse (F args) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Env.moves g.mode ws args) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r ∧
          ∀ b ∈ g.result.blocks final out.reverse (F args), regionsDisjoint r b) ∧
        (g.depth = false → heap'.top.toNat ≤ heap.top.toNat + A args) := by
  obtain ⟨hFalse, hTrue, fn, hfn, hnum⟩ := hF
  cases hdep : g.depth
  · have hRun := (hFalse hdep host store heap ws args hAt hRep hSep hCap).append_args
      (by simp [hm.imports]) (by simpa [hm.imports] using hfn)
      (by simp [hRep.length, hnum, hdep]) rest
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact hRun.mono fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, fun _ => hTop⟩
  · have hSep' : Separate store
        (Env.moves (paramMode (.word :: g.params) (.borrowed :: g.modes)) (.i64 d :: ws)
          (.cons (t := .word) d args))
        (Env.reads (paramMode (.word :: g.params) (.borrowed :: g.modes)) (.i64 d :: ws)
          (.cons (t := .word) d args)) := by
      rw [Env.moves_depth, Env.reads_depth]; exact hSep
    have hRun := (hTrue hdep d (hd hdep) host store heap (.i64 d :: ws)
      (.cons (t := .word) d args) hAt rfl
      (Env.rep_depth.mpr ⟨ws, rfl, hRep⟩) hSep' hCap).append_args
      (by simp [hm.imports]) (by simpa [hm.imports] using hfn)
      (by simp [hRep.length, hnum, hdep]; omega) rest
    simp only [Bool.or_true, ↓reduceIte]
    rw [show ws.reverse ++ ([.i64 d] ++ rest) = (.i64 d :: ws).reverse ++ rest by simp]
    exact hRun.mono fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, _⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, fun r hr hpos hA =>
        hRegions r hr hpos (by
          show Apart store (Env.moves (paramMode (.word :: g.params) (.borrowed :: g.modes))
            (.i64 d :: ws) (.cons (t := .word) d args)) r
          rw [Env.moves_depth]; exact hA), nofun⟩

theorem loopCost_succ_true {α : Type} {cc : α → Nat} {cond : α → Bool} {bc : UInt64 → α → Nat}
    {step : UInt64 → α → α} {n : Nat} {i : UInt64} {x : α} (h : cond x = true) :
    loopCost cc cond bc step (n + 1) i x = cc x + (bc i x + loopCost cc cond bc step n (i + 1)
      (step i x)) := by
  simp [loopCost, h]

theorem loopCost_succ_false {α : Type} {cc : α → Nat} {cond : α → Bool} {bc : UInt64 → α → Nat}
    {step : UInt64 → α → α} {n : Nat} {i : UInt64} {x : α} (h : cond x = false) :
    loopCost cc cond bc step (n + 1) i x = cc x := by
  simp [loopCost, h]

theorem loopCost_zero {α : Type} {cc : α → Nat} {cond : α → Bool} {bc : UInt64 → α → Nat}
    {step : UInt64 → α → α} {i : UInt64} {x : α} : loopCost cc cond bc step 0 i x = 0 := rfl

/-- The bytes of a loop's iterations from index `i`, with `n` indices left, at the state `x`, as
`Expr.allocs` counts them. -/
def Expr.loopRest {S : List Sig} {Γ : List Ty} {t : Ty} (funs : Funs S) (bounds : Bounds S)
    (modes : List Mode) (live : Nat → Bool) (init : Expr S Γ t) (cond : Expr S (t :: Γ) .bool)
    (body : Expr S (t :: .word :: Γ) t) (env : Env Γ) (n : Nat) (i : UInt64) (x : t.denote) :
    Nat :=
  loopCost
    (fun s => cond.allocs funs bounds (.borrowed :: modes)
      (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
      (.cons s env))
    (fun s => cond.denote funs (.cons s env))
    (fun i s =>
      body.allocs funs bounds (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
          modes))) :: .borrowed :: modes)
          (shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)))
          (.cons s (.cons i env)) +
        coerceCost t (body.mode (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
          modes))) :: .borrowed :: modes))
          ((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)))
          (body.denote funs (.cons s (.cons i env))))
    (fun i s => body.denote funs (.cons s (.cons i env))) n i x

theorem Expr.allocs_loop {S : List Sig} {Γ : List Ty} {t : Ty} (funs : Funs S)
    (bounds : Bounds S) (modes : List Mode) (live : Nat → Bool) (count : Expr S Γ .word)
    (init : Expr S Γ t) (cond : Expr S (t :: Γ) .bool) (body : Expr S (t :: .word :: Γ) t)
    (env : Env Γ) :
    (Expr.loop count init cond body).allocs funs bounds modes live env =
      count.allocs funs bounds modes
          (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2)) || init.uses i) env +
        init.allocs funs bounds modes (fun i => live i || cond.uses (i + 1) || body.uses (i + 2))
          env +
        coerceCost t (init.mode modes)
          ((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)))
          (init.denote funs env) +
        Expr.loopRest funs bounds modes live init cond body env (count.denote funs env).toNat 0
          (init.denote funs env) := rfl

theorem Expr.loopRest_true {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {bounds : Bounds S} {modes : List Mode} {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ} {n : Nat}
    {i : UInt64} {x : t.denote} (h : cond.denote funs (.cons x env) = true) :
    Expr.loopRest funs bounds modes live init cond body env (n + 1) i x =
      cond.allocs funs bounds (.borrowed :: modes)
          (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
          (.cons x env) +
        (body.allocs funs bounds (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
            modes))) :: .borrowed :: modes)
            (shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)))
            (.cons x (.cons i env)) +
          coerceCost t (body.mode (((init.mode modes).join (body.mode (.borrowed :: .borrowed ::
            modes))) :: .borrowed :: modes))
            ((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)))
            (body.denote funs (.cons x (.cons i env))) +
          Expr.loopRest funs bounds modes live init cond body env n (i + 1)
            (body.denote funs (.cons x (.cons i env)))) := by
  unfold Expr.loopRest
  exact loopCost_succ_true (cond := fun s => cond.denote funs (.cons s env)) h

theorem Expr.loopRest_false {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {bounds : Bounds S} {modes : List Mode} {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ} {n : Nat}
    {i : UInt64} {x : t.denote} (h : cond.denote funs (.cons x env) = false) :
    Expr.loopRest funs bounds modes live init cond body env (n + 1) i x =
      cond.allocs funs bounds (.borrowed :: modes)
          (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
          (.cons x env) := by
  unfold Expr.loopRest
  exact loopCost_succ_false (cond := fun s => cond.denote funs (.cons s env)) h

theorem Expr.loopRest_zero {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {bounds : Bounds S} {modes : List Mode} {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ}
    {i : UInt64} {x : t.denote} :
    Expr.loopRest funs bounds modes live init cond body env 0 i x = 0 := rfl

/-- Room for `total` gives room for `c` at a heap whose `top` plus `c` stays within the first
heap's `top` plus `total`. -/
theorem _root_.LeanExe.Pipeline.Heap.Within.of_le {heap heap1 : Heap} {store store1 : Store Unit}
    {m : Module} {total c : Nat} (h : heap.Within store m total)
    (hle : heap1.top.toNat + c ≤ heap.top.toNat + total)
    (hCaps : store1.memoryCap m 0 = store.memoryCap m 0) : heap1.Within store1 m c := by
  unfold Heap.Within at *; rw [hCaps]; omega

theorem Expr.loopRest_cond_le {S : List Sig} {Γ : List Ty} {t : Ty} {funs : Funs S}
    {bounds : Bounds S} {modes : List Mode} {live : Nat → Bool} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {env : Env Γ} {n : Nat}
    {i : UInt64} {x : t.denote} :
    cond.allocs funs bounds (.borrowed :: modes)
        (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
        (.cons x env) ≤
      Expr.loopRest funs bounds modes live init cond body env (n + 1) i x := by
  cases h : cond.denote funs (.cons x env)
  · rw [Expr.loopRest_false h]
  · rw [Expr.loopRest_true h]; omega

theorem sumBelow_mono (f : Nat → Nat) {i j : Nat} (h : i ≤ j) : sumBelow f i ≤ sumBelow f j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hl | hg
    · have := ih (by omega); simp only [sumBelow]; omega
    · rw [show i = j + 1 by omega]

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {bounds : Bounds S} {host : HostEnv Unit}
  {pv : List Value}

/-- `seq_spec` with the allocation bound: the two parts trap only as the whole's allowance
`d || (a && …)` allows for the sum of their bounds, and, when the whole takes no call depth,
`top` rises by at most that sum. -/
theorem seq_specB {Γ : List Ty} {t u : Ty} {l : Expr S Γ t} {r : Expr S Γ u}
    (lSpec : ∀ env slots live, CodeSpecB m funs bounds host pv l env slots live)
    (rSpec : ∀ env slots live, CodeSpecB m funs bounds host pv r env slots live)
    (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (h base : Nat) (heap : Heap)
    (store : Store Unit) (s : Locals) (hh : s.half = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ h) (hRoomR : base + r.width ≤ h)
    (hPlaceL : l.placeArgs = true) (hPlaceR : r.placeArgs = true) (rest : Program)
    (Q : Assertion Unit) {d a : Bool}
    (hTrap : TrapOK (d || (a && !decide (heap.Within store m
      (l.allocs funs bounds (slots.map Slot.mode) (fun i => live i || r.uses i) env +
        r.allocs funs bounds (slots.map Slot.mode) live env)))) Q)
    (hdl : l.depthCalls = true → d = true) (hdr : r.depthCalls = true → d = true)
    (hal : (l.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (har : (r.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (hNext : ∀ heap2 store2 s2 ws1 ws2,
      Step heap store (Holds.KeepDying env slots (fun i => live i || (l.uses i || r.uses i)) live
          store s) heap2 store2
        ((l.mode (slots.map Slot.mode)).fresh store2 t ws1 (l.denote funs env) ++
          (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env)) →
      Frame base s s2 → Holds env slots live base heap2 store2 s2 →
      t.Rep (l.mode (slots.map Slot.mode)) heap2 store2 ws1 (l.denote funs env) →
      u.Rep (r.mode (slots.map Slot.mode)) heap2 store2 ws2 (r.denote funs env) →
      Holds.Apart env slots live store2 s2 t (l.mode (slots.map Slot.mode)) ws1
        (l.denote funs env) →
      Holds.Apart env slots live store2 s2 u (r.mode (slots.map Slot.mode)) ws2
        (r.denote funs env) →
      (∀ x ∈ t.regions (l.mode (slots.map Slot.mode)) store2 ws1 (l.denote funs env),
        ∀ y ∈ (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env),
          regionsDisjoint x y) →
      (d = false → heap2.top.toNat ≤ heap.top.toNat +
        (l.allocs funs bounds (slots.map Slot.mode) (fun i => live i || r.uses i) env +
          r.allocs funs bounds (slots.map Slot.mode) live env)) →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ (ws1.reverse ++ s.values) } host) :
    wp m (l.code h slots base (fun i => live i || r.uses i) ++ (r.code h slots base live ++ rest))
      Q store s host := by
  have hIn : ∀ i, (live i || r.uses i || l.uses i) = true →
      (live i || (l.uses i || r.uses i)) = true := fun i h => live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hdl' : d = false → l.depthCalls = false := fun hd => by
    cases hl : l.depthCalls
    · rfl
    · rw [hdl hl] at hd; exact nomatch hd
  have hdr' : d = false → r.depthCalls = false := fun hd => by
    cases hr : r.depthCalls
    · rfl
    · rw [hdr hr] at hd; exact nomatch hd
  refine lSpec env slots _ h base heap store s hh hpv hVarsL hAt hCap hBase hRoomL hPlaceL _ _
      (hTrap.part hdl hal fun _ hw => hw.mono (Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  refine rSpec env slots live h base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.frame.half.trans hh) (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues)
    a1.step.at_
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) hRoomR hPlaceR _ _
    (hTrap.part hdr har fun hd hw => hw.after (hTop1 (hdl' hd)) (a1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTop2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  exact hNext heap2 store2 s2 ws1 ws2
    (hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb) hFrame
    a2.holds hRep1 a2.rep hApart1 a2.apart hDisjoint fun hd => by
      have := hTop1 (hdl' hd); have := hTop2 (hdr' hd); omega

/-- A constant word. -/
theorem specB_word {Γ : List Ty} (value : UInt64) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.word (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote] using
    hNext0 store s [.i64 value] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .word rfl] at hb; exact nomatch hb)


/-- A constant `Bool`. -/
theorem specB_bool {Γ : List Ty} (value : Bool) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.bool (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote] using
    hNext0 store s [.i64 (boolWord value)] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .bool rfl] at hb; exact nomatch hb)


/-- A float constant, from its bit pattern. -/
theorem specB_float {Γ : List Ty} (bits : UInt64) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.float (S := S) (Γ := Γ) bits) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote, F64Bits.toBits_ofBits] using
    hNext0 store s [.f64 (Float.ofBits bits).toBits] (After.refl hAt hVars
      (by intro i h; simp [h]) rfl (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .float rfl] at hb; exact nomatch hb)


/-- An operation on words; division and remainder save their operands to test the divisor. -/
theorem specB_bin {Γ : List Ty} (op : BinOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.bin op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hR : right.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  have hS : op.scratch ≤ max op.scratch (max left.width right.width) := Nat.le_max_left ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op
  case div | rem =>
    have hW2 : base + 2 ≤ h := by
      have := hRoom
      simp only [Expr.width, BinOp.scratch] at this
      omega
    have hp2 : s2.params = s.params := hF.params
    have hh2 : s2.half = h := hF.half.trans hh
    simp only [BinOp.code, List.cons_append, List.nil_append]
    refine wp_localSet_local (by rw [hp2]; omega)
      (Locals.lt_total (show base + 1 < ({ s2 with values := _ } : Locals).half by
        rw [Locals.half_values, hh2]; omega)) ?_
    refine wp_localSet_local (vs := s.values)
      (s := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
        (.i64 (right.denote funs env)))
      (by show s2.params.length ≤ base; rw [hp2]; omega)
      (Locals.lt_total (by simp only [Locals.half_setLocal, Locals.half_values]; omega)) ?_
    let s2a := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
      (.i64 (right.denote funs env))
    let s2b := setLocal { s2a with values := s.values } base (.i64 (left.denote funs env))
    show wp m _ Q store2 s2b host
    have hLowA : ({ s2 with values := .i64 (left.denote funs env) :: s.values } :
        Locals).params.length ≤ base + 1 := by
      show s2.params.length ≤ base + 1; rw [hp2]; omega
    have hLowB : ({ s2a with values := s.values } : Locals).params.length ≤ base := by
      show s2.params.length ≤ base; rw [hp2]; omega
    have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote funs env)) := by
      rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]
      exact Locals.get_setLocal_same hLowA
        (Locals.lt_total (by simp only [Locals.half_values]; omega))
    have hLeftSlot : s2b.get base = some (.i64 (left.denote funs env)) :=
      Locals.get_setLocal_same hLowB
        (Locals.lt_total (by simp only [s2a, Locals.half_setLocal, Locals.half_values]; omega))
    have hF2 : Frame base s2 s2b :=
      (Frame.setValues (s := s2) (vs := .i64 (left.denote funs env) :: s.values)
        (v := .i64 (right.denote funs env)) (by rw [hp2]; omega) (by omega) (by omega)).trans
        (Frame.setValues (s := s2a) (vs := s.values) (v := .i64 (left.denote funs env))
          (by show s2.params.length ≤ base; rw [hp2]; omega) le_rfl
          (by simp only [s2a, Locals.half_setLocal, Locals.half_values]; omega))
    have hFrame : Frame base s s2b := hF.trans hF2
    have hHolds : Holds env slots live base heap2 store2 s2b := hH.agree hF2
    have hs2b : s2b.values = s.values := rfl
    simp only [wp_localGet_cons, hRightSlot, wp_eqzI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : right.denote funs env = 0
    · simp only [hZero, ite_true, ne_eq]
      simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
    · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
      simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
  all_goals
    simpa [BinOp.code, Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
      ← UInt64.shiftRight_eq_shiftRight_mod] using
      hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- A comparison of words. -/
theorem specB_cmp {Γ : List Ty} (op : CmpOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.cmp op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op <;>
    simp only [CmpOp.instr, wp_eqI64_cons, wp_neI64_cons, wp_ltUI64_cons, wp_leUI64_cons,
      wp_extendUI32_cons]
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env < right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env ≤ right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv


/-- An operation on floats. -/
theorem specB_fbin {Γ : List Ty} (op : FBinOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.fbin op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 [.f64 ((Expr.fbin op left right).denote funs env).toBits]
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simpa [FBinOp.instr, Expr.denote, FBinOp.apply, f64Add, f64Sub, f64Mul, f64Div,
      F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div] using hv


/-- A comparison of floats. -/
theorem specB_fcmp {Γ : List Ty} (op : FCmpOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.fcmp op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simp only [FCmpOp.instr, wp_f64Lt_cons, wp_f64Le_cons, wp_f64Eq_cons, wp_extendUI32_cons]
  · cases hc : IEEE64.lt (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_lt, f64Lt, boolWord] using hv
  · cases hc : IEEE64.le (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_le, f64Le, boolWord] using hv
  · cases hc : IEEE64.eq (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.beq_eq, f64Eq, boolWord] using hv


/-- An operation on one float.  The negation subtracts from negative zero, pushed first. -/
theorem specB_funary {Γ : List Ty} (op : FUnOp) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.funary op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code]
  cases op with
  | neg =>
    simp only [FUnOp.code, List.cons_append, List.append_assoc, wp_f64Const_cons]
    refine eSpec env slots live h base heap store { s with values := .f64 0x8000000000000000 ::
      s.values } hh hpv (hVars.agree Frame.ofValues) hAt hCap hBase hRoom hPlace _ _ hTrap
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f64 (-(e.denote funs env)).toBits]
      (After.ofValues (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl))
    simpa [Expr.denote, FUnOp.apply, f64Sub, F64Bits.toBits_neg] using hv
  | sqrt | abs =>
    simp only [FUnOp.code, List.append_assoc, List.cons_append, List.nil_append]
    refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
        hTrap
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f64 ((Expr.funary _ e).denote funs env).toBits]
      (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
    simpa [Expr.denote, FUnOp.apply, f64Sqrt, f64Abs, F64Bits.toBits_sqrt, F64Bits.toBits_abs]
      using hv


/-- A conversion of a word to a float. -/
theorem specB_toFloat {Γ : List Ty} (op : ToFloat) {e : Expr S Γ .word}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.toFloat op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR : ws = [.i64 (e.denote funs env)] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.f64 ((Expr.toFloat op e).denote funs env).toBits]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToFloat.code, Expr.denote, ToFloat.apply, f64ConvertI64U, f64Add,
      F64Convert.toBits_toFloat, F64Bits.toBits_ofBits, add_negZero] using hv


/-- A conversion of a float to a word. -/
theorem specB_toWord {Γ : List Ty} (op : ToWord) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.toWord op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.i64 ((Expr.toWord op e).denote funs env)]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToWord.instr, Expr.denote, ToWord.apply, i64TruncSatF64U, F64Convert.toUInt64_eq]
      using hv


/-- The negation of a `Bool`. -/
theorem specB_not {Γ : List Ty} {e : Expr S Γ .bool}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.not e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR := a1.rep
  simp only [Ty.rep_bool] at hR
  subst hR
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons, wp_extendUI32_cons, boolWord_not]
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  simpa [Expr.denote] using
    hNext1 store1 s1 _ (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)


/-- The conjunction of `Bool`s. -/
theorem specB_and {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.and left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_andI64_cons, boolWord_and]
  simpa [Expr.denote] using hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- The disjunction of `Bool`s. -/
theorem specB_or {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.or left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_orI64_cons, boolWord_or]
  simpa [Expr.denote] using hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- A tuple of two elements: the code of each, in order. -/
theorem specB_mk {Γ : List Ty} {a b : Elem} {first : Expr S Γ (.elem a)}
    {second : Expr S Γ (.elem b)}
    (firstSpec : ∀ env slots live, CodeSpecB m funs bounds host pv first env slots live)
    (secondSpec : ∀ env slots live, CodeSpecB m funs bounds host pv second env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.mk first second) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have hR : second.width ≤ max first.width second.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB firstSpec secondSpec env slots live h base heap store s hh hpv hVars hAt hCap
      hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = a.values (first.denote funs env) := hR1
  have hR2' : ws2 = b.values (second.denote funs env) := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2
    (a.values (first.denote funs env) ++ b.values (second.denote funs env))
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simpa [List.reverse_append, List.append_assoc] using hv


/-- A variable: read in place when borrowed, moved where it dies, and copied where it stays
live. -/
theorem specB_var (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.var (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom _ rest Q hTrap hNext
  have hx : (fun i => live i || (Expr.var (S := S) x).uses i) x.index = true := by
    simp [Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  have hl := hRep.length
  have hMode : (Expr.var (S := S) x).mode (slots.map Slot.mode) =
      (slots.getD x.index default).mode := Slot.modes_getD slots x.index
  have hLiveIn : ∀ i, live i = true → (live i || (Expr.var (S := S) x).uses i) = true :=
    fun i h => by simp [h]
  by_cases hCopy : (slots.getD x.index default).mode = .owned ∧ live x.index = true
  · -- A copy into new blocks.
    obtain ⟨hOwned, hLiveX⟩ := hCopy
    simp only [Expr.code, Var.code, hOwned, hLiveX, and_self, ↓reduceIte]
    have hc : (Expr.var (S := S) x).allocs funs bounds (slots.map Slot.mode) live env =
        tTy.copyCost (env.get x) := by
      simp only [Expr.allocs, Var.cost, modeAt, Slot.modes_getD, hOwned, hLiveX, and_self,
        ↓reduceIte]
    have hT : TrapOK (false || (true && !decide (heap.Within store m (tTy.copyCost (env.get x)))))
        Q := hTrap.part nofun (fun _ => by simp [Slot.any_owned hOwned])
      fun _ hw => by rwa [hc] at hw
    refine wp_copyCode hm tTy hAt hCap hT hh hRep hold hBelow hBase
      (by rw [hh]; simpa [Expr.width] using hRoom) fun heap' store' s' ws' hStep hRep' hF hTop => ?_
    have hHolds := (hVars.live_mono hLiveIn).step hStep (fun _ _ _ _ _ _ _ _ => trivial)
    refine hNext heap' store' s' ws' ⟨?_, hF, hHolds.frame hF le_rfl, ?_, ?_⟩
      (fun _ => by rw [hc]; exact hTop)
    · rw [hMode, hOwned]
      exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · rw [hMode, hOwned]; exact hRep'
    · rw [hMode, hOwned]
      intro u y hy _ wy hwy hly b hb c hc
      have hwy' := ((hVars.live_mono hLiveIn).hold_agree hF hy hly).mp
        hwy
      obtain ⟨hSame, hFresh⟩ := (hVars.live_mono hLiveIn).regions_after hStep hy hwy' hly
        fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · simp only [Expr.code, Var.code, hCopy, ↓reduceIte]
    by_cases hOwned : (slots.getD x.index default).mode = .owned
    · -- A move: the variable dies here, and the value owns its blocks.
      have hDead : live x.index = false := by
        cases h : live x.index
        · rfl
        · exact absurd ⟨hOwned, h⟩ hCopy
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws ⟨?_, Frame.refl base s,
        hVars.live_mono hLiveIn, ?_, ?_⟩ fun _ => Nat.le_add_right _ _)
      · rw [hMode, hOwned]
        exact ⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr,
          fun b hb => hk tTy x hx hDead hOwned ws hold hl b hb⟩⟩
      · rw [hMode]; exact hRep
      · rw [hMode, hOwned]
        intro u y hy _ wy hwy hly b hb c hc
        have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
        exact hVars.2 tTy u x y hx (hLiveIn _ hy) hne hOwned ws wy hold hl hwy hly b hb c hc
    · -- A view of a borrowed variable.
      have hBorrowed : (slots.getD x.index default).mode = .borrowed := by
        cases h : (slots.getD x.index default).mode
        · rfl
        · exact absurd h hOwned
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws (After.refl hAt hVars hLiveIn
        (by rw [hMode]; exact hRep) (by rw [hMode, hBorrowed]; rfl) ?_)
        fun _ => Nat.le_add_right _ _)
      rw [hMode]
      intro u y hy hm wy hwy hly b hb c hc
      rcases hm with hm | hm
      · exact absurd hm hOwned
      · have hne : y.index ≠ x.index := fun he => by
          rw [he] at hm; exact hOwned hm
        rw [hm] at hc
        exact regionsDisjoint_symm
          (hVars.2 u tTy y x (hLiveIn _ hy) hx hne hm wy ws hwy hly hold hl c hc b hb)


/-- The release of an array variable that a reader reads, when it is owned and dies there,
which leaves `top`. -/
theorem read_releaseT (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    {vals : List Value} {rest : Program} {Q : Assertion Unit} {e : Elem} (x : Var Γ (.array e))
    (hVars : Holds env slots (fun k => live k || k == x.index) base heap store s)
    (hAt : heap.At store)
    (hNext : ∀ heap' store', Evolves env slots (fun k => live k || k == x.index) live base heap
      store s heap' store' s → heap'.top = heap.top →
      wp m rest Q store' { s with values := vals } host) :
    wp m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode (.array e) (slots.getD x.index default).loc else []) ++ rest) Q store
      { s with values := vals } host := by
  have hCode : (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode (.array e) (slots.getD x.index default).loc else []) =
      (if live x.index = false then [x.index] else []).flatMap (releaseVar Γ slots) := by
    cases live x.index <;> simp [releaseVar, x.getElem?_index]
  rw [hCode]
  refine wp_releaseVarsT hm _ (by split <;> simp) (hVars.agree Frame.ofValues) hAt
    (by split <;> simp) fun heap' store' e hTop => hNext heap' store' ?_ hTop
  have e' := e.mono (live' := live) fun k h => by
    split
    · next hx =>
      have hne : k ≠ x.index := fun he => by rw [he, hx] at h; exact nomatch h
      simp [h, hne]
    · simp [h]
  exact ⟨e'.step, ⟨e'.frame.params, e'.frame.length, e'.frame.below⟩,
    e'.holds.agree Frame.ofValues⟩

/-- The size of an array variable: the load of its length word, then the release of the variable
when it is owned and dies there. -/
theorem specB_size (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e)) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.size (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  obtain ⟨ptr, rfl, hB⟩ := hRep
  have hA := hB.borrow.values
  have hLength := hA.lengthBound
  have hPtr : s.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word hold
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hPtr, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode e.width_pos,
    words_div e.width_pos hnk]
  refine read_releaseT hm x hVars hAt fun heap' store' ev hTop => ?_
  exact hNext heap' store' s [.i64 (env.get x).size.toUInt64]
    (After.ofScalar rfl ev.step rfl ev.frame ev.holds rfl) fun _ => by rw [hTop]; omega

/-- A read of an array variable: the position in local `base`, a comparison of it with the
array's size as a flag in local `base + 1`, the position of the element's first word in local
`base`, the loads of its words under the flag, and the release of the variable when it is owned and
dies there. -/
theorem specB_get (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots live, CodeSpecB m funs bounds host pv i env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.get x i) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi : i.width ≤ max i.width 2 := Nat.le_max_left ..
  have h2 : 2 ≤ max i.width 2 := Nat.le_max_right ..
  simp only [Expr.placeArgs] at hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.get x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace _ _
    hTrap fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  obtain ⟨hBelowX, wx, holdx, hRepx⟩ := e1.holds.1 _ x (by simp)
  obtain ⟨ptr, rfl, hBx⟩ := hRepx
  have hA := hBx.borrow.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hk := e.width_pos
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  simp only [Ty.width] at hBelowX
  have hPtr1 : s1.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word holdx
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  -- The position, in local `base`.
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHigh1 : base < s1.half := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  let s1a := setLocal { s1 with values := s.values } base (.i64 (i.denote funs env))
  have hK : s1a.get base = some (.i64 (i.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hP : s1a.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]
    exact hPtr1
  show wp m _ Q store1 s1a host
  simp only [wp_localGet_cons, Locals.get_values, hK, hP, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode hk,
    words_div hk hnk]
  simp only [wp_ltUI64_cons, wp_extendUI32_cons]
  -- The flag, in local `base + 1`.
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  set b := decide ((i.denote funs env).toNat < (env.get x).size) with hb
  have hFlag : UInt64.ofNat (if i.denote funs env < UInt64.ofNat (env.get x).size then (1 : UInt32)
      else 0).toNat = boolWord b := by
    by_cases hc : (i.denote funs env).toNat < (env.get x).size
    · simp [hb, hc, hLess.mpr hc, boolWord]
    · simp [hb, hc, (not_congr hLess).mpr hc, boolWord]
  rw [hFlag]
  have hLowB : ({ s1a with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s1.params.length ≤ base + 1; rw [hp1]; omega
  have hHighB : base + 1 < ({ s1a with values := s.values } : Locals).half := by
    simp only [s1a, Locals.half_setLocal, Locals.half_values, hh1]; omega
  refine wp_localSet_local hLowB (Locals.lt_total hHighB) ?_
  let s1b := setLocal { s1a with values := s.values } (base + 1) (.i64 (boolWord b))
  have hFb : s1b.get (base + 1) = some (.i64 (boolWord b)) :=
    Locals.get_setLocal_same hLowB (Locals.lt_total hHighB)
  have hKb : s1b.get base = some (.i64 (i.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hK
  have hPb : s1b.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hP
  -- The position of the element's first word, in local `base`.
  show wp m _ Q store1 s1b host
  simp only [wp_localGet_cons, hKb]
  rw [wp_scaleCode]
  have hLowC : ({ s1b with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHighC : base < ({ s1b with values := s.values } : Locals).half := by
    simp only [s1b, s1a, Locals.half_setLocal, Locals.half_values, hh1]; omega
  refine wp_localSet_local hLowC (Locals.lt_total hHighC) ?_
  let s1c := setLocal { s1b with values := s.values } base
    (.i64 (i.denote funs env * wordCount e.width))
  have hWc : s1c.get base = some (.i64 (i.denote funs env * wordCount e.width)) :=
    Locals.get_setLocal_same hLowC (Locals.lt_total hHighC)
  have hFc : s1c.get (base + 1) = some (.i64 (boolWord b)) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hFb
  have hPc : s1c.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hPb
  have f1 : Frame base s1 s1c :=
    ((Frame.setValues (s := s1) (vs := s.values) hLow1 le_rfl hHigh1).trans
      (Frame.setValues (s := s1a) (vs := s.values) hLowB (by omega)
        (by simpa [s1a, Locals.half_setLocal, Locals.half_values] using hHighB))).trans
      (Frame.setValues (s := s1b) (vs := s.values) hLowC le_rfl
        (by simpa [s1b, s1a, Locals.half_setLocal, Locals.half_values] using hHighC))
  have hFrame : Frame base s s1c := e1.frame.trans f1
  have hVars1 : Holds env slots (fun k => live k || k == x.index) base heap1 store1 s1c :=
    e1.holds.agree f1
  have hsc : s1c.values = s.values := rfl
  -- The words of the element, or zeros past the end.
  show wp m _ Q store1 s1c host
  refine wp_loadWordsCode (ws := e.words (env.get x)) b (fun _ => hA) 0 e.types s1c
    (e.toWords (env.get x)[(i.denote funs env).toNat]!) hPc hWc hFc
    (by rw [e.toWords_length, e.types_length]) (fun hbt => ?_) (fun hbf => ?_) ?_
  · have hc : (i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbt
    have hw : (i.denote funs env * wordCount e.width).toNat =
        (i.denote funs env).toNat * e.width := by
      have hs := words_scale (i := (i.denote funs env).toNat) hk
        (lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hc)) hnk)
      rw [UInt64.ofNat_toNat] at hs
      rw [hs, UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 18446744073709551616 from rfl]
          have := Nat.mul_le_mul_right e.width (Nat.le_of_lt hc); omega)]
    rw [hw, e.types_length, Elem.words_size]
    refine ⟨by
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
        rw [Nat.succ_mul] at this; omega,
      fun j hj => ?_⟩
    rw [e.toWords_length] at hj
    rw [Nat.add_zero, Elem.words_getElem! e _ hc hj, getElem!_pos (env.get x) _ hc]
  · have hc : ¬(i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbf
    rw [getElem!_neg (env.get x) _ hc, e.toWords_default, e.types_length]
  · rw [e.values_typed, hsc]
    refine read_releaseT hm x hVars1 e1.step.at_ fun heap2 store2 e2 hTop2 => ?_
    have e12 := Evolves.trans (hVars.live_mono hIn) ⟨e1.step, hFrame, hVars1⟩ e2
      (fun k h => by simp [h]) fun k h => by simp [h]
    exact hNext heap2 store2 s1c (e.values (env.get x)[(i.denote funs env).toNat]!)
      ((After.ofScalar (t := .elem e) (mode := .borrowed) rfl e12.step rfl e12.frame e12.holds
        rfl).liveIn hIn) fun hd => by rw [hTop2]; exact hTop1 hd

/-- A component of a tuple variable: the loads of the words that hold it. -/
theorem specB_proj {Γ' : List Ty} {e e' : Elem} (x : Var Γ' (.elem e)) (p : Path e e') :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.proj (S := S) x p) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hRep' : ws = e.values (env.get x) := hRep
  subst hRep'
  simp only [Expr.code]
  exact wp_loadCode _ (by rw [e'.values_length, e'.types_length]) hh (p.holds hold)
    (hNext heap store s _ (After.refl hAt hVars (by intro i h; simp [Expr.uses, h]) rfl rfl
      (Holds.Apart.ofScalar rfl)) fun _ => Nat.le_add_right _ _)

/-- A value turned from mode `source` into mode `target` after an expression's code: a borrowed
value that must be owned is copied into new blocks, which raises `top` by at most `coerceCost t source target v`, and the
facts of `After` carry over. -/
theorem After.coerceB (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {h base base' : Nat} {heap : Heap} {store : Store Unit}
    {s : Locals} {t : Ty} {source target : Mode} {v : t.denote} {heap1 : Heap}
    {store1 : Store Unit} {s1 : Locals} {ws vs : List Value} {rest : Program}
    {Q : Assertion Unit}
    (a : After env slots liveIn live base heap store s t source v heap1 store1 s1 ws)
    (hTarget : source = .owned → target = .owned) (hBase' : base ≤ base')
    (hLow : s1.params.length ≤ base') (hh : s1.half = h) (hRoom : base' + copyWidth t ≤ h)
    (hCap : store1.memoryCap m 0 ≤ 65535)
    (hTrap : source = .borrowed → target = .owned → t.scalar = false →
      TrapOK (!decide (heap1.Within store1 m (t.copyCost v))) Q)
    (hNext : ∀ heap2 store2 s2 ws2,
      After env slots liveIn live base heap store s t target v heap2 store2 s2 ws2 →
      heap2.top.toNat ≤ heap1.top.toNat + coerceCost t source target v →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ vs } host) :
    wp m (coerceCode h t source target base' ++ rest) Q store1
      { s1 with values := ws.reverse ++ vs } host := by
  by_cases hCopy : source = .borrowed ∧ target = .owned ∧ t.scalar = false
  · obtain ⟨hs, ht, hScalar⟩ := hCopy
    subst hs ht
    have hW : copyWidth t = t.width + 3 := by simp [copyWidth, hScalar]
    simp only [coerceCode, and_self, hScalar, ↓reduceIte, List.append_assoc]
    refine wp_storeCode ws h base' t.types s1 vs a.rep.typed hh hLow
      (by rw [Ty.types_length, hh]; omega) fun s2 hF2 hold2 _ => ?_
    refine wp_copyCode hm t a.step.at_ hCap (hTrap rfl rfl hScalar)
      (hF2.half.trans hh) a.rep
      hold2 (le_refl _) (by rw [hF2.params]; omega)
      (by simp only [Locals.half_values, hF2.half, hh, Ty.copyScratch, hScalar,
        Bool.false_eq_true, ↓reduceIte]; omega)
      fun heap3 store3 s3 ws3 hStep3 hRep3 hF3 hTop3 => ?_
    have hF13 : Frame base s1 s3 :=
      (hF2.mono hBase').trans (Frame.ofValues.trans (hF3.mono (by omega)))
    have hF : Frame base s s3 := a.frame.trans hF13
    have hStep0 := a.step
    simp only [Mode.fresh] at hStep0
    refine hNext heap3 store3 s3 ws3 ⟨?_, hF, ?_, hRep3, ?_⟩ (by simpa [coerceCost] using hTop3)
    · exact hStep0.trans hStep3 fun _ hr => ⟨hr, fun _ => trivial⟩
    · exact (a.holds.step hStep3 fun _ _ _ _ _ _ _ _ => trivial).agree hF13
    · intro u y hy _ wy hwy hly b hb c hc
      have hwy' := (a.holds.hold_agree hF13 hy hly).mp hwy
      obtain ⟨hSame, hFresh⟩ := a.holds.regions_after hStep3 hy hwy' hly fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · have hEmpty : coerceCode h t source target base' = [] := by
      simp only [coerceCode]; rw [ite_eq_right hCopy]
    rw [hEmpty, List.nil_append]
    -- No copy: the modes agree, or the type holds no arrays.
    have hSame : source = target ∨ t.scalar = true := by
      cases source <;> cases target <;> simp_all
    rcases hSame with rfl | hScalar
    · exact hNext heap1 store1 s1 ws a (Nat.le_add_right _ _)
    · refine hNext heap1 store1 s1 ws ⟨?_, a.frame, a.holds, ?_, ?_⟩ (Nat.le_add_right _ _)
      · have hStep := a.step
        rw [Mode.fresh_scalar hScalar] at hStep ⊢
        exact hStep
      · cases target
        · exact a.rep.borrow
        · exact a.rep.owned hScalar
      · intro u y hy hm wy hwy hly b hb
        rw [Ty.regions_scalar t hScalar] at hb
        exact nomatch hb

/-- The allowance of an allocation of a part, from that of the whole, which may allocate. -/
theorem _root_.Wasm.TrapOK.alloc {Q : Assertion Unit} {d a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (d || (a && !decide P)) Q) (ha : a = true)
    (hP : d = false → P → P') : TrapOK (!decide P') Q :=
  h.part (d' := false) (a' := true) nofun (fun _ => ha) hP

/-- One branch of an `if`, after the condition: the releases of the owned variables that die at
its entry, its code, the coercion of its value to the `if`'s mode, and the store of its words,
which the code loads after the `if`. -/
theorem ite_branchB (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE b : Expr S Γ' tTy}
    (bSpec : ∀ env slots live, CodeSpecB m funs bounds host pv b env slots live)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.half = h)
    (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) base heap
      store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomB : base + tTy.width + max b.width (copyWidth tTy) ≤ h)
    {B cA : Nat}
    (hTrap : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) live base heap store s
        tTy ((Expr.ite c thenE elseE).mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).denote funs env) heap' store' s' ws →
      ((Expr.ite c thenE elseE).depthCalls = false → heap'.top.toNat ≤ heap.top.toNat + B) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host)
    {heap1 : Heap} {store1 : Store Unit} {s1 : Locals}
    (e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values })
    (hTop1 : (Expr.ite c thenE elseE).depthCalls = false → heap1.top.toNat ≤ heap.top.toNat + cA)
    (hB : B = cA + (b.allocs funs bounds (slots.map Slot.mode) live env +
      coerceCost tTy (b.mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (b.denote funs env)))
    (hbd : b.depthCalls = true → (Expr.ite c thenE elseE).depthCalls = true)
    (hbPlace : b.placeArgs = true)
    (hbu : ∀ i, b.uses i = true → (thenE.uses i || elseE.uses i) = true)
    (hba : b.aborts = true → (Expr.ite c thenE elseE).aborts = true)
    (hval : b.denote funs env = (Expr.ite c thenE elseE).denote funs env)
    (hbm : b.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned)
    (Qb : Assertion Unit) (hQbTrap : ∀ st, Q (.Trap st "unreachable") → Qb (.Trap st "unreachable"))
    (hQb : ∀ st' s', wp m (loadCode h base tTy.types ++ rest) Q st'
      { s' with values := s.values } host → Qb (.Fallthrough st' s')) :
    wp m (releaseWhere Γ' slots (fun i => (live i || thenE.uses i || elseE.uses i) &&
        !(live i || b.uses i)) ++
      (b.code h slots (base + tTy.width) live ++
        (coerceCode h tTy (b.mode (slots.map Slot.mode))
          ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (base + tTy.width) ++
          storeCode h base tTy.types))) Qb store1 { s1 with values := s.values } host := by
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  have hTrapB : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B) Qb :=
    hTrap.imp hQbTrap
  have hbd' : (Expr.ite c thenE elseE).depthCalls = false → b.depthCalls = false := fun hd => by
    cases hb : b.depthCalls
    · rfl
    · rw [hbd hb] at hd; exact nomatch hd
  have hSubMid : ∀ i, (live i || b.uses i) = true →
      (live i || thenE.uses i || elseE.uses i) = true := fun i =>
    ite_live_branch _ _ _ _ (hbu i)
  refine wp_releaseWhereT hm e1.holds e1.step.at_
    (fun i h => by simp only [Bool.and_eq_true] at h; exact h.1) fun heap2 store2 e2 hTop2 => ?_
  have hEq : (fun i => (live i || thenE.uses i || elseE.uses i) &&
      !((live i || thenE.uses i || elseE.uses i) && !(live i || b.uses i))) =
      (fun i => live i || b.uses i) := by
    funext i
    exact live_released _ _ (hSubMid i)
  rw [hEq] at e2
  rw [← List.append_nil (storeCode h base tTy.types)]
  have hbw := Nat.le_max_left b.width (copyWidth tTy)
  have hcw := Nat.le_max_right b.width (copyWidth tTy)
  refine bSpec env slots live h (base + tTy.width) heap2 store2 { s1 with values := s.values }
    hh1 (hp1.trans hpv) (e2.holds.mono (by omega)) e2.step.at_
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base + tTy.width; rw [hp1]; omega)
    (by omega) hbPlace _ _ (hTrapB.part hbd (fun h => by
          simp only [Bool.or_eq_true] at h ⊢; exact h.imp_left hba) fun hd hw => by
        rw [hB] at hw
        exact (hw.after (heap1 := heap2) (store1 := store2)
          (by have := hTop1 hd; have := congrArg UInt64.toNat hTop2; omega)
          (by rw [e2.step.cap m, e1.step.cap m])).mono (Nat.le_add_right _ _))
    fun heap3 store3 s3 ws3 a3 hTop3 => ?_
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hh3 : s3.half = h := a3.frame.half.trans hh1
  refine After.coerceB hm a3 hbm le_rfl (by rw [hp3]; omega) hh3 (by omega)
    (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m]; exact hCap)
    (fun hs ht _ => hTrapB.alloc (by
      have := (Expr.ite c thenE elseE).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this; exact this) fun hd hw => by
        rw [hB, ← Nat.add_assoc] at hw
        have h3 := hw.after (heap1 := heap3) (store1 := store3)
          (c1 := cA + b.allocs funs bounds (slots.map Slot.mode) live env)
          (by have := hTop3 (hbd' hd); have := hTop1 hd; have := congrArg UInt64.toNat hTop2; omega)
          (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m])
        simpa [coerceCost, hs, ht] using h3)
    fun heap4 store4 s4 ws4 a4 hTop4 => ?_
  have hp4 : s4.params = s.params := a4.frame.params.trans hp1
  have hh4 : s4.half = h := a4.frame.half.trans hh1
  refine wp_storeCode ws4 h base tTy.types s4 s.values a4.rep.typed hh4 (by rw [hp4]; omega)
    (by rw [Ty.types_length, hh4]; omega) fun s5 hF5 hold _ => ?_
  rw [wp_nil]
  refine hQb _ _ (wp_loadCode ws4 a4.rep.typed (hF5.half.trans hh4) hold ?_)
  -- The `if`'s facts: the evolutions of the condition and the releases, then the branch.
  have hLower := a4.lower e2.holds (Nat.le_add_right _ _) (fun i h => by simp [h])
  have hEntry : ∀ i, (live i || thenE.uses i || elseE.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact ite_live_entry _ _ _ _ h
  have e12 := Evolves.trans hVars e1 e2 hSubMid hEntry
  have aAll := After.prepend hVars e12 hLower (fun i h => hEntry i (hSubMid i h))
    (fun i h => by simp [h])
  have hF45 : Frame base s4 { s5 with values := s.values } := hF5.trans Frame.ofValues
  have hFrame : Frame base s { s5 with values := s.values } := aAll.frame.trans hF45
  rw [hval] at aAll
  refine hNext heap4 store4 _ ws4 ⟨aAll.step, hFrame, aAll.holds.agree hF45, aAll.rep, ?_⟩
    fun hd => by
      have := hTop1 hd; have := hTop3 (hbd' hd); have := congrArg UInt64.toNat hTop2
      have := congrArg UInt64.toNat hTop2
      rw [hB]; omega
  exact aAll.apart.agree aAll.holds hF45

/-- An `if`: the condition, then each branch as `ite_branchB` describes. -/
theorem specB_ite (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE : Expr S Γ' tTy}
    (cSpec : ∀ env slots live, CodeSpecB m funs bounds host pv c env slots live)
    (thenSpec : ∀ env slots live, CodeSpecB m funs bounds host pv thenE env slots live)
    (elseSpec : ∀ env slots live, CodeSpecB m funs bounds host pv elseE env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.ite c thenE elseE) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc : c.width ≤ max c.width (tTy.width + max (max thenE.width elseE.width)
      (copyWidth tTy)) := Nat.le_max_left ..
  have hb : tTy.width + max (max thenE.width elseE.width) (copyWidth tTy) ≤
      max c.width (tTy.width + max (max thenE.width elseE.width) (copyWidth tTy)) :=
    Nat.le_max_right ..
  have ht : thenE.width ≤ max thenE.width elseE.width := Nat.le_max_left ..
  have he : elseE.width ≤ max thenE.width elseE.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨hPlaceC, hPlaceT⟩, hPlaceE⟩ := hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hMid : ∀ i, ((live i || thenE.uses i || elseE.uses i) || c.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := by
    intro i h; simp only [Expr.uses]; exact ite_live_cond _ _ _ _ h
  refine cSpec env slots _ h base heap store s hh hpv (hVars.live_mono hMid) hAt hCap hBase
    (by omega) hPlaceC _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact ite_trap_cond _ _ _ _ h)
      fun _ hw => hw.mono (by simp only [Expr.allocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_bool] at hR1
  subst hR1
  have e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values } := by
    have e := (a1.toEvolves rfl).values s.values
    exact ⟨e.step.mono (fun r hr => hr.mono fun i h1 h2 => ⟨hMid i h1, h2⟩) fun _ h => h,
      e.frame, e.holds⟩
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hModeT : thenE.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned :=
    fun h => by simp [Expr.mode, h, Mode.join]
  have hModeE : elseE.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned := fun h => by
    simp only [Expr.mode, h]
    cases thenE.mode (slots.map Slot.mode) <;> rfl
  have hRoomT : base + tTy.width + max thenE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨ht.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  have hRoomE : base + tTy.width + max elseE.width (copyWidth tTy) ≤ h := by
    have := Nat.max_le.mpr ⟨he.trans (Nat.le_max_left _ (copyWidth tTy)), Nat.le_max_right _ _⟩
    omega
  cases hcv : c.denote funs env
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branchB hm elseSpec hh hpv hVars hCap hBase hRoomE hTrap hNext e1
      (fun hd => hTop1 (by simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1.1))
      (by simp only [Expr.allocs, Expr.mode, hcv, Bool.false_eq_true, ↓reduceIte])
      (fun h => by simp [Expr.depthCalls, h]) hPlaceE
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeE _ (fun _ h => h) fun _ _ h => by simpa using h
  · simp (config := { decide := true }) only [↓reduceIte]
    exact ite_branchB hm thenSpec hh hpv hVars hCap hBase hRoomT hTrap hNext e1
      (fun hd => hTop1 (by simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1.1))
      (by simp only [Expr.allocs, Expr.mode]; rw [if_pos hcv])
      (fun h => by simp [Expr.depthCalls, h]) hPlaceT
      (fun i h => by simp [h]) (fun h => by simp [Expr.aborts, h])
      (by simp [Expr.denote, hcv]) hModeT _ (fun _ h => h) fun _ _ h => by simpa using h

/-- A `let` binding: the value's code, the store of its words from local `base` on, the release
of the value when it is owned and the body does not use it, and the body's code. -/
theorem specB_letE (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy}
    (valueSpec : ∀ env slots live, CodeSpecB m funs bounds host pv value env slots live)
    (bodySpec : ∀ env slots live, CodeSpecB m funs bounds host pv body env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.letE value body) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
  have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 1)) || value.uses i) = true →
      (live i || (Expr.letE value body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine valueSpec env slots (fun i => live i || body.uses (i + 1)) h (base + sTy.width) heap
    store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt hCap (by omega) (by omega) hPlace.1 _
        _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by simp only [Expr.allocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.half = h := a1.frame.half.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (Nat.le_add_right _ _) fun i h => by simp [h]
  refine wp_storeCode ws1 h base sTy.types s1 s.values a1.rep.typed hh1 (by rw [hp1]; omega)
    (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold _ => ?_
  have f2 : Frame base s1 { s2 with values := s.values } := hF2.trans Frame.ofValues
  have hp2 : s2.params = s.params := hF2.params.trans hp1
  have hh2 : ({ s2 with values := s.values } : Locals).half = h := f2.half.trans hh1
  have hold' : LocalsHold { s2 with values := s.values } base sTy.types ws1 := hold
  -- The body's context: the value as variable 0, in the locals from `base` on.
  have hVarsB : Holds (Env.cons (value.denote funs env) env)
      (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => i == 0 || shift 1 live i || body.uses i) (base + sTy.width) heap1 store1
      { s2 with values := s.values } :=
    Holds.push ((a1'.holds.agree f2).live_mono fun i h => by
        simpa using h)
      hold' a1.rep ((a1'.apart.agree a1'.holds f2).live_mono
        fun i h => by simpa using h)
  have hRelease : (if value.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
      releaseCode sTy base else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (sTy :: Γ') (⟨base, value.mode (slots.map Slot.mode)⟩ :: slots)) := by
    cases body.uses 0 <;> cases value.mode (slots.map Slot.mode) <;> simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letE value body).depthCalls = false → value.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  have hd3 : (Expr.letE value body).depthCalls = false → body.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.2
  refine wp_releaseVarsT hm _ (by split <;> simp) hVarsB a1.step.at_ (by split <;> simp)
    fun heap2 store2 e2 hTop2 => ?_
  have e2' := e2.mono (live' := fun i => shift 1 live i || body.uses i) fun i h => by
    cases i with
    | zero =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | succ k => split <;> simpa using h
  refine bodySpec _ _ (shift 1 live) h (base + sTy.width) heap2 store2
    { s2 with values := s.values } hh2 (hp2.trans hpv) e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s2.params.length ≤ base + sTy.width; rw [hp2]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := value.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        simp only [Expr.allocs] at hw
        exact hw.after (heap1 := heap2) (store1 := store2)
          (by have := hTop1 (hd1 hd); have := congrArg UInt64.toNat hTop2; omega)
          (by rw [e2'.step.cap m, a1.step.cap m]))
    fun heap3 store3 s3 ws3 aB hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  exact hNext heap3 store3 s3 ws3
    ((After.bind (hVars.live_mono hV) a1' f2 hold' aB' (fun i h => by simpa using h)
      (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV) fun hd => by
      have := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      simp only [List.map_cons] at h3
      simp only [Expr.allocs]; omega

/-- An allowance for a trap when `top` cannot rise by a charge gives the allowance of a part
that takes no call depth and whose room follows from the charge's. -/
theorem _root_.Wasm.TrapOK.narrow {Q : Assertion Unit} {a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (!decide P) Q) (hP : P → P') : TrapOK (false || (a && !decide P')) Q :=
  h.of_imp fun h' => by
    simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h' ⊢
    exact fun hp => h'.2 (hP hp)

/-- A variable in an owned position: its words as an owned value, which move it when it is owned
and dies, and a copy otherwise, which raises `top` by at most `x.ownedCost` and traps only when
`top` cannot rise by that much. -/
theorem specB_ownedVar (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.half = h)
    (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || i == x.index) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoom : base + copyWidth tTy ≤ h)
    (hTrap : TrapOK (!decide (heap.Within store m
      (x.ownedCost (slots.map Slot.mode) live (env.get x)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || i == x.index) live base heap store s tTy .owned
        (env.get x) heap' store' s' ws →
      heap'.top.toNat ≤ heap.top.toNat + x.ownedCost (slots.map Slot.mode) live (env.get x) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (x.ownedCode h slots base live ++ rest) Q store s host := by
  simp only [Var.ownedCode, List.append_assoc]
  have hScratch := tTy.copyScratch_le
  have hMode : modeAt (slots.map Slot.mode) x.index = (slots.getD x.index default).mode :=
    Slot.modes_getD slots x.index
  refine specB_var (S := []) (funs := .nil) (bounds := .nil) hm x env slots live h base heap store
      s hh hpv hVars hAt
    hCap hBase (by simp only [Expr.width]; omega) rfl _ _
    (hTrap.narrow fun hw => hw.mono (by simp only [Expr.allocs, Var.ownedCost]; omega))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hTop1' := hTop1 rfl
  simp only [Expr.allocs] at hTop1'
  rw [show (Expr.var (S := []) x).mode (slots.map Slot.mode) = (slots.getD x.index default).mode
    from Slot.modes_getD slots x.index] at a1
  exact After.coerceB hm a1 (fun _ => rfl) le_rfl (by rw [a1.frame.params]; exact hBase)
    (a1.frame.half.trans hh) (by omega) (by rw [a1.step.cap m]; exact hCap)
    (fun hs _ _ => hTrap.within fun hw => by
      have h2 := hw.after (heap1 := heap1) (store1 := store1)
        (c1 := x.cost (slots.map Slot.mode) live (env.get x))
        (c2 := coerceCost tTy (modeAt (slots.map Slot.mode) x.index) .owned (env.get x)) hTop1'
        (a1.step.cap m)
      simp only [coerceCost, hMode, hs, and_self, ↓reduceIte] at h2
      exact h2)
    fun heap2 store2 s2 ws2 a2 hTop2 => hNext heap2 store2 s2 ws2 a2 (by
      simp only [Expr.denote] at hTop2
      simp only [Var.ownedCost]; rw [hMode]; omega)

/-- A pair: the code of each component, each followed by its coercion to the pair's mode. -/
theorem specB_pair (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {first : Expr S Γ' sTy}
    {second : Expr S Γ' tTy}
    (firstSpec : ∀ env slots live, CodeSpecB m funs bounds host pv first env slots live)
    (secondSpec : ∀ env slots live, CodeSpecB m funs bounds host pv second env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.pair first second) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have h1 : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have h2 : second.width ≤ max first.width second.width := Nat.le_max_right ..
  have hc1 : copyWidth sTy ≤ max (copyWidth sTy) (copyWidth tTy) := Nat.le_max_left ..
  have hc2 : copyWidth tTy ≤ max (copyWidth sTy) (copyWidth tTy) := Nat.le_max_right ..
  have hw := Nat.le_max_left (max first.width second.width) (max (copyWidth sTy) (copyWidth tTy))
  have hc := Nat.le_max_right (max first.width second.width) (max (copyWidth sTy) (copyWidth tTy))
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hIn : ∀ i, ((live i || second.uses i) || first.uses i) = true →
      (live i || (Expr.pair first second).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hOwnedA : (Expr.pair first second).mode (slots.map Slot.mode) = .owned →
      ((Expr.pair first second).aborts || slots.any (·.mode == .owned)) = true := fun ht => by
    have := (Expr.pair first second).mode_owned (slots.map Slot.mode) ht
    rw [Slot.any_map] at this
    exact this
  have hdF : (Expr.pair first second).depthCalls = false → first.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  have hdS : (Expr.pair first second).depthCalls = false → second.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.2
  have hB : (Expr.pair first second).allocs funs bounds (slots.map Slot.mode) live env =
      first.allocs funs bounds (slots.map Slot.mode) (fun i => live i || second.uses i) env +
        coerceCost sTy (first.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (first.denote funs env) +
        second.allocs funs bounds (slots.map Slot.mode) live env +
        coerceCost tTy (second.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (second.denote funs env) := by
    simp only [Expr.allocs, Expr.mode]
  refine firstSpec env slots (fun i => live i || second.uses i) h base heap store s hh hpv
      hVarsL hAt
    hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by rw [hB]; omega))
    fun heap1 store1 s1 ws1 a1 hTopF => ?_
  refine After.coerceB hm a1 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a1.frame.params]; exact hBase) (a1.frame.half.trans hh) (by omega)
    (by rw [a1.step.cap m]; exact hCap) (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost sTy (first.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (first.denote funs env) =
          sTy.copyCost (first.denote funs env) := by rw [coerceCost, if_pos ⟨hs, ht⟩]
      exact hw.shift (c1 := first.allocs funs bounds (slots.map Slot.mode)
        (fun i => live i || second.uses i) env) (hTopF (hdF hd)) (by rw [hB]; omega)
        (a1.step.cap m))
    fun heap1 store1 s1 ws1 a1 hTopC1 => ?_
  refine secondSpec env slots live h base heap1 store1
    { s1 with values := ws1.reverse ++ s.values } (a1.frame.half.trans hh)
    (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues) a1.step.at_
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_right _ _ _ h)
      fun hd hw => hw.shift (heap1 := heap1) (store1 := store1)
        (c1 := first.allocs funs bounds (slots.map Slot.mode) (fun i => live i || second.uses i)
          env + coerceCost sTy (first.mode (slots.map Slot.mode)) ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
            (first.denote funs env))
        (by have := hTopF (hdF hd); have := hTopC1; omega) (by rw [hB]; omega) (a1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTopS => ?_
  refine After.coerceB hm a2 (fun h => by
      simp only [Mode.join, h]; cases first.mode (slots.map Slot.mode) <;> rfl) le_rfl
    (by rw [a2.frame.params, a1.frame.params]; exact hBase)
    (a2.frame.half.trans (a1.frame.half.trans hh)) (by omega)
    (by rw [a2.step.cap m, a1.step.cap m]; exact hCap)
    (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy (second.mode (slots.map Slot.mode))
          ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode))) (second.denote funs env) =
          tTy.copyCost (second.denote funs env) := by rw [coerceCost, if_pos ⟨hs, ht⟩]
      exact hw.shift (heap1 := heap2) (store1 := store2)
        (c1 := first.allocs funs bounds (slots.map Slot.mode) (fun i => live i || second.uses i)
          env + coerceCost sTy (first.mode (slots.map Slot.mode)) ((first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)))
            (first.denote funs env) + second.allocs funs bounds (slots.map Slot.mode) live env)
        (by have := hTopF (hdF hd); have := hTopC1; have := hTopS (hdS hd); omega)
        (by rw [hB]; omega)
        (by rw [a2.step.cap m, a1.step.cap m]))
    fun heap2 store2 s2 ws2 a2 hTopC2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  have hl1 := hRep1.length
  have hv := hNext heap2 store2 s2 (ws1 ++ ws2) ⟨by
      rw [Mode.fresh_pair hl1]
      exact hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb,
    hFrame, a2.holds, ⟨ws1, ws2, rfl, hRep1, a2.rep, fun hmo x hx y hy => by
      have hmo' : (first.mode (slots.map Slot.mode)).join (second.mode (slots.map Slot.mode)) =
          .owned := hmo
      rw [hmo'] at hDisjoint
      exact hDisjoint x hx y hy⟩, fun w y hy hmo wy hwy hly b hb c hc => by
      rw [Ty.regions_append hl1] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hApart1 w y hy hmo wy hwy hly b hb c hc
      · exact a2.apart w y hy hmo wy hwy hly b hb c hc⟩
      (fun hd => by
        have := hTopF (hdF hd); have := hTopC1; have := hTopS (hdS hd); have := hTopC2
        rw [hB]; omega)
  simpa [List.reverse_append, List.append_assoc] using hv

/-- A binding of a pair's components: the pair's code, the stores of its components' words, the
release of each component that is owned and that the body does not use, and the body's code. -/
theorem specB_letPair (hm : Runtime m) {Γ' : List Ty} {sTy tTy uTy : Ty}
    {e : Expr S Γ' (.pair sTy tTy)} {body : Expr S (tTy :: sTy :: Γ') uTy}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live)
    (bodySpec : ∀ env slots live, CodeSpecB m funs bounds host pv body env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.letPair e body) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hER : e.width ≤ max e.width body.width := Nat.le_max_left ..
  have hBR : body.width ≤ max e.width body.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  have hV : ∀ i, ((live i || body.uses (i + 2)) || e.uses i) = true →
      (live i || (Expr.letPair e body).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine eSpec env slots (fun i => live i || body.uses (i + 2)) h
    (base + sTy.width + tTy.width) heap store s hh hpv ((hVars.mono (by omega)).live_mono hV) hAt
        hCap
    (by omega) (by omega) hPlace.1
    _ _ (hTrap.part (by flag_tac) (fun h => by simp only [Expr.aborts]; exact trap_left _ _ _ h)
      fun _ hw => hw.mono (by simp only [Expr.allocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws a1 hTop1 => ?_
  have hp1 : s1.params = s.params := a1.frame.params
  have hh1 : s1.half = h := a1.frame.half.trans hh
  have a1' := a1.lower (hVars.live_mono hV) (by omega) fun i h => by simp [h]
  obtain ⟨wf, wsec, rfl, hRf, hRs, hDisj⟩ := a1.rep
  have hlf := hRf.length
  have hls := hRs.length
  rw [List.reverse_append, List.append_assoc]
  refine wp_storeCode wsec h (base + sTy.width) tTy.types s1 (wf.reverse ++ s.values) hRs.typed
    hh1 (by rw [hp1]; omega) (by rw [Ty.types_length, hh1]; omega) fun s2 hF2 hold2 _ => ?_
  have hh2 : s2.half = h := hF2.half.trans hh1
  refine wp_storeCode wf h base sTy.types s2 s.values hRf.typed hh2 (by rw [hF2.params, hp1]; omega)
    (by rw [Ty.types_length, hh2]; omega) fun s3 hF3 hold1 habove3 => ?_
  have hold1' : LocalsHold { s3 with values := s.values } base sTy.types wf := hold1
  have hold2' : LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types wsec :=
    hold2.keep hF3.half habove3 (by rw [Ty.types_length]) (by rw [hls, hh2]; omega)
  have f3 : Frame base s1 { s3 with values := s.values } :=
    (hF2.mono (by omega)).trans (hF3.trans Frame.ofValues)
  have hp3 : s3.params = s.params := hF3.params.trans (hF2.params.trans hp1)
  -- The body's context: the second component as variable 0 and the first as variable 1.
  have hVars1 := (a1'.holds.agree f3)
  have hApart := a1'.apart.agree a1'.holds f3
  have hVarsB : Holds (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
        ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)
      (fun i => decide (i < 2) || shift 2 live i || body.uses i)
      (base + sTy.width + tTy.width) heap1 store1 { s3 with values := s.values } := by
    refine Holds.push (Holds.push (hVars1.live_mono fun i h => by simpa using h) hold1' hRf
      ((hApart.fst hlf).live_mono fun i h => by simpa using h)) hold2' hRs ?_
    refine Holds.Apart.push ((hApart.snd hlf).live_mono fun i h => by simpa using h) hold1' hlf
      fun hmo b hb c hc => ?_
    have hmo' : e.mode (slots.map Slot.mode) = .owned := by simpa using hmo
    rw [hmo'] at hb hc hDisj
    exact regionsDisjoint_symm (hDisj rfl c hc b hb)
  have hRelease : ∀ rest' : Program,
      (if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 1 = false then
        releaseCode sTy base else []) ++
      ((if e.mode (slots.map Slot.mode) = .owned ∧ body.uses 0 = false then
        releaseCode tTy (base + sTy.width) else []) ++ rest') =
      ((if body.uses 1 = false then [1] else []) ++
        (if body.uses 0 = false then [0] else [])).flatMap
        (releaseVar (tTy :: sTy :: Γ') (⟨base + sTy.width, e.mode (slots.map Slot.mode)⟩ ::
          ⟨base, e.mode (slots.map Slot.mode)⟩ :: slots)) ++ rest' := by
    intro rest'
    cases body.uses 1 <;> cases body.uses 0 <;> cases e.mode (slots.map Slot.mode) <;>
      simp [releaseVar]
  rw [hRelease]
  have hd1 : (Expr.letPair e body).depthCalls = false → e.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  have hd3 : (Expr.letPair e body).depthCalls = false → body.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.2
  refine wp_releaseVarsT hm _ (by split <;> split <;> simp) hVarsB a1.step.at_
    (by split <;> split <;> simp) fun heap2 store2 e2 hTop2 => ?_
  have e2' := e2.mono (live' := fun i => shift 2 live i || body.uses i) fun i h => by
    match i with
    | 0 =>
      have h0 : body.uses 0 = true := by simpa [shift] using h
      simp [h0]
    | 1 =>
      have h1 : body.uses 1 = true := by simpa [shift] using h
      simp [h1]
    | k + 2 => split <;> split <;> simpa using h
  refine bodySpec _ _ (shift 2 live) h (base + sTy.width + tTy.width) heap2 store2
    { s3 with values := s.values } (f3.half.trans hh1) (hp3.trans hpv) e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, a1.step.cap m]; exact hCap)
    (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3]; omega)
    (by omega) hPlace.2 _ _
    (hTrap.part (by flag_tac) (fun h => by
      have hmo := e.mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact let_trap_body2 _ _ _ _ (fun hv => hmo (by simpa using hv)) h) fun hd hw => by
        simp only [Expr.allocs] at hw
        exact hw.shift (heap1 := heap2) (store1 := store2)
          (c1 := e.allocs funs bounds (slots.map Slot.mode) (fun i => live i || body.uses (i + 2))
            env)
          (by have := hTop1 (hd1 hd); have := congrArg UInt64.toNat hTop2; omega)
          (by simp only [List.map_cons]; omega) (by rw [e2'.step.cap m, a1.step.cap m]))
    fun heap3 store3 s4 ws4 aB hTop3 => ?_
  have aB' := After.prepend hVarsB e2' aB (fun i h => live_right _ _ _ h) fun i h => by simp [h]
  have hNew : ∀ r, (∀ b ∈ (e.mode (slots.map Slot.mode)).fresh store1 (.pair sTy tTy) (wf ++ wsec)
      (e.denote funs env), regionsDisjoint r b) →
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } (base + sTy.width) tTy.types w →
        w.length = tTy.width →
        ∀ b ∈ tTy.blocks store1 w (e.denote funs env).2, regionsDisjoint r b) ∧
      ((e.mode (slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold { s3 with values := s.values } base sTy.types w → w.length = sTy.width →
        ∀ b ∈ sTy.blocks store1 w (e.denote funs env).1, regionsDisjoint r b) := by
    intro r hFresh
    rw [Mode.fresh_pair hlf] at hFresh
    refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo w hw hlw b hb => ?_⟩
    · obtain rfl := LocalsHold.unique hw hold2' (hlw.trans hls.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_right _ hb)
    · obtain rfl := LocalsHold.unique hw hold1' (hlw.trans hlf.symm)
      rw [hmo] at hFresh
      exact hFresh b (List.mem_append_left _ hb)
  exact hNext heap3 store3 s4 ws4
    ((After.bind2 (hVars.live_mono hV) a1' f3 aB' (by omega) hNew
      (fun i h => by simpa using h) (fun i h => by simp [h]) fun i h => by simp [h]).liveIn hV)
    fun hd => by
      have := hTop1 (hd1 hd); have h3 := hTop3 (hd3 hd); have := congrArg UInt64.toNat hTop2
      simp only [List.map_cons] at h3
      simp only [Expr.allocs]; omega

/-- The code of a call's arguments pushes words that represent their values in the modes
`modes`, in order.  An argument without arrays runs its code with the variables `all` live after
it, so that no argument consumes a variable.  A borrowed argument with arrays, a place, loads its
variables' words.  An owned argument, a variable, loads its words when it is owned and not in
`kept`, which moves it into the call, and is copied otherwise.  The copies are the fresh blocks
`F` of the arguments' step.  The owned arguments' blocks lie apart from one another and from the
borrowed arguments' arrays, and a region apart from `F` and from the blocks of the moved
variables lies apart from the owned arguments' blocks.  A region apart from the variables that
the arguments with arrays read lies apart from the borrowed arguments' arrays. -/
theorem args_specB (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {all kept : Nat → Bool} {h base : Nat} {d a : Bool} :
    {ps : List Ty} → (modes : Nat → Mode) →
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (∀ i env slots live, CodeSpecB m funs bounds host pv (args i) env slots live) →
    (∀ i k, (args i).uses k = true → all k = true) → (∀ k, kept k = true → all k = true) →
    (∀ i : Fin ps.length, modes i = .owned → (ps.get i).scalar = false) →
    (∀ i, (ps.get i).scalar = false → modes i = .borrowed → (args i).isPlace = true) →
    (∀ i : Fin ps.length, modes i = .owned → ∃ x : Var Γ (ps.get i), args i = .var x ∧
      (kept x.index = false → (slots.getD x.index default).mode = .owned ∧
        ∀ j : Fin ps.length, j ≠ i → (ps.get j).scalar = false →
          (args j).uses x.index = false)) →
    (∀ i, (args i).placeArgs = true) →
    (∀ i, (args i).depthCalls = true → d = true) →
    (∀ i, ((args i).aborts || modes i == .owned || slots.any (·.mode == .owned)) = true →
      a = true) →
    ∀ (heap : Heap) (store : Store Unit) (s : Locals), s.half = h → s.params = pv →
    Holds env slots all base heap store s → heap.At store → store.memoryCap m 0 ≤ 65535 →
    s.params.length ≤ base →
    (∀ i : Fin ps.length,
      base + (if modes i = .owned then copyWidth (ps.get i) else (args i).width) ≤ h) →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (d || (a && !decide (heap.Within store m
      (argsSum (argCost funs bounds (slots.map Slot.mode) all kept modes args env))))) Q →
    (∀ heap' store' s' ws F, Step heap store (fun _ => True) heap' store' F →
      Frame base s s' → Holds env slots all base heap' store' s' →
      Env.Rep modes heap' store' ws (Env.ofFn fun i => (args i).denote funs env) →
      Separate store' (Env.moves modes ws (Env.ofFn fun i => (args i).denote funs env))
        (Env.reads modes ws (Env.ofFn fun i => (args i).denote funs env)) →
      (∀ r, (∀ b ∈ F, regionsDisjoint r b) →
        Holds.KeepDying env slots
          (fun k => argsAny fun i => modes i == .owned && (args i).uses k && !kept k)
          (fun _ => false) store s r →
        Apart store' (Env.moves modes ws (Env.ofFn fun i => (args i).denote funs env)) r) →
      (∀ r, Holds.ApartFrom env slots
          (fun k => argsAny fun i => !(ps.get i).scalar && (args i).uses k) store s r →
        ∀ c ∈ Env.reads modes ws (Env.ofFn fun i => (args i).denote funs env),
          regionsDisjoint r c) →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        argsSum (argCost funs bounds (slots.map Slot.mode) all kept modes args env)) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (argsCode (fun i => if (ps.get i).scalar then (args i).code h slots base all
      else if modes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots) ++ rest) Q store s host
  | [], _, _, _, _, _, _, _, _, _, _, _, heap, store, s, _, _, hVars, hAt, _, _, _, rest, Q, _,
      hNext => by
    simpa [argsCode, Env.ofFn, Env.Rep, Env.moves, Env.reads] using
      hNext heap store s [] [] (Step.refl hAt _) (Frame.refl base s) hVars rfl Separate.nil
        (fun _ _ _ => Apart.nil) (fun _ _ _ h => nomatch h) fun _ => Nat.le_add_right _ _
  | p :: ps, modes, args, argsSpec, hUses, hKept, hArray, hPlace, hOwned, hPlaceArgs, hdA, haA,
      heap, store, s, hh, hpv, hVars, hAt, hCap, hBase, hRoom, rest, Q, hTrap, hNext => by
    simp only [argsCode, List.append_assoc]
    have hSum : argsSum (argCost funs bounds (slots.map Slot.mode) all kept modes args env) =
        argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩ +
          argsSum (argCost funs bounds (slots.map Slot.mode) all kept (fun i => modes (i + 1))
            (fun i : Fin ps.length => args i.succ) env) := rfl
    have hd0 : d = false → (args ⟨0, by simp⟩).depthCalls = false := fun hd => by
      cases h0 : (args ⟨0, by simp⟩).depthCalls
      · rfl
      · rw [hdA _ h0] at hd; exact nomatch hd
    -- The other arguments, from the state after the first, and the facts of all of them.
    have hRest : ∀ heap1 store1 s1 ws0 F0,
        (d = false → heap1.top.toNat ≤ heap.top.toNat +
          argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩) →
        Step heap store (fun _ => True) heap1 store1 F0 → Frame base s s1 →
        Holds env slots all base heap1 store1 s1 →
        p.Rep (modes 0) heap1 store1 ws0 ((args ⟨0, by simp⟩).denote funs env) →
        (∀ r, (∀ b ∈ F0, regionsDisjoint r b) →
          Holds.KeepDying env slots
            (fun k => modes 0 == .owned && (args ⟨0, by simp⟩).uses k && !kept k)
            (fun _ => false) store s r →
          ∀ q ∈ (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []),
            regionsDisjoint r (block store1 q)) →
        (∀ q ∈ (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []),
          Holds.ApartFrom env slots (fun k => argsAny fun i : Fin ps.length =>
            !(ps.get i).scalar && (args i.succ).uses k) store1 s1 (block store1 q)) →
        (∀ r, Holds.ApartFrom env slots (fun k => !p.scalar && (args ⟨0, by simp⟩).uses k)
            store s r →
          ∀ c ∈ (match modes 0 with
            | .owned => []
            | .borrowed => p.reads ws0 ((args ⟨0, by simp⟩).denote funs env)),
            regionsDisjoint r c) →
        wp m (argsCode (fun i : Fin ps.length =>
            if ((p :: ps).get i.succ).scalar then (args i.succ).code h slots base all
            else if modes i.succ = .owned then (args i.succ).ownedCode h slots base kept
            else (args i.succ).placeCode h slots) ++ rest) Q store1
          { s1 with values := ws0.reverse ++ s.values } host := by
      intro heap1 store1 s1 ws0 F0 hTop0 hStep1 hF1 hH1 hR1 h5a h5c h6b
      have hl0 := hR1.length
      have hAllUses : ∀ (i : Fin ps.length) k, (args i.succ).uses k = true → all k = true :=
        fun i => hUses i.succ
      refine args_specB hm (fun i => modes (i + 1)) (fun i => args i.succ)
        (fun i => argsSpec i.succ) hAllUses hKept (fun i => hArray i.succ)
        (fun i => hPlace i.succ) (fun i hmo => ?_) (fun i => hPlaceArgs i.succ)
        (fun i => hdA i.succ) (fun i => haA i.succ) heap1
        store1 { s1 with values := ws0.reverse ++ s.values } (hF1.half.trans hh)
        (hF1.params.trans hpv) (hH1.agree Frame.ofValues) hStep1.at_ (by rw [hStep1.cap m]; exact
            hCap)
        (by show s1.params.length ≤ base; rw [hF1.params]; exact hBase)
        (fun i => hRoom i.succ) _ _
        (hTrap.part id id fun hd hw => hw.shift (heap1 := heap1) (store1 := store1)
          (hTop0 hd) (by rw [hSum]) (hStep1.cap m))
        fun heap2 store2 s2 ws2 F2 hStep2 hF2 hH2 hRep2 hSep2 hX2 hY2 hTop2 => ?_
      · obtain ⟨x, hx, hk⟩ := hOwned i.succ hmo
        exact ⟨x, hx, fun h => ⟨(hk h).1, fun j hj hs => (hk h).2 j.succ
          (fun he => hj (Fin.succ_injective _ he)) hs⟩⟩
      -- The first argument's value and its regions in the final state.
      obtain ⟨hR0, hSame0, hFresh0⟩ := hR1.step hStep2 fun _ _ => trivial
      have hBlock : ∀ q ∈ (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []),
          block store2 q = block store1 q ∧ ∀ b ∈ F2, regionsDisjoint (block store1 q) b := by
        intro q hq
        cases hmd : modes 0 with
        | borrowed => rw [hmd] at hq; exact nomatch hq
        | owned =>
          rw [hmd] at hq hSame0 hFresh0
          simp only [Ty.regions, Ty.blocks_pointers] at hSame0 hFresh0
          exact ⟨List.map_inj_left.mp hSame0 q hq, hFresh0 _ (List.mem_map_of_mem hq)⟩
      have hMoves : Env.moves modes (ws0 ++ ws2)
          (Env.ofFn fun i : Fin (p :: ps).length => (args i).denote funs env) =
          (match modes 0 with | .owned => p.pointers ws0 | .borrowed => []) ++
            Env.moves (fun i => modes (i + 1)) ws2
              (Env.ofFn fun i : Fin ps.length => (args i.succ).denote funs env) :=
        Env.moves_cons hl0
      have hReads : Env.reads modes (ws0 ++ ws2)
          (Env.ofFn fun i : Fin (p :: ps).length => (args i).denote funs env) =
          (match modes 0 with
            | .owned => []
            | .borrowed => p.reads ws0 ((args ⟨0, by simp⟩).denote funs env)) ++
            Env.reads (fun i => modes (i + 1)) ws2
              (Env.ofFn fun i : Fin ps.length => (args i.succ).denote funs env) :=
        Env.reads_cons hl0
      -- A variable that a later owned argument moves is apart from the first argument's arrays.
      have hMovedRest : ∀ c ∈ (match modes 0 with
          | .owned => []
          | .borrowed => p.reads ws0 ((args ⟨0, by simp⟩).denote funs env)),
          Holds.KeepDying env slots (fun k => argsAny fun i : Fin ps.length =>
            modes (i + 1) == .owned && (args i.succ).uses k && !kept k) (fun _ => false) store1
            { s1 with values := ws0.reverse ++ s.values } c := by
        intro c hc t x hx _ hmx wx hwx hlx b hb
        obtain ⟨i, hi⟩ := argsAny_true.mp hx
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hi
        obtain ⟨⟨hmo, hux⟩, hkx⟩ := hi
        obtain ⟨y, hy, hk⟩ := hOwned i.succ hmo
        have hxy : x.index = y.index := by
          have := hux
          rw [hy] at this
          simpa [Expr.uses] using this
        have hNot0 := (hk (hxy ▸ hkx)).2 ⟨0, by simp⟩
          (fun he => absurd (congrArg Fin.val he) (Nat.succ_ne_zero _).symm)
        have hwx' := (hH1.hold_agree Frame.ofValues (hUses _ _ hux) hlx).mp hwx
        have hSameX := (hVars.regions_after hStep1 (hUses _ _ hux)
          ((hVars.hold_agree hF1 (hUses _ _ hux) hlx).mp hwx') hlx
          fun _ _ => trivial).1
        simp only [Ty.regions, hmx] at hSameX
        rw [hSameX] at hb
        refine regionsDisjoint_symm (h6b b ?_ c hc)
        refine Holds.ApartFrom.owned hVars (hUses _ _ hux) hmx
          ((hVars.hold_agree hF1 (hUses _ _ hux) hlx).mp hwx') hlx
          (fun k hk' => ?_) b hb
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk'
        refine ⟨hUses _ _ hk'.2, fun he => ?_⟩
        rw [he, hxy] at hk'
        have := hNot0 hk'.1
        rw [hk'.2] at this
        exact nomatch this
      have e := hNext heap2 store2 s2 (ws0 ++ ws2) (F0 ++ F2)
        (hStep1.transBoth hStep2 fun _ _ => ⟨trivial, fun _ => trivial⟩)
        (hF1.trans hF2.values) (hH2.agree Frame.ofValues) ⟨ws0, ws2, rfl, hR0, hRep2⟩ ?_ ?_ ?_
        (fun hd => by have := hTop0 hd; have := hTop2 hd; rw [hSum]; omega)
      · simpa [List.reverse_append, List.append_assoc] using e
      · -- The owned arguments' blocks are pairwise apart, and apart from the borrowed arrays.
        rw [hMoves, hReads]
        refine ⟨?_, fun c hc => ?_⟩
        · rw [List.map_append]
          refine List.pairwise_append.mpr ⟨?_, hSep2.1, fun a ha b hb => ?_⟩
          · cases hmd : modes 0 with
            | borrowed => exact List.Pairwise.nil
            | owned =>
              rw [hmd] at hR0
              have := hR0.pairwise
              rwa [Ty.blocks_pointers] at this
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
            obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
            obtain ⟨hEq, hF⟩ := hBlock q hq
            rw [hEq]
            exact hX2 _ hF (Holds.ApartFrom.keepDying (liveIn := fun k =>
                argsAny fun i : Fin ps.length =>
                  modes (↑i + 1) == .owned && (args i.succ).uses k && !kept k)
                (liveOut := fun _ => false) (h5c q hq) fun k hk _ => by
              obtain ⟨i, hi⟩ := argsAny_true.mp hk
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hi
              refine argsAny_true.mpr ⟨i, ?_⟩
              simp only [Bool.and_eq_true, Bool.not_eq_true']
              exact ⟨hArray i.succ hi.1.1, hi.1.2⟩) q' hq'
        · rcases List.mem_append.mp hc with hc | hc
          · refine Apart.append (fun q hq => ?_) (hX2 c ?_ (hMovedRest c hc))
            · cases hmd : modes 0 with
              | borrowed => rw [hmd] at hq; exact nomatch hq
              | owned => rw [hmd] at hc; exact nomatch hc
            · cases hmd : modes 0 with
              | owned => rw [hmd] at hc; exact nomatch hc
              | borrowed =>
                rw [hmd] at hc hFresh0
                exact hFresh0 c hc
          · refine Apart.append (fun q hq => ?_) (hSep2.2 c hc)
            obtain ⟨hEq, -⟩ := hBlock q hq
            rw [hEq]
            exact regionsDisjoint_symm (hY2 _ (h5c q hq) c hc)
      · -- A region apart from the copies and the moved variables lies apart from every owned
        -- argument's blocks.
        intro r hr hk
        rw [hMoves]
        refine Apart.append (fun q hq => ?_) (hX2 r (fun b hb => hr b (List.mem_append_right _ hb))
          ?_)
        · rw [(hBlock q hq).1]
          exact h5a r (fun b hb => hr b (List.mem_append_left _ hb))
            (hk.mono fun i h1 _ => ⟨le_argsAny (fun j : Fin (p :: ps).length =>
              modes j == .owned && (args j).uses i && !kept i) ⟨0, by simp⟩ h1, rfl⟩) q hq
        · refine Holds.KeepDying.transfer (s1 := { s1 with values := ws0.reverse ++ s.values })
            (liveIn := fun k => argsAny fun i : Fin ps.length =>
              modes (↑i + 1) == .owned && (args i.succ).uses k && !kept k)
            (liveOut := fun _ => false) hVars (hStep1.mono (fun _ _ => trivial) fun _ h => h)
            (hF1.trans Frame.ofValues) (fun _ h => h) (fun i h _ => ?_)
            (hk.mono fun i h1 _ => ⟨by
              obtain ⟨j, hj⟩ := argsAny_true.mp h1
              exact le_argsAny (fun j : Fin (p :: ps).length =>
                modes j == .owned && (args j).uses i && !kept i) j.succ hj, rfl⟩)
          obtain ⟨j, hj⟩ := argsAny_true.mp h
          simp only [Bool.and_eq_true] at hj
          exact hUses _ _ hj.1.2
      · -- A region apart from the variables that the arguments with arrays read lies apart from
        -- the borrowed arguments' arrays.
        intro r hr c hc
        rw [hReads] at hc
        rcases List.mem_append.mp hc with hc | hc
        · exact h6b r (hr.mono fun i h => le_argsAny (fun j : Fin (p :: ps).length =>
            !((p :: ps).get j).scalar && (args j).uses i) ⟨0, by simp⟩ h) c hc
        · refine hY2 r ((Holds.ApartFrom.iff hVars hStep1 hF1
            (fun k hk => ?_)).mpr (hr.mono fun i h => by
              obtain ⟨j, hj⟩ := argsAny_true.mp h
              exact le_argsAny (fun j : Fin (p :: ps).length =>
                !((p :: ps).get j).scalar && (args j).uses i) j.succ hj)) c hc
          obtain ⟨j, hj⟩ := argsAny_true.mp hk
          simp only [Bool.and_eq_true] at hj
          exact hUses _ _ hj.2
    by_cases hp : p.scalar = true
    · -- An argument without arrays: its code, with every argument's variables live after it.
      rw [ite_eq_left (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      have hmd : modes 0 = .borrowed := by
        cases h : modes 0 with
        | borrowed => rfl
        | owned => have := hArray ⟨0, by simp⟩ h; simp [hp] at this
      have hSub : ∀ k, (all k || (args ⟨0, by simp⟩).uses k) = true → all k = true :=
        fun k h => by
          simp only [Bool.or_eq_true] at h
          exact h.elim id (hUses _ k)
      have hRoom0 := hRoom ⟨0, by simp⟩
      simp only [show modes ↑(⟨0, by simp⟩ : Fin (p :: ps).length) = .borrowed from hmd,
        reduceCtorEq, ↓reduceIte] at hRoom0
      have hc0 : argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩ =
          (args ⟨0, by simp⟩).allocs funs bounds (slots.map Slot.mode) all env := by
        simp only [argCost]; rw [if_pos (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      refine argsSpec ⟨0, by simp⟩ env slots all h base heap store s hh hpv (hVars.live_mono
          hSub)
        hAt hCap hBase hRoom0 (hPlaceArgs _) _ _
        (hTrap.part (hdA _) (fun h => haA _ (by
            simp only [Bool.or_eq_true] at h ⊢; tauto))
          fun _ hw => hw.mono (by rw [hSum, hc0]; exact Nat.le_add_right _ _))
        fun heap1 store1 s1 ws1 a1 hTop1 => ?_
      have hStep := a1.step
      rw [Mode.fresh_scalar (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)] at hStep
      refine hRest heap1 store1 s1 ws1 [] (fun hd => by rw [hc0]; exact hTop1 (hd0 hd))
        (hStep.mono (fun _ _ => (Holds.KeepDying.none).mono
          fun i h1 h2 => ⟨hSub i h1, h2⟩) fun _ h => h) a1.frame a1.holds
        (by rw [hmd]; exact a1.rep.borrow) (fun _ _ _ q hq => ?_) (fun q hq => ?_)
        (fun _ _ c hc => ?_)
      · rw [hmd] at hq; exact nomatch hq
      · rw [hmd] at hq; exact nomatch hq
      · rw [hmd, Ty.reads_scalar _ hp] at hc; exact nomatch hc
    · rw [ite_eq_right (show ¬((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      cases hmd : modes 0 with
      | owned =>
        -- An owned argument, a variable: moved when it dies, and copied otherwise.
        rw [ite_eq_left (rfl : Mode.owned = Mode.owned)]
        obtain ⟨x, hx, hk⟩ := hOwned ⟨0, by simp⟩ hmd
        have hux : (args ⟨0, by simp⟩).uses x.index = true := by rw [hx]; simp [Expr.uses]
        have hAllX := hUses _ _ hux
        have hv : (args ⟨0, by simp⟩).denote funs env = env.get x := by rw [hx]; rfl
        rw [show (args ⟨0, by simp⟩).ownedCode h slots base kept = x.ownedCode h slots base kept by
          rw [hx]; rfl]
        cases hkx : kept x.index with
        | false =>
          obtain ⟨hmx, hOthers⟩ := hk hkx
          rw [Var.ownedCode_move x hmx hkx]
          obtain ⟨-, ws, hold, hRep⟩ := hVars.get x hAllX
          refine wp_loadCode ws hRep.typed hh hold (hRest heap store s ws []
            (fun _ => Nat.le_add_right _ _) (Step.refl hAt _)
            (Frame.refl base s) hVars (by rw [hmd, hv, ← hmx]; exact hRep)
            (fun r _ hr q hq => ?_) (fun q hq => ?_) (fun _ _ c hc => ?_))
          · rw [hmd] at hq
            refine hr _ x (by simp only [hmd, hux, hkx]; rfl) rfl hmx ws hold hRep.length _ ?_
            rw [Ty.blocks_pointers]
            exact List.mem_map_of_mem hq
          · rw [hmd] at hq
            refine Holds.ApartFrom.owned hVars hAllX hmx hold hRep.length (fun k hk' => ?_) _
              (by rw [Ty.blocks_pointers]; exact List.mem_map_of_mem hq)
            obtain ⟨j, hj⟩ := argsAny_true.mp hk'
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hj
            refine ⟨hUses _ _ hj.2, fun he => ?_⟩
            have := hOthers j.succ (fun h => absurd (congrArg Fin.val h) (Nat.succ_ne_zero _)) hj.1
            rw [he] at hj
            rw [hj.2] at this
            exact nomatch this
          · rw [hmd] at hc; exact nomatch hc
        | true =>
          rw [Var.ownedCode_live x (live' := all) (by rw [hkx, hAllX])]
          have hRoom0 := hRoom ⟨0, by simp⟩
          simp only [show modes ↑(⟨0, by simp⟩ : Fin (p :: ps).length) = .owned from hmd,
            ↓reduceIte] at hRoom0
          have hc0 : argCost funs bounds (slots.map Slot.mode) all kept modes args env ⟨0, by simp⟩ =
              x.ownedCost (slots.map Slot.mode) all (env.get x) := by
            simp only [argCost]
            rw [if_neg (show ¬((p :: ps).get ⟨0, by simp⟩).scalar = true from hp),
              if_pos (show modes ↑(⟨0, by simp⟩ : Fin (p :: ps).length) = .owned from hmd), hx]
            simp only [Expr.ownedCost, Var.ownedCost, Var.cost, hkx, hAllX]
          refine specB_ownedVar hm x hh hpv (hVars.live_mono fun i h => by
              simp only [Bool.or_eq_true, beq_iff_eq] at h
              exact h.elim id fun he => he ▸ hAllX) hAt hCap hBase hRoom0
            (hTrap.alloc (haA ⟨0, by simp⟩ (by simp [hmd])) fun _ hw => hw.mono (by
              rw [hSum, hc0]; exact Nat.le_add_right _ _))
            fun heap1 store1 s1 ws1 a1 hTop1 => ?_
          have hStep := a1.step
          simp only [Mode.fresh] at hStep
          refine hRest heap1 store1 s1 ws1 (p.blocks store1 ws1 (env.get x))
            (fun _ => by rw [hc0]; exact hTop1)
            (hStep.mono (fun _ _ => (Holds.KeepDying.none).mono fun i h1 h2 => ⟨by
              simp only [Bool.or_eq_true, beq_iff_eq] at h1
              exact h1.elim id fun he => he ▸ hAllX, h2⟩) fun _ h => h) a1.frame a1.holds
            (by rw [hmd, hv]; exact a1.rep) (fun r hr _ q hq => ?_) (fun q hq => ?_)
            (fun _ _ c hc => ?_)
          · rw [hmd] at hq
            exact hr _ (by rw [Ty.blocks_pointers]; exact List.mem_map_of_mem hq)
          · rw [hmd] at hq
            intro u y hy wy hwy hly c hc
            obtain ⟨j, hj⟩ := argsAny_true.mp hy
            simp only [Bool.and_eq_true] at hj
            exact a1.apart u y (hUses _ _ hj.2) (Or.inl rfl) wy hwy hly _
              (by simp only [Ty.regions]; rw [Ty.blocks_pointers]; exact List.mem_map_of_mem hq)
              c hc
          · rw [hmd] at hc; exact nomatch hc
      | borrowed =>
        -- A borrowed argument with arrays, a place: its variables' words.
        rw [ite_eq_right (show ¬(Mode.borrowed = Mode.owned) from nofun)]
        exact place_spec hh hVars (args ⟨0, by simp⟩) (hPlace _ (by simpa using hp) hmd)
          (fun k h => hUses _ k h) fun ws1 hR1 hReads1 =>
            hRest heap store s ws1 [] (fun _ => Nat.le_add_right _ _) (Step.refl hAt _)
              (Frame.refl base s) hVars
              (by rw [hmd]; exact hR1) (fun _ _ _ q hq => by rw [hmd] at hq; exact nomatch hq)
              (fun q hq => by rw [hmd] at hq; exact nomatch hq)
              fun r hr c hc => by
                rw [hmd] at hc
                exact hReads1 r (hr.mono fun k h => by
                  rw [Bool.and_eq_true]; exact ⟨by simpa using hp, h⟩) c hc

/-- The release of the owned variables that `sel` selects after an expression's code, those live
in `L1` and not in `live`, gives the facts of the code and the release for `live`.  The value lies
apart from the released blocks, so its words still represent it, and `top` is unchanged. -/
theorem After.releaseT (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live sel : Nat → Bool} {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit}
    {s s1 : Locals} {t : Ty} {mode : Mode} {v : t.denote} {ws vals : List Value}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : After env slots L0 L1 base heap store s t mode v heap1 store1 s1 ws)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hSel : ∀ i, sel i = true → L1 i = true)
    (hLive : ∀ i, live i = true → (L1 i && !sel i) = true)
    (hNext : ∀ heap2 store2,
      After env slots L0 live base heap store s t mode v heap2 store2 s1 ws →
      heap2.top = heap1.top → wp m rest Q store2 { s1 with values := vals } host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store1 { s1 with values := vals } host := by
  refine wp_releaseWhereT hm (a.holds.agree Frame.ofValues) a.step.at_ hSel
    fun heap2 store2 e hTop => ?_
  have e' := e.mono hLive
  have hLiveL1 : ∀ i, live i = true → L1 i = true := fun i h => by
    have := hLive i h
    simp only [Bool.and_eq_true] at this
    exact this.1
  -- The value lies apart from the blocks of the variables that die.
  have hKeepV : ∀ r ∈ t.regions mode store1 ws v,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vals } r := by
    intro r hr u x hx _ hmx wx hwx hlx b hb
    have hb' : b ∈ u.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hmx]; exact hb
    exact a.apart u x hx (Or.inr hmx) wx hwx hlx r hr b hb'
  obtain ⟨hRep, hSame, -⟩ := a.rep.step e'.step hKeepV
  have hStep := a.step.transBoth (keep := Holds.KeepDying env slots L0 live store s) e'.step
    fun r hr =>
    ⟨hr.mono fun i h1 h2 => ⟨h1, by
        cases hl : live i with
        | false => rfl
        | true => rw [hLiveL1 i hl] at h2; exact nomatch h2⟩,
      fun _ => Holds.KeepDying.transfer h0 a.step a.frame hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine hNext heap2 store2 ⟨hStep.mono (fun _ h => h) fun b hb => ?_, a.frame,
    e'.holds.agree Frame.ofValues, hRep, ?_⟩ hTop
  · rw [Mode.fresh_congr hSame] at hb
    exact List.mem_append_left _ hb
  · exact Holds.Apart.transfer (a.holds.live_mono hLiveL1) (a.apart.live_mono hLiveL1) e'.step
      Frame.ofValues (fun u y hy wy hwy hly => a.holds.keepDying hLiveL1 hy hwy hly) hSame

/-- A call: the arguments, the callee, whose theorem `Calls` gives, and the release of the owned
variables that the arguments use and that die at the call, other than those that the call
consumes. -/
theorem specB_call (hm : Runtime m) {d0 : UInt64} (hCalls : CallsAtB m funs bounds d0) {sig : Sig}
    {Γ' : List Ty} (g : FVar S sig)
    (args : (i : Fin sig.params.length) → Expr S Γ' (sig.params.get i))
    (argsSpec : ∀ i env slots live, CodeSpecB m funs bounds host pv (args i) env slots live)
    (hDepth : (Expr.call g args).depthCalls = true → pv.head? = some (.i64 d0)) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.call g args) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hRoom' : ∀ i : Fin sig.params.length, base + (if sig.mode i = .owned then
      copyWidth (sig.params.get i)
      else (args i).width) ≤ h := fun i =>
    (Nat.add_le_add_left (le_argsMax (fun i => if sig.mode i = .owned then
      copyWidth (sig.params.get i) else (args i).width) i) base).trans hRoom
  simp only [Expr.placeArgs, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hPlace
  obtain ⟨⟨hA, hV⟩, hB⟩ := hPlace
  have hPlace1 : ∀ i, (sig.params.get i).scalar = false → sig.mode i = .borrowed →
      (args i).isPlace = true := fun i hs _ => by
    cases hi : (args i).isPlace with
    | true => rfl
    | false =>
      have := le_argsAny (fun i => !(sig.params.get i).scalar && !(args i).isPlace) i
        (by simp only [hs, hi, Bool.not_false, Bool.and_self])
      rw [hA] at this
      exact nomatch this
  have hVar : ∀ i : Fin sig.params.length, sig.mode i = .owned → ∃ x, args i = .var x :=
      fun i hmo => by
    refine Expr.exists_var (args i) ?_
    cases hi : (args i).varIndex?.isNone with
    | false => rfl
    | true =>
      have := le_argsAny (fun i => sig.mode i == .owned && (args i).varIndex?.isNone) i
        (by simp [hmo, hi])
      rw [hV] at this
      exact nomatch this
  have hPlace2 : ∀ i, (args i).placeArgs = true := fun i => by
    cases hi : (args i).placeArgs with
    | true => rfl
    | false =>
      have := le_argsAny (fun i => !(args i).placeArgs) i (by simp [hi])
      rw [hB] at this
      exact nomatch this
  -- The variables that the call consumes: those that an argument moves.
  have hMoved : ∀ k, (argsAny fun j => callMoves slots live args j && (args j).uses k) = true →
      ∃ j x, args j = .var x ∧ x.index = k ∧ sig.mode j = .owned ∧
        (slots.getD k default).mode = .owned ∧ live k = false ∧
        ∀ j', j' ≠ j → (sig.params.get j').scalar = false → (args j').uses k = false := by
    intro k hk
    obtain ⟨j, hj⟩ := argsAny_true.mp hk
    simp only [Bool.and_eq_true, callMoves, beq_iff_eq] at hj
    obtain ⟨⟨hmo, hj⟩, hu⟩ := hj
    obtain ⟨x, hx⟩ := hVar j hmo
    rw [hx] at hj hu
    simp only [Expr.varIndex?, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hj
    simp only [Expr.uses, beq_iff_eq] at hu
    subst hu
    obtain ⟨⟨hmx, hlx⟩, hOthers⟩ := hj
    refine ⟨j, x, hx, rfl, hmo, hmx, hlx, fun j' hj' hs => ?_⟩
    cases hu : (args j').uses x.index with
    | false => rfl
    | true =>
      have := le_argsAny (fun j' => j' != j && !(sig.params.get j').scalar &&
        (args j').uses x.index) j' (by rw [hs, hu]; simp [hj'])
      rw [hOthers] at this
      exact nomatch this
  have hAllocs : (Expr.call g args).allocs funs bounds (slots.map Slot.mode) live env =
      argsSum (argCost funs bounds (slots.map Slot.mode)
        (fun i => live i || argsAny fun j => (args j).uses i)
        (fun i => (live i || argsAny fun j => (args j).uses i) &&
          !(argsAny fun j => callMoves slots live args j && (args j).uses i)) sig.mode args env) +
        bounds.get g (Env.ofFn fun i => (args i).denote funs env) := by
    simp only [Expr.allocs, callMovesAt_eq]; rfl
  simp only [Expr.code, List.append_assoc]
  refine wp_depthCode sig.depth (fun hd => by
    rw [hpv]; exact hDepth (by simp [Expr.depthCalls, hd])) ?_
  refine args_specB hm (all := fun i => live i || argsAny fun j => (args j).uses i)
    (kept := fun i => (live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) sig.mode args argsSpec
    (fun i k h => by
      simp only [Bool.or_eq_true]
      exact Or.inr (le_argsAny (fun j => (args j).uses k) i h))
    (fun k h => by simp only [Bool.and_eq_true] at h; exact h.1)
    (fun i hmo => ?_) hPlace1 (fun i hmo => ?_) hPlace2
    (fun i h => by
      simp only [Expr.depthCalls, Bool.or_eq_true]; exact Or.inr (le_argsAny _ i h))
    (fun i h => by
      simp only [Bool.or_eq_true] at h
      simp only [Expr.aborts, Bool.or_eq_true]
      rcases h with h | h
      · exact Or.inl (Or.inr (le_argsAny (fun j => (args j).aborts || sig.mode j == .owned) i
          (by simpa only [Bool.or_eq_true] using h)))
      · exact Or.inr h) heap store
    { s with values := (if sig.depth then [.i64 (d0 + 1)] else []) ++ s.values } hh hpv hVars hAt
    hCap hBase hRoom' _ _
    (hTrap.part id id fun _ hw => hw.mono (by rw [hAllocs]; exact Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 F hStep1 hF1 hH1 hRep1 hSep1 hX1 hY1 hTop1 => ?_
  · -- An owned parameter holds arrays.
    have := paramMode_owned hmo
    exact this
  · obtain ⟨x, hx⟩ := hVar i hmo
    refine ⟨x, hx, fun hkx => ?_⟩
    have hux : (args i).uses x.index = true := by rw [hx]; simp [Expr.uses]
    have hAll : (argsAny fun j => (args j).uses x.index) = true := le_argsAny _ i hux
    simp only [hAll, Bool.or_true, Bool.true_and, Bool.not_eq_false'] at hkx
    obtain ⟨j, y, hy, hyx, -, hmy, -, hOthers⟩ := hMoved _ hkx
    have hji : j = i := by
      by_contra hne
      have := hOthers i (Ne.symm hne) (paramMode_owned hmo)
      rw [hux] at this
      exact nomatch this
    subst hji
    exact ⟨hmy, hOthers⟩
  -- The callee, from the arguments' state, above the next call depth when its code takes it.
  replace hF1 : Frame base s s1 := hF1.values
  simp only [Holds.keepDying_values] at hX1
  have hRun := FunSpecB.runs (hCalls g) hm host hStep1.at_ hRep1 hSep1
    (by rw [hStep1.cap m]; exact hCap) (d := d0 + 1) (fun _ => rfl) s.values
  have hsd : (Expr.call g args).depthCalls = false → sig.depth = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd.1
  refine wp_call_runs hRun (hTrap.of_imp fun h => by
    simp only [trapFlag, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h ⊢
    cases hdc : (Expr.call g args).depthCalls
    · rcases h with ⟨ha, hw⟩ | hd
      · have hab : ((Expr.call g args).aborts || slots.any (·.mode == .owned)) = true := by
          simp only [Expr.aborts, Bool.or_eq_true]; exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
        refine Or.inr ⟨by simpa only [Bool.or_eq_true] using hab, fun hW => hw ?_⟩
        rw [hAllocs] at hW
        exact hW.shift (hTop1 hdc) le_rfl (hStep1.cap m)
      · rw [hsd hdc] at hd; exact nomatch hd
    · exact Or.inl rfl) fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, hTopC⟩ := hPost
  have hRep : sig.result.Rep ((Expr.call g args).mode (slots.map Slot.mode)) heap' st'
      out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := by
    simp only [Expr.mode]
    split
    · exact Ty.Rep.borrow hOwned
    · exact hOwned
  have hStepC : Step heap1 store1
      (Apart store1 (Env.moves sig.mode ws1 (Env.ofFn fun i => (args i).denote funs env))) heap'
      st' (((Expr.call g args).mode (slots.map Slot.mode)).fresh st' sig.result out.reverse
        (funs.get g (Env.ofFn fun i => (args i).denote funs env))) :=
    ⟨hAt', hCaps, fun r hr hpos hA => by
      obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos hA
      exact ⟨hb, hreg, fun b hb' => hout b (Mode.fresh_sub hb')⟩⟩
  -- The variables live after the call: those that its arguments use, other than the moved ones.
  have hKeptAll : ∀ i, ((live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) = true →
      (live i || argsAny fun j => (args j).uses i) = true :=
    fun i h => by simp only [Bool.and_eq_true] at h; exact h.1
  have hMovedDie : ∀ i, (argsAny fun j => sig.mode j == .owned && (args j).uses i &&
      !((live i || argsAny fun j => (args j).uses i) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses i))) = true →
      (live i || argsAny fun j => (args j).uses i) = true ∧
        ((live i || argsAny fun j => (args j).uses i) &&
          !(argsAny fun j => callMoves slots live args j && (args j).uses i)) = false := by
    intro i h
    obtain ⟨j, hj⟩ := argsAny_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hj
    refine ⟨?_, hj.2⟩
    simp only [Bool.or_eq_true]
    exact Or.inr (le_argsAny (fun j => (args j).uses i) j hj.1.2)
  have hKeepC : ∀ (u : Ty) (y : Var Γ' u),
      ((live y.index || argsAny fun j => (args j).uses y.index) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses y.index)) = true →
      ∀ wy, LocalsHold s1 (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store1 wy (env.get y),
        Apart store1 (Env.moves sig.mode ws1 (Env.ofFn fun i => (args i).denote funs env)) c := by
    intro u y hy wy hwy hly c hc
    have hyAll := hKeptAll _ hy
    have hwy' := (hVars.hold_agree hF1 hyAll hly).mp hwy
    obtain ⟨hSame, hFresh⟩ := hVars.regions_after hStep1 hyAll hwy' hly fun _ _ => trivial
    rw [hSame] at hc
    refine hX1 c (hFresh c hc) fun t x hx _ hmx wx hwx hlx b hb => ?_
    obtain ⟨hxAll, hxKept⟩ := hMovedDie _ hx
    have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hxKept; exact nomatch hxKept
    exact regionsDisjoint_symm
      (hVars.2 t u x y hxAll hyAll hne hmx wx wy hwx hlx hwy' hly b hb c hc)
  have aCall : After env slots (fun i => live i || (Expr.call g args).uses i)
      (fun i => (live i || argsAny fun j => (args j).uses i) &&
        !(argsAny fun j => callMoves slots live args j && (args j).uses i)) base heap store s
      sig.result ((Expr.call g args).mode (slots.map Slot.mode))
      (funs.get g (Env.ofFn fun i => (args i).denote funs env)) heap' st' s1 out.reverse := by
    refine ⟨hStep1.trans hStepC fun r hr => ⟨trivial, fun hF => hX1 r hF
        (hr.mono fun i h _ => hMovedDie i h)⟩, hF1,
      (hH1.live_mono hKeptAll).step hStepC hKeepC, hRep, ?_⟩
    intro u y hy _ wy hwy hly b hb c hc
    obtain ⟨hSame, hFresh⟩ := (hH1.live_mono hKeptAll).regions_after hStepC hy hwy hly
      (hKeepC u y hy wy hwy hly)
    rw [hSame] at hc
    have hb' : b ∈ ((Expr.call g args).mode (slots.map Slot.mode)).fresh st' sig.result
        out.reverse (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := by
      simp only [Expr.mode] at hb ⊢
      cases hsc : sig.result.scalar
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hb ⊢
        exact hb
      · simp only [hsc, ↓reduceIte] at hb
        rw [Ty.regions_scalar _ hsc] at hb
        exact nomatch hb
    exact regionsDisjoint_symm (hFresh c hc b hb')
  refine After.releaseT hm (s1 := s1) (live := live)
    (sel := fun i => ((live i || argsAny fun j => (args j).uses i) &&
      !(argsAny fun j => callMoves slots live args j && (args j).uses i)) && !live i) hVars aCall
    hKeptAll (fun i h => by simp only [Bool.and_eq_true] at h ⊢; exact h.1) (fun i h => ?_)
    fun heap2 store2 a2 hTopR => ?_
  · have hk : (argsAny fun j => callMoves slots live args j && (args j).uses i) = false := by
      cases hm' : argsAny fun j => callMoves slots live args j && (args j).uses i with
      | false => rfl
      | true =>
        obtain ⟨_, _, _, _, _, _, hl, _⟩ := hMoved i hm'
        rw [hl] at h
        exact nomatch h
    simp [h, hk]
  · simpa using hNext heap2 store2 s1 out.reverse a2 fun hd => by
      have := hTop1 hd; have := hTopC (hsd hd); have := congrArg UInt64.toNat hTopR
      rw [hAllocs]; omega

/-- `LeanExe.loop` with a condition: the count in local `base`, the initial state, coerced to the
loop's mode, from local `base + 2` on, and the index in local `base + 1`.  The invariant at the top
of the WebAssembly `loop` holds the count, the index `i`, and the state after `i` passes, with the
facts of `After` for the outer variables live in the loop, those live after it or used by the
condition or the body.  Each pass leaves at the count, then runs the condition with the state as a
borrowed variable, in which no variable dies, so `After.test` keeps the invariant at its heap.  A
false condition leaves with the state, which `loopState_stop` shows is the loop's value.
Otherwise the pass releases a state that the body does not use, runs the body, coerces its value
to the loop's mode, and stores it as the next state.  After the loop the outer variables that only
the condition or the body uses are released. -/
theorem specB_loop (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word}
    {init : Expr S Γ' tTy} {cond : Expr S (tTy :: Γ') .bool}
    {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots live, CodeSpecB m funs bounds host pv count env slots live)
    (initSpec : ∀ env slots live, CodeSpecB m funs bounds host pv init env slots live)
    (condSpec : ∀ env slots live, CodeSpecB m funs bounds host pv cond env slots live)
    (bodySpec : ∀ env slots live, CodeSpecB m funs bounds host pv body env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.loop count init cond body) env slots live :=
        by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (max (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy)))
  have hi := (Nat.le_max_left (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy))).trans
    (Nat.le_max_right count.width _)
  have hb := (Nat.le_max_right (1 + max init.width (copyWidth tTy))
    (2 + tTy.width + max (max cond.width body.width) (copyWidth tTy))).trans
    (Nat.le_max_right count.width _)
  have hi1 := Nat.le_max_left init.width (copyWidth tTy)
  have hi2 := Nat.le_max_right init.width (copyWidth tTy)
  have hb1 := Nat.le_max_left (max cond.width body.width) (copyWidth tTy)
  have hb2 := Nat.le_max_right (max cond.width body.width) (copyWidth tTy)
  have hcd := Nat.le_max_left cond.width body.width
  have hbd := Nat.le_max_right cond.width body.width
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  obtain ⟨⟨⟨hPc, hPi⟩, hPcd⟩, hPb⟩ := hPlace
  have hOwnedA : (Expr.loop count init cond body).mode (slots.map Slot.mode) = .owned →
      ((Expr.loop count init cond body).aborts || slots.any (·.mode == .owned)) = true :=
    fun ht => by
      have := (Expr.loop count init cond body).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this
      exact this
  have hdl : (Expr.loop count init cond body).depthCalls = false →
      count.depthCalls = false ∧ init.depthCalls = false ∧ cond.depthCalls = false ∧
        body.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd
    exact ⟨hd.1.1.1, hd.1.1.2, hd.1.2, hd.2⟩
  have hT := Expr.allocs_loop funs bounds (slots.map Slot.mode) live count init cond body env
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
      count.uses i) = true → (live i || (Expr.loop count init cond body).uses i) = true :=
    fun i h => by simp only [Expr.uses]; exact loop_live_count _ _ _ _ _ h
  refine countSpec env slots
    (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) h base heap
    store s hh hpv (hVars.live_mono hCountIn) hAt hCap hBase (by omega) hPc _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun h => by
        simp only [Expr.aborts]; exact loop_trap_count _ _ _ _ _ h)
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopK => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hHigh1 : base < s1.half := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  have f2 : Frame base s1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    Frame.setValues hLow1 le_rfl hHigh1
  have hF2 : Frame base s
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    e1.frame.trans f2
  have hN2 : (setLocal { s1 with values := s.values } base
      (.i64 (count.denote funs env))).get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have e1' : Evolves env slots
      (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) || count.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) base heap store s
      heap1 store1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    Evolves.mk e1.step hF2 (e1.holds.agree f2)
  -- The initial state, coerced to the loop's mode, in the locals from `base + 2` on.
  refine initSpec env slots (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) h
    (base + 1) heap1 store1 _ (hF2.half.trans hh) (hF2.params.trans hpv)
    (e1'.holds.mono (Nat.le_succ base))
    e1'.step.at_ (by rw [e1'.step.cap m]; exact hCap) (by rw [hF2.params]; omega) (by omega) hPi
    _ _ (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun h => by
        simp only [Expr.aborts]; exact loop_trap_init _ _ _ _ _ h)
      fun hd hw => hw.shift (heap1 := heap1) (store1 := store1) (hTopK (hdl hd).1)
        (by rw [hT]; omega) (e1'.step.cap m))
    fun heap2 store2 s3 ws0 a2 hTopI => ?_
  have hTop2 : (Expr.loop count init cond body).depthCalls = false →
      heap2.top.toNat ≤ heap.top.toNat + (count.allocs funs bounds (slots.map Slot.mode)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) env +
        init.allocs funs bounds (slots.map Slot.mode)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) env) := fun hd => by
    have := hTopK (hdl hd).1; have := hTopI (hdl hd).2.1; omega
  refine After.coerceB hm a2 (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [a2.frame.params, hF2.params]; omega) (a2.frame.half.trans (hF2.half.trans hh))
    (by omega) (by rw [a2.step.cap m, e1'.step.cap m]; exact hCap)
    (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy (init.mode (slots.map Slot.mode)) ((init.mode (slots.map Slot.mode)).join (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
          (init.denote funs env) = tTy.copyCost (init.denote funs env) := by
        rw [coerceCost, if_pos ⟨hs, ht⟩]
      exact hw.shift (hTop2 hd) (by rw [hT]; omega) (by rw [a2.step.cap m, e1'.step.cap m]))
    fun heap2' store2 s3 ws0 a2 hTopCo => ?_
  have hTopEntry : (Expr.loop count init cond body).depthCalls = false →
      heap2'.top.toNat + Expr.loopRest funs bounds (slots.map Slot.mode) live init cond body env
        (count.denote funs env).toNat 0 (init.denote funs env) ≤ heap.top.toNat + (Expr.loop count init cond body).allocs funs bounds (slots.map Slot.mode) live env :=
    fun hd => by have := hTop2 hd; rw [hT]; omega
  have hF3 : Frame base s s3 := hF2.trans (a2.frame.mono (Nat.le_succ base))
  have hh3 : s3.half = h := hF3.half.trans hh
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) :=
    (a2.frame.below base (by omega)).1.trans hN2
  have a0 := (After.prepend (hVars.live_mono hCountIn) e1'
    (a2.lower e1'.holds (Nat.le_succ base) fun i h => by simp [h]) (fun i h => by simp [h])
    fun i h => by simp [h]).liveIn hCountIn
  refine wp_storeCode ws0 h (base + 2) tTy.types s3 s.values a0.rep.typed hh3
    (by rw [hF3.params]; omega) (by rw [Ty.types_length, hh3]; omega)
    fun s4 hF4 hold4 _ => ?_
  -- The index, in local `base + 1`.
  simp only [wp_constI64_cons]
  have hh4 : s4.half = h := hF4.half.trans hh3
  have hLow4 : ({ s4 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s4.params.length ≤ base + 1; rw [hF4.params, hF3.params]; omega
  have hHigh4 : base + 1 < s4.half := by rw [hh4]; omega
  refine wp_localSet_local (s := s4) (vs := s.values) hLow4 (Locals.lt_total hHigh4) ?_
  have f5 : Frame (base + 1) s4 (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    Frame.setValues hLow4 le_rfl hHigh4
  have hF5 : Frame base s3 (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    (hF4.mono (base := base) (by omega)).trans (f5.mono (base := base) (by omega))
  have hN5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get base =
      some (.i64 (count.denote funs env)) := by
    rw [(((hF4.mono (base := base + 1) (by omega)).trans f5).below base (by omega)).1]
    exact hN3
  have hI5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get (base + 1) =
      some (.i64 0) :=
    Locals.get_setLocal_same hLow4 (Locals.lt_total hHigh4)
  have hold5 : LocalsHold (setLocal { s4 with values := s.values } (base + 1) (.i64 0))
      (base + 2) tTy.types ws0 :=
    hold4.keep (lo := base + 2) (by simp)
      (fun j hj _ => ⟨by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl⟩) le_rfl
      (by rw [a0.rep.length, hh4]; omega)
  -- The exit at either test: the release of the outer variables that only the loop uses, and the
  -- load of the state.
  have hExit : ∀ heapX stX sX wsX (vals : List Value), vals = s.values →
      LocalsHold sX (base + 2) tTy.types wsX →
      After env slots (fun i => live i || (Expr.loop count init cond body).uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) base heap store s tTy
        ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
        ((Expr.loop count init cond body).denote funs env) heapX stX sX wsX →
      ((Expr.loop count init cond body).depthCalls = false →
        heapX.top.toNat ≤ heap.top.toNat + (Expr.loop count init cond body).allocs funs bounds (slots.map Slot.mode) live env) →
      wp m (releaseWhere Γ' slots (fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) ++
        (loadCode h (base + 2) tTy.types ++ rest)) Q stX { sX with values := vals } host := by
    intro heapX stX sX wsX vals hv holdX aX hTopX
    subst hv
    refine After.releaseT hm (live := live)
      (sel := fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) hVars aX
      (fun i h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; exact loop_sel _ _ _ h.1)
      (fun i h => by simp [h]) fun heap' store' a' hTopR => ?_
    refine wp_loadCode wsX a'.rep.typed (aX.frame.half.trans hh) holdX ?_
    exact hNext heap' store' sX wsX a' fun hd => by
      have := hTopX hd; have := congrArg UInt64.toNat hTopR; omega
  -- The loop.  The invariant holds the count, the index `i`, and the state after `i` passes, and
  -- the count less the index decreases.
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ heapI wsI, ∃ i : UInt64, i ≤ count.denote funs env ∧
      si.get base = some (.i64 (count.denote funs env)) ∧ si.get (base + 1) = some (.i64 i) ∧
      LocalsHold si (base + 2) tTy.types wsI ∧
      After env slots (fun i => live i || (Expr.loop count init cond body).uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) base heap store s tTy
        ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) heapI st si wsI ∧
      ((Expr.loop count init cond body).depthCalls = false →
        heapI.top.toNat + Expr.loopRest funs bounds (slots.map Slot.mode) live init cond body env
          ((count.denote funs env).toNat - i.toNat) i
          (loopState (init.denote funs env)
            (fun i acc => bif cond.denote funs (.cons acc env) then
              body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) ≤
          heap.top.toNat + (Expr.loop count init cond body).allocs funs bounds (slots.map Slot.mode) live env))
    (fun _ s' => match s'.get (base + 1) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2', ws0, 0, UInt64.zero_le, hN5, hI5, hold5, a0.reframe hF5, fun hd => by
      simpa only [UInt64.toNat_zero, Nat.sub_zero, loopState] using hTopEntry hd⟩ ?_
  rintro st si ⟨heapI, wsI, i, hiN, hNi, hii, holdi, aI, hInv⟩
  simp only [wp_localGet_cons, Locals.get_values, hii, hNi, wp_geUI64_cons, wp_br_if_cons]
  by_cases hge : count.denote funs env ≤ i
  · -- The index reached the count.
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    have hieq := UInt64.le_antisymm hiN hge
    rw [hieq, loopState_eq] at aI
    exact hExit _ _ _ _ _ rfl holdi aI fun hd => by
      have := hInv hd
      rw [hieq, Nat.sub_self, Expr.loopRest_zero] at this
      omega
  -- One more pass, if the condition holds.
  have hlt : i < count.denote funs env := UInt64.not_le.mp hge
  have hk : (count.denote funs env).toNat - i.toNat =
      ((count.denote funs env).toNat - i.toNat - 1) + 1 := by
    have := UInt64.lt_iff_toNat_lt.mp hlt; omega
  have hsucc : (i + 1).toNat = i.toNat + 1 := by
    have := UInt64.lt_iff_toNat_lt.mp hlt
    have := (count.denote funs env).toNat_lt
    rw [UInt64.toNat_add]; simp; omega
  simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte]
  have hhi : si.half = h := aI.frame.half.trans hh
  -- The condition's context: the state, borrowed, as variable 0.
  have hdAll : ∀ j, cond.uses (j + 1) = true →
      (live j || cond.uses (j + 1) || body.uses (j + 2)) = true := fun j h => by simp [h]
  have hVarsC : Holds (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
      (⟨base + 2, .borrowed⟩ :: slots)
      (fun j => (j == 0 ||
        shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) || cond.uses j)
      (base + 2 + tTy.width) heapI st si :=
    Holds.push ((aI.holds.mono (by omega)).live_mono fun j hj => cond_live_outer _ _ hdAll j hj)
      holdi aI.rep.borrow
      ((aI.apart.borrow aI.rep).live_mono fun j hj => cond_live_outer _ _ hdAll j hj)
  refine condSpec _ (⟨base + 2, .borrowed⟩ :: slots)
    (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) h
    (base + 2 + tTy.width) heapI st si hhi (aI.frame.params.trans hpv) hVarsC aI.step.at_
    (by rw [aI.step.cap m]; exact hCap)
    (by rw [aI.frame.params]; omega) (by omega) hPcd _ _
    ((hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun h => by
      have h' : (cond.aborts || slots.any (·.mode == .owned)) = true := by
        simpa [List.any_cons] using h
      simp only [Expr.aborts]; exact loop_trap_cond _ _ _ _ _ h') fun hd hw => hw.of_le
        (by
          have := hInv hd
          have := Expr.loopRest_cond_le (funs := funs) (bounds := bounds)
            (modes := slots.map Slot.mode) (live := live) (init := init) (cond := cond)
            (body := body) (env := env) (n := (count.denote funs env).toNat - i.toNat - 1) (i := i)
            (x := loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
          rw [← hk] at this
          simp only [List.map_cons]; omega)
        (aI.step.cap m)).imp fun _ h => h)
    fun heapC stC sC wsC aC hTopC => ?_
  have hRC := aC.rep
  simp only [Ty.rep_bool] at hRC
  subst hRC
  have aI2 := After.test aI aC (by omega) (cond_live _ _ hdAll) rfl
  have hiiC : sC.get (base + 1) = some (.i64 i) :=
    (aC.frame.below (base + 1) (by omega)).1.trans hii
  have hNiC : sC.get base = some (.i64 (count.denote funs env)) :=
    (aC.frame.below base (by omega)).1.trans hNi
  have holdC : LocalsHold sC (base + 2) tTy.types wsI :=
    (LocalsHold.frame aC.frame (by rw [aI.rep.length, Ty.types_length])
      (by rw [Ty.types_length])).mpr holdi
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons, wp_br_if_cons]
  cases hcv : cond.denote funs (Env.cons (loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
        body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
  · -- The condition fails: the state stays for the remaining passes.
    simp (config := { decide := true }) only [↓reduceIte, List.take_zero, List.drop_zero,
      List.nil_append]
    have hStop := loopState_stop (init.denote funs env)
      (fun acc => cond.denote funs (.cons acc env))
      (fun i acc => body.denote funs (.cons acc (.cons i env))) hcv _
      (UInt64.le_iff_toNat_le.mp hiN)
    rw [← hStop, loopState_eq] at aI2
    exact hExit _ _ _ _ _ rfl holdC aI2 fun hd => by
      have h1 := hInv hd
      rw [hk, Expr.loopRest_false hcv] at h1
      have h2 := hTopC (hdl hd).2.2.1
      simp only [List.map_cons] at h2
      omega
  simp (config := { decide := true }) only [↓reduceIte]
  -- The condition holds: the pass runs the body.
  set sB : Locals := { sC with values := si.values }
  have aB0 := aI2.reframe (Frame.ofValues (s := sC) (values := si.values))
  have holdB : LocalsHold sB (base + 2) tTy.types wsI := holdC
  have hiiB : sB.get (base + 1) = some (.i64 i) := hiiC
  have hNiB : sB.get base = some (.i64 (count.denote funs env)) := hNiC
  have holdIdx : LocalsHold sB (base + 1) Ty.word.types [.i64 i] := fun k hk => by
    obtain rfl : k = 0 := by simpa using hk
    simpa [Ty.types, slotIndex] using hiiB
  have hhB : sB.half = h := aB0.frame.half.trans hh
  have hRoomi : base + 2 + tTy.width + max body.width (copyWidth tTy) ≤ h := by omega
  -- The body's context: the state as variable 0 and the index as variable 1.
  have hIdx := Holds.push (t := .word) (v := i) (mode := .borrowed)
    (live' := fun j => decide (j + 1 < 2) ||
      shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) (j + 1) ||
        body.uses (j + 1))
    ((aB0.holds.mono (Nat.le_add_right base 1)).live_mono fun j h => by simpa using h) holdIdx
    rfl
    (Holds.Apart.ofScalar rfl)
  have hVarsB : Holds (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j < 2) ||
        shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j || body.uses j)
      (base + 2 + tTy.width) heapC stC sB :=
    Holds.push (hIdx.mono (base' := base + 2) (by simp [Ty.width])) holdB aB0.rep
      (Holds.Apart.push (u := .word) (v := i) (mv := .borrowed)
        (live' := fun j => decide (j + 1 < 2) ||
          shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) (j + 1) ||
            body.uses (j + 1))
        (aB0.apart.live_mono fun j h => by simpa using h) holdIdx rfl
        fun _ _ _ c hc => by simp [Ty.regions, Ty.reads] at hc)
  have hRelease : (if (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) = .owned ∧
        body.uses 0 = false then releaseCode tTy (base + 2) else []) =
      (if body.uses 0 = false then [0] else []).flatMap
        (releaseVar (tTy :: .word :: Γ') (⟨base + 2, (init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
          ⟨base + 1, .borrowed⟩ :: slots)) := by
    cases body.uses 0 <;>
      cases (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) <;> simp [releaseVar]
  rw [hRelease]
  have hInv' := fun hd => by
    have h1 := hInv hd
    rw [hk, Expr.loopRest_true hcv] at h1
    exact h1
  have hTopC' := fun hd => by
    have h2 := hTopC ((hdl hd).2.2.1)
    simp only [List.map_cons] at h2
    exact h2
  refine wp_releaseVarsT hm _ (by split <;> simp) hVarsB aB0.step.at_ (by split <;> simp)
    fun heap2 store2 e2 hTopRel => ?_
  have e2' := e2.mono
    (live' := fun j =>
      shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j || body.uses j)
    fun j h => by
      match j with
      | 0 =>
        have h0 : body.uses 0 = true := by simpa [shift] using h
        simp [h0]
      | 1 => simp
      | k + 2 => split <;> simpa using h
  refine bodySpec _ _ (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) h
    (base + 2 + tTy.width) heap2 store2 sB hhB (aB0.frame.params.trans hpv) e2'.holds e2'.step.at_
    (by rw [e2'.step.cap m, aB0.step.cap m]; exact hCap) (by rw [aB0.frame.params]; omega)
    (by omega) hPb _ _
    ((hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun h => by
      have hmo := (Expr.loop count init cond body).mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact loop_trap_body _ _ _ _ _ _ _ (fun hv => hmo (beq_iff_eq.mp hv)) rfl h) fun hd hw =>
        hw.of_le (by
          have := hInv' hd; have := hTopC' hd; have := congrArg UInt64.toNat hTopRel
          simp only [List.map_cons]; omega)
        (by rw [e2'.step.cap m, aB0.step.cap m])).imp
        fun _ h => h)
    fun heap6 store6 s6 ws6 aB hTopB => ?_
  have hp6 : s6.params = s.params := aB.frame.params.trans aB0.frame.params
  refine After.coerceB hm aB
    (fun h => loop_mode (f := fun md => body.mode (md :: .borrowed :: slots.map Slot.mode)) h)
    le_rfl (by rw [hp6]; omega) (aB.frame.half.trans hhB) (by omega)
    (by rw [aB.step.cap m, e2'.step.cap m, aB0.step.cap m]; exact hCap)
    (fun hs ht _ => (hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy (body.mode (((init.mode (slots.map Slot.mode)).join (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))) :: .borrowed ::
          slots.map Slot.mode)) ((init.mode (slots.map Slot.mode)).join (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
          (body.denote funs (.cons (loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) =
          tTy.copyCost (body.denote funs (.cons (loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) := by
        rw [coerceCost, if_pos ⟨by simpa only [List.map_cons] using hs, ht⟩]
      exact hw.of_le (by
          have := hInv' hd; have := hTopC' hd; have := congrArg UInt64.toNat hTopRel
          have h6 := hTopB (hdl hd).2.2.2
          simp only [List.map_cons] at h6
          omega)
        (by rw [aB.step.cap m, e2'.step.cap m, aB0.step.cap m])).imp fun _ h => h)
    fun heap6' store6 s6 ws6 aB hTopCo2 => ?_
  have hp6 : s6.params = s.params := aB.frame.params.trans aB0.frame.params
  have hh6 : s6.half = h := aB.frame.half.trans hhB
  refine wp_storeCode ws6 h (base + 2) tTy.types s6 si.values aB.rep.typed hh6
    (by rw [hp6]; omega) (by rw [Ty.types_length, hh6]; omega) fun s7 hF7 hold7 _ => ?_
  have hp7' : s7.params = s.params := hF7.params.trans hp6
  have hh7 : s7.half = h := hF7.half.trans hh6
  have hget7 : ∀ j < base + 2, s7.get j = sB.get j := fun j hj => by
    rw [(hF7.below j hj).1]
    exact (aB.frame.below j (by omega)).1
  -- The next index, in local `base + 1`.
  simp only [wp_localGet_cons, Locals.get_values, hget7 (base + 1) (by omega), hiiB,
    wp_constI64_cons, wp_addI64_cons]
  have hLow7 : ({ s7 with values := si.values } : Locals).params.length ≤ base + 1 := by
    show s7.params.length ≤ base + 1; rw [hp7']; omega
  have hHigh7 : base + 1 < s7.half := by rw [hh7]; omega
  refine wp_localSet_local (s := s7) (vs := si.values) hLow7 (Locals.lt_total hHigh7) ?_
  have hget8 : (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))).get
      (base + 1) = some (.i64 (i + 1)) :=
    Locals.get_setLocal_same hLow7 (Locals.lt_total hHigh7)
  have hold8 : LocalsHold (setLocal { s7 with values := si.values } (base + 1)
      (.i64 (i + 1))) (base + 2) tTy.types ws6 :=
    hold7.keep (lo := base + 2) (by simp)
      (fun j hj _ => ⟨by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl⟩) le_rfl
      (by rw [aB.rep.length, hh7]; omega)
  -- The state after `i + 1` iterations: the facts of the body's code for the outer context.
  have aB' := After.prepend hVarsB e2' aB (fun j h => live_right _ _ _ h) fun j h => by
    simp [h]
  have hNew : ∀ r, (∀ b ∈ ((init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))).fresh stC tTy wsI
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat),
        regionsDisjoint r b) →
      ((init.mode (slots.map Slot.mode)).join
          (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)) = .owned → ∀ w,
        LocalsHold sB (base + 2) tTy.types w → w.length = tTy.width →
        ∀ b ∈ tTy.blocks stC w (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat),
        regionsDisjoint r b) ∧
      (Mode.borrowed = .owned → ∀ w, LocalsHold sB (base + 1) Ty.word.types w →
        w.length = Ty.word.width →
        ∀ b ∈ Ty.word.blocks stC w i, regionsDisjoint r b) := by
    intro r hFresh
    refine ⟨fun hmo w hw hlw b hb => ?_, fun hmo => nomatch hmo⟩
    obtain rfl := LocalsHold.unique hw holdB (hlw.trans aB0.rep.length.symm)
    rw [hmo] at hFresh
    exact hFresh b hb
  have aNext := After.bind2 hVars aB0 (Frame.refl base sB) aB' (by omega) hNew
    (fun j h => by simpa using h)
    (fun j h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ h) fun _ h => h
  have hv : loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) (i + 1).toNat =
      body.denote funs (.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env)) := by
    rw [hsucc, loopState, UInt64.ofNat_toNat]
    simp only [hcv, Bool.cond_true]
  rw [wp_br_cons]
  dsimp only
  refine ⟨⟨heap6', ws6, i + 1, UInt64.le_iff_toNat_le.mpr ?_, ?_, hget8, hold8, ?_, ?_⟩, ?_⟩
  · have := UInt64.lt_iff_toNat_lt.mp hlt
    omega
  · rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values, hget7 base (by omega)]
    exact hNiB
  · rw [hv]
    exact aNext.reframe ((hF7.mono (base := base) (by omega)).trans
      ((Frame.setValues (s := s7) (vs := si.values) (base := base + 1) hLow7 le_rfl
        hHigh7).mono (base := base)
        (by omega)))
  · intro hd
    rw [hv, hsucc, show (count.denote funs env).toNat - (i.toNat + 1) =
      (count.denote funs env).toNat - i.toNat - 1 by omega]
    have := hInv' hd; have := hTopC' hd; have := congrArg UInt64.toNat hTopRel
    have h6 := hTopB (hdl hd).2.2.2
    simp only [List.map_cons] at h6 hTopCo2
    omega
  · have := UInt64.lt_iff_toNat_lt.mp hlt
    simp only [hget8]
    omega

/-- `LeanExe.build`: the count in local `base`, a trap at `unreachable` when it is `2 ^ 29` or
more, a new owned array at the address in local `base + 1`, and the index in local `base + 2`.
The invariant at the top of the WebAssembly `loop` holds an owned array of the count's length
whose elements below the index are the built ones, with the facts of `After` for the outer
variables live in the loop.  Each iteration runs the element's code in the context with the
index, which keeps every region, and stores the element. -/
theorem specB_build (hm : Runtime m) {Γ' : List Ty} {e : Elem} {count : Expr S Γ' .word}
    {elem : Expr S (.word :: Γ') (.elem e)}
    (countSpec : ∀ env slots live, CodeSpecB m funs bounds host pv count env slots live)
    (elemSpec : ∀ env slots live, CodeSpecB m funs bounds host pv elem env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.build count elem) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (3 + max elem.width (e.width + 1))
  have he := Nat.le_max_right count.width (3 + max elem.width (e.width + 1))
  have he1 := Nat.le_max_left elem.width (e.width + 1)
  have he2 := Nat.le_max_right elem.width (e.width + 1)
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hT : (Expr.build count elem).allocs funs bounds (slots.map Slot.mode) live env = count.allocs funs bounds (slots.map Slot.mode) (fun i => live i || elem.uses (i + 1)) env + allocCost (((count.denote funs env).toNat * e.width + 1) * 8) + sumBelow (fun k => elem.allocs funs bounds (.borrowed :: slots.map Slot.mode)
          (shift 1 (fun i => live i || elem.uses (i + 1))) (.cons (UInt64.ofNat k) env)) (count.denote funs env).toNat := rfl
  have hdK : (Expr.build count elem).depthCalls = false → count.depthCalls = false ∧
      elem.depthCalls = false := fun hd => by
    simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd
  have hTrapW : ¬heap.Within store m
      ((Expr.build count elem).allocs funs bounds (slots.map Slot.mode) live env) →
      TrapOK true Q := fun hw =>
    hTrap.of_imp fun _ => by simp [trapFlag, Expr.aborts, hw]
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || elem.uses (i + 1)) || count.uses i) = true →
      (live i || (Expr.build count elem).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  refine countSpec env slots (fun i => live i || elem.uses (i + 1)) h base heap store s hh hpv
    (hVars.live_mono hCountIn) hAt hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopK => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hHigh1 : base < s1.half := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  set s2 := setLocal { s1 with values := s.values } base (.i64 (count.denote funs env)) with hs2
  have f2 : Frame base s1 s2 := Frame.setValues hLow1 le_rfl hHigh1
  have hN2 : s2.get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hh2 : s2.half = h := by simp only [hs2, Locals.half_setLocal, Locals.half_values, hh1]
  -- The trap when the count's words would be `2 ^ 29` or more.
  simp only [wp_localGet_cons, hN2, wp_constI64_cons, wp_geUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hBig : UInt64.ofNat ((536870912 + e.width - 1) / e.width) ≤ count.denote funs env
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wp_unreachable_cons]
    refine hTrapW (fun hw => ?_) _
    have hLim' : (536870912 + e.width - 1) / e.width < UInt64.size := by
      rw [show UInt64.size = 18446744073709551616 from rfl]
      have hd : (536870912 + e.width - 1) / e.width ≤ 536870912 :=
        Nat.div_le_of_le_mul (by omega)
      omega
    have hge := UInt64.le_iff_toNat_le.mp hBig
    rw [UInt64.toNat_ofNat_of_lt' hLim'] at hge
    have hlt := Nat.lt_mul_div_succ (536870912 + e.width - 1) hk
    have hmul := Nat.mul_le_mul_right e.width hge
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at hlt
    unfold Heap.Within at hw
    rw [hT] at hw
    unfold allocCost at hw
    omega
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
  rw [wp_nil]
  dsimp only
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  have hLim : (536870912 + e.width - 1) / e.width < UInt64.size := by
    rw [show UInt64.size = 18446744073709551616 from rfl]
    have hd : (536870912 + e.width - 1) / e.width ≤ 536870912 :=
      Nat.div_le_of_le_mul (by omega)
    omega
  have hcLim : (count.denote funs env).toNat < (536870912 + e.width - 1) / e.width := by
    have := UInt64.not_le.mp hBig
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hLim] at this
    exact this
  have hck := build_limit hk hcLim
  have hcSmall : (count.denote funs env).toNat ≤ (count.denote funs env).toNat * e.width :=
    Nat.le_mul_of_pos_right _ hk
  -- The count of words, in local `base + 2`.
  show wp m _ Q store1 s2 host
  simp only [wp_localGet_cons, hN2]
  rw [wp_scaleCode, show count.denote funs env = UInt64.ofNat (count.denote funs env).toNat by simp,
    words_scale hk hck]
  have hLowT : ({ s2 with values := s.values } : Locals).params.length ≤ base + 2 := by
    show s1.params.length ≤ base + 2; rw [hp1]; omega
  have hHighT : base + 2 < ({ s2 with values := s.values } : Locals).half := by
    simp only [Locals.half_values, hh2]; omega
  refine wp_localSet_local hLowT (Locals.lt_total hHighT) ?_
  set s3 := setLocal { s2 with values := s.values } (base + 2)
    (.i64 (UInt64.ofNat ((count.denote funs env).toNat * e.width))) with hs3
  have hT3 : s3.get (base + 2) =
      some (.i64 (UInt64.ofNat ((count.denote funs env).toNat * e.width))) :=
    Locals.get_setLocal_same hLowT (Locals.lt_total hHighT)
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLowT (by omega), Locals.get_values]; exact hN2
  have f3 : Frame base s2 s3 := Frame.setValues hLowT (by omega) (by simpa using hHighT)
  have hh3 : s3.half = h := by simp only [hs3, Locals.half_setLocal, Locals.half_values, hh2]
  have hp3 : s3.params = s.params := by
    simp only [hs3, hs2, setLocal]; exact hp1
  -- The new array, at the address in local `base + 1`.
  have hTn : (UInt64.ofNat ((count.denote funs env).toNat * e.width)).toNat =
      (count.denote funs env).toNat * e.width :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hLow4 : s3.params.length ≤ base + 1 := by rw [hp3]; omega
  have hHigh4' : base + 1 < s3.half := by rw [hh3]; omega
  have hHigh4 := Locals.lt_total hHigh4'
  refine wp_allocArray (c := allocCost (((count.denote funs env).toNat * e.width + 1) * 8)) hm e1.step.at_ (by rw [e1.step.cap m]; exact hCap)
    (by rw [hTn]; unfold allocCost; omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.shift (hTopK (hdK hd).1)
      (by rw [hT]; omega) (e1.step.cap m))
    (by rw [hTn]; exact hck) hT3 hLow4 hHigh4 (by omega)
    fun heap2 store2 root words hSize hStepA hOwned hTopA => ?_
  rw [hTn] at hSize
  set s4 := setLocal { s3 with values := s3.values } (base + 1) (.i64 root) with hs4
  have f4 : Frame base s3 s4 := Frame.setValues hLow4 (by omega) hHigh4'
  have hF4 : Frame base s s4 := e1.frame.trans (f2.trans (f3.trans f4))
  have hN4 : s4.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hN3
  have hRoot4 : s4.get (base + 1) = some (.i64 root) := Locals.get_setLocal_same hLow4 hHigh4
  have hh4 : s4.half = h := by simp only [hs4, Locals.half_setLocal, Locals.half_values, hh3]
  have hp4 : s4.params = s.params := by simp only [hs4, setLocal]; exact hp3
  -- The facts of `After` for the new array.
  have hVars1 : Holds env slots (fun i => live i || elem.uses (i + 1)) base heap1 store1 s4 :=
    e1.holds.agree (f2.trans (f3.trans f4))
  have a0 : After env slots (fun i => live i || (Expr.build count elem).uses i)
      (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heap2
      store2 s4 [.i64 root] := by
    refine ⟨(e1.step.trans hStepA fun _ hr => ⟨hr, fun _ => trivial⟩).mono
      (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) (fun _ h => h), hF4,
      hVars1.step hStepA (fun _ _ _ _ _ _ _ _ => trivial), ⟨root, rfl, hOwned⟩, ?_⟩
    intro u y hy _ wy hwy hly b hb c hc
    obtain ⟨hSame, hFresh⟩ := hVars1.regions_after hStepA hy hwy hly fun _ _ => trivial
    rw [hSame] at hc
    exact regionsDisjoint_symm (hFresh c hc b hb)
  -- The index, in local `base + 2`.
  simp only [wp_constI64_cons]
  have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤ base + 2 := by
    show s4.params.length ≤ base + 2; rw [hp4]; omega
  have hHigh5' : base + 2 < s4.half := by rw [hh4]; omega
  have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
  refine wp_localSet_local hLow5 hHigh5 ?_
  set s5 := setLocal { s4 with values := s4.values } (base + 2) (.i64 0) with hs5
  have hF5 : Frame base s4 s5 := Frame.setValues hLow5 (by omega) hHigh5'
  have hN5 : s5.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow5 (by omega), Locals.get_values]; exact hN4
  have hRoot5 : s5.get (base + 1) = some (.i64 root) := by
    rw [Locals.get_setLocal_ne hLow5 (by omega), Locals.get_values]; exact hRoot4
  have hIdx5 : s5.get (base + 2) = some (.i64 0) := Locals.get_setLocal_same hLow5 hHigh5
  -- The loop.  The invariant holds an array of the count's elements' words whose elements below
  -- the index `i` hold the built ones, and the count less the index decreases.
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ heapI words, ∃ i : Nat, i ≤ (count.denote funs env).toNat ∧
      words.size = (count.denote funs env).toNat * e.width ∧
      (∀ i', i' < i → ∀ j, j < e.width → words[i' * e.width + j]! =
        (e.toWords (elem.denote funs (.cons (UInt64.ofNat i') env)))[j]!) ∧
      si.get base = some (.i64 (count.denote funs env)) ∧
      si.get (base + 1) = some (.i64 root) ∧ si.get (base + 2) = some (.i64 (UInt64.ofNat i)) ∧
      After env slots (fun i => live i || (Expr.build count elem).uses i)
        (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heapI
        st si [.i64 root] ∧
      ((Expr.build count elem).depthCalls = false →
        heapI.top.toNat ≤ heap.top.toNat + (count.allocs funs bounds (slots.map Slot.mode) (fun i => live i || elem.uses (i + 1)) env + allocCost (((count.denote funs env).toNat * e.width + 1) * 8) +
          sumBelow (fun k => elem.allocs funs bounds (.borrowed :: slots.map Slot.mode)
          (shift 1 (fun i => live i || elem.uses (i + 1))) (.cons (UInt64.ofNat k) env)) i)))
    (fun _ si => match si.get (base + 2) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2, words, 0, Nat.zero_le _, hSize, fun _ h => absurd h (Nat.not_lt_zero _), hN5,
      hRoot5, hIdx5, a0.reframe hF5, fun hd => by
        have := hTopK (hdK hd).1; simp only [sumBelow]; omega⟩ ?_
  rintro st si ⟨heapI, words, i, hi, hSize, hPrefix, hNi, hRooti, hIdxi, aI, hInv⟩
  have hi64 : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wp_localGet_cons, Locals.get_values, hIdxi, hNi, wp_geUI64_cons, wp_br_if_cons]
  by_cases hDone : count.denote funs env ≤ UInt64.ofNat i
  · -- The array is complete: the release of the outer variables that only the element reads,
    -- and the array's address.
    have hiEq : i = (count.denote funs env).toNat := by
      rw [UInt64.le_iff_toNat_le, hi64] at hDone; omega
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    have hWords : words = e.words (LeanExe.build (count.denote funs env)
        fun i => elem.denote funs (.cons i env)) := by
      refine Elem.words_ext e (by rw [hSize]; simp [LeanExe.build]) fun i' hi' j hj => ?_
      have hi'' : i' < (count.denote funs env).toNat := by simpa [LeanExe.build] using hi'
      rw [hPrefix i' (by omega) j hj, getElem!_pos (LeanExe.build (count.denote funs env)
        fun i => elem.denote funs (.cons i env)) i' hi']
      simp [LeanExe.build]
    rw [hWords] at aI
    refine After.releaseT hm (s1 := si) (live := live)
      (sel := fun i => elem.uses (i + 1) && !live i) hVars (After.ofWords aI)
      (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; simp [h.1]) (fun i h => by simp [h])
      fun heap' store' a' hTopR => ?_
    simp only [wp_localGet_cons, Locals.get_values, hRooti]
    simpa [setLocal, hs2] using hNext heap' store' si [.i64 root] a' fun hd => by
      have h1 := hInv hd; have := congrArg UInt64.toNat hTopR
      rw [hiEq] at h1
      rw [hT]; omega
  -- One more element.
  have hLess : i < (count.denote funs env).toNat := by
    rw [UInt64.le_iff_toNat_le, hi64] at hDone; omega
  simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
  -- The element, in the context with the index as variable 0.
  have holdIdx : LocalsHold si (base + 2) Ty.word.types [.i64 (UInt64.ofNat i)] :=
    fun j hj => by
      obtain rfl : j = 0 := by simpa using hj
      simpa [Ty.types, slotIndex] using hIdxi
  have hhi : si.half = h := aI.frame.half.trans hh
  have hLE : ∀ j, (shift 1 (fun i => live i || elem.uses (i + 1)) (j + 1) ||
      elem.uses (j + 1)) = true → (live j || elem.uses (j + 1)) = true := fun j h => by
    simp only [shift_add] at h; exact live_dup _ _ h
  have hVarsI : Holds env slots (fun i => live i || elem.uses (i + 1)) (base + 2) heapI st si :=
    aI.holds.mono (by omega)
  have hVarsE := (Holds.push (t := .word) (v := UInt64.ofNat i) (mode := .borrowed)
    (live' := fun j => shift 1 (fun i => live i || elem.uses (i + 1)) j || elem.uses j)
    (hVarsI.live_mono hLE) holdIdx rfl (Holds.Apart.ofScalar rfl)).mono
    (base' := base + 3) (by simp [Ty.width])
  refine elemSpec _ _ (shift 1 fun i => live i || elem.uses (i + 1)) h (base + 3) heapI st si hhi
    (aI.frame.params.trans hpv) hVarsE aI.step.at_ (by rw [aI.step.cap m]; exact hCap)
    (by show si.params.length ≤ base + 3; rw [aI.frame.params]; omega) (by omega)
    hPlace.2 _ _ ((hTrap.part (fun h => by simp [Expr.depthCalls, h])
        (fun _ => by simp [Expr.aborts]) fun hd hw => hw.of_le (by
          have := hInv hd
          have := sumBelow_mono (fun k => elem.allocs funs bounds (.borrowed :: slots.map Slot.mode)
          (shift 1 (fun i => live i || elem.uses (i + 1))) (.cons (UInt64.ofNat k) env)) (show i + 1 ≤ (count.denote funs env).toNat by omega)
          simp only [sumBelow] at this
          simp only [List.map_cons]; rw [hT]; omega) (aI.step.cap m)).imp fun _ h => h)
    fun heapE stE sE wsE aE hTopE => ?_
  have hRE := Ty.rep_elem.mp aE.rep
  subst hRE
  -- The element's facts for the outer context, after the array's.
  have aE1 := After.bind (base := base + 2) hVarsI
    (After.refl (t := .word) (mode := .borrowed) (v := UInt64.ofNat i)
      (ws := [.i64 (UInt64.ofNat i)]) aI.step.at_ hVarsI (fun _ h => h) rfl rfl
      (Holds.Apart.ofScalar rfl))
    (Frame.refl _ _) holdIdx aE hLE (fun _ h => h) fun _ h => h
  have aE2 := aE1.lower aI.holds (by omega) fun _ h => h
  obtain ⟨hStep, hFrame, hRep1, hApart1, -⟩ := After.seq hVars aI aE2
    (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h) fun _ h => h
  have aI2 : After env slots (fun i => live i || (Expr.build count elem).uses i)
      (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heapE
      stE sE [.i64 root] :=
    ⟨hStep.mono (fun _ h => h) fun b hb => List.mem_append_left _ hb, hFrame, aE2.holds,
      hRep1, hApart1⟩
  have hpE : sE.params = s.params := aE.frame.params.trans aI.frame.params
  have hhE : sE.half = h := aE.frame.half.trans hhi
  have hgetE : ∀ j < base + 3, sE.get j = si.get j := fun j hj => (aE.frame.below j hj).1
  -- The element's words, from local `base + 3` on.
  refine wp_storeCode (e.values (elem.denote funs (.cons (UInt64.ofNat i) env))) h (base + 3)
    e.types sE si.values (by rw [e.values_length, e.types_length]) hhE
    (by rw [hpE]; omega) (by rw [e.types_length, hhE]; omega)
    fun s6 f6 hold6 _ => ?_
  have hp6 : s6.params = s.params := f6.params.trans hpE
  have hh6 : s6.half = h := f6.half.trans hhE
  have hget6 : ∀ j < base + 3, s6.get j = si.get j := fun j hj =>
    (f6.below j hj).1.trans (hgetE j hj)
  -- The position of the element's first word, in local `base + 3 + k`.
  simp only [wp_localGet_cons, Locals.get_values, hget6 (base + 2) (by omega), hIdxi]
  rw [wp_scaleCode, words_scale hk
    (lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hLess)) hck)]
  have hLow7 : ({ s6 with values := si.values } : Locals).params.length ≤ base + 3 + e.width := by
    show s6.params.length ≤ _; rw [hp6]; omega
  have hHigh7' : base + 3 + e.width < s6.half := by rw [hh6]; omega
  have hHigh7 := Locals.lt_total (s := { s6 with values := si.values }) hHigh7'
  refine wp_localSet_local hLow7 hHigh7 ?_
  set s7 := setLocal { s6 with values := si.values } (base + 3 + e.width)
    (.i64 (UInt64.ofNat (i * e.width))) with hs7
  have f7 : Frame (base + 3) s6 s7 := Frame.setValues hLow7 (by omega) hHigh7'
  have hW7 : s7.get (base + 3 + e.width) = some (.i64 (UInt64.ofNat (i * e.width))) :=
    Locals.get_setLocal_same hLow7 hHigh7
  have hget7 : ∀ j < base + 3, s7.get j = si.get j := fun j hj =>
    (f7.below j hj).1.trans (hget6 j hj)
  have hh7 : s7.half = h := f7.half.trans hh6
  have hold7 : LocalsHold s7 (base + 3) e.types
      (List.zipWith typedValue e.types
        (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env)))) := by
    rw [e.values_typed]
    intro j hj
    have := hold6 j hj
    rw [e.values_length] at hj
    rw [show s7.half = s6.half from f7.half]
    rw [← this]
    simp only [hs7]
    rw [Locals.get_setLocal_ne hLow7, Locals.get_values]
    cases hty : e.types.getD j .i64 <;> simp only [slotIndex] <;> omega
  -- The writes of the element's words.
  have hik : i * e.width + e.width ≤ words.size := by
    rw [hSize]; have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hLess)
    rw [Nat.succ_mul] at this; exact this
  have hik64 : (UInt64.ofNat (i * e.width)).toNat = i * e.width :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  refine wp_storeWordsCode 0 (base + 3) e.types
    (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env))) words stE s7
    (aI2.reframe ((f6.mono (by omega)).trans (f7.mono (by omega)))) hh7
    (by rw [hget7 (base + 1) (by omega)]; exact hRooti) hW7 hold7
    (by rw [e.toWords_length, e.types_length]) (by rw [hik64, e.types_length]; omega)
    fun store8 a8 => ?_
  rw [hik64, Nat.add_zero] at a8
  -- The next index, in local `base + 2`.
  simp only [wp_localGet_cons, hget7 (base + 2) (by omega), hIdxi, wp_constI64_cons,
    wp_addI64_cons]
  have hLow9 : ({ s7 with values := s7.values } : Locals).params.length ≤ base + 2 := by
    show s7.params.length ≤ base + 2; rw [f7.params, hp6]; omega
  have hHigh9' : base + 2 < s7.half := by rw [hh7]; omega
  have hHigh9 := Locals.lt_total (s := { s7 with values := s7.values }) hHigh9'
  refine wp_localSet_local (s := s7) (vs := s7.values) hLow9 hHigh9 ?_
  have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
    rw [UInt64.ofNat_add]; rfl
  have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hIdx9 := Locals.get_setLocal_same (v := .i64 (UInt64.ofNat i + 1)) hLow9 hHigh9
  rw [wp_br_cons]
  dsimp only
  have hfit : i * e.width + (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env))).length ≤
      words.size := by rw [e.toWords_length]; exact hik
  refine ⟨⟨heapE, _, i + 1, by omega, by rw [writeWords_size, hSize], fun i' hi' j hj => ?_,
    ?_, ?_, by rw [hIdx9, hSucc],
    a8.reframe (Frame.setValues hLow9 (by omega) hHigh9'), ?_⟩, ?_⟩
  · rw [writeWords_getElem! _ _ _ hfit, e.toWords_length]
    by_cases hii : i' = i
    · subst hii
      rw [if_pos (by omega), show i' * e.width + j - i' * e.width = j by omega]
    · have hlt : i' < i := by omega
      have hout : ¬(i * e.width ≤ i' * e.width + j ∧ i' * e.width + j < i * e.width + e.width) := by
        intro ⟨h1, _⟩
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at this; omega
      rw [if_neg hout]
      exact hPrefix i' hlt j hj
  · rw [Locals.get_setLocal_ne hLow9 (by omega), Locals.get_values, hget7 base (by omega)]
    exact hNi
  · rw [Locals.get_setLocal_ne hLow9 (by omega), Locals.get_values, hget7 (base + 1) (by omega)]
    exact hRooti
  · intro hd
    have := hInv hd; have h6 := hTopE (hdK hd).2
    simp only [List.map_cons] at h6
    simp only [sumBelow]; omega
  · rw [hIdx9]
    simp only [hSucc, hSucc64]
    omega

/-- `x.set! i.toNat v`: the position in local `base`, the value's words from local `base + 1` on,
the array as owned in local `base + 1 + k`, which is `x`'s own block when `x` is owned and dies,
and, when the position is below the size, the position of the element's first word in local
`base + 2 + k` and the writes of the element's words. -/
theorem specB_set (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word} {v : Expr S Γ' (.elem e)}
    (iSpec : ∀ env slots live, CodeSpecB m funs bounds host pv i env slots live)
    (vSpec : ∀ env slots live, CodeSpecB m funs bounds host pv v env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.set x i v) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width (max (1 + v.width) (1 + e.width + copyWidth (.array e)))
  have hv := (Nat.le_max_left (1 + v.width) (1 + e.width + copyWidth (.array e))).trans
    (Nat.le_max_right i.width _)
  have hx := (Nat.le_max_right (1 + v.width) (1 + e.width + copyWidth (.array e))).trans
    (Nat.le_max_right i.width _)
  have hcw : copyWidth (Ty.array e) = 4 := rfl
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hT : (Expr.set x i v).allocs funs bounds (slots.map Slot.mode) live env = i.allocs funs bounds (slots.map Slot.mode) (fun j => live j || j == x.index || v.uses j) env + v.allocs funs bounds (slots.map Slot.mode) (fun j => live j || j == x.index) env + x.ownedCost (slots.map Slot.mode) live (env.get x) := rfl
  have hdS : (Expr.set x i v).depthCalls = false → i.depthCalls = false ∧ v.depthCalls = false :=
    fun hd => by simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index || v.uses k) || i.uses k) = true →
      (live k || (Expr.set x i v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact set_live_index _ _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index || v.uses k) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopI => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWord a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hh1 := e1.frame.half.trans hh
  -- The value's words, from local `base + 1` on.
  refine vSpec env slots (fun k => live k || k == x.index) h (base + 1) heap1 store1 _ hh1
    (hp1.trans hpv) (e1.holds.mono (Nat.le_succ base)) e1.step.at_ (by rw [e1.step.cap m]; exact
        hCap)
    (by rw [hp1]; omega) (by omega) hPlace.2 _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun _ => by simp [Expr.aborts])
      fun hd hw => hw.shift (hTopI (hdS hd).1) (by rw [hT]; omega) (e1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTopV => ?_
  have hR2 := Ty.rep_elem.mp a2.rep
  subst hR2
  have e2a := a2.toEvolves rfl
  have hp2a : s2.params = s.params := e2a.frame.params.trans hp1
  have hh2a : s2.half = h := e2a.frame.half.trans hh1
  refine wp_storeCode (e.values (v.denote funs env)) h (base + 1) e.types s2 s.values
    (by rw [e.values_length, e.types_length]) hh2a (by rw [hp2a]; omega)
    (by rw [e.types_length, hh2a]; omega) fun s2' f2 hold2 _ => ?_
  have f2' : Frame (base + 1) s2 { s2' with values := s.values } := f2.trans Frame.ofValues
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) (base + 1) heap1 store1 _ heap2 store2
      { s2' with values := s.values } :=
    ⟨e2a.step, e2a.frame.trans f2', e2a.holds.agree f2'⟩
  have hp2 : s2'.params = s.params := f2.params.trans hp2a
  have hh2 : s2'.half = h := f2.half.trans hh2a
  have hI2 : s2'.get base = some (.i64 (i.denote funs env)) :=
    (e2.frame.below base (by omega)).1.trans hI1
  -- The array as owned, in local `base + 1 + k`.
  refine specB_ownedVar hm x (s := { s2' with values := s.values }) hh2 (hp2.trans hpv)
    ((e2.holds.mono (by omega)) : Holds env slots
      (fun k => live k || k == x.index) (base + 1 + e.width) heap2 store2 _) e2.step.at_
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s2'.params.length ≤ _; rw [hp2]; omega)
    (by omega) (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le (by
      have := hTopI (hdS hd).1; have := hTopV (hdS hd).2; rw [hT]; omega)
      (by rw [e2.step.cap m, e1.step.cap m]))
    fun heap3 store3 s3 ws3 a3 hTopO => ?_
  obtain ⟨p, hws, hOwned⟩ := a3.rep
  subst hws
  have hp3 : s3.params = s.params := a3.frame.params.trans hp2
  have hh3 : s3.half = h := a3.frame.half.trans hh2
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow3 : ({ s3 with values := s.values } : Locals).params.length ≤ base + 1 + e.width := by
    show s3.params.length ≤ _; rw [hp3]; omega
  have hHigh3' : base + 1 + e.width < s3.half := by rw [hh3]; omega
  have hHigh3 := Locals.lt_total (s := { s3 with values := s.values }) hHigh3'
  refine wp_localSet_local hLow3 hHigh3 ?_
  set s4 : Locals := setLocal { s3 with values := s.values } (base + 1 + e.width) (.i64 p)
    with hs4
  have hP4 : s4.get (base + 1 + e.width) = some (.i64 p) := Locals.get_setLocal_same hLow3 hHigh3
  have hF4 : Frame (base + 1 + e.width) s3 s4 := Frame.setValues hLow3 le_rfl hHigh3'
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (hF4.below base (by omega)).1.trans ((a3.frame.below base (by omega)).1.trans hI2)
  have hold4 : LocalsHold s4 (base + 1) e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans (a3.frame.trans hF4))
      (by rw [e.values_length, e.types_length]) (by rw [e.types_length])).mpr hold2
  have hh4 : s4.half = h := hF4.half.trans hh3
  have hp4 : s4.params = s.params := hF4.params.trans hp3
  have hValues4 : s4.values = s.values := rfl
  have a4 := a3.reframe hF4
  -- The rest of the code, from the array after the writes or without them.
  have hFinish : ∀ (store4 : Store Unit) (s' : Locals) (ws : Array UInt64),
      Frame (base + 1 + e.width) s4 s' → s'.values = s.values →
      ws = e.words ((env.get x).set! (i.denote funs env).toNat (v.denote funs env)) →
      After env slots (fun k => live k || k == x.index) live (base + 1 + e.width) heap2 store2
        { s2' with values := s.values } (.array .word) .owned ws heap3 store4 s' [.i64 p] →
      wp m rest Q store4 { s' with values := .i64 p :: s'.values } host := by
    rintro store4 s' ws _ hv' rfl aX
    have aX1 := (After.ofWords aX).lower e2.holds (by omega) fun k h => by simp [h]
    have aX2 := After.prepend (e1.holds.mono (Nat.le_succ base)) e2 aX1
      (fun k h => by simp [h]) fun k h => by simp [h]
    have aX3 := After.prepend (hVars.live_mono hIn) e1 (aX2.lower e1.holds (Nat.le_succ base)
      fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
    simpa [hv'] using hNext heap3 store4 _ [.i64 p] (aX3.liveIn hIn) fun hd => by
      have := hTopI (hdS hd).1; have := hTopV (hdS hd).2; rw [hT]; omega
  have hA := hOwned.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  show wp m _ Q store3 s4 host
  simp only [wp_localGet_cons, Locals.get_values, hI4, hP4, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode hk, words_div hk hnk]
  simp only [wp_ltUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  by_cases hc : (i.denote funs env).toNat < (env.get x).size
  · -- The writes of the element's words.
    rw [ite_eq_left (by simp [hLess.mpr hc])]
    have hik : (i.denote funs env).toNat * e.width < 536870912 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hc)) hnk
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get_values, hI4]
    have hs := words_scale hk hik
    rw [UInt64.ofNat_toNat] at hs
    rw [wp_scaleCode, hs]
    have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤
        base + 2 + e.width := by
      show s4.params.length ≤ _; rw [hp4]; omega
    have hHigh5' : base + 2 + e.width < s4.half := by rw [hh4]; omega
    have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
    refine wp_localSet_local hLow5 hHigh5 ?_
    set s5 : Locals := setLocal { s4 with values := s4.values } (base + 2 + e.width)
      (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) with hs5
    have hF5 : Frame (base + 2 + e.width) s4 s5 := Frame.setValues hLow5 le_rfl hHigh5'
    have hW5 : s5.get (base + 2 + e.width) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) :=
      Locals.get_setLocal_same hLow5 hHigh5
    have hP5 : s5.get (base + 1 + e.width) = some (.i64 p) :=
      (hF5.below _ (by omega)).1.trans hP4
    have hold5 : LocalsHold s5 (base + 1) e.types
        (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
      rw [e.values_typed]
      exact (LocalsHold.frame hF5 (by rw [e.values_length, e.types_length])
        (by rw [e.types_length]; omega)).mpr hold4
    have hik64 : (UInt64.ofNat ((i.denote funs env).toNat * e.width)).toNat =
        (i.denote funs env).toNat * e.width :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    rw [← List.append_nil (storeWordsCode h (base + 1 + e.width) (base + 2 + e.width) 0 (base + 1)
      e.types)]
    refine wp_storeWordsCode 0 (base + 1) e.types (e.toWords (v.denote funs env))
      (e.words (env.get x)) store3 s5 (a4.toWords.reframe (hF5.mono (by omega)))
      (hF5.half.trans hh4) hP5 hW5 hold5 (by rw [e.toWords_length, e.types_length])
      (by rw [hik64, e.types_length, Elem.words_size]
          have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
          rw [Nat.succ_mul] at this; omega)
      fun store6 a6 => ?_
    rw [hik64] at a6
    simp only [Nat.add_zero] at a6
    rw [Elem.words_set e hc] at a6
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons, hP5]
    exact hFinish store6 s5 _ (hF5.mono (by omega)) rfl rfl a6
  · rw [ite_eq_right (by simp [hLess, hc])]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons, hP4]
    exact hFinish _ s4 (e.words (env.get x)) (Frame.refl _ _) rfl
      (by simp [Array.set!, Array.setIfInBounds, hc]) a4.toWords

/-- A request of at least 8 and at most `8 * k` bytes, within `2 ^ 32`, takes at most `8 * k`
bytes. -/
theorem allocSize_le_mul {bytes : UInt64} {k : Nat} (h8 : 8 ≤ bytes.toNat)
    (hb : bytes.toNat ≤ 4294967296) (h : bytes.toNat ≤ 8 * k) :
    (allocSize bytes).toNat ≤ 8 * k := by
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · simp only [UInt64.reduceToNat]; omega
  · rw [hRound]; omega

/-- `Var.roomCost` covers a copy at the new length. -/
theorem Var.roomCost_copy {Γ : List Ty} {e : Elem} (x : Var Γ (.array e)) (modes : List Mode)
    (live : Nat → Bool) (xs : Array e.denote) (ext : Nat) :
    allocCost ((xs.size * e.width + ext + 1) * 8) ≤ x.roomCost modes live xs ext := by
  simp only [Var.roomCost, allocCost]
  split <;> omega

/-- `Var.roomCode`: an owned array, at the address in local `b + 4`, whose first elements are
those of `x`, whose length is `x`'s length plus the word `e` in local `ext`, and whose block has
room for that length.  An owned `x` that dies is consumed; any other `x` is read.  The code traps
only when `top` cannot rise by `Var.roomCost` within the cap, and it raises `top` by at most that
cost. -/
theorem specB_room (hm : Runtime m) {Γ' : List Ty} {el : Elem} (x : Var Γ' (.array el))
    {env : Env Γ'}
    {slots : List Slot} {live : Nat → Bool} {b ext : Nat} {e : UInt64} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots (fun i => live i || i == x.index) b heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ b)
    (hRoom : b + 6 ≤ s.half) (hExt : s.get ext = some (.i64 e))
    (hExtB : ext < b) (he : e.toNat ≤ 536870912)
    (hTrap : TrapOK (!decide (heap.Within store m
      (x.roomCost (slots.map Slot.mode) live (env.get x) e.toNat))) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (q : UInt64)
      (words : Array UInt64), words.size = (el.words (env.get x)).size + e.toNat →
      (∀ j (hj : j < (el.words (env.get x)).size), words[j]! = (el.words (env.get x))[j]) →
      After env slots (fun i => live i || i == x.index) live b heap store s (.array .word) .owned
        words heap' store' s' [.i64 q] →
      s'.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) →
      s'.get (b + 4) = some (.i64 q) → s'.values = s.values →
      heap'.top.toNat ≤ heap.top.toNat + x.roomCost (slots.map Slot.mode) live (env.get x) e.toNat →
      wp m rest Q store' s' host) :
    wp m (x.roomCode slots b live ext ++ rest) Q store s host := by
  have hTot : 2 * s.half ≤ s.params.length + s.locals.length := by
    simp only [Locals.half]; omega
  obtain ⟨hBelowX, ws, hold, hRep⟩ := hVars.get x (by simp)
  obtain ⟨p, rfl, hArr⟩ := hRep
  have hB := hArr.borrow
  have hA := hB.values
  have hLenB := hA.lengthBound
  have hFitA := hA.1
  have hn : (el.words (env.get x)).size < 536870912 := by omega
  have hN : (UInt64.ofNat (el.words (env.get x)).size).toNat = (el.words (env.get x)).size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hP : s.get (slots.getD x.index default).loc = some (.i64 p) := by
    exact LocalsHold.word hold
  simp only [Var.roomCode, List.append_assoc, List.cons_append, List.nil_append]
  -- The address, in local `b`.
  simp only [wp_localGet_cons, hP]
  refine wp_localSet_local hBase (by omega) ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ b := hBase
  let s1 := setLocal { s with values := s.values } b (.i64 p)
  have hP1 : s1.get b = some (.i64 p) := Locals.get_setLocal_same hLow0 (by omega)
  have hExt1 : s1.get ext = some (.i64 e) := by
    rw [Locals.get_setLocal_ne hLow0 (by omega)]; exact hExt
  -- The length, in local `b + 1`.
  show wp m _ Q store s1 host
  simp only [wp_localGet_cons, hP1, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ b + 1 := by
    show s.params.length ≤ b + 1; omega
  have hHigh1 : b + 1 < ({ s1 with values := s.values } : Locals).params.length +
      ({ s1 with values := s.values } : Locals).locals.length := by
    show b + 1 < s.params.length + (setLocal _ _ _).locals.length; simp [setLocal]; omega
  refine wp_localSet_local hLow1 hHigh1 ?_
  let s2 := setLocal { s1 with values := s.values } (b + 1)
    (.i64 (UInt64.ofNat (el.words (env.get x)).size))
  have hN2 : s2.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) :=
    Locals.get_setLocal_same hLow1 hHigh1
  have hP2 : s2.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact hP1
  have hExt2 : s2.get ext = some (.i64 e) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact hExt1
  -- The new length, in local `b + 2`.
  show wp m _ Q store s2 host
  simp only [wp_localGet_cons, Locals.get_values, hN2, hExt2, wp_addI64_cons]
  have hLow2 : ({ s2 with values := s.values } : Locals).params.length ≤ b + 2 := by
    show s.params.length ≤ b + 2; omega
  have hHigh2 : b + 2 < ({ s2 with values := s.values } : Locals).params.length +
      ({ s2 with values := s.values } : Locals).locals.length := by
    show b + 2 < s.params.length + (setLocal _ _ _).locals.length; simp [s1, setLocal]; omega
  refine wp_localSet_local hLow2 hHigh2 ?_
  let s3 := setLocal { s2 with values := s.values } (b + 2)
    (.i64 (UInt64.ofNat (el.words (env.get x)).size + e))
  have hT3 : s3.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hN3 : s3.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hN2
  have hP3 : s3.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hP2
  have hTotal : (UInt64.ofNat (el.words (env.get x)).size + e).toNat =
      (el.words (env.get x)).size + e.toNat := by
    rw [UInt64.toNat_add, hN]; omega
  -- The trap when the new length is `2 ^ 29` or more.
  show wp m _ Q store s3 host
  simp only [wp_localGet_cons, hT3, wp_constI64_cons, wp_geUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases hBig : (536870912 : UInt64) ≤ UInt64.ofNat (el.words (env.get x)).size + e
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wp_unreachable_cons]
    have hW : ¬heap.Within store m (x.roomCost (slots.map Slot.mode) live (env.get x) e.toNat) := by
      have hc := x.roomCost_copy (slots.map Slot.mode) live (env.get x) e.toNat
      rw [UInt64.le_iff_toNat_le, hTotal, Elem.words_size] at hBig
      simp only [UInt64.reduceToNat] at hBig
      simp only [Heap.Within, allocCost] at hc ⊢
      omega
    exact (hTrap.of_imp (a := true) fun _ => by simpa using hW) _
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
  rw [wp_nil]
  dsimp only
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  have hTotalLt : (el.words (env.get x)).size + e.toNat < 536870912 := by
    have := UInt64.not_le.mp hBig
    rw [UInt64.lt_iff_toNat_lt, hTotal] at this
    exact this
  have hT3' : ({ s3 with values := s3.values } : Locals).get (b + 2) =
      some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := hT3
  have hFrame3 : ∀ j < b, s3.get j = s.get j ∧ s3.get (j + s.half) = s.get (j + s.half) :=
    fun j hj => ⟨by
      rw [Locals.get_setLocal_ne hLow2 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow0 (by omega), Locals.get_values], by
      rw [Locals.get_setLocal_ne hLow2 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values,
        Locals.get_setLocal_ne hLow0 (by omega), Locals.get_values]⟩
  have hh3 : s3.half = s.half := by simp [s3, s2, s1]
  have hp3 : s3.params = s.params := rfl
  have hl3 : s3.locals.length = s.locals.length := by simp [s3, s2, s1, setLocal]
  have hv3 : s3.values = s.values := rfl
  by_cases hMove : (slots.getD x.index default).mode = .owned ∧ live x.index = false
  swap
  · -- A copy into a block with room.
    rw [ite_eq_right hMove]
    simp only [List.cons_append, List.append_assoc, wp_localGet_cons, hT3', wp_constI64_cons,
      wp_addI64_cons, wp_mulI64_cons]
    have hBytes : ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8).toNat =
        8 * ((UInt64.ofNat (el.words (env.get x)).size + e).toNat + 1) := by
      simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat] at hTotal ⊢
      omega
    have hc : allocCost (allocSize ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8)).toNat ≤
        x.roomCost (slots.map Slot.mode) live (env.get x) e.toNat := by
      have h1 := allocSize_le_mul (k := (el.words (env.get x)).size + e.toNat + 1)
        (bytes := (UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8)
        (by rw [hBytes]; omega) (by rw [hBytes, hTotal]; omega) (by rw [hBytes, hTotal])
      have h2 := x.roomCost_copy (slots.map Slot.mode) live (env.get x) e.toNat
      rw [← Elem.words_size el (env.get x)] at h2
      simp only [allocCost] at h2 ⊢
      omega
    refine wp_allocCopy hm hAt hCap hc hTrap hB (by rw [hTotal]; exact hTotalLt)
      (by omega)
      (by rw [hBytes]) (by rw [hBytes, hTotal]; omega) hP3 hT3 hN3
      (by show s.params.length ≤ b + 4; omega) (by rw [hp3, hl3]; omega)
      (by show s.params.length ≤ b + 5; omega) (by rw [hp3, hl3]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      fun heap1 store1 s4 q words hSize hPrefix hStep hOwnedQ _ hp4 hl4 hOther4 hQ4 hv4 hTop4 => ?_
    have hF4 : Frame b s s4 := ⟨hp4.trans hp3, hl4.trans hl3, fun j hj =>
      ⟨by rw [hOther4 j (by omega) (by omega), (hFrame3 j hj).1],
        by rw [hOther4 _ (by omega) (by omega), (hFrame3 j hj).2]⟩⟩
    have hVarsL := hVars.live_mono (live' := live) fun i h => by simp [h]
    refine hNext heap1 store1 s4 q words (by rw [hSize, hTotal]) hPrefix ⟨?_, hF4, ?_,
      ⟨q, rfl, hOwnedQ⟩, ?_⟩ (by rw [hOther4 _ (by omega) (by omega)]; exact hN3) hQ4
      (by rw [hv4, hv3]) hTop4
    · exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · exact (hVarsL.step hStep fun _ _ _ _ _ _ _ _ => trivial).frame hF4 le_rfl
    · intro u y hy _ wy hwy hly c hc d hd
      have hwy' := (hVarsL.hold_agree hF4 hy hly).mp hwy
      obtain ⟨hSame, hFresh⟩ := hVarsL.regions_after hStep hy hwy' hly fun _ _ => trivial
      rw [hSame] at hd
      exact regionsDisjoint_symm (hFresh d hd c hc)
  -- An owned `x` that dies: its block, extended in place or replaced by a larger one.
  obtain ⟨hOwnedX, hDead⟩ := hMove
  rw [ite_eq_left (show (slots.getD x.index default).mode = .owned ∧ live x.index = false from
    ⟨hOwnedX, hDead⟩)]
  have hOwned : heap.Owned store p (el.words (env.get x)) := by rw [hOwnedX] at hArr; exact hArr
  have hCost : x.roomCost (slots.map Slot.mode) live (env.get x) e.toNat =
      allocCost (16 * ((env.get x).size * el.width + e.toNat + 1)) := by
    simp only [Var.roomCost, modeAt, Slot.modes_getD, hOwnedX, hDead, and_self, ↓reduceIte]
  have hBaseP := hOwned.base
  have hAddrP := hOwned.address
  have hBelowP := hOwned.below
  have hTop := hAt.top
  have hCapacityP := hOwned.capacity
  have a0 := (After.move x hVars hAt hOwnedX hDead hold rfl).reframe
    ⟨hp3, hl3, fun j hj => hFrame3 j hj⟩
  have hP3' : ({ s3 with values := s3.values } : Locals).get b = some (.i64 p) := hP3
  have hCapAddr : (p - 32).toUInt32.toNat = p.toNat - 32 :=
    headerAddress_toNat (by simp only [UInt64.reduceToNat]; omega) (by omega)
  -- The capacity, in local `b + 3`.
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, hP3', wp_constI64_cons,
    wp_subI64_cons, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by rw [hCapAddr]; omega)]
  have hLow3 : ({ s3 with values := s3.values } : Locals).params.length ≤ b + 3 := by
    show s.params.length ≤ b + 3; omega
  have hHigh3 : b + 3 < ({ s3 with values := s3.values } : Locals).params.length +
      ({ s3 with values := s3.values } : Locals).locals.length := by
    show b + 3 < s3.params.length + s3.locals.length; rw [hp3, hl3]; omega
  refine wp_localSet_local hLow3 hHigh3 ?_
  let s4 := setLocal { s3 with values := s3.values } (b + 3)
    (.i64 (store.mem.read64 (p - 32).toUInt32))
  have hC4 : s4.get (b + 3) = some (.i64 (store.mem.read64 (p - 32).toUInt32)) :=
    Locals.get_setLocal_same hLow3 hHigh3
  have hT4 : s4.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hT3
  have hN4 : s4.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hN3
  have hP4 : s4.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hP3
  have hp4 : s4.params = s.params := rfl
  have hl4 : s4.locals.length = s.locals.length := by simp [s4, setLocal, hl3]
  have hF4 : Frame b s3 s4 := ⟨rfl, by simp [s4, setLocal], fun j hj =>
    ⟨by rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values],
      by rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]⟩⟩
  have hh4 : s4.half = s.half := by simp [s4, hh3]
  have hcN : (store.mem.read64 (p - 32).toUInt32).toNat = capacityAt store p := rfl
  -- The room test.
  show wp m _ Q store s4 host
  simp only [wp_localGet_cons, Locals.get_values, hT4, hC4, wp_constI64_cons, wp_addI64_cons,
    wp_mulI64_cons, wp_leUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hNeed : ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8).toNat =
      8 * ((el.words (env.get x)).size + e.toNat + 1) := by
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat] at hTotal ⊢
    omega
  by_cases hFits : (UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8 ≤
    store.mem.read64 (p - 32).toUInt32
  · -- Room in the block: the new length, in place.
    simp (config := { decide := true }) only [hFits, ↓reduceIte]
    rw [UInt64.le_iff_toNat_le, hNeed, hcN] at hFits
    have hP4' : ({ s4 with values := s4.values } : Locals).get b = some (.i64 p) := hP4
    simp only [wp_localGet_cons, hP4']
    have hLow4 : ({ s4 with values := s4.values } : Locals).params.length ≤ b + 4 := by
      show s.params.length ≤ b + 4; omega
    have hHigh4 : b + 4 < ({ s4 with values := s4.values } : Locals).params.length +
        ({ s4 with values := s4.values } : Locals).locals.length := by
      show b + 4 < s4.params.length + s4.locals.length; rw [hp4, hl4]; omega
    refine wp_localSet_local hLow4 hHigh4 ?_
    let s5 := setLocal { s4 with values := s4.values } (b + 4) (.i64 p)
    have hQ5 : s5.get (b + 4) = some (.i64 p) := Locals.get_setLocal_same hLow4 hHigh4
    have hT5 : s5.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hT4
    have hN5 : s5.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hN4
    have hF5 : Frame b s4 s5 := ⟨rfl, by simp [s5, setLocal], fun j hj =>
      ⟨by rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values],
        by rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]⟩⟩
    show wp m _ _ store s5 host
    have hP32 : p.toUInt32.toNat = p.toNat := by rw [Memory.toUInt32_toNat]; omega
    simp only [wp_localGet_cons, Locals.get_values, hQ5, hT5, wp_wrapI64_cons, wrap_toUInt32,
      wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hP32]; omega), wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    -- The block holds the new length, the elements of `x`, and what memory held after them.
    let store' : Store Unit :=
      { store with
        mem := store.mem.write64 p.toUInt32 (UInt64.ofNat (el.words (env.get x)).size + e) }
    let words : Array UInt64 :=
      Array.ofFn (n := (UInt64.ofNat (el.words (env.get x)).size + e).toNat) fun j =>
        if j.val < (el.words (env.get x)).size then (el.words (env.get x))[j.val]!
        else store'.mem.read64 (UInt64Array.wordAddress p (j.val + 1))
    have hSize : words.size = (UInt64.ofNat (el.words (env.get x)).size + e).toNat :=
      Array.size_ofFn
    have hValues : UInt64Array.At store' p words := by
      refine ⟨by rw [hSize, hTotal]; omega, ?_, ?_, fun j hj => ?_⟩
      · rw [hSize, hTotal]; simp only [store', Wasm.Mem.write64_pages]; omega
      · rw [hSize, UInt64.ofNat_toNat]; exact Memory.read64_write64 ..
      · simp only [words, Array.getElem_ofFn]
        rw [hSize, hTotal] at hj
        split
        · next hjn =>
          rw [getElem!_pos _ j hjn, ← hA.elementRead j hjn]
          refine Memory.read64_write64_disjoint _ _ _ _ (Or.inr ?_)
          rw [hP32, ← UInt64Array.wordAddress, UInt64Array.wordAddress_toNat hFitA (by omega)]
          omega
        · rfl
    have hWrites : Memory.WritesRange store store' p.toNat (p.toNat + 8) :=
      Memory.WritesRange.write64 _ p.toUInt32 _ _ _ (by omega) (by omega)
    have hWithin : WritesWithin store store' p.toNat (capacityAt store p) :=
      ⟨by rw [hWrites.1], hWrites.2.1, fun a ha => hWrites.2.2 a (by omega)⟩
    have aW := ((a0.toWords.reframe hF4).reframe hF5).rewrite hWithin (by rw [hWrites.1]) hValues
      (by rw [hSize, hTotal]; omega)
    refine hNext heap store' _ p words (by rw [hSize, hTotal]) (fun j hj => ?_) aW hN5 hQ5 rfl
      (Nat.le_add_right _ _)
    rw [getElem!_pos words j (by rw [hSize, hTotal]; omega)]
    simp only [words, Array.getElem_ofFn]
    rw [ite_eq_left hj, getElem!_pos _ j hj]
  · -- No room: a block of at least twice the capacity, then the release of the old one.
    simp (config := { decide := true }) only [hFits, ↓reduceIte]
    have hT4' : ({ s4 with values := s4.values } : Locals).get (b + 2) =
        some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := hT4
    have hC4' : ({ s4 with values := s4.values } : Locals).get (b + 3) =
        some (.i64 (store.mem.read64 (p - 32).toUInt32)) := hC4
    refine wp_requestCode hT4' hC4' (by rw [hTotal]; exact hTotalLt) (by rw [hcN]; omega)
      fun r hr1 hr2 hr3 => ?_
    have hc : allocCost (allocSize r).toNat ≤
        x.roomCost (slots.map Slot.mode) live (env.get x) e.toNat := by
      rw [UInt64.le_iff_toNat_le, hNeed, hcN] at hFits
      rw [hTotal, hcN] at hr3
      have hr : r.toNat ≤ 8 * (2 * ((el.words (env.get x)).size + e.toNat + 1)) :=
        hr3.trans (max_le (by omega) (by omega))
      have h1 := allocSize_le_mul (by rw [hTotal] at hr1; omega) hr2 hr
      rw [hCost]
      rw [Elem.words_size] at h1
      simp only [allocCost]
      omega
    refine wp_allocCopy hm hAt hCap hc (hTrap.imp fun _ h => h) hOwned.borrowed
      (by rw [hTotal]; exact hTotalLt) (by rw [hTotal]; omega) hr1 hr2 hP4 hT4 hN4
      (by show s.params.length ≤ b + 4; omega) (by rw [hp4, hl4]; omega)
      (by show s.params.length ≤ b + 5; omega) (by rw [hp4, hl4]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      fun heap1 store1 s5 q words hSize hPrefix hStep1 hOwnedQ _ hp5 hl5 hOther5 hQ5 hv5 hTop5 => ?_
    have hP5 : s5.get b = some (.i64 p) := by rw [hOther5 b (by omega) (by omega)]; exact hP4
    simp only [wp_localGet_cons, hP5]
    obtain ⟨⟨hOwnedP1, hCapP1⟩, hApartPQ⟩ := hStep1.owned hOwned trivial
    refine wp_release hm hStep1.at_ hOwnedP1 ?_
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    have hRel := releaseStep hStep1.at_ hOwnedP1
    have hPQ : regionsDisjoint (block store1 q) (block store1 p) := by
      rw [block_eq hCapP1]
      exact regionsDisjoint_symm (hApartPQ _ (List.mem_singleton_self _))
    obtain ⟨⟨hOwnedQ2, hCapQ2⟩, -⟩ := hRel.owned hOwnedQ hPQ
    have hStepG := hStep1.transBoth hRel (keep := fun r => regionsDisjoint r (block store p))
      fun _ hr => ⟨trivial, fun _ => by rw [block_eq hCapP1]; exact hr⟩
    have aG := (a0.toWords.reframe hF4).replace (hStepG.mono (fun _ h => h) fun c hc => by
      rw [List.mem_singleton.mp hc, block_eq hCapQ2]
      exact List.mem_append_left _ (List.mem_singleton_self _)) hOwnedQ2
    have hF5 : Frame b s4 { s5 with values := s4.values } := ⟨hp5, hl5, fun j hj =>
      ⟨by show s5.get j = s4.get j; exact hOther5 j (by omega) (by omega),
        by show s5.get _ = s4.get _; exact hOther5 _ (by omega) (by omega)⟩⟩
    exact hNext _ _ _ q words (by rw [hSize, hTotal]) hPrefix (aG.reframe hF5)
      (by show s5.get (b + 1) = _; rw [hOther5 _ (by omega) (by omega)]; exact hN4) hQ5 rfl hTop5

/-- `x.push v`: the value's words from local `base` on, the array taken with room for one more
element by `Var.roomCode` from local `base + k + 1` on, and the writes of the element's words
after the array's words. -/
theorem specB_push (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {v : Expr S Γ' (.elem e)}
    (vSpec : ∀ env slots live, CodeSpecB m funs bounds host pv v env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.push x v) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hv := Nat.le_max_left v.width (e.width + 7)
  have h8 := Nat.le_max_right v.width (e.width + 7)
  have hk := e.width_pos
  simp only [Expr.placeArgs] at hPlace
  have hT : (Expr.push x v).allocs funs bounds (slots.map Slot.mode) live env =
      v.allocs funs bounds (slots.map Slot.mode) (fun j => live j || j == x.index) env +
        x.roomCost (slots.map Slot.mode) live (env.get x) (wordCount e.width).toNat := rfl
  have hdS : (Expr.push x v).depthCalls = false → v.depthCalls = false :=
    fun hd => by simpa [Expr.depthCalls] using hd
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The value's words, from local `base` on.
  have hIn : ∀ k, ((live k || k == x.index) || v.uses k) = true →
      (live k || (Expr.push x v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine vSpec env slots (fun k => live k || k == x.index) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopV => ?_
  have hR1 := Ty.rep_elem.mp a1.rep
  subst hR1
  have e1a := a1.toEvolves rfl
  have hp1a : s1.params = s.params := e1a.frame.params
  have hh1a : s1.half = h := e1a.frame.half.trans hh
  refine wp_storeCode (e.values (v.denote funs env)) h base e.types s1 s.values
    (by rw [e.values_length, e.types_length]) hh1a (by rw [hp1a]; omega)
    (by rw [e.types_length, hh1a]; omega) fun s1' f1 hold1 _ => ?_
  have f1' : Frame base s1 { s1' with values := s.values } := f1.trans Frame.ofValues
  have e1 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) base heap store s heap1 store1
      { s1' with values := s.values } :=
    ⟨e1a.step, e1a.frame.trans f1', e1a.holds.agree f1'⟩
  have hp1 : s1'.params = s.params := f1.params.trans hp1a
  have hh1 : s1'.half = h := f1.half.trans hh1a
  -- The count of new words, in local `base + k`.
  simp only [wp_constI64_cons]
  have hLowK : ({ s1' with values := s.values } : Locals).params.length ≤ base + e.width := by
    show s1'.params.length ≤ _; rw [hp1]; omega
  have hHighK' : base + e.width < ({ s1' with values := s.values } : Locals).half := by
    simp only [Locals.half_values, hh1]; omega
  have hHighK := Locals.lt_total hHighK'
  refine wp_localSet_local hLowK hHighK ?_
  set s2 := setLocal { s1' with values := s.values } (base + e.width) (.i64 (wordCount e.width))
    with hs2
  have hK2 : s2.get (base + e.width) = some (.i64 (wordCount e.width)) :=
    Locals.get_setLocal_same hLowK hHighK
  have hF2 : Frame (base + e.width) { s1' with values := s.values } s2 :=
    Frame.setValues (s := { s1' with values := s.values }) (vs := s.values) hLowK le_rfl hHighK'
  have hold2 : LocalsHold s2 base e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans hF2) (by rw [e.values_length, e.types_length])
      (by rw [e.types_length])).mpr hold1
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) base heap store s heap1 store1 s2 :=
    ⟨e1.step, e1.frame.trans (hF2.mono (by omega)), e1.holds.agree (hF2.mono (by omega))⟩
  have hp2 : s2.params = s.params := e2.frame.params
  have hh2 : s2.half = h := e2.frame.half.trans hh
  -- The array, with room for one more element, from local `base + k + 1` on.
  refine specB_room hm x (b := base + e.width + 1) (ext := base + e.width) (e := wordCount e.width)
    (s := s2) (e2.holds.mono (by omega))
    e2.step.at_ (by rw [e2.step.cap m]; exact hCap) (by rw [hp2]; omega)
    (by rw [hh2]; omega) hK2 (by omega) (by rw [wordCount_toNat]; omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le
      (by have := hTopV (hdS hd); rw [hT]; omega) (e2.step.cap m))
    fun heap2 store2 s3 q words hSize hPrefix aR hN3 hQ3 hv3 hTopR => ?_
  obtain ⟨p, hp, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap2.Owned store2 p words := hOwnedQ
  obtain rfl : p = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hFitQ := hOwnedQ.values.1
  have hkw : (wordCount e.width).toNat = e.width := by
    rw [wordCount_toNat] at hSize ⊢; omega
  rw [hkw, Elem.words_size] at hSize
  have hL64 : (UInt64.ofNat (e.words (env.get x)).size).toNat = (env.get x).size * e.width := by
    rw [Elem.words_size]
    exact UInt64.toNat_ofNat_of_lt'
      (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hold3 : LocalsHold s3 base e.types
      (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
    rw [e.values_typed]
    exact (LocalsHold.frame (aR.frame.mono (base := base + e.width) (by omega))
      (by rw [e.values_length, e.types_length]) (by rw [e.types_length])).mpr hold2
  -- The writes of the element's words after the array's words.
  refine wp_storeWordsCode 0 base e.types (e.toWords (v.denote funs env)) words store2 s3 aR
    (aR.frame.half.trans hh2) hQ3 hN3 hold3 (by rw [e.toWords_length, e.types_length])
    (by rw [hL64, e.types_length, hSize]; omega) fun store4 a4 => ?_
  rw [hL64] at a4
  simp only [Nat.add_zero] at a4
  rw [Elem.words_push_into e (v.denote funs env) hSize (fun w hw => by
    rw [getElem!_pos (e.words (env.get x)) w (by rw [Elem.words_size]; exact hw)]
    exact hPrefix w (by rw [Elem.words_size]; exact hw))] at a4
  have aFin := After.prepend (hVars.live_mono hIn) e2 ((After.ofWords a4).lower e2.holds (by omega)
    fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
  simp only [wp_localGet_cons, hQ3]
  simpa [hv3, hs2, setLocal] using hNext heap2 store4 s3 [.i64 p] (aFin.liveIn hIn) fun hd => by
    have := hTopV (hdS hd); rw [hT]; omega

/-- `x ++ y`: the length of `y` in local `base`, the array `x` taken with room for `y`'s elements
by `Var.roomCode` from local `base + 1` on, with `y` live, the copy of `y`'s elements after `x`'s,
and the release of `y` when it is owned and dies there. -/
theorem specB_append (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x y : Var Γ' (.array e)) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.append (S := S) x y) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom _ rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hT : (Expr.append (S := S) x y).allocs funs bounds (slots.map Slot.mode) live env =
      x.roomCost (slots.map Slot.mode) (fun k => live k || k == y.index) (env.get x)
        ((env.get y).size * e.width) := rfl
  have hTot : 2 * s.half ≤ s.params.length + s.locals.length := by
    simp only [Locals.half]; omega
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The length of `y`, in local `base`.
  obtain ⟨hBelowY, wy, holdy, hRepY⟩ := hVars.get y (by simp [Expr.uses])
  obtain ⟨py, rfl, hArrY⟩ := hRepY
  have hYB : (slots.getD y.index default).loc < base := by
    have := hBelowY; simp only [Ty.width] at this; omega
  have hBY := hArrY.borrow
  have hAY := hBY.values
  have hLenY := hAY.lengthBound
  have hFitY := hAY.1
  have hmY : (e.words (env.get y)).size < 536870912 := by omega
  have hMY : (UInt64.ofNat (e.words (env.get y)).size).toNat = (e.words (env.get y)).size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hExt : (UInt64.ofNat (e.words (env.get y)).size).toNat = (env.get y).size * e.width := by
    rw [hMY, Elem.words_size]
  have hPY : s.get (slots.getD y.index default).loc = some (.i64 py) := by
    exact LocalsHold.word holdy
  simp only [wp_localGet_cons, hPY, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hAY.lengthRead]
  refine wp_localSet_local hBase (by omega) ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ base := hBase
  set s1 := setLocal { s with values := s.values } base
    (.i64 (UInt64.ofNat (e.words (env.get y)).size))
    with hs1
  have hM1 : s1.get base = some (.i64 (UInt64.ofNat (e.words (env.get y)).size)) :=
    Locals.get_setLocal_same hLow0 (by omega)
  have hF1 : Frame base s s1 := by
    rw [hs1]; exact Frame.setValues hLow0 le_rfl (by rw [hh]; omega)
  have hh1' : s1.half = s.half := hF1.half
  -- The array `x` with room, from local `base + 1` on, with `y` live.
  have hIn : ∀ k, ((live k || k == y.index) || k == x.index) = true →
      (live k || (Expr.append (S := S) x y).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact append_live _ _ _ h
  have hVars1 : Holds env slots (fun k => (live k || k == y.index) || k == x.index) (base + 1)
      heap store s1 :=
    ((hVars.live_mono hIn).agree hF1).mono (by omega)
  refine specB_room hm x (b := base + 1) (ext := base) (e := UInt64.ofNat (e.words (env.get y)).size)
    (s := s1) hVars1 hAt hCap (by show s.params.length ≤ base + 1; omega)
    (by rw [hh1', hh]; omega)
    hM1 (by omega) (by rw [hMY]; exact Nat.le_of_lt hmY)
    (hTrap.alloc (by simp [Expr.aborts]) fun _ hw => hw.mono (by rw [hT, hExt]))
    fun heap1 store1 s2 q words hSize hPrefix aR hN2 hQ2 hv2 hTopR => ?_
  rw [hMY] at hSize
  have hp2 : s2.params = s.params := aR.frame.params
  have hl2 : s2.locals.length = s.locals.length := by rw [aR.frame.length]; simp [s1, setLocal]
  have hM2 : s2.get base = some (.i64 (UInt64.ofNat (e.words (env.get y)).size)) :=
    (aR.frame.below base (by omega)).1.trans hM1
  have hh2' : s2.half = s.half := aR.frame.half.trans hh1'
  -- `y` stays readable, apart from the new array.
  obtain ⟨-, wy', holdy', hRepY'⟩ := aR.holds.get y (by simp)
  have hAgree2 : ∀ j < base, s2.get j = s.get j := fun j hj =>
    (aR.frame.below j (by omega)).1.trans (hF1.below j hj).1
  have holdy2 : LocalsHold s2 (slots.getD y.index default).loc (Ty.array e).types [.i64 py] :=
    (LocalsHold.frame (hF1.trans (aR.frame.mono (base := base) (by omega))) rfl
      (by simp only [Ty.types, List.length_singleton]; omega)).mpr holdy
  obtain rfl := LocalsHold.unique holdy' holdy2 (by rw [hRepY'.length]; rfl)
  obtain ⟨py', hpy, hArrY1⟩ := hRepY'
  obtain rfl : py = py' := by simp only [List.cons.injEq, Value.i64.injEq] at hpy; exact hpy.1
  have hBY1 := hArrY1.borrow
  obtain ⟨p, hp, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap1.Owned store1 p words := hOwnedQ
  obtain rfl : p = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hCapQ := hOwnedQ.capacity
  have hBaseQ := hOwnedQ.base
  have hApartQY : py.toNat + 8 * ((e.words (env.get y)).size + 1) ≤ p.toNat ∨
      p.toNat + 8 * (words.size + 1) ≤ py.toNat := by
    have hD := aR.apart _ y (by simp) (Or.inl rfl) [.i64 py] holdy2 rfl (block store1 p)
      (List.mem_singleton_self _)
    cases hmy : (slots.getD y.index default).mode
    · rw [hmy] at hD
      have := hD _ (List.mem_singleton_self _)
      simp only [block, regionsDisjoint] at this
      omega
    · rw [hmy] at hD hArrY1
      have hOwnedY : heap1.Owned store1 py (e.words (env.get y)) := hArrY1
      have := hD (block store1 py) (List.mem_singleton_self _)
      have := hOwnedY.capacity
      have := hOwnedY.base
      simp only [block, regionsDisjoint] at *
      omega
  -- The address of element `n` of the new array, in local `base + 4`.
  have h8n : UInt64.ofNat (e.words (env.get x)).size * 8 =
      UInt64.ofNat (8 * (e.words (env.get x)).size) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  simp only [wp_localGet_cons, Locals.get_values, hQ2, hN2, wp_constI64_cons, wp_mulI64_cons,
    wp_addI64_cons, h8n]
  have hLow2 : ({ s2 with values := s2.values } : Locals).params.length ≤ base + 4 := by
    show s2.params.length ≤ base + 4; rw [hp2]; omega
  have hHigh2 : base + 4 < ({ s2 with values := s2.values } : Locals).params.length +
      ({ s2 with values := s2.values } : Locals).locals.length := by
    show base + 4 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega
  refine wp_localSet_local hLow2 hHigh2 ?_
  set s3 := setLocal { s2 with values := s2.values } (base + 4)
    (.i64 (p + UInt64.ofNat (8 * (e.words (env.get x)).size))) with hs3
  have hD3 : s3.get (base + 4) = some (.i64 (p + UInt64.ofNat (8 * (e.words (env.get x)).size))) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hGet3 : ∀ j, j ≠ base + 4 → s3.get j = s2.get j := fun j hj => by
    rw [hs3, Locals.get_setLocal_ne hLow2 hj, Locals.get_values]
  have hp3 : s3.params = s.params := hp2
  have hl3 : s3.locals.length = s.locals.length := by simp [s3, setLocal, hl2]
  -- The copy of `y`'s elements after `x`'s.
  refine wp_copyInto (k := (e.words (env.get x)).size) hBY1.values hOwnedQ.values (by omega)
    hApartQY
    (by rw [hGet3 _ (by omega), hAgree2 _ hYB]; exact hPY) hD3
    (by rw [hGet3 _ (by omega)]; exact hM2) (by omega) (by omega)
    (by omega) (by rw [hp3]; omega) (by rw [hp3, hl3]; omega)
    fun store2 s4 hW hA2 hp4 hl4 hOther4 hv4 => ?_
  have hWords : overlay words (e.words (env.get y)) (e.words (env.get x)).size
      (e.words (env.get y)).size = e.words (env.get x ++ env.get y) := by
    rw [Elem.words_append]
    apply Array.ext (by simp [overlay_size, hSize]) fun j h1 h2 => ?_
    simp only [overlay, Array.getElem_ofFn]
    rw [overlay_size] at h1
    by_cases hj : j < (e.words (env.get x)).size
    · rw [ite_eq_right (by omega), Array.getElem_append_left hj, ← hPrefix j hj,
        getElem!_pos words j h1]
    · rw [ite_eq_left (by omega), Array.getElem_append_right (by omega),
        getElem!_pos _ _ (by omega)]
  rw [hWords] at hA2
  have hWithin : WritesWithin store1 store2 p.toNat (capacityAt store1 p) :=
    ⟨by rw [hW.1], hW.2.1, fun a ha => hW.2.2 a (by omega)⟩
  have aW := aR.rewrite hWithin (by rw [hW.1]) hA2
    (by rw [Elem.words_append, Array.size_append]; omega)
  have hF4 : Frame (base + 1) s2 s4 := ⟨hp4.trans rfl, by rw [hl4]; simp [s3, setLocal],
    fun j hj => ⟨by rw [hOther4 j (by omega), hGet3 j (by omega)],
      by rw [hOther4 _ (by omega), hGet3 _ (by omega)]⟩⟩
  -- The release of `y` when it is owned and dies here.
  refine After.releaseT hm (s1 := s4) (live := live)
    (sel := fun k => k == y.index && !live k) hVars1 (After.ofWords (aW.reframe hF4))
    (fun k h => by simp [h]) (fun k h => by
      simp only [Bool.and_eq_true, beq_iff_eq] at h; simp [h.1])
    (fun k h => by simp [h]) fun heap2 store3 a' hTop2 => ?_
  have hQ4 : s4.get (base + 5) = some (.i64 p) := by
    rw [hOther4 _ (by omega), hGet3 _ (by omega)]; exact hQ2
  simp only [wp_localGet_cons, hQ4]
  have e0 : Evolves env slots (fun i => live i || (Expr.append (S := S) x y).uses i)
      (fun k => (live k || k == y.index) || k == x.index) base heap store s heap store s1 :=
    ⟨Step.refl hAt _, hF1, (hVars.live_mono hIn).agree hF1⟩
  have aFin := After.prepend hVars e0 (a'.lower ((hVars.live_mono hIn).agree
    hF1) (by omega) fun k h => by simp [h]) hIn fun k h => by simp [h]
  have hv3 : s3.values = s.values := by rw [hs3]; exact hv2
  simpa [hv4, hv3] using hNext heap2 store3 s4 [.i64 p] aFin fun _ => by
    rw [hTop2, hT, ← hExt]; exact hTopR

/-- `LeanExe.eraseAt x i`: the position in local `base`, the array as owned in local `base + 1`,
its length in local `base + 2`, and, when the position is below the size, the element's first
word in local `base + 3`, the move of the words after the element down by its word count, and the
write of the shorter length. -/
theorem specB_eraseAt (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots live, CodeSpecB m funs bounds host pv i env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.eraseAt x i) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width 8
  have hx := Nat.le_max_right i.width 8
  have hk := e.width_pos
  have hcw : copyWidth (Ty.array e) = 4 := rfl
  simp only [Expr.placeArgs] at hPlace
  have hT : (Expr.eraseAt x i).allocs funs bounds (slots.map Slot.mode) live env =
      i.allocs funs bounds (slots.map Slot.mode) (fun j => live j || j == x.index) env +
        x.ownedCost (slots.map Slot.mode) live (env.get x) := rfl
  have hdS : (Expr.eraseAt x i).depthCalls = false → i.depthCalls = false :=
    fun hd => by simpa [Expr.depthCalls] using hd
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.eraseAt x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopI => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWord a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hh1 := e1.frame.half.trans hh
  -- The array as owned, in local `base + 1`.
  refine specB_ownedVar hm x hh1 (hp1.trans hpv) (e1.holds.mono (Nat.le_succ base)) e1.step.at_
    (by rw [e1.step.cap m]; exact hCap) (by rw [hp1]; omega) (by omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le
      (by have := hTopI (hdS hd); rw [hT]; omega) (e1.step.cap m))
    fun heap3 store3 s3 ws3 a3 hTopO => ?_
  obtain ⟨p, hws, hOwned⟩ := a3.rep
  subst hws
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hh3 : s3.half = h := a3.frame.half.trans hh1
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow3 : ({ s3 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s3.params.length ≤ _; rw [hp3]; omega
  have hHigh3' : base + 1 < s3.half := by rw [hh3]; omega
  have hHigh3 := Locals.lt_total (s := { s3 with values := s.values }) hHigh3'
  refine wp_localSet_local hLow3 hHigh3 ?_
  set s4 : Locals := setLocal { s3 with values := s.values } (base + 1) (.i64 p) with hs4
  have hP4 : s4.get (base + 1) = some (.i64 p) := Locals.get_setLocal_same hLow3 hHigh3
  have hF4 : Frame (base + 1) s3 s4 := Frame.setValues hLow3 le_rfl hHigh3'
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (hF4.below base (by omega)).1.trans ((a3.frame.below base (by omega)).1.trans hI1)
  have hh4 : s4.half = h := hF4.half.trans hh3
  have hp4 : s4.params = s.params := hF4.params.trans hp3
  have a4 := a3.toWords.reframe hF4
  -- The rest of the code, from the array after the move or without it.
  have hFinish : ∀ (store4 : Store Unit) (s' : Locals) (ws : Array UInt64),
      Frame (base + 1) s4 s' → s'.values = s.values →
      ws = e.words (LeanExe.eraseAt (env.get x) (i.denote funs env)) →
      After env slots (fun k => live k || k == x.index) live (base + 1) heap1 store1
        (setLocal { s1 with values := s.values } base (.i64 (i.denote funs env)))
        (.array .word) .owned ws heap3 store4 s' [.i64 p] →
      wp m rest Q store4 { s' with values := .i64 p :: s'.values } host := by
    rintro store4 s' ws _ hv' rfl aX
    have aX1 := (After.ofWords aX).lower e1.holds (Nat.le_succ base) fun k h => by simp [h]
    have aX2 := After.prepend (hVars.live_mono hIn) e1 aX1 (fun k h => by simp [h])
      fun k h => by simp [h]
    simpa [hv'] using hNext heap3 store4 _ [.i64 p] (aX2.liveIn hIn) fun hd => by
      have := hTopI (hdS hd); rw [hT]; omega
  have hA := hOwned.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  -- The length, in local `base + 2`.
  show wp m _ Q store3 s4 host
  simp only [wp_localGet_cons, hP4, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size]
  have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤ base + 2 := by
    show s4.params.length ≤ _; rw [hp4]; omega
  have hHigh5' : base + 2 < s4.half := by rw [hh4]; omega
  have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
  refine wp_localSet_local hLow5 hHigh5 ?_
  set L := (env.get x).size * e.width with hLdef
  set s5 : Locals := setLocal { s4 with values := s4.values } (base + 2) (.i64 (UInt64.ofNat L))
    with hs5
  have hF5 : Frame (base + 2) s4 s5 := Frame.setValues hLow5 le_rfl hHigh5'
  have hL5 : s5.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
    Locals.get_setLocal_same hLow5 hHigh5
  have hI5 : s5.get base = some (.i64 (i.denote funs env)) :=
    (hF5.below base (by omega)).1.trans hI4
  have hP5 : s5.get (base + 1) = some (.i64 p) := (hF5.below _ (by omega)).1.trans hP4
  have hh5 : s5.half = h := hF5.half.trans hh4
  have hp5 : s5.params = s.params := hF5.params.trans hp4
  -- The test of the position.
  simp only [wp_localGet_cons, Locals.get_values, hI5, hL5]
  rw [wp_divCode hk, words_div hk hnk]
  simp only [wp_ltUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  by_cases hc : (i.denote funs env).toNat < (env.get x).size
  · rw [ite_eq_left (by simp [hLess.mpr hc])]
    set I := (i.denote funs env).toNat with hIdef
    set W := I * e.width with hWdef
    have hk29 : e.width < 536870912 := by
      have := Nat.le_mul_of_pos_left e.width (show 0 < (env.get x).size by omega); omega
    have hIk : W + e.width ≤ L := by
      have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
      rw [Nat.succ_mul] at this; omega
    have hwc := wordCount_eq hk29
    -- The element's first word, in local `base + 3`.
    simp only [wp_localGet_cons, Locals.get_values, hI5]
    have hs := words_scale hk (show I * e.width < 536870912 by omega)
    rw [UInt64.ofNat_toNat] at hs
    rw [wp_scaleCode, hs]
    have hLow6 : ({ s5 with values := s5.values } : Locals).params.length ≤ base + 3 := by
      show s5.params.length ≤ _; rw [hp5]; omega
    have hHigh6' : base + 3 < s5.half := by rw [hh5]; omega
    have hHigh6 := Locals.lt_total (s := { s5 with values := s5.values }) hHigh6'
    refine wp_localSet_local hLow6 hHigh6 ?_
    set s6 : Locals := setLocal { s5 with values := s5.values } (base + 3) (.i64 (UInt64.ofNat W))
      with hs6
    have hF6 : Frame (base + 3) s5 s6 := Frame.setValues hLow6 le_rfl hHigh6'
    have hW6 : s6.get (base + 3) = some (.i64 (UInt64.ofNat W)) :=
      Locals.get_setLocal_same hLow6 hHigh6
    have hL6 : s6.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF6.below _ (by omega)).1.trans hL5
    have hP6 : s6.get (base + 1) = some (.i64 p) := (hF6.below _ (by omega)).1.trans hP5
    have hh6 : s6.half = h := hF6.half.trans hh5
    have hp6 : s6.params = s.params := hF6.params.trans hp5
    -- The count of words to move, in local `base + 4`.
    simp only [wp_localGet_cons, Locals.get_values, hL6, hW6, wp_subI64_cons, wp_constI64_cons]
    have hCount : UInt64.ofNat L - UInt64.ofNat W - wordCount e.width =
        UInt64.ofNat (L - W - e.width) := by
      rw [hwc]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_sub, UInt64.toNat_ofNat']
      omega
    rw [hCount]
    have hLow7 : ({ s6 with values := s6.values } : Locals).params.length ≤ base + 4 := by
      show s6.params.length ≤ _; rw [hp6]; omega
    have hHigh7' : base + 4 < s6.half := by rw [hh6]; omega
    have hHigh7 := Locals.lt_total (s := { s6 with values := s6.values }) hHigh7'
    refine wp_localSet_local hLow7 hHigh7 ?_
    set s7 : Locals := setLocal { s6 with values := s6.values } (base + 4)
      (.i64 (UInt64.ofNat (L - W - e.width))) with hs7
    have hF7 : Frame (base + 4) s6 s7 := Frame.setValues hLow7 le_rfl hHigh7'
    have hN7 : s7.get (base + 4) = some (.i64 (UInt64.ofNat (L - W - e.width))) :=
      Locals.get_setLocal_same hLow7 hHigh7
    have hW7 : s7.get (base + 3) = some (.i64 (UInt64.ofNat W)) :=
      (hF7.below _ (by omega)).1.trans hW6
    have hL7 : s7.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF7.below _ (by omega)).1.trans hL6
    have hP7 : s7.get (base + 1) = some (.i64 p) := (hF7.below _ (by omega)).1.trans hP6
    have hh7 : s7.half = h := hF7.half.trans hh6
    have hp7 : s7.params = s.params := hF7.params.trans hp6
    -- The source address, in local `base + 5`.
    simp only [wp_localGet_cons, Locals.get_values, hP7, hW7, wp_constI64_cons, wp_addI64_cons,
      wp_mulI64_cons]
    have hSrc : p + (UInt64.ofNat W + wordCount e.width) * 8 =
        p + UInt64.ofNat (8 * (W + e.width)) := by
      rw [hwc]; congr 1
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    rw [hSrc]
    have hLow8 : ({ s7 with values := s7.values } : Locals).params.length ≤ base + 5 := by
      show s7.params.length ≤ _; rw [hp7]; omega
    have hHigh8' : base + 5 < s7.half := by rw [hh7]; omega
    have hHigh8 := Locals.lt_total (s := { s7 with values := s7.values }) hHigh8'
    refine wp_localSet_local hLow8 hHigh8 ?_
    set s8 : Locals := setLocal { s7 with values := s7.values } (base + 5)
      (.i64 (p + UInt64.ofNat (8 * (W + e.width)))) with hs8
    have hF8 : Frame (base + 5) s7 s8 := Frame.setValues hLow8 le_rfl hHigh8'
    have hS8 : s8.get (base + 5) = some (.i64 (p + UInt64.ofNat (8 * (W + e.width)))) :=
      Locals.get_setLocal_same hLow8 hHigh8
    have hN8 : s8.get (base + 4) = some (.i64 (UInt64.ofNat (L - W - e.width))) :=
      (hF8.below _ (by omega)).1.trans hN7
    have hW8 : s8.get (base + 3) = some (.i64 (UInt64.ofNat W)) :=
      (hF8.below _ (by omega)).1.trans hW7
    have hL8 : s8.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF8.below _ (by omega)).1.trans hL7
    have hP8 : s8.get (base + 1) = some (.i64 p) := (hF8.below _ (by omega)).1.trans hP7
    have hh8 : s8.half = h := hF8.half.trans hh7
    have hp8 : s8.params = s.params := hF8.params.trans hp7
    -- The destination address, in local `base + 6`.
    simp only [wp_localGet_cons, Locals.get_values, hP8, hW8, wp_constI64_cons, wp_addI64_cons,
      wp_mulI64_cons]
    have hDst : p + UInt64.ofNat W * 8 = p + UInt64.ofNat (8 * W) := by
      congr 1
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    rw [hDst]
    have hLow9 : ({ s8 with values := s8.values } : Locals).params.length ≤ base + 6 := by
      show s8.params.length ≤ _; rw [hp8]; omega
    have hHigh9' : base + 6 < s8.half := by rw [hh8]; omega
    have hHigh9 := Locals.lt_total (s := { s8 with values := s8.values }) hHigh9'
    refine wp_localSet_local hLow9 hHigh9 ?_
    set s9 : Locals := setLocal { s8 with values := s8.values } (base + 6)
      (.i64 (p + UInt64.ofNat (8 * W))) with hs9
    have hF9 : Frame (base + 6) s8 s9 := Frame.setValues hLow9 le_rfl hHigh9'
    have hD9 : s9.get (base + 6) = some (.i64 (p + UInt64.ofNat (8 * W))) :=
      Locals.get_setLocal_same hLow9 hHigh9
    have hS9 : s9.get (base + 5) = some (.i64 (p + UInt64.ofNat (8 * (W + e.width)))) :=
      (hF9.below _ (by omega)).1.trans hS8
    have hN9 : s9.get (base + 4) = some (.i64 (UInt64.ofNat (L - W - e.width))) :=
      (hF9.below _ (by omega)).1.trans hN8
    have hL9 : s9.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF9.below _ (by omega)).1.trans hL8
    have hP9 : s9.get (base + 1) = some (.i64 p) := (hF9.below _ (by omega)).1.trans hP8
    have hh9 : s9.half = h := hF9.half.trans hh8
    have hp9 : s9.params = s.params := hF9.params.trans hp8
    -- The move of the words after the element.
    have hWs : (e.words (env.get x)).size = L := Elem.words_size e _
    refine wp_copyDown (l := W) (n := L - W - e.width) (k := e.width) hA (by omega) hS9 hD9 hN9
      (by omega) (by omega) (by omega) (by rw [hp9]; omega)
      (Locals.lt_total (s := s9) (by rw [hh9]; omega))
      fun store10 s10 hW10 hA10 hp10 hl10 hOther10 hv10 => ?_
    have hP10 : s10.get (base + 1) = some (.i64 p) := by rw [hOther10 _ (by omega)]; exact hP9
    have hL10 : s10.get (base + 2) = some (.i64 (UInt64.ofNat L)) := by
      rw [hOther10 _ (by omega)]; exact hL9
    -- The shorter length.
    simp only [wp_localGet_cons, Locals.get_values, hP10, hL10, wp_wrapI64_cons, wrap_toUInt32,
      wp_constI64_cons, wp_subI64_cons]
    have hLen : UInt64.ofNat L - wordCount e.width = UInt64.ofNat (L - e.width) := by
      rw [hwc]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_sub, UInt64.toNat_ofNat']
      omega
    rw [hLen]
    have hFit10 := hA10.1
    have hMem10 := hA10.2.1
    have hPtr := hA10.pointerAddress_toNat
    simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hPtr]; rw [shiftDown_size] at hFit10 hMem10; omega)]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hP10]
    have hFrame : Frame (base + 1) s4 s10 :=
      (hF5.mono (by omega)).trans ((hF6.mono (by omega)).trans ((hF7.mono (by omega)).trans
        ((hF8.mono (by omega)).trans ((hF9.mono (by omega)).trans
          (Frame.ofOthers hp10 hl10 hOther10 (by omega) (by rw [hh9]; omega))))))
    have hEq : LeanExe.eraseAt (env.get x) (i.denote funs env) = (env.get x).eraseIdx I hc :=
      dite_eq_left hc
    rw [show s5.values = s10.values from hv10.symm]
    refine hFinish _ s10 _ hFrame hv10 (by rw [hEq]; exact Elem.words_eraseIdx e hc)
      ((a4.reframe hFrame).rewriteRange
        (hW10.trans (writeLength_frame store10 p (e.words (env.get x)).size (L - e.width)
          (by rw [shiftDown_size] at hFit10; exact hFit10)))
        (hA10.writeLength (by rw [shiftDown_size]; omega))
        (by simp only [Array.size_extract, shiftDown_size]; omega))
  · rw [ite_eq_right (by simp [hLess, hc])]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons, hP5]
    exact hFinish _ s5 (e.words (env.get x)) (hF5.mono (by omega)) rfl
      (by simp [LeanExe.eraseAt, Array.eraseIdxIfInBounds, hc]) (a4.reframe (hF5.mono (by omega)))

/-- `LeanExe.insertAt x i v`: the position in local `base`, the value's words from local `base + 1`
on, their count after them, the array taken with room for one more element by `Var.roomCode` from
local `base + k + 2` on, and then, when the position is at most the size, the element's first word
in local `base + k + 4`, the move of the words from there up by the element's word count, and the
writes of the value's words, or otherwise the old length written back. -/
theorem specB_insertAt (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word} {v : Expr S Γ' (.elem e)}
    (iSpec : ∀ env slots live, CodeSpecB m funs bounds host pv i env slots live)
    (vSpec : ∀ env slots live, CodeSpecB m funs bounds host pv v env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.insertAt x i v) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width (max (1 + v.width) (e.width + 8))
  have hv := (Nat.le_max_left (1 + v.width) (e.width + 8)).trans (Nat.le_max_right i.width _)
  have hx := (Nat.le_max_right (1 + v.width) (e.width + 8)).trans (Nat.le_max_right i.width _)
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hT : (Expr.insertAt x i v).allocs funs bounds (slots.map Slot.mode) live env =
      i.allocs funs bounds (slots.map Slot.mode) (fun j => live j || j == x.index || v.uses j) env +
        v.allocs funs bounds (slots.map Slot.mode) (fun j => live j || j == x.index) env +
        x.roomCost (slots.map Slot.mode) live (env.get x) (wordCount e.width).toNat := rfl
  have hdS : (Expr.insertAt x i v).depthCalls = false →
      i.depthCalls = false ∧ v.depthCalls = false :=
    fun hd => by simp only [Expr.depthCalls, Bool.or_eq_false_iff] at hd; exact hd
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index || v.uses k) || i.uses k) = true →
      (live k || (Expr.insertAt x i v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact set_live_index _ _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index || v.uses k) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopI => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWord a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hh1 := e1.frame.half.trans hh
  -- The value's words, from local `base + 1` on.
  refine vSpec env slots (fun k => live k || k == x.index) h (base + 1) heap1 store1 _ hh1
    (hp1.trans hpv) (e1.holds.mono (Nat.le_succ base)) e1.step.at_ (by rw [e1.step.cap m]; exact
        hCap)
    (by rw [hp1]; omega) (by omega) hPlace.2 _ _
    (hTrap.part (fun h => by simp [Expr.depthCalls, h]) (fun _ => by simp [Expr.aborts])
      fun hd hw => hw.shift (hTopI (hdS hd).1) (by rw [hT]; omega) (e1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTopV => ?_
  have hR2 := Ty.rep_elem.mp a2.rep
  subst hR2
  have e2a := a2.toEvolves rfl
  have hp2a : s2.params = s.params := e2a.frame.params.trans hp1
  have hh2a : s2.half = h := e2a.frame.half.trans hh1
  refine wp_storeCode (e.values (v.denote funs env)) h (base + 1) e.types s2 s.values
    (by rw [e.values_length, e.types_length]) hh2a (by rw [hp2a]; omega)
    (by rw [e.types_length, hh2a]; omega) fun s2' f2 hold2 _ => ?_
  have f2' : Frame (base + 1) s2 { s2' with values := s.values } := f2.trans Frame.ofValues
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) (base + 1) heap1 store1 _ heap2 store2
      { s2' with values := s.values } :=
    ⟨e2a.step, e2a.frame.trans f2', e2a.holds.agree f2'⟩
  have hp2 : s2'.params = s.params := f2.params.trans hp2a
  have hh2 : s2'.half = h := f2.half.trans hh2a
  have hI2 : s2'.get base = some (.i64 (i.denote funs env)) :=
    (e2.frame.below base (by omega)).1.trans hI1
  -- The count of new words, in local `base + k + 1`.
  simp only [wp_constI64_cons]
  have hLowK : ({ s2' with values := s.values } : Locals).params.length ≤ base + e.width + 1 := by
    show s2'.params.length ≤ _; rw [hp2]; omega
  have hHighK' : base + e.width + 1 < ({ s2' with values := s.values } : Locals).half := by
    simp only [Locals.half_values, hh2]; omega
  have hHighK := Locals.lt_total hHighK'
  refine wp_localSet_local hLowK hHighK ?_
  set s3 := setLocal { s2' with values := s.values } (base + e.width + 1)
    (.i64 (wordCount e.width)) with hs3
  have hK3 : s3.get (base + e.width + 1) = some (.i64 (wordCount e.width)) :=
    Locals.get_setLocal_same hLowK hHighK
  have hF3 : Frame (base + e.width + 1) { s2' with values := s.values } s3 :=
    Frame.setValues (s := { s2' with values := s.values }) (vs := s.values) hLowK le_rfl hHighK'
  have hold3 : LocalsHold s3 (base + 1) e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans hF3) (by rw [e.values_length, e.types_length])
      (by rw [e.types_length]; omega)).mpr hold2
  have e3 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) (base + 1) heap1 store1 _ heap2 store2 s3 :=
    ⟨e2.step, e2.frame.trans (hF3.mono (by omega)), e2.holds.agree (hF3.mono (by omega))⟩
  have hp3 : s3.params = s.params := e3.frame.params.trans hp1
  have hh3 : s3.half = h := e3.frame.half.trans hh1
  have hI3 : s3.get base = some (.i64 (i.denote funs env)) :=
    (hF3.below base (by omega)).1.trans hI2
  -- The array, with room for one more element, from local `base + k + 2` on.
  refine specB_room hm x (b := base + e.width + 2) (ext := base + e.width + 1)
    (e := wordCount e.width) (s := s3) (e3.holds.mono (by omega))
    e3.step.at_ (by rw [e3.step.cap m, e1.step.cap m]; exact hCap) (by rw [hp3]; omega)
    (by rw [hh3]; omega) hK3 (by omega) (by rw [wordCount_toNat]; omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le
      (by have := hTopI (hdS hd).1; have := hTopV (hdS hd).2; rw [hT]; omega)
      (by rw [e3.step.cap m, e1.step.cap m]))
    fun heap3 store3 s4 q words hSize hPrefix aR hN4 hQ4 hv4 hTopR => ?_
  obtain ⟨p0, hp0, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap3.Owned store3 p0 words := hOwnedQ
  obtain rfl : p0 = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp0; exact hp0.1.symm
  have hAQ := hOwnedQ.values
  have hFitQ := hAQ.1
  have hMemQ := hAQ.2.1
  have hPtrQ := hAQ.pointerAddress_toNat
  have hWs : (e.words (env.get x)).size = (env.get x).size * e.width := Elem.words_size e _
  have hk29 : e.width < 536870912 := by
    rw [wordCount_toNat] at hSize; omega
  have hkw : (wordCount e.width).toNat = e.width := by rw [wordCount_toNat]; omega
  rw [hkw, hWs] at hSize
  have hnk : (env.get x).size * e.width < 536870912 := by omega
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  have hN4' : s4.get (base + e.width + 3) =
      some (.i64 (UInt64.ofNat ((env.get x).size * e.width))) := by
    rw [← hWs]; exact hN4
  have hQ4' : s4.get (base + e.width + 6) = some (.i64 p0) := hQ4
  have hPrefix' : ∀ w, w < (env.get x).size * e.width →
      words[w]! = (e.words (env.get x))[w]! := fun w hw => by
    rw [hPrefix w (by rw [hWs]; exact hw), getElem!_pos _ w (by rw [hWs]; exact hw)]
  have hp4 : s4.params = s.params := aR.frame.params.trans hp3
  have hh4 : s4.half = h := aR.frame.half.trans hh3
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (aR.frame.below base (by omega)).1.trans hI3
  have hold4 : LocalsHold s4 (base + 1) e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame aR.frame (by rw [e.values_length, e.types_length])
      (by rw [e.types_length]; omega)).mpr hold3
  -- The rest of the code, from the array after the writes or with the old length.
  have hFinish : ∀ (store5 : Store Unit) (s' : Locals) (ws : Array UInt64),
      s'.values = s.values →
      ws = e.words (LeanExe.insertAt (env.get x) (i.denote funs env) (v.denote funs env)) →
      After env slots (fun k => live k || k == x.index) live (base + e.width + 2) heap2 store2 s3
        (.array .word) .owned ws heap3 store5 s' [.i64 p0] →
      wp m rest Q store5 { s' with values := .i64 p0 :: s'.values } host := by
    rintro store5 s' ws hv' rfl aX
    have aX1 := (After.ofWords aX).lower e3.holds (by omega) fun k h => by simp [h]
    have aX2 := After.prepend (e1.holds.mono (Nat.le_succ base)) e3 aX1
      (fun k h => by simp [h]) fun k h => by simp [h]
    have aX3 := After.prepend (hVars.live_mono hIn) e1 (aX2.lower e1.holds (Nat.le_succ base)
      fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
    simpa [hv'] using hNext heap3 store5 _ [.i64 p0] (aX3.liveIn hIn) fun hd => by
      have := hTopI (hdS hd).1; have := hTopV (hdS hd).2; rw [hT]; omega
  -- The test of the position.
  simp only [wp_localGet_cons, Locals.get_values, hI4, hN4']
  rw [wp_divCode hk, words_div hk hnk]
  simp only [wp_leUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hLe : i.denote funs env ≤ UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat ≤ (env.get x).size := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hn64]
  by_cases hc : (i.denote funs env).toNat ≤ (env.get x).size
  · rw [ite_eq_left (by simp [hLe.mpr hc])]
    have hWL : (i.denote funs env).toNat * e.width ≤ (env.get x).size * e.width :=
      Nat.mul_le_mul_right _ hc
    -- The element's first word, in local `base + k + 4`.
    simp only [wp_localGet_cons, Locals.get_values, hI4]
    have hs := words_scale hk (show (i.denote funs env).toNat * e.width < 536870912 by omega)
    rw [UInt64.ofNat_toNat] at hs
    rw [wp_scaleCode, hs]
    have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤ base + e.width + 4 := by
      show s4.params.length ≤ _; rw [hp4]; omega
    have hHigh5' : base + e.width + 4 < s4.half := by rw [hh4]; omega
    have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
    refine wp_localSet_local hLow5 hHigh5 ?_
    set s5 : Locals := setLocal { s4 with values := s4.values } (base + e.width + 4)
      (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) with hs5
    have hF5 : Frame (base + e.width + 4) s4 s5 := Frame.setValues hLow5 le_rfl hHigh5'
    have hW5 : s5.get (base + e.width + 4) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) :=
      Locals.get_setLocal_same hLow5 hHigh5
    have hN5 : s5.get (base + e.width + 3) =
        some (.i64 (UInt64.ofNat ((env.get x).size * e.width))) :=
      (hF5.below _ (by omega)).1.trans hN4'
    have hQ5 : s5.get (base + e.width + 6) = some (.i64 p0) := by
      rw [Locals.get_setLocal_ne hLow5 (by omega)]; exact hQ4'
    have hh5 : s5.half = h := hF5.half.trans hh4
    have hp5 : s5.params = s.params := hF5.params.trans hp4
    -- The old length, in local `base + k + 7`.
    simp only [wp_localGet_cons, hN5]
    have hLow6 : ({ s5 with values := s5.values } : Locals).params.length ≤ base + e.width + 7 := by
      show s5.params.length ≤ _; rw [hp5]; omega
    have hHigh6' : base + e.width + 7 < s5.half := by rw [hh5]; omega
    have hHigh6 := Locals.lt_total (s := { s5 with values := s5.values }) hHigh6'
    refine wp_localSet_local hLow6 hHigh6 ?_
    set s6 : Locals := setLocal { s5 with values := s5.values } (base + e.width + 7)
      (.i64 (UInt64.ofNat ((env.get x).size * e.width))) with hs6
    have hF6 : Frame (base + e.width + 7) s5 s6 := Frame.setValues hLow6 le_rfl hHigh6'
    have hL6 : s6.get (base + e.width + 7) =
        some (.i64 (UInt64.ofNat ((env.get x).size * e.width))) :=
      Locals.get_setLocal_same hLow6 hHigh6
    have hW6 : s6.get (base + e.width + 4) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) :=
      (hF6.below _ (by omega)).1.trans hW5
    have hQ6 : s6.get (base + e.width + 6) = some (.i64 p0) :=
      (hF6.below _ (by omega)).1.trans hQ5
    have hh6 : s6.half = h := hF6.half.trans hh5
    have hp6 : s6.params = s.params := hF6.params.trans hp5
    -- The move of the words from the element's first word up.
    refine wp_shiftUp (ptr := base + e.width + 6) (lo := base + e.width + 4)
      (index := base + e.width + 7) (k := e.width) (l := (i.denote funs env).toNat * e.width)
      (h := (env.get x).size * e.width) hAQ hWL (by omega) hQ6 hW6 hL6 (by omega) (by omega)
      (by rw [hp6]; omega) (Locals.lt_total (s := s6) (by rw [hh6]; omega))
      fun store7 s7 hW7 hA7 hp7 hl7 hOther7 hv7 => ?_
    have hQ7 : s7.get (base + e.width + 6) = some (.i64 p0) := by
      rw [hOther7 _ (by omega)]; exact hQ6
    have hW7' : s7.get (base + e.width + 4) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) := by
      rw [hOther7 _ (by omega)]; exact hW6
    have hFrame7 : Frame (base + e.width + 2) s4 s7 :=
      (hF5.mono (by omega)).trans ((hF6.mono (by omega)).trans
        (Frame.ofOthers hp7 hl7 hOther7 (by omega) (by rw [hh6]; omega)))
    have aS := (aR.reframe hFrame7).rewriteRange hW7 hA7 (by rw [shiftUp_size])
    have hold7 : LocalsHold s7 (base + 1) e.types
        (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
      rw [e.values_typed]
      exact (LocalsHold.frame hFrame7 (by rw [e.values_length, e.types_length])
        (by rw [e.types_length]; omega)).mpr hold4
    have hW64 : (UInt64.ofNat ((i.denote funs env).toNat * e.width)).toNat =
        (i.denote funs env).toNat * e.width :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    -- The writes of the value's words.
    rw [← List.append_nil (storeWordsCode h (base + e.width + 6) (base + e.width + 4) 0 (base + 1)
      e.types)]
    refine wp_storeWordsCode 0 (base + 1) e.types (e.toWords (v.denote funs env))
      (shiftUp words ((i.denote funs env).toNat * e.width) ((env.get x).size * e.width) e.width)
      store7 s7 aS (hFrame7.half.trans hh4) hQ7 hW7' hold7
      (by rw [e.toWords_length, e.types_length])
      (by rw [hW64, e.types_length, shiftUp_size, hSize]; omega) fun store8 a8 => ?_
    rw [hW64] at a8
    simp only [Nat.add_zero] at a8
    have hEq : LeanExe.insertAt (env.get x) (i.denote funs env) (v.denote funs env) =
        (env.get x).insertIdx (i.denote funs env).toNat (v.denote funs env) hc := dite_eq_left hc
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hQ7]
    rw [show s4.values = s7.values from (hv7.trans rfl).symm]
    exact hFinish store8 s7 _ (hv7.trans hv4)
      (by rw [hEq]; exact Elem.words_insertIdx e (v.denote funs env) hc hSize hPrefix') a8
  · rw [ite_eq_right (by simp [hLe, hc])]
    simp only [wp_localGet_cons, Locals.get_values, hQ4', wp_wrapI64_cons, wrap_toUInt32, hN4']
    simp only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hPtrQ]; omega)]
    rw [wp_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hQ4']
    have hEq : LeanExe.insertAt (env.get x) (i.denote funs env) (v.denote funs env) = env.get x :=
      dite_eq_right hc
    exact hFinish _ s4 _ hv4
      (by rw [hEq]; exact Elem.words_extract_prefix e (by omega) hPrefix')
      (aR.rewriteRange (writeLength_frame store3 p0 words.size ((env.get x).size * e.width) hFitQ)
        (hAQ.writeLength (by omega)) (by simp only [Array.size_extract]; omega))

end Cases

/-- The code of every expression meets its specification with the allocation bound. -/
theorem Expr.code_specB {S : List Sig} (m : Module) (funs : Funs S) (bounds : Bounds S)
    (host : HostEnv Unit) (hm : Runtime m) {pv : List Value} {d0 : UInt64}
    (hCalls : CallsAtB m funs bounds d0) {Γ : List Ty} {t : Ty} (expr : Expr S Γ t) :
    (expr.depthCalls = true → pv.head? = some (.i64 d0)) →
    ∀ env slots live, CodeSpecB m funs bounds host pv expr env slots live := by
  induction expr with
  | word value => intro _; exact specB_word value
  | bool value => intro _; exact specB_bool value
  | var x => intro _; exact specB_var hm x
  | bin op left right leftSpec rightSpec =>
    intro hD
    exact specB_bin op (leftSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | cmp op left right leftSpec rightSpec =>
    intro hD
    exact specB_cmp op (leftSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | not e eSpec => intro hD; exact specB_not (eSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | and left right leftSpec rightSpec =>
    intro hD
    exact specB_and (leftSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | or left right leftSpec rightSpec =>
    intro hD
    exact specB_or (leftSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | ite c thenE elseE cSpec thenSpec elseSpec =>
    intro hD
    exact specB_ite hm (cSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (thenSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (elseSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | letE value body valueSpec bodySpec =>
    intro hD
    exact specB_letE hm (valueSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (bodySpec fun h => hD (by simp [Expr.depthCalls, h]))
  | call g args argsSpec =>
    intro hD
    exact specB_call hm hCalls g args (fun i => argsSpec i fun h => hD (by
      simp only [Expr.depthCalls, Bool.or_eq_true]
      exact Or.inr (le_argsAny _ i h))) hD
  | pair first second firstSpec secondSpec =>
    intro hD
    exact specB_pair hm (firstSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (secondSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | letPair e body eSpec bodySpec =>
    intro hD
    exact specB_letPair hm (eSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (bodySpec fun h => hD (by simp [Expr.depthCalls, h]))
  | loop count init cond body countSpec initSpec condSpec bodySpec =>
    intro hD
    exact specB_loop hm (countSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (initSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (condSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (bodySpec fun h => hD (by simp [Expr.depthCalls, h]))
  | size x => intro _; exact specB_size hm x
  | get x i iSpec =>
    intro hD; exact specB_get hm x (iSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | build count elem countSpec elemSpec =>
    intro hD
    exact specB_build hm (countSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (elemSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | set x i v iSpec vSpec =>
    intro hD
    exact specB_set hm x (iSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (vSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | push x v vSpec =>
    intro hD; exact specB_push hm x (vSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | append x y => intro _; exact specB_append hm x y
  | insertAt x i v iSpec vSpec =>
    intro hD
    exact specB_insertAt hm x (iSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (vSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | eraseAt x i iSpec =>
    intro hD; exact specB_eraseAt hm x (iSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | float bits => intro _; exact specB_float bits
  | fbin op left right leftSpec rightSpec =>
    intro hD
    exact specB_fbin op (leftSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | funary op e eSpec =>
    intro hD; exact specB_funary op (eSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | fcmp op left right leftSpec rightSpec =>
    intro hD
    exact specB_fcmp op (leftSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | toFloat op e eSpec =>
    intro hD; exact specB_toFloat op (eSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | toWord op e eSpec =>
    intro hD; exact specB_toWord op (eSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | mk first second firstSpec secondSpec =>
    intro hD
    exact specB_mk (firstSpec fun h => hD (by simp [Expr.depthCalls, h]))
      (secondSpec fun h => hD (by simp [Expr.depthCalls, h]))
  | proj x p => intro _; exact specB_proj x p

end Verified
