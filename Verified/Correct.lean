import Verified.State

/-! The compiler's correctness theorem: every function of a compiled program returns the value
that the program gives it, with the heap and store changed only as `ImplementsA` allows, and
without a trap when the function cannot trap. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem boolWord_and (x y : Bool) : boolWord x &&& boolWord y = boolWord (x && y) := by
  cases x <;> cases y <;> decide

theorem boolWord_or (x y : Bool) : boolWord x ||| boolWord y = boolWord (x || y) := by
  cases x <;> cases y <;> decide

theorem boolWord_not (x : Bool) :
    UInt64.ofNat ((if boolWord x = 0 then (1 : UInt32) else 0).toNat) = boolWord (!x) := by
  cases x <;> decide

theorem wrap_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 2 ^ 32) = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

/-- `wrap_toUInt32` with the modulus as `simp` writes it. -/
theorem ofNat_mod_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 4294967296) = a.toUInt32 :=
  wrap_toUInt32 a

/-- The offset of element `k` of an array of `size` words. -/
theorem element_offset {k : UInt64} {size : Nat} (hk : k.toNat < size)
    (hSize : 8 * (size + 1) ≤ 4294967296) :
    (k + 1) * 8 = UInt64.ofNat (8 * (k.toNat + 1)) := by
  have := hk
  have := hSize
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

@[simp] theorem shift_add (k : Nat) (live : Nat → Bool) (i : Nat) :
    shift k live (i + k) = live i := by
  simp [shift]

/-- Closes an inclusion between sets of live variables. -/
macro "live_tac" : tactic =>
  `(tactic| (intro i h; simp only [Expr.uses, Nat.add_assoc, Nat.reduceAdd, shift_add,
    Bool.or_eq_true] at h ⊢; tauto))

/-- The entry rule's assertion accepts the traps that its flag allows. -/
theorem _root_.Wasm.TrapOK.of_msg {a : Bool} {Q : Assertion Unit}
    (hQ : ∀ st, Q (.Trap st "unreachable") ↔ TrapMsg a "unreachable") : TrapOK a Q := by
  cases a
  · trivial
  · exact fun st => (hQ st).mpr rfl

theorem _root_.Wasm.TrapOK.of_imp {a b : Bool} {Q : Assertion Unit} (h : TrapOK b Q)
    (hab : a = true → b = true) : TrapOK a Q := by
  cases a
  · trivial
  · rw [hab rfl] at h; exact h

/-- The functions that `funs` gives are the module's functions at their call indices, each
returning its value with the heap and store changed only as `ImplementsA` allows, and without a
trap when the function cannot trap. -/
def Calls {S : List Sig} (m : Module) (funs : Funs S) : Prop :=
  ∀ {g : Sig} (f : FVar S g),
    @ImplementsA _ _ (Env.represent g.params) (Ty.represent g.result) g.aborts m f.callIndex
        (funs.get f) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
      ∃ fn, m.funcs[f.callIndex]? = some fn ∧ fn.numParams = widthSum g.params

theorem le_argsMax : {ps : List Ty} → (w : (i : Fin ps.length) → Nat) →
    (i : Fin ps.length) → w i ≤ argsMax w
  | _ :: _, w, ⟨0, _⟩ => Nat.le_max_left _ _
  | _ :: _, w, ⟨i + 1, h⟩ =>
    (le_argsMax (fun j => w j.succ) ⟨i, by simpa using h⟩).trans (Nat.le_max_right _ _)

theorem le_argsAny : {n : Nat} → (b : (i : Fin n) → Bool) → (i : Fin n) → b i = true →
    argsAny b = true
  | _ + 1, b, ⟨0, _⟩, h => by simp only [argsAny, Bool.or_eq_true]; exact Or.inl h
  | _ + 1, b, ⟨i + 1, hi⟩, h => by
    simp only [argsAny, Bool.or_eq_true]
    exact Or.inr (le_argsAny (fun j => b j.succ) ⟨i, by omega⟩ h)

/-- The state of `LeanExe.loop` after `k` iterations. -/
def loopState (init : α) (f : UInt64 → α → α) : Nat → α
  | 0 => init
  | k + 1 => f (UInt64.ofNat k) (loopState init f k)

theorem loopState_eq (n : UInt64) (init : α) (f : UInt64 → α → α) :
    loopState init f n.toNat = LeanExe.loop n init f := by
  unfold LeanExe.loop
  induction n.toNat with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, ← ih]; rfl

/-- The code of an expression, for the variables `live` live after it, pushes words that
represent its value: from any heap and store with the allocator invariant, in which the variables
live before the expression hold their values below `base` and the locals from `base` on are free,
the code ends after a step, with no parameter and no local below `base` changed. -/
def CodeSpec {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (host : HostEnv Unit) (e : Expr S Γ t) (env : Env Γ) (slots : List Slot)
    (live : Nat → Bool) : Prop :=
  ∀ (base : Nat) (heap : Heap) (store : Store Unit) (s : Locals),
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base →
    base + e.width ≤ s.params.length + s.locals.length →
    ∀ (rest : Program) (Q : Assertion Unit), TrapOK e.aborts Q →
    (∀ heap' store' s' ws, Step heap store heap' store' → Frame base s s' →
      t.Rep .borrowed heap' store' ws (e.denote funs env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (e.code slots base live ++ rest) Q store s host

/-- Two expressions in a row push the words of both values, the first's below the second's. -/
theorem seq_spec {S : List Sig} {Γ : List Ty} {t u : Ty} {m : Module} {funs : Funs S}
    {host : HostEnv Unit} {l : Expr S Γ t} {r : Expr S Γ u}
    (lSpec : ∀ env slots live, CodeSpec m funs host l env slots live)
    (rSpec : ∀ env slots live, CodeSpec m funs host r env slots live)
    (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (base : Nat) (heap : Heap)
    (store : Store Unit) (s : Locals)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ s.params.length + s.locals.length)
    (hRoomR : base + r.width ≤ s.params.length + s.locals.length) (rest : Program)
    (Q : Assertion Unit) (hTrap : TrapOK (l.aborts || r.aborts) Q)
    (hNext : ∀ heap' store' s' ws1 ws2, Step heap store heap' store' → Frame base s s' →
      t.Rep .borrowed heap' store' ws1 (l.denote funs env) →
      u.Rep .borrowed heap' store' ws2 (r.denote funs env) →
      wp m rest Q store' { s' with values := ws2.reverse ++ (ws1.reverse ++ s.values) } host) :
    wp m (l.code slots base (fun i => live i || r.uses i) ++ (r.code slots base live ++ rest))
      Q store s host := by
  refine lSpec env slots (fun i => live i || r.uses i) base heap store s
    (hVars.live_mono (by live_tac)) hAt hCap hBase hRoomL
    _ _ (hTrap.of_imp fun h => by simp [h]) fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
  refine rSpec env slots live base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (((hVars.frame f1 le_rfl).step h1).live_mono (live' := fun i => live i || r.uses i)
      (by live_tac))
    h1.at_ (by rw [h1.cap m]; exact hCap) (by show s1.params.length ≤ base; rw [f1.params]; omega)
    (by show base + r.width ≤ s1.params.length + s1.locals.length
        rw [f1.params, f1.length]; omega) _ _ (hTrap.of_imp fun h => by simp [h])
    fun heap2 store2 s2 ws2 h2 f2 hR2 => ?_
  exact hNext heap2 store2 s2 ws1 ws2 (h1.trans h2) (f1.trans f2.values) (hR1.step h2) hR2

/-- The code of a call's arguments pushes words that represent their values, in order. -/
theorem args_spec {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {host : HostEnv Unit} {ps : List Ty} (args : (i : Fin ps.length) → Expr S Γ (ps.get i))
    (argsSpec : ∀ i env slots live, CodeSpec m funs host (args i) env slots live)
    (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (base : Nat) (heap : Heap)
    (store : Store Unit) (s : Locals)
    (hVars : Holds env slots (fun k => live k || argsAny fun i => (args i).uses k) base heap
      store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoom : ∀ i, base + (args i).width ≤ s.params.length + s.locals.length) (rest : Program)
    (Q : Assertion Unit) (hTrap : TrapOK (argsAny fun i => (args i).aborts) Q)
    (hNext : ∀ heap' store' s' ws, Step heap store heap' store' → Frame base s s' →
      Env.Rep .borrowed heap' store' ws (Env.ofFn fun i => (args i).denote funs env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (argsCode (fun i live => (args i).code slots base live) (fun i => (args i).uses) live ++
      rest) Q store s host := by
  induction ps generalizing heap store s rest Q with
  | nil =>
    simpa [argsCode, Env.ofFn, Env.Rep] using
      hNext heap store s [] (Step.refl hAt) (Frame.refl base s) rfl
  | cons p ps ih =>
    simp only [argsCode, List.append_assoc]
    refine argsSpec ⟨0, by simp⟩ env slots
      (fun k => live k || argsAny fun i => (args i.succ).uses k) base heap store s
      (hVars.live_mono fun k hk => by
        simp only [argsAny, Bool.or_eq_true] at hk ⊢; tauto)
      hAt hCap hBase (hRoom _) _ _
      (hTrap.of_imp fun h => by simp only [argsAny, Bool.or_eq_true]; exact Or.inl h)
      fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
    refine ih (fun i => args i.succ) (fun i => argsSpec i.succ) heap1 store1
      { s1 with values := ws1.reverse ++ s.values }
      (((hVars.frame f1 le_rfl).step h1).live_mono
        (live' := fun k => live k || argsAny fun i => (args i.succ).uses k) fun k hk => by
          simp only [argsAny, Bool.or_eq_true] at hk ⊢; tauto)
      h1.at_ (by rw [h1.cap m]; exact hCap)
      (by show s1.params.length ≤ base; rw [f1.params]; exact hBase)
      (fun i => by
        show base + (args i.succ).width ≤ s1.params.length + s1.locals.length
        rw [f1.params, f1.length]; exact hRoom _) _ _
      (hTrap.of_imp fun h => by simp only [argsAny, Bool.or_eq_true]; exact Or.inr h)
      fun heap2 store2 s2 ws2 h2 f2 hR2 => ?_
    have := hNext heap2 store2 s2 (ws1 ++ ws2) (h1.trans h2) (f1.trans f2.values)
      ⟨ws1, ws2, rfl, hR1.step h2, hR2⟩
    simpa [List.reverse_append, List.append_assoc] using this

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {host : HostEnv Unit}

/-- A constant word. -/
theorem spec_word {Γ : List Ty} (value : UInt64) :
    ∀ env slots live,
      CodeSpec m funs host (Expr.word (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live base heap store s _ hAt _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.denote] using
    hNext heap store s [.i64 value] (Step.refl hAt) (Frame.refl base s) rfl

/-- A constant `Bool`. -/
theorem spec_bool {Γ : List Ty} (value : Bool) :
    ∀ env slots live,
      CodeSpec m funs host (Expr.bool (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live base heap store s _ hAt _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.denote] using
    hNext heap store s [.i64 (boolWord value)] (Step.refl hAt) (Frame.refl base s) rfl

/-- A variable: the load of its words. -/
theorem spec_var {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots live, CodeSpec m funs host (Expr.var (S := S) x) env slots live := by
  intro env slots live base heap store s hVars hAt _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars tTy x (by simp [Expr.uses])
  simp only [Expr.code]
  exact wp_loadCode ws hRep.length hold
    (hNext heap store s ws (Step.refl hAt) (Frame.refl base s) hRep.borrow)

/-- An operation on words; division and remainder save their operands to test the divisor. -/
theorem spec_bin {Γ : List Ty} (op : BinOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.bin op left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
  cases op
  case div | rem =>
    simp only [BinOp.scratch] at hWidth
    simp only [Expr.code, BinOp.code, BinOp.scratch, List.append_assoc, List.cons_append,
      List.nil_append]
    refine leftSpec env slots (fun i => live i || right.uses i) (base + 2) heap store s
      ((hVars.mono (by omega)).live_mono (by live_tac)) hAt hCap (by omega) (by omega) _ _
      (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
    simp only [Ty.rep_word] at hR1
    subst hR1
    have hp1 : s1.params = s.params := f1.params
    have hl1 : s1.locals.length = s.locals.length := f1.length
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
    let s1a := setLocal { s1 with values := s.values } base (.i64 (left.denote funs env))
    have hp1a : s1a.params = s.params := hp1
    have hl1a : s1a.locals.length = s.locals.length := by simp [s1a, setLocal, hl1]
    have hVars1 : Holds env slots (fun i => live i || (left.uses i || right.uses i)) base heap1
        store1 s1a :=
      ((hVars.frame f1 (by omega)).step h1).setLocal (le_refl _)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
    refine rightSpec env slots live (base + 2) heap1 store1 s1a
      ((hVars1.mono (by omega)).live_mono (by live_tac)) h1.at_
      (by rw [h1.cap m]; exact hCap) (by rw [hp1a]; omega) (by rw [hp1a, hl1a]; omega) _ _
      (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap2 store2 s2 ws2 h2 f2 hR2 => ?_
    simp only [Ty.rep_word] at hR2
    subst hR2
    have hp2 : s2.params = s.params := f2.params.trans hp1a
    have hl2 : s2.locals.length = s.locals.length := f2.length.trans hl1a
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    refine wp_localSet_local (by rw [hp2]; omega) (by rw [hp2, hl2]; omega) ?_
    let s2b := setLocal { s2 with values := s.values } (base + 1) (.i64 (right.denote funs env))
    show wp m _ Q store2 s2b host
    have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote funs env)) :=
      Locals.get_setLocal_same (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
        (by show base + 1 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega)
    have hLeftSlot : s2b.get base = some (.i64 (left.denote funs env)) := by
      calc s2b.get base = s2.get base :=
            Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
              (by omega)
        _ = s1a.get base := f2.below base (by omega)
        _ = some (.i64 (left.denote funs env)) :=
          Locals.get_setLocal_same (by show s1.params.length ≤ base; rw [hp1]; omega)
            (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
    have hFrame : Frame base s s2b := by
      refine ⟨hp2, by simp [s2b, setLocal, hl2], fun j hj => ?_⟩
      calc s2b.get j = s2.get j :=
            Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
              (by omega)
        _ = s1a.get j := f2.below j (by omega)
        _ = s1.get j :=
            Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega)
              (by omega)
        _ = s.get j := f1.below j (by omega)
    have hs2b : s2b.values = s.values := rfl
    simp only [wp_localGet_cons, hRightSlot, wp_eqzI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : right.denote funs env = 0
    · simp only [hZero, ite_true, ne_eq]
      simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext heap2 store2 s2b _ (h1.trans h2) hFrame rfl
    · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
      simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext heap2 store2 s2b _ (h1.trans h2) hFrame rfl
  all_goals
    simp only [BinOp.scratch, Nat.zero_add] at hWidth
    simp only [Expr.code, BinOp.code, BinOp.scratch, Nat.add_zero, List.append_assoc]
    refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
      (by omega) (by omega) _ _ hTrap fun heap2 store2 s2 ws1 ws2 h2 f2 hR1 hR2 => ?_
    simp only [Ty.rep_word] at hR1 hR2
    subst hR1 hR2
    simpa [Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
      ← UInt64.shiftRight_eq_shiftRight_mod] using hNext heap2 store2 s2 _ h2 f2 rfl

/-- A comparison of words. -/
theorem spec_cmp {Γ : List Ty} (op : CmpOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.cmp op left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) _ _ hTrap fun heap2 store2 s2 ws1 ws2 h2 f2 hR1 hR2 => ?_
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hv := hNext heap2 store2 s2 _ h2 f2 rfl
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

/-- The negation of a `Bool`. -/
theorem spec_not {Γ : List Ty} {e : Expr S Γ .bool}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.not e) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine eSpec env slots live base heap store s hVars hAt hCap hBase (by omega) _ _ hTrap
    fun heap1 store1 s1 ws h1 f1 hR => ?_
  simp only [Ty.rep_bool] at hR
  subst hR
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons, wp_extendUI32_cons, boolWord_not]
  simpa [Expr.denote] using hNext heap1 store1 s1 _ h1 f1 rfl

/-- The conjunction of `Bool`s. -/
theorem spec_and {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.and left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) _ _ hTrap fun heap2 store2 s2 ws1 ws2 h2 f2 hR1 hR2 => ?_
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_andI64_cons, boolWord_and]
  simpa [Expr.denote] using hNext heap2 store2 s2 _ h2 f2 rfl

/-- The disjunction of `Bool`s. -/
theorem spec_or {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpec m funs host left env slots live)
    (rightSpec : ∀ env slots live, CodeSpec m funs host right env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.or left right) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.code, List.append_assoc]
  refine seq_spec leftSpec rightSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) _ _ hTrap fun heap2 store2 s2 ws1 ws2 h2 f2 hR1 hR2 => ?_
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_orI64_cons, boolWord_or]
  simpa [Expr.denote] using hNext heap2 store2 s2 _ h2 f2 rfl

/-- An `if`: each branch stores its words in locals, which the code loads after the `if`. -/
theorem spec_ite {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool} {thenE elseE : Expr S Γ' tTy}
    (cSpec : ∀ env slots live, CodeSpec m funs host c env slots live)
    (thenSpec : ∀ env slots live, CodeSpec m funs host thenE env slots live)
    (elseSpec : ∀ env slots live, CodeSpec m funs host elseE env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.ite c thenE elseE) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc : c.width ≤ max c.width (tTy.width + max thenE.width elseE.width) :=
    Nat.le_max_left ..
  have hb : tTy.width + max thenE.width elseE.width ≤
      max c.width (tTy.width + max thenE.width elseE.width) := Nat.le_max_right ..
  have ht : thenE.width ≤ max thenE.width elseE.width := Nat.le_max_left ..
  have he : elseE.width ≤ max thenE.width elseE.width := Nat.le_max_right ..
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine cSpec env slots (fun i => live i || thenE.uses i || elseE.uses i) base heap store s
    (hVars.live_mono (by live_tac)) hAt hCap hBase
    (by omega) _ _ (hTrap.of_imp fun h => by simp [Expr.aborts, h])
    fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
  simp only [Ty.rep_bool] at hR1
  subst hR1
  have hp1 : s1.params = s.params := f1.params
  have hl1 : s1.locals.length = s.locals.length := f1.length
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hVars1 : Holds env slots (fun i => live i || (c.uses i || thenE.uses i || elseE.uses i))
      base heap1 store1 { s1 with values := s.values } :=
    (hVars.frame f1 le_rfl).step h1
  have hBase1 :
      ({ s1 with values := s.values } : Locals).params.length ≤ base + tTy.width := by
    show s1.params.length ≤ base + tTy.width; rw [hp1]; omega
  -- Each branch: its code, the store of its words, and the load after the `if`.
  have branch : ∀ (b : Expr S Γ' tTy),
      (∀ env slots live, CodeSpec m funs host b env slots live) →
      b.width ≤ max thenE.width elseE.width →
      (∀ i, b.uses i = true → (thenE.uses i || elseE.uses i) = true) →
      (b.aborts = true → (Expr.ite c thenE elseE).aborts = true) →
      b.denote funs env = (Expr.ite c thenE elseE).denote funs env →
      ∀ (Qb : Assertion Unit),
        (∀ st, Q (.Trap st "unreachable") → Qb (.Trap st "unreachable")) →
        (∀ st' s', wp m (loadCode base tTy.width ++ rest) Q st'
          { s' with values := s.values } host → Qb (.Fallthrough st' s')) →
        wp m (b.code slots (base + tTy.width) live ++ storeCode base tTy.width) Qb store1
          { s1 with values := s.values } host := by
    intro b bSpec hbw hbu hba hval Qb hQbTrap hQb
    rw [← List.append_nil (storeCode base tTy.width)]
    refine bSpec env slots live (base + tTy.width) heap1 store1 _
      ((hVars1.mono (by omega)).live_mono fun i hi => by
        have := hbu i
        simp only [Bool.or_eq_true] at hi this ⊢
        tauto)
      h1.at_ (by rw [h1.cap m]; exact hCap) hBase1
      (by show base + tTy.width + b.width ≤ s1.params.length + s1.locals.length
          rw [hp1, hl1]; omega) _ _ ((hTrap.of_imp hba).imp hQbTrap)
      fun heap2 store2 s2 ws2 h2 f2 hR2 => ?_
    have hp2 : s2.params = s.params := f2.params.trans hp1
    have hl2 : s2.locals.length = s.locals.length := f2.length.trans hl1
    refine wp_storeCode ws2 base tTy.width s2 s.values hR2.length (by rw [hp2]; omega)
      (by rw [hp2, hl2]; omega) fun s3 hp3 hl3 hold hout => ?_
    rw [wp_nil]
    refine hQb _ _ (wp_loadCode ws2 hR2.length hold ?_)
    have hFrame : Frame base s { s3 with values := s.values } := by
      refine ⟨hp3.trans hp2, hl3.trans hl2, fun j hj => ?_⟩
      show s3.get j = s.get j
      rw [hout j (Or.inl hj), f2.below j (by omega)]
      exact f1.below j hj
    rw [hval] at hR2
    exact hNext heap2 store2 _ ws2 (h1.trans h2) hFrame hR2
  cases hcv : c.denote funs env
  · simp (config := { decide := true }) only [↓reduceIte]
    exact branch elseE elseSpec he (fun i h => by simp [h])
      (fun h => by simp [Expr.aborts, h]) (by simp [Expr.denote, hcv]) _ (fun _ h => h)
      fun _ _ h => by simpa using h
  · simp (config := { decide := true }) only [↓reduceIte]
    exact branch thenE thenSpec ht (fun i h => by simp [h])
      (fun h => by simp [Expr.aborts, h]) (by simp [Expr.denote, hcv]) _ (fun _ h => h)
      fun _ _ h => by simpa using h

/-- A binding: the value's words in locals, then the body. -/
theorem spec_letE {Γ' : List Ty} {sTy tTy : Ty} {value : Expr S Γ' sTy}
    {body : Expr S (sTy :: Γ') tTy}
    (valueSpec : ∀ env slots live, CodeSpec m funs host value env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.letE value body) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
  have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
  simp only [Expr.code, List.append_assoc]
  refine valueSpec env slots (fun i => live i || body.uses (i + 1)) (base + sTy.width) heap
    store s
    ((hVars.mono (by omega)).live_mono (by live_tac)) hAt hCap (by omega) (by omega) _ _
    (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
  have hp1 : s1.params = s.params := f1.params
  have hl1 : s1.locals.length = s.locals.length := f1.length
  refine wp_storeCode ws1 base sTy.width s1 s.values hR1.length (by rw [hp1]; omega)
    (by rw [hp1, hl1]; omega) fun s2 hp2 hl2 hold hout => ?_
  have hVars2 : Holds (Env.cons (value.denote funs env) env) (⟨base, .borrowed⟩ :: slots)
      (fun i => shift 1 live i || body.uses i) (base + sTy.width) heap1 store1
      { s2 with values := s.values } :=
    ((((hVars.frame f1 (by omega)).step h1).agree (s' := { s2 with values := s.values })
      fun j hj => hout j (Or.inl hj)).live_mono (by live_tac)).push hold hR1
  refine bodySpec _ _ (shift 1 live) (base + sTy.width) heap1 store1
    { s2 with values := s.values } hVars2 h1.at_ (by rw [h1.cap m]; exact hCap)
    (by show s2.params.length ≤ base + sTy.width; rw [hp2, hp1]; omega)
    (by show base + sTy.width + body.width ≤ s2.params.length + s2.locals.length
        rw [hp2, hl2, hp1, hl1]; omega) _ _ (hTrap.of_imp fun h => by simp [Expr.aborts, h])
    fun heap2 store2 s3 ws2 h2 f3 hR2 => ?_
  have hFrame : Frame base s s3 := by
    refine ⟨f3.params.trans (hp2.trans hp1), f3.length.trans (hl2.trans hl1),
      fun j hj => ?_⟩
    rw [f3.below j (by omega)]
    show s2.get j = s.get j
    rw [hout j (Or.inl hj)]
    exact f1.below j (by omega)
  exact hNext heap2 store2 s3 ws2 (h1.trans h2) hFrame hR2

/-- A call: the arguments, then the callee, whose theorem `Calls` gives. -/
theorem spec_call (hImports : m.imports = []) (hCalls : Calls m funs) {sig : Sig}
    {Γ' : List Ty} (g : FVar S sig)
    (args : (i : Fin sig.params.length) → Expr S Γ' (sig.params.get i))
    (argsSpec : ∀ i env slots live, CodeSpec m funs host (args i) env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.call g args) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hRoom' : ∀ i, base + (args i).width ≤ s.params.length + s.locals.length := fun i =>
    (Nat.add_le_add_left (le_argsMax (fun i => (args i).width) i) base).trans hRoom
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine args_spec args argsSpec env slots live base heap store s hVars hAt hCap hBase hRoom'
    _ _ (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
  obtain ⟨hImpl, fn, hfn, hnum⟩ := hCalls g
  have hRun := (hImpl host store1 heap1 ws1 (Env.ofFn fun i => (args i).denote funs env)
    h1.at_ trivial hR1 Separate.nil (by rw [h1.cap m]; exact hCap)).append_args
    (by simp [hImports]) (by simpa [hImports] using hfn) (by simp [hR1.length, hnum]) s.values
  refine wp_call_runs hRun (hTrap.of_imp fun h => by simp [Expr.aborts, h])
    fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, -⟩ := hPost
  have hStep : Step heap1 store1 heap' st' :=
    ⟨hAt', hCaps, fun r hr hpos _ => hRegions r hr hpos Apart.nil⟩
  have hRep : sig.result.Rep .owned heap' st' out.reverse
      (funs.get g (Env.ofFn fun i => (args i).denote funs env)) := hOwned
  simpa using hNext heap' st' s1 out.reverse (h1.trans hStep) f1 hRep.borrow

/-- A pair: the words of both components. -/
theorem spec_pair {Γ' : List Ty} {sTy tTy : Ty} {first : Expr S Γ' sTy} {second : Expr S Γ' tTy}
    (firstSpec : ∀ env slots live, CodeSpec m funs host first env slots live)
    (secondSpec : ∀ env slots live, CodeSpec m funs host second env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.pair first second) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hFirstRoom : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have hSecondRoom : second.width ≤ max first.width second.width := Nat.le_max_right ..
  simp only [Expr.code, List.append_assoc]
  refine seq_spec firstSpec secondSpec env slots live base heap store s hVars hAt hCap hBase
    (by omega) (by omega) _ _ hTrap fun heap2 store2 s2 ws1 ws2 h2 f2 hR1 hR2 => ?_
  simpa [List.reverse_append, List.append_assoc] using
    hNext heap2 store2 s2 (ws1 ++ ws2) h2 f2 ⟨ws1, ws2, rfl, hR1, hR2⟩

/-- A destructuring of a pair: the components' words in locals, then the body. -/
theorem spec_letPair {Γ' : List Ty} {sTy tTy uTy : Ty} {e : Expr S Γ' (.pair sTy tTy)}
    {body : Expr S (tTy :: sTy :: Γ') uTy}
    (eSpec : ∀ env slots live, CodeSpec m funs host e env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.letPair e body) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hERoom : e.width ≤ max e.width body.width := Nat.le_max_left ..
  have hBodyRoom : body.width ≤ max e.width body.width := Nat.le_max_right ..
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots (fun i => live i || body.uses (i + 2)) (base + sTy.width + tTy.width)
    heap store s
    ((hVars.mono (by omega)).live_mono fun i h => by
      show (live i || (e.uses i || body.uses (i + 2))) = true
      simp only [Bool.or_eq_true] at h ⊢
      tauto) hAt hCap (by omega) (by omega) _ _
    (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap1 store1 s1 ws h1 f1 hR => ?_
  obtain ⟨ws1, ws2, rfl, hR1, hR2⟩ := hR
  have hp1 : s1.params = s.params := f1.params
  have hl1 : s1.locals.length = s.locals.length := f1.length
  rw [show (ws1 ++ ws2).reverse ++ s.values = ws2.reverse ++ (ws1.reverse ++ s.values) by
    simp]
  refine wp_storeCode ws2 (base + sTy.width) tTy.width s1 _ hR2.length (by rw [hp1]; omega)
    (by rw [hp1, hl1]; omega) fun s2 hp2 hl2 hold2 hout2 => ?_
  refine wp_storeCode ws1 base sTy.width s2 s.values hR1.length (by rw [hp2, hp1]; omega)
    (by rw [hp2, hl2, hp1, hl1]; omega) fun s3 hp3 hl3 hold3 hout3 => ?_
  have hbelow : ∀ j < base, ({ s3 with values := s.values } : Locals).get j = s1.get j := by
    intro j hj
    show s3.get j = s1.get j
    rw [hout3 j (Or.inl hj), hout2 j (Or.inl (by omega))]
  have hold2' : LocalsHold { s3 with values := s.values } (base + sTy.width) ws2 := by
    intro k hk
    show s3.get (base + sTy.width + k) = _
    rw [hout3 _ (Or.inr (by omega))]
    exact hold2 k hk
  have hVars3 : Holds (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
      (⟨base + sTy.width, .borrowed⟩ :: ⟨base, .borrowed⟩ :: slots)
      (fun i => shift 2 live i || body.uses i) (base + sTy.width + tTy.width) heap1 store1
      { s3 with values := s.values } :=
    ((((((hVars.frame f1 (by omega)).step h1).agree hbelow).live_mono
      (live' := fun i => shift 2 live (i + 1 + 1) || body.uses (i + 1 + 1)) (by live_tac)).push
        (live' := fun i => shift 2 live (i + 1) || body.uses (i + 1)) hold3 hR1).push
        (live' := fun i => shift 2 live i || body.uses i) hold2' hR2)
  refine bodySpec _ _ (shift 2 live) (base + sTy.width + tTy.width) heap1 store1
    { s3 with values := s.values } hVars3 h1.at_ (by rw [h1.cap m]; exact hCap)
    (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3, hp2, hp1]; omega)
    (by show base + sTy.width + tTy.width + body.width ≤
          s3.params.length + s3.locals.length
        rw [hp3, hl3, hp2, hl2, hp1, hl1]; omega) _ _
    (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap2 store2 s4 ws4 h2 f4 hR4 => ?_
  have hFrame : Frame base s s4 := by
    refine ⟨f4.params.trans (hp3.trans (hp2.trans hp1)),
      f4.length.trans (hl3.trans (hl2.trans hl1)), fun j hj => ?_⟩
    rw [f4.below j (by omega), hbelow j hj]
    exact f1.below j (by omega)
  exact hNext heap2 store2 s4 ws4 (h1.trans h2) hFrame hR4

/-- A loop, by `wp_loop_cons` with an invariant: the index `i` is at most the count, and the
state locals hold the state after `i` iterations. -/
theorem spec_loop {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word} {init : Expr S Γ' tTy}
    {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots live, CodeSpec m funs host count env slots live)
    (initSpec : ∀ env slots live, CodeSpec m funs host init env slots live)
    (bodySpec : ∀ env slots live, CodeSpec m funs host body env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.loop count init body) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc : count.width ≤
      max count.width (max (1 + init.width) (2 + tTy.width + body.width)) :=
    Nat.le_max_left ..
  have hi : 1 + init.width ≤
      max count.width (max (1 + init.width) (2 + tTy.width + body.width)) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hb : 2 + tTy.width + body.width ≤
      max count.width (max (1 + init.width) (2 + tTy.width + body.width)) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  refine countSpec env slots (fun i => live i || init.uses i || body.uses (i + 2)) base heap
    store s (hVars.live_mono (by live_tac)) hAt hCap hBase
    (by omega) _ _ (hTrap.of_imp fun h => by simp [Expr.aborts, h])
    fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
  simp only [Ty.rep_word] at hR1
  subst hR1
  have hp1 : s1.params = s.params := f1.params
  have hl1 : s1.locals.length = s.locals.length := f1.length
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
  have hF2 : Frame base s
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) :=
    ⟨hp1, by simp [setLocal, hl1], fun j hj => by
      rw [Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega)
        (by omega)]
      exact f1.below j hj⟩
  have hN2 : (setLocal { s1 with values := s.values } base
      (.i64 (count.denote funs env))).get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same (by show s1.params.length ≤ base; rw [hp1]; omega)
      (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
  -- The initial state, in the locals from `base + 2` on.
  refine initSpec env slots (fun i => live i || body.uses (i + 2)) (base + 1) heap1 store1 _
    ((((hVars.agree fun j hj => hF2.below j hj).step h1).mono (Nat.le_succ base)).live_mono
      (by live_tac))
    h1.at_ (by rw [h1.cap m]; exact hCap) (by rw [hF2.params]; omega)
    (by rw [hF2.params, hF2.length]; omega) _ _
    (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap2 store2 s3 ws0 h3 f3 hR0 => ?_
  have hF3 : Frame base s s3 := hF2.trans (f3.mono (Nat.le_succ base))
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) :=
    (f3.below base (by omega)).trans hN2
  refine wp_storeCode ws0 (base + 2) tTy.width s3 s.values hR0.length
    (by rw [hF3.params]; omega) (by rw [hF3.params, hF3.length]; omega)
    fun s4 hp4 hl4 hold4 hout4 => ?_
  -- The index, in local `base + 1`.
  simp only [wp_constI64_cons]
  refine wp_localSet_local (s := s4) (vs := s.values) (by rw [hp4, hF3.params]; omega)
    (by rw [hp4, hl4, hF3.params, hF3.length]; omega) ?_
  have hLow4 : ({ s4 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s4.params.length ≤ base + 1; rw [hp4, hF3.params]; omega
  have hF5 : Frame base s
      (setLocal { s4 with values := s.values } (base + 1) (.i64 0)) :=
    ⟨hp4.trans hF3.params, by simp [setLocal, hl4, hF3.length], fun j hj => by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values,
        hout4 j (Or.inl (by omega))]
      exact hF3.below j hj⟩
  have hN5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get base =
      some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values,
      hout4 base (Or.inl (by omega))]
    exact hN3
  have hI5 : (setLocal { s4 with values := s.values } (base + 1) (.i64 0)).get (base + 1) =
      some (.i64 0) :=
    Locals.get_setLocal_same hLow4
      (by show base + 1 < s4.params.length + s4.locals.length
          rw [hp4, hl4, hF3.params, hF3.length]; omega)
  have hold5 : LocalsHold (setLocal { s4 with values := s.values } (base + 1) (.i64 0))
      (base + 2) ws0 := fun k hk => by
    rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]
    exact hold4 k hk
  -- The loop: the invariant holds the count, the index `i`, and the state after `i`
  -- iterations, and the count less the index decreases.
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st s' => ∃ heapI, Step heap store heapI st ∧ Frame base s s' ∧
      s'.get base = some (.i64 (count.denote funs env)) ∧
      ∃ i : UInt64, i ≤ count.denote funs env ∧ s'.get (base + 1) = some (.i64 i) ∧
        ∃ ws, LocalsHold s' (base + 2) ws ∧ tTy.Rep .borrowed heapI st ws
          (loopState (init.denote funs env)
            (fun i acc => body.denote funs (.cons acc (.cons i env))) i.toNat))
    (fun _ s' => match s'.get (base + 1) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2, h1.trans h3, hF5, hN5, 0, UInt64.zero_le, hI5, ws0, hold5, hR0⟩ ?_
  rintro st si ⟨heapI, hStepI, hFi, hNi, i, hiN, hii, wsI, holdi, hRi⟩
  simp only [wp_localGet_cons, Locals.get_values, hii, hNi, wp_geUI64_cons, wp_br_if_cons]
  have hRoomi : base + 2 + tTy.width + body.width ≤ si.params.length + si.locals.length := by
    rw [hFi.params, hFi.length]; omega
  by_cases hge : count.denote funs env ≤ i
  · -- The index reached the count: the state locals hold the loop's value.
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    rw [UInt64.le_antisymm hiN hge, loopState_eq] at hRi
    refine wp_loadCode wsI hRi.length holdi ?_
    exact hNext heapI st si wsI hStepI hFi hRi
  · -- One more iteration: the body, the store of its value, and the next index.
    have hlt : i < count.denote funs env := UInt64.not_le.mp hge
    have hsucc : (i + 1).toNat = i.toNat + 1 := by
      have := UInt64.lt_iff_toNat_lt.mp hlt
      have := (count.denote funs env).toNat_lt
      rw [UInt64.toNat_add]; simp; omega
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte]
    have holdIdx : LocalsHold si (base + 1) [.i64 i] := fun k hk => by
      obtain rfl : k = 0 := by simpa using hk
      simpa using hii
    have hOuter : Holds env slots (fun j => live j || (count.uses j || init.uses j ||
        body.uses (j + 2))) base heapI st si :=
      (hVars.frame hFi le_rfl).step hStepI
    have hVarsB := ((((hOuter.mono (Nat.le_succ base)).live_mono
      (live' := fun j => shift 2 (fun i => live i || body.uses (i + 2)) (j + 1 + 1) ||
        body.uses (j + 1 + 1)) (by live_tac)).push (t := .word) (v := i) (mode := .borrowed)
        (live' := fun j => shift 2 (fun i => live i || body.uses (i + 2)) (j + 1) ||
          body.uses (j + 1)) holdIdx rfl).mono (by show base + 1 + 1 ≤ base + 2; omega)).push
        (mode := .borrowed)
        (live' := fun j => shift 2 (fun i => live i || body.uses (i + 2)) j || body.uses j)
        holdi hRi
    refine bodySpec _ _ (shift 2 fun i => live i || body.uses (i + 2)) (base + 2 + tTy.width)
      heapI st si hVarsB hStepI.at_
      (by rw [hStepI.cap m]; exact hCap) (by rw [hFi.params]; omega) hRoomi _ _
      ((hTrap.of_imp fun h => by simp [Expr.aborts, h]).imp fun _ h => h)
      fun heap6 store6 s6 ws6 h6 f6 hR6 => ?_
    refine wp_storeCode ws6 (base + 2) tTy.width s6 si.values hR6.length
      (by rw [f6.params, hFi.params]; omega)
      (by rw [f6.params, f6.length, hFi.params, hFi.length]; omega)
      fun s7 hp7 hl7 hold7 hout7 => ?_
    have hp7' : s7.params = s.params := hp7.trans (f6.params.trans hFi.params)
    have hl7' : s7.locals.length = s.locals.length :=
      hl7.trans (f6.length.trans hFi.length)
    have hget7 : ∀ j < base + 2, s7.get j = si.get j := fun j hj => by
      rw [hout7 j (Or.inl hj)]
      exact f6.below j (by omega)
    simp only [wp_localGet_cons, Locals.get_values, hget7 (base + 1) (by omega), hii,
      wp_constI64_cons, wp_addI64_cons]
    have hLow7 : ({ s7 with values := si.values } : Locals).params.length ≤ base + 1 := by
      show s7.params.length ≤ base + 1; rw [hp7']; omega
    refine wp_localSet_local (s := s7) (vs := si.values) (by rw [hp7']; omega)
      (by rw [hp7', hl7']; omega) ?_
    have hget8 : (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))).get
        (base + 1) = some (.i64 (i + 1)) :=
      Locals.get_setLocal_same hLow7
        (by show base + 1 < s7.params.length + s7.locals.length; rw [hp7', hl7']; omega)
    have hold8 : LocalsHold (setLocal { s7 with values := si.values } (base + 1)
        (.i64 (i + 1))) (base + 2) ws6 := fun k hk => by
      rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values]
      exact hold7 k hk
    have hR8 : tTy.Rep .borrowed heap6 store6 ws6 (loopState (init.denote funs env)
        (fun i acc => body.denote funs (.cons acc (.cons i env))) (i + 1).toNat) := by
      rw [hsucc, loopState, UInt64.ofNat_toNat]
      exact hR6
    rw [wp_br_cons]
    dsimp only
    refine ⟨⟨heap6, hStepI.trans h6, ⟨hp7', by simp [setLocal, hl7'], fun j hj => ?_⟩, ?_,
      i + 1, UInt64.le_iff_toNat_le.mpr ?_, hget8, ws6, hold8, hR8⟩, ?_⟩
    · rw [Locals.get_values, Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values,
        hget7 j (by omega)]
      exact hFi.below j hj
    · rw [Locals.get_setLocal_ne hLow7 (by omega), Locals.get_values,
        hget7 base (by omega)]
      exact hNi
    · have := UInt64.lt_iff_toNat_lt.mp hlt
      omega
    · have := UInt64.lt_iff_toNat_lt.mp hlt
      simp only [hget8]
      omega

/-- The size of an array: the load of its length word. -/
theorem spec_size {Γ' : List Ty} {a : Expr S Γ' .array}
    (aSpec : ∀ env slots live, CodeSpec m funs host a env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.size a) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine aSpec env slots live base heap store s hVars hAt hCap hBase hRoom _ _ hTrap
    fun heap1 store1 s1 ws h1 f1 hR => ?_
  obtain ⟨ptr, rfl, hB⟩ := hR
  have hA := hB.borrow.values
  have hLength := hA.lengthBound
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero,
    UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using
    hNext heap1 store1 s1 [.i64 (a.denote funs env).size.toUInt64] h1 f1 rfl

/-- A read of an array: the address and the position in locals, a comparison of the position
with the length word, and the load of the element or 0. -/
theorem spec_get {Γ' : List Ty} {a : Expr S Γ' .array} {i : Expr S Γ' .word}
    (aSpec : ∀ env slots live, CodeSpec m funs host a env slots live)
    (iSpec : ∀ env slots live, CodeSpec m funs host i env slots live) :
    ∀ env slots live, CodeSpec m funs host (Expr.get a i) env slots live := by
  intro env slots live base heap store s hVars hAt hCap hBase hRoom rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have ha : a.width ≤ max a.width (max 2 (1 + i.width)) := Nat.le_max_left ..
  have h2 : 2 ≤ max a.width (max 2 (1 + i.width)) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hi : 1 + i.width ≤ max a.width (max 2 (1 + i.width)) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The address, in local `base`.
  refine aSpec env slots (fun k => live k || i.uses k) base heap store s
    (hVars.live_mono (by live_tac)) hAt hCap hBase (by omega) _ _
    (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap1 store1 s1 ws1 h1 f1 hR1 => ?_
  obtain ⟨ptr, rfl, hB1⟩ := hR1
  have hp1 : s1.params = s.params := f1.params
  have hl1 : s1.locals.length = s.locals.length := f1.length
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
  let s1a := setLocal { s1 with values := s.values } base (.i64 ptr)
  have hp1a : s1a.params = s.params := hp1
  have hl1a : s1a.locals.length = s.locals.length := by simp [s1a, setLocal, hl1]
  have hVars1 : Holds env slots (fun k => live k || (a.uses k || i.uses k)) base heap1 store1
      s1a :=
    ((hVars.frame f1 le_rfl).step h1).setLocal (le_refl _)
      (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
  have hPtr1 : s1a.get base = some (.i64 ptr) :=
    Locals.get_setLocal_same (by show s1.params.length ≤ base; rw [hp1]; omega)
      (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
  -- The position, in local `base + 1`.
  refine iSpec env slots live (base + 1) heap1 store1 s1a
    ((hVars1.mono (Nat.le_succ base)).live_mono (by live_tac)) h1.at_
    (by rw [h1.cap m]; exact hCap) (by rw [hp1a]; omega) (by rw [hp1a, hl1a]; omega) _ _
    (hTrap.of_imp fun h => by simp [Expr.aborts, h]) fun heap2 store2 s2 ws2 h2 f2 hR2 => ?_
  simp only [Ty.rep_word] at hR2
  subst hR2
  have hp2 : s2.params = s.params := f2.params.trans hp1a
  have hl2 : s2.locals.length = s.locals.length := f2.length.trans hl1a
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  refine wp_localSet_local (by rw [hp2]; omega) (by rw [hp2, hl2]; omega) ?_
  let s2b := setLocal { s2 with values := s.values } (base + 1) (.i64 (i.denote funs env))
  show wp m _ Q store2 s2b host
  have hK : s2b.get (base + 1) = some (.i64 (i.denote funs env)) :=
    Locals.get_setLocal_same (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
      (by show base + 1 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega)
  have hP : s2b.get base = some (.i64 ptr) := by
    calc s2b.get base = s2.get base :=
          Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
            (by omega)
      _ = s1a.get base := f2.below base (by omega)
      _ = some (.i64 ptr) := hPtr1
  have hFrame : Frame base s s2b := by
    refine ⟨hp2, by simp [s2b, setLocal, hl2], fun j hj => ?_⟩
    calc s2b.get j = s2.get j :=
          Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
            (by omega)
      _ = s1a.get j := f2.below j (by omega)
      _ = s1.get j :=
          Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega) (by omega)
      _ = s.get j := f1.below j (by omega)
  have hs2b : s2b.values = s.values := rfl
  have hA := (hB1.step h2).borrow.values
  have hLength := hA.lengthBound
  have hSize := hA.size_lt
  have hv := hNext heap2 store2 s2b [.i64 (a.denote funs env)[(i.denote funs env).toNat]!]
    (h1.trans h2) hFrame rfl
  simp only [wp_localGet_cons, Locals.get_values, hK, hP, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  simp only [wp_ltUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (a.denote funs env).size ↔
      (i.denote funs env).toNat < (a.denote funs env).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hSize]
  by_cases hk : (i.denote funs env).toNat < (a.denote funs env).size
  · rw [ite_eq_left (by simp [hLess.mpr hk])]
    have hOffset := element_offset hk (by have := hA.1; omega)
    have hElement := hA.elementBound _ hk
    simp only [wp_localGet_cons, Locals.get_values, hK, hP, wp_constI64_cons, wp_addI64_cons,
      wp_mulI64_cons, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32, UInt32.toNat_zero,
      Nat.add_zero, UInt32.add_zero, hOffset]
    rw [ite_eq_right (by omega), hA.elementRead _ hk,
      ← getElem!_pos (a.denote funs env) (i.denote funs env).toNat hk]
    simpa [wp_nil, hs2b] using hv
  · rw [ite_eq_right (by simp [hLess, hk])]
    simp only [wp_constI64_cons, getElem!_neg (a.denote funs env) (i.denote funs env).toNat hk]
      at hv ⊢
    simpa [wp_nil, hs2b, show (default : UInt64) = 0 from rfl] using hv

end Cases

/-- The code of every expression meets its specification. -/
theorem Expr.code_spec {S : List Sig} (m : Module) (funs : Funs S) (host : HostEnv Unit)
    (hImports : m.imports = []) (hCalls : Calls m funs) {Γ : List Ty} {t : Ty}
    (expr : Expr S Γ t) : ∀ env slots live, CodeSpec m funs host expr env slots live := by
  induction expr with
  | word value => exact spec_word value
  | bool value => exact spec_bool value
  | var x => exact spec_var x
  | bin op left right leftSpec rightSpec => exact spec_bin op leftSpec rightSpec
  | cmp op left right leftSpec rightSpec => exact spec_cmp op leftSpec rightSpec
  | not e eSpec => exact spec_not eSpec
  | and left right leftSpec rightSpec => exact spec_and leftSpec rightSpec
  | or left right leftSpec rightSpec => exact spec_or leftSpec rightSpec
  | ite c thenE elseE cSpec thenSpec elseSpec => exact spec_ite cSpec thenSpec elseSpec
  | letE value body valueSpec bodySpec => exact spec_letE valueSpec bodySpec
  | call g args argsSpec => exact spec_call hImports hCalls g args argsSpec
  | pair first second firstSpec secondSpec => exact spec_pair firstSpec secondSpec
  | letPair e body eSpec bodySpec => exact spec_letPair eSpec bodySpec
  | loop count init body countSpec initSpec bodySpec => exact spec_loop countSpec initSpec bodySpec
  | size a aSpec => exact spec_size aSpec
  | get a i aSpec iSpec => exact spec_get aSpec iSpec

theorem Var.index_lt {Γ : List Ty} {t : Ty} (x : Var Γ t) : x.index < Γ.length := by
  induction x with
  | here => simp [Var.index]
  | there y ih => simp [Var.index]; omega

/-- The position of a variable's first word among the words of the context's values. -/
def Var.offset : {Γ : List Ty} → {t : Ty} → Var Γ t → Nat
  | _ :: _, _, .here => 0
  | s :: _, _, .there y => s.width + y.offset

theorem paramSlots_getD {Γ : List Ty} {t : Ty} (x : Var Γ t) (loc : Nat) :
    (paramSlots Γ loc).getD x.index default = ⟨loc + x.offset, .borrowed⟩ := by
  induction x generalizing loc with
  | here => simp [paramSlots, Var.index, Var.offset]
  | @there Γ' t' s' y ih =>
    simp only [paramSlots, Var.index, Var.offset, List.getD_cons_succ, ih]
    congr 1
    omega

theorem Var.offset_width {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    x.offset + t.width ≤ widthSum Γ := by
  induction x with
  | here => simp [Var.offset, widthSum_cons]
  | @there Γ' t' s' y ih => simp only [Var.offset, widthSum_cons]; omega

/-- The words of a variable among the words of the context's values. -/
theorem Env.Rep.var {mode : Mode} {heap : Heap} {store : Store Unit} {Γ : List Ty} {t : Ty}
    (x : Var Γ t) : ∀ {ws : List Value} {env : Env Γ}, Env.Rep mode heap store ws env →
      t.Rep mode heap store ((ws.drop x.offset).take t.width) (env.get x) := by
  induction x with
  | here =>
    intro ws env h
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, -⟩ := h
      rw [Var.offset, List.drop_zero, List.take_left' h1.length]
      exact h1
  | @there Γ' t' s' y ih =>
    intro ws env h
    cases env with
    | cons v rest =>
      obtain ⟨first, rest', rfl, h1, h2⟩ := h
      rw [Var.offset, ← h1.length, List.drop_append, List.drop_eq_nil_of_le (by omega),
        List.nil_append, Nat.add_sub_cancel_left]
      exact ih h2

theorem FVar.index_lt {S : List Sig} {g : Sig} (f : FVar S g) :
    f.index < S.length := by
  induction f with
  | here => simp [FVar.index]
  | there g ih => simp [FVar.index]; omega

/-- A function at position `pos` of a module whose functions at the call indices compute the
functions it calls computes `func.denote funs`. -/
theorem Func.correct {S : List Sig} (func : Func S) (funs : Funs S) (m : Module) (pos : Nat)
    (hImports : m.imports = []) (hFunc : m.funcs[pos]? = some (func.function pos))
    (hCalls : Calls m funs) :
    @ImplementsA _ _ (Env.represent func.params) (Ty.represent func.result) func.body.aborts m
      pos (func.denote funs) (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap params args hAt _ hArgs _ hCap
  have hArgs' : Env.Rep .borrowed heap store params args := hArgs
  have hLength : params.length = widthSum func.params := hArgs'.length
  apply Runs.of_wp_entry_for (f := func.function pos)
    (by rw [hImports, List.length_nil, Nat.sub_zero]; exact hFunc) (hImp := by simp [hImports])
  have hTake : (params.reverse.take (func.function pos).numParams).reverse = params := by
    rw [List.take_of_length_le (by simp [Func.function, Func.type, Function.numParams, hLength])]
    simp
  rw [hTake, show (func.function pos).body =
    func.body.code (paramSlots func.params 0) (widthSum func.params) (fun _ => false) ++ [] by
      simp [Func.function]]
  refine Expr.code_spec m funs host hImports hCalls func.body args (paramSlots func.params 0)
    (fun _ => false) (widthSum func.params) heap store _ (fun t x _ => ?_) hAt hCap
    (by simp [Function.toLocals, hLength]) (by simp [Function.toLocals, Func.function, hLength])
    [] _ ?_ fun heap' store' s' ws hStep _ hRep => ?_
  · rw [paramSlots_getD x 0, Nat.zero_add]
    refine ⟨x.offset_width, _, fun k hk => ?_, hArgs'.var x⟩
    have hk' := hk
    simp only [List.length_take, List.length_drop] at hk'
    have hlt : x.offset + k < params.length := by omega
    simp only [Locals.get, Function.toLocals, hlt, ↓reduceIte, List.getElem_take,
      List.getElem_drop]
    simp [List.getElem?_eq_getElem hlt]
  · exact TrapOK.of_msg fun _ => Iff.rfl
  · rw [wp_nil]
    refine ⟨heap', hStep.at_, ?_, hStep.caps, fun r hr hpos _ =>
      hStep.keeps r hr hpos (fun _ hb => nomatch hb), trivial⟩
    have hLen := hRep.length
    show func.result.Rep .owned heap' store' _ (func.body.denote funs args)
    convert hRep.owned func.result_scalar using 1
    simp [Func.function, Func.type, Function.numParams, Function.toLocals, hLen, hLength,
      List.take_of_length_le]

/-- Every function of a program, placed from position 2 of a module without imports, computes
its meaning. -/
theorem Prog.calls {S : List Sig} (prog : Prog S) (m : Module) (hImports : m.imports = [])
    (hFuncs : ∀ k < S.length, m.funcs[2 + k]? = prog.functions[k]?) : Calls m prog.funs := by
  induction prog with
  | nil => intro g fv; cases fv
  | @cons S' f rest ih =>
    have hRest : Calls m rest.funs := ih fun k hk => by
      rw [hFuncs k (by simp; omega)]
      simp [Prog.functions, List.getElem?_append_left (by rw [rest.functions_length]; exact hk)]
    intro g fv
    cases fv with
    | here =>
      have hpos : m.funcs[2 + S'.length]? = some (f.function (2 + S'.length)) := by
        rw [hFuncs _ (by simp)]
        simp [Prog.functions, rest.functions_length]
      refine ⟨?_, f.function (2 + S'.length), ?_, ?_⟩
      · simpa [FVar.callIndex, FVar.index, Funs.get, Prog.funs] using
          Func.correct f rest.funs m _ hImports hpos hRest
      · simpa [FVar.callIndex, FVar.index] using hpos
      · simp [Func.function, Func.type, Function.numParams]
    | there g' =>
      obtain ⟨h1, fn, h2, h3⟩ := hRest g'
      have hidx : (FVar.there g' :
          FVar (⟨f.params, f.result, f.body.aborts⟩ :: S') g).callIndex = g'.callIndex := by
        have := g'.index_lt
        simp only [FVar.callIndex, FVar.index, List.length_cons]
        omega
      rw [hidx]
      exact ⟨by simpa [Funs.get, Prog.funs] using h1, fn, h2, h3⟩

/-- The correctness theorem.  Every function of a program's module, at its call index, computes
the function that the program gives it: it returns words that represent the value, with the
heap and store changed only as `ImplementsA` allows, and it traps only when it may allocate. -/
theorem Prog.correct {S : List Sig} (prog : Prog S) : Calls (compile prog) prog.funs :=
  prog.calls _ rfl fun k _ => compile_funcs prog k

/-- A function's theorem for the verified compiler's representation gives the theorem for Lean
types whose representations agree with it. -/
theorem ImplementsA.comap {α β γ δ : Type} [Represent α] [Represent β] [Represent γ]
    [Represent δ] {aborts : Bool} {m : Module} {entry : Nat} {f : α → γ}
    (h : ImplementsA aborts m entry f (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (g : β → α) (k : γ → δ)
    (hArgs : ∀ heap store vs y, Represent.borrowed heap store vs y →
      Represent.borrowed heap store vs (g y))
    (hSep : ∀ store vs y,
      Separate store (Represent.moves store vs y) (Represent.reads store vs y) →
        Separate store (Represent.moves store vs (g y)) (Represent.reads store vs (g y)))
    (hMoves : ∀ store vs y, Represent.moves store vs (g y) = Represent.moves store vs y)
    (hResult : ∀ heap store vs z, Represent.owned heap store vs z →
      Represent.owned heap store vs (k z))
    (hBlocks : ∀ store vs z, Represent.blocks store vs (k z) = Represent.blocks store vs z) :
    ImplementsA aborts m entry (k ∘ f ∘ g) (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro env store heap vs y hAt _ hY hSep' hCap
  exact (h env store heap vs (g y) hAt trivial (hArgs _ _ _ _ hY) (hSep _ _ _ hSep') hCap).mono
    fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, _⟩ =>
      ⟨heap', hAt', hResult _ _ _ _ hOwned, hCaps, fun r hr hpos hA => by
        obtain ⟨hb, hreg, hout⟩ := hRegions r hr hpos (by rw [hMoves]; exact hA)
        refine ⟨hb, hreg, ?_⟩
        simp only [Represent.outside, Function.comp_apply, hBlocks]
        exact hout, trivial⟩

/-- A function's theorem in the form of Lean's instances: for the Lean tuple of its arguments and
its result type, with the instances Lean synthesizes for them. -/
theorem ImplementsA.lean {ps : List Ty} {r : Ty} {aborts : Bool} {m : Module} {entry : Nat}
    {f : Env ps → r.denote} (hr : r.scalar = true)
    (h : @ImplementsA _ _ (Env.represent ps) (Ty.represent r) aborts m entry f
      (fun _ _ _ => True) (fun _ _ _ _ _ => True)) :
    @ImplementsA _ _ (argsInst ps) r.leanInst aborts m entry (fun y => f (Env.ofArgs ps y))
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  @ImplementsA.comap _ _ _ _ (Env.represent ps) (argsInst ps) (Ty.represent r) r.leanInst
    aborts m entry f h (Env.ofArgs ps) id
    (fun _ _ _ _ hy => (argsInst_borrowed ps).mp hy) (fun _ _ _ _ => Separate.nil)
    (fun _ _ _ => (argsInst_moves ps).symm)
    (fun _ _ _ _ hz => (r.leanInst_owned hr).mpr hz) (fun _ _ _ => r.leanInst_blocks hr)

end Verified
