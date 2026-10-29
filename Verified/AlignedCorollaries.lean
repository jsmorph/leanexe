import Verified.AlignedCopy

/-!
The original theorems whose flagged twins take `CopyCodeX` or `ReadReleaseX` and lie upstream of
`Verified/AlignedCopy.lean`, which proves both premises for every runtime.  Each is the
`strict = false` instance of its twin, with the premises from `copyCodeX` and `readReleaseX`, and
keeps its name and statement.  `spec_loop_with` keeps its own proof, which uses the corollaries
of this module.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit}
  {pv : List Value}

/-- A call: the arguments, the callee, whose theorem `Calls` gives, and the release of the owned
variables that the arguments use and that die at the call, other than those that the call
consumes. -/
theorem spec_call (hm : Runtime m) {d0 : UInt64}
    (hCalls : CallsAt m funs flags bounds fits d0 pool)
    {sig : Sig}
    {Γ' : List Ty} (g : FVar S sig)
    (args : (i : Fin sig.params.length) → Expr S Γ' (sig.params.get i))
    (argsSpec : ∀ i env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (args i) env
        slots paid live)
    (hDepth : (Expr.call g args).depthCalls = true → pv.head? = some (.i64 d0)) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.call g args) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_call (strict := false) hm nofun (copyCodeX hm)
      (CallsAtX.false_iff.mpr hCalls) g args
      (fun i env slots paid live => CodeSpecX.false_iff.mpr (argsSpec i env slots paid live)) hDepth
      env slots paid live)

/-- A variable in an owned position: its words as an owned value, which move it when it is owned
and dies, and a copy otherwise, which raises `top` by at most `x.ownedCost` and traps only when
`top` cannot rise by that much. -/
theorem spec_ownedVar (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.positions = h)
    (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || i == x.index) base heap store s)
    (hAt : heap.At store)
    (hSafe : pool.Safe env slots (fun i => live i || i == x.index) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoom : base + copyWidth tTy ≤ h)
    (hTrap : TrapOK (!decide (heap.Within store m
      (x.ownedCost (slots.map Slot.mode) live (env.get x)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || i == x.index) live base heap store s tTy .owned
        (env.get x) heap' store' s' ws →
      heap'.top.toNat ≤ heap.top.toNat + x.ownedCost (slots.map Slot.mode) live (env.get x) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wp m (x.ownedCode h slots base live ++ rest) Q store s host :=
  specX_ownedVar (strict := false) (copyCodeX hm) x hh hpv hVars hAt nofun hSafe hCap hBase hRoom
    hTrap (fun heap' store' s' ws a1 _ a3 => hNext heap' store' s' ws a1 a3)

theorem spec_bytesGet (hm : Runtime m) {Γ' : List Ty} (x : Var Γ' .bytes)
    {index : Expr S Γ' .word}
    (indexSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv index env slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.bytesGet x index)
      env slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_bytesGet (strict := false)
      (readReleaseX (strict := false) hm nofun) x
      (fun env slots paid live => CodeSpecX.false_iff.mpr (indexSpec env slots paid live)) env slots
      paid live)

/-- A value turned from mode `source` into mode `target` after an expression's code: a borrowed
value that must be owned is copied into new blocks, which raises `top` by at most
`coerceCost t source target v`, a value already owned keeps its store and words, and the facts of
`After` carry over. -/
theorem After.coerce (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {liveIn live : Nat → Bool} {h base base' : Nat} {heap : Heap} {store : Store Unit}
    {s : Locals} {t : Ty} {source target : Mode} {v : t.denote} {heap1 : Heap}
    {store1 : Store Unit} {s1 : Locals} {ws vs : List Value} {rest : Program}
    {Q : Assertion Unit}
    (a : After env slots liveIn live base heap store s t source v heap1 store1 s1 ws)
    (hTarget : source = .owned → target = .owned) (hBase' : base ≤ base')
    (hLow : s1.params.length ≤ base') (hh : s1.positions = h) (hRoom : base' + copyWidth t ≤ h)
    (hCap : store1.memoryCap m 0 ≤ 65535)
    (hTrap : source = .borrowed → target = .owned → t.scalar = false →
      TrapOK (!decide (heap1.Within store1 m (t.copyCost v))) Q)
    (hNext : ∀ heap2 store2 s2 ws2,
      After env slots liveIn live base heap store s t target v heap2 store2 s2 ws2 →
      heap2.top.toNat ≤ heap1.top.toNat + coerceCost t source target v →
      (source = .owned → store2 = store1 ∧ ws2 = ws) →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ vs } host) :
    wp m (coerceCode h t source target base' ++ rest) Q store1
      { s1 with values := ws.reverse ++ vs } host :=
  After.coerceX (strict := false) (copyCodeX hm) a nofun hTarget hBase' hLow hh hRoom hCap hTrap
    (fun heap2 store2 s2 ws2 a1 a2 a3 _ => hNext heap2 store2 s2 ws2 a1 a2 a3)

/-- A pair: the code of each component, each followed by its coercion to the pair's mode. -/
theorem spec_pair (hm : Runtime m) {Γ' : List Ty} {sTy tTy : Ty} {first : Expr S Γ' sTy}
    {second : Expr S Γ' tTy}
    (firstSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv first env
        slots paid live)
    (secondSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv second env
        slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.pair first second) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_pair (strict := false) (copyCodeX hm)
      (fun env slots paid live => CodeSpecX.false_iff.mpr (firstSpec env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (secondSpec env slots paid live)) env
      slots paid live)

/-- A read of an array variable: the position in local `base`, a comparison of it with the
array's size as a flag in local `base + 1`, the position of the element's first word in local
`base`, the loads of its words under the flag, and the release of the variable when it is owned and
dies there. -/
theorem spec_get (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv i env slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.get x i) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_get (strict := false)
      (readReleaseX (strict := false) hm nofun) x
      (fun env slots paid live => CodeSpecX.false_iff.mpr (iSpec env slots paid live)) env slots
      paid live)

/-- The code of a call's arguments pushes words that represent their values in the modes
`modes`, in order.  An argument without arrays runs its code with the variables `all` live after
it, so that no argument consumes a variable.  A borrowed argument with arrays, a place, loads its
variables' words.  An owned argument, a variable, loads its words when it is owned and not in
`kept`, which moves it into the call, and is copied otherwise.  The copies are the fresh blocks
`F` of the arguments' step.  The owned arguments' blocks lie apart from one another and from the
borrowed arguments' arrays, and a region apart from `F` and from the blocks of the moved
variables lies apart from the owned arguments' blocks.  A region apart from the variables that
the arguments with arrays read lies apart from the borrowed arguments' arrays. -/
theorem args_spec (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {paid : List Bool} {all kept : Nat → Bool} {h base : Nat} {d a : Bool} :
    {ps : List Ty} → (modes : Nat → Mode) →
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) →
    (∀ i env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (args i) env slots paid live) →
    (∀ i k, (args i).uses k = true → all k = true) → (∀ k, kept k = true → all k = true) →
    (∀ i : Fin ps.length, modes i = .owned → (ps.get i).scalar = false) →
    (∀ i, (ps.get i).scalar = false → modes i = .borrowed → (args i).isPlace = true) →
    (∀ i : Fin ps.length, modes i = .owned → ∃ x : Var Γ (ps.get i), args i = .var x ∧
      (kept x.index = false → (slots.getD x.index default).mode = .owned ∧
        ∀ j : Fin ps.length, j ≠ i → (ps.get j).scalar = false →
          (args j).uses x.index = false)) →
    (∀ i, (args i).placeArgs = true) →
    (∀ i, (!(args i).fits funs fits env) = true → d = true) →
    (∀ i, ((args i).aborts || modes i == .owned || slots.any (·.mode == .owned)) = true →
      a = true) →
    ∀ (heap : Heap) (store : Store Unit) (s : Locals), s.positions = h → s.params = pv →
    Holds env slots all base heap store s → heap.At store →
    pool.Safe env slots all heap store s → store.memoryCap m 0 ≤ 65535 →
    s.params.length ≤ base →
    (∀ i : Fin ps.length,
      base + (if modes i = .owned then copyWidth (ps.get i) else (args i).width) ≤ h) →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (d || (a && !decide (heap.Within store m
      (argsSum (argCost funs flags bounds (slots.map Slot.mode) paid all kept modes args env))))) Q →
    (∀ heap' store' s' ws F, Step heap store (fun _ => True) heap' store' F →
      Frame base s s' → Holds env slots all base heap' store' s' →
      Env.Rep modes heap' store' ws (Env.ofFn fun i => (args i).denote funs env) →
      Separate store' (Env.moves store' modes ws (Env.ofFn fun i => (args i).denote funs env))
        (Env.reads store' modes ws (Env.ofFn fun i => (args i).denote funs env)) →
      (∀ r, (∀ b ∈ F, regionsDisjoint r b) →
        Holds.KeepDying env slots
          (fun k => argsAny fun i => modes i == .owned && (args i).uses k && !kept k)
          (fun _ => false) store s r →
        Apart store' (Env.moves store' modes ws (Env.ofFn fun i => (args i).denote funs env)) r) →
      (∀ r, Holds.ApartFrom env slots
          (fun k => argsAny fun i =>
            modes i == .borrowed && !(ps.get i).scalar && (args i).uses k) store s r →
        ∀ c ∈ Env.reads store' modes ws (Env.ofFn fun i => (args i).denote funs env),
          regionsDisjoint r c) →
      (d = false → heap'.top.toNat ≤ heap.top.toNat +
        argsSum (argCost funs flags bounds (slots.map Slot.mode) paid all kept modes args env)) →
      (∀ sel : Nat → Bool, (∀ i, sel i = true → modes i = .owned) →
        Env.argPot store' sel ws (Env.ofFn fun i => (args i).denote funs env) ≤
          argsSum fun i =>
            if sel i = true then (args i).paramPot funs store' s env slots paid kept else 0) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (argsCode (fun i => if (ps.get i).scalar then (args i).code (pool := pool) h slots base all
      else if modes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots) ++ rest) Q store s host :=
  fun {_} modes args hSpec hUses hKept hArray hPlace hOwned hPlaceArgs hdA haA heap store s hh
      hpv hVars hAt hSafe hCap hBase hRoom rest Q hTrap hNext =>
    args_specX (strict := false) (copyCodeX hm) modes args
      (fun i env slots paid live => CodeSpecX.false_iff.mpr (hSpec i env slots paid live)) hUses
      hKept hArray hPlace hOwned hPlaceArgs hdA haA heap store s hh hpv hVars hAt nofun hSafe hCap
      hBase hRoom rest Q hTrap
      fun heap' store' s' ws F hs hf hv hr _ hsep hk ha hd hp =>
        hNext heap' store' s' ws F hs hf hv hr hsep hk ha hd hp

theorem spec_fold (hm : Runtime m) {Γ' : List Ty} {e : Elem} {t : Ty}
    (x : Var Γ' (.array e)) {init : Expr S Γ' t}
    {body : Expr S (.elem e :: t :: .word :: Γ') t}
    (initSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv init env
      slots paid live)
    (bodySpec : ∀ buy env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits
      host pv body env slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.fold x init body)
      env slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_fold (strict := false) hm nofun (copyCodeX hm) x
      (fun env slots paid live => CodeSpecX.false_iff.mpr (initSpec env slots paid live))
      (fun buy env slots paid live => CodeSpecInX.false_iff.mpr (bodySpec buy env slots paid live))
      env slots paid live)

/-- `LeanExe.eraseAt x i`: the position in local `base`, the array as owned in local `base + 1`,
its length in local `base + 2`, and, when the position is below the size, the element's first
word in local `base + 3`, the move of the words after the element down by its word count, and the
write of the shorter length. -/
theorem spec_eraseAt (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv i env slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.eraseAt x i) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_eraseAt (strict := false) (copyCodeX hm) x
      (fun env slots paid live => CodeSpecX.false_iff.mpr (iSpec env slots paid live)) env slots
      paid live)

/-- A loop: the bound of `spec_loop_with` at the state's flag, or, for a state of pair type that
is paid, at the flag whose bound is smaller. -/
theorem spec_loop (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word}
    {init : Expr S Γ' tTy} {cond : Expr S (tTy :: Γ') .bool}
    {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv count env
        slots paid live)
    (initSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv init env slots paid live)
    (condSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv cond env slots paid live)
    (bodySpec : ∀ buy env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host
        pv body env slots paid live) :
    ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.loop count init cond body) env slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_loop (strict := false) hm nofun (copyCodeX hm)
      (fun env slots paid live => CodeSpecX.false_iff.mpr (countSpec env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (initSpec env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (condSpec env slots paid live))
      (fun buy env slots paid live => CodeSpecInX.false_iff.mpr (bodySpec buy env slots paid live))
      env slots paid live)

/-- `x.set! i.toNat v`: the position in local `base`, the value's words from local `base + 1` on,
the array as owned in local `base + 1 + k`, which is `x`'s own block when `x` is owned and dies,
and, when the position is below the size, the position of the element's first word in local
`base + 2 + k` and the writes of the element's words. -/
theorem spec_set (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word} {v : Expr S Γ' (.elem e)}
    (iSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv i env slots paid live)
    (vSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv v env slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.set x i v) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_set (strict := false) (copyCodeX hm) x
      (fun env slots paid live => CodeSpecX.false_iff.mpr (iSpec env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (vSpec env slots paid live)) env slots
      paid live)

theorem spec_leSize (hm : Runtime m) {Γ' : List Ty} {e : Elem}
    (x : Var Γ' (.array e)) (i : Var Γ' .word) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv
      (Expr.leSize (S := S) x i) env slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_leSize (strict := false) hm
      (readReleaseX (strict := false) hm nofun) (copyCodeX hm)
      x i env slots paid live)

/-- An `if`: the condition, then each branch as `ite_branch` describes. -/
theorem spec_ite (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE : Expr S Γ' tTy} {buy : Bool}
    (cSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv c env slots paid live)
    (thenSpec : ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        thenE env slots paid live)
    (elseSpec : ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        elseE env slots paid live) :
    ∀ env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv
        (Expr.ite c thenE elseE) env slots paid live :=
  fun env slots paid live =>
    CodeSpecInX.false_iff.mp (specX_ite (strict := false) hm nofun (copyCodeX hm)
      (fun env slots paid live => CodeSpecX.false_iff.mpr (cSpec env slots paid live))
      (fun env slots paid live => CodeSpecInX.false_iff.mpr (thenSpec env slots paid live))
      (fun env slots paid live => CodeSpecInX.false_iff.mpr (elseSpec env slots paid live)) env
      slots paid live)

theorem spec_bytesSize (hm : Runtime m) {Γ' : List Ty} (x : Var Γ' .bytes) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.bytesSize (S := S) x)
      env slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_bytesSize (strict := false)
      (readReleaseX (strict := false) hm nofun) x env slots
      paid live)

/-- A variable: read in place when borrowed, moved where it dies, and copied where it stays
live. -/
theorem spec_var (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.var (S := S) x) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_var (strict := false) (copyCodeX hm) x env slots paid live)

/-- One branch of an `if`, after the condition: the releases of the owned variables that die at
its entry, its code, the coercion of its value to the `if`'s mode, and the store of its words,
which the code loads after the `if`. -/
theorem ite_branch (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {c : Expr S Γ' .bool}
    {thenE elseE b : Expr S Γ' tTy} {buy : Bool}
    (bSpec : ∀ env slots paid live,
      CodeSpecIn (pool := pool) buy m funs flags bounds fits host pv b env slots paid live)
    {env : Env Γ'} {slots : List Slot} {paid : List Bool} {live : Nat → Bool} {h base : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) base heap
      store s)
    (hSafe : pool.Safe env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomB : base + tTy.width + max b.width (copyWidth tTy) ≤ h)
    {B cA Db K : Nat} {wf P : Bool}
    (hTrap : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B wf) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || (Expr.ite c thenE elseE).uses i) live base heap store s
        tTy ((Expr.ite c thenE elseE).mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).denote funs env) heap' store' s' ws →
      (wf = true → heap'.top.toNat +
          (if P = true then tTy.pot store' ws ((Expr.ite c thenE elseE).denote funs env) else 0) ≤
        heap.top.toNat + B) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host)
    {heap1 : Heap} {store1 : Store Unit} {s1 : Locals}
    (e1 : Evolves env slots (fun i => live i || (Expr.ite c thenE elseE).uses i)
      (fun i => live i || thenE.uses i || elseE.uses i) base heap store s heap1 store1
      { s1 with values := s.values })
    (hTop1 : wf = true → heap1.top.toNat ≤ heap.top.toNat + cA)
    (hB : B = cA + (Db + (b.allocs funs flags bounds (slots.map Slot.mode) paid live env +
      coerceCost tTy (b.mode (slots.map Slot.mode))
        ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (b.denote funs env) +
      (b.buysIn buy funs flags (slots.map Slot.mode) paid live env + K))))
    (hDb : dyingPot store s env slots paid (fun i => live i || b.uses i) live ≤ Db)
    (hbd : wf = true → b.fits funs fits env = true)
    (hbPlace : b.placeArgs = true)
    (hbu : ∀ i, b.uses i = true → (thenE.uses i || elseE.uses i) = true)
    (hba : b.aborts = true → (Expr.ite c thenE elseE).aborts = true)
    (hval : b.denote funs env = (Expr.ite c thenE elseE).denote funs env)
    (hbm : b.mode (slots.map Slot.mode) = .owned →
      (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned)
    (hPm : P = true → (Expr.ite c thenE elseE).mode (slots.map Slot.mode) = .owned)
    (hK : P = true → b.paidIn buy flags (slots.map Slot.mode) paid live = false →
      tTy.credit (b.denote funs env) ≤ K)
    (Qb : Assertion Unit) (hQbTrap : ∀ st, Q (.Trap st "unreachable") → Qb (.Trap st "unreachable"))
    (hQb : ∀ st' s', wp m (loadCode h base tTy.types ++ rest) Q st'
      { s' with values := s.values } host → Qb (.Fallthrough st' s')) :
    wp m (releaseWhere Γ' slots (fun i => (live i || thenE.uses i || elseE.uses i) &&
        !(live i || b.uses i)) ++
      (b.code (pool := pool) h slots (base + tTy.width) live ++
        (coerceCode h tTy (b.mode (slots.map Slot.mode))
          ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (base + tTy.width) ++
          storeCode h base tTy.types))) Qb store1 { s1 with values := s.values } host := by
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  have hTrapB : TrapOK (trapFlag m (Expr.ite c thenE elseE) slots heap store B wf) Qb :=
    hTrap.imp hQbTrap
  have hwf : (!wf) = false → wf = true := fun hd => by simpa using hd
  have hbd' : (!wf) = false → b.fits funs fits env = true := fun hd => hbd (hwf hd)
  have hSubMid : ∀ i, (live i || b.uses i) = true →
      (live i || thenE.uses i || elseE.uses i) = true := fun i =>
    ite_live_branch _ _ _ _ (hbu i)
  refine wp_releaseWhere hm e1.holds e1.step.at_
    (fun i h => by simp only [Bool.and_eq_true] at h; exact h.1) fun heap2 store2 e2 hTop2 => ?_
  have hEq : (fun i => (live i || thenE.uses i || elseE.uses i) &&
      !((live i || thenE.uses i || elseE.uses i) && !(live i || b.uses i))) =
      (fun i => live i || b.uses i) := by
    funext i
    exact live_released _ _ (hSubMid i)
  rw [hEq] at e2
  have hEntry : ∀ i, (live i || thenE.uses i || elseE.uses i) = true →
      (live i || (Expr.ite c thenE elseE).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact ite_live_entry _ _ _ _ h
  -- The variables that die in the branch keep their potential across the condition and the
  -- releases.
  have hDb2 : dyingPot store2 { s1 with values := s.values } env slots paid
      (fun i => live i || b.uses i) live =
        dyingPot store s env slots paid (fun i => live i || b.uses i) live := by
    rw [dyingPot_evolves e1.holds e2 hSubMid _ _ fun _ h => h,
      dyingPot_evolves hVars e1 hEntry _ _ hSubMid]
  rw [← List.append_nil (storeCode h base tTy.types)]
  have hbw := Nat.le_max_left b.width (copyWidth tTy)
  have hcw := Nat.le_max_right b.width (copyWidth tTy)
  refine bSpec env slots paid live h (base + tTy.width) heap2 store2 { s1 with values := s.values }
    hh1 (hp1.trans hpv) (e2.holds.mono (by omega)) e2.step.at_
    ((hSafe.evolves hVars e1 hEntry).evolves e1.holds e2 hSubMid)
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base + tTy.width; rw [hp1]; omega)
    (by omega) hbPlace _ _ (hTrapB.part (fun h => by
          cases hw : wf
          · rfl
          · simp [hbd hw] at h) (fun h => by
          simp only [Bool.or_eq_true] at h ⊢; exact h.imp_left hba) fun hd hw => by
        rw [hB] at hw
        exact (hw.after (heap1 := heap2) (store1 := store2)
          (by have := hTop1 (hwf hd); have := congrArg UInt64.toNat hTop2; omega)
          (by rw [e2.step.cap m, e1.step.cap m])).mono (by rw [hDb2]; omega))
    fun heap3 store3 s3 ws3 a3 hTop3 => ?_
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hh3 : s3.positions = h := a3.frame.positions.trans hh1
  refine After.coerce hm a3 hbm le_rfl (by rw [hp3]; omega) hh3 (by omega)
    (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m]; exact hCap)
    (fun hs ht _ => hTrapB.alloc (by
      have := (Expr.ite c thenE elseE).mode_owned (slots.map Slot.mode) ht
      rw [Slot.any_map] at this; exact this) fun hd hw => by
        have h3 := hw.shift (heap1 := heap3) (store1 := store3)
          (c1 := cA + Db + b.allocs funs flags bounds (slots.map Slot.mode) paid live env +
            b.buysIn buy funs flags (slots.map Slot.mode) paid live env)
          (c2 := coerceCost tTy (b.mode (slots.map Slot.mode))
            ((Expr.ite c thenE elseE).mode (slots.map Slot.mode)) (b.denote funs env))
          (by have := hTop3 (hbd' hd); have := hTop1 (hwf hd); have := congrArg UInt64.toNat hTop2
              omega)
          (by rw [hB]; omega)
          (by rw [a3.step.cap m, e2.step.cap m, e1.step.cap m])
        simpa [coerceCost, hs, ht] using h3)
    fun heap4 store4 s4 ws4 a4 hTop4 hSame4 => ?_
  have hp4 : s4.params = s.params := a4.frame.params.trans hp1
  have hh4 : s4.positions = h := a4.frame.positions.trans hh1
  refine wp_storeCode ws4 h base tTy.types s4 s.values a4.rep.typed hh4 (by rw [hp4]; omega)
    (by rw [Ty.types_length, hh4]; omega) fun s5 hF5 hold _ => ?_
  rw [wp_nil]
  refine hQb _ _ (wp_loadCode ws4 a4.rep.typed (hF5.positions.trans hh4) hold ?_)
  -- The `if`'s facts: the evolutions of the condition and the releases, then the branch.
  have hLower := a4.lower e2.holds (Nat.le_add_right _ _) (fun i h => by simp [h])
  have e12 := Evolves.trans hVars e1 e2 hSubMid hEntry
  have aAll := After.prepend hVars e12 hLower (fun i h => hEntry i (hSubMid i h))
    (fun i h => by simp [h])
  have hF45 : Frame base s4 { s5 with values := s.values } := hF5.trans Frame.ofValues
  have hFrame : Frame base s { s5 with values := s.values } := aAll.frame.trans hF45
  rw [hval] at aAll
  refine hNext heap4 store4 _ ws4 ⟨aAll.step, hFrame, aAll.holds.agree hF45, aAll.rep, ?_⟩
    fun hd => by
      have := hTop1 hd; have := hTop3 (hbd hd); have := congrArg UInt64.toNat hTop2
      -- A paid branch keeps its owned value through the coercion.  The charge `K` of an unpaid
      -- branch of a paid `if` bounds the potential of the owned result.
      have hPot : (if P = true then
            tTy.pot store4 ws4 ((Expr.ite c thenE elseE).denote funs env) else 0) ≤
          (if b.paidIn buy flags (slots.map Slot.mode) paid live = true then
            tTy.pot store3 ws3 (b.denote funs env) else 0) + K := by
        by_cases hP : P = true
        · by_cases hbP : b.paidIn buy flags (slots.map Slot.mode) paid live = true
          · obtain ⟨rfl, rfl⟩ := hSame4 (Expr.mode_of_paidIn b hbP)
            rw [ite_eq_left hP, ite_eq_left hbP, ← hval]
            omega
          · have hRep4 := a4.rep
            rw [hPm hP] at hRep4
            have hle := Ty.pot_le_credit tTy ws4 _ hRep4
            have hk := hK hP (by simpa using hbP)
            rw [ite_eq_left hP, ite_eq_right hbP, ← hval]
            omega
        · rw [ite_eq_right hP]
          omega
      rw [hB]; omega
  exact aAll.apart.agree aAll.holds hF45

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
theorem spec_loop_with (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} {count : Expr S Γ' .word}
    {init : Expr S Γ' tTy} {cond : Expr S (tTy :: Γ') .bool}
    {body : Expr S (tTy :: .word :: Γ') tTy}
    (countSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv count env
        slots paid live)
    (initSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv init env slots paid live)
    (condSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv cond env slots paid live)
    (bodySpec : ∀ buy env slots paid live, CodeSpecIn (pool := pool) buy m funs flags bounds fits host
        pv body env slots paid live) :
    ∀ env slots paid live (ps : Bool),
      (ps = true → Expr.statePaid flags (slots.map Slot.mode) paid live init cond body = true) →
      ((Expr.loop count init cond body).paid flags (slots.map Slot.mode) paid live = true →
        ps = true) →
      CodeSpecWith (pool := pool)
        ((Expr.loop count init cond body).paid flags (slots.map Slot.mode) paid live)
        (Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body
          env)
        m funs flags bounds fits host pv (Expr.loop count init cond body) env slots paid live := by
  intro env slots paid live ps hpsS hlpS h base heap store s hh hpv hVars hAt hSafe hCap hBase
      hRoom hPlace rest Q hTrap hNext
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
  have hdl : (Expr.loop count init cond body).fits funs fits env = true →
      count.fits funs fits env = true ∧ init.fits funs fits env = true ∧
        Expr.loopFitsRest funs fits cond body env (count.denote funs env).toNat 0 (init.denote funs env) = true :=
    fun hd => by
      simp only [Expr.fits, Bool.and_eq_true] at hd
      exact ⟨hd.1.1, hd.1.2, hd.2⟩
  have hT := Expr.loopBound_def ps funs flags bounds (slots.map Slot.mode) paid live count init cond
    body env
  simp only [Expr.code, loopCode, Expr.usesFast_eq, List.append_assoc, List.cons_append,
    List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
      count.uses i) = true → (live i || (Expr.loop count init cond body).uses i) = true :=
    fun i h => by simp only [Expr.uses]; exact loop_live_count _ _ _ _ _ h
  -- The variables that die in the count and in the initial state.  The others that die in the
  -- loop are released after it, and their potential is dropped.
  have hDw : dyingPot store s env slots paid
        (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
          count.uses i) (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) +
      dyingPot store s env slots paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) ≤
      dyingPot store s env slots paid (fun i => live i || (Expr.loop count init cond body).uses i)
        live := by
    rw [dyingPot_split _ (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      _ (fun i h => hCountIn i (by simp [h])) (fun i h => by simp [h]),
      dyingPot_split (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) live (fun i h => by simp [h])
      (fun i h => by simp [h])]
    rw [dyingPot_congr (L0 := fun i => live i || (Expr.loop count init cond body).uses i)
      (L0' := fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
        count.uses i) (fun i => by
          simp only [Expr.uses]
          cases live i <;> cases count.uses i <;> cases init.uses i <;>
            cases cond.uses (i + 1) <;> cases body.uses (i + 2) <;> rfl) fun _ => rfl]
    omega
  refine countSpec env slots paid _ h base heap
    store s hh hpv (hVars.live_mono hCountIn) hAt (hSafe.mono hCountIn) hCap hBase (by omega) hPc _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun h => by simp only [Expr.aborts]; exact loop_trap_count _ _ _ _ _ h)
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hTopK => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hHigh1 : base < s1.positions := by rw [hh1]; omega
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
  have hDi : dyingPot store1
      (setLocal { s1 with values := s.values } base (.i64 (count.denote funs env))) env slots paid
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) =
    dyingPot store s env slots paid
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i)
      (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) :=
    dyingPot_evolves (hVars.live_mono hCountIn) e1' (fun i h => by simp [h]) _ _ fun _ h => h
  refine initSpec env slots paid _ h
    (base + 1) heap1 store1 _ (hF2.positions.trans hh) (hF2.params.trans hpv)
    (e1'.holds.mono (Nat.le_succ base))
    e1'.step.at_
    ((hSafe.mono hCountIn).evolves (hVars.live_mono hCountIn) e1' (fun i hi => by simp [hi]))
    (by rw [e1'.step.cap m]; exact hCap) (by rw [hF2.params]; omega) (by omega) hPi
    _ _ (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun h => by simp only [Expr.aborts]; exact loop_trap_init _ _ _ _ _ h)
      fun hd hw => by
        have := hTopK (hdl (fits_of_not hd)).1
        rw [hDi]
        exact hw.shift (heap1 := heap1) (store1 := store1)
          (c1 := dyingPot store s env slots paid
            (fun i => (live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) ||
              count.uses i)
            (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) +
            count.allocs funs flags bounds (slots.map Slot.mode) paid
              (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) env)
          (by omega) (by rw [hT]; omega) (e1'.step.cap m))
    fun heap2 storeV _ wsV aV hTopI => ?_
  have hTop2 : (Expr.loop count init cond body).fits funs fits env = true →
      heap2.top.toNat ≤ heap.top.toNat +
        (dyingPot store s env slots paid
            (fun i => live i || (Expr.loop count init cond body).uses i)
          live +
        (count.allocs funs flags bounds (slots.map Slot.mode) paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2) || init.uses i) env +
        init.allocs funs flags bounds (slots.map Slot.mode) paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) env)) := fun hd => by
    have := hTopK (hdl hd).1; have := hTopI (hdl hd).2.1; rw [hDi] at this; omega
  refine After.coerce hm aV (fun h => by simp [Mode.join, h]) le_rfl
    (by rw [aV.frame.params, hF2.params]; omega) (aV.frame.positions.trans (hF2.positions.trans hh))
    (by omega) (by rw [aV.step.cap m, e1'.step.cap m]; exact hCap)
    (fun hs ht _ => hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy (init.mode (slots.map Slot.mode))
          ((init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
          (init.denote funs env) = tTy.copyCost (init.denote funs env) := by
        rw [coerceCost, if_pos ⟨hs, ht⟩]
      exact hw.shift (hTop2 (fits_of_not hd)) (by rw [hT]; omega)
        (by rw [aV.step.cap m, e1'.step.cap m]))
    fun heap2' store2 s3 ws0 a2 hTopCo hSame0 => ?_
  -- The first state's potential: a paid initial value's, which the coercion keeps, or the credit.
  have hTopEntry : (Expr.loop count init cond body).fits funs fits env = true →
      heap2'.top.toNat +
          (if ps = true then
            tTy.pot store2 ws0 (init.denote funs env) else 0) +
          Expr.loopRest funs flags bounds (slots.map Slot.mode) paid live ps init cond body env
            (count.denote funs env).toNat 0 (init.denote funs env) ≤
        heap.top.toNat +
          (dyingPot store s env slots paid
              (fun i => live i || (Expr.loop count init cond body).uses i)
            live +
          Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body env) := fun hd => by
    have hK := hTopK (hdl hd).1
    have hI := hTopI (hdl hd).2.1
    rw [hDi] at hI
    have hE := loop_entry_pot (ps := ps)
      (ip := init.paid flags (slots.map Slot.mode) paid
        (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)))
      (P0 := tTy.pot storeV wsV (init.denote funs env))
      (P1 := tTy.pot store2 ws0 (init.denote funs env)) (C := tTy.credit (init.denote funs env))
      (fun _ hip => by
        obtain ⟨rfl, rfl⟩ := hSame0 (Expr.mode_of_paid init hip)
        rfl)
      (fun hps _ => by
        have hr := a2.rep
        rw [Expr.statePaid_mode (hpsS hps)] at hr
        exact Ty.pot_le_credit tTy ws0 _ hr)
    rw [hT]
    omega
  have hF3 : Frame base s s3 := hF2.trans (a2.frame.mono (Nat.le_succ base))
  have hh3 : s3.positions = h := hF3.positions.trans hh
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
  have hh4 : s4.positions = h := hF4.positions.trans hh3
  have hLow4 : ({ s4 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s4.params.length ≤ base + 1; rw [hF4.params, hF3.params]; omega
  have hHigh4 : base + 1 < s4.positions := by rw [hh4]; omega
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
        by rw [Locals.get_setLocal_ne hLow4 (by omega)]; rfl,
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
      ((Expr.loop count init cond body).fits funs fits env = true →
        heapX.top.toNat +
            (if ps = true then
              tTy.pot stX wsX ((Expr.loop count init cond body).denote funs env) else 0) ≤
          heap.top.toNat +
          (dyingPot store s env slots paid
              (fun i => live i || (Expr.loop count init cond body).uses i)
            live +
          Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body env)) →
      wp m (releaseWhere Γ' slots (fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) ++
        (loadCode h (base + 2) tTy.types ++ rest)) Q stX { sX with values := vals } host := by
    intro heapX stX sX wsX vals hv holdX aX hTopX
    subst hv
    refine After.release hm (live := live)
      (sel := fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) hVars aX
      (fun i h => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; exact loop_sel _ _ _ h.1)
      (fun i h => by simp [h]) fun heap' store' a' hTopR hReg => ?_
    refine wp_loadCode wsX a'.rep.typed (aX.frame.positions.trans hh) holdX ?_
    refine hNext heap' store' sX wsX a' fun hd => ?_
    have h1 := hTopX hd
    have h2 := congrArg UInt64.toNat hTopR
    -- The loop's value has the last state's potential, which the release keeps.
    have hP : (if ps = true then
          tTy.pot store' wsX ((Expr.loop count init cond body).denote funs env) else 0) =
        (if ps = true then
          tTy.pot stX wsX ((Expr.loop count init cond body).denote funs env) else 0) := by
      split
      · next hps => rw [Ty.pot_of_regions (Expr.statePaid_mode (hpsS hps)) hReg]
      · rfl
    -- A paid loop has a paid state.
    have hLoopPaid : (if (Expr.loop count init cond body).paid flags (slots.map Slot.mode) paid live =
          true then tTy.pot store' wsX ((Expr.loop count init cond body).denote funs env) else 0) ≤
        (if ps = true then
          tTy.pot store' wsX ((Expr.loop count init cond body).denote funs env) else 0) := by
      split
      · next hlp =>
        rw [ite_eq_left (hlpS hlp)]
      · exact Nat.zero_le _
    rw [hP] at hLoopPaid
    omega
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
      ((Expr.loop count init cond body).fits funs fits env = true →
        Expr.loopFitsRest funs fits cond body env ((count.denote funs env).toNat - i.toNat) i
          (loopState (init.denote funs env)
            (fun i acc => bif cond.denote funs (.cons acc env) then
              body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) = true ∧
        heapI.top.toNat +
            (if ps = true then
              tTy.pot st wsI (loopState (init.denote funs env)
                (fun i acc => bif cond.denote funs (.cons acc env) then
                  body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) +
          Expr.loopRest funs flags bounds (slots.map Slot.mode) paid live ps init cond body env
          ((count.denote funs env).toNat - i.toNat) i
          (loopState (init.denote funs env)
            (fun i acc => bif cond.denote funs (.cons acc env) then
              body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) ≤
          heap.top.toNat +
            (dyingPot store s env slots paid
              (fun i => live i || (Expr.loop count init cond body).uses i) live +
            Expr.loopBound ps funs flags bounds (slots.map Slot.mode) paid live count init cond body env)))
    (fun _ s' => match s'.get (base + 1) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2', ws0, 0, UInt64.zero_le, hN5, hI5, hold5, a0.reframe hF5, fun hd =>
      ⟨by simpa only [UInt64.toNat_zero, Nat.sub_zero, loopState] using (hdl hd).2.2,
        by simpa only [UInt64.toNat_zero, Nat.sub_zero, loopState] using hTopEntry hd⟩⟩ ?_
  rintro st si ⟨heapI, wsI, i, hiN, hNi, hii, holdi, aI, hInv⟩
  simp only [wp_localGet_cons, Locals.get_values, hii, hNi, wp_geUI64_cons, wp_br_if_cons]
  by_cases hge : count.denote funs env ≤ i
  · -- The index reached the count.
    simp (config := { decide := true }) only [ge_iff_le, hge, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    have hieq := UInt64.le_antisymm hiN hge
    have hden : (Expr.loop count init cond body).denote funs env =
        loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat := by
      rw [hieq, loopState_eq]; rfl
    rw [hieq, loopState_eq] at aI
    refine hExit _ _ _ _ _ rfl holdi aI fun hd => ?_
    have := (hInv hd).2
    rw [hieq, Nat.sub_self, Expr.loopRest_zero] at this
    rw [hden, hieq]
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
  have hhi : si.positions = h := aI.frame.positions.trans hh
  -- The pass's frames, from the invariant.
  have hFitsI : (Expr.loop count init cond body).fits funs fits env = true →
      Expr.loopFitsRest funs fits cond body env ((count.denote funs env).toNat - i.toNat - 1 + 1) i
        (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) = true :=
    fun hd => by rw [← hk]; exact (hInv hd).1
  have hFitsC : (Expr.loop count init cond body).fits funs fits env = true → cond.fits funs fits (.cons (loopState (init.denote funs env)
      (fun i acc => bif cond.denote funs (.cons acc env) then
        body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env) = true :=
    fun hd => Expr.loopFitsRest_cond (hFitsI hd)
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
  have hSafeI := (hSafe.after hVars aI
    (fun j hj => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ hj)).1
  have hSafeC : pool.Safe
      (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
      (⟨base + 2, .borrowed⟩ :: slots)
      (fun j => (j == 0 ||
        shift 1 (fun k => live k || cond.uses (k + 1) || body.uses (k + 2)) j) || cond.uses j)
      heapI st si :=
    (hSafeI.mono fun j hj => cond_live_outer _ _ hdAll j hj).push
      holdi aI.rep.borrow (by simp only [Mode.fresh]; exact fun _ _ _ hMem => nomatch hMem)
  -- No variable dies in the condition: the outer ones it uses stay live, and the state is
  -- borrowed.
  have hDc : dyingPot st si (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) env)
      (⟨base + 2, .borrowed⟩ :: slots) (false :: paid)
      (fun j => (j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) ||
        cond.uses j)
      (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j) =
      0 :=
    dyingPot_eq_zero fun j h => cond_live _ _ hdAll j h
  refine condSpec _ (⟨base + 2, .borrowed⟩ :: slots) (false :: paid) _ h
    (base + 2 + tTy.width) heapI st si hhi (aI.frame.params.trans hpv) hVarsC aI.step.at_
    hSafeC
    (by rw [aI.step.cap m]; exact hCap)
    (by rw [aI.frame.params]; omega) (by omega) hPcd _ _
    ((hTrap.part (fun h => by
          cases hw : (Expr.loop count init cond body).fits funs fits env
          · rfl
          · exact absurd (hFitsC hw) (by simpa using h)) (fun h => by
      have h' : (cond.aborts || slots.any (·.mode == .owned)) = true := by
        simpa [List.any_cons] using h
      simp only [Expr.aborts]; exact loop_trap_cond _ _ _ _ _ h') fun hd hw => hw.of_le
        (by
          have := (hInv (fits_of_not hd)).2
          have := Expr.loopRest_cond_le (funs := funs) (flags := flags) (bounds := bounds)
            (modes := slots.map Slot.mode) (paid := paid) (live := live) (ps := ps) (init := init)
                (cond := cond)
            (body := body) (env := env) (n := (count.denote funs env).toNat - i.toNat - 1) (i := i)
            (x := loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
          rw [← hk] at this
          rw [hDc]
          simp only [List.map_cons]; omega)
        (aI.step.cap m)).imp fun _ h => h)
    fun heapC stC sC wsC aC hTopC => ?_
  have hRC := aC.rep
  simp only [Ty.rep_bool] at hRC
  subst hRC
  have aI2 := After.test aI aC (by omega) (cond_live _ _ hdAll) rfl
  -- The condition keeps the state's blocks, and so its potential.
  have hPotC : (if ps = true then
        tTy.pot stC wsI (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) =
      (if ps = true then
        tTy.pot st wsI (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) := by
    split
    · next hps =>
      rw [Ty.pot_of_regions (Expr.statePaid_mode (hpsS hps))
        (After.test_regions aI aC (cond_live _ _ hdAll))]
    · rfl
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
    have hden : (Expr.loop count init cond body).denote funs env =
        loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat := by
      rw [← hStop, loopState_eq]; rfl
    rw [← hStop, loopState_eq] at aI2
    refine hExit _ _ _ _ _ rfl holdC aI2 fun hd => ?_
    have h1 := (hInv hd).2
    rw [hk, Expr.loopRest_false hcv] at h1
    have h2 := hTopC (hFitsC hd)
    rw [hDc] at h2
    simp only [List.map_cons] at h2
    rw [hden, hPotC]
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
  have hhB : sB.positions = h := aB0.frame.positions.trans hh
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
  obtain ⟨hSafeB0, hFreshB0⟩ := hSafe.after hVars aB0
    (fun j hj => by simp only [Expr.uses]; exact loop_live_state _ _ _ _ _ hj)
  have hSafeIdx : pool.Safe (.cons (t := .word) i env) (⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j + 1 < 2) ||
        shift 2 (fun k => live k || cond.uses (k + 1) || body.uses (k + 2)) (j + 1) ||
          body.uses (j + 1)) heapC stC sB :=
    (hSafeB0.mono fun j hj => by simpa using hj).push
      holdIdx (show Ty.word.Rep .borrowed heapC stC [.i64 i] i from rfl)
      (by simp only [Mode.fresh]; exact fun _ _ _ hMem => nomatch hMem)
  have hSafeB : pool.Safe
      (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (fun j => decide (j < 2) ||
        shift 2 (fun k => live k || cond.uses (k + 1) || body.uses (k + 2)) j || body.uses j)
      heapC stC sB := hSafeIdx.push holdB aB0.rep hFreshB0
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
    have h1 := (hInv hd).2
    rw [hk, Expr.loopRest_true hcv] at h1
    exact h1
  have hTopC' := fun hd => by
    have h2 := hTopC (hFitsC hd)
    rw [hDc] at h2
    simp only [List.map_cons] at h2
    exact h2
  have hFitsB : (Expr.loop count init cond body).fits funs fits env = true →
      body.fits funs fits (.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
          body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env)) = true ∧
      Expr.loopFitsRest funs fits cond body env ((count.denote funs env).toNat - i.toNat - 1) (i + 1)
        (body.denote funs (.cons (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) = true :=
    fun hd => Expr.loopFitsRest_body (hFitsI hd) hcv
  refine wp_releaseVars hm _ (by split <;> simp) hVarsB aB0.step.at_ (by split <;> simp)
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
  -- The only paid variable that can die in the body is the state, when the body uses it.
  have hDbody : dyingPot store2 sB (Env.cons (loopState (init.denote funs env)
        (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat)
        (Env.cons (t := .word) i env))
      (⟨base + 2, (init.mode (slots.map Slot.mode)).join
        (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))⟩ ::
        ⟨base + 1, .borrowed⟩ :: slots)
      (ps :: false :: paid)
      (fun j => shift 2 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j ||
        body.uses j)
      (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) ≤
      (if ps = true then
        tTy.pot st wsI (loopState (init.denote funs env)
          (fun i acc => bif cond.denote funs (.cons acc env) then
            body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) else 0) := by
    rw [dyingPot_evolves hVarsB e2' (fun j h => live_right _ _ _ h) _ _ fun _ h => h, ← hPotC,
      ← holdB.read_eq (by rw [aB0.rep.length, Ty.types_length])]
    exact dyingPot_le_head _ _ _ _ _ loop_body_dies
  refine bodySpec (ps) _ _
    (ps :: false :: paid)
    (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) h
    (base + 2 + tTy.width) heap2 store2 sB hhB (aB0.frame.params.trans hpv) e2'.holds e2'.step.at_
    (hSafeB.evolves hVarsB e2' (fun j hj => live_right _ _ _ hj))
    (by rw [e2'.step.cap m, aB0.step.cap m]; exact hCap) (by rw [aB0.frame.params]; omega)
    (by omega) hPb _ _
    ((hTrap.part (fun h => by
          cases hw : (Expr.loop count init cond body).fits funs fits env
          · rfl
          · exact absurd (hFitsB hw).1 (by simpa using h)) (fun h => by
      have hmo := (Expr.loop count init cond body).mode_owned (slots.map Slot.mode)
      rw [Slot.any_map] at hmo
      simp only [List.any_cons, Expr.aborts] at h ⊢
      exact loop_trap_body _ _ _ _ _ _ _ (fun hv => hmo (beq_iff_eq.mp hv)) rfl h) fun hd hw =>
        hw.of_le (by
          have := hInv' (fits_of_not hd); have := hTopC' (fits_of_not hd)
          have := congrArg UInt64.toNat hTopRel
          have := hDbody
          simp only [List.map_cons, Expr.buysIn]; omega)
        (by rw [e2'.step.cap m, aB0.step.cap m])).imp
        fun _ h => h)
    fun heap6 _ s6b _ aBb hTopB => ?_
  have hp6 : s6b.params = s.params := aBb.frame.params.trans aB0.frame.params
  refine After.coerce hm aBb
    (fun h => loop_mode (f := fun md => body.mode (md :: .borrowed :: slots.map Slot.mode)) h)
    le_rfl (by rw [hp6]; omega) (aBb.frame.positions.trans hhB) (by omega)
    (by rw [aBb.step.cap m, e2'.step.cap m, aB0.step.cap m]; exact hCap)
    (fun hs ht _ => (hTrap.alloc (hOwnedA ht) fun hd hw => by
      have hcc : coerceCost tTy
          (body.mode (((init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode))) :: .borrowed ::
            slots.map Slot.mode))
          ((init.mode (slots.map Slot.mode)).join
            (body.mode (.borrowed :: .borrowed :: slots.map Slot.mode)))
          (body.denote funs (.cons (loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) =
          tTy.copyCost (body.denote funs (.cons (loopState (init.denote funs env)
              (fun i acc => bif cond.denote funs (.cons acc env) then
                body.denote funs (.cons acc (.cons i env)) else acc) i.toNat) (.cons i env))) := by
        rw [coerceCost, if_pos ⟨by simpa only [List.map_cons] using hs, ht⟩]
      exact hw.of_le (by
          have := hInv' (fits_of_not hd); have := hTopC' (fits_of_not hd)
          have := congrArg UInt64.toNat hTopRel
          have h6 := hTopB (hFitsB (fits_of_not hd)).1
          have := hDbody
          simp only [List.map_cons, Expr.buysIn] at h6
          omega)
        (by rw [aBb.step.cap m, e2'.step.cap m, aB0.step.cap m])).imp fun _ h => h)
    fun heap6' store6 s6 ws6 aB hTopCo2 hSame6 => ?_
  have hp6 : s6.params = s.params := aB.frame.params.trans aB0.frame.params
  have hh6 : s6.positions = h := aB.frame.positions.trans hhB
  refine wp_storeCode ws6 h (base + 2) tTy.types s6 si.values aB.rep.typed hh6
    (by rw [hp6]; omega) (by rw [Ty.types_length, hh6]; omega) fun s7 hF7 hold7 _ => ?_
  have hp7' : s7.params = s.params := hF7.params.trans hp6
  have hh7 : s7.positions = h := hF7.positions.trans hh6
  have hget7 : ∀ j < base + 2, s7.get j = sB.get j := fun j hj => by
    rw [(hF7.below j hj).1]
    exact (aB.frame.below j (by omega)).1
  -- The next index, in local `base + 1`.
  simp only [wp_localGet_cons, Locals.get_values, hget7 (base + 1) (by omega), hiiB,
    wp_constI64_cons, wp_addI64_cons]
  have hLow7 : ({ s7 with values := si.values } : Locals).params.length ≤ base + 1 := by
    show s7.params.length ≤ base + 1; rw [hp7']; omega
  have hHigh7 : base + 1 < s7.positions := by rw [hh7]; omega
  refine wp_localSet_local (s := s7) (vs := si.values) hLow7 (Locals.lt_total hHigh7) ?_
  have hget8 : (setLocal { s7 with values := si.values } (base + 1) (.i64 (i + 1))).get
      (base + 1) = some (.i64 (i + 1)) :=
    Locals.get_setLocal_same hLow7 (Locals.lt_total hHigh7)
  have hold8 : LocalsHold (setLocal { s7 with values := si.values } (base + 1)
      (.i64 (i + 1))) (base + 2) tTy.types ws6 :=
    hold7.keep (lo := base + 2) (by simp)
      (fun j hj _ => ⟨by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl,
        by rw [Locals.get_setLocal_ne hLow7 (by omega)]; rfl,
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
    refine ⟨(hFitsB hd).2, ?_⟩
    have := hInv' hd; have := hTopC' hd; have := congrArg UInt64.toNat hTopRel
    have h6 := hTopB (hFitsB hd).1
    simp only [List.map_cons] at h6 hTopCo2
    -- The body's value, which is paid when the state is, keeps its potential through the
    -- coercion, the identity on an owned value.
    simp only [Expr.buysIn] at h6
    have := loop_body_pot (Expr.statePaid_body_of hpsS)
      (fun hps => by
        obtain ⟨rfl, rfl⟩ := hSame6 (Expr.mode_of_paidIn body (Expr.statePaid_body_of hpsS hps))
        rfl)
      h6 hDbody hTopCo2
    omega
  · have := UInt64.lt_iff_toNat_lt.mp hlt
    simp only [hget8]
    omega

end Cases

end Verified
