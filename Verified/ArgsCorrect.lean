import Verified.ExprSpec
import Verified.VarCorrect

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value}

/-- The allowance of an allocation of a part, from that of the whole, which may allocate. -/
theorem _root_.Wasm.TrapOK.alloc {Q : Assertion Unit} {d a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (d || (a && !decide P)) Q) (ha : a = true)
    (hP : d = false → P → P') : TrapOK (!decide P') Q :=
  h.part (d' := false) (a' := true) nofun (fun _ => ha) hP

/-- A potential counted under `P` is at most one counted under `Q` when `P` implies `Q` and the two
agree under `P`. -/
theorem pot_keep {P Q : Bool} {a b : Nat} (hPQ : P = true → Q = true) (hab : P = true → a = b) :
    (if P = true then a else 0) ≤ (if Q = true then b else 0) := by
  cases P <;> cases Q <;> simp_all

/-- An allowance for a trap when `top` cannot rise by a charge gives the allowance of a part
that takes no call depth and whose room follows from the charge's. -/
theorem _root_.Wasm.TrapOK.narrow {Q : Assertion Unit} {a : Bool} {P P' : Prop} [Decidable P]
    [Decidable P'] (h : TrapOK (!decide P) Q) (hP : P → P') :
    TrapOK (false || (a && !decide P')) Q :=
  h.of_imp fun h' => by
    simp only [Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h' ⊢
    exact fun hp => h'.2 (hP hp)

/-- A variable in an owned position: its words as an owned value, which move it when it is owned
and dies, and a copy otherwise, which raises `top` by at most `x.ownedCost` and traps only when
`top` cannot rise by that much. -/
theorem spec_ownedVar (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.positions = h)
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
  refine spec_var (S := []) (funs := .nil) (flags := .nil) (bounds := .nil) (fits := .nil) hm x env
      slots [] live h
      base heap store s hh hpv hVars hAt
    hCap hBase (by simp only [Expr.width]; omega) rfl _ _
    (hTrap.narrow fun hw => hw.mono (by
      rw [dyingPot_nil]; simp only [Expr.allocs, Var.ownedCost]; omega))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hTop1' := hTop1 rfl
  simp only [Expr.allocs, Expr.paid, paidAt, List.getD_nil, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero, dyingPot_nil] at hTop1'
  rw [show (Expr.var (S := []) x).mode (slots.map Slot.mode) = (slots.getD x.index default).mode
    from Slot.modes_getD slots x.index] at a1
  exact After.coerce hm a1 (fun _ => rfl) le_rfl (by rw [a1.frame.params]; exact hBase)
    (a1.frame.positions.trans hh) (by omega) (by rw [a1.step.cap m]; exact hCap)
    (fun hs _ _ => hTrap.within fun hw => by
      have h2 := hw.after (heap1 := heap1) (store1 := store1)
        (c1 := x.cost (slots.map Slot.mode) live (env.get x))
        (c2 := coerceCost tTy (modeAt (slots.map Slot.mode) x.index) .owned (env.get x)) hTop1'
        (a1.step.cap m)
      simp only [coerceCost, hMode, hs, and_self, ↓reduceIte] at h2
      exact h2)
    fun heap2 store2 s2 ws2 a2 hTop2 _ => hNext heap2 store2 s2 ws2 a2 (by
      simp only [Expr.denote] at hTop2
      simp only [Var.ownedCost]; rw [hMode]; omega)

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
    (∀ i env slots paid live, CodeSpec m funs flags bounds fits host pv (args i) env slots paid live) →
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
    Holds env slots all base heap store s → heap.At store → store.memoryCap m 0 ≤ 65535 →
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
    wp m (argsCode (fun i => if (ps.get i).scalar then (args i).code h slots base all
      else if modes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots) ++ rest) Q store s host
  | [], _, _, _, _, _, _, _, _, _, _, _, heap, store, s, _, _, hVars, hAt, _, _, _, rest, Q, _,
      hNext => by
    simpa [argsCode, Env.ofFn, Env.Rep, Env.moves, Env.reads] using
      hNext heap store s [] [] (Step.refl hAt _) (Frame.refl base s) hVars rfl Separate.nil
        (fun _ _ _ => Apart.nil) (fun _ _ _ h => nomatch h) (fun _ => Nat.le_add_right _ _)
        fun _ _ => Nat.zero_le _
  | p :: ps, modes, args, argsSpec, hUses, hKept, hArray, hPlace, hOwned, hPlaceArgs, hdA, haA,
      heap, store, s, hh, hpv, hVars, hAt, hCap, hBase, hRoom, rest, Q, hTrap, hNext => by
    simp only [argsCode, List.append_assoc]
    have hSum : argsSum (argCost funs flags bounds (slots.map Slot.mode) paid all kept modes args env) =
        argCost funs flags bounds (slots.map Slot.mode) paid all kept modes args env ⟨0, by simp⟩ +
          argsSum (argCost funs flags bounds (slots.map Slot.mode) paid all kept (fun i => modes (i + 1))
            (fun i : Fin ps.length => args i.succ) env) := rfl
    have hd0 : d = false → (args ⟨0, by simp⟩).fits funs fits env = true := fun hd => by
      by_contra hc
      rw [hdA ⟨0, by simp⟩ (by simpa using hc)] at hd
      exact nomatch hd
    -- The other arguments, from the state after the first, and the facts of all of them.
    have hRest : ∀ heap1 store1 s1 ws0 F0,
        (d = false → heap1.top.toNat ≤ heap.top.toNat +
          argCost funs flags bounds (slots.map Slot.mode) paid all kept modes args env ⟨0, by simp⟩) →
        Step heap store (fun _ => True) heap1 store1 F0 → Frame base s s1 →
        Holds env slots all base heap1 store1 s1 →
        p.Rep (modes 0) heap1 store1 ws0 ((args ⟨0, by simp⟩).denote funs env) →
        (∀ r, (∀ b ∈ F0, regionsDisjoint r b) →
          Holds.KeepDying env slots
            (fun k => modes 0 == .owned && (args ⟨0, by simp⟩).uses k && !kept k)
            (fun _ => false) store s r →
          ∀ q ∈ (match modes 0 with | .owned => p.pointers store1 ws0 ((args ⟨0, by simp⟩).denote funs env) | .borrowed => []),
            regionsDisjoint r (block store1 q)) →
        (∀ q ∈ (match modes 0 with | .owned => p.pointers store1 ws0 ((args ⟨0, by simp⟩).denote funs env) | .borrowed => []),
          Holds.ApartFrom env slots (fun k => argsAny fun i : Fin ps.length =>
            !(ps.get i).scalar && (args i.succ).uses k) store1 s1 (block store1 q)) →
        (∀ r, Holds.ApartFrom env slots
            (fun k => modes 0 == .borrowed && !p.scalar && (args ⟨0, by simp⟩).uses k)
            store s r →
          ∀ c ∈ (match modes 0 with
            | .owned => []
            | .borrowed => p.reads store1 ws0 ((args ⟨0, by simp⟩).denote funs env)),
            regionsDisjoint r c) →
        (modes 0 = .owned → ∀ x : Var Γ ((p :: ps).get ⟨0, by simp⟩),
          args ⟨0, by simp⟩ = .var x → kept x.index = false →
          LocalsHold s (slots.getD x.index default).loc ((p :: ps).get ⟨0, by simp⟩).types ws0) →
        wp m (argsCode (fun i : Fin ps.length =>
            if ((p :: ps).get i.succ).scalar then (args i.succ).code h slots base all
            else if modes i.succ = .owned then (args i.succ).ownedCode h slots base kept
            else (args i.succ).placeCode h slots) ++ rest) Q store1
          { s1 with values := ws0.reverse ++ s.values } host := by
      intro heap1 store1 s1 ws0 F0 hTop0 hStep1 hF1 hH1 hR1 h5a h5c h6b hW0
      have hl0 := hR1.length
      have hAllUses : ∀ (i : Fin ps.length) k, (args i.succ).uses k = true → all k = true :=
        fun i => hUses i.succ
      refine args_spec hm (fun i => modes (i + 1)) (fun i => args i.succ)
        (fun i => argsSpec i.succ) hAllUses hKept (fun i => hArray i.succ)
        (fun i => hPlace i.succ) (fun i hmo => ?_) (fun i => hPlaceArgs i.succ)
        (fun i => hdA i.succ) (fun i => haA i.succ) heap1
        store1 { s1 with values := ws0.reverse ++ s.values } (hF1.positions.trans hh)
        (hF1.params.trans hpv) (hH1.agree Frame.ofValues) hStep1.at_ (by rw [hStep1.cap m]; exact
            hCap)
        (by show s1.params.length ≤ base; rw [hF1.params]; exact hBase)
        (fun i => hRoom i.succ) _ _
        (hTrap.part id id fun hd hw => hw.shift (heap1 := heap1) (store1 := store1)
          (hTop0 hd) (by rw [hSum]) (hStep1.cap m))
        fun heap2 store2 s2 ws2 F2 hStep2 hF2 hH2 hRep2 hSep2 hX2 hY2 hTop2 hPot2 => ?_
      · obtain ⟨x, hx, hk⟩ := hOwned i.succ hmo
        exact ⟨x, hx, fun h => ⟨(hk h).1, fun j hj hs => (hk h).2 j.succ
          (fun he => hj (Fin.succ_injective _ he)) hs⟩⟩
      -- The first argument's value and its regions in the final state.
      obtain ⟨hR0, hSame0, hFresh0⟩ := hR1.step hStep2 fun _ _ => trivial
      have hPointers (hm : modes 0 = .owned) :
          p.pointers store2 ws0 ((args ⟨0, by simp⟩).denote funs env) =
            p.pointers store1 ws0 ((args ⟨0, by simp⟩).denote funs env) := by
        have hOwned : p.Rep .owned heap1 store1 ws0 ((args ⟨0, by simp⟩).denote funs env) := by
          rw [← hm]; exact hR1
        exact hOwned.pointers_step hStep2 fun _ _ => trivial
      have hBlock : ∀ q ∈ (match modes 0 with | .owned => p.pointers store1 ws0 ((args ⟨0, by simp⟩).denote funs env) | .borrowed => []),
          block store2 q = block store1 q ∧ ∀ b ∈ F2, regionsDisjoint (block store1 q) b := by
        intro q hq
        cases hmd : modes 0 with
        | borrowed => rw [hmd] at hq; exact nomatch hq
        | owned =>
          rw [hmd] at hq hSame0 hFresh0
          simp only [Ty.regions, Ty.blocks_pointers] at hSame0 hFresh0
          rw [hPointers hmd] at hSame0
          exact ⟨List.map_inj_left.mp hSame0 q hq, hFresh0 _ (List.mem_map_of_mem hq)⟩
      have hMoves : Env.moves store2 modes (ws0 ++ ws2)
          (Env.ofFn fun i : Fin (p :: ps).length => (args i).denote funs env) =
          (match modes 0 with | .owned => p.pointers store1 ws0 ((args ⟨0, by simp⟩).denote funs env) | .borrowed => []) ++
            Env.moves store2 (fun i => modes (i + 1)) ws2
              (Env.ofFn fun i : Fin ps.length => (args i.succ).denote funs env) :=
        by
          simp only [Env.ofFn]
          rw [Env.moves_cons hl0]
          congr 1
          cases hm : modes 0
          · rfl
          · exact hPointers hm
      have hReads : Env.reads store2 modes (ws0 ++ ws2)
          (Env.ofFn fun i : Fin (p :: ps).length => (args i).denote funs env) =
          (match modes 0 with
            | .owned => []
            | .borrowed => p.reads store1 ws0 ((args ⟨0, by simp⟩).denote funs env)) ++
            Env.reads store2 (fun i => modes (i + 1)) ws2
              (Env.ofFn fun i : Fin ps.length => (args i.succ).denote funs env) :=
        by
          simp only [Env.ofFn]
          rw [Env.reads_cons hl0]
          congr 1
          cases hm : modes 0
          · simpa only [Ty.regions, hm] using hSame0
          · rfl
      -- A variable that a later owned argument moves is apart from the first argument's arrays.
      have hMovedRest : ∀ c ∈ (match modes 0 with
          | .owned => []
          | .borrowed => p.reads store1 ws0 ((args ⟨0, by simp⟩).denote funs env)),
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
        have := hNot0 hk'.1.2
        rw [hk'.2] at this
        exact nomatch this
      have e := hNext heap2 store2 s2 (ws0 ++ ws2) (F0 ++ F2)
        (hStep1.transBoth hStep2 fun _ _ => ⟨trivial, fun _ => trivial⟩)
        (hF1.trans hF2.values) (hH2.agree Frame.ofValues) ⟨ws0, ws2, rfl, hR0, hRep2⟩ ?_ ?_ ?_
        (fun hd => by have := hTop0 hd; have := hTop2 hd; rw [hSum]; omega) ?_
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
              rwa [Ty.blocks_pointers, hPointers hmd] at this
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
            have hApart : Holds.ApartFrom env slots
                (fun k => argsAny fun i : Fin ps.length =>
                  modes (i + 1) == .borrowed && !(ps.get i).scalar && (args i.succ).uses k)
                store1 s1 (block store1 q) := (h5c q hq).mono fun k hk => by
              obtain ⟨j, hj⟩ := argsAny_true.mp hk
              simp only [Bool.and_eq_true] at hj
              exact le_argsAny _ j (by simp only [Bool.and_eq_true]; exact ⟨hj.1.2, hj.2⟩)
            exact regionsDisjoint_symm (hY2 _ hApart c hc)
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
            modes j == .borrowed && !((p :: ps).get j).scalar && (args j).uses i)
              ⟨0, by simp⟩ h) c hc
        · refine hY2 r ((Holds.ApartFrom.iff hVars hStep1 hF1
            (fun k hk => ?_)).mpr (hr.mono fun i h => by
              obtain ⟨j, hj⟩ := argsAny_true.mp h
              exact le_argsAny (fun j : Fin (p :: ps).length =>
                modes j == .borrowed && !((p :: ps).get j).scalar && (args j).uses i)
                  j.succ hj)) c hc
          obtain ⟨j, hj⟩ := argsAny_true.mp hk
          simp only [Bool.and_eq_true] at hj
          exact hUses _ _ hj.2
      · -- The potential of the arguments at the picked parameters: the first's, from its words,
        -- and the others', whose slots the first argument's code keeps.
        intro sel hsel
        have h0 : (if sel 0 = true then
              ((p :: ps).get ⟨0, by simp⟩).pot store2 ws0 ((args ⟨0, by simp⟩).denote funs env)
              else 0) ≤
            (if sel 0 = true then
              (args ⟨0, by simp⟩).paramPot funs store2 s env slots paid kept else 0) := by
          split
          · next hs =>
            have hmo := hsel 0 hs
            obtain ⟨x, hx, -⟩ := hOwned ⟨0, by simp⟩ hmo
            have hR := hR0
            rw [hmo] at hR
            rw [hx] at hR ⊢
            simp only [Expr.paramPot]
            split
            · next hmp =>
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmp
              have hw := hW0 hmo x hx hmp.1
              rw [Env.potOf, hw.read_eq (by rw [hR.length, Ty.types_length]; rfl)]
              exact Nat.le_refl _
            · exact Ty.pot_le_credit _ _ _ hR
          · exact Nat.le_refl 0
        have hr := hPot2 (fun i => sel (i + 1)) fun i h => hsel (i + 1) h
        have hEq : (argsSum fun i : Fin ps.length => if sel (i + 1) = true then
              (args i.succ).paramPot funs store2 { s1 with values := ws0.reverse ++ s.values } env
                slots paid kept else 0) =
            argsSum fun i : Fin ps.length => if sel (i + 1) = true then
              (args i.succ).paramPot funs store2 s env slots paid kept else 0 := by
          congr 1
          funext i
          rw [Expr.paramPot_frame hVars (hF1.trans Frame.ofValues) _ (hUses i.succ)]
        rw [hEq] at hr
        have hl0' : ws0.length = ((p :: ps).get ⟨0, by simp⟩).width := hl0
        have hR : (argsSum fun i : Fin (p :: ps).length => if sel i = true then
              (args i).paramPot funs store2 s env slots paid kept else 0) =
            (if sel 0 = true then
              (args ⟨0, by simp⟩).paramPot funs store2 s env slots paid kept else 0) +
              argsSum fun i : Fin ps.length => if sel (i + 1) = true then
                (args i.succ).paramPot funs store2 s env slots paid kept else 0 := rfl
        rw [hR]
        show Env.argPot store2 sel (ws0 ++ ws2) (.cons ((args ⟨0, by simp⟩).denote funs env)
          (Env.ofFn fun i : Fin ps.length => (args i.succ).denote funs env)) ≤ _
        simp only [Env.argPot, List.take_left' hl0', List.drop_left' hl0']
        omega
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
      have hc0 : argCost funs flags bounds (slots.map Slot.mode) paid all kept modes args env
          ⟨0, by simp⟩ =
          (args ⟨0, by simp⟩).allocs funs flags bounds (slots.map Slot.mode) paid all env := by
        simp only [argCost]; rw [if_pos (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)]
      have hD0 : dyingPot store s env slots paid (fun k => all k || (args ⟨0, by simp⟩).uses k)
          all = 0 := dyingPot_eq_zero hSub
      refine argsSpec ⟨0, by simp⟩ env slots paid all h base heap store s hh hpv (hVars.live_mono
          hSub)
        hAt hCap hBase hRoom0 (hPlaceArgs _) _ _
        (hTrap.part (hdA _) (fun h => haA _ (by
            simp only [Bool.or_eq_true] at h ⊢; tauto))
          fun _ hw => hw.mono (by rw [hD0, hSum, hc0]; omega))
        fun heap1 store1 s1 ws1 a1 hTop1 => ?_
      have hStep := a1.step
      rw [Mode.fresh_scalar (show ((p :: ps).get ⟨0, by simp⟩).scalar = true from hp)] at hStep
      refine hRest heap1 store1 s1 ws1 [] (fun hd => by
          have := hTop1 (hd0 hd); rw [hD0] at this; rw [hc0]; omega)
        (hStep.mono (fun _ _ => (Holds.KeepDying.none).mono
          fun i h1 h2 => ⟨hSub i h1, h2⟩) fun _ h => h) a1.frame a1.holds
        (by rw [hmd]; exact a1.rep.borrow) (fun _ _ _ q hq => ?_) (fun q hq => ?_)
        (fun _ _ c hc => ?_) (fun hmo => by rw [hmd] at hmo; exact nomatch hmo)
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
            (fun r _ hr q hq => ?_) (fun q hq => ?_) (fun _ _ c hc => ?_)
            (fun _ x' hx' _ => by rw [hx] at hx'; cases hx'; exact hold))
          · rw [hmd, hv] at hq
            refine hr _ x (by simp only [hmd, hux, hkx]; rfl) rfl hmx ws hold hRep.length _ ?_
            rw [Ty.blocks_pointers]
            exact List.mem_map_of_mem hq
          · rw [hmd, hv] at hq
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
          have hc0 : argCost funs flags bounds (slots.map Slot.mode) paid all kept modes args env
              ⟨0, by simp⟩ =
              x.ownedCost (slots.map Slot.mode) all (env.get x) := by
            simp only [argCost]
            rw [if_neg (show ¬((p :: ps).get ⟨0, by simp⟩).scalar = true from hp),
              if_pos (show modes ↑(⟨0, by simp⟩ : Fin (p :: ps).length) = .owned from hmd), hx]
            simp only [Expr.ownedCost, Var.ownedCost, Var.cost, hkx, hAllX]
          refine spec_ownedVar hm x hh hpv (hVars.live_mono fun i h => by
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
            (fun _ _ c hc => ?_) (fun _ x' hx' hk' => by
              rw [hx] at hx'; cases hx'; rw [hkx] at hk'; exact nomatch hk')
          · rw [hmd, hv] at hq
            exact hr _ (by rw [Ty.blocks_pointers]; exact List.mem_map_of_mem hq)
          · rw [hmd, hv] at hq
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
              (fun r hr c hc => by
                rw [hmd] at hc
                exact hReads1 r (hr.mono fun k h => by
                  simp only [Bool.and_eq_true]
                  exact ⟨⟨by simp [hmd], by simpa using hp⟩, h⟩) c hc)
              fun hmo => by rw [hmd] at hmo; exact nomatch hmo

/-- The release of the owned variables that `sel` selects after an expression's code, those live
in `L1` and not in `live`, gives the facts of the code and the release for `live`.  The value lies
apart from the released blocks, so its words still represent it, and `top` is unchanged. -/
theorem After.release (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live sel : Nat → Bool} {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit}
    {s s1 : Locals} {t : Ty} {mode : Mode} {v : t.denote} {ws vals : List Value}
    {rest : Program} {Q : Assertion Unit}
    (h0 : Holds env slots L0 base heap store s)
    (a : After env slots L0 L1 base heap store s t mode v heap1 store1 s1 ws)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hSel : ∀ i, sel i = true → L1 i = true)
    (hLive : ∀ i, live i = true → (L1 i && !sel i) = true)
    (hNext : ∀ heap2 store2,
      After env slots L0 live base heap store s t mode v heap2 store2 s1 ws →
      heap2.top = heap1.top → t.regions mode store2 ws v = t.regions mode store1 ws v →
      wp m rest Q store2 { s1 with values := vals } host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store1 { s1 with values := vals } host := by
  refine wp_releaseWhere hm (a.holds.agree Frame.ofValues) a.step.at_ hSel
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
    e'.holds.agree Frame.ofValues, hRep, ?_⟩ hTop hSame
  · rw [Mode.fresh_congr hSame] at hb
    exact List.mem_append_left _ hb
  · exact Holds.Apart.transfer (a.holds.live_mono hLiveL1) (a.apart.live_mono hLiveL1) e'.step
      Frame.ofValues (fun u y hy wy hwy hly => a.holds.keepDying hLiveL1 hy hwy hly) hSame

end

/-- The mode of a parameter's slot is the parameter's mode. -/
theorem paramSlots_getD_mode (ps : List Ty) (ms : List Mode) (p0 i : Nat) :
    ((paramSlots ps ms p0).getD i default).mode = paramMode ps ms i := by
  rw [← Slot.modes_getD, paramSlots_modes]
  rfl

/-- The potential of a function's parameters, read from their slots, is that of its arguments'
words when each slot holds its parameter's words. -/
theorem Env.pot_paramSlots {store : Store Unit} {s : Locals} :
    {ps : List Ty} → (ms : List Mode) → (p0 : Nat) → (sel : Nat → Bool) → (ws : List Value) →
    (args : Env ps) → ws.length = widthSum ps →
    (∀ {t : Ty} (x : Var ps t),
      LocalsHold s (p0 + x.offset) t.types ((ws.drop x.offset).take t.width)) →
    args.pot store s (paramSlots ps ms p0) sel = Env.argPot store sel ws args
  | [], _, _, _, _, .nil, _, _ => rfl
  | t :: ts, ms, p0, sel, ws, .cons v rest, hl, hHold => by
    have hw := hHold (Var.here : Var (t :: ts) t)
    simp only [Var.offset, List.drop_zero, Nat.add_zero] at hw
    have hlt : (ws.take t.width).length = t.types.length := by
      simp only [List.length_take, Ty.types_length, widthSum, List.map_cons, List.sum_cons] at hl ⊢
      omega
    have hrest := Env.pot_paramSlots (store := store) (s := s) ms.tail (p0 + t.width)
      (fun i => sel (i + 1)) (ws.drop t.width) rest (by
        simp only [List.length_drop, widthSum, List.map_cons, List.sum_cons] at hl ⊢
        omega) fun x => by
      have := hHold (Var.there x)
      simp only [Var.offset] at this
      rw [show p0 + t.width + x.offset = p0 + (t.width + x.offset) by omega, List.drop_drop]
      exact this
    simp only [paramSlots, Env.pot, Env.argPot, List.getD_cons_zero, List.tail_cons]
    rw [hw.read_eq hlt, hrest]

end Verified
