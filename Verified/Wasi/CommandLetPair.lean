import Verified.AlignedCorrect
import Verified.Wasi.CommandBindValueSpec
import Verified.Wasi.CostBindValue

/-! The rules of `Command.letPair`, whose code is that of `Expr.letPair (.var pair)`: the pair's
code, which moves an owned pair that dies there and copies one that stays live, the stores of its
components from `base` on, the release of each owned component that the body does not use, and
the body's code.  `wp_letPair_head_with` runs the pair's code, `wp_letPair_tail_with` the stores
and the releases, and `After.letPair` joins the facts after the body to those of the binding. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem Relocation.programWith_loadCode (calls : List LeanExe.Wasi.Call) (h : Nat) :
    (loc : Nat) → (types : List ValueType) →
      Relocation.programWith calls (loadCode h loc types) = loadCode h loc types
  | _, [] => rfl
  | loc, _ :: types => by
    simp only [loadCode, Relocation.programWith_cons, Relocation.programWith_loadCode calls h
      (loc + 1) types]
    rfl

theorem letPairReleaseCode_eq (first second : Ty) (mode : Mode) (base : Nat)
    (firstUsed secondUsed : Bool) (context : List Ty) (slots : List Slot) :
    letPairReleaseCode first second mode base firstUsed secondUsed =
      ((if firstUsed = false then [1] else []) ++ (if secondUsed = false then [0] else [])).flatMap
        (releaseVar (second :: first :: context)
          (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots)) := by
  cases firstUsed <;> cases secondUsed <;> cases mode <;>
    simp [letPairReleaseCode, releaseVar]

/-- The release of the variables `indices`, relocated past the module's imports. -/
theorem wp_releaseVars_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {base : Nat}
    {source target : Module} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {heap : Heap} {initial : Store World} {locals : Locals}
    {rest : Program} {Q : Assertion World} (indices : List Nat) (distinct : indices.Nodup)
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (indices.flatMap (releaseVar context slots)))
    (closed : Relocation.programClosed source.funcs.length
      (indices.flatMap (releaseVar context slots)) = true)
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (selected : ∀ i ∈ indices, live i = true)
    (next : ∀ finalHeap final,
      Evolves env slots live (fun i => live i && !indices.contains i) base heap
        (PureTransport.erase initial) locals finalHeap (PureTransport.erase final) locals →
      finalHeap.top = heap.top → final.host = initial.host →
      wp target rest Q final locals targetHost) :
    wp target (Relocation.programWith calls (indices.flatMap (releaseVar context slots)) ++ rest)
      Q initial locals targetHost := by
  let P : Assertion Unit := fun continuation =>
    match continuation with
    | .Fallthrough final finalLocals =>
        ∃ finalHeap, Evolves env slots live (fun i => live i && !indices.contains i) base heap
          (PureTransport.erase initial) locals finalHeap final locals ∧
          finalLocals = locals ∧ finalHeap.top = heap.top
    | _ => False
  have pureCode : wp source (indices.flatMap (releaseVar context slots)) P
      (PureTransport.erase initial) locals sourceHost := by
    have execution := wp_releaseVars (host := sourceHost) runtime indices distinct vars at_
      selected (rest := []) (Q := P) (fun finalHeap final evolution top => by
        simp only [wp_nil, P]
        exact ⟨finalHeap, evolution, trivial, top⟩)
    simpa only [List.append_nil] using execution
  have transported := PureTransport.wp_prefix_with (calls := calls) layout profile form closed
    initial.host pureCode (rest := rest) (Q := Q) (targetHost := targetHost)
    (fun continuation post => by
      cases continuation with
      | Fallthrough final finalLocals =>
          obtain ⟨finalHeap, evolution, rfl, top⟩ := post
          apply next finalHeap (PureTransport.restore initial.host final)
          · simpa only [PureTransport.erase_restore] using evolution
          · exact top
          · rfl
      | _ => exact False.elim post)
  simpa only [PureTransport.restore_erase] using transported

/-- The code of the pair's variable, relocated past the module's imports: a copy of an owned pair
that stays live, and the pair's own words otherwise.  The continuation receives the facts that
`Expr.code` of the variable gives, that the regions of the words lie apart from the low memory,
and that the host's world stays the same. -/
theorem wp_letPair_head_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {S : List Sig} {context : List Ty} {first second : Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {pool : Bytes.LiteralPool} {pair : Var context (.pair first second)} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {params : List Value}
    {heap : Heap} {initial : Store World} {locals : Locals} {h base : Nat}
    {rest : Program} {Q : Assertion World}
    (layout : Relocation.LayoutWith calls source target) (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params (.var pair) env slots [] live
      pool)
    (form : Encoding.ProgramForm ((Expr.var (S := S) pair).code (pool := pool) h slots base live))
    (closed : Relocation.programClosed source.funcs.length
      ((Expr.var (S := S) pair).code (pool := pool) h slots base live) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || (Expr.var (S := S) pair).uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || (Expr.var (S := S) pair).uses i) heap
      (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots (fun i => live i || (Expr.var (S := S) pair).uses i)
      (PureTransport.erase initial) locals ABI.low)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + (Ty.pair first second).copyScratch ≤ h)
    (resource : (!decide (heap.Within (PureTransport.erase initial) source
        (pair.cost (slots.map Slot.mode) live (env.get pair)))) = true →
      ∀ final : Store World, final.host = initial.host → Q (.Trap final "unreachable"))
    (next : ∀ finalHeap finalStore finalLocals words,
      Verified.After env slots (fun i => live i || (Expr.var (S := S) pair).uses i) live base heap
        (PureTransport.erase initial) locals (.pair first second)
        ((Expr.var (S := S) pair).mode (slots.map Slot.mode)) (env.get pair)
        finalHeap (PureTransport.erase finalStore) finalLocals words →
      (∀ region ∈ (Ty.pair first second).regions
          ((Expr.var (S := S) pair).mode (slots.map Slot.mode))
          (PureTransport.erase finalStore) words (env.get pair),
        regionsDisjoint ABI.low region) →
      finalStore.host = initial.host →
      finalHeap.top.toNat ≤ heap.top.toNat + pair.cost (slots.map Slot.mode) live (env.get pair) →
      wp target rest Q finalStore { finalLocals with values := words.reverse ++ locals.values }
        targetHost) :
    wp target (Relocation.programWith calls
        ((Expr.var (S := S) pair).code (pool := pool) h slots base live) ++ rest)
      Q initial locals targetHost := by
  have mode : (Expr.var (S := S) pair).mode (slots.map Slot.mode) =
      (slots.getD pair.index default).mode := Slot.modes_getD slots pair.index
  have used : (fun i => live i || (Expr.var (S := S) pair).uses i) pair.index = true := by
    simp [Expr.uses]
  by_cases owned : (slots.getD pair.index default).mode = .owned
  · let P : Assertion Unit := fun continuation =>
      match continuation with
      | .Fallthrough finalStore resultLocals =>
          ∃ finalHeap finalLocals words,
            Verified.After env slots (fun i => live i || (Expr.var (S := S) pair).uses i) live base
              heap (PureTransport.erase initial) locals (.pair first second)
              ((Expr.var (S := S) pair).mode (slots.map Slot.mode)) (env.get pair)
              finalHeap finalStore finalLocals words ∧
            resultLocals = { finalLocals with values := words.reverse ++ locals.values } ∧
            finalHeap.top.toNat ≤ heap.top.toNat +
              pair.cost (slots.map Slot.mode) live (env.get pair)
      | .Trap _ message => (!decide (heap.Within (PureTransport.erase initial) source
          (pair.cost (slots.map Slot.mode) live (env.get pair)))) = true ∧
          message = "unreachable"
      | _ => False
    have pureCode : wp source ((Expr.var (S := S) pair).code (pool := pool) h slots base live) P
        (PureTransport.erase initial) locals sourceHost := by
      have failing : TrapOK (!decide (heap.Within (PureTransport.erase initial) source
          (pair.cost (slots.map Slot.mode) live (env.get pair)))) P := by
        cases failure : (!decide (heap.Within (PureTransport.erase initial) source
            (pair.cost (slots.map Slot.mode) live (env.get pair)))) with
        | false => trivial
        | true => exact fun _ => ⟨failure, rfl⟩
      have trap : TrapOK (trapFlag source (Expr.var (S := S) pair) slots heap
          (PureTransport.erase initial)
          (dyingPot (PureTransport.erase initial) locals env slots []
              (fun i => live i || (Expr.var (S := S) pair).uses i) live +
            (Expr.var (S := S) pair).allocs funs flags bounds (slots.map Slot.mode) [] live env)
          ((Expr.var (S := S) pair).fits funs fits env)) P :=
        TrapOK.of_imp failing (fun flag => by
          simp only [trapFlag, Expr.fits, Bool.not_true, Bool.false_or, dyingPot_nil,
            Nat.zero_add, Expr.allocs, Bool.and_eq_true] at flag
          exact flag.2)
      have execution := spec h base heap (PureTransport.erase initial) locals positions parameters
        vars at_ safe cap low (by simpa only [Expr.width] using room) rfl [] P trap
        (fun finalHeap finalStore finalLocals words after top => by
          simp only [wp_nil, P]
          refine ⟨finalHeap, finalLocals, words, after, rfl, ?_⟩
          have bound := top rfl
          simpa only [Expr.paid, paidAt, List.getD_nil, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte, Nat.add_zero, dyingPot_nil, Nat.zero_add, Expr.allocs] using bound)
      simpa only [List.append_nil] using execution
    have transported := PureTransport.wp_prefix_with (calls := calls) layout profile form closed
      initial.host pureCode (rest := rest) (Q := Q) (targetHost := targetHost)
      (fun continuation post => by
        cases continuation with
        | Fallthrough finalStore resultLocals =>
            obtain ⟨finalHeap, finalLocals, words, after, rfl, top⟩ := post
            change wp target rest Q (PureTransport.restore initial.host finalStore)
              { finalLocals with values := words.reverse ++ locals.values } targetHost
            have after' : Verified.After env slots
                (fun i => live i || (Expr.var (S := S) pair).uses i) live base heap
                (PureTransport.erase initial) locals (.pair first second)
                ((Expr.var (S := S) pair).mode (slots.map Slot.mode)) (env.get pair) finalHeap
                (PureTransport.erase (PureTransport.restore initial.host finalStore)) finalLocals
                words := by
              simpa only [PureTransport.erase_restore] using after
            refine next finalHeap _ finalLocals words after' ?_ rfl top
            have rep := after'.rep
            rw [mode, owned] at rep ⊢
            exact owned_low rep
        | Trap finalStore message =>
            obtain ⟨failure, rfl⟩ := post
            exact resource failure _ rfl
        | _ => exact False.elim post)
    simpa only [PureTransport.restore_erase] using transported
  · have borrowed : (slots.getD pair.index default).mode = .borrowed := by
      cases hMode : (slots.getD pair.index default).mode
      · rfl
      · exact absurd hMode owned
    obtain ⟨_, words, held, rep⟩ := vars.get pair used
    have width := rep.length
    have code : (Expr.var (S := S) pair).code (pool := pool) h slots base live =
        loadCode h (slots.getD pair.index default).loc (Ty.pair first second).types := by
      simp only [Expr.code, Var.code, owned, false_and, ↓reduceIte]
    rw [code, Relocation.programWith_loadCode]
    refine wp_loadCode words rep.typed positions held ?_
    have liveIn : ∀ i, live i = true → (live i || (Expr.var (S := S) pair).uses i) = true :=
      fun i hLive => by simp [hLive]
    refine next heap initial locals words (After.refl at_ vars liveIn
      (by rw [mode]; exact rep) (by rw [mode, borrowed]; rfl) ?_) ?_ rfl (Nat.le_add_right _ _)
    · rw [mode]
      intro other y hy modes otherWords otherHeld otherWidth block member region regionMember
      rcases modes with modes | modes
      · exact absurd modes owned
      · have distinct : y.index ≠ pair.index := fun same => by
          rw [same] at modes
          exact owned modes
        rw [modes] at regionMember
        exact regionsDisjoint_symm (vars.2 other _ y pair (liveIn _ hy) used distinct modes
          otherWords words otherHeld otherWidth held width region regionMember block member)
    · rw [mode]
      exact fun region member => scratch _ pair used words held width region member

/-- The facts after the code of a `letPair` and the body's `After` give the binding's `After`. -/
theorem After.letPair {World : Type} {context : List Ty} {env : Env context} {slots : List Slot}
    {first second : Ty} {value : (Ty.pair first second).denote} {mode : Mode}
    {liveIn liveMid bodyLive bodyIn live : Nat → Bool} {base : Nat}
    {heap middleHeap bodyHeap finalHeap : Heap}
    {store middleStore bodyStore finalStore : Store World}
    {locals middleLocals bodyLocals finalLocals : Locals}
    {result : ResultTy} {resultValue : result.denote} {words finalWords : List Value}
    (vars : Holds env slots liveIn base heap (PureTransport.erase store) locals)
    (head : Verified.After env slots liveIn liveMid base heap (PureTransport.erase store) locals
      (.pair first second) mode value middleHeap (PureTransport.erase middleStore) middleLocals
      words)
    (frame : Frame base middleLocals bodyLocals)
    (parts : Holds (.cons value.2 (.cons value.1 env))
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyLive
      (base + first.width + second.width) middleHeap (PureTransport.erase middleStore) bodyLocals)
    (release : Evolves (.cons value.2 (.cons value.1 env))
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyLive bodyIn
      (base + first.width + second.width) middleHeap (PureTransport.erase middleStore) bodyLocals
      bodyHeap (PureTransport.erase bodyStore) bodyLocals)
    (body : After (.cons value.2 (.cons value.1 env))
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyIn (shift 2 live)
      (base + first.width + second.width) bodyHeap bodyStore bodyLocals result resultValue
      finalHeap finalStore finalLocals finalWords)
    (fresh : ∀ region, (∀ block ∈ mode.fresh (PureTransport.erase middleStore)
        (.pair first second) words value, regionsDisjoint region block) →
      (mode = .owned → ∀ held, LocalsHold bodyLocals (base + first.width) second.types held →
        held.length = second.width →
        ∀ block ∈ second.blocks (PureTransport.erase middleStore) held value.2,
          regionsDisjoint region block) ∧
      (mode = .owned → ∀ held, LocalsHold bodyLocals base first.types held →
        held.length = first.width →
        ∀ block ∈ first.blocks (PureTransport.erase middleStore) held value.1,
          regionsDisjoint region block))
    (bodySelected : ∀ i, bodyLive (i + 2) = true → liveMid i = true)
    (releaseSelected : ∀ i, bodyIn i = true → bodyLive i = true)
    (outputSelected : ∀ i, shift 2 live i = true → bodyIn i = true)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true) :
    After env slots liveIn live base heap store locals result resultValue finalHeap finalStore
      finalLocals finalWords := by
  have tail : Step middleHeap (PureTransport.erase middleStore)
      (fun region => Holds.KeepDying (.cons value.2 (.cons value.1 env))
          (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyLive (shift 2 live)
          (PureTransport.erase middleStore) bodyLocals region ∧
        regionsDisjoint region ABI.low)
      finalHeap (PureTransport.erase finalStore)
      (result.fresh (PureTransport.erase finalStore) finalWords resultValue) := by
    refine release.step.trans body.step fun region kept =>
      ⟨kept.1.mono fun i hIn hOut => ⟨hIn, ?_⟩, fun _ => ⟨?_, kept.2⟩⟩
    · cases hLive : shift 2 live i with
      | false => rfl
      | true => rw [outputSelected i hLive] at hOut; exact nomatch hOut
    · exact Holds.KeepDying.transfer parts release.step release.frame releaseSelected
        (fun i hIn _ => hIn) (kept.1.mono fun i hIn hOut => ⟨releaseSelected _ hIn, hOut⟩)
  refine ⟨head.step.trans tail fun region kept => ⟨?_, fun hFresh => ⟨?_, kept.2⟩⟩,
    head.frame.trans (frame.trans (body.frame.mono (by omega))), ?_, body.rep, ?_⟩
  · exact kept.1.mono fun i hIn hOut => ⟨hIn, by
      cases hLive : live i with
      | false => rfl
      | true => rw [selected i hLive] at hOut; exact nomatch hOut⟩
  · have middle : Holds.KeepDying env slots liveMid live (PureTransport.erase middleStore)
        middleLocals region :=
      Holds.KeepDying.transfer vars head.step head.frame midSelected (fun i hIn _ => hIn)
        (kept.1.mono fun i hIn hOut => ⟨midSelected _ hIn, hOut⟩)
    obtain ⟨freshSecond, freshFirst⟩ := fresh region hFresh
    intro type x hIn hOut owned held holds width block member
    cases x with
    | here => exact freshSecond owned held holds width block member
    | there x =>
      cases x with
      | here => exact freshFirst owned held holds width block member
      | there x =>
        change (slots.getD x.index default).mode = .owned at owned
        change LocalsHold bodyLocals (slots.getD x.index default).loc type.types held at holds
        have hMid : liveMid x.index = true := bodySelected x.index hIn
        have hDead : live x.index = false := by
          simpa [Var.index, shift, Nat.add_assoc] using hOut
        exact middle type x hMid hDead owned held
          ((head.holds.hold_agree frame hMid width).mp holds) width block member
  · exact (body.holds.pop.pop.live_mono fun i h => by
      simpa [shift, Nat.add_assoc] using h).lower vars fun i h => midSelected _ (selected _ h)
  · cases result with
    | unit => trivial
    | value type =>
      exact body.apart.pop.pop.live_mono fun i h => by simpa [shift, Nat.add_assoc] using h

/-- The stores of the pair's components and the releases of the owned components that the body
does not use, after the pair's code.  The continuation receives the facts about the body's
context from which the body's code runs, and the composition of the body's `After` with the
binding's. -/
theorem wp_letPair_tail_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {S : List Sig} {effects : List EffectSig} {context : List Ty} {first second : Ty}
    {result : ResultTy} {source target : Wasm.Module} {sourceHost : HostEnv Unit}
    {targetHost : HostEnv World} {pool : Bytes.LiteralPool}
    {pair : Var context (.pair first second)}
    {body : Command S effects (second :: first :: context) result}
    {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {heap middleHeap : Heap} {initial middle : Store World} {locals middleLocals : Locals}
    {h base : Nat} {words : List Value} {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source)
    (releaseForm : Encoding.ProgramForm (letPairReleaseCode first second
      ((Expr.var (S := S) pair).mode (slots.map Slot.mode)) base (body.uses 1) (body.uses 0)))
    (releaseClosed : Relocation.programClosed source.funcs.length (letPairReleaseCode first second
      ((Expr.var (S := S) pair).mode (slots.map Slot.mode)) base (body.uses 1) (body.uses 0)) =
        true)
    (vars : Holds env slots (fun i => (live i || body.uses (i + 2)) ||
      (Expr.var (S := S) pair).uses i) base heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots (fun i => (live i || body.uses (i + 2)) ||
      (Expr.var (S := S) pair).uses i) (PureTransport.erase initial) locals ABI.low)
    (safe : pool.Safe env slots (fun i => (live i || body.uses (i + 2)) ||
      (Expr.var (S := S) pair).uses i) heap (PureTransport.erase initial) locals)
    (positions : locals.positions = h) (low : locals.params.length ≤ base)
    (room : base + first.width + second.width ≤ h)
    (head : Verified.After env slots (fun i => (live i || body.uses (i + 2)) ||
        (Expr.var (S := S) pair).uses i) (fun i => live i || body.uses (i + 2))
      (base + first.width + second.width) heap (PureTransport.erase initial) locals
      (.pair first second) ((Expr.var (S := S) pair).mode (slots.map Slot.mode)) (env.get pair)
      middleHeap (PureTransport.erase middle) middleLocals words)
    (fresh : ∀ region ∈ (Ty.pair first second).regions
        ((Expr.var (S := S) pair).mode (slots.map Slot.mode))
        (PureTransport.erase middle) words (env.get pair),
      regionsDisjoint ABI.low region)
    (next : ∀ bodyHeap bodyStore bodyLocals,
      Holds (.cons (env.get pair).2 (.cons (env.get pair).1 env))
        (⟨base + first.width, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ ::
          ⟨base, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ :: slots)
        (fun i => shift 2 live i || body.uses i) (base + first.width + second.width)
        bodyHeap (PureTransport.erase bodyStore) bodyLocals →
      bodyHeap.At (PureTransport.erase bodyStore) →
      pool.Safe (.cons (env.get pair).2 (.cons (env.get pair).1 env))
        (⟨base + first.width, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ ::
          ⟨base, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ :: slots)
        (fun i => shift 2 live i || body.uses i) bodyHeap (PureTransport.erase bodyStore)
        bodyLocals →
      Holds.ApartFrom (.cons (env.get pair).2 (.cons (env.get pair).1 env))
        (⟨base + first.width, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ ::
          ⟨base, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ :: slots)
        (fun i => shift 2 live i || body.uses i) (PureTransport.erase bodyStore) bodyLocals
        ABI.low →
      bodyStore.host = middle.host → bodyHeap.top = middleHeap.top →
      (PureTransport.erase bodyStore).memoryCap source 0 =
        (PureTransport.erase initial).memoryCap source 0 →
      bodyLocals.params = locals.params → bodyLocals.positions = h →
      bodyLocals.values = locals.values →
      (∀ (bodyResult : ResultTy) (resultValue : bodyResult.denote) finalHeap
          (final : Store World) finalLocals finalWords,
        After (.cons (env.get pair).2 (.cons (env.get pair).1 env))
          (⟨base + first.width, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ ::
            ⟨base, (Expr.var (S := S) pair).mode (slots.map Slot.mode)⟩ :: slots)
          (fun i => shift 2 live i || body.uses i) (shift 2 live)
          (base + first.width + second.width) bodyHeap bodyStore bodyLocals bodyResult resultValue
          finalHeap final finalLocals finalWords →
        After env slots (fun i => (live i || body.uses (i + 2)) ||
            (Expr.var (S := S) pair).uses i) live base heap initial locals bodyResult resultValue
          finalHeap final finalLocals finalWords) →
      wp target rest Q bodyStore bodyLocals targetHost) :
    wp target (storeCode h (base + first.width) second.types ++ (storeCode h base first.types ++
        (Relocation.programWith calls (letPairReleaseCode first second
          ((Expr.var (S := S) pair).mode (slots.map Slot.mode)) base (body.uses 1) (body.uses 0)) ++
          rest)))
      Q middle { middleLocals with values := words.reverse ++ locals.values } targetHost := by
  generalize (Expr.var (S := S) pair).mode (slots.map Slot.mode) = mode
    at head fresh releaseForm releaseClosed next ⊢
  let mid := fun i => live i || body.uses (i + 2)
  let all := fun i => mid i || (Expr.var (S := S) pair).uses i
  let bodyLive := fun i => decide (i < 2) || shift 2 live i || body.uses i
  let bodyIn := fun i => shift 2 live i || body.uses i
  have midSelected : ∀ i, mid i = true → all i = true := fun i hMid => by
    simp only [all, hMid, Bool.true_or]
  have head' := head.lower vars (by omega) midSelected
  obtain ⟨firstWords, secondWords, rfl, firstRep, secondRep, disjoint⟩ := head'.rep
  have firstWidth := firstRep.length
  have secondWidth := secondRep.length
  rw [List.reverse_append, List.append_assoc]
  refine wp_storeCode secondWords h (base + first.width) second.types middleLocals
    (firstWords.reverse ++ locals.values) secondRep.typed (head'.frame.positions.trans positions)
    (by rw [head'.frame.params]; omega)
    (by rw [Ty.types_length, head'.frame.positions, positions]; omega)
    fun secondLocals secondFrame secondHeld _ => ?_
  refine wp_storeCode firstWords h base first.types secondLocals locals.values firstRep.typed
    (secondFrame.positions.trans (head'.frame.positions.trans positions))
    (by rw [secondFrame.params, head'.frame.params]; omega)
    (by rw [Ty.types_length, secondFrame.positions, head'.frame.positions, positions]; omega)
    fun firstLocals firstFrame firstHeld above => ?_
  let bodyLocals := { firstLocals with values := locals.values }
  have firstHeld' : LocalsHold bodyLocals base first.types firstWords := firstHeld
  have secondHeld' : LocalsHold bodyLocals (base + first.width) second.types secondWords :=
    secondHeld.keep firstFrame.positions above (by rw [Ty.types_length])
      (by rw [secondWidth, secondFrame.positions, head'.frame.positions, positions]; omega)
  have frame : Frame base middleLocals bodyLocals :=
    (secondFrame.mono (by omega)).trans (firstFrame.trans Frame.ofValues)
  have midVars := head'.holds.agree frame
  have midApart := head'.apart.agree head'.holds frame
  have parts : Holds (.cons (env.get pair).2 (.cons (env.get pair).1 env))
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyLive
      (base + first.width + second.width) middleHeap (PureTransport.erase middle) bodyLocals := by
    refine Holds.push (Holds.push (midVars.live_mono fun i h => by simpa [bodyLive, mid] using h)
      firstHeld' firstRep ((midApart.fst firstWidth).live_mono fun i h => by
        simpa [bodyLive, mid] using h)) secondHeld' secondRep ?_
    refine Holds.Apart.push ((midApart.snd firstWidth).live_mono fun i h => by
      simpa [bodyLive, mid] using h) firstHeld' firstWidth
      fun owned block member region regionMember => ?_
    have owned' : mode = .owned := by simpa using owned
    rw [owned'] at member regionMember disjoint
    exact regionsDisjoint_symm (disjoint rfl region regionMember block member)
  have splitSafe : pool.Safe (.cons (env.get pair).2 (.cons (env.get pair).1 env))
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyLive middleHeap
      (PureTransport.erase middle) bodyLocals :=
    safe.bind2 vars head' midSelected (fun i h => by simpa [bodyLive, mid] using h) frame
      firstRep secondRep firstHeld' secondHeld'
  have midScratch : Holds.ApartFrom env slots mid (PureTransport.erase middle) bodyLocals
      ABI.low :=
    Holds.ApartFrom.transfer vars (scratch.mono midSelected) head'.step
      (head'.frame.trans frame) midSelected
      fun _ _ hLive _ held width _ member => vars.keepDying midSelected hLive held width _ member
  have splitScratch : Holds.ApartFrom (.cons (env.get pair).2 (.cons (env.get pair).1 env))
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) bodyLive
      (PureTransport.erase middle) bodyLocals ABI.low := by
    refine Holds.ApartFrom.push (Holds.ApartFrom.push
      (midScratch.mono fun i h => by simpa [bodyLive, mid, shift] using h) firstHeld' firstWidth
      fun _ block member => fresh block ?_) secondHeld' secondWidth
      fun _ block member => fresh block ?_
    · rw [Ty.regions_append firstWidth]
      exact List.mem_append_left _ member
    · rw [Ty.regions_append firstWidth]
      exact List.mem_append_right _ member
  rw [letPairReleaseCode_eq first second _ base (body.uses 1) (body.uses 0) context slots]
    at releaseForm releaseClosed ⊢
  refine wp_releaseVars_with (sourceHost := sourceHost) _ (by split <;> split <;> simp) runtime
    layout profile releaseForm
    releaseClosed parts head'.step.at_ (by split <;> split <;> simp [bodyLive])
    fun bodyHeap bodyStore release top sameHost => ?_
  have release' := release.mono (live' := bodyIn) fun i h => by
    match i with
    | 0 =>
      have used : body.uses 0 = true := by simpa [bodyIn, shift] using h
      simp [bodyLive, used]
    | 1 =>
      have used : body.uses 1 = true := by simpa [bodyIn, shift] using h
      simp [bodyLive, used]
    | k + 2 => split <;> split <;> simpa [bodyLive, bodyIn] using h
  have bodySelected : ∀ i, bodyLive (i + 2) = true → mid i = true := fun i h => by
    simpa [bodyLive, mid, shift] using h
  have inLive : ∀ i, bodyIn i = true → bodyLive i = true := fun i h => by
    simp only [bodyLive, bodyIn, Bool.or_eq_true] at h ⊢
    rcases h with h | h <;> simp [h]
  refine next bodyHeap bodyStore bodyLocals release'.holds release'.step.at_
    (splitSafe.evolves parts release' inLive)
    (Holds.ApartFrom.transfer parts (splitScratch.mono inLive) release'.step release'.frame
      inLive fun _ _ hLive _ held width _ member =>
        parts.keepDying inLive hLive held width _ member)
    sameHost top
    (by rw [release'.step.cap source, head'.step.cap source])
    (by rw [frame.params, head'.frame.params]) (frame.positions.trans
      (head'.frame.positions.trans positions)) rfl ?_
  intro bodyResult resultValue finalHeap final finalLocals finalWords after
  have fresh' : ∀ region, (∀ block ∈ mode.fresh (PureTransport.erase middle)
      (.pair first second) (firstWords ++ secondWords) (env.get pair),
        regionsDisjoint region block) →
      (mode = .owned → ∀ held, LocalsHold bodyLocals (base + first.width) second.types held →
        held.length = second.width →
        ∀ block ∈ second.blocks (PureTransport.erase middle) held (env.get pair).2,
          regionsDisjoint region block) ∧
      (mode = .owned → ∀ held, LocalsHold bodyLocals base first.types held →
        held.length = first.width →
        ∀ block ∈ first.blocks (PureTransport.erase middle) held (env.get pair).1,
          regionsDisjoint region block) := by
    intro region hFresh
    rw [Mode.fresh_pair firstWidth] at hFresh
    refine ⟨fun owned held holds width block member => ?_,
      fun owned held holds width block member => ?_⟩
    · obtain rfl := LocalsHold.unique holds secondHeld' (width.trans secondWidth.symm)
      rw [owned] at hFresh
      exact hFresh block (List.mem_append_right _ member)
    · obtain rfl := LocalsHold.unique holds firstHeld' (width.trans firstWidth.symm)
      rw [owned] at hFresh
      exact hFresh block (List.mem_append_left _ member)
  exact After.letPair vars head' frame parts release' after fresh' bodySelected inLive
    (fun i h => by simp [bodyIn, h]) midSelected (fun i h => by simp [h])

/-- A classification of the body's code from the state after the binding's code is one of the
binding's code, whose meaning is the body's at the components. -/
theorem CommandResult.letPair {World : Type} {host : Host World} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {bodyContext : List Ty} {bodyEnv : Env bodyContext} {bodySlots : List Slot}
    {bodyIn bodyLive : Nat → Bool} {bodyBase : Nat} {result : ResultTy}
    {action : Action result.denote} {heap bodyHeap : Heap}
    {initial bodyStore : Store (Observed World)} {locals bodyLocals : Locals} {aborts : Bool}
    {continuation : Continuation (Observed World)}
    (sameHost : bodyStore.host = initial.host) (sameValues : bodyLocals.values = locals.values)
    (compose : ∀ value finalHeap final finalLocals words,
      After bodyEnv bodySlots bodyIn bodyLive bodyBase bodyHeap bodyStore bodyLocals result value
        finalHeap final finalLocals words →
      After env slots liveIn live base heap initial locals result value finalHeap final
        finalLocals words)
    (execution : CommandResult host bodyEnv bodySlots bodyIn bodyLive bodyBase result action
      bodyHeap bodyStore bodyLocals aborts continuation) :
    CommandResult host env slots liveIn live base result action heap initial locals aborts
      continuation := by
  cases execution with
  | returned value finalHeap final finalLocals words trace run after =>
    rw [sameValues]
    refine .returned value finalHeap final finalLocals words trace ?_ (compose _ _ _ _ _ after)
    rw [← sameHost]
    exact run
  | terminal final trace outcome message run ending =>
    refine .terminal final trace outcome message ?_ ending
    rw [← sameHost]
    exact run
  | resource final trace residual allowed progress =>
    refine .resource final trace residual allowed ?_
    rw [← sameHost]
    exact progress

theorem command_letPair_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {first second : Ty} {result : ResultTy}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    (pair : Var context (.pair first second))
    (body : Command pureSigs effectSigs (second :: first :: context) result)
    (bodySpec : CommandCodeSpecWith calls source target pure effects pool body) :
    CommandCodeSpecWith calls source target pure effects pool (.letPair pair body) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place
  obtain ⟨ready, callsOk⟩ := ready
  have allEq : (fun i => live i || (Command.letPair pair body).uses i) =
      (fun i => (live i || body.uses (i + 2)) || (Expr.var (S := pureSigs) pair).uses i) := by
    funext i
    simp only [Command.uses, Expr.uses]
    cases live i <;> cases body.uses (i + 2) <;> cases (i == pair.index) <;> rfl
  rw [allEq] at vars safe scratch ⊢
  change base + (first.width + second.width +
    max (Ty.pair first second).copyScratch body.width) ≤ h at room
  have headReady := ready _ List.mem_cons_self
  have releaseReady := ready _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have bodyReady : body.ReadyWith calls source h
      (⟨base + first.width, (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)⟩ ::
        ⟨base, (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)⟩ :: slots)
      (base + first.width + second.width) (shift 2 live) pool :=
    ⟨fun fragment member => ready fragment (List.mem_append_right _ member), callsOk⟩
  have spec := (Expr.var (S := pureSigs) pair).code_spec source pure.funs pure.flags
    (pure.callBounds depth) (pure.callFits depth) sourceHost facts.runtime
    (Calls.at facts.calls depth) (List.nil_subset _) (fun _ => depthParam) env slots []
    (fun i => live i || body.uses (i + 2))
  simp only [Command.codeWith, List.append_assoc]
  refine wp_letPair_head_with facts.layout facts.profile spec headReady.1 headReady.2 positions rfl
    (vars.mono (by omega)) at_ safe scratch cap (by omega) (by omega)
    (fun _ final same => CommandResult.resource_refl rfl same) ?_
  intro middleHeap middle middleLocals words head fresh sameHost _
  refine wp_letPair_tail_with (sourceHost := sourceHost) facts.runtime facts.layout facts.profile
    releaseReady.1 releaseReady.2 vars scratch safe positions low (by omega) head fresh ?_
  intro bodyHeap bodyStore bodyLocals bodyVars bodyAt bodySafe bodyScratch bodyHost _ bodyCap
    bodyParams bodyPositions bodyValues compose
  have bodyRun := bodySpec World host targetHost depth _ _ (shift 2 live) h
    (base + first.width + second.width) bodyHeap bodyStore bodyLocals valid below
    (by rw [bodyParams]; exact depthParam) bodyPositions bodyVars bodyAt bodySafe bodyScratch
    (by rw [bodyCap]; exact cap) (by rw [bodyParams]; omega) (by omega) bodyReady covered place
  exact wp.conseq (fun _ classification =>
    CommandResult.letPair (bodyHost.trans sameHost) bodyValues (compose result) classification)
    bodyRun

theorem cost_command_letPair_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {first second : Ty} {result : ResultTy}
    (facts : CompilerFactsWith calls source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit) (pair : Var context (.pair first second))
    (body : Command pureSigs effectSigs (second :: first :: context) result)
    (bodySpec : CostCommandCodeSpecWith calls source target pure program pool body) :
    CostCommandCodeSpecWith calls source target pure program pool (.letPair pair body) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place resource
  obtain ⟨ready, callsOk⟩ := ready
  have allEq : (fun i => live i || (Command.letPair pair body).uses i) =
      (fun i => (live i || body.uses (i + 2)) || (Expr.var (S := pureSigs) pair).uses i) := by
    funext i
    simp only [Command.uses, Expr.uses]
    cases live i <;> cases body.uses (i + 2) <;> cases (i == pair.index) <;> rfl
  rw [allEq] at vars safe scratch ⊢
  change base + (first.width + second.width +
    max (Ty.pair first second).copyScratch body.width) ≤ h at room
  have headReady := ready _ List.mem_cons_self
  have releaseReady := ready _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have bodyReady : body.ReadyWith calls source h
      (⟨base + first.width, (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)⟩ ::
        ⟨base, (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)⟩ :: slots)
      (base + first.width + second.width) (shift 2 live) pool :=
    ⟨fun fragment member => ready fragment (List.mem_append_right _ member), callsOk⟩
  have spec := (Expr.var (S := pureSigs) pair).code_spec source pure.funs pure.flags
    (pure.callBounds depth) (pure.callFits depth) sourceHost facts.runtime
    (Calls.at facts.calls depth) (List.nil_subset _) (fun _ => depthParam) env slots []
    (fun i => live i || body.uses (i + 2))
  have charge : Resource.letPairCost (slots.map Slot.mode) live pair body env =
      pair.cost (slots.map Slot.mode) (fun i => live i || body.uses (i + 2)) (env.get pair) := rfl
  simp only [Command.codeWith, List.append_assoc]
  refine wp_letPair_head_with facts.layout facts.profile spec headReady.1 headReady.2 positions rfl
    (vars.mono (by omega)) at_ safe scratch cap (by omega) (by omega) ?_ ?_
  · intro failure final same
    cases aborts with
    | true => exact CostCommandResult.trapped final _ (CommandResult.resource_refl rfl same)
    | false =>
      obtain ⟨within, bounded⟩ := resource rfl
      have fits : heap.Within (PureTransport.erase initial) source
          (pair.cost (slots.map Slot.mode) (fun i => live i || body.uses (i + 2))
            (env.get pair)) := by
        rw [← charge]
        exact within.mono bounded.letPair_charge
      simp [fits] at failure
  intro middleHeap middle middleLocals words head fresh sameHost headTop
  refine wp_letPair_tail_with (sourceHost := sourceHost) facts.runtime facts.layout facts.profile
    releaseReady.1 releaseReady.2 vars scratch safe positions low (by omega) head fresh ?_
  intro bodyHeap bodyStore bodyLocals bodyVars bodyAt bodySafe bodyScratch bodyHost bodyTop bodyCap
    bodyParams bodyPositions bodyValues compose
  have growth : bodyHeap.top.toNat ≤ heap.top.toNat +
      Resource.letPairCost (slots.map Slot.mode) live pair body env := by
    rw [bodyTop, charge]
    exact headTop
  have bodyRun := bodySpec World host targetHost depth _ _ (shift 2 live) h
    (base + first.width + second.width) bodyHeap bodyStore bodyLocals
    (budget - Resource.letPairCost (slots.map Slot.mode) live pair body env) aborts valid below
    (by rw [bodyParams]; exact depthParam) bodyPositions bodyVars bodyAt bodySafe bodyScratch
    (by rw [bodyCap]; exact cap) (by rw [bodyParams]; omega) (by omega) bodyReady covered place
    (fun noAbort => by
      obtain ⟨within, bounded⟩ := resource noAbort
      have bound := bounded.letPair_charge
      refine ⟨within.shift growth (by omega) bodyCap, ?_⟩
      rw [bodyHost, sameHost]
      exact bounded.letPair_body)
  refine wp.conseq (fun continuation classification => ?_) bodyRun
  cases classification with
  | returned value finalHeap final finalLocals finalWords trace spent fits execution after top =>
    rw [bodyValues]
    refine .returned value finalHeap final finalLocals finalWords trace
      (Resource.letPairCost (slots.map Slot.mode) live pair body env + spent) fits ?_
      (compose _ _ _ _ _ _ after) fun valid => by
        have bodyGrowth := top valid
        omega
    apply Resource.ResourceExec.letPair
    rw [← sameHost, ← bodyHost]
    exact execution
  | trapped final message classification =>
    exact .trapped final message
      (CommandResult.letPair (bodyHost.trans sameHost) bodyValues (compose result) classification)

end Verified.Wasi
