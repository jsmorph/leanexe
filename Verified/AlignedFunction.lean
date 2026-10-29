import Verified.AlignedExprCorrect
import Verified.AlignedEnv
import LeanExe.Pipeline.AlignedAlloc

/-!
The function level under the flag.  `bodyFunction_runsX` is `bodyFunction_runs` with `RunsX` for
`Runs`: from an aligned heap and aligned arguments, the run of a body function makes only aligned
64-bit accesses, and it ends with an aligned heap and an aligned owned result.  The guard on the
call depth and the copy of the parameters make no 64-bit access, so their flagged rules come from
the originals through `wpX_append_free`.  `RunsA.append_args` and `RunsA.mono`, in
`LeanExe/Pipeline/AlignedAlloc.lean`, extend an aligned run to a longer operand stack and weaken
its postcondition, as `Runs.append_args` and `Runs.mono` do for a run.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `Runs.of_wp_entry_for` and `RunsA.of_wpA_entry_for` under the flag. -/
theorem RunsX.of_wpX_entry_for {α : Type} {strict aborts : Bool} {env : HostEnv α} {m : Module}
    {id : Nat} {initial : Store α} {args : List Value} {P : Store α → List Value → Prop}
    {f : Function} (hf : m.funcs[id - m.imports.length]? = some f)
    (h : wpX strict m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              P st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs =>
              P st' (vs.take f.results.length ++ args.drop f.numParams)
          | .Trap _ msg => TrapMsg aborts msg
          | _ => False)
        initial (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none) :
    RunsX strict aborts env m id initial args P := by
  cases strict
  · exact Runs.of_wp_entry_for hf h hImp
  · exact RunsA.of_wpA_entry_for hf h hImp

/-- `wp_guardCode` under the flag. -/
theorem wpX_guardCode {strict : Bool} {m : Module} {host : HostEnv Unit} {Q : Assertion Unit}
    {store : Store Unit} {s : Locals} {rest : Program} (depth : Bool) {d : UInt64}
    (h0 : depth = true → s.get 0 = some (.i64 d))
    (hTrap : depth = true → ¬d < depthLimit → ∀ st, Q (.Trap st "unreachable"))
    (hNext : (depth = true → d < depthLimit) → wpX strict m rest Q store s host) :
    wpX strict m ((if depth then guardCode else []) ++ rest) Q store s host := by
  refine wpX_append_free (by cases depth <;> rfl) ?_
  have := wp_guardCode (m := m) (host := host) (rest := []) (Q := ThenX strict m rest Q host)
    depth h0 hTrap fun hd => wp_nil.mpr (hNext hd)
  rwa [List.append_nil] at this

theorem paramCopyCode_free (h : Nat) (tys : List ValueType) :
    ∀ p, freeCode (paramCopyCode h p tys) = true := by
  induction tys with
  | nil => intro p; rfl
  | cons ty tys ih =>
    intro p
    cases ty <;> simp [paramCopyCode, freeCode, freeInst, ih]

/-- `wp_paramCopyCode` under the flag. -/
theorem wpX_paramCopyCode {α : Type} {strict : Bool} {m : Module} {Q : Assertion α}
    {store : Store α} {host : HostEnv α} {h : Nat} (tys : List ValueType) (p : Nat) {s : Locals}
    {rest : Program} (hP : p + tys.length ≤ s.params.length) (hH : s.params.length ≤ h)
    (hh : s.positions = h)
    (hNext : ∀ s', Frame p s s' → s'.values = s.values →
      (∀ q, p ≤ q → q < p + tys.length →
        s'.get (slotIndex h q (tys.getD (q - p) .i64)) = s.get q) →
      wpX strict m rest Q store s' host) :
    wpX strict m (paramCopyCode h p tys ++ rest) Q store s host := by
  refine wpX_append_free (paramCopyCode_free h tys p) ?_
  have := wp_paramCopyCode (m := m) (host := host) (Q := ThenX strict m rest Q host) (s := s)
    (rest := []) tys p hP hH hh fun s' hF hv hq => wp_nil.mpr (hNext s' hF hv hq)
  rwa [List.append_nil] at this

/-- `body_code_spec` under the flag: the code leaves an aligned heap and an aligned owned
result. -/
theorem body_code_specX {strict : Bool} {S : List Sig} {params : List Ty} {result : Ty} (modes : List Mode)
    (body : Expr S params result) (hCovered : body.Covered pool)
    (placeArgs : body.placeArgs = true) (p0 h : Nat)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S) (pf : List Bool)
    (rf : Bool) (hrf : rf = true →
      body.paid flags (entryModes params modes) pf (fun _ => false) = true)
    (m : Module) (host : HostEnv Unit)
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m) (hRt : strict = true → AllocAligned m)
    (hCopy : CopyCodeX strict m host)
    (hListFold : ∀ pv, ListFoldSpecX strict m funs flags bounds fits host pv pool)
    {d0 : UInt64} (hCalls : CallsAtX strict m funs flags bounds fits d0 pool)
    (args : Env params)
    (heap : Heap)
    (store : Store Unit) (s : Locals) (hh : s.positions = h)
    (hRoom : p0 + widthSum params + body.width + copyWidth result ≤ h)
    (hDepth : body.depthCalls = true → s.params.head? = some (.i64 d0))
    (hVars : Holds args (paramSlots params modes p0) (fun _ => true) (p0 + widthSum params)
      heap store s)
    (hAt : heap.At store)
    (hAl : strict = true →
      HoldsA args (paramSlots params modes p0) (fun _ => true) heap store s)
    (hSafe : pool.Safe args (paramSlots params modes p0) (fun _ => true) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hBase : s.params.length ≤ p0 + widthSum params) (Q : Assertion Unit)
    (hTrap : TrapOK (!body.fits funs fits args ||
      ((body.aborts || !result.scalar || (paramModes params modes).any (· == .owned)) &&
        !decide (heap.Within store m
          (args.pot store s (paramSlots params modes p0) (fun i =>
              paidAt pf i && paramMode params modes i == .owned) +
            bodyBound modes pf body funs flags bounds args)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After args (paramSlots params modes p0) (fun _ => true) (fun _ => false)
        (p0 + widthSum params) heap store s result .owned (body.denote funs args) heap' store' s'
        ws →
      (strict = true → HoldsA args (paramSlots params modes p0) (fun _ => false) heap' store' s' ∧
        Ty.AlignedVal .owned store' result ws (body.denote funs args)) →
      (body.fits funs fits args = true →
        heap'.top.toNat + (if rf then result.pot store' ws (body.denote funs args) else 0) ≤
          heap.top.toNat +
            args.pot store s (paramSlots params modes p0) (fun i =>
              paidAt pf i && paramMode params modes i == .owned) +
            bodyBound modes pf body funs flags bounds args) →
      Q (.Fallthrough store' { s' with values := ws.reverse ++ s.values })) :
    wpX strict m (releaseWhere params (paramSlots params modes p0) (fun i => !body.uses i) ++
      (body.code (pool := pool) h (paramSlots params modes p0) (p0 + widthSum params) (fun _ => false) ++
      (coerceCode h result (body.mode ((paramSlots params modes p0).map Slot.mode)) .owned
        (p0 + widthSum params + body.width) ++ []))) Q store s host := by
  have hModes : (paramSlots params modes p0).map Slot.mode = entryModes params modes := by
    rw [entryModes, paramSlots_modes, paramSlots_modes]
  refine wpX_releaseWhere hm hRA hVars hAt hAl (fun _ _ => rfl) fun heap1 store1 e hTop1 hAl1 => ?_
  have e' := e.mono (live' := fun i => false || body.uses i) fun i h => by simpa using h
  -- The paid parameters that the body uses keep their potential across the release, and die in
  -- the body.
  have hDp : dyingPot store1 s args (paramSlots params modes p0) pf
        (fun i => false || body.uses i) (fun _ => false) ≤
      args.pot store s (paramSlots params modes p0) (fun i =>
        paidAt pf i && paramMode params modes i == .owned) := by
    rw [dyingPot_evolves hVars e' (fun _ _ => rfl) _ _ fun _ h => h]
    exact Env.pot_mono args _ _ _ fun i h => by
      simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
      exact ⟨h.1.2, by rw [← paramSlots_getD_mode params modes p0]; exact h.2⟩
  refine Expr.code_specX m funs flags bounds fits host hm hRA hRt hCopy hCalls (hListFold _) body
    hCovered hDepth args
    (paramSlots params modes p0) pf (fun _ => false) h (p0 + widthSum params)
    heap1 store1 s hh rfl e'.holds e'.step.at_
    (fun hs => (hAl1 hs).live_mono fun i h => by simpa using h)
    (hSafe.evolves hVars e' (fun _ _ => rfl))
    (by rw [e'.step.cap m]; exact hCap) hBase (by omega)
    placeArgs _ _
    (hTrap.part (fun h => h)
      (fun h => by
        rw [← Slot.any_map, paramSlots_modes] at h
        exact trap_left _ _ _ h)
      fun _ hw => hw.of_le (by rw [hTop1, hModes]; simp only [bodyBound]; omega)
        (e'.step.cap m))
    fun heap' store' s' ws a hAlB hTopB => ?_
  have hDp' : dyingPot store1 s args (paramSlots params modes p0) pf
      (fun i => (fun _ => false) i || body.uses i) (fun _ => false) ≤
      args.pot store s (paramSlots params modes p0) (fun i =>
        paidAt pf i && paramMode params modes i == .owned) := hDp
  have a' := After.prepend hVars e' a (fun _ _ => rfl) fun _ h => nomatch h
  refine After.coerceX hCopy a' hAlB (fun _ => rfl) (Nat.le_add_right _ _)
    (by rw [a'.frame.params]; omega) (a'.frame.positions.trans hh) (by omega)
    (by rw [a'.step.cap m]; exact hCap)
    (fun hs _ hsc => hTrap.alloc (by simp [hsc]) fun hd hw => hw.of_le (by
      have := hTopB (fits_of_not hd)
      rw [hModes] at this hs
      rw [hTop1] at this
      simp only [bodyBound, coerceCost, hs, and_self, ↓reduceIte]
      omega) (a'.step.cap m))
    fun heap'' store'' s'' ws'' a'' hTopC hSameC hAlC => ?_
  rw [wpX_nil]
  refine hNext heap'' store'' s'' ws'' a'' hAlC fun hd => ?_
  have hB := hTopB hd
  rw [hModes] at hB hTopC
  rw [hTop1] at hB
  -- A paid result is the body's paid value, which the coercion of an owned value keeps.
  have hK := pot_keep (P := rf) (Q := body.paid flags (entryModes params modes) pf (fun _ => false))
    (a := result.pot store'' ws'' (body.denote funs args))
    (b := result.pot store' ws (body.denote funs args)) hrf fun hp => by
      obtain ⟨rfl, rfl⟩ := hSameC (by rw [hModes]; exact Expr.mode_of_paid body (hrf hp))
      rfl
  simp only [bodyBound]
  omega

/-- `bodyFunction_runs` under the flag: from an aligned heap and aligned arguments, the run is
aligned and ends with an aligned heap and an aligned owned result. -/
theorem bodyFunction_runsX {strict : Bool} {S : List Sig} {params : List Ty} {result : Ty} (modes : List Mode)
    (body : Expr S params result) (placeArgs : body.placeArgs = true) (depth : Bool)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S) (pf : List Bool)
    (rf : Bool) (hrf : rf = true →
      body.paid flags (entryModes params modes) pf (fun _ => false) = true)
    (m : Module) (pos : Nat) (hm : Runtime m)
    (hFunc : m.funcs[pos]? = some (bodyFunction modes body depth pos pool))
    (hCovered : body.Covered pool) (d : UInt64)
    (hCalls : (depth = true → d < depthLimit) → CallsAtX strict m funs flags bounds fits d pool)
    (hDepth : depth = false → body.depthCalls = false) (aborts : Bool)
    (hAborts : (body.aborts || !result.scalar || (paramModes params modes).any (· == .owned) ||
      depth) = true → aborts = true)
    (host : HostEnv Unit) (store : Store Unit) (heap : Heap) (ws : List Value)
    (args : Env params) (hAt : heap.At store)
    (hInput : @pool.Input (Env params) (Env.represent params modes) heap store ws args)
    (hRep : Env.Rep (paramMode params modes) heap store ws args)
    (hSep : Separate store (Env.moves store (paramMode params modes) ws args)
      (Env.reads store (paramMode params modes) ws args))
    (hCap : store.memoryCap m 0 ≤ 65535) (hRA : strict = true → ReleaseAligned m) (hRt : strict = true → AllocAligned m)
    (hCopy : CopyCodeX strict m host)
    (hListFold : ∀ pv, ListFoldSpecX strict m funs flags bounds fits host pv pool)
    (hAl : strict = true → heap.Aligned ∧ Env.AlignedVals store (paramMode params modes) ws args) :
    RunsX strict ((depth && !(decide (d < depthLimit) && body.fits funs fits args)) ||
        (aborts && !decide (heap.Within store m
          (Env.argPot store (fun i => paidAt pf i && paramMode params modes i == .owned) ws args +
            bodyBound modes pf body funs flags bounds args))))
      host m pos store ((if depth then [Value.i64 d] else []) ++ ws).reverse
      fun final values => ∃ heap' : Heap, heap'.At final ∧
        result.Rep .owned heap' final values.reverse (body.denote funs args) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 →
          Apart store (Env.moves store (paramMode params modes) ws args) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r ∧
          ∀ b ∈ result.blocks final values.reverse (body.denote funs args), regionsDisjoint r b) ∧
        ((depth && !(decide (d < depthLimit) && body.fits funs fits args)) = false →
          heap'.top.toNat + (if rf then result.pot final values.reverse (body.denote funs args)
              else 0) ≤
            heap.top.toNat +
              Env.argPot store (fun i => paidAt pf i && paramMode params modes i == .owned) ws
                args +
              bodyBound modes pf body funs flags bounds args) ∧
        (strict = true → heap'.Aligned ∧
          Ty.AlignedVal .owned final result values.reverse (body.denote funs args)) := by
  have hLength : ws.length = widthSum params := hRep.length
  have hdv : (if depth then [Value.i64 d] else []).length = (if depth then 1 else 0) := by
    cases depth <;> rfl
  have hNum := bodyFunction_numParams (pool := pool) modes body depth pos
  have hRes : (bodyFunction modes body depth pos pool).results.length = result.width := by
    simp [bodyFunction, Expr.usesFast_eq, Ty.types_length]
  apply RunsX.of_wpX_entry_for (f := bodyFunction modes body depth pos pool)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact hFunc)
    (hImp := by simp [hm.imports])
  have hTake : (((if depth then [Value.i64 d] else []) ++ ws).reverse.take
      (bodyFunction modes body depth pos pool).numParams).reverse =
      (if depth then [Value.i64 d] else []) ++ ws := by
    rw [List.take_of_length_le (by
      rw [hNum, List.length_reverse, List.length_append, hdv, hLength])]
    simp
  rw [hTake, show (bodyFunction modes body depth pos pool).body =
    (if depth then guardCode else []) ++
    (paramCopyCode (positions body depth) (if depth then 1 else 0) (params.flatMap Ty.types) ++
    (releaseWhere params (paramSlots params modes (if depth then 1 else 0))
        (fun i => !body.uses i) ++
      (body.code (pool := pool) (positions body depth) (paramSlots params modes (if depth then 1 else 0))
        ((if depth then 1 else 0) + widthSum params) (fun _ => false) ++
      (coerceCode (positions body depth) result
        (body.mode ((paramSlots params modes (if depth then 1 else 0)).map Slot.mode)) .owned
        ((if depth then 1 else 0) + widthSum params + body.width) ++ [])))) by
    simp [bodyFunction, Expr.usesFast_eq]]
  have hl0 : ((bodyFunction modes body depth pos pool).toLocals
      ((if depth then [Value.i64 d] else []) ++ ws)).locals.length =
      body.width + copyWidth result + positions body depth + positions body depth := by
    simp [Function.toLocals, bodyFunction, Nat.add_assoc]
  have hHead : depth = true →
      ((if depth then [Value.i64 d] else []) ++ ws).head? = some (.i64 d) := by
    intro hd; subst hd; rfl
  refine wpX_guardCode depth (d := d) (fun hd => by subst hd; simp [Function.toLocals])
    (fun hd hnd st => by
      show TrapMsg _ "unreachable"
      simp only [hd, hnd, decide_false, Bool.false_and, Bool.not_false, Bool.true_and,
        Bool.true_or]
      rfl) fun hlt => ?_
  have hCalls' : CallsAtX strict m funs flags bounds fits d pool := hCalls hlt
  have hFitsB : (depth && !(decide (d < depthLimit) && body.fits funs fits args)) = false →
      body.fits funs fits args = true := fun h => by
    cases hdep : depth
    · exact Expr.fits_of_depthCalls funs fits body (hDepth hdep) args
    · simp only [hdep, Bool.true_and, Bool.not_eq_false', Bool.and_eq_true,
        decide_eq_true_eq] at h
      exact h.2
  have hPos : positions body depth =
      (if depth then 1 else 0) + widthSum params + body.width + copyWidth result := rfl
  have hp0 : ((bodyFunction modes body depth pos pool).toLocals
      ((if depth then [Value.i64 d] else []) ++ ws)).params =
      (if depth then [Value.i64 d] else []) ++ ws := rfl
  have hv0 : ((bodyFunction modes body depth pos pool).toLocals
      ((if depth then [Value.i64 d] else []) ++ ws)).values = [] := rfl
  generalize (bodyFunction modes body depth pos pool).toLocals
    ((if depth then [Value.i64 d] else []) ++ ws) = s0 at hl0 hp0 hv0 ⊢
  generalize (if depth then 1 else 0) = p0 at hdv hNum hPos ⊢
  generalize (if depth then [Value.i64 d] else []) = dv at hdv hHead hp0 ⊢
  generalize positions body depth = h at hPos hl0 ⊢
  have hLocals : s0.params.length + s0.locals.length = h + h + h := by
    rw [hp0, hl0, List.length_append, hdv, hLength, hPos]; omega
  refine wpX_paramCopyCode (params.flatMap Ty.types) p0
    (by rw [flatMap_types_length, hp0, List.length_append, hdv, hLength])
    (by rw [hp0, List.length_append, hdv, hLength, hPos]; omega)
    (by simp only [Locals.positions, hLocals]; omega)
    fun s1 frame1 hv1 hcopy1 => ?_
  have hp1 := frame1.params
  have hh1 : s1.positions = h := by
    rw [frame1.positions, Locals.positions, hLocals]; omega
  have hParam : ∀ j (hj : j < ws.length), s0.get (p0 + j) = some ws[j] := by
    intro j hj
    have hlt : p0 + j < (dv ++ ws).length := by rw [List.length_append, hdv]; omega
    simp only [Locals.get, hp0, hlt, ↓reduceIte]
    rw [List.getElem?_append_right (by omega), hdv, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj]
  -- The locals after the copy hold each parameter's words.
  have hHold : ∀ {t : Ty} (x : Var params t),
      LocalsHold s1 (p0 + x.offset) t.types ((ws.drop x.offset).take t.width) := by
    intro t x k hk
    have hk' := hk
    simp only [List.length_take, List.length_drop] at hk'
    have hlt : x.offset + k < ws.length := by have := x.offset_width; omega
    have hkw : k < t.width := by have := x.offset_width; omega
    rw [List.getElem_take, List.getElem_drop, hh1]
    have copied := hcopy1 (p0 + x.offset + k) (by omega)
      (by rw [flatMap_types_length]; have := x.offset_width; omega)
    rw [show p0 + x.offset + k - p0 = x.offset + k by omega, x.types_getD hkw] at copied
    rw [copied, Nat.add_assoc]
    exact hParam _ hlt
  have hWords : ∀ {t : Ty} (x : Var params t),
      ((ws.drop x.offset).take t.width).length = t.width := by
    intro t x
    have := x.offset_width
    simp only [List.length_take, List.length_drop]
    omega
  have hPotEq : args.pot store s1 (paramSlots params modes p0)
      (fun i => paidAt pf i && paramMode params modes i == .owned) =
      Env.argPot store (fun i => paidAt pf i && paramMode params modes i == .owned) ws args :=
    Env.pot_paramSlots modes p0 _ ws args hLength fun x => hHold x
  refine body_code_specX modes body hCovered placeArgs p0 h funs flags bounds fits pf rf hrf m host hm
    hRA hRt hCopy hListFold hCalls'
    args heap store s1
    hh1 (by omega) (fun hb => ?_)
    ⟨fun t x _ => ?_, fun t u x y _ _ hxy hmo wx wy hwx hlx hwy hly => ?_⟩ hAt
    (fun hs => ?_) (hInput.params hRep hHold) hCap
    (by rw [hp1, hp0, List.length_append, hdv, hLength]) _
    ((TrapOK.of_msg fun _ => Iff.rfl).of_imp fun hb => by
      rw [hPotEq] at hb
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hb ⊢
      rcases hb with hb | ⟨ha, hw⟩
      · have hd : depth = true := by
          cases hdep : depth
          · have := Expr.fits_of_depthCalls funs fits body (hDepth hdep) args
            simp [this] at hb
          · rfl
        refine Or.inl ⟨hd, ?_⟩
        simp only [Bool.not_eq_true'] at hb
        simp [hb]
      · exact Or.inr ⟨hAborts (by simp only [Bool.or_eq_true]; exact Or.inl ha), hw⟩)
    fun heap' store' s' ws' a hAlB hTopB => ?_
  · cases hdep : depth
    · rw [hDepth hdep] at hb; exact nomatch hb
    · rw [hp1, hp0]; exact hHead hdep
  · rw [paramSlots_getD x]
    exact ⟨show p0 + x.offset + t.width ≤ p0 + widthSum params by
      have := x.offset_width; omega, _, hHold x, hRep.var x⟩
  · rw [paramSlots_getD x] at hwx hmo
    rw [paramSlots_getD y] at hwy ⊢
    obtain rfl := LocalsHold.unique hwx (hHold x) (by rw [hlx, hWords])
    obtain rfl := LocalsHold.unique hwy (hHold y) (by rw [hly, hWords])
    exact hRep.apart x hSep y hxy hmo
  · obtain ⟨hHeap, hVals⟩ := hAl hs
    refine ⟨hHeap, fun t x _ wx hwx hlx => ?_⟩
    rw [paramSlots_getD x] at hwx ⊢
    obtain rfl := LocalsHold.unique hwx (hHold x) (by rw [hlx, hWords])
    exact hVals.var x
  · have hLen := a.rep.length
    have hValues : (ws'.reverse ++ s1.values).take
        (bodyFunction modes body depth pos pool).results.length ++
        (dv ++ ws).reverse.drop (bodyFunction modes body depth pos pool).numParams = ws'.reverse := by
      rw [hv1, hv0, hNum, hRes, List.append_nil,
        List.take_of_length_le (by rw [List.length_reverse, hLen]),
        List.drop_of_length_le (by rw [List.length_reverse, List.length_append, hdv, hLength]),
        List.append_nil]
    simp only [hValues]
    refine ⟨heap', a.step.at_, ?_, a.step.caps, fun r hr hpos hA => ?_, fun hf => ?_, fun hs => ?_⟩
    · rw [List.reverse_reverse]
      exact a.rep
    · obtain ⟨hb, hreg, hf⟩ := a.step.keeps r hr hpos fun t x _ _ hmo wx hwx hlx b hb => by
        rw [paramSlots_getD x] at hwx hmo
        obtain rfl := LocalsHold.unique hwx (hHold x) (by rw [hlx, hWords x])
        rw [Ty.blocks_pointers] at hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
        exact hA q (Env.moves_var x hRep hmo q hq)
      refine ⟨hb, hreg, fun b hb' => hf b ?_⟩
      rw [List.reverse_reverse] at hb'
      exact hb'
    · have := hTopB (hFitsB hf)
      rw [hPotEq] at this
      rw [List.reverse_reverse]
      exact this
    · rw [List.reverse_reverse]
      exact ⟨(hAlB hs).1.1, (hAlB hs).2⟩


theorem _root_.LeanExe.ProofKit.RunsA.of_imp {α : Type} {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {P : Store α → List Value → Prop} {a a' : Bool}
    (h : RunsA a env m id initial args P) (himp : a = true → a' = true) :
    RunsA a' env m id initial args P :=
  ⟨h.1.of_imp himp, h.2⟩

/-- `FunAligned` of a body function whose code takes no call depth, as `bodyFunction_implements`
gives its `ImplementsP`. -/
theorem bodyFunction_aligned {S : List Sig} {params : List Ty} {result : Ty}
    (modes : List Mode) (body : Expr S params result) (placeArgs : body.placeArgs = true)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S) (pf : List Bool)
    (rf : Bool) (hrf : rf = true →
      body.paid flags (entryModes params modes) pf (fun _ => false) = true)
    (m : Module) (pos : Nat) (hm : Runtime m) (hRA : ReleaseAligned m) (hRt : AllocAligned m)
    (hCopy : ∀ host, CopyCodeX true m host)
    (hListFold : ∀ host pv, ListFoldSpecX true m funs flags bounds fits host pv pool)
    (hFunc : m.funcs[pos]? = some (bodyFunction modes body false pos pool))
    (hCovered : body.Covered pool) {d0 : UInt64}
    (hCalls : CallsAtX true m funs flags bounds fits d0 pool) (hDepth : body.depthCalls = false)
    (aborts : Bool)
    (hAborts : (body.aborts || !result.scalar || (paramModes params modes).any (· == .owned)) =
      true → aborts = true) (Fi : Env params → Bool) (D : UInt64 → Prop) :
    FunAligned m ⟨params, result, aborts, modes, false⟩ pos (body.denote funs) pf rf
      (bodyBound modes pf body funs flags bounds) Fi D pool := by
  intro host heap store ws args hAt hInput hRep hSep hCap hHeap hVals d _ rest
  have hRun : RunsA _ host m pos store _ _ := bodyFunction_runsX (strict := true) modes body
    placeArgs false funs flags bounds fits pf rf hrf m pos hm hFunc hCovered d0 (fun _ => hCalls)
    (fun _ => hDepth) aborts (fun h => hAborts (by simpa using h)) host store heap ws args hAt
    hInput hRep hSep hCap (fun _ => hRA) (fun _ => hRt) (hCopy host) (hListFold host)
    (fun _ => ⟨hHeap, hVals⟩)
  have hApp := hRun.append_args (f := bodyFunction modes body false pos pool)
    (by simp [hm.imports]) (by simpa [hm.imports] using hFunc)
    (by simp [hRep.length, bodyFunction_numParams]) rest
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, Bool.false_and,
    Bool.false_or, Bool.or_false] at hApp ⊢
  exact hApp.mono fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop, hAl⟩ =>
    ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, fun _ => hTop trivial, fun _ => hAl trivial⟩

/-- `FunAligned` of a body function whose code takes the call depth, at the depth `d`, as
`bodyFunction_depth` gives its `ImplementsP`. -/
theorem bodyFunction_depthAligned {S : List Sig} {params : List Ty} {result : Ty}
    (modes : List Mode) (body : Expr S params result) (placeArgs : body.placeArgs = true)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S) (pf : List Bool)
    (rf : Bool) (hrf : rf = true →
      body.paid flags (entryModes params modes) pf (fun _ => false) = true)
    (m : Module) (pos : Nat) (hm : Runtime m) (hRA : ReleaseAligned m) (hRt : AllocAligned m)
    (hCopy : ∀ host, CopyCodeX true m host)
    (hListFold : ∀ host pv, ListFoldSpecX true m funs flags bounds fits host pv pool)
    (hFunc : m.funcs[pos]? = some (bodyFunction modes body true pos pool))
    (hCovered : body.Covered pool) (d : UInt64)
    (hCalls : d < depthLimit → CallsAtX true m funs flags bounds fits d pool) (aborts : Bool)
    (Fi : Env params → Bool) (A : Env params → Nat)
    (hFi : ∀ args, Fi args = (decide (d < depthLimit) && body.fits funs fits args))
    (hA : d < depthLimit → ∀ args, A args = bodyBound modes pf body funs flags bounds args) :
    FunAligned m ⟨params, result, aborts, modes, true⟩ pos (body.denote funs) pf rf A Fi
      (fun d' => d' = d) pool := by
  intro host heap store ws args hAt hInput hRep hSep hCap hHeap hVals d' hd rest
  obtain rfl : d' = d := hd rfl
  have hRun : RunsA _ host m pos store _ _ := bodyFunction_runsX (strict := true) modes body
    placeArgs true funs flags bounds fits pf rf hrf m pos hm hFunc hCovered d'
    (fun h => hCalls (h rfl)) nofun true (fun _ => rfl) host store heap ws args hAt hInput hRep
    hSep hCap (fun _ => hRA) (fun _ => hRt) (hCopy host) (hListFold host)
    (fun _ => ⟨hHeap, hVals⟩)
  have hApp := hRun.append_args (f := bodyFunction modes body true pos pool)
    (by simp [hm.imports]) (by simpa [hm.imports] using hFunc)
    (by simp [hRep.length, bodyFunction_numParams]; omega) rest
  simp only [↓reduceIte, List.singleton_append, Bool.true_and] at hApp
  simp only [↓reduceIte, Bool.true_and, Bool.or_true]
  rw [show ws.reverse ++ ([Value.i64 d'] ++ rest) = (Value.i64 d' :: ws).reverse ++ rest by simp]
  refine (hApp.of_imp fun h => ?_).mono
    fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, hTop, hAl⟩ =>
      ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, fun hf => ?_, fun _ => hAl trivial⟩
  · rw [hFi]
    simp only [Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.and_eq_false_iff] at h ⊢
    by_cases hlt : d' < depthLimit
    · rcases h with h | h
      · exact Or.inl (Or.inr (h.resolve_left (by simpa using hlt)))
      · refine Or.inr ?_
        rw [hA hlt]; exact h
    · exact Or.inl (Or.inl (by simpa using hlt))
  · have hFi' : Fi args = true := by simpa using hf
    rw [hFi] at hFi'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hFi'
    rw [hA hFi'.1]
    exact hTop (by simp [hFi'.1, hFi'.2])

end Verified
