import Verified.AlignedListFold
import Verified.AlignedFunction
import Verified.TailEntry

/-!
The code and the run of a tail function under the flag.  `TailBody.code_specX` proves
`TailCodeSpecX` of every tail body from `Expr.code_specX`.  `TailFunc.function_runsX` is
`TailFunc.function_runs` with `RunsX` for `Runs`: from an aligned heap and aligned arguments, the
run of a tail function makes only aligned 64-bit accesses, and it ends with an aligned heap and
an aligned owned result.
Each theorem is its original with the flagged constructs and rules and the alignment premises.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem TailBody.code_specX {strict : Bool} {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit) (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hRt : strict = true → AllocAligned m)
    (hCopy : CopyCodeX strict m host) {pv : List Value}
    {d0 : UInt64} {pool : Bytes.LiteralPool}
    (hCalls : CallsAtX strict m funs flags bounds fits d0 pool) {Γ params : List Ty}
    {result : Ty} (targetModes : List Mode) (body : TailBody S params result Γ) :
    body.Covered pool →
    (body.depthCalls = true → pv.head? = some (.i64 d0)) →
    TailCodeSpecX strict m funs flags bounds fits host pv targetModes body pool := by
  induction body with
  | ret value =>
    intro hCovered hDepth
    exact tail_ret_specX hm hCopy targetModes value
      (Expr.code_specX m funs flags bounds fits host hm hRA hRt hCopy hCalls value hCovered hDepth)
  | next args =>
    intro hCovered hDepth
    have hArgs : ∀ i, (args i).Covered pool :=
      (literals_args_subset.mp hCovered)
    exact tail_next_specX hm hRA hCopy targetModes args fun i =>
      Expr.code_specX m funs flags bounds fits host hm hRA hRt hCopy hCalls (args i) (hArgs i) fun hd =>
        hDepth (le_argsAny _ i hd)
  | ite cond yes no yesSpec noSpec =>
    intro hCovered hDepth
    have hParts : (cond.Covered pool ∧ yes.Covered pool) ∧ no.Covered pool := by
      simpa only [TailBody.Covered, TailBody.literals_ite, TailBody.literals_letE,
        TailBody.literals_letPair, Expr.Covered, List.append_subset,
        and_assoc] using hCovered
    exact tail_ite_specX hm hRA targetModes cond yes no
      (Expr.code_specX m funs flags bounds fits host hm hRA hRt hCopy hCalls cond hParts.1.1 fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (yesSpec hParts.1.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
      (noSpec hParts.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | letE value body bodySpec =>
    intro hCovered hDepth
    have hParts : value.Covered pool ∧ body.Covered pool := by
      simpa only [TailBody.Covered, TailBody.literals_ite, TailBody.literals_letE,
        TailBody.literals_letPair, Expr.Covered, List.append_subset] using hCovered
    exact tail_let_specX hm hRA targetModes value body
      (Expr.code_specX m funs flags bounds fits host hm hRA hRt hCopy hCalls value hParts.1 fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (bodySpec hParts.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | letPair value body bodySpec =>
    intro hCovered hDepth
    have hParts : value.Covered pool ∧ body.Covered pool := by
      simpa only [TailBody.Covered, TailBody.literals_ite, TailBody.literals_letE,
        TailBody.literals_letPair, Expr.Covered, List.append_subset] using hCovered
    exact tail_letPair_specX hm hRA targetModes value body
      (Expr.code_specX m funs flags bounds fits host hm hRA hRt hCopy hCalls value hParts.1 fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (bodySpec hParts.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | treeCase x empty nodes emptySpec nodesSpec =>
    intro hCovered hDepth
    have hParts := List.append_subset.mp hCovered
    exact tail_treeCase_specX hm hRA hCopy targetModes x empty nodes
      (fun hn => emptySpec hn (by
          have hEmpty := hParts.1
          rw [dif_pos hn] at hEmpty
          exact hEmpty)
        fun hd => hDepth (by simp [TailBody.depthCalls, hn, hd]))
      (fun r => nodesSpec r (literals_args_subset.mp hParts.2 r) fun hd => hDepth (by
        simp [TailBody.depthCalls, le_argsAny (fun r => (nodes r).depthCalls) r hd]))

theorem TailFunc.function_runsX {strict : Bool} {S : List Sig} (func : TailFunc S)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (decreases : func.Decreases funs) (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (m : Module) (pos : Nat) (hm : Runtime m) {pool : Bytes.LiteralPool}
    (hFunc : m.funcs[pos]? = some (func.function (pool := pool) pos))
    (hCovered : func.body.Covered pool) (d : UInt64)
    (hCalls : (func.depth = true → d < depthLimit) → CallsAtX strict m funs flags bounds fits d pool)
    (host : HostEnv Unit) (store : Store Unit) (heap : Heap) (ws : List Value)
    (args : Env func.params) (hAt : heap.At store)
    (hInput : @Bytes.LiteralPool.Input (Env func.params) (Env.represent func.params func.modes)
      pool heap store ws args)
    (hRep : Env.Rep (paramMode func.params func.modes) heap store ws args)
    (hSep : Separate store (Env.moves store (paramMode func.params func.modes) ws args)
      (Env.reads store (paramMode func.params func.modes) ws args))
    (hCap : store.memoryCap m 0 ≤ 65535) (hRA : strict = true → ReleaseAligned m)
    (hRt : strict = true → AllocAligned m) (hCopy : CopyCodeX strict m host)
    (hAl : strict = true →
      heap.Aligned ∧ Env.AlignedVals store (paramMode func.params func.modes) ws args) :
    RunsX strict ((func.depth && !(decide (d < depthLimit) && func.fits funs fits args)) ||
      (func.aborts && !decide (heap.Within store m
        (Env.argPot store (fun i => paidAt (func.paidParams flags) i &&
          paramMode func.params func.modes i == .owned) ws args +
            func.bound funs flags bounds args))))
      host m pos store ((if func.depth then [Value.i64 d] else []) ++ ws).reverse
      fun final values => ∃ heap' : Heap, heap'.At final ∧
        func.result.Rep .owned heap' final values.reverse (meaning args) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 →
          Apart store (Env.moves store (paramMode func.params func.modes) ws args) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
          heap'.Region r ∧
          ∀ b ∈ func.result.blocks final values.reverse (meaning args), regionsDisjoint r b) ∧
        ((func.depth && !(decide (d < depthLimit) && func.fits funs fits args)) = false →
          heap'.top.toNat + (if func.paidResult flags then
            func.result.pot final values.reverse (meaning args) else 0) ≤
            heap.top.toNat + Env.argPot store
              (fun i => paidAt (func.paidParams flags) i && paramMode func.params func.modes i == .owned)
              ws args + func.bound funs flags bounds args) ∧
        (strict = true → heap'.Aligned ∧
          Ty.AlignedVal .owned final func.result values.reverse (meaning args)) := by
  have hLength := hRep.length
  have hdv : (if func.depth then [Value.i64 d] else []).length = (if func.depth then 1 else 0) := by
    cases func.depth <;> rfl
  have hNum := func.function_numParams (pool := pool) pos
  have hRes : (func.function (pool := pool) pos).results.length = func.result.width := by
    simp only [TailFunc.function, Ty.types_length]
  apply RunsX.of_wpX_entry_for (f := func.function (pool := pool) pos)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact hFunc)
    (hImp := by simp [hm.imports])
  have hTake : (((if func.depth then [Value.i64 d] else []) ++ ws).reverse.take
      (func.function (pool := pool) pos).numParams).reverse =
      (if func.depth then [Value.i64 d] else []) ++ ws := by
    rw [List.take_of_length_le (by rw [hNum, List.length_reverse, List.length_append, hdv, hLength])]
    exact List.reverse_reverse _
  rw [hTake, show (func.function (pool := pool) pos).body =
    (if func.depth then guardCode else []) ++
      (paramCopyCode func.positions (if func.depth then 1 else 0) (func.params.flatMap Ty.types) ++
      (loadCode func.positions (if func.depth then 1 else 0) (func.params.flatMap Ty.types) ++
      (storeParamsCode func.positions ((if func.depth then 1 else 0) + widthSum func.params)
        func.params ++
      ([.block 0 0 [.loop 0 0
        (releaseWhere func.params
          (paramSlots func.params func.modes ((if func.depth then 1 else 0) + widthSum func.params))
          (fun i => !func.body.usesFast i) ++
        func.body.code (pool := pool) func.modes func.positions
          ((if func.depth then 1 else 0) + widthSum func.params)
          ((if func.depth then 1 else 0) + widthSum func.params + widthSum func.params)
          (paramSlots func.params func.modes ((if func.depth then 1 else 0) + widthSum func.params))
          ((if func.depth then 1 else 0) + widthSum func.params + widthSum func.params + func.result.width)
          1 0) [] []] [] []] ++
      loadCode func.positions
        ((if func.depth then 1 else 0) + widthSum func.params + widthSum func.params)
        func.result.types)))) by simp only [TailFunc.function, List.append_assoc]]
  have hl0 : ((func.function (pool := pool) pos).toLocals
      ((if func.depth then [Value.i64 d] else []) ++ ws)).locals.length =
      widthSum func.params + func.result.width + func.body.width func.modes +
        func.positions + func.positions := by
    simp only [Function.toLocals, TailFunc.function, List.length_map, List.length_append,
      List.length_replicate, Nat.add_assoc]
  have hHead : func.depth = true →
      ((if func.depth then [Value.i64 d] else []) ++ ws).head? = some (.i64 d) := by
    intro hd
    rw [hd]
    rfl
  refine wpX_guardCode func.depth (d := d) (fun hd => by rw [hd]; simp [Function.toLocals])
    (fun hd hn st => by
      show TrapMsg _ "unreachable"
      simp only [hd, hn, decide_false, Bool.false_and, Bool.not_false, Bool.true_and, Bool.true_or]
      rfl) fun hlt => ?_
  have hCalls' : CallsAtX strict m funs flags bounds fits d pool := hCalls hlt
  have hFits : (func.depth && !(decide (d < depthLimit) && func.fits funs fits args)) = false →
      func.fits funs fits args = true := by
    intro hf
    cases hd : func.depth
    · exact func.fits_of_depthCalls funs fits decreases hd args
    · simp only [hd, Bool.true_and, Bool.not_eq_false', Bool.and_eq_true] at hf
      exact hf.2
  have hPos : func.positions = (if func.depth then 1 else 0) +
      2 * widthSum func.params + func.result.width + func.body.width func.modes := rfl
  have hp0 : ((func.function (pool := pool) pos).toLocals
      ((if func.depth then [Value.i64 d] else []) ++ ws)).params =
      (if func.depth then [Value.i64 d] else []) ++ ws := rfl
  have hv0 : ((func.function (pool := pool) pos).toLocals
      ((if func.depth then [Value.i64 d] else []) ++ ws)).values = [] := rfl
  generalize (func.function (pool := pool) pos).toLocals
    ((if func.depth then [Value.i64 d] else []) ++ ws) = s0 at hl0 hp0 hv0 ⊢
  generalize (if func.depth then 1 else 0) = p0 at hdv hNum hPos ⊢
  generalize (if func.depth then [Value.i64 d] else []) = dv at hdv hHead hp0 ⊢
  generalize func.positions = h at hPos hl0 ⊢
  have hLocals : s0.params.length + s0.locals.length = h + h + h := by
    rw [hp0, hl0, List.length_append, hdv, hLength]
    omega
  refine wpX_paramCopyCode (func.params.flatMap Ty.types) p0
    (by rw [flatMap_types_length, hp0, List.length_append, hdv, hLength])
    (by rw [hp0, List.length_append, hdv, hLength]; omega)
    (by simp only [Locals.positions, hLocals]; omega)
    fun s1 frame1 hv1 copy1 => ?_
  have hp1 := frame1.params
  have hh1 : s1.positions = h := by
    rw [frame1.positions, Locals.positions, hLocals]; omega
  have hParam : ∀ j (hj : j < ws.length), s0.get (p0 + j) = some ws[j] := by
    intro j hj
    have hlt : p0 + j < (dv ++ ws).length := by rw [List.length_append, hdv]; omega
    simp only [Locals.get, hp0, hlt, ↓reduceIte]
    rw [List.getElem?_append_right (by omega), hdv, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj]
  have hold1 := LocalsHold.afterParamCopy
    (tys := func.params.flatMap Ty.types) (by rw [flatMap_types_length]; exact hLength)
    hh1 hParam copy1
  refine wpX_loadCode ws (by rw [flatMap_types_length]; exact hLength) hh1 hold1 ?_
  rw [storeParamsCode_eq]
  refine wpX_storeCode ws h (p0 + widthSum func.params) (func.params.flatMap Ty.types) s1 s1.values
    (by rw [flatMap_types_length]; exact hLength) hh1
    (by rw [hp1, hp0, List.length_append, hdv, hLength])
    (by rw [flatMap_types_length, hh1]; omega) fun s2 frame2 hold2 _ => ?_
  refine wpX_block_cons ?_
  refine tail_loop_specX hm hRA func decreases meaning fixed
    (TailBody.code_specX m funs flags bounds fits host hm hRA hRt hCopy hCalls' func.modes func.body hCovered
      fun hd => ?_)
    h (p0 + widthSum func.params) (p0 + widthSum func.params + widthSum func.params)
    (p0 + widthSum func.params + widthSum func.params + func.result.width) args heap store
    { s2 with values := s1.values } ws (frame2.positions.trans hh1) rfl hRep hSep hold2 hAt hAl hInput hCap
    (by change s2.params.length ≤ p0 + widthSum func.params
        rw [frame2.params, hp1, hp0, List.length_append, hdv, hLength])
    le_rfl le_rfl (by omega) _
    ((TrapOK.of_msg fun _ => Iff.rfl).of_imp fun hb => by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hb ⊢
      rcases hb with hb | hb
      · have hd : func.depth = true := by
          cases hd : func.depth
          · have ht := func.fits_of_depthCalls funs fits decreases hd args
            simp [ht] at hb
          · rfl
        simp only [Bool.not_eq_true'] at hb
        exact Or.inl ⟨hd, by simp [hb]⟩
      · exact Or.inr hb)
    fun heap' store' s' words step frame rep hold hAlR top => ?_
  · cases hdepth : func.depth
    · change func.body.depthCalls = false at hdepth
      rw [hdepth] at hd
      exact nomatch hd
    · rw [frame2.params, hp1, hp0]
      exact hHead hdepth
  · simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [← List.append_nil (loadCode h (p0 + widthSum func.params + widthSum func.params)
      func.result.types)]
    refine wpX_loadCode words (s := { s' with values := s1.values }) rep.typed
      (frame.positions.trans (frame2.positions.trans hh1)) hold ?_
    rw [wpX_nil]
    have hValues : (words.reverse ++ s1.values).take (func.function (pool := pool) pos).results.length ++
        (dv ++ ws).reverse.drop (func.function (pool := pool) pos).numParams = words.reverse := by
      rw [hv1, hv0, hNum, hRes, List.append_nil,
        List.take_of_length_le (by rw [List.length_reverse, rep.length]),
        List.drop_of_length_le (by rw [List.length_reverse, List.length_append, hdv, hLength]),
        List.append_nil]
    simp only [hValues]
    refine ⟨heap', step.at_, ?_, step.caps, ?_, ?_, ?_⟩
    · rw [List.reverse_reverse]
      exact rep
    · intro r hr hpos hApart
      obtain ⟨bytes, region, outside⟩ := step.keeps r hr hpos hApart
      refine ⟨bytes, region, ?_⟩
      rw [List.reverse_reverse]
      exact outside
    · intro hf
      rw [List.reverse_reverse]
      exact top (hFits hf)
    · intro hs
      rw [List.reverse_reverse]
      exact hAlR hs

end Verified
