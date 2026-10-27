import Verified.TailWhile
import Verified.TailEntryFacts
import Verified.TailCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem TailFunc.function_runs {S : List Sig} (func : TailFunc S)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (decreases : func.Decreases funs) (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (m : Module) (pos : Nat) (hm : Runtime m) {pool : Bytes.LiteralPool}
    (hFunc : m.funcs[pos]? = some (func.function (pool := pool) pos))
    (hCovered : func.body.Covered pool) (d : UInt64)
    (hCalls : (func.depth = true → d < depthLimit) → CallsAt m funs flags bounds fits d pool)
    (host : HostEnv Unit) (store : Store Unit) (heap : Heap) (ws : List Value)
    (args : Env func.params) (hAt : heap.At store)
    (hInput : @Bytes.LiteralPool.Input (Env func.params) (Env.represent func.params func.modes)
      pool heap store ws args)
    (hRep : Env.Rep (paramMode func.params func.modes) heap store ws args)
    (hSep : Separate store (Env.moves store (paramMode func.params func.modes) ws args)
      (Env.reads store (paramMode func.params func.modes) ws args))
    (hCap : store.memoryCap m 0 ≤ 65535) :
    Runs ((func.depth && !(decide (d < depthLimit) && func.fits funs fits args)) ||
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
              ws args + func.bound funs flags bounds args) := by
  have hLength := hRep.length
  have hdv : (if func.depth then [Value.i64 d] else []).length = (if func.depth then 1 else 0) := by
    cases func.depth <;> rfl
  have hNum := func.function_numParams (pool := pool) pos
  have hRes : (func.function (pool := pool) pos).results.length = func.result.width := by
    simp only [TailFunc.function, Ty.types_length]
  apply Runs.of_wp_entry_for (f := func.function (pool := pool) pos)
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
  refine wp_guardCode func.depth (d := d) (fun hd => by rw [hd]; simp [Function.toLocals])
    (fun hd hn st => by
      show TrapMsg _ "unreachable"
      simp only [hd, hn, decide_false, Bool.false_and, Bool.not_false, Bool.true_and, Bool.true_or]
      rfl) fun hlt => ?_
  have hCalls' : CallsAt m funs flags bounds fits d pool := hCalls hlt
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
  refine wp_paramCopyCode (func.params.flatMap Ty.types) p0
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
  refine wp_loadCode ws (by rw [flatMap_types_length]; exact hLength) hh1 hold1 ?_
  rw [storeParamsCode_eq]
  refine wp_storeCode ws h (p0 + widthSum func.params) (func.params.flatMap Ty.types) s1 s1.values
    (by rw [flatMap_types_length]; exact hLength) hh1
    (by rw [hp1, hp0, List.length_append, hdv, hLength])
    (by rw [flatMap_types_length, hh1]; omega) fun s2 frame2 hold2 _ => ?_
  refine wp_block_cons ?_
  refine tail_loop_spec hm func decreases meaning fixed
    (TailBody.code_spec m funs flags bounds fits host hm hCalls' func.modes func.body hCovered
      fun hd => ?_)
    h (p0 + widthSum func.params) (p0 + widthSum func.params + widthSum func.params)
    (p0 + widthSum func.params + widthSum func.params + func.result.width) args heap store
    { s2 with values := s1.values } ws (frame2.positions.trans hh1) rfl hRep hSep hold2 hAt hInput hCap
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
    fun heap' store' s' words step frame rep hold top => ?_
  · cases hdepth : func.depth
    · change func.body.depthCalls = false at hdepth
      rw [hdepth] at hd
      exact nomatch hd
    · rw [frame2.params, hp1, hp0]
      exact hHead hdepth
  · simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [← List.append_nil (loadCode h (p0 + widthSum func.params + widthSum func.params)
      func.result.types)]
    refine wp_loadCode words (s := { s' with values := s1.values }) rep.typed
      (frame.positions.trans (frame2.positions.trans hh1)) hold ?_
    rw [wp_nil]
    have hValues : (words.reverse ++ s1.values).take (func.function (pool := pool) pos).results.length ++
        (dv ++ ws).reverse.drop (func.function (pool := pool) pos).numParams = words.reverse := by
      rw [hv1, hv0, hNum, hRes, List.append_nil,
        List.take_of_length_le (by rw [List.length_reverse, rep.length]),
        List.drop_of_length_le (by rw [List.length_reverse, List.length_append, hdv, hLength]),
        List.append_nil]
    simp only [hValues]
    refine ⟨heap', step.at_, ?_, step.caps, ?_, ?_⟩
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

#print axioms TailFunc.function_runs

end Verified
