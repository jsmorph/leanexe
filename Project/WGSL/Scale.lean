import Project.WGSL.Kernel
import Project.WGSL.RoundTrip
import LeanExe.Examples.Binary32

/-!
The kernel of `scale32 a x`, written by hand: invocation `g` stores element `g` of the result
when `g` is below the length of `x`.  `scaleKernel_dispatch` proves that a dispatch of at least
`x.size` invocations leaves the output holding the result as a Wasm array, with distinct
invocations storing to distinct words, and `scaleKernel_text` that the printed text parses to
this kernel.
-/

namespace Project.WGSL

open Project.ProofKit

/-- The kernel of `scale32`: buffer 0 holds `x` as a Wasm array, buffer 1 the word of `a`, and
buffer 2 receives the result's elements. -/
def scaleKernel : Module :=
  { inputs := 2, workgroupSize := 64
    body := [
      .let_ 0 .vec2u (.vec2 .gidX (.lit 0)),
      .let_ 1 .vec2u (.vec2 (.index 0 (.lit 0)) (.index 0 (.lit 1))),
      .ite (.not (lt64 0 1)) [.ret] [],
      .let_ 2 .f32 (.toF32 (.index 1 (.lit 0))),
      .let_ 3 .f32 (.toF32 (readLow 0 0 1)),
      .let_ 4 .f32 (.bin .mul (.var 2) (.var 3)),
      .store 2 (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst 0))) (.toU32 (.var 4)),
      .store 2 (.bin .add (.lit 3) (.bin .mul (.lit 2) (.fst 0))) (.lit 0)] }

/-- What invocation `g` stores: the two words of element `g` when `g` is below the length, and
nothing otherwise. -/
theorem scaleKernel_invoke (a : Float32) (x : Array Float32) (b0 : Array UInt32) (outputSize : Nat)
    (hSize : 2 + 2 * x.size < 2 ^ 32) (hOut : outputSize = 2 + 2 * x.size)
    (h0 : b0[0]? = some (UInt32.ofNat x.size)) (h1 : b0[1]? = some 0)
    (hlen : b0.size = 2 + 2 * x.size)
    (hread : ∀ k, k < x.size → b0[2 + 2 * k]? = some x[k]!.toBits)
    (g : Nat) (hg : g < 2 ^ 32) :
    scaleKernel.invoke [b0, #[a.toBits, 0]] outputSize (UInt32.ofNat g) =
      some (if g < x.size then [(2 + 2 * g, (a * x[g]!).toBits), (3 + 2 * g, 0)] else []) := by
  have hn : x.size < 2 ^ 31 := by omega
  unfold Module.invoke
  simp only [scaleKernel, List.length_cons, List.length_nil, ite_true]
  set ctx : Context := { gid := UInt32.ofNat g, inputs := [b0, #[a.toBits, 0]], outputSize }
    with hctx
  set G := UInt32.ofNat g
  set N := UInt32.ofNat x.size
  have hGN : decide (G < N) = decide (g < x.size) := by
    simp only [G, N, UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat']
    rw [Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt (by omega)]
  let env1 : Env := [(0, .vec2 G 0, false)]
  let env2 : Env := (1, .vec2 N 0, false) :: env1
  have e1 : Stmt.exec ctx ⟨[], [], false⟩ (.let_ 0 .vec2u (.vec2 .gidX (.lit 0))) =
      some ⟨env1, [], false⟩ := by
    simp [Stmt.exec, Expr.eval, Ty.holds, Env.find, ctx, env1, G]
  have e2 : Stmt.exec ctx ⟨env1, [], false⟩
      (.let_ 1 .vec2u (.vec2 (.index 0 (.lit 0)) (.index 0 (.lit 1)))) =
      some ⟨env2, [], false⟩ := by
    simp [Stmt.exec, Expr.eval, Ty.holds, Env.find, ctx, env1, env2, h0, h1, N]
  have hlt := lt64_eval ctx env2 0 1 G N (by simp [Env.find, env2, env1]) (by simp [Env.find, env2])
  have hGnat : G.toNat = g := by simp only [G, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hg
  by_cases hgn : g < x.size
  · let env3 : Env := (2, .f32 a.toBits, false) :: env2
    let env4 : Env := (3, .f32 x[g]!.toBits, false) :: env3
    let env5 : Env := (4, .f32 (Wasm.IEEE32.mul a.toBits x[g]!.toBits), false) :: env4
    have e3 : Stmt.exec ctx ⟨env2, [], false⟩ (.ite (.not (lt64 0 1)) [.ret] []) =
        some ⟨env2, [], false⟩ := by
      simp [Stmt.exec, Expr.eval, hlt, hGN, hgn, Stmt.execList]
    have e4 : Stmt.exec ctx ⟨env2, [], false⟩ (.let_ 2 .f32 (.toF32 (.index 1 (.lit 0)))) =
        some ⟨env3, [], false⟩ := by
      simp [Stmt.exec, Expr.eval, Ty.holds, Env.find, ctx, env1, env2, env3]
    have hread3 := readLow_eval ctx env3 0 0 1 G x.size b0 (by simp [ctx]) hlen hn
      (by simp [Env.find, env3, env2, env1]) (by simp [Env.find, env3, env2, N])
    have hb : b0[2 + 2 * g]! = x[g]!.toBits := by
      rw [getElem!_pos b0 _ (by omega)]
      have := hread g hgn
      rw [Array.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    have e5 : Stmt.exec ctx ⟨env3, [], false⟩ (.let_ 3 .f32 (.toF32 (readLow 0 0 1))) =
        some ⟨env4, [], false⟩ := by
      simp [Stmt.exec, Expr.eval, hread3, hGnat, hgn, hb, Ty.holds, Env.find, env4, env3, env2,
        env1]
    have e6 : Stmt.exec ctx ⟨env4, [], false⟩ (.let_ 4 .f32 (.bin .mul (.var 2) (.var 3))) =
        some ⟨env5, [], false⟩ := by
      simp [Stmt.exec, Expr.eval, Env.find, BinOp.apply, Ty.holds, env5, env4, env3, env2, env1]
    have hpos2 : (2 + 2 * G).toNat = 2 + 2 * g := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, hGnat]; simp only [UInt32.reduceToNat]; omega
    have hpos3 : (3 + 2 * G).toNat = 3 + 2 * g := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, hGnat]; simp only [UInt32.reduceToNat]; omega
    have e7 : Stmt.exec ctx ⟨env5, [], false⟩
        (.store 2 (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst 0))) (.toU32 (.var 4))) =
        some ⟨env5, [(2 + 2 * g, Wasm.IEEE32.mul a.toBits x[g]!.toBits)], false⟩ := by
      simp [Stmt.exec, Expr.eval, Env.find, BinOp.apply, ctx, hpos2, hOut, env5, env4, env3,
        env2, env1]
      omega
    have e8 : Stmt.exec ctx ⟨env5, [(2 + 2 * g, Wasm.IEEE32.mul a.toBits x[g]!.toBits)], false⟩
        (.store 2 (.bin .add (.lit 3) (.bin .mul (.lit 2) (.fst 0))) (.lit 0)) =
        some ⟨env5, [(2 + 2 * g, Wasm.IEEE32.mul a.toBits x[g]!.toBits), (3 + 2 * g, 0)],
          false⟩ := by
      simp [Stmt.exec, Expr.eval, Env.find, BinOp.apply, ctx, hpos3, hOut, env5, env4, env3,
        env2, env1]
      omega
    simp only [Stmt.execList, Bool.false_eq_true, ite_false, e1, e2, e3, e4, e5, e6, e7, e8,
      Option.bind_eq_bind, Option.bind_some, Option.map_some, hgn, ite_true, F32Bits.toBits_mul]
  · have e3 : Stmt.exec ctx ⟨env2, [], false⟩ (.ite (.not (lt64 0 1)) [.ret] []) =
        some ⟨env2, [], true⟩ := by
      simp [Stmt.exec, Expr.eval, hlt, hGN, hgn, Stmt.execList]
    simp [Stmt.execList, e1, e2, e3, hgn]

/-- Word `i` of the output once the invocations below `k` have stored their elements. -/
def scaleWord (a : Float32) (x : Array Float32) (output : Array UInt32) (k i : Nat) : Option UInt32 :=
  if 2 ≤ i ∧ (i - 2) / 2 < k ∧ (i - 2) / 2 < x.size then
    some (if i % 2 = 0 then (a * x[(i - 2) / 2]!).toBits else 0)
  else output[i]?

theorem scale_fold (a : Float32) (x : Array Float32) (output : Array UInt32)
    (hOut : output.size = 2 + 2 * x.size) :
    ∀ k, ∀ i, ((List.range k).foldl (fun out g => applyWrites out
      (if g < x.size then [(2 + 2 * g, (a * x[g]!).toBits), (3 + 2 * g, 0)] else []))
      output)[i]? = scaleWord a x output k i ∧
      ((List.range k).foldl (fun out g => applyWrites out
        (if g < x.size then [(2 + 2 * g, (a * x[g]!).toBits), (3 + 2 * g, 0)] else []))
        output).size = output.size := by
  intro k
  induction k with
  | zero => intro i; simp [scaleWord]
  | succ k ih =>
      intro i
      rw [List.range_succ, List.foldl_append]
      have hsize := (ih 0).2
      have hi := (ih i).1
      simp only [List.foldl_cons, List.foldl_nil]
      generalize (List.range k).foldl _ output = out at hi hsize
      by_cases hk : k < x.size
      · simp only [hk, ite_true, applyWrites, List.foldl_cons, List.foldl_nil]
        refine ⟨?_, by simp [hsize]⟩
        rw [Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_setIfInBounds,
          hsize, hi]
        unfold scaleWord
        by_cases h3 : 3 + 2 * k = i
        · subst h3
          rw [if_pos rfl, if_pos (by omega), if_pos (by omega), if_neg (by omega)]
        · rw [if_neg h3]
          by_cases h2 : 2 + 2 * k = i
          · subst h2
            have hd : (2 + 2 * k - 2) / 2 = k := by omega
            rw [if_pos rfl, if_pos (by omega), if_pos (by omega), hd, if_pos (by omega)]
          · rw [if_neg h2]
            by_cases hc : 2 ≤ i ∧ (i - 2) / 2 < k ∧ (i - 2) / 2 < x.size
            · rw [if_pos hc, if_pos (show 2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < x.size by omega)]
            · rw [if_neg hc,
                if_neg (show ¬(2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < x.size) by omega)]
      · simp only [hk, ite_false, applyWrites, List.foldl_nil]
        refine ⟨?_, hsize⟩
        rw [hi]
        unfold scaleWord
        by_cases hc : 2 ≤ i ∧ (i - 2) / 2 < k ∧ (i - 2) / 2 < x.size
        · rw [if_pos hc, if_pos (show 2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < x.size by omega)]
        · rw [if_neg hc,
            if_neg (show ¬(2 ≤ i ∧ (i - 2) / 2 < k + 1 ∧ (i - 2) / 2 < x.size) by omega)]

/-- The kernel computes `scale32 a x`: on buffers that hold `x` as a Wasm array and `a`'s word,
with an output of the result's size whose length word the host has written, `count ≥ x.size`
invocations leave the output holding the result as a Wasm array, and distinct invocations store
to distinct words. -/
theorem scaleKernel_dispatch (a : Float32) (x : Array Float32) (output : Array UInt32)
    (hSize : 2 + 2 * x.size < 2 ^ 32) (hOut : output.size = 2 + 2 * x.size)
    (hL0 : output[0]? = some (UInt32.ofNat x.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCount : x.size ≤ count) (hCount32 : count ≤ 2 ^ 32) :
    scaleKernel.dispatch [arrayWords (x.map fun v => v.toBits.toUInt64), #[a.toBits, 0]] output
        count = some (arrayWords ((LeanExe.Examples.Binary32.scale32 a x).map
          fun v => v.toBits.toUInt64)) ∧
      scaleKernel.RaceFree [arrayWords (x.map fun v => v.toBits.toUInt64), #[a.toBits, 0]]
        output.size count := by
  obtain ⟨h0, h1, hlen, hread⟩ := arrayWords_floats x hSize
  have hinv := fun g (hg : g < 2 ^ 32) =>
    scaleKernel_invoke a x _ output.size hSize hOut h0 h1 hlen hread g hg
  refine ⟨?_, ?_⟩
  · unfold Module.dispatch
    rw [foldlM_some _ (fun out g => applyWrites out
      (if g < x.size then [(2 + 2 * g, (a * x[g]!).toBits), (3 + 2 * g, 0)] else []))
      (List.range count) (fun b g hg => by
        rw [hinv g (by simp at hg; omega)]; rfl)]
    congr 1
    apply Array.ext_getElem?
    intro i
    rw [(scale_fold a x output hOut count i).1]
    have hres : ∀ k, k < x.size →
        ((LeanExe.Examples.Binary32.scale32 a x).map fun v => v.toBits.toUInt64)[k]! =
          (a * x[k]!).toBits.toUInt64 := by
      intro k hk
      have hk' : k < (LeanExe.Examples.Binary32.scale32 a x).size := by
        simp [LeanExe.Examples.Binary32.scale32, LeanExe.build]; omega
      have hk64 : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
      rw [getElem!_pos _ k (by simpa using hk')]
      simp [LeanExe.Examples.Binary32.scale32, LeanExe.build, hk64]
    have hrsize : (LeanExe.Examples.Binary32.scale32 a x).size = x.size := by
      simp [LeanExe.Examples.Binary32.scale32, LeanExe.build]; omega
    unfold scaleWord
    by_cases hi : i < 2 + 2 * x.size
    · rw [arrayWords_get _ _ (by simp [hrsize]; omega)]
      by_cases hi2 : i < 2
      · rw [if_neg (by omega), if_pos hi2]
        simp only [Array.size_map, hrsize, wordHalf]
        interval_cases i
        · simp [hL0]
        · simp only [hL1, if_pos (show (1 : Nat) = 1 from rfl)]
          congr 1
          apply UInt32.toNat_inj.mp
          simp [UInt64.toNat_shiftRight]
          omega
      · rw [if_pos (show 2 ≤ i ∧ (i - 2) / 2 < count ∧ (i - 2) / 2 < x.size by omega), if_neg hi2,
          hres _ (by omega)]
        by_cases hev : i % 2 = 0
        · simp [hev, wordHalf]
        · have : i % 2 = 1 := by omega
          simp [hev, this, wordHalf]
          apply UInt32.toNat_inj.mp
          simp [UInt64.toNat_shiftRight]
          have := (a * x[(i - 2) / 2]!).toBits.toNat_lt
          omega
    · rw [if_neg (show ¬(2 ≤ i ∧ (i - 2) / 2 < count ∧ (i - 2) / 2 < x.size) by omega),
        Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by simp [arrayWords_size, hrsize]; omega)]
  · intro g h hg hh hgh wg wh hwg hwh
    rw [hinv g (by omega)] at hwg
    rw [hinv h (by omega)] at hwh
    cases hwg
    cases hwh
    intro p hp q hq
    split at hp <;> split at hq <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    · rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp <;> omega
    all_goals exact hp.elim <|> exact hq.elim

theorem scaleKernel_wf : scaleKernel.WF := by
  simp [Module.WF, Stmt.ListWF, Stmt.WF, Expr.WF, scaleKernel, lt64, readLow]

/-- The printed text of the kernel parses to the kernel. -/
theorem scaleKernel_text : Module.parse scaleKernel.print = some scaleKernel :=
  Module.parse_print scaleKernel scaleKernel_wf

end Project.WGSL
