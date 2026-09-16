import Project.TinyGpt2Hidden.Normalization
import Project.TinyGpt2Hidden.Attention
import Project.TinyGpt2Hidden.Projection
import Project.TinyGpt2Hidden.Contract
import Project.TinyGpt2Hidden.Embedding
import Project.TinyGpt2Hidden.HiddenModel
import Project.TinyGpt2Hidden.HiddenCode
import Project.ProofKit.ProofStep
import Project.ProofKit.ExactCall

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit HiddenCode

set_option Elab.async false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192

theorem hidden_exact_for (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (weights : Array UInt64) (t0 t1 t2 t3 position : UInt64)
    (expected : Row) (hexpected : hidden weights t0 t1 t2 t3 position = expected)
    (ha : UInt64Array.At initial pointer weights) (hb : 2488 ≤ weights.size)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256) :
    TerminatesWith env Project.TinyGpt2Hidden.module 71 initial
      [.i64 position, .i64 t3, .i64 t2, .i64 t1, .i64 t0, .i64 pointer]
      (fun final values => final = initial ∧
        values = rowResults expected) := by
  proof_step =>
    refine TerminatesWith.of_wp_entry_for (f := func71Def) rfl ?_ (by decide)
    change wp Project.TinyGpt2Hidden.module func71 _ initial
      (func71Def.toLocals [.i64 pointer, .i64 t0, .i64 t1, .i64 t2, .i64 t3, .i64 position]) env
    rw [program_eq]
    unfold tail0
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
    refine wp_call_exact_append (embedding_exact env initial 0 pointer weights t0 0 ha (by omega) ht0 (by decide))
      (f := func8Def) rfl rfl rfl _ rfl ?_
    unfold tail1
    generalize he0 : embedding weights t0 0 = e0
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (embedding_exact env initial 0 pointer weights t1 1 ha (by omega) ht1 (by decide))
      (f := func8Def) rfl rfl rfl _ rfl ?_
    unfold tail2
    generalize he1 : embedding weights t1 1 = e1
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (embedding_exact env initial 0 pointer weights t2 2 ha (by omega) ht2 (by decide))
      (f := func8Def) rfl rfl rfl _ rfl ?_
    unfold tail3
    generalize he2 : embedding weights t2 2 = e2
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (embedding_exact env initial 0 pointer weights t3 3 ha (by omega) ht3 (by decide))
      (f := func8Def) rfl rfl rfl _ rfl ?_
    unfold tail4
    generalize he3 : embedding weights t3 3 = e3
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 18 2464 (some 18) rfl rfl)
      (f := func18Def) rfl rfl rfl _ rfl ?_
    unfold tail5
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2464 e0 ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail6
    generalize hn0 : Project.TinyGpt2.norm weights 2464 e0 = n0
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 18 2464 (some 18) rfl rfl)
      (f := func18Def) rfl rfl rfl _ rfl ?_
    unfold tail7
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2464 e1 ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail8
    generalize hn1 : Project.TinyGpt2.norm weights 2464 e1 = n1
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 18 2464 (some 18) rfl rfl)
      (f := func18Def) rfl rfl rfl _ rfl ?_
    unfold tail9
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2464 e2 ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail10
    generalize hn2 : Project.TinyGpt2.norm weights 2464 e2 = n2
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 18 2464 (some 18) rfl rfl)
      (f := func18Def) rfl rfl rfl _ rfl ?_
    unfold tail11
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2464 e3 ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail12
    generalize hn3 : Project.TinyGpt2.norm weights 2464 e3 = n3
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 27 1040 (some 27) rfl rfl)
      (f := func27Def) rfl rfl rfl _ rfl ?_
    unfold tail13
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (contextRow_exact env initial ⟨n0, n1, n2, n3⟩ position)
      (f := func28Def) rfl rfl rfl _ rfl ?_
    unfold tail14
    generalize hqueryRow : contextRow ⟨n0, n1, n2, n3⟩ position = queryRow
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (project4_exact env initial 0 pointer weights 1040 queryRow ha (by omega))
      (f := func26Def) rfl rfl rfl _ rfl ?_
    unfold tail15
    generalize hquery : project4 weights 1040 queryRow = query
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 30 1056 (some 30) rfl rfl)
      (f := func30Def) rfl rfl rfl _ rfl ?_
    unfold tail16
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (projectContext_exact env initial 0 pointer weights 1056 ⟨n0, n1, n2, n3⟩ ha (by omega))
      (f := func29Def) rfl rfl rfl _ rfl ?_
    unfold tail17
    generalize hkeys : projectContext weights 1056 ⟨n0, n1, n2, n3⟩ = keys
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 31 1072 (some 31) rfl rfl)
      (f := func31Def) rfl rfl rfl _ rfl ?_
    unfold tail18
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (projectContext_exact env initial 0 pointer weights 1072 ⟨n0, n1, n2, n3⟩ ha (by omega))
      (f := func29Def) rfl rfl rfl _ rfl ?_
    unfold tail19
    generalize hvalues : projectContext weights 1072 ⟨n0, n1, n2, n3⟩ = values
    simp only [contextResults, rowResults, List.append_nil, List.cons_append, List.nil_append]
    iterate 6 wp_fixed_frame_step
  proof_step =>
    iterate 6 wp_fixed_frame_step
  proof_step =>
    iterate 6 wp_fixed_frame_step
  proof_step =>
    iterate 6 wp_fixed_frame_step
  proof_step =>
    iterate 6 wp_fixed_frame_step
  proof_step =>
    iterate 6 wp_fixed_frame_step
  proof_step =>
    iterate 6 wp_fixed_frame_step
  proof_step =>
    iterate 6 wp_fixed_frame_step
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (attentionRow_exact env initial (position+1) query keys values)
      (f := func48Def) rfl rfl rfl _ rfl ?_
    unfold tail20
    generalize hattended : attentionRow (position+1) query keys values = attended
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 49 1088 (some 49) rfl rfl)
      (f := func49Def) rfl rfl rfl _ rfl ?_
    unfold tail21
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (project4_exact env initial 0 pointer weights 1088 attended ha (by omega))
      (f := func26Def) rfl rfl rfl _ rfl ?_
    unfold tail22
    generalize hprojected : project4 weights 1088 attended = projected
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 50 1104 (some 50) rfl rfl)
      (f := func50Def) rfl rfl rfl _ rfl ?_
    unfold tail23
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1104 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail24
    generalize habias : loadRow weights 1104 = attentionBias
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 49 1088 (some 49) rfl rfl)
      (f := func49Def) rfl rfl rfl _ rfl ?_
    unfold tail25
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (project4_exact env initial 0 pointer weights 1088 attended ha (by omega))
      (f := func26Def) rfl rfl rfl _ rfl ?_
    unfold tail26
    rw [hprojected]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 50 1104 (some 50) rfl rfl)
      (f := func50Def) rfl rfl rfl _ rfl ?_
    unfold tail27
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1104 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail28
    rw [habias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 49 1088 (some 49) rfl rfl)
      (f := func49Def) rfl rfl rfl _ rfl ?_
    unfold tail29
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (project4_exact env initial 0 pointer weights 1088 attended ha (by omega))
      (f := func26Def) rfl rfl rfl _ rfl ?_
    unfold tail30
    rw [hprojected]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 50 1104 (some 50) rfl rfl)
      (f := func50Def) rfl rfl rfl _ rfl ?_
    unfold tail31
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1104 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail32
    rw [habias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 49 1088 (some 49) rfl rfl)
      (f := func49Def) rfl rfl rfl _ rfl ?_
    unfold tail33
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (project4_exact env initial 0 pointer weights 1088 attended ha (by omega))
      (f := func26Def) rfl rfl rfl _ rfl ?_
    unfold tail34
    rw [hprojected]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 50 1104 (some 50) rfl rfl)
      (f := func50Def) rfl rfl rfl _ rfl ?_
    unfold tail35
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1104 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail36
    rw [habias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (contextRow_exact env initial ⟨e0, e1, e2, e3⟩ position)
      (f := func28Def) rfl rfl rfl _ rfl ?_
    unfold tail37
    generalize hembeddedRow : contextRow ⟨e0, e1, e2, e3⟩ position = embeddedRow
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (addRows_exact env initial embeddedRow (addRows projected attentionBias))
      (f := func4Def) rfl rfl rfl _ rfl ?_
    unfold tail38
    generalize hresidual : addRows embeddedRow (addRows projected attentionBias) = residual
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail39
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail40
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail41
    generalize hnff : Project.TinyGpt2.norm weights 2472 residual = nff
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 0 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail42
    generalize hd0 : dotColumn4 weights 1108 8 0 nff = d0
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail43
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail44
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail45
    rw [hnff]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 1 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail46
    generalize hd1 : dotColumn4 weights 1108 8 1 nff = d1
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail47
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail48
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail49
    rw [hnff]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 2 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail50
    generalize hd2 : dotColumn4 weights 1108 8 2 nff = d2
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail51
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail52
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail53
    rw [hnff]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 3 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail54
    generalize hd3 : dotColumn4 weights 1108 8 3 nff = d3
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail55
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail56
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail57
    rw [hnff]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 4 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail58
    generalize hd4 : dotColumn4 weights 1108 8 4 nff = d4
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail59
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail60
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail61
    rw [hnff]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 5 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail62
    generalize hd5 : dotColumn4 weights 1108 8 5 nff = d5
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail63
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail64
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail65
    rw [hnff]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 6 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail66
    generalize hd6 : dotColumn4 weights 1108 8 6 nff = d6
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 51 1108 (some 51) rfl rfl)
      (f := func51Def) rfl rfl rfl _ rfl ?_
    unfold tail67
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 54 2472 (some 54) rfl rfl)
      (f := func54Def) rfl rfl rfl _ rfl ?_
    unfold tail68
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2472 residual ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail69
    rw [hnff]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (dotColumn4_exact env initial 0 pointer weights 1108 8 7 nff ha (by omega))
      (f := func25Def) rfl rfl rfl _ rfl ?_
    unfold tail70
    generalize hd7 : dotColumn4 weights 1108 8 7 nff = d7
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 52 1140 (some 52) rfl rfl)
      (f := func52Def) rfl rfl rfl _ rfl ?_
    unfold tail71
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1140 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail72
    generalize hlbias : loadRow weights 1140 = lowBias
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 52 1140 (some 52) rfl rfl)
      (f := func52Def) rfl rfl rfl _ rfl ?_
    unfold tail73
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1140 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail74
    rw [hlbias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 52 1140 (some 52) rfl rfl)
      (f := func52Def) rfl rfl rfl _ rfl ?_
    unfold tail75
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1140 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail76
    rw [hlbias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 52 1140 (some 52) rfl rfl)
      (f := func52Def) rfl rfl rfl _ rfl ?_
    unfold tail77
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1140 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail78
    rw [hlbias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    simp only [show (1140:UInt64)+4 = 1144 by decide,
      show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1144 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail79
    generalize hhbias : loadRow weights 1144 = highBias
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    simp only [show (1140:UInt64)+4 = 1144 by decide,
      show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1144 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail80
    rw [hhbias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    simp only [show (1140:UInt64)+4 = 1144 by decide,
      show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1144 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail81
    rw [hhbias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
    refine wp_iff_cons rfl ?_
    simp only [show (1140:UInt64)+4 = 1144 by decide,
      show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (loadRow_exact env initial 0 pointer weights 1144 ha (by omega))
      (f := func5Def) rfl rfl rfl _ rfl ?_
    unfold tail82
    rw [hhbias]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (activate_exact env initial (addRows ⟨d0, d1, d2, d3⟩ lowBias))
      (f := func62Def) rfl rfl rfl _ rfl ?_
    unfold tail83
    generalize hactLow : activate (addRows ⟨d0, d1, d2, d3⟩ lowBias) = actLow
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (activate_exact env initial (addRows ⟨d4, d5, d6, d7⟩ highBias))
      (f := func62Def) rfl rfl rfl _ rfl ?_
    unfold tail84
    generalize hactHigh : activate (addRows ⟨d4, d5, d6, d7⟩ highBias) = actHigh
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (contractRow_exact env initial 0 pointer weights ⟨actLow, actHigh⟩ ha (by omega))
      (f := func69Def) rfl rfl rfl _ rfl ?_
    unfold tail85
    generalize hcontracted : contractRow weights ⟨actLow, actHigh⟩ = contracted
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (contractRow_exact env initial 0 pointer weights ⟨actLow, actHigh⟩ ha (by omega))
      (f := func69Def) rfl rfl rfl _ rfl ?_
    unfold tail86
    rw [hcontracted]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (contractRow_exact env initial 0 pointer weights ⟨actLow, actHigh⟩ ha (by omega))
      (f := func69Def) rfl rfl rfl _ rfl ?_
    unfold tail87
    rw [hcontracted]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (contractRow_exact env initial 0 pointer weights ⟨actLow, actHigh⟩ ha (by omega))
      (f := func69Def) rfl rfl rfl _ rfl ?_
    unfold tail88
    rw [hcontracted]
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (ConstantFunction.exact Project.TinyGpt2Hidden.module env initial 70 2480 (some 70) rfl rfl)
      (f := func70Def) rfl rfl rfl _ rfl ?_
    unfold tail89
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
  proof_step =>
    refine wp_call_exact_append (norm_exact env initial 0 pointer weights 2480 (addRows residual contracted) ha (by omega))
      (f := func17Def) rfl rfl rfl _ rfl ?_
    unfold tail90
    generalize hfinal : TinyGpt2.norm weights 2480 (addRows residual contracted) = finalRow
  proof_step =>
    wp_fixed_frame [func71Def, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
    have hrow : finalRow = expected := hfinal.symm.trans
      ((hidden_of_stages weights t0 t1 t2 t3 position
        he0 he1 he2 he3 hn0 hn1 hn2 hn3 hqueryRow hquery hkeys hvalues hattended hprojected
        habias hembeddedRow hresidual hnff hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hlbias hhbias
        hactLow hactHigh hcontracted).symm.trans hexpected)
    exact ⟨True.intro, congrArg rowResults hrow⟩

theorem hidden_exact (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (weights : Array UInt64) (t0 t1 t2 t3 position : UInt64)
    (ha : UInt64Array.At initial pointer weights) (hb : 2488 ≤ weights.size)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256) :
    TerminatesWith env Project.TinyGpt2Hidden.module 71 initial
      [.i64 position, .i64 t3, .i64 t2, .i64 t1, .i64 t0, .i64 pointer]
      (fun final values => final = initial ∧
        values = rowResults (hidden weights t0 t1 t2 t3 position)) :=
  hidden_exact_for env initial pointer weights t0 t1 t2 t3 position _ rfl ha hb ht0 ht1 ht2 ht3

#print axioms hidden_exact
end Project.TinyGpt2Hidden.Spec
