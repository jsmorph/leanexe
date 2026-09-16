import Project.TinyGpt2Hidden.Normalization
import Project.TinyGpt2Hidden.Attention
import Project.TinyGpt2Hidden.Projection
import Project.TinyGpt2Hidden.Contract
import Project.TinyGpt2Hidden.Embedding
import Project.TinyGpt2Hidden.HiddenModel
import Project.ProofKit.ProofStep
import Project.ProofKit.ExactCall

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

syntax "tiny_hidden_steps " ident ident "(" term ")" "(" term ")"
  "[" ident,* "]" "[" ident,* "]" : tactic

macro_rules
  | `(tactic| tiny_hidden_steps $target:ident $codeNamespace:ident ($transfer:term) ($ownerValue:term)
      [$env:ident, $initial:ident, $pointer:ident, $weights:ident, $t0:ident, $t1:ident, $t2:ident, $t3:ident, $position:ident, $expected:ident, $hexpected:ident]
      [$ha:ident, $hb:ident, $ht0:ident, $ht1:ident, $ht2:ident, $ht3:ident]) => do
    let targetModule := Lean.mkIdent (target.getId ++ `module)
    let func17Def := Lean.mkIdent (target.getId ++ `func17Def)
    let func18Def := Lean.mkIdent (target.getId ++ `func18Def)
    let func25Def := Lean.mkIdent (target.getId ++ `func25Def)
    let func26Def := Lean.mkIdent (target.getId ++ `func26Def)
    let func27Def := Lean.mkIdent (target.getId ++ `func27Def)
    let func28Def := Lean.mkIdent (target.getId ++ `func28Def)
    let func29Def := Lean.mkIdent (target.getId ++ `func29Def)
    let func30Def := Lean.mkIdent (target.getId ++ `func30Def)
    let func31Def := Lean.mkIdent (target.getId ++ `func31Def)
    let func48Def := Lean.mkIdent (target.getId ++ `func48Def)
    let func49Def := Lean.mkIdent (target.getId ++ `func49Def)
    let func4Def := Lean.mkIdent (target.getId ++ `func4Def)
    let func50Def := Lean.mkIdent (target.getId ++ `func50Def)
    let func51Def := Lean.mkIdent (target.getId ++ `func51Def)
    let func52Def := Lean.mkIdent (target.getId ++ `func52Def)
    let func54Def := Lean.mkIdent (target.getId ++ `func54Def)
    let func5Def := Lean.mkIdent (target.getId ++ `func5Def)
    let func62Def := Lean.mkIdent (target.getId ++ `func62Def)
    let func69Def := Lean.mkIdent (target.getId ++ `func69Def)
    let func70Def := Lean.mkIdent (target.getId ++ `func70Def)
    let func71Def := Lean.mkIdent (target.getId ++ `func71Def)
    let func8Def := Lean.mkIdent (target.getId ++ `func8Def)
    let tail1 := Lean.mkIdent (codeNamespace.getId ++ `tail1)
    let tail2 := Lean.mkIdent (codeNamespace.getId ++ `tail2)
    let tail3 := Lean.mkIdent (codeNamespace.getId ++ `tail3)
    let tail4 := Lean.mkIdent (codeNamespace.getId ++ `tail4)
    let tail5 := Lean.mkIdent (codeNamespace.getId ++ `tail5)
    let tail6 := Lean.mkIdent (codeNamespace.getId ++ `tail6)
    let tail7 := Lean.mkIdent (codeNamespace.getId ++ `tail7)
    let tail8 := Lean.mkIdent (codeNamespace.getId ++ `tail8)
    let tail9 := Lean.mkIdent (codeNamespace.getId ++ `tail9)
    let tail10 := Lean.mkIdent (codeNamespace.getId ++ `tail10)
    let tail11 := Lean.mkIdent (codeNamespace.getId ++ `tail11)
    let tail12 := Lean.mkIdent (codeNamespace.getId ++ `tail12)
    let tail13 := Lean.mkIdent (codeNamespace.getId ++ `tail13)
    let tail14 := Lean.mkIdent (codeNamespace.getId ++ `tail14)
    let tail15 := Lean.mkIdent (codeNamespace.getId ++ `tail15)
    let tail16 := Lean.mkIdent (codeNamespace.getId ++ `tail16)
    let tail17 := Lean.mkIdent (codeNamespace.getId ++ `tail17)
    let tail18 := Lean.mkIdent (codeNamespace.getId ++ `tail18)
    let tail19 := Lean.mkIdent (codeNamespace.getId ++ `tail19)
    let tail20 := Lean.mkIdent (codeNamespace.getId ++ `tail20)
    let tail21 := Lean.mkIdent (codeNamespace.getId ++ `tail21)
    let tail22 := Lean.mkIdent (codeNamespace.getId ++ `tail22)
    let tail23 := Lean.mkIdent (codeNamespace.getId ++ `tail23)
    let tail24 := Lean.mkIdent (codeNamespace.getId ++ `tail24)
    let tail25 := Lean.mkIdent (codeNamespace.getId ++ `tail25)
    let tail26 := Lean.mkIdent (codeNamespace.getId ++ `tail26)
    let tail27 := Lean.mkIdent (codeNamespace.getId ++ `tail27)
    let tail28 := Lean.mkIdent (codeNamespace.getId ++ `tail28)
    let tail29 := Lean.mkIdent (codeNamespace.getId ++ `tail29)
    let tail30 := Lean.mkIdent (codeNamespace.getId ++ `tail30)
    let tail31 := Lean.mkIdent (codeNamespace.getId ++ `tail31)
    let tail32 := Lean.mkIdent (codeNamespace.getId ++ `tail32)
    let tail33 := Lean.mkIdent (codeNamespace.getId ++ `tail33)
    let tail34 := Lean.mkIdent (codeNamespace.getId ++ `tail34)
    let tail35 := Lean.mkIdent (codeNamespace.getId ++ `tail35)
    let tail36 := Lean.mkIdent (codeNamespace.getId ++ `tail36)
    let tail37 := Lean.mkIdent (codeNamespace.getId ++ `tail37)
    let tail38 := Lean.mkIdent (codeNamespace.getId ++ `tail38)
    let tail39 := Lean.mkIdent (codeNamespace.getId ++ `tail39)
    let tail40 := Lean.mkIdent (codeNamespace.getId ++ `tail40)
    let tail41 := Lean.mkIdent (codeNamespace.getId ++ `tail41)
    let tail42 := Lean.mkIdent (codeNamespace.getId ++ `tail42)
    let tail43 := Lean.mkIdent (codeNamespace.getId ++ `tail43)
    let tail44 := Lean.mkIdent (codeNamespace.getId ++ `tail44)
    let tail45 := Lean.mkIdent (codeNamespace.getId ++ `tail45)
    let tail46 := Lean.mkIdent (codeNamespace.getId ++ `tail46)
    let tail47 := Lean.mkIdent (codeNamespace.getId ++ `tail47)
    let tail48 := Lean.mkIdent (codeNamespace.getId ++ `tail48)
    let tail49 := Lean.mkIdent (codeNamespace.getId ++ `tail49)
    let tail50 := Lean.mkIdent (codeNamespace.getId ++ `tail50)
    let tail51 := Lean.mkIdent (codeNamespace.getId ++ `tail51)
    let tail52 := Lean.mkIdent (codeNamespace.getId ++ `tail52)
    let tail53 := Lean.mkIdent (codeNamespace.getId ++ `tail53)
    let tail54 := Lean.mkIdent (codeNamespace.getId ++ `tail54)
    let tail55 := Lean.mkIdent (codeNamespace.getId ++ `tail55)
    let tail56 := Lean.mkIdent (codeNamespace.getId ++ `tail56)
    let tail57 := Lean.mkIdent (codeNamespace.getId ++ `tail57)
    let tail58 := Lean.mkIdent (codeNamespace.getId ++ `tail58)
    let tail59 := Lean.mkIdent (codeNamespace.getId ++ `tail59)
    let tail60 := Lean.mkIdent (codeNamespace.getId ++ `tail60)
    let tail61 := Lean.mkIdent (codeNamespace.getId ++ `tail61)
    let tail62 := Lean.mkIdent (codeNamespace.getId ++ `tail62)
    let tail63 := Lean.mkIdent (codeNamespace.getId ++ `tail63)
    let tail64 := Lean.mkIdent (codeNamespace.getId ++ `tail64)
    let tail65 := Lean.mkIdent (codeNamespace.getId ++ `tail65)
    let tail66 := Lean.mkIdent (codeNamespace.getId ++ `tail66)
    let tail67 := Lean.mkIdent (codeNamespace.getId ++ `tail67)
    let tail68 := Lean.mkIdent (codeNamespace.getId ++ `tail68)
    let tail69 := Lean.mkIdent (codeNamespace.getId ++ `tail69)
    let tail70 := Lean.mkIdent (codeNamespace.getId ++ `tail70)
    let tail71 := Lean.mkIdent (codeNamespace.getId ++ `tail71)
    let tail72 := Lean.mkIdent (codeNamespace.getId ++ `tail72)
    let tail73 := Lean.mkIdent (codeNamespace.getId ++ `tail73)
    let tail74 := Lean.mkIdent (codeNamespace.getId ++ `tail74)
    let tail75 := Lean.mkIdent (codeNamespace.getId ++ `tail75)
    let tail76 := Lean.mkIdent (codeNamespace.getId ++ `tail76)
    let tail77 := Lean.mkIdent (codeNamespace.getId ++ `tail77)
    let tail78 := Lean.mkIdent (codeNamespace.getId ++ `tail78)
    let tail79 := Lean.mkIdent (codeNamespace.getId ++ `tail79)
    let tail80 := Lean.mkIdent (codeNamespace.getId ++ `tail80)
    let tail81 := Lean.mkIdent (codeNamespace.getId ++ `tail81)
    let tail82 := Lean.mkIdent (codeNamespace.getId ++ `tail82)
    let tail83 := Lean.mkIdent (codeNamespace.getId ++ `tail83)
    let tail84 := Lean.mkIdent (codeNamespace.getId ++ `tail84)
    let tail85 := Lean.mkIdent (codeNamespace.getId ++ `tail85)
    let tail86 := Lean.mkIdent (codeNamespace.getId ++ `tail86)
    let tail87 := Lean.mkIdent (codeNamespace.getId ++ `tail87)
    let tail88 := Lean.mkIdent (codeNamespace.getId ++ `tail88)
    let tail89 := Lean.mkIdent (codeNamespace.getId ++ `tail89)
    let tail90 := Lean.mkIdent (codeNamespace.getId ++ `tail90)
    `(tactic|
      (
        proof_step =>
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
          refine wp_call_exact_append ($transfer 8 (by decide) (embedding_exact $env $initial $ownerValue $pointer $weights $t0 0 $ha (by omega) $ht0 (by decide)))
            (f := $func8Def) rfl rfl rfl _ rfl ?_
          unfold $tail1
          generalize he0 : embedding $weights $t0 0 = e0
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 8 (by decide) (embedding_exact $env $initial $ownerValue $pointer $weights $t1 1 $ha (by omega) $ht1 (by decide)))
            (f := $func8Def) rfl rfl rfl _ rfl ?_
          unfold $tail2
          generalize he1 : embedding $weights $t1 1 = e1
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 8 (by decide) (embedding_exact $env $initial $ownerValue $pointer $weights $t2 2 $ha (by omega) $ht2 (by decide)))
            (f := $func8Def) rfl rfl rfl _ rfl ?_
          unfold $tail3
          generalize he2 : embedding $weights $t2 2 = e2
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 8 (by decide) (embedding_exact $env $initial $ownerValue $pointer $weights $t3 3 $ha (by omega) $ht3 (by decide)))
            (f := $func8Def) rfl rfl rfl _ rfl ?_
          unfold $tail4
          generalize he3 : embedding $weights $t3 3 = e3
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 18 2464 (some 18) rfl rfl)
            (f := $func18Def) rfl rfl rfl _ rfl ?_
          unfold $tail5
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2464 e0 $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail6
          generalize hn0 : Project.TinyGpt2.norm $weights 2464 e0 = n0
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 18 2464 (some 18) rfl rfl)
            (f := $func18Def) rfl rfl rfl _ rfl ?_
          unfold $tail7
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2464 e1 $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail8
          generalize hn1 : Project.TinyGpt2.norm $weights 2464 e1 = n1
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 18 2464 (some 18) rfl rfl)
            (f := $func18Def) rfl rfl rfl _ rfl ?_
          unfold $tail9
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2464 e2 $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail10
          generalize hn2 : Project.TinyGpt2.norm $weights 2464 e2 = n2
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 18 2464 (some 18) rfl rfl)
            (f := $func18Def) rfl rfl rfl _ rfl ?_
          unfold $tail11
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2464 e3 $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail12
          generalize hn3 : Project.TinyGpt2.norm $weights 2464 e3 = n3
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 27 1040 (some 27) rfl rfl)
            (f := $func27Def) rfl rfl rfl _ rfl ?_
          unfold $tail13
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 28 (by decide) (contextRow_exact $env $initial ⟨n0, n1, n2, n3⟩ $position))
            (f := $func28Def) rfl rfl rfl _ rfl ?_
          unfold $tail14
          generalize hqueryRow : contextRow ⟨n0, n1, n2, n3⟩ $position = queryRow
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 26 (by decide) (project4_exact $env $initial $ownerValue $pointer $weights 1040 queryRow $ha (by omega)))
            (f := $func26Def) rfl rfl rfl _ rfl ?_
          unfold $tail15
          generalize hquery : project4 $weights 1040 queryRow = query
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 30 1056 (some 30) rfl rfl)
            (f := $func30Def) rfl rfl rfl _ rfl ?_
          unfold $tail16
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 29 (by decide) (projectContext_exact $env $initial $ownerValue $pointer $weights 1056 ⟨n0, n1, n2, n3⟩ $ha (by omega)))
            (f := $func29Def) rfl rfl rfl _ rfl ?_
          unfold $tail17
          generalize hkeys : projectContext $weights 1056 ⟨n0, n1, n2, n3⟩ = keys
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 31 1072 (some 31) rfl rfl)
            (f := $func31Def) rfl rfl rfl _ rfl ?_
          unfold $tail18
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 29 (by decide) (projectContext_exact $env $initial $ownerValue $pointer $weights 1072 ⟨n0, n1, n2, n3⟩ $ha (by omega)))
            (f := $func29Def) rfl rfl rfl _ rfl ?_
          unfold $tail19
          generalize hvalues : projectContext $weights 1072 ⟨n0, n1, n2, n3⟩ = values
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
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 48 (by decide) (attentionRow_exact $env $initial ($position+1) query keys values))
            (f := $func48Def) rfl rfl rfl _ rfl ?_
          unfold $tail20
          generalize hattended : attentionRow ($position+1) query keys values = attended
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 49 1088 (some 49) rfl rfl)
            (f := $func49Def) rfl rfl rfl _ rfl ?_
          unfold $tail21
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 26 (by decide) (project4_exact $env $initial $ownerValue $pointer $weights 1088 attended $ha (by omega)))
            (f := $func26Def) rfl rfl rfl _ rfl ?_
          unfold $tail22
          generalize hprojected : project4 $weights 1088 attended = projected
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 50 1104 (some 50) rfl rfl)
            (f := $func50Def) rfl rfl rfl _ rfl ?_
          unfold $tail23
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1104 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail24
          generalize habias : loadRow $weights 1104 = attentionBias
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 49 1088 (some 49) rfl rfl)
            (f := $func49Def) rfl rfl rfl _ rfl ?_
          unfold $tail25
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 26 (by decide) (project4_exact $env $initial $ownerValue $pointer $weights 1088 attended $ha (by omega)))
            (f := $func26Def) rfl rfl rfl _ rfl ?_
          unfold $tail26
          rw [hprojected]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 50 1104 (some 50) rfl rfl)
            (f := $func50Def) rfl rfl rfl _ rfl ?_
          unfold $tail27
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1104 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail28
          rw [habias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 49 1088 (some 49) rfl rfl)
            (f := $func49Def) rfl rfl rfl _ rfl ?_
          unfold $tail29
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 26 (by decide) (project4_exact $env $initial $ownerValue $pointer $weights 1088 attended $ha (by omega)))
            (f := $func26Def) rfl rfl rfl _ rfl ?_
          unfold $tail30
          rw [hprojected]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 50 1104 (some 50) rfl rfl)
            (f := $func50Def) rfl rfl rfl _ rfl ?_
          unfold $tail31
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1104 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail32
          rw [habias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 49 1088 (some 49) rfl rfl)
            (f := $func49Def) rfl rfl rfl _ rfl ?_
          unfold $tail33
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 26 (by decide) (project4_exact $env $initial $ownerValue $pointer $weights 1088 attended $ha (by omega)))
            (f := $func26Def) rfl rfl rfl _ rfl ?_
          unfold $tail34
          rw [hprojected]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 50 1104 (some 50) rfl rfl)
            (f := $func50Def) rfl rfl rfl _ rfl ?_
          unfold $tail35
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1104 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail36
          rw [habias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 28 (by decide) (contextRow_exact $env $initial ⟨e0, e1, e2, e3⟩ $position))
            (f := $func28Def) rfl rfl rfl _ rfl ?_
          unfold $tail37
          generalize hembeddedRow : contextRow ⟨e0, e1, e2, e3⟩ $position = embeddedRow
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 4 (by decide) (addRows_exact $env $initial embeddedRow (addRows projected attentionBias)))
            (f := $func4Def) rfl rfl rfl _ rfl ?_
          unfold $tail38
          generalize hresidual : addRows embeddedRow (addRows projected attentionBias) = residual
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail39
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail40
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail41
          generalize hnff : Project.TinyGpt2.norm $weights 2472 residual = nff
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 0 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail42
          generalize hd0 : dotColumn4 $weights 1108 8 0 nff = d0
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail43
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail44
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail45
          rw [hnff]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 1 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail46
          generalize hd1 : dotColumn4 $weights 1108 8 1 nff = d1
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail47
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail48
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail49
          rw [hnff]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 2 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail50
          generalize hd2 : dotColumn4 $weights 1108 8 2 nff = d2
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail51
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail52
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail53
          rw [hnff]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 3 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail54
          generalize hd3 : dotColumn4 $weights 1108 8 3 nff = d3
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail55
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail56
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail57
          rw [hnff]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 4 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail58
          generalize hd4 : dotColumn4 $weights 1108 8 4 nff = d4
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail59
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail60
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail61
          rw [hnff]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 5 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail62
          generalize hd5 : dotColumn4 $weights 1108 8 5 nff = d5
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail63
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail64
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail65
          rw [hnff]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 6 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail66
          generalize hd6 : dotColumn4 $weights 1108 8 6 nff = d6
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 51 1108 (some 51) rfl rfl)
            (f := $func51Def) rfl rfl rfl _ rfl ?_
          unfold $tail67
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 54 2472 (some 54) rfl rfl)
            (f := $func54Def) rfl rfl rfl _ rfl ?_
          unfold $tail68
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2472 residual $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail69
          rw [hnff]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 25 (by decide) (dotColumn4_exact $env $initial $ownerValue $pointer $weights 1108 8 7 nff $ha (by omega)))
            (f := $func25Def) rfl rfl rfl _ rfl ?_
          unfold $tail70
          generalize hd7 : dotColumn4 $weights 1108 8 7 nff = d7
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 52 1140 (some 52) rfl rfl)
            (f := $func52Def) rfl rfl rfl _ rfl ?_
          unfold $tail71
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1140 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail72
          generalize hlbias : loadRow $weights 1140 = lowBias
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 52 1140 (some 52) rfl rfl)
            (f := $func52Def) rfl rfl rfl _ rfl ?_
          unfold $tail73
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1140 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail74
          rw [hlbias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 52 1140 (some 52) rfl rfl)
            (f := $func52Def) rfl rfl rfl _ rfl ?_
          unfold $tail75
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1140 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail76
          rw [hlbias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 52 1140 (some 52) rfl rfl)
            (f := $func52Def) rfl rfl rfl _ rfl ?_
          unfold $tail77
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1140 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail78
          rw [hlbias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
          refine wp_iff_cons rfl ?_
          simp only [show (1140:UInt64)+4 = 1144 by decide,
            show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1144 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail79
          generalize hhbias : loadRow $weights 1144 = highBias
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
          refine wp_iff_cons rfl ?_
          simp only [show (1140:UInt64)+4 = 1144 by decide,
            show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1144 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail80
          rw [hhbias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
          refine wp_iff_cons rfl ?_
          simp only [show (1140:UInt64)+4 = 1144 by decide,
            show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1144 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail81
          rw [hhbias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
          refine wp_iff_cons rfl ?_
          simp only [show (1140:UInt64)+4 = 1144 by decide,
            show ¬(1144:UInt64) < 1140 by decide, reduceIte, ne_eq, not_true_eq_false]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 5 (by decide) (loadRow_exact $env $initial $ownerValue $pointer $weights 1144 $ha (by omega)))
            (f := $func5Def) rfl rfl rfl _ rfl ?_
          unfold $tail82
          rw [hhbias]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 62 (by decide) (activate_exact $env $initial (addRows ⟨d0, d1, d2, d3⟩ lowBias)))
            (f := $func62Def) rfl rfl rfl _ rfl ?_
          unfold $tail83
          generalize hactLow : activate (addRows ⟨d0, d1, d2, d3⟩ lowBias) = actLow
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 62 (by decide) (activate_exact $env $initial (addRows ⟨d4, d5, d6, d7⟩ highBias)))
            (f := $func62Def) rfl rfl rfl _ rfl ?_
          unfold $tail84
          generalize hactHigh : activate (addRows ⟨d4, d5, d6, d7⟩ highBias) = actHigh
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 69 (by decide) (contractRow_exact $env $initial $ownerValue $pointer $weights ⟨actLow, actHigh⟩ $ha (by omega)))
            (f := $func69Def) rfl rfl rfl _ rfl ?_
          unfold $tail85
          generalize hcontracted : contractRow $weights ⟨actLow, actHigh⟩ = contracted
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 69 (by decide) (contractRow_exact $env $initial $ownerValue $pointer $weights ⟨actLow, actHigh⟩ $ha (by omega)))
            (f := $func69Def) rfl rfl rfl _ rfl ?_
          unfold $tail86
          rw [hcontracted]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 69 (by decide) (contractRow_exact $env $initial $ownerValue $pointer $weights ⟨actLow, actHigh⟩ $ha (by omega)))
            (f := $func69Def) rfl rfl rfl _ rfl ?_
          unfold $tail87
          rw [hcontracted]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 69 (by decide) (contractRow_exact $env $initial $ownerValue $pointer $weights ⟨actLow, actHigh⟩ $ha (by omega)))
            (f := $func69Def) rfl rfl rfl _ rfl ?_
          unfold $tail88
          rw [hcontracted]
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append (ConstantFunction.exact $targetModule $env $initial 70 2480 (some 70) rfl rfl)
            (f := $func70Def) rfl rfl rfl _ rfl ?_
          unfold $tail89
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
        proof_step =>
          refine wp_call_exact_append ($transfer 17 (by decide) (norm_exact $env $initial $ownerValue $pointer $weights 2480 (addRows residual contracted) $ha (by omega)))
            (f := $func17Def) rfl rfl rfl _ rfl ?_
          unfold $tail90
          generalize hfinal : TinyGpt2.norm $weights 2480 (addRows residual contracted) = finalRow
        proof_step =>
          wp_fixed_frame [$func71Def:term, rowResults, contextResults, wideResults, List.append_nil, List.cons_append, List.nil_append]
          have hrow : finalRow = $expected := hfinal.symm.trans
            ((hidden_of_stages $weights $t0 $t1 $t2 $t3 $position
              he0 he1 he2 he3 hn0 hn1 hn2 hn3 hqueryRow hquery hkeys hvalues hattended hprojected
              habias hembeddedRow hresidual hnff hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hlbias hhbias
              hactLow hactHigh hcontracted).symm.trans $hexpected)
          exact ⟨True.intro, congrArg rowResults hrow⟩
      ))

end Project.TinyGpt2Hidden.Spec
