import Project.TinyGpt2Hidden.Program
import Project.ProofKit.ConstantFunction

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.ProofKit

theorem layout_norm1_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 18 initial []
      (fun final values => final = initial ∧ values = [.i64 2464]) :=
  ConstantFunction.exact _ env initial 18 2464 (some 18) rfl rfl

theorem layout_query_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 27 initial []
      (fun final values => final = initial ∧ values = [.i64 1040]) :=
  ConstantFunction.exact _ env initial 27 1040 (some 27) rfl rfl

theorem layout_key_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 30 initial []
      (fun final values => final = initial ∧ values = [.i64 1056]) :=
  ConstantFunction.exact _ env initial 30 1056 (some 30) rfl rfl

theorem layout_value_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 31 initial []
      (fun final values => final = initial ∧ values = [.i64 1072]) :=
  ConstantFunction.exact _ env initial 31 1072 (some 31) rfl rfl

theorem layout_attention_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 53 initial []
      (fun final values => final = initial ∧ values = [.i64 1088]) :=
  ConstantFunction.exact _ env initial 53 1088 (some 53) rfl rfl

theorem layout_attentionBias_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 54 initial []
      (fun final values => final = initial ∧ values = [.i64 1104]) :=
  ConstantFunction.exact _ env initial 54 1104 (some 54) rfl rfl

theorem layout_expand_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 55 initial []
      (fun final values => final = initial ∧ values = [.i64 1108]) :=
  ConstantFunction.exact _ env initial 55 1108 (some 55) rfl rfl

theorem layout_expandBias_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 56 initial []
      (fun final values => final = initial ∧ values = [.i64 1140]) :=
  ConstantFunction.exact _ env initial 56 1140 (some 56) rfl rfl

theorem layout_norm2_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 58 initial []
      (fun final values => final = initial ∧ values = [.i64 2472]) :=
  ConstantFunction.exact _ env initial 58 2472 (some 58) rfl rfl

theorem layout_normFinal_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.TinyGpt2Hidden.module 73 initial []
      (fun final values => final = initial ∧ values = [.i64 2480]) :=
  ConstantFunction.exact _ env initial 73 2480 (some 73) rfl rfl

end Project.TinyGpt2Hidden.Spec
