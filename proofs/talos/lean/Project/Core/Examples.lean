import LeanExe.Core.Examples
import Project.Core.Compiler

namespace Project.Core.Examples

open LeanExe.Core.Examples

def arithmeticCompiled : Compiled (arity := 2) arithmetic :=
  (compileNative arithmeticCertificate).toOption.get (by decide)

def gcdCompiled : Compiled (arity := 2) LeanExe.Core.Examples.gcd :=
  (compileNative gcdCertificate).toOption.get (by decide)

def nonTailCompiled : Compiled (arity := 1) nonTail :=
  (compileNative nonTailCertificate).toOption.get (by decide)

def calledCompiled : Compiled (arity := 2) called :=
  (compileNative calledCertificate).toOption.get (by decide)

def diamondCompiled : Compiled (arity := 1) diamond :=
  (compileNative diamondCertificate).toOption.get (by decide)

def falseComparisonCompiled : Compiled (arity := 2) falseComparison :=
  (compileNative falseComparisonCertificate).toOption.get (by decide)

def zeroArgumentsCompiled : Compiled (arity := 0) zeroArguments :=
  (compileNative zeroArgumentsCertificate).toOption.get (by decide)

/-- The generated module returns the ordinary recursive Lean definition's value. -/
theorem gcd_correct (a b : UInt64) (host : Wasm.HostEnv α) (store : Wasm.Store α) :
    Wasm.TerminatesWith host gcdCompiled.target gcdCompiled.entry store [.i64 b, .i64 a]
      (fun final values => final = store ∧ values = [.i64 (LeanExe.Core.Examples.gcd a b)]) :=
  gcdCompiled.correct [a, b] rfl α host store

/-- Both recursive calls execute before their results are combined. -/
theorem nonTail_correct (n : UInt64) (host : Wasm.HostEnv α) (store : Wasm.Store α) :
    Wasm.TerminatesWith host nonTailCompiled.target nonTailCompiled.entry store [.i64 n]
      (fun final values => final = store ∧ values = [.i64 (nonTail n)]) :=
  nonTailCompiled.correct [n] rfl α host store

theorem called_correct (a b : UInt64) (host : Wasm.HostEnv α) (store : Wasm.Store α) :
    Wasm.TerminatesWith host calledCompiled.target calledCompiled.entry store [.i64 b, .i64 a]
      (fun final values => final = store ∧ values = [.i64 (called a b)]) :=
  calledCompiled.correct [a, b] rfl α host store

#print axioms gcd_correct
#print axioms nonTail_correct
#print axioms called_correct

end Project.Core.Examples
