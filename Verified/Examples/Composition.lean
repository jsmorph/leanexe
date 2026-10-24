import Verified.Examples.CompositionBase
import Verified.ModuleComposition

namespace Verified.Examples.Composition

open LeanExe.Pipeline

def wordCaller (x y : UInt64) : UInt64 := CompositionBase.add x y * 3

def floatCaller (x : Float) : Float := CompositionBase.scale x + 0.25

def wordFunc : Func [CompositionBase.compiled.scale.func.sig,
    CompositionBase.compiled.add.func.sig] where
  name := "wordCaller"
  params := [.word, .word]
  modes := []
  result := .word
  body := .bin .mul (.call (.there .here) (Args.cons (.var .here)
    (Args.cons (.var (.there .here)) .nil)).get) (.word 3)
  placeArgs := rfl

def floatFunc : Func (wordFunc.sig :: [CompositionBase.compiled.scale.func.sig,
    CompositionBase.compiled.add.func.sig]) where
  name := "floatCaller"
  params := [.float]
  modes := []
  result := .float
  body := .fbin .add (.call (.there .here) (Args.cons (.var .here) .nil).get)
    (.float 4598175219545276416)
  placeArgs := rfl

def program := Prog.cons floatFunc (Prog.cons wordFunc CompositionBase.compiled.program)

def module := compile program

theorem base_prefix : CompositionBase.compiled.program.functions <+: program.functions :=
  (CompositionBase.compiled.program.functions_prefix_cons wordFunc).trans
    ((Prog.cons wordFunc CompositionBase.compiled.program).functions_prefix_cons floatFunc)

theorem base_calls : Calls module CompositionBase.compiled.funs
    CompositionBase.compiled.program.flags
    (CompositionBase.compiled.program.boundsAt CompositionBase.compiled.funs)
    (CompositionBase.compiled.program.fitsAt CompositionBase.compiled.funs) :=
  CompositionBase.compiled.program.calls_extension program _ CompositionBase.compiled.meaning
    base_prefix [] [] (by
      have noLiterals : CompositionBase.compiled.program.literals = [] := by decide +kernel
      simp only [Prog.Covered, noLiterals, List.nil_subset])

theorem add_implements : ImplementsA false module 2
    (fun p : UInt64 × UInt64 => CompositionBase.add p.1 p.2)
    (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  exact ImplementsA.lean ((base_calls (.there .here) 0).implementsB_unpaid rfl rfl).implementsA

theorem scale_implements : ImplementsA false module 3 CompositionBase.scale
    (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  exact ImplementsA.lean ((base_calls .here 0).implementsB_unpaid rfl rfl).implementsA

theorem wordCaller_implements : ImplementsA false module 4
    (fun p : UInt64 × UInt64 => wordCaller p.1 p.2)
    (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  exact ImplementsA.lean
    (((program.correct_funs rfl (by decide +kernel)) (.there .here) 0).implementsB_unpaid rfl rfl).implementsA

theorem floatCaller_implements : ImplementsA false module 5 floatCaller
    (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  exact ImplementsA.lean
    (((program.correct_funs rfl (by decide +kernel)) .here 0).implementsB_unpaid rfl rfl).implementsA

#print axioms base_calls
#print axioms add_implements
#print axioms scale_implements
#print axioms wordCaller_implements
#print axioms floatCaller_implements

end Verified.Examples.Composition
