import Verified.Examples.ScalarComposition
import Verified.ProgramAppendCorrect

namespace Verified.Examples.Relocation

open LeanExe.Pipeline

def seed (x : UInt64) : UInt64 := x + 101

verified_compile seedLibrary := [seed]

def libraryProgram := ScalarComposition.compiled.program.append seedLibrary.program

def libraryFuns := ScalarComposition.compiled.funs.append seedLibrary.funs

theorem libraryMeaning : libraryProgram.Meaning libraryFuns :=
  ScalarComposition.compiled.meaning.append seedLibrary.meaning

def callBoth (n : UInt64) : UInt64 := seed n + ScalarComposition.shiftedSum n

private def signatures {S : List Sig} (_ : Prog S) : List Sig := S

def caller : Func (signatures libraryProgram) where
  name := "callBoth"
  params := [.word]
  modes := []
  result := .word
  body := .bin .add
    (.call (FVar.appendRight (signatures ScalarComposition.compiled.program)
      (FVar.here (S := []) (g := seedLibrary.seed.func.sig))) (Args.cons (.var .here) .nil).get)
    (.call (FVar.appendLeft (S := signatures ScalarComposition.compiled.program)
      (signatures seedLibrary.program) (.there (.there (.there (.there .here)))))
      (Args.cons (.var .here) .nil).get)
  placeArgs := rfl

theorem caller_denote (n : UInt64) : caller.denote libraryFuns (.cons n .nil) = callBoth n := by
  exact congrArg₂ (fun x y : UInt64 => x + y)
    (seedLibrary.seed.denote_eq n) (ScalarComposition.compiled.shiftedSum.denote_eq n)

def program := Prog.cons caller libraryProgram

def funs := Funs.cons (g := caller.sig) (caller.denote libraryFuns) libraryFuns

theorem meaning : program.Meaning funs := .cons libraryMeaning

def module := compile program

theorem prefix_calls : Calls module seedLibrary.funs seedLibrary.program.flags
    (seedLibrary.program.boundsAt seedLibrary.funs) (seedLibrary.program.fitsAt seedLibrary.funs) :=
  seedLibrary.program.calls_extension program seedLibrary.funs seedLibrary.meaning
    ((ScalarComposition.compiled.program.functions_prefix_append seedLibrary.program).trans
      (libraryProgram.functions_prefix_cons caller)) [] [] (by decide +kernel)

theorem seed_implements : ImplementsA false module 2 seed
    (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  exact ImplementsA.lean ((prefix_calls .here 0).implementsB_unpaid rfl rfl).implementsA

theorem relocated_calls : Calls module funs program.flags (program.boundsAt funs)
    (program.fitsAt funs) :=
  program.correct funs meaning (by decide +kernel)

theorem sum_implements : ImplementsA false module 5
    (fun p : UInt64 × UInt64 => ScalarComposition.sum p.1 p.2)
    (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  exact ImplementsA.lean
    ((relocated_calls (.there (.there (.there (.there (.there (.there .here)))))) 0).implementsB_unpaid rfl rfl).implementsA

theorem callBoth_implements : ImplementsA false module 11 callBoth
    (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  have h : ImplementsA (α := UInt64) (β := UInt64) false module 11
      (fun n : UInt64 => (caller.denote libraryFuns (.cons n .nil) : UInt64))
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
    ImplementsA.lean ((relocated_calls .here 0).implementsB_unpaid rfl rfl).implementsA
  simpa only [caller_denote] using h

run_cmd Lean.Elab.Command.liftTermElabM do
  let m := Lean.mkConst ``module
  let names : Array Lean.Name := #[`seed, `divide, `choose, `sum, `shiftedSum,
    `scale, `twice, `round32, `bits32, `callBoth]
  let mut callees : List (Nat × Lean.Expr) := []
  for k in [:names.size] do
    let index := k + 2
    let some proof ← Reflect.scalarEntryProof m index (fun i =>
        (callees.find? (fun pair => pair.1 == i)).map Prod.snd)
      | throwError "missing scalar store proof at {index}"
    let name := `Verified.Examples.Relocation.uniforms ++ names[k]!
    Reflect.addTheorem name (← Lean.Meta.inferType proof) proof
    callees := (index, Lean.mkConst name) :: callees

theorem seed_pure : ImplementsPureA false module 2 seed :=
  implementsPure_of_uniform seed_implements uniforms.seed

theorem sum_pure : ImplementsPureA false module 5
    (fun p : UInt64 × UInt64 => ScalarComposition.sum p.1 p.2) :=
  implementsPure_of_uniform sum_implements uniforms.sum

theorem callBoth_pure : ImplementsPureA false module 11 callBoth :=
  implementsPure_of_uniform callBoth_implements uniforms.callBoth

#print axioms meaning
#print axioms prefix_calls
#print axioms seed_implements
#print axioms relocated_calls
#print axioms sum_implements
#print axioms callBoth_implements
#print axioms seed_pure
#print axioms sum_pure
#print axioms callBoth_pure

end Verified.Examples.Relocation
