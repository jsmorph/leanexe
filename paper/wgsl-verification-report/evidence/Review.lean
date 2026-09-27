import LeanExe.WGSL.Examples.Body

open LeanExe.WGSL LeanExe.WGSL.Source LeanExe.WGSL.Statement

def reviewCode : Code :=
  .bind (.loadA (.add (.mul .row (.lit 3)) .col))
    (.bind (.loadB (.add (.mul .row (.lit 3)) .col))
      (.bind (.add 1 0) (.finish 0)))

theorem reviewSource : Examples.Body.add = reviewCode.term.kernel := by
  funext ar a b row col
  rfl

theorem reviewValid : reviewCode.Valid ⟨2, 3, 6, 6⟩ [] 0 := by decide +kernel

theorem reviewInvocation (ar : ScalarArithmetic) (memory : Memory) (sizeC : Nat)
    (row col : UInt32) (ha : 6 ≤ memory.sizeA) (hb : 6 ≤ memory.sizeB)
    (hc : 6 ≤ sizeC) :
    invoke ⟨2, 3, reviewCode⟩ ar memory sizeC row col =
      .ok (expected ⟨2, 3, 6, 6⟩ Examples.Body.add ar memory row col) :=
  invoke_eq _ _ _ (by decide) reviewValid reviewSource ar memory sizeC row col ha hb hc

#print axioms Source.Index.bound_le
#print axioms Source.Index.word_eq
#print axioms Statement.Code.run_eq
#print axioms Statement.shader_implements
#print axioms Statement.dispatch_covers
#print axioms Statement.stores_disjoint
#print axioms reviewSource
#print axioms reviewValid
#print axioms reviewInvocation

def main : IO Unit := do
  let shader := Source.emit ⟨2, 3, 6, 6⟩ reviewCode.term
  IO.FS.writeFile "build/wgsl/review-add.wgsl" shader
  let .ok parsed := Source.parse shader | throw (IO.userError "review shader failed parsing")
  IO.FS.writeFile "build/wgsl/review-code.txt" parsed.code.lean
  IO.println "Executable parser accepted the review shader."
