import Project.Smalltalk.ScanInvariant

namespace Project.Smalltalk.Marking
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Worklist Project.Smalltalk.MarkInvariant Project.Smalltalk.ScanInvariant

def condition (s : Array UInt64) : Bool := read s 18 != 0 && read s 0 != 4

def scans (s : Array UInt64) (fuel : UInt64) : Array UInt64 :=
  (LeanExe.repeatWhile fuel ((0 : UInt64), s)
    (fun st => condition st.2) (fun st => scanNext st.2)).2

theorem scans_eq_go (s : Array UInt64) (fuel : UInt64) :
    scans s fuel = LeanExe.repeatWhile.go condition scanCell fuel.toNat s := by
  exact Project.Smalltalk.Loops.go_relation (fun st : UInt64 × Array UInt64 => fun t => st.2 = t)
    (fun st => condition st.2) condition (fun st => scanNext st.2) scanCell
    (fun _ _ eq => congrArg condition eq)
    (by intro st t eq _; exact congrArg scanCell eq) fuel.toNat (0, s) s rfl

theorem go_finish {original t : Array UInt64} {cap : Nat} {done queue : List UInt64}
    (valid : Graph.Valid original cap) (phase : read original 0 ≠ 4)
    (st : Holds original t cap done queue) (closed : Closed original done queue)
    (roots : ∀ h, Root original h → h ∈ done ++ queue)
    (fuel : Nat) (enough : cap ≤ done.length + fuel) :
    ∃ finalDone, Holds original (LeanExe.repeatWhile.go condition scanCell fuel t) cap finalDone [] ∧
      Closed original finalDone [] ∧ (∀ h, Root original h → h ∈ finalDone) := by
  induction fuel generalizing t done queue with
  | zero =>
    have bound := handles_length st.distinct (bounds st valid)
    simp only [List.length_append] at bound
    have empty : queue.length = 0 := by omega
    have nil : queue = [] := List.length_eq_zero_iff.mp empty
    subst queue
    exact ⟨done, st, closed, by simpa using roots⟩
  | succ fuel ih =>
    rcases List.eq_nil_or_concat queue with nil | ⟨rest, h, append⟩
    · subst queue
      have zero : read t 18 = 0 := by
        apply UInt64.toNat_inj.mp
        simpa only [List.length_nil, UInt64.reduceToNat] using st.work.count
      have stop : condition t = false := by simp [condition, zero]
      rw [Project.Smalltalk.Loops.go_stop condition scanCell t stop]
      exact ⟨done, st, closed, by simpa using roots⟩
    · have eq : queue = rest ++ [h] := by simpa only [List.concat_eq_append] using append
      rw [eq] at st closed roots
      have nonempty : read t 18 ≠ 0 := by
        intro zero
        have count := st.work.count
        rw [zero] at count
        simp at count
      have running : read t 0 ≠ 4 := by
        rw [st.registers 0 (by decide) (by decide)]
        exact phase
      have test : condition t = true := by simp [condition, nonempty, running]
      rcases scan_holds valid st closed with ⟨more, next, nextClosed, keep⟩
      simp only [LeanExe.repeatWhile.go, test, ite_true]
      exact ih next nextClosed (fun g root => keep g (roots g root)) (by
        simp only [List.length_cons]
        omega)

theorem drained_exact {original t : Array UInt64} {cap : Nat} {done : List UInt64}
    (st : Holds original t cap done []) (closed : Closed original done [])
    (roots : ∀ h, Root original h → h ∈ done) : MarkedExactly original t cap := by
  have complete : ∀ h, Reachable original h → h ∈ done := by
    intro h reached
    induction reached with
    | root root => exact roots _ root
    | next _ edge ih => simpa using closed _ ih _ edge
  refine ⟨st.shape, st.payload, ?_⟩
  intro h hh
  rw [st.marks h hh]
  constructor
  · exact st.sound h
  · intro reached
    simpa using complete h reached

/-- The actual clearing, root-marking, and bounded scan passes. -/
def marking (original : Array UInt64) : Array UInt64 :=
  scans (markRoots (write (Project.Smalltalk.Clear.cleared original) 18 0)) (read original 14)

theorem marking_correct {original : Array UInt64} {cap : Nat}
    (valid : Graph.Valid original cap) (phase : read original 0 ≠ 4) :
    MarkedExactly original (marking original) cap ∧
      read (marking original) 18 = 0 ∧
      (∀ r : UInt64, r.toNat < 24 → r ≠ 18 → read (marking original) r = read original r) := by
  rcases roots_holds valid (initial_holds valid) with ⟨queue, start, roots⟩
  have closed : Closed original [] queue := by intro parent impossible; simp at impossible
  have cover : ∀ h, Root original h → h ∈ [] ++ queue := by simpa using roots
  rcases go_finish valid phase start closed cover (read original 14).toNat
      (by rw [valid.1.2.2.2]; simp) with
    ⟨done, final, finalClosed, finalRoots⟩
  rw [marking, scans_eq_go]
  refine ⟨drained_exact final finalClosed finalRoots, ?_, final.registers⟩
  apply UInt64.toNat_inj.mp
  simpa only [List.length_nil, UInt64.reduceToNat] using final.work.count

end Project.Smalltalk.Marking
