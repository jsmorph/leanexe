import Library.Combinatorics.DancingLinks.Count

/-! Reading the options word by word, as step X1 does.  The state of `readStep` holds the finished
options and the run being read: a nonzero word extends the run, and a zero finishes a nonempty
run.  `finish_read` shows that reading words from a state and then finishing the last run gives
the finished options followed by the nonempty runs of the run and the words, as `List.splitOn`
cuts them.  From the empty state, that is the specification's `options`, and `read_prefix`
gives, for any prefix of the words, how the state after it sits inside the options. -/

namespace Library.Combinatorics.DancingLinks

/-- One word of the reader: a nonzero word extends the run, and a zero finishes a nonempty run. -/
def readStep (s : List (List Nat) × List Nat) (w : Nat) : List (List Nat) × List Nat :=
  if w = 0 then (if s.2 = [] then s else (s.1 ++ [s.2], [])) else (s.1, s.2 ++ [w])

/-- The finished options and the last run, if it is nonempty. -/
def finish (s : List (List Nat) × List Nat) : List (List Nat) :=
  s.1 ++ (if s.2 = [] then [] else [s.2])

/-- The nonempty runs of a word list. -/
def runs (ws : List Nat) : List (List Nat) := (ws.splitOn 0).filter (· ≠ [])

theorem runs_nozero_append (cur rest : List Nat) (hc : 0 ∉ cur) :
    ((cur ++ 0 :: rest).splitOn 0) = cur :: rest.splitOn 0 := by
  rw [List.splitOn_eq_splitOnP, List.splitOn_eq_splitOnP]
  exact List.splitOnP_append_cons_of_forall_mem
    (fun x hx => by simp only [beq_eq_false_iff_ne]; rintro rfl; exact hc hx) 0 (by simp) rest

theorem read_noZero : ∀ (ws : List Nat) (s : List (List Nat) × List Nat), 0 ∉ s.2 →
    0 ∉ (ws.foldl readStep s).2
  | [], _, h => h
  | w :: ws, s, h => by
    rw [List.foldl_cons]
    refine read_noZero ws _ ?_
    unfold readStep
    by_cases hw : w = 0
    · rw [ite_eq_left hw]
      split
      · exact h
      · simp
    · rw [ite_eq_right hw]
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨h, fun e => hw e.symm⟩

/-- Reading words from a state and finishing gives the finished options and the nonempty runs of
the run followed by the words. -/
theorem finish_read : ∀ (ws : List Nat) (done : List (List Nat)) (cur : List Nat), 0 ∉ cur →
    finish (ws.foldl readStep (done, cur)) = done ++ runs (cur ++ ws)
  | [], done, cur, hc => by
    rw [List.foldl_nil, finish, runs, List.append_nil, List.splitOn_eq_splitOnP,
      List.splitOnP_eq_singleton (fun x hx => by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hc hx)]
    by_cases h : cur = []
    · simp [h]
    · simp [h]
  | w :: ws, done, cur, hc => by
    rw [List.foldl_cons]
    by_cases hw : w = 0
    · subst hw
      have hstep : readStep (done, cur) 0 =
          (if cur = [] then (done, []) else (done ++ [cur], [])) := by
        unfold readStep; simp only [ite_true]
        split <;> simp_all
      rw [hstep]
      by_cases hcur : cur = []
      · rw [ite_eq_left hcur, finish_read ws done [] (by simp), hcur]
        unfold runs
        have := runs_nozero_append [] ws (by simp)
        rw [List.nil_append] at this
        rw [List.nil_append, List.nil_append, this]
        simp
      · rw [ite_eq_right hcur, finish_read ws _ [] (by simp)]
        unfold runs
        rw [runs_nozero_append cur ws hc, List.nil_append]
        simp [hcur]
    · have hstep : readStep (done, cur) w = (done, cur ++ [w]) := by
        unfold readStep; simp [hw]
      rw [hstep, finish_read ws done (cur ++ [w]) (by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hc, fun e => hw e.symm⟩), List.append_assoc, List.singleton_append]

theorem runs_eq_options (x : Array UInt64) : runs ((x.toList.drop 1).map UInt64.toNat) = options x :=
  rfl

/-- After reading a prefix of the words, the finished options begin the options, and a nonempty
run begins the next option. -/
theorem read_prefix (pre rest : List Nat) :
    let s := pre.foldl readStep ([], [])
    runs (pre ++ rest) = s.1 ++ runs (s.2 ++ rest) := by
  intro s
  have h := finish_read (pre ++ rest) [] [] (by simp)
  rw [List.nil_append, List.nil_append] at h
  rw [← h, List.foldl_append]
  exact finish_read rest s.1 s.2 (read_noZero pre ([], []) (by simp))

end Library.Combinatorics.DancingLinks
