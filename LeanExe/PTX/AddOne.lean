import LeanExe.PTX.Launch

/-!
A kernel written by hand that adds one to each word of an array.  The input buffer holds the
length `n` in word 0 and the array in words `1` to `n`; the output buffer has the same layout, and
the host writes its word 0.  Thread `g` with `g < n` stores `input[1 + g] + 1` to `output[1 + g]`.
`addOne_executions` states the output for every consistent execution of a launch with at least `n`
threads, and `addOne_execution_exists` shows that a consistent execution exists.
-/

namespace LeanExe.PTX

/-- The add-one kernel. -/
def addOne : Module where
  inputs := 1
  regs32 := 3
  regs64 := 10
  regsF := 0
  preds := 1
  body := [
    .instr none (.special 0 .ctaidX),
    .instr none (.special 1 .ntidX),
    .instr none (.special 2 .tidX),
    .instr none (.widen 0 2),
    .instr none (.madWide 1 0 1 0),
    .instr none (.ldParam 2 0),
    .instr none (.cvtaGlobal 2 2),
    .instr none (.ldParam 3 1),
    .instr none (.cvtaGlobal 3 3),
    .instr none (.ld 4 2 0),
    .instr none (.setp .lt 0 1 (.reg 4)),
    .ite 0 [
      .instr none (.shift .shl 5 1 (.imm 3)),
      .instr none (.bin64 .add 6 2 (.reg 5)),
      .instr none (.ld 7 6 8),
      .instr none (.bin64 .add 8 7 (.imm 1)),
      .instr none (.bin64 .add 9 3 (.reg 5)),
      .instr none (.st 9 8 8)] []]

/-- A launch of the add-one kernel on the array `xs`, with output words `ys` after the length. -/
def addOneLaunch (xs ys : Array UInt64) (blocks block : Nat) : Launch :=
  ⟨addOne, [#[UInt64.ofNat xs.size] ++ xs], #[UInt64.ofNat xs.size] ++ ys, blocks, block⟩

theorem wordAt_zero (n : Nat) : wordAt (n + 1) 0 0 = some 0 := by simp [wordAt]

theorem wordAt_elem {n g : Nat} (h : g < n) (hg : g < 2 ^ 60) :
    wordAt (n + 1) (UInt64.ofNat g <<< 3) 8 = some (g + 1) := by
  have h1 : (UInt64.ofNat g <<< 3).toNat = 8 * g := by
    rw [UInt64.toNat_shiftLeft]
    simp [Nat.shiftLeft_eq]
    omega
  have h2 : (8 : UInt64).toNat = 8 := rfl
  simp only [wordAt, h1, h2]
  have : (8 * g + 8) / 8 = g + 1 := by omega
  simp [this]
  omega

theorem ofNat_lt_iff {g n : Nat} (hg : g < 2 ^ 60) (hn : n < 2 ^ 60) :
    decide (UInt64.ofNat g < UInt64.ofNat n) = decide (g < n) := by
  simp [UInt64.lt_iff_toNat_lt]
  omega

/-- The events of thread `g` with the input oracle. -/
def addOneEvents (xs : Array UInt64) (g : Nat) : List Event :=
  if h : g < xs.size then
    [.read 0 0 (UInt64.ofNat xs.size), .read 0 (g + 1) xs[g], .write (g + 1) (xs[g] + 1)]
  else [.read 0 0 (UInt64.ofNat xs.size)]

theorem addOne_thread (xs ys : Array UInt64) (blocks block g : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hq : g / block < 2 ^ 32) (hg : g < 2 ^ 60) (hn : xs.size < 2 ^ 60)
    (hys : ys.size = xs.size) :
    (addOneLaunch xs ys blocks block).events (inputOracle [#[UInt64.ofNat xs.size] ++ xs]) g =
      (addOneEvents xs g, true) := by
  have hsz : (#[UInt64.ofNat xs.size] ++ ys).size = xs.size + 1 := by simp [hys]; omega
  have hsizes : [#[UInt64.ofNat xs.size] ++ xs].map (·.size) = [xs.size + 1] := by
    simp; omega
  simp only [Launch.events, addOneLaunch, hsz, hsizes]
  by_cases hgn : g < xs.size
  · simp [addOneEvents, hgn, Module.invoke, addOne, Stmt.execList, Stmt.exec, Instr.exec,
      Local.initial, Local.set32, Local.set64, Local.setp, Res.andThen, threadShape, Src64.get,
      Src64.word, Src32.get, Local.word, Bin64.apply, Shift.apply, Cmp.apply, inputOracle,
      index_eq hb hb32 hq hg, get_head, get_tail, wordAt_zero, ofNat_lt_iff hg hn,
      wordAt_elem hgn hg]
  · simp [addOneEvents, hgn, Module.invoke, addOne, Stmt.execList, Stmt.exec, Instr.exec,
      Local.initial, Local.set32, Local.set64, Local.setp, Res.andThen, threadShape, Src64.get,
      Src64.word, Local.word, Cmp.apply, inputOracle, index_eq hb hb32 hq hg, get_head,
      wordAt_zero, ofNat_lt_iff hg hn]

theorem writesOf_addOneEvents (xs : Array UInt64) (g : Nat) :
    writesOf (addOneEvents xs g) = if h : g < xs.size then [(g + 1, xs[g] + 1)] else [] := by
  unfold addOneEvents
  split <;> rfl

/-- The sequential run of the add-one kernel leaves each word plus one, and distinct threads store
to distinct words. -/
theorem addOne_seq (xs ys : Array UInt64) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hys : ys.size = xs.size)
    (hcover : xs.size ≤ blocks * block) (hthreads : blocks * block < 2 ^ 60) :
    (addOneLaunch xs ys blocks block).seq =
        some (#[UInt64.ofNat xs.size] ++ xs.map (· + 1)) ∧
      (addOneLaunch xs ys blocks block).RaceFree := by
  have hthread : ∀ g, g < blocks * block →
      (addOneLaunch xs ys blocks block).events (inputOracle [#[UInt64.ofNat xs.size] ++ xs]) g =
        (addOneEvents xs g, true) := fun g hg =>
    addOne_thread xs ys blocks block g hb hb32
      (by have := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hg; exact hg); omega)
      (by omega) (by omega) hys
  refine ⟨?_, ?_⟩
  · rw [Launch.seq_some (addOneLaunch xs ys blocks block) (addOneEvents xs)
      fun g hg => hthread g hg]
    congr 1
    apply Array.ext_getElem?
    intro i
    have hsize : (#[UInt64.ofNat xs.size] ++ ys).size = xs.size + 1 := by simp [hys]; omega
    by_cases hi : i < xs.size + 1
    · rw [setAll_get (by simpa [Launch.threads, addOneLaunch, hsize] using hi)]
      simp only [show (addOneLaunch xs ys blocks block).threads = blocks * block from rfl]
      cases i with
      | zero =>
          rw [lastVal_flatMap _ 0 (blocks * block) (blocks * block) (fun g _ _ w hw => by
            simp only [writesOf_addOneEvents] at hw
            split at hw <;> simp_all) _ _ (Nat.le_refl _)]
          simp [addOneLaunch, get_head]
      | succ j =>
          rw [lastVal_flatMap _ (j + 1) j (blocks * block) (fun g _ hne w hw => by
            simp only [writesOf_addOneEvents] at hw
            split at hw <;> simp_all) _ _ (Nat.le_refl _)]
          have hj : j < xs.size := by omega
          simp [addOneLaunch, writesOf_addOneEvents, hj, lastVal,
            show j < blocks * block by omega, get_tail]
    · rw [Array.getElem?_eq_none (by simpa [addOneLaunch, hsize] using hi),
        Array.getElem?_eq_none (by simp; omega)]
  · intro g h hg hh hgh i v w hv hw
    have e1 : (addOneLaunch xs ys blocks block).events
        (inputOracle (addOneLaunch xs ys blocks block).inputs) g = (addOneEvents xs g, true) :=
      hthread g hg
    have e2 : (addOneLaunch xs ys blocks block).events
        (inputOracle (addOneLaunch xs ys blocks block).inputs) h = (addOneEvents xs h, true) :=
      hthread h hh
    rw [e1] at hv
    rw [e2] at hw
    unfold addOneEvents at hv hw
    split at hv <;> split at hw <;> simp_all

/-- In every consistent execution of a launch of the add-one kernel with at least `xs.size`
threads, no access of a thread is in a data race and the copy back reads the length followed by
each word of `xs` plus one. -/
theorem addOne_executions (xs ys : Array UInt64) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hys : ys.size = xs.size)
    (hcover : xs.size ≤ blocks * block) (hthreads : blocks * block < 2 ^ 60) (E : Execution)
    (hE : (addOneLaunch xs ys blocks block).Consistent E) :
    (addOneLaunch xs ys blocks block).NoDataRace E ∧ ∀ i, i < xs.size + 1 →
      (#[UInt64.ofNat xs.size] ++ xs.map (· + 1))[i]? = some (E.observed i) := by
  obtain ⟨hs, hr⟩ := addOne_seq xs ys blocks block hb hb32 hbl hys hcover hthreads
  obtain ⟨-, hrace, hout⟩ := Launch.executions _ hs hr E hE
  exact ⟨hrace, fun i hi => hout i (by simp [addOneLaunch, hys]; omega)⟩

/-- A launch of the add-one kernel with at least `xs.size` threads has a consistent execution. -/
theorem addOne_execution_exists (xs ys : Array UInt64) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hys : ys.size = xs.size)
    (hcover : xs.size ≤ blocks * block) (hthreads : blocks * block < 2 ^ 60) :
    ∃ E, (addOneLaunch xs ys blocks block).Consistent E := by
  obtain ⟨hs, hr⟩ := addOne_seq xs ys blocks block hb hb32 hbl hys hcover hthreads
  exact Launch.execution_exists _ hs hr

end LeanExe.PTX

#print axioms LeanExe.PTX.addOne_executions
#print axioms LeanExe.PTX.addOne_execution_exists
