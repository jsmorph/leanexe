import Demos.Euler.Verified
import Demos.Euler.ReconstructedSpec
import Verified.Call

/-! The calls of the verified Euler solvers from the store in which the module starts.  The bound
that `verified_compile` generates for `solve` charges the initial grid, the grids that each try of
a timestep builds, and the packed result, and it ignores the reuse of freed blocks.  `solve_bound`
bounds it by `solveBytes n`, a closed form in the cells of the grid and the tries of the run, and
`reconstructedSolve_bound` does the same for the reconstructed solver.  `euler_solve_call` states
that both exports, called from the store in which the module starts with a memory cap that holds
the heap base and the closed form, return the words of `solve n` and of
`reconstructedSolve n trials` without a trap. -/

namespace Demos.Euler.Verified

open Wasm LeanExe.Pipeline _root_.Demos.Euler

/-- A loop whose passes cost at most `m` times those of a second loop with the same condition and
step, at every state that an invariant `P` of the step admits, costs at most `m` times as much. -/
theorem loopCost_le_mul {α : Type} {C C' : α → Bool} {BA BB : UInt64 → α → Nat}
    {F F' : UInt64 → α → α} (P : α → Prop) (m : Nat) (hC : ∀ s, C s = C' s)
    (hF : ∀ i s, F i s = F' i s) (hcost : ∀ i s, P s → C s = true → BA i s ≤ m * BB i s)
    (hstep : ∀ i s, P s → C s = true → P (F i s)) :
    ∀ (k : Nat) (i : UInt64) (s : α), P s →
      _root_.Verified.loopCost (fun _ => 0) C BA F k i s ≤
        m * _root_.Verified.loopCost (fun _ => 0) C' BB F' k i s
  | 0, _, _, _ => by simp [_root_.Verified.loopCost]
  | k + 1, i, s, hP => by
    simp only [_root_.Verified.loopCost, Nat.zero_add, ← hC s, ← hF i s]
    cases h : C s
    · simp
    · have h1 := hcost i s hP h
      have h2 := loopCost_le_mul P m hC hF hcost hstep k (i + 1) (F i s) (hstep i s hP h)
      simp only [↓reduceIte, Nat.mul_add]
      omega

/-- The cells of the grid of a run of `n`: `n * n` for `n` from 2 to 800, and none otherwise. -/
def cells (n : UInt64) : Nat := if (2 ≤ n && n ≤ 800) = true then (n * n).toNat else 0

theorem cells_le (n : UInt64) : cells n ≤ 640000 := by
  unfold cells
  split
  · rename_i hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    have h1 := UInt64.le_iff_toNat_le.mp hn.2
    simp only [UInt64.reduceToNat] at h1
    rw [UInt64.toNat_mul,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul h1 h1) (by decide))]
    exact Nat.mul_le_mul h1 h1
  · exact Nat.zero_le _

theorem run_grid (n : UInt64) : (Demos.Euler.run n).2.2.size = cells n := by
  unfold Demos.Euler.run cells
  split
  · exact runFrom_size n
  · rfl

theorem reconstructedRun_grid (n trials : UInt64) :
    (reconstructedRun n trials).2.2.size = cells n := by
  unfold reconstructedRun cells
  split
  · exact reconstructedRunFrom_size n trials
  · rfl

private theorem size_toUInt64 {c : Nat} (h : c ≤ 640000) : c.toUInt64.toNat = c := by
  simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (show c < 2 ^ 64 by omega)]

/-- The bound of `pack` is a block of `2 c + 5` words and its header for a grid of `c` cells. -/
theorem pack_bound (n : UInt64) (r : UInt64 × Float × Array Cell)
    (h : r.2.2.size ≤ 640000) :
    compiled.pack.bound (n, r) = 16 * r.2.2.size + 88 := by
  obtain ⟨status, time, grid⟩ := r
  dsimp only at h ⊢
  rw [compiled.pack.bound_eq, _root_.Verified.blockCost_eq, UInt64.toNat_add, UInt64.toNat_mul,
    size_toUInt64 h]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The tries of the timestep that `advanceStep` takes from `time` on `grid`: the passes of the
loop of `advanceWith`, and none when the grid fails its scan. -/
def stepTries (n : UInt64) (time : Float) (grid : Array Cell) : Nat :=
  if ((scan grid).1 == 0) = true then
    _root_.Verified.loopCost (fun _ => 0) (fun s : UInt64 × Float × Array Cell => s.1 == 9)
      (fun _ _ => 1) (fun _ s => attempt n time s.2.1 s.2.2) 2048 0
      (9, proposal n time (scan grid).2, grid)
  else 0

/-- The tries of a run of `n`: those of each timestep, summed over the passes of the loop of
`runFrom`. -/
def tries (n : UInt64) : Nat :=
  if (2 ≤ n && n ≤ 800) = true then
    _root_.Verified.loopCost (fun _ => 0)
      (fun s : UInt64 × Float × Array Cell => s.1 == 0 && s.2.1.toBits != endTime.toBits)
      (fun _ s => stepTries n s.2.1 s.2.2) (fun _ s => advanceStep n s.1 s.2.1 s.2.2)
      4294967296 0 (0, 0, initialCells n)
  else 0

private theorem mul_one_add_two (a t : Nat) : a * (1 + 2 * t) = a + 2 * a * t := by
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm a 2]

/-- The bytes by which a call of `solve n` can raise `top`, where `c` is `cells n`: a block of
`6 c + 1` words and its 48-byte header for the initial grid and for each of at most two sweeps per
try, and a block of `2 c + 5` words and its header for the result. -/
def solveBytes (n : UInt64) : Nat :=
  (48 * cells n + 56) * (1 + 2 * tries n) + 16 * cells n + 88

theorem attempt_bound (n : UInt64) (time dt : Float) (grid : Array Cell)
    (h : grid.size ≤ 640000) :
    compiled.attempt.bound (n, time, dt, { val := grid }) ≤ 2 * (48 * grid.size + 56) * 1 := by
  rw [compiled.attempt.bound_eq]
  split
  · rw [compiled.tryStep.bound_eq, compiled.step.bound_eq, compiled.finishStep.bound_eq,
      compiled.sweep.bound_eq, _root_.Verified.blockCost_eq, size_toUInt64 h]
    split
    · rw [compiled.sweep.bound_eq, _root_.Verified.blockCost_eq,
        sweep_size n false _ grid (by omega), size_toUInt64 h]
      omega
    · omega
  · exact Nat.zero_le _

theorem advanceStep_bound (n status : UInt64) (time : Float) (grid : Array Cell)
    (h : grid.size ≤ 640000) :
    compiled.advanceStep.bound (n, status, time, { val := grid }) ≤
      2 * (48 * grid.size + 56) * stepTries n time grid := by
  rw [compiled.advanceStep.bound_eq, stepTries]
  by_cases hs : ((scan grid).1 == 0) = true
  · rw [ite_eq_left hs, ite_eq_left hs, compiled.advanceWith.bound_eq]
    simp only [UInt64.reduceToNat]
    refine loopCost_le_mul (fun s : UInt64 × Float × Array Cell => s.2.2.size = grid.size) _
      ?hC ?hF ?hcost ?hstep _ _ _ rfl
    case hC => rintro ⟨_, _, _⟩; rfl
    case hF => rintro _ ⟨_, _, _⟩; rfl
    case hcost =>
      rintro _ ⟨_, dt, g⟩ hg -
      dsimp only at hg ⊢
      rw [← hg]
      exact attempt_bound n time dt g (by omega)
    case hstep =>
      rintro _ ⟨_, dt, g⟩ hg -
      dsimp only at hg ⊢
      rw [attempt_size n time dt g (by omega), hg]
  · rw [ite_eq_right hs, ite_eq_right hs]
    exact Nat.zero_le _

/-- The bound of `solve` is at most `solveBytes n`. -/
theorem solve_bound (n : UInt64) : compiled.solve.bound n ≤ solveBytes n := by
  have hc := cells_le n
  have hpack := pack_bound n (Demos.Euler.run n) (by rw [run_grid]; exact hc)
  rw [run_grid] at hpack
  rw [compiled.solve.bound_eq, hpack, compiled.run.bound_eq]
  unfold solveBytes tries
  by_cases hn : (2 ≤ n && n ≤ 800) = true
  · have hcn : (n * n).toNat = cells n := by rw [cells, ite_eq_left hn]
    rw [ite_eq_left hn, ite_eq_left hn, compiled.runFrom.bound_eq, compiled.initialCells.bound_eq,
      _root_.Verified.blockCost_eq, hcn, mul_one_add_two]
    simp only [UInt64.reduceToNat]
    refine Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left (loopCost_le_mul
      (fun s : UInt64 × Float × Array Cell => s.2.2.size = cells n) (2 * (48 * cells n + 56))
      (C' := fun s : UInt64 × Float × Array Cell => s.1 == 0 && s.2.1.toBits != endTime.toBits)
      (BB := fun _ s => stepTries n s.2.1 s.2.2)
      (F' := fun _ s => advanceStep n s.1 s.2.1 s.2.2) ?hC ?hF ?hcost ?hstep _ _ _ ?hI) _) _) ?_
    case hC => rintro ⟨_, _, _⟩; rfl
    case hF => rintro _ ⟨_, _, _⟩; rfl
    case hcost =>
      rintro _ ⟨status, time, g⟩ hs -
      dsimp only at hs ⊢
      rw [← hs]
      exact advanceStep_bound n status time g (by omega)
    case hstep =>
      rintro _ ⟨status, time, g⟩ hs -
      dsimp only at hs ⊢
      rw [advanceStep_size (by omega), hs]
    case hI => exact (initialCells_size n).trans hcn
    omega
  · have hc0 : cells n = 0 := by rw [cells, ite_eq_right hn]
    rw [ite_eq_right hn, ite_eq_right hn, hc0, _root_.Verified.blockCost_eq]
    simp

/-- The tries of the timestep that `reconstructedAdvanceStep` takes from `time` on `grid`: the
passes of the loop of `reconstructedAdvanceWith`, and none when the grid fails its bound. -/
def reconstructedStepTries (n trials : UInt64) (time : Float) (grid : Array Cell) : Nat :=
  if ((gridUpper grid).status == 0) = true then
    _root_.Verified.loopCost (fun _ => 0) (fun s : UInt64 × Float × Array Cell => s.1 == 9)
      (fun _ _ => 1)
      (fun _ s => reconstructedAttempt n trials time (gridUpper grid).value s.2.1 s.2.2) 2048 0
      (9, proposal n time (gridUpper grid).value, grid)
  else 0

/-- The tries of a reconstructed run of `n`: those of each timestep, summed over the passes of the
loop of `reconstructedRunFrom`. -/
def reconstructedTries (n trials : UInt64) : Nat :=
  if (2 ≤ n && n ≤ 800) = true then
    _root_.Verified.loopCost (fun _ => 0)
      (fun s : UInt64 × Float × Array Cell => s.1 == 0 && s.2.1.toBits != endTime.toBits)
      (fun _ s => reconstructedStepTries n trials s.2.1 s.2.2)
      (fun _ s => reconstructedAdvanceStep n trials s.2.1 s.2.2) 4294967296 0
      (0, 0, initialCells n)
  else 0

/-- `solveBytes` for the reconstructed solver. -/
def reconstructedSolveBytes (n trials : UInt64) : Nat :=
  (48 * cells n + 56) * (1 + 2 * reconstructedTries n trials) + 16 * cells n + 88

theorem reconstructedAttempt_bound (n trials : UInt64) (time alpha dt : Float)
    (grid : Array Cell) (h : grid.size ≤ 640000) :
    compiled.reconstructedAttempt.bound (n, trials, time, alpha, dt, { val := grid }) ≤
      2 * (48 * grid.size + 56) * 1 := by
  rw [compiled.reconstructedAttempt.bound_eq]
  split
  · split
    · rw [compiled.reconstructedTry.bound_eq, compiled.reconstructedStepGrid.bound_eq,
        compiled.reconstructedFinish.bound_eq, compiled.reconstructedSweep.bound_eq,
        _root_.Verified.blockCost_eq, size_toUInt64 h]
      split
      · rw [compiled.reconstructedSweep.bound_eq, _root_.Verified.blockCost_eq,
          reconstructedSweep_size n false trials _ grid (by omega), size_toUInt64 h]
        omega
      · omega
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem reconstructedAdvanceStep_bound (n trials : UInt64) (time : Float) (grid : Array Cell)
    (h : grid.size ≤ 640000) :
    compiled.reconstructedAdvanceStep.bound (n, trials, time, { val := grid }) ≤
      2 * (48 * grid.size + 56) * reconstructedStepTries n trials time grid := by
  rw [compiled.reconstructedAdvanceStep.bound_eq, reconstructedStepTries]
  by_cases hs : ((gridUpper grid).status == 0) = true
  · rw [ite_eq_left hs, ite_eq_left hs, compiled.reconstructedAdvanceWith.bound_eq]
    simp only [UInt64.reduceToNat]
    refine loopCost_le_mul (fun s : UInt64 × Float × Array Cell => s.2.2.size = grid.size) _
      ?hC ?hF ?hcost ?hstep _ _ _ rfl
    case hC => rintro ⟨_, _, _⟩; rfl
    case hF => rintro _ ⟨_, _, _⟩; rfl
    case hcost =>
      rintro _ ⟨_, dt, g⟩ hg -
      dsimp only at hg ⊢
      rw [← hg]
      exact reconstructedAttempt_bound n trials time _ dt g (by omega)
    case hstep =>
      rintro _ ⟨_, dt, g⟩ hg -
      dsimp only at hg ⊢
      rw [reconstructedAttempt_size n trials time _ dt g (by omega), hg]
  · rw [ite_eq_right hs, ite_eq_right hs]
    exact Nat.zero_le _

/-- The bound of `reconstructedSolve` is at most `reconstructedSolveBytes n trials`. -/
theorem reconstructedSolve_bound (n trials : UInt64) :
    compiled.reconstructedSolve.bound (n, trials) ≤ reconstructedSolveBytes n trials := by
  have hc := cells_le n
  have hpack := pack_bound n (reconstructedRun n trials)
    (by rw [reconstructedRun_grid]; exact hc)
  rw [reconstructedRun_grid] at hpack
  rw [compiled.reconstructedSolve.bound_eq, hpack, compiled.reconstructedRun.bound_eq]
  unfold reconstructedSolveBytes reconstructedTries
  by_cases hn : (2 ≤ n && n ≤ 800) = true
  · have hcn : (n * n).toNat = cells n := by rw [cells, ite_eq_left hn]
    rw [ite_eq_left hn, ite_eq_left hn, compiled.reconstructedRunFrom.bound_eq,
      compiled.initialCells.bound_eq, _root_.Verified.blockCost_eq, hcn, mul_one_add_two]
    simp only [UInt64.reduceToNat]
    refine Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left (loopCost_le_mul
      (fun s : UInt64 × Float × Array Cell => s.2.2.size = cells n) (2 * (48 * cells n + 56))
      (C' := fun s : UInt64 × Float × Array Cell => s.1 == 0 && s.2.1.toBits != endTime.toBits)
      (BB := fun _ s => reconstructedStepTries n trials s.2.1 s.2.2)
      (F' := fun _ s => reconstructedAdvanceStep n trials s.2.1 s.2.2) ?hC ?hF ?hcost ?hstep
      _ _ _ ?hI) _) _) ?_
    case hC => rintro ⟨_, _, _⟩; rfl
    case hF => rintro _ ⟨_, _, _⟩; rfl
    case hcost =>
      rintro _ ⟨_, time, g⟩ hs -
      dsimp only at hs ⊢
      rw [← hs]
      exact reconstructedAdvanceStep_bound n trials time g (by omega)
    case hstep =>
      rintro _ ⟨_, time, g⟩ hs -
      dsimp only at hs ⊢
      rw [reconstructedAdvanceStep_size (by omega), hs]
    case hI => exact (initialCells_size n).trans hcn
    omega
  · have hc0 : cells n = 0 := by rw [cells, ite_eq_right hn]
    rw [ite_eq_right hn, ite_eq_right hn, hc0, _root_.Verified.blockCost_eq]
    simp

/-- The pages that hold the heap base, 4096 bytes, and `solveBytes n` bytes above it. -/
def solvePages (n : UInt64) : Nat := (4096 + solveBytes n + 65535) / 65536

/-- The pages that hold the heap base and `reconstructedSolveBytes n trials` bytes above it. -/
def reconstructedSolvePages (n trials : UInt64) : Nat :=
  (4096 + reconstructedSolveBytes n trials + 65535) / 65536

/-- Entry 23 computes `solve` from every ready store in which `top` can rise by `solveBytes n`
bytes within the memory cap, and `top` rises by at most that much. -/
theorem solve_callSpec :
    _root_.Verified.CallSpec compiled.module compiled.tables 23 solve solveBytes :=
  (_root_.Verified.ImplementsTables.call
    (_root_.Verified.ImplementsTables.ofA compiled.solve.trapFree) compiled.tables nofun).spec
    (fun x _ _ h => h.mono (solve_bound x))
    (fun x _ _ _ _ h => h.trans (Nat.add_le_add_left (solve_bound x) _))
    fun _ _ _ _ _ => rfl

/-- Entry 56 computes `reconstructedSolve` from every ready store in which `top` can rise by
`reconstructedSolveBytes n trials` bytes within the memory cap, and `top` rises by at most that
much. -/
theorem reconstructedSolve_callSpec :
    _root_.Verified.CallSpec compiled.module compiled.tables 56
      (fun x : UInt64 × UInt64 => reconstructedSolve x.1 x.2)
      (fun x => reconstructedSolveBytes x.1 x.2) :=
  (_root_.Verified.ImplementsTables.call
    (_root_.Verified.ImplementsTables.ofA compiled.reconstructedSolve.trapFree) compiled.tables
    nofun).spec
    (fun x _ _ h => h.mono (reconstructedSolve_bound x.1 x.2))
    (fun x _ _ _ _ h => h.trans (Nat.add_le_add_left (reconstructedSolve_bound x.1 x.2) _))
    fun _ _ _ _ _ => rfl

theorem solve_export :
    ({ name := "solve", funcIdx := 23 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem reconstructedSolve_export :
    ({ name := "reconstructedSolve", funcIdx := 56 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The store in which the module starts, with the memory cap set to `cap` pages, is ready.  The
module has no tables. -/
theorem ready_initial (cap : Nat) (hcap : cap ≤ 65535) :
    _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables)
      { (compiled.module.initialStore : Store Unit) with memoryCaps := [cap] } := by
  obtain ⟨hAt, -, -⟩ := _root_.Verified.Ready.initial rfl compiled.initial
  exact ⟨⟨hAt.globals, hAt.freeList, hAt.base, hAt.top, hAt.pages, hAt.above, hAt.below⟩,
    hcap, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

/-- The bytes of `compiled.module` decode to the module, whose exports `solve` and
`reconstructedSolve` are entries 23 and 56.  Called from the store in which the module starts,
with a memory cap of `cap` pages, at least `solvePages n` and at most 65,535, entry 23 returns
without a trap the address of a new array that holds `solve n`.  It leaves a
ready store in which `top` lies at most `solveBytes n` bytes above the heap base.  Entry 56 does
the same for `reconstructedSolve n trials`, with `reconstructedSolvePages n trials` and
`reconstructedSolveBytes n trials`. -/
theorem euler_solve_call :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
    ({ name := "solve", funcIdx := 23 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "reconstructedSolve", funcIdx := 56 } : Wasm.Export) ∈ compiled.module.exports ∧
    (∀ (env : HostEnv Unit) (n : UInt64) (cap : Nat), solvePages n ≤ cap → cap ≤ 65535 →
      Runs false env compiled.module 23
        { (compiled.module.initialStore : Store Unit) with memoryCaps := [cap] } [.i64 n]
        fun final values => ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap,
          heap'.Owned final optr (solve n) ∧
          _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
          heap'.top.toNat ≤ 4096 + solveBytes n) ∧
    (∀ (env : HostEnv Unit) (n trials : UInt64) (cap : Nat),
      reconstructedSolvePages n trials ≤ cap → cap ≤ 65535 →
      Runs false env compiled.module 56
        { (compiled.module.initialStore : Store Unit) with memoryCaps := [cap] }
        [.i64 trials, .i64 n]
        fun final values => ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap,
          heap'.Owned final optr (reconstructedSolve n trials) ∧
          _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
          heap'.top.toNat ≤ 4096 + reconstructedSolveBytes n trials) := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  have htop : (_root_.Verified.initialHeap compiled.tables).top.toNat = 4096 := rfl
  refine ⟨⟨bytes, henc, hdec⟩, solve_export, reconstructedSolve_export,
    fun env n cap hpages hcap => ?_, fun env n trials cap hpages hcap => ?_⟩
  · refine (_root_.Verified.Call.array solve_callSpec env _ _ [.i64 n] n (ready_initial cap hcap)
      rfl rfl ?_).mono fun _ _ ⟨optr, hv, heap', hown, hR, _, _, hrise⟩ =>
        ⟨optr, hv, heap', hown, hR, htop ▸ hrise⟩
    show (_root_.Verified.initialHeap compiled.tables).top.toNat + solveBytes n ≤ 65536 * cap
    unfold solvePages at hpages
    omega
  · refine (_root_.Verified.Call.array reconstructedSolve_callSpec env _ _ [.i64 n, .i64 trials]
      (n, trials) (ready_initial cap hcap) rfl rfl ?_).mono
        fun _ _ ⟨optr, hv, heap', hown, hR, _, _, hrise⟩ =>
          ⟨optr, hv, heap', hown, hR, htop ▸ hrise⟩
    show (_root_.Verified.initialHeap compiled.tables).top.toNat +
      reconstructedSolveBytes n trials ≤ 65536 * cap
    unfold reconstructedSolvePages at hpages
    omega

#print axioms loopCost_le_mul
#print axioms solve_bound
#print axioms reconstructedSolve_bound
#print axioms solve_callSpec
#print axioms reconstructedSolve_callSpec
#print axioms solve_export
#print axioms reconstructedSolve_export
#print axioms ready_initial
#print axioms euler_solve_call

end Demos.Euler.Verified
