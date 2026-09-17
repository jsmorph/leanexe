import LeanExe.WGSL.StatementRun

namespace LeanExe.WGSL.Statement
open Source

theorem readLocal_ok {words : List UInt32} {slot : Nat} (h : slot < words.length) :
    readLocal words slot = .ok (words[slot]?.getD 0) := by
  simp [readLocal, List.getElem?_eq_getElem h]

theorem AccessValid.bounds {shape ranges size i} (h : AccessValid shape ranges size i) :
    ∃ bound, i.bound shape ranges = .ok bound ∧ bound < size := by
  unfold AccessValid at h
  split at h
  next he => contradiction
  next bound he => exact ⟨bound, he, h⟩

theorem Prim.run_eq {shape : Shape} {ranges : List Nat}
    (ar : ScalarArithmetic) (memory : Memory) (row col : UInt32)
    (indices words : List UInt32) (p : Prim)
    (hr : row.toNat < shape.rows) (hc : col.toNat < shape.cols)
    (ha : shape.elementsA ≤ memory.sizeA) (hb : shape.elementsB ≤ memory.sizeB)
    (hi : LocalsBound (indices.map UInt32.toNat) ranges)
    (valid : p.Valid shape ranges words.length) :
    p.run ar memory row col indices words =
      .ok (p.term.eval ar memory.a memory.b row.toNat col.toNat
        (indices.map UInt32.toNat) words) := by
  cases p with
  | literal w => rfl
  | copy slot => exact readLocal_ok valid
  | loadA i =>
      obtain ⟨bound, he, hlt⟩ := AccessValid.bounds valid
      have eq := i.word_eq hr hc hi he
      have le := i.bound_le hr hc hi he
      simp only [Prim.run, Prim.term, Term.eval, eq]
      rw [ite_eq_left (by omega)]
  | loadB i =>
      obtain ⟨bound, he, hlt⟩ := AccessValid.bounds valid
      have eq := i.word_eq hr hc hi he
      have le := i.bound_le hr hc hi he
      simp only [Prim.run, Prim.term, Term.eval, eq]
      rw [ite_eq_left (by omega)]
  | add a b =>
      simp only [Prim.Valid] at valid
      simp [Prim.run, Prim.term, Term.eval, readLocal_ok valid.1, readLocal_ok valid.2,
        bind, Except.bind, pure, Except.pure]
  | mul a b =>
      simp only [Prim.Valid] at valid
      simp [Prim.run, Prim.term, Term.eval, readLocal_ok valid.1, readLocal_ok valid.2,
        bind, Except.bind, pure, Except.pure]

/-- Loop execution follows the u32 test and increment. The invariant gives the
accumulator after precisely `k` completed iterations. This also proves that the
budget error cannot occur and that the counter never wraps. -/
theorem loopRun_eq (body : UInt32 → UInt32 → Except Error UInt32)
    (step : Nat → UInt32 → UInt32) (initial : UInt32) (count : Nat)
    (hc : count < 4294967296)
    (hbody : ∀ k, k < count → ∀ acc, body (UInt32.ofNat k) acc = .ok (step k acc))
    (fuel k : Nat) (hk : k + fuel = count) :
    loopRun body (UInt32.ofNat count) fuel (UInt32.ofNat k) (Source.fold k initial step) =
      .ok (Source.fold count initial step) := by
  induction fuel generalizing k with
  | zero =>
      have h : k = count := by omega
      subst k
      simp [loopRun]
  | succ fuel ih =>
      have hkc : k < count := by omega
      have hk32 : k < 4294967296 := by omega
      have test : UInt32.ofNat k < UInt32.ofNat count := by
        simpa only [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hc,
          Nat.mod_eq_of_lt hk32] using hkc
      have inc : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
        apply UInt32.toNat_inj.1
        simp [UInt32.toNat_add, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hk32]
      rw [loopRun, ite_eq_left test, hbody k hkc]
      dsimp only [Bind.bind, Except.bind]
      rw [inc]
      exact ih (k + 1) (by omega)

theorem Code.run_eq {shape : Shape} {ranges : List Nat}
    (ar : ScalarArithmetic) (memory : Memory) (row col : UInt32)
    (indices words : List UInt32) (code : Code)
    (hr : row.toNat < shape.rows) (hc : col.toNat < shape.cols)
    (ha : shape.elementsA ≤ memory.sizeA) (hb : shape.elementsB ≤ memory.sizeB)
    (hi : LocalsBound (indices.map UInt32.toNat) ranges)
    (valid : code.Valid shape ranges words.length) :
    code.run ar memory row col indices words =
      .ok (code.term.eval ar memory.a memory.b row.toNat col.toNat
        (indices.map UInt32.toNat) words) := by
  induction code generalizing ranges indices words with
  | finish n => exact readLocal_ok valid
  | bind value next ih =>
      simp only [Code.Valid] at valid
      rw [Code.run, value.run_eq ar memory row col indices words hr hc ha hb hi valid.1]
      dsimp only [Bind.bind, Except.bind]
      exact ih indices _ hi (by simpa using valid.2)
  | loop count initial body next ihbody ihnext =>
      rcases valid with ⟨hcount, hinitial, hbody, hnext⟩
      let step := fun k acc => body.term.eval ar memory.a memory.b row.toNat col.toNat
        (k :: indices.map UInt32.toNat) (acc :: words)
      have bodyOk : ∀ k, k < count → ∀ acc,
          body.run ar memory row col (UInt32.ofNat k :: indices) (acc :: words) =
            .ok (step k acc) := by
        intro k hk acc
        have hk32 : (UInt32.ofNat k).toNat = k :=
          UInt32.toNat_ofNat_of_lt' (by change k < 4294967296; omega)
        have hiv : LocalsBound ((UInt32.ofNat k :: indices).map UInt32.toNat)
            ((count - 1) :: ranges) := by
          simp only [List.map_cons, hk32]
          exact hi.cons (by omega)
        simpa only [List.map_cons, hk32] using
          ihbody (UInt32.ofNat k :: indices) (acc :: words) hiv (by simpa using hbody)
      have loopOk := loopRun_eq
        (fun k acc => body.run ar memory row col (k :: indices) (acc :: words))
        step (words[initial]?.getD 0) count (by omega) bodyOk count 0 (by omega)
      change loopRun _ _ _ (0 : UInt32) (words[initial]?.getD 0) =
        .ok (Source.fold count (words[initial]?.getD 0) step) at loopOk
      rw [Code.run, readLocal_ok hinitial]
      dsimp only [Bind.bind, Except.bind]
      rw [loopOk]
      dsimp only [Bind.bind, Except.bind]
      exact ihnext indices _ hi (by simpa using hnext)

end LeanExe.WGSL.Statement
