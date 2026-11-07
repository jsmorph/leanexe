import LeanExe.A64.Proof.ImageTheorem
import LeanExe.A64.Image
import LeanExe.Pipeline.Implements

/-!
`ProgramRuns` from the compiler's theorem of the function that a program calls.  `program_runs`
takes `ImplementsA` of function `k` of `m`, an argument whose values, of the parameters' types `ts`,
have the program's arguments as their words, and a heap at the module's initial store that satisfies
the theorem's precondition.  The types `ts` default to `i64` for every argument.  It gives
`ProgramRuns` for the bytes of the function's result, with the status 1 of the trap at `unreachable`
when the theorem allows that trap, and the status 4 of an overflow of the stack when function `k`
calls others and the room lies below `stackBound m k`.  `program_runs_implements` states the
statuses 1 and 4, `program_runs_trapFree` the status 4 for a theorem without the trap, and
`program_runs_bounded` no status for a theorem without the trap and a room that holds the stack's
bound.  `entryOk` holds the facts about the module that `genProgram` leaves unchecked, and each
theorem takes it from the kernel's evaluation by default.
-/

namespace LeanExe.A64

open Wasm LeanExe.Pipeline

/-- The facts about function `k` of `m` that `program_sim` needs and `genProgram` does not check,
for `n` arguments and the output `o`: `m` imports no function, function `k` takes `n` parameters
of the types `ts`, and the program's instructions, those of `main`, of the functions that calls
reach from function `k`, and of the trap stubs, number fewer than 2^62. -/
def entryOk (m : Module) (k : Nat) (ts : List ValueType) (n : Nat) (o : Output) : Bool :=
  m.imports.isEmpty && decide ((m.funcs[k]?).map (·.params) = some ts) &&
    decide (ts.length = n) && match (reachFrom m k).mapM (funcOf m) with
    | .ok fs => decide (4 * (mainSize n o +
        (fs.map fun x => functionSize (sigIn (callTargets m k) fs) x.2).sum + 20) < 2 ^ 64)
    | .error _ => false

/-- The number of pages with which the memory of `m` starts, or 0 when `m` has no memory. -/
def initialPages (m : Module) : Nat := (m.memory.map (·.pagesMin.toNat)).getD 0

/-- The bytes `out` that `main` writes in the form `o` for the values `vs` that the function
returns in the store `st`: the eight bytes of the one value's word, or the bytes of the array at
the pointer that the one value holds. -/
def Writes : Output → Store Unit → List Value → List UInt8 → Prop
  | .word, _, vs, out => ∃ v w, vs = [v] ∧ ValRel v w ∧ out = bytesOf w
  | .array, st, vs, out => ∃ ptr ws, vs = [.i64 ptr] ∧
      LeanExe.ProofKit.UInt64Array.At st ptr ws ∧ out = arrayBytes ws

/-- An owned result of type `UInt64` gives its eight bytes. -/
theorem writes_word (heap : Heap) (st : Store Unit) (vs : List Value) (y : UInt64)
    (h : Represent.owned heap st vs y) : Writes .word st vs (bytesOf y) :=
  ⟨.i64 y, y, h, rfl, rfl⟩

/-- An owned result of type `Float` gives the eight bytes of its word. -/
theorem writes_float (heap : Heap) (st : Store Unit) (vs : List Value) (y : Float)
    (h : Represent.owned heap st vs y) : Writes .word st vs (bytesOf y.toBits) :=
  ⟨.f64 y.toBits, y.toBits, h, rfl, rfl⟩

/-- A value is the value of at most one word. -/
theorem ValRel.unique {v : Value} {w w' : UInt64} (h : ValRel v w) (h' : ValRel v w') :
    w = w' := by
  cases v <;> simp only [ValRel] at h h' <;> rw [h, h']

/-- An owned result of type `Array UInt64` gives the bytes of the array. -/
theorem writes_array (heap : Heap) (st : Store Unit) (vs : List Value) (y : Array UInt64)
    (h : Represent.owned heap st vs y) : Writes .array st vs (arrayBytes y) := by
  obtain ⟨ptr, hv, hO⟩ := h
  exact ⟨ptr, y, hv, hO.values, rfl⟩

theorem heapAt_initStore {heap : Heap} {m : Module} (h : heap.At (m.initialStore : Store Unit))
    (cap : Nat) : heap.At (initStore m cap) :=
  ⟨h.globals, h.freeList, h.base, h.top, h.pages, h.above, h.below⟩

/-- A heap whose `top` can rise by `n` bytes within the initial pages of the memory of `m` can do
so within a cap of `cap` pages at or above them. -/
theorem room_initStore {heap : Heap} {m : Module} {cap n : Nat}
    (h : heap.top.toNat + n ≤ 65536 * initialPages m) (hp : initialPages m ≤ cap) :
    heap.top.toNat + n ≤ 65536 * (initStore m cap).memoryCap m 0 :=
  Nat.le_trans h (Nat.mul_le_mul_left 65536 hp)

theorem ProgramRuns.mono {m : Module} {k : Nat} {args : List UInt64} {room : UInt64} {cap : Nat}
    {o : Output} {out : List UInt8} {T T' : UInt64 → Prop}
    (h : ProgramRuns m k args room cap o out T) (hT : ∀ c, T c → T' c) :
    ProgramRuns m k args room cap o out T' := by
  intro P base area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove
  exact (h P base area hg ms himage hpc hal hroom htop hstack h17 harea hamap habove).imp id
    fun ⟨ms', hr, hp, ht, ho⟩ => ⟨ms', hr, hp, hT _ ht, ho⟩

/-- `ProgramRuns` from the compiler's theorem `h` that function `k` of `m` computes `f`.  The
argument `x` has the words `args`, and the heap `heap` lies at the module's initial store and
satisfies `Pre` with the store of a memory of `cap` pages when `cap` covers the memory's initial
pages.  `hout` gives the bytes `enc y` that `main` writes in the form `o` for an owned result `y`.
The program writes `enc (f x)` and returns 0, or it reaches the exit word with the status 1 of
`unreachable` when `aborts` holds, or with the status 4 of an overflow of the stack when function
`k` calls others and `room` lies below `stackBound m k`.  The values of the argument have the
types `ts` of the function's parameters and the words `args`. -/
theorem program_runs {α β : Type} [Scalar α] [Represent β] {aborts : Bool} {m : Module}
    {k : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    {args : List UInt64} {room : UInt64} {cap : Nat} {o : Output} {enc : β → List UInt8}
    (h : ImplementsA aborts m k f Pre Post) (x : α) {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (hpre : initialPages m ≤ cap → Pre x heap (initStore m cap))
    (hout : ∀ heap st vs y, Represent.owned heap st vs y → Writes o st vs (enc y))
    (ts : List ValueType := args.map fun _ => .i64)
    (hargs : argValues ts args = Scalar.values x := by rfl)
    (hok : entryOk m k ts args.length o = true := by decide +kernel) :
    ProgramRuns m k args room cap o (enc (f x)) fun c => (aborts = true ∧ c = 1) ∨
      (callTargets m k ≠ [] ∧ room.toNat < stackBound m k ∧ c = 4) := by
  intro P base area is hg ms himage hpc hal hroom htop hstack h17 harea hamap habove
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, hao, -, -, hfs, -⟩ := gen_program hg
  have hcap := cap_lt_of_areaOk hao
  unfold entryOk at hok
  rw [hfs] at hok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨himp, hpar⟩, hlen⟩, hsize⟩ := hok
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genProgram_length hg hfs]
    exact hsize
  obtain ⟨g, hk, hp⟩ : ∃ g, m.funcs[k]? = some g ∧ g.params = ts := by
    cases hk : m.funcs[k]? with
    | none => rw [hk] at hpar; cases hpar
    | some g => rw [hk] at hpar; exact ⟨g, rfl, Option.some.inj hpar⟩
  obtain ⟨N, hN⟩ := h {} (initStore m cap) heap (argValues ts args) x
    (heapAt_initStore hheap cap) (hpre (pages_le_of_areaOk hao)) hargs Separate.nil
    (show cap ≤ 65535 by omega)
  have hs := program_sim_stack P _ hg (codeAt_fetchFrom hn himage) himp hk
    (by rw [hp, hlen]) N ms hpc hal hroom htop hstack h17 harea hamap habove
  rw [hp] at hs
  rcases hN N (Nat.le_refl _) with ⟨vs, st', hrun, heap', -, hown, -⟩ | hab
  · have hw := hout heap' st' vs.reverse (f x) hown
    cases o with
    | word =>
        obtain ⟨v, w, hv, hvw, he⟩ := hw
        rw [List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append] at hv
        subst hv
        rw [he]
        rcases ProgramOutcome.success P _ hs hrun with ⟨hc, ms', hr, hpc', hx, ho⟩ |
          ⟨w', ms', hw', hr, hpc', -, hx, ho⟩
        · exact .inr ⟨ms', hr, hpc', .inr ⟨hc.1, hc.2, hx⟩, ho⟩
        · rw [ValRel.unique hvw hw']
          exact .inl ⟨ms', hr, hpc', hx, ho⟩
    | array =>
        obtain ⟨ptr, ws, hv, hat, he⟩ := hw
        rw [List.reverse_eq_cons_iff, List.reverse_nil, List.nil_append] at hv
        subst hv
        rw [he]
        rcases ProgramOutcome.array P _ hs hrun hat with ⟨hc, ms', hr, hpc', hx, ho⟩ |
          ⟨ms', hr, hpc', -, hx, ho⟩
        · exact .inr ⟨ms', hr, hpc', .inr ⟨hc.1, hc.2, hx⟩, ho⟩
        · exact .inl ⟨ms', hr, hpc', hx, ho⟩
  · cases aborts with
    | false => exact hab.elim
    | true =>
        obtain ⟨st', hrun⟩ := hab
        rcases ProgramOutcome.unreachable P _ hs hrun with ⟨hc, ms', hr, hpc', hx, ho⟩ |
          ⟨ms', hr, hpc', hx, ho⟩
        · exact .inr ⟨ms', hr, hpc', .inr ⟨hc.1, hc.2, hx⟩, ho⟩
        · exact .inr ⟨ms', hr, hpc', .inl ⟨rfl, hx⟩, ho⟩

/-- `program_runs` with the statuses 1 and 4. -/
theorem program_runs_implements {α β : Type} [Scalar α] [Represent β] {aborts : Bool}
    {m : Module} {k : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    {args : List UInt64} {room : UInt64} {cap : Nat} {o : Output} {enc : β → List UInt8}
    (h : ImplementsA aborts m k f Pre Post) (x : α) {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (hpre : initialPages m ≤ cap → Pre x heap (initStore m cap))
    (hout : ∀ heap st vs y, Represent.owned heap st vs y → Writes o st vs (enc y))
    (ts : List ValueType := args.map fun _ => .i64)
    (hargs : argValues ts args = Scalar.values x := by rfl)
    (hok : entryOk m k ts args.length o = true := by decide +kernel) :
    ProgramRuns m k args room cap o (enc (f x)) fun c => c = 1 ∨ c = 4 :=
  (program_runs h x hheap hpre hout ts hargs hok).mono fun _ hc =>
    hc.imp And.right fun h => h.2.2

/-- `program_runs` for a theorem without the trap at `unreachable`: the status 4 alone. -/
theorem program_runs_trapFree {α β : Type} [Scalar α] [Represent β] {m : Module} {k : Nat}
    {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    {args : List UInt64} {room : UInt64} {cap : Nat} {o : Output} {enc : β → List UInt8}
    (h : ImplementsA false m k f Pre Post) (x : α) {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (hpre : initialPages m ≤ cap → Pre x heap (initStore m cap))
    (hout : ∀ heap st vs y, Represent.owned heap st vs y → Writes o st vs (enc y))
    (ts : List ValueType := args.map fun _ => .i64)
    (hargs : argValues ts args = Scalar.values x := by rfl)
    (hok : entryOk m k ts args.length o = true := by decide +kernel) :
    ProgramRuns m k args room cap o (enc (f x)) fun c => c = 4 :=
  (program_runs h x hheap hpre hout ts hargs hok).mono fun _ hc => by
    rcases hc with ⟨hf, -⟩ | ⟨-, -, h4⟩
    · cases hf
    · exact h4

/-- `program_runs` for a theorem without the trap at `unreachable` and a stack whose bound is at
most 4096 bytes, which `ProgramRuns` requires of the room, or at most `room`: no status. -/
theorem program_runs_bounded {α β : Type} [Scalar α] [Represent β] {m : Module} {k : Nat}
    {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    {args : List UInt64} {room : UInt64} {cap : Nat} {o : Output} {enc : β → List UInt8}
    (h : ImplementsA false m k f Pre Post) (x : α) {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (hpre : initialPages m ≤ cap → Pre x heap (initStore m cap))
    (hout : ∀ heap st vs y, Represent.owned heap st vs y → Writes o st vs (enc y))
    (hbound : stackBound m k ≤ 4096 ∨ stackBound m k ≤ room.toNat)
    (ts : List ValueType := args.map fun _ => .i64)
    (hargs : argValues ts args = Scalar.values x := by rfl)
    (hok : entryOk m k ts args.length o = true := by decide +kernel) :
    ProgramRuns m k args room cap o (enc (f x)) fun _ => False := by
  intro P base area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove
  rcases program_runs h x hheap hpre hout ts hargs hok P base area hg ms himage hpc hal hroom htop
    hstack h17 harea hamap habove with hr | ⟨_, -, -, ⟨hf, -⟩ | ⟨-, hlt, -⟩, -⟩
  · exact .inl hr
  · cases hf
  · omega

end LeanExe.A64
