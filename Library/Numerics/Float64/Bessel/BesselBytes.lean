import Library.Numerics.Float64.Bessel.BesselJ0Theorem
import Library.Numerics.Float64.Bessel.BesselJ1Theorem
import Library.Numerics.Float64.Bessel.BesselY0Theorem
import Library.Numerics.Float64.Bessel.BesselY1Theorem
import Library.Numerics.Float64.Bessel.BesselYnTheorem
import LeanExe.ProofKit.BorrowedKept

/-!
The byte theorems for `j0`, `j1`, `y0`, `y1`, `jn`, and `yn` in the module of `Bessel.lean`, whose
exports `j0`, `j1`, `y0`, `y1`, `jn`, and `yn` are functions 36 to 41.  The module writes six
tables from address 4096: `Trig.invPi` at 4096, `Trig.halfPi` at 4264, `Bessel.j0Table` at 4288,
`Bessel.j1Table` at 5032, `Log.logTable` at 5856, and `Log.logTable2` at 7912.  `j0` and `j1` read
the first two and their own table, `y0` and `y1` also read the two tables of `Log`, and `jn` and
`yn` read all six.  A store is ready when the allocator invariant holds, the six tables are
borrowed arrays at their addresses, and the memory cap is at most 65,535 pages.  A call of any of
the six entries from a ready store returns without a trap the bits of the Lean function and leaves
a ready store, so the theorems cover every sequence of calls to the six entries from the initial
store.  The bounds are those of `BesselJ0Theorem.j0_accuracy`, `BesselJ1Theorem.j1_accuracy`,
`BesselY0Theorem.y0_accuracy`, `BesselY1Theorem.y1_positive`, `BesselJnTheorem.jn_accuracy`, and
`BesselYnTheorem.yn_accuracy` with `yn_overflow`, and `bessel_module_accuracy` states all six.
The entries `jn` and `yn` take the order and then the argument.
-/

namespace Library.Numerics.Float64.Bessel.BesselBytes
open CodeLib.IEEE64
open LeanExe.ProofKit
open LeanExe.ProofKit.Bessel (J0 Y0 J1 Y1)
open BesselOrderN (JZ YZ)
open BesselRecur (modn)
open BesselJnTheorem (orderZ)
open BesselYnOrderOne (YBound)

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entries run, with `heap` the allocator's state. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Trig.invPi ∧ heap.Borrowed store 4264 Trig.halfPi ∧
    heap.Borrowed store 4288 Bessel.j0Table ∧ heap.Borrowed store 5032 Bessel.j1Table ∧
    heap.Borrowed store 5856 Log.logTable ∧ heap.Borrowed store 7912 Log.logTable2 ∧
    store.memoryCap Bessel.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Bessel.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hBor 2 (by decide), hBor 3 (by decide),
    hBor 4 (by decide), hBor 5 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- After a call that keeps every region of the heap, a ready store stays ready. -/
theorem ready_kept (heap heap' : Heap) (store final : Store Unit) (h : Ready heap store)
    (hAt' : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r)
    (hcap : final.memoryCap Bessel.compiled.module 0 ≤ 65535) : Ready heap' final :=
  ⟨hAt', BorrowedKept.borrowed_kept h.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.1 hAt' hkeep, BorrowedKept.borrowed_kept h.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.1 hAt' hkeep,
    BorrowedKept.borrowed_kept h.2.2.2.2.2.2.1 hAt' hkeep, hcap⟩

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store that `j0` reads, as its entry takes them. -/
theorem j0_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi),
        ((4288 : UInt64), Bessel.j0Table)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `j0` entry from a ready store. -/
theorem j0_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Bessel.compiled.module 36 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Bessel.j0 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Bessel.compiled.j0.implements env store heap [.f64 x.toBits] x h.1 trivial
    (j0_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Bessel.j0 x).toBits] := howned
  have hvs : values = [.f64 (Bessel.j0 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2), hkeep⟩

/-- Function 36 of the module is its export `j0`. -/
theorem j0_export :
    ({ name := "j0", funcIdx := 36 } : Wasm.Export) ∈ Bessel.compiled.module.exports := by
  decide +kernel

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store that `j1` reads, as its entry takes them. -/
theorem j1_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi),
        ((5032 : UInt64), Bessel.j1Table)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `j1` entry from a ready store. -/
theorem j1_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Bessel.compiled.module 37 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Bessel.j1 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Bessel.compiled.j1.implements env store heap [.f64 x.toBits] x h.1 trivial
    (j1_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Bessel.j1 x).toBits] := howned
  have hvs : values = [.f64 (Bessel.j1 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2), hkeep⟩

/-- Function 37 of the module is its export `j1`. -/
theorem j1_export :
    ({ name := "j1", funcIdx := 37 } : Wasm.Export) ∈ Bessel.compiled.module.exports := by
  decide +kernel

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store that `y0` reads, as its entry takes them. -/
theorem y0_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi),
        ((5856 : UInt64), Log.logTable), ((7912 : UInt64), Log.logTable2),
        ((4288 : UInt64), Bessel.j0Table)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `y0` entry from a ready store. -/
theorem y0_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Bessel.compiled.module 38 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Bessel.y0 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Bessel.compiled.y0.implements env store heap [.f64 x.toBits] x h.1 trivial
    (y0_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Bessel.y0 x).toBits] := howned
  have hvs : values = [.f64 (Bessel.y0 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2), hkeep⟩

/-- Function 38 of the module is its export `y0`. -/
theorem y0_export :
    ({ name := "y0", funcIdx := 38 } : Wasm.Export) ∈ Bessel.compiled.module.exports := by
  decide +kernel

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store that `y1` reads, as its entry takes them. -/
theorem y1_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi),
        ((5856 : UInt64), Log.logTable), ((7912 : UInt64), Log.logTable2),
        ((5032 : UInt64), Bessel.j1Table)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `y1` entry from a ready store. -/
theorem y1_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Bessel.compiled.module 39 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Bessel.y1 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Bessel.compiled.y1.implements env store heap [.f64 x.toBits] x h.1 trivial
    (y1_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Bessel.y1 x).toBits] := howned
  have hvs : values = [.f64 (Bessel.y1 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2), hkeep⟩

/-- Function 39 of the module is its export `y1`. -/
theorem y1_export :
    ({ name := "y1", funcIdx := 39 } : Wasm.Export) ∈ Bessel.compiled.module.exports := by
  decide +kernel

open Wasm LeanExe.Pipeline in
/-- The tables of a ready store that `jn` and `yn` read, as their entries take them. -/
theorem jn_tables (heap : Heap) (store : Store Unit) (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi),
        ((5856 : UInt64), Log.logTable), ((7912 : UInt64), Log.logTable2),
        ((4288 : UInt64), Bessel.j0Table), ((5032 : UInt64), Bessel.j1Table)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.1, Apart.nil⟩
  · exact ⟨h.2.2.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `jn` entry from a ready store.  The entry takes `n` and then `x`; the
list of arguments is in reverse order. -/
theorem jn_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (n : UInt64)
    (x : Float) (h : Ready heap store) :
    Runs false env Bessel.compiled.module 40 store [.f64 x.toBits, .i64 n] fun final values =>
      values = [.f64 (Bessel.jn n x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Bessel.compiled.jn.implements env store heap [.i64 n, .f64 x.toBits] (n, x) h.1 trivial
    (jn_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Bessel.jn n x).toBits] := howned
  have hvs : values = [.f64 (Bessel.jn n x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2), hkeep⟩

/-- Function 40 of the module is its export `jn`. -/
theorem jn_export :
    ({ name := "jn", funcIdx := 40 } : Wasm.Export) ∈ Bessel.compiled.module.exports := by
  decide +kernel

open Wasm LeanExe.Pipeline in
/-- A call of the module's `yn` entry from a ready store.  The entry takes `n` and then `x`; the
list of arguments is in reverse order. -/
theorem yn_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (n : UInt64)
    (x : Float) (h : Ready heap store) :
    Runs false env Bessel.compiled.module 41 store [.f64 x.toBits, .i64 n] fun final values =>
      values = [.f64 (Bessel.yn n x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine (Bessel.compiled.yn.implements env store heap [.i64 n, .f64 x.toBits] (n, x) h.1 trivial
    (jn_tables heap store h) rfl Separate.nil h.2.2.2.2.2.2.2).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Bessel.yn n x).toBits] := howned
  have hvs : values = [.f64 (Bessel.yn n x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ready_kept heap heap' store final h hAt' hkeep
    (memoryCap_le_of_caps hcaps h.2.2.2.2.2.2.2), hkeep⟩

/-- Function 41 of the module is its export `yn`. -/
theorem yn_export :
    ({ name := "yn", funcIdx := 41 } : Wasm.Export) ∈ Bessel.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled `j0`: the bytes decode to the module, whose function 36 is
exported as `j0`, and the initial store is ready.  A call of that entry from a ready store returns
without a trap the bits of `Bessel.j0 x` and leaves a ready store in which every region of the heap
before the call keeps its bytes.  For finite `x` the value lies within
`10 · 2^-53 · √(J₀(|x|)² + Y₀(|x|)²)` of `J₀(x)`. -/
theorem j0_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "j0", funcIdx := 36 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 36 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.j0 x).toBits ∧
            (Finite x.toBits →
              |value w - J0 (value x.toBits)| ≤
                10 / 2 ^ 53 * √(J0 |value x.toBits| ^ 2 + Y0 |value x.toBits| ^ 2)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Bessel.compiled.bytes
  refine ⟨bytes, henc, hdec, j0_export, ready_initial,
    fun env heap store x h => (j0_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Bessel.j0 x).toBits, hv, rfl, BesselJ0Theorem.j0_accuracy x, hrest⟩

/-- The accuracy theorem for the compiled `j1`: the bytes decode to the module, whose function 37 is
exported as `j1`, and the initial store is ready.  A call of that entry from a ready store returns
without a trap the bits of `Bessel.j1 x` and leaves a ready store in which every region of the heap
before the call keeps its bytes.  For finite `x` the value lies within
`12 · 2^-53 · √(J₁(|x|)² + Y₁(|x|)²)` of `J₁(x)`. -/
theorem j1_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "j1", funcIdx := 37 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 37 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.j1 x).toBits ∧
            (Finite x.toBits →
              |value w - J1 (value x.toBits)| ≤
                12 / 2 ^ 53 * √(J1 |value x.toBits| ^ 2 + Y1 |value x.toBits| ^ 2)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Bessel.compiled.bytes
  refine ⟨bytes, henc, hdec, j1_export, ready_initial,
    fun env heap store x h => (j1_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Bessel.j1 x).toBits, hv, rfl, BesselJ1Theorem.j1_accuracy x, hrest⟩

/-- The accuracy theorem for the compiled `y0`: the bytes decode to the module, whose function 38 is
exported as `y0`, and the initial store is ready.  A call of that entry from a ready store returns
without a trap the bits of `Bessel.y0 x` and leaves a ready store in which every region of the heap
before the call keeps its bytes.  For finite positive `x` the value lies within
`11 · 2^-53 · √(J₀(x)² + Y₀(x)²)` of `Y₀(x)`. -/
theorem y0_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "y0", funcIdx := 38 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 38 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.y0 x).toBits ∧
            (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → x.toBits.toNat ≠ 0 →
              |value w - Y0 (value x.toBits)| ≤
                11 / 2 ^ 53 * √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Bessel.compiled.bytes
  refine ⟨bytes, henc, hdec, y0_export, ready_initial,
    fun env heap store x h => (y0_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Bessel.y0 x).toBits, hv, rfl, BesselY0Theorem.y0_accuracy x, hrest⟩

/-- The accuracy theorem for the compiled `y1`: the bytes decode to the module, whose function 39 is
exported as `y1`, and the initial store is ready.  A call of that entry from a ready store returns
without a trap the bits of `Bessel.y1 x` and leaves a ready store in which every region of the heap
before the call keeps its bytes.  For finite positive `x` the value lies within
`12 · 2^-53 · √(J₁(x)² + Y₁(x)²)` of `Y₁(x)` from `2^-1022` on, and within one step of the
nearest-even rounding of `Y₁(x)` for the words of `x` below `0x3C90000100000000`. -/
theorem y1_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "y1", funcIdx := 39 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 39 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.y1 x).toBits ∧
            (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → x.toBits.toNat ≠ 0 →
              (0x0010000000000000 ≤ x.toBits.toNat →
                |value w - Y1 (value x.toBits)| ≤
                  12 / 2 ^ 53 * √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2)) ∧
              (x.toBits.toNat < 0x3C90000100000000 →
                F64SignedRounding.WithinSteps 1 (Y1 (value x.toBits)) w)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Bessel.compiled.bytes
  refine ⟨bytes, henc, hdec, y1_export, ready_initial,
    fun env heap store x h => (y1_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Bessel.y1 x).toBits, hv, rfl, BesselY1Theorem.y1_positive x, hrest⟩

/-- The accuracy theorem for the compiled `jn`: the bytes decode to the module, whose function 40 is
exported as `jn`, and the initial store is ready.  A call of that entry with the order `n` and the
argument `x` from a ready store returns without a trap the bits of `Bessel.jn n x` and leaves a
ready store in which every region of the heap before the call keeps its bytes.  For finite `x`
outside `2 ≤ |x| < 2^302` with `|x| < 2 |N|`, where `N` is C's `int` in the low 32 bits of `n`,
the value lies within `(23 + 12 |N|) · 2^-53 · M_|N|(|x|)` of `J_N(x)`. -/
theorem jn_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "jn", funcIdx := 40 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (n : UInt64) (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 40 store [.f64 x.toBits, .i64 n]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.jn n x).toBits ∧
            (Finite x.toBits →
              ¬ (2 ≤ |value x.toBits| ∧ |value x.toBits| < 2 ^ 302 ∧
                |value x.toBits| < 2 * ((orderZ n).natAbs : ℝ)) →
              |value w - JZ (orderZ n) (value x.toBits)| ≤
                (23 + 12 * ((orderZ n).natAbs : ℝ)) * unitRoundoff64 *
                  modn |value x.toBits| (orderZ n).natAbs) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Bessel.compiled.bytes
  refine ⟨bytes, henc, hdec, jn_export, ready_initial,
    fun env heap store n x h => (jn_entry_call env heap store n x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Bessel.jn n x).toBits, hv, rfl, BesselJnTheorem.jn_accuracy n x, hrest⟩

/-- The accuracy theorem for the compiled `yn`: the bytes decode to the module, whose function 41 is
exported as `yn`, and the initial store is ready.  A call of that entry with the order `n` and the
argument `x` from a ready store returns without a trap the bits of `Bessel.yn n x` and leaves a
ready store in which every region of the heap before the call keeps its bytes.  For finite
positive `x` outside `2 ≤ x < 2^302` with `x < 2 |N|`, the value is finite and within
`(250 + 12 |N|) · 2^-53 · M_|N|(x)` of `Y_N(x)`, or it is the infinity of the sign of `Y_N(x)` and
`|Y_N(x)| > 2^1023`, and it is that infinity from `|Y_N(x)| ≥ 2^1025` on. -/
theorem yn_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "yn", funcIdx := 41 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (n : UInt64) (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 41 store [.f64 x.toBits, .i64 n]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.yn n x).toBits ∧
            (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → x.toBits.toNat ≠ 0 →
              ¬ (2 ≤ value x.toBits ∧ value x.toBits < 2 ^ 302 ∧
                value x.toBits < 2 * ((orderZ n).natAbs : ℝ)) →
              YBound w (YZ (orderZ n) (value x.toBits))
                  ((250 + 12 * ((orderZ n).natAbs : ℝ)) * unitRoundoff64 *
                    modn (value x.toBits) (orderZ n).natAbs) ∧
                (2 ^ 1025 ≤ |YZ (orderZ n) (value x.toBits)| →
                  w = Wasm.IEEE64.infinity (decide (YZ (orderZ n) (value x.toBits) < 0)))) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Bessel.compiled.bytes
  refine ⟨bytes, henc, hdec, yn_export, ready_initial,
    fun env heap store n x h => (yn_entry_call env heap store n x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Bessel.yn n x).toBits, hv, rfl, fun hxf hpos hnz hopen =>
    ⟨BesselYnTheorem.yn_accuracy n x hxf hpos hnz hopen,
      BesselYnTheorem.yn_overflow n x hxf hpos hnz hopen⟩, hrest⟩

/-- The six byte theorems of the module. -/
theorem bessel_module_accuracy :
    (∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "j0", funcIdx := 36 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 36 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.j0 x).toBits ∧
            (Finite x.toBits →
              |value w - J0 (value x.toBits)| ≤
                10 / 2 ^ 53 * √(J0 |value x.toBits| ^ 2 + Y0 |value x.toBits| ^ 2)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "j1", funcIdx := 37 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 37 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.j1 x).toBits ∧
            (Finite x.toBits →
              |value w - J1 (value x.toBits)| ≤
                12 / 2 ^ 53 * √(J1 |value x.toBits| ^ 2 + Y1 |value x.toBits| ^ 2)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "y0", funcIdx := 38 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 38 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.y0 x).toBits ∧
            (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → x.toBits.toNat ≠ 0 →
              |value w - Y0 (value x.toBits)| ≤
                11 / 2 ^ 53 * √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "y1", funcIdx := 39 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 39 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.y1 x).toBits ∧
            (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → x.toBits.toNat ≠ 0 →
              (0x0010000000000000 ≤ x.toBits.toNat →
                |value w - Y1 (value x.toBits)| ≤
                  12 / 2 ^ 53 * √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2)) ∧
              (x.toBits.toNat < 0x3C90000100000000 →
                F64SignedRounding.WithinSteps 1 (Y1 (value x.toBits)) w)) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "jn", funcIdx := 40 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (n : UInt64) (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 40 store [.f64 x.toBits, .i64 n]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.jn n x).toBits ∧
            (Finite x.toBits →
              ¬ (2 ≤ |value x.toBits| ∧ |value x.toBits| < 2 ^ 302 ∧
                |value x.toBits| < 2 * ((orderZ n).natAbs : ℝ)) →
              |value w - JZ (orderZ n) (value x.toBits)| ≤
                (23 + 12 * ((orderZ n).natAbs : ℝ)) * unitRoundoff64 *
                  modn |value x.toBits| (orderZ n).natAbs) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) ∧
    (∃ bytes, Wasm.Encoding.encode Bessel.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Bessel.compiled.module ∧
      ({ name := "yn", funcIdx := 41 } : Wasm.Export) ∈ Bessel.compiled.module.exports ∧
      Ready (Verified.initialHeap Bessel.compiled.tables) Bessel.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (n : UInt64) (x : Float), Ready heap store →
        Wasm.Runs false env Bessel.compiled.module 41 store [.f64 x.toBits, .i64 n]
          (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Bessel.yn n x).toBits ∧
            (Finite x.toBits → x.toBits.toNat < 2 ^ 63 → x.toBits.toNat ≠ 0 →
              ¬ (2 ≤ value x.toBits ∧ value x.toBits < 2 ^ 302 ∧
                value x.toBits < 2 * ((orderZ n).natAbs : ℝ)) →
              YBound w (YZ (orderZ n) (value x.toBits))
                  ((250 + 12 * ((orderZ n).natAbs : ℝ)) * unitRoundoff64 *
                    modn (value x.toBits) (orderZ n).natAbs) ∧
                (2 ^ 1025 ≤ |YZ (orderZ n) (value x.toBits)| →
                  w = Wasm.IEEE64.infinity (decide (YZ (orderZ n) (value x.toBits) < 0)))) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r)) :=
  ⟨j0_bytes_accuracy, j1_bytes_accuracy, y0_bytes_accuracy, y1_bytes_accuracy, jn_bytes_accuracy,
    yn_bytes_accuracy⟩

#print axioms ready_initial
#print axioms j0_entry_call
#print axioms j1_entry_call
#print axioms y0_entry_call
#print axioms y1_entry_call
#print axioms j0_export
#print axioms j1_export
#print axioms y0_export
#print axioms y1_export
#print axioms j0_bytes_accuracy
#print axioms j1_bytes_accuracy
#print axioms y0_bytes_accuracy
#print axioms y1_bytes_accuracy
#print axioms jn_entry_call
#print axioms yn_entry_call
#print axioms jn_export
#print axioms yn_export
#print axioms jn_bytes_accuracy
#print axioms yn_bytes_accuracy
#print axioms bessel_module_accuracy

end Library.Numerics.Float64.Bessel.BesselBytes
