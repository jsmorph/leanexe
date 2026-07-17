import Project.ClobMarket.InvalidResult

/-!
# Invalid exported `market` branch

The invalid branch returns status one and the borrowed input book.  It
allocates one owned empty trade array and states the exact allocator, page,
and memory-frame effects.  The proof composes the four allocation phases.
-/

namespace Project.ClobMarket.Invalid

open Wasm Project.Common Project.Clob Project.ClobMarket
  Project.ClobMatchFuel.AllocatorFrame Project.ClobPostOnly.Model

def InvalidSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit)
    (book bookCapacity g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL),
    os.length < 4294967296 →
    48 ≤ book.toNat →
    book.toNat + fixedArrayBytes os.length 5 < 4294967296 →
    fixedArrayBytes os.length 5 ≤ bookCapacity.toNat →
    book.toNat + bookCapacity.toNat ≤ g0.toNat →
    OwnedOrderArrayAt st book bookCapacity os →
    g0.toNat + 56 < 4294967296 →
    g0.toNat + 56 ≤ st.mem.pages * 65536 →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 0) →
    st.globals.globals[2]? = some (.i64 g2) →
    ¬validOrderL os order →
    TerminatesWith (m := Project.ClobMarket.«module») (id := 21)
      (initial := st) (env := env) (Entry.marketArgs book order)
      (fun final values =>
        InvalidPost.Postcondition st final book bookCapacity g0 g2 os values)

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

set_option Elab.async false in
theorem func21_invalid : InvalidSpec := by
  intro env st book bookCapacity g0 g2 os order hLength hBook48 hBook32
    hBookCapacity hBookBelow hBook hFit32 hFit hPages hg0 hg1 hg2 hInvalid
  apply TerminatesWith.of_wp_entry_for (f := func21Def)
  · simp [Project.ClobMarket.«module»]
  · change wp Project.ClobMarket.«module» func21 _ st
      (Entry.entryFrame book order) env
    rw [Entry.func21_decomposition]
    apply InvalidEntry.entryProg_invalid_spec env st book os order hLength
      hBook.2 hInvalid
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    apply InvalidProgram.invalidProg_spec env st book g0 g2 order hFit32
      hFit hPages hg0 hg1 hg2
    apply InvalidResult.resultProg_spec env
      (Project.ClobLimit.RunMatchEmptyAlloc.allocStore st g0 g2)
      book order g0
    simp only [wp_simp]
    exact InvalidPost.allocStore_postcondition st book bookCapacity g0 g2 os
      hBook48 hBook32 hBookCapacity hBookBelow hBook hFit32 hFit

end Project.ClobMarket.Invalid
