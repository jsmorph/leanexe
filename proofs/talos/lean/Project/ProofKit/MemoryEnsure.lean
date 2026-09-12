import Project.ProofKit.MemoryGrowth
import Project.ProofKit.Frame

namespace Project.ProofKit.MemoryGrowth
open Wasm

def ensured (store : Store Unit) (required : Nat) : Store Unit :=
  if store.mem.pages < required then grown store required else store

theorem ensured_pages (store : Store Unit) (required : Nat) :
    (ensured store required).mem.pages = max store.mem.pages required := by
  unfold ensured
  split <;> rename_i h
  · exact (Nat.max_eq_right (Nat.le_of_lt h)).symm
  · exact (Nat.max_eq_left (Nat.le_of_not_lt h)).symm

theorem ensured_bytes (store : Store Unit) (required : Nat) :
    (ensured store required).mem.bytes = store.mem.bytes := by
  unfold ensured
  split <;> rfl

def ensureProgram (pageLocal : Nat) : Wasm.Program :=
  [.memorySize, .extendUI32, .localGet pageLocal, .ltUI64,
    .iff 0 0 (.localGet pageLocal :: growProgram) []]

theorem ensureProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pageLocal required : Nat)
    (hMemory32 : module_.memIs64 = false) (hValues : frame.values = [])
    (hLocal : frame.get pageLocal = some (.i64 (UInt64.ofNat required)))
    (hCurrent : store.mem.pages ≤ 65536) (hBound : required ≤ 65536)
    (hCap : required ≤ store.memoryCap module_ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (ensured store required) frame env) :
    wp module_ (ensureProgram pageLocal ++ rest) Q store frame env := by
  have hEmpty : ({ frame with values := [] } : Locals) = frame :=
    Frame.ext _ _ rfl rfl hValues.symm
  have hLocal' := hLocal
  simp only [Locals.get] at hLocal'
  have hCurrentNat := Project.ProofKit.Allocation.memoryPages_toNat store.mem.pages hCurrent
  have hRequired64 : required < UInt64.size := by
    change required < 18446744073709551616
    omega
  have hCompare : ((UInt32.ofNat store.mem.pages).toUInt64 < UInt64.ofNat required) =
      (store.mem.pages < required) := by
    apply propext
    rw [UInt64.lt_iff_toNat_lt, hCurrentNat, UInt64.toNat_ofNat_of_lt' hRequired64]
  unfold ensureProgram
  simp only [List.cons_append, List.nil_append, wp_memorySize_cons, sizeValue,
    hMemory32, Bool.false_eq_true, reduceIte, wp_extendUI32_cons,
    UInt64.ofNat_uInt32ToNat, wp_localGet_cons, Frame.withValues_get,
    hLocal, hValues, wp_ltUI64_cons]
  refine wp_iff_cons rfl ?_
  by_cases hLess : store.mem.pages < required
  · simp [hCompare, hLess, hLocal']
    apply growProgram_spec module_ env store _ required [] hMemory32 rfl
      (Nat.le_of_lt hLess) hBound hCap _ []
    simpa [ensured, hLess, hValues, hEmpty] using hNext
  · simpa [hCompare, hLess, ensured, hValues, hEmpty] using hNext

#print axioms ensured_pages
#print axioms ensured_bytes
#print axioms ensureProgram_spec

end Project.ProofKit.MemoryGrowth
