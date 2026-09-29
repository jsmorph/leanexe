import Project.ProofKit.Allocation
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.MemoryGrowth
open Wasm Project.ProofKit.Memory

def delta (current required : Nat) : UInt32 :=
  (UInt64.ofNat required - (UInt32.ofNat current).toUInt64).toUInt32

theorem delta_toNat (current required : Nat)
    (hOrder : current ≤ required) (hBound : required ≤ 65536) :
    (delta current required).toNat = required - current := by
  have hRequired : required < UInt64.size := by change required < 18446744073709551616; omega
  have hCurrent : ((UInt32.ofNat current).toUInt64).toNat = current :=
    Project.ProofKit.Allocation.memoryPages_toNat current (by omega)
  unfold delta
  rw [toUInt32_toNat, toNat_sub_of_le _ _ (by
    rw [UInt64.toNat_ofNat_of_lt' hRequired, hCurrent]
    exact hOrder), UInt64.toNat_ofNat_of_lt' hRequired, hCurrent,
    Nat.mod_eq_of_lt (by omega)]

def grown (store : Store Unit) (required : Nat) : Store Unit :=
  { store with mem := { store.mem with pages := required } }

theorem grow_exact (store : Store Unit) (required cap : Nat)
    (hOrder : store.mem.pages ≤ required) (hBound : required ≤ 65536)
    (hCap : required ≤ cap) :
    store.mem.grow (delta store.mem.pages required) cap =
      some ((grown store required).mem, store.mem.pages) := by
  have hDelta := delta_toNat store.mem.pages required hOrder hBound
  have hPages : store.mem.pages + (required - store.mem.pages) = required := by omega
  simp only [Mem.grow, hDelta, hPages, hCap, reduceIte, grown]

theorem previous_not_failure (current : Nat) (hBound : current ≤ 65536) :
    UInt32.ofNat current ≠ (4294967295 : UInt32) := by
  intro h
  have hNat := congrArg UInt32.toNat h
  have hCurrent : current < UInt32.size := by change current < 4294967296; omega
  rw [UInt32.toNat_ofNat_of_lt' hCurrent] at hNat
  change current = 4294967295 at hNat
  omega

def growProgram : Wasm.Program :=
  [.memorySize, .extendUI32, .subI64, .wrapI64, .memoryGrow,
    .const 4294967295, .eq, .iff 0 0 [.unreachable] []]

theorem growProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (required : Nat) (values : List Wasm.Value)
    (hMemory32 : module_.memIs64 = false)
    (hValues : frame.values = .i64 (UInt64.ofNat required) :: values)
    (hOrder : store.mem.pages ≤ required) (hBound : required ≤ 65536)
    (hCap : required ≤ store.memoryCap module_ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (grown store required) { frame with values := values } env) :
    wp module_ (growProgram ++ rest) Q store frame env := by
  have hGrow := grow_exact store required (store.memoryCap module_ 0) hOrder hBound hCap
  simp only [delta] at hGrow
  have hNotFailure := previous_not_failure store.mem.pages (by omega)
  unfold growProgram
  simp only [List.cons_append, List.nil_append]
  wp_run [hValues, hMemory32, sizeValue, Bool.false_eq_true, reduceIte, Nat.reducePow,
    UInt64.ofNat_uInt32ToNat, ← toUInt32_eq_ofNat, hGrow]
  refine wp_iff_cons rfl ?_
  simpa [hNotFailure, grown] using hNext

#print axioms delta_toNat
#print axioms grow_exact
#print axioms growProgram_spec

end Project.ProofKit.MemoryGrowth
