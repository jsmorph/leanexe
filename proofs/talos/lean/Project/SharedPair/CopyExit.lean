import Project.SharedPair.CopyTail

/-!
# Shared-pair construction after the byte-copy loop

The theorem starts after the copy loop has exited.  It proves the bang store,
the pair allocation and writes, and the inline retain sequence.
-/

namespace Project.SharedPair.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

theorem copyExit_correct
    (env : HostEnv Unit) (st1 st2 : Store Unit)
    (ptr g0 g2 g3 : UInt64) (bytes : List UInt8)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hg0_32 : g0.toNat < 4294967296)
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hg1 : st1.globals.globals[1]? = some (.i64 0))
    (hg2 : st1.globals.globals[2]? = some (.i64 g2))
    (hg3 : st1.globals.globals[3]? = some (.i64 g3))
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16)
    (hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24)
    (hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32)
    (hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40)
    (hpg : st2.mem.pages = st1.mem.pages)
    (hgl : st2.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
        (.i64 (g2 + 1)))
    (hlo : ∀ a < g0.toNat, st2.mem.bytes a = st1.mem.bytes a)
    (hpref : ∀ i < bytes.length,
      st2.mem.bytes (g0.toNat + 48 + i) = bytes[i]!)
    (hh0 : st2.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8 : st2.mem.read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh16 : st2.mem.read64
      (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
      allocSizeU (UInt64.ofNat bytes.length))
    (hh24 : st2.mem.read64
      (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0) :
    wp «module» copyExitProg (copyPost st1 ptr g0 g2 g3 bytes) st2
      (vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length)
        (allocSizeU (UInt64.ofNat bytes.length)) 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1)
        (g0 + 48)) env := by
  unfold copyExitProg copySuffix
  simp only [Project.SharedPair.func0, List.drop]
  have hTrap : ∀ (st' : Store Unit) (msg : String),
      copyPost st1 ptr g0 g2 g3 bytes (.Trap st' msg) = False := by
    intro st' msg
    rfl
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  refine ⟨by omega, ?_⟩
  refine wp_iff_cons rfl ?_
  rw [if_neg (by decide)]
  have hglen : 3 < st1.globals.globals.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hg3
    exact h
  have hg0len : 0 < st1.globals.globals.length := by omega
  have hg1len : 1 < st1.globals.globals.length := by omega
  have hg2len : 2 < st1.globals.globals.length := by omega
  have hgnil : ¬ st1.globals.globals = [] := by
    intro h
    rw [h] at hglen
    simp at hglen
  have hg1S : st2.globals.globals[1]? = some (.i64 0) := by
    rw [hgl]
    rw [List.getElem?_set, List.getElem?_set]
    simp only [if_neg (by omega : ¬ (2 = 1)), if_neg (by omega : ¬ (0 = 1))]
    exact hg1
  wp_run
  try simp only [hg1S]
  try wp_run
  try simp
  have h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hszU]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun stX sX =>
      stX = { st2 with mem := (st2.mem.write8
        (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
        33) } ∧
      sX = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
        (UInt64.ofNat bytes.length + 1) 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56
        0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) /
          65536 + 1)
        0)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, by simp [vFrame]⟩
  · intro stX sX hInv
    rcases hInv with ⟨rfl, rfl⟩
    rw [Wasm.wp_localGet_cons, vFrame_get_19]
    simp only
    rw [Wasm.wp_constI64_cons, Wasm.wp_eqI64_cons]
    simp only [if_pos rfl]
    rw [Wasm.wp_br_if_cons]
    simp only [Project.Common.Locals.values_values, List.take, List.drop,
      List.nil_append]
    exact copyBuildTail_correct env st1 st2 ptr g0 g2 g3 bytes hLen
      hPtr32 hBelow hFit32 hg0_32 hszN_ge hszN_ge8 hlenU hszU hFit
      hPages hg1 hg2 hg3 h17 hsub40 hpg hgl hlo hpref hh0 hh8 hglen
      hg0len hg2len hg1S

end Project.SharedPair.Spec
