import Verified.Bytes.LiteralCode
import Verified.Bytes.LiteralFrame
import Verified.Bytes.CopyOwned

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.Pipeline.Bytes LeanExe.ProofKit LeanExe.Runtime

theorem wp_literal {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {pool : LiteralPool} {bytes : Literal} {offset base : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hPool : pool.Static heap store)
    (hOffset : literalOffset pool.values bytes = some offset) (hNonempty : bytes ≠ [])
    (hBase : s.params.length ≤ base) (hRoom : base + 4 ≤ s.positions)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocationCost bytes.length))) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (root : UInt64),
      Step heap store (fun _ => True) heap' store' (regions store' root) →
      Rep heap' store' root (UInt64.ofNat bytes.length) bytes.value →
      Frame base s s' → heap'.top.toNat ≤ heap.top.toNat + allocationCost bytes.length →
      wp m rest Q store'
        { s' with values := .i64 (UInt64.ofNat bytes.length) :: .i64 root :: s.values } host) :
    wp m (literalCode (UInt64.ofNat (pool.base + offset)) bytes base ++ rest) Q
      store s host := by
  obtain ⟨hSource, hRegion⟩ := hPool.literal hOffset hNonempty
  have hLength : (UInt64.ofNat bytes.length).toNat = bytes.value.data.size := by
    have hSize : bytes.value.data.size = bytes.length := by
      simp [Literal.value, ByteArray.size]
    have hBound := hSource.memory
    have hPages := hHeap.pages
    rw [hSize]
    exact UInt64.toNat_ofNat_of_lt' (by change bytes.length < 2 ^ 64; omega)
  simp only [literalCode, List.append_assoc, List.cons_append, List.nil_append,
    wp_constI64_cons]
  refine wp_localSet_local (s := s) (vs := s.values) hBase
    (Locals.lt_total (by omega)) ?_
  let s1 := setLocal { s with values := s.values } base
    (.i64 (UInt64.ofNat (pool.base + offset)))
  have hFrame1 : Frame base s s1 := Frame.setValues hBase le_rfl (by omega)
  have hSource1 : s1.get base = some (.i64 (UInt64.ofNat (pool.base + offset))) :=
    Locals.get_setLocal_same hBase (Locals.lt_total (by omega))
  have hLow : s1.params.length ≤ base + 1 := by rw [hFrame1.params]; omega
  have hHigh : base + 1 < s1.positions := by rw [hFrame1.positions]; omega
  simp only [wp_constI64_cons]
  refine wp_localSet_local (s := s1) (vs := s.values) hLow (Locals.lt_total hHigh) ?_
  let s2 := setLocal { s1 with values := s.values } (base + 1)
    (.i64 (UInt64.ofNat bytes.length))
  have hFrame2 : Frame base s1 s2 := Frame.setValues hLow (by omega) hHigh
  have hSource2 : s2.get base = some (.i64 (UInt64.ofNat (pool.base + offset))) := by
    rw [Locals.get_setLocal_ne (s := { s1 with values := s.values }) hLow
      (by omega : base ≠ base + 1), Locals.get_values]
    exact hSource1
  have hLength2 : s2.get (base + 1) = some (.i64 (UInt64.ofNat bytes.length)) :=
    Locals.get_setLocal_same hLow (Locals.lt_total hHigh)
  show wp m _ Q store s2 host
  refine wp_copyOwned hm hHeap hSource hRegion hLength hSource2 hLength2
    (by omega) (by omega) (by rw [hFrame2.params, hFrame1.params]; omega)
    (by rw [hFrame2.positions, hFrame1.positions]; omega) hCap
    (by simpa only [Literal.value, ByteArray.size, List.size_toArray] using hTrap)
    fun heap' store' s' root hStep hRep hFrame hTop _ => ?_
  have hNext' := hNext heap' store' s' root hStep hRep
    (hFrame1.trans (hFrame2.trans (hFrame.mono (by omega))))
    (by simpa only [Literal.value, ByteArray.size, List.size_toArray] using hTop)
  simpa only [s2, s1, setLocal] using hNext'

end Verified.Bytes
