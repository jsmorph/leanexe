import Verified.LocalFrame
import Verified.TreeCopyCode
import Verified.TreeStorage

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_headerLoad {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr : Nat} {p back : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q store
      { s with values := .i64 (store.mem.read64 (p - back).toUInt32) :: s.values } host) :
    wp m (headerLoad ptr back ++ rest) Q store s host := by
  simp only [Locals.get] at hPtr
  simp only [UInt64.toUInt32_sub] at hRoom
  simpa [headerLoad, wp_simp, hPtr, wrap_toUInt32_num, hRoom, Nat.not_lt.mpr hRoom] using hNext

theorem wp_headerStoreWord {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr : Nat} {p back value : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wp m (headerStore ptr back [.constI64 value] ++ rest) Q store s host := by
  simp only [Locals.get] at hPtr
  simp only [UInt64.toUInt32_sub] at hRoom
  simpa [headerStore, wp_simp, hPtr, wrap_toUInt32_num, hRoom, Nat.not_lt.mpr hRoom] using hNext

theorem wp_headerStoreLocal {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr src : Nat} {p back value : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hValue : s.get src = some (.i64 value))
    (hRoom : (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q
      { store with mem := store.mem.write64 (p - back).toUInt32 value } s host) :
    wp m (headerStore ptr back [.localGet src] ++ rest) Q store s host := by
  simp only [Locals.get] at hPtr hValue
  simp only [UInt64.toUInt32_sub] at hRoom
  simpa [headerStore, wp_simp, hPtr, hValue, wrap_toUInt32_num, hRoom,
    Nat.not_lt.mpr hRoom] using hNext

#print axioms wp_headerLoad
#print axioms wp_headerStoreWord
#print axioms wp_headerStoreLocal

end Verified
