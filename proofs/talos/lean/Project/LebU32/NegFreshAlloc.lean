import Project.LebU32.Frame

/-!
# Continuation-byte fresh allocation

This module isolates the fresh-allocation branch shared by the LEB128
continuation path.  It separates the allocation arithmetic from the six
header stores.  Both program fragments come from the decoded artifact program.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

def negFreshAllocationBody : Program :=
  match negProg.drop 58 with
  | .iff _ _ body _ :: _ => body
  | _ => []

def negFreshHeaderWrites : Program := negFreshAllocationBody.drop 29

def negFreshAllocationPrelude : Program := negFreshAllocationBody

def negFreshHeaderStartStore (st : Store Unit) (g0 : UInt64) (k : Nat) :
    Store Unit :=
  { st with globals := { globals := (st.globals.globals.set 0
      (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8))) } }

def negFreshResultStore (st : Store Unit) (g0 : UInt64) (k : Nat) :
    Store Unit :=
  { negFreshHeaderStartStore st g0 k with
    mem := (((((st.mem.write64
      (UInt32.ofNat ((g0.toNat + 56 * k) % 4294967296))
      5501223100278326855).write64
      (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 40).toNat %
        4294967296)) 1).write64
      (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 32).toNat %
        4294967296)) 8).write64
      (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 24).toNat %
        4294967296)) 0).write64
      (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 16).toNat %
        4294967296)) 0).write64
      (UInt32.ofNat ((g0 + 56 * UInt64.ofNat k + 48 - 8).toNat %
        4294967296)) 0 }

def negFreshEntryFrame (g0 v : UInt64) (k : Nat) (e : Nat → UInt64) :
    Locals :=
  lFrameFlat (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
    (UInt64.ofNat k) 0 0 0 0 (e 9) (e 10) (e 11) (e 12) (v / 128)
    (v % 128 + 128 &&& 255) (bufPtr g0 k) (UInt64.ofNat k) (e 17)
    (e 18) (e 19) (e 20) (e 21) (e 22) (e 23) (e 24) (bufPtr g0 k)
    (UInt64.ofNat k) (v % 128 + 128 &&& 255) (e 28)
    (UInt64.ofNat k + 1) (e 30) ((UInt64.ofNat k + 1 + 7) / 8 * 8)
    0 0 (e 34) (e 35) 0

def negFreshResultFrame (g0 v : UInt64) (k : Nat) (e : Nat → UInt64) :
    Locals :=
  lFrameFlat (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
    (UInt64.ofNat k) 0 0 0 0 (e 9) (e 10) (e 11) (e 12) (v / 128)
    (v % 128 + 128 &&& 255) (bufPtr g0 k) (UInt64.ofNat k) (e 17)
    (e 18) (e 19) (e 20) (e 21) (e 22) (e 23) (e 24) (bufPtr g0 k)
    (UInt64.ofNat k) (v % 128 + 128 &&& 255) (e 28)
    (UInt64.ofNat k + 1) (e 30) 8 0 0
    (g0 + 56 * UInt64.ofNat k + 48 + 8)
    ((g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1)
    (g0 + 56 * UInt64.ofNat k + 48)

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem negFreshHeaderWritesWp (env : HostEnv Unit) (st st0 : Store Unit)
    (g0 v : UInt64) (k : Nat) (e : Nat → UInt64)
    (Q : Assertion Unit)
    (hk5 : k < 5)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hpg0 : st0.mem.pages = st.mem.pages)
    (hs40 : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat =
      g0.toNat + 56 * k + 8)
    (hs32 : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat =
      g0.toNat + 56 * k + 16)
    (hs24 : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat =
      g0.toNat + 56 * k + 24)
    (hs16 : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat =
      g0.toNat + 56 * k + 32)
    (hs8 : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat =
      g0.toNat + 56 * k + 40)
    (hs0m : (g0.toNat + 56 * k) % 4294967296 = g0.toNat + 56 * k)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      Q (.Trap st' msg) = False)
    (hDone : Q (.Fallthrough (negFreshResultStore st0 g0 k)
      (negFreshResultFrame g0 v k e))) :
    wp «module» negFreshHeaderWrites Q (negFreshHeaderStartStore st0 g0 k)
      (negFreshResultFrame g0 v k e) env := by
  simp only [negFreshHeaderWrites, negFreshAllocationBody, negProg,
    List.drop, negFreshHeaderStartStore, negFreshResultFrame]
  wp_run_folded []
  try simp [hTrap]
  refine ⟨by rw [hs0m]; omega, by rw [hs40]; omega, by rw [hs32]; omega,
    by rw [hs24]; omega, by rw [hs16]; omega,
    by rw [hs8]; omega, ?_⟩
  simpa only [negFreshResultStore, negFreshHeaderStartStore,
    negFreshResultFrame, lFrameFlat] using hDone

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem negFreshAllocationPreludeWp (env : HostEnv Unit)
    (st st0 : Store Unit) (g0 v : UInt64) (k : Nat) (e : Nat → UInt64)
    (Q : Assertion Unit)
    (hk5 : k < 5)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (h0 : st0.globals.globals[0]? =
      some (.i64 (g0 + UInt64.ofNat (56 * k))))
    (hpg0 : st0.mem.pages = st.mem.pages)
    (hcap8 : (UInt64.ofNat k + 1 + 7) / 8 * 8 = 8)
    (hno_wrap : ¬ (g0 + 56 * UInt64.ofNat k + 48 + 8 <
      g0 + 56 * UInt64.ofNat k))
    (hgeM : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1 ≤
      (UInt32.ofNat st.mem.pages).toUInt64)
    (hs40 : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat =
      g0.toNat + 56 * k + 8)
    (hs32 : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat =
      g0.toNat + 56 * k + 16)
    (hs24 : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat =
      g0.toNat + 56 * k + 24)
    (hs16 : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat =
      g0.toNat + 56 * k + 32)
    (hs8 : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat =
      g0.toNat + 56 * k + 40)
    (hs0m : (g0.toNat + 56 * k) % 4294967296 = g0.toNat + 56 * k)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      Q (.Trap st' msg) = False)
    (hDone : Q (.Fallthrough (negFreshResultStore st0 g0 k)
      (negFreshResultFrame g0 v k e))) :
    wp «module» negFreshAllocationPrelude Q st0
      (negFreshEntryFrame g0 v k e) env := by
  rw [show negFreshAllocationPrelude =
      negFreshAllocationBody.take 29 ++ negFreshHeaderWrites from by
    simp only [negFreshAllocationPrelude, negFreshHeaderWrites,
      List.take_append_drop]]
  simp only [negFreshAllocationBody, negProg, List.drop, List.take,
    negFreshEntryFrame]
  wp_run_folded []
  try simp
  try simp only [h0]
  try wp_run_folded []
  try simp only [hcap8]
  try wp_run_folded []
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hno_wrap])]
  wp_run_folded []
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hpg0, hgeM])]
  wp_run_folded []
  try simp only [h0]
  try simp
  exact negFreshHeaderWritesWp env st st0 g0 v k e Q hk5 hFit32 hFit
    hpg0 hs40 hs32 hs24 hs16 hs8 hs0m hTrap hDone

end Project.LebU32.Spec
