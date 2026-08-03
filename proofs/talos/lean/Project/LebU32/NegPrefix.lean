import Project.LebU32.Frame
import Project.LebU32.NegAfterFree

/-!
# Continuation-byte instruction prefix

This module executes the continuation-byte program through allocation and
delegates its copy loop to `negIterAllocWp`.  Its inputs include the arithmetic
facts proved by `negIterLemma`.  The separation prevents those proof terms from
sharing an elaboration process with the generated instruction prefix.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem negPrefixWp (env : HostEnv Unit) (st stL : Store Unit)
    (n g0 g2 : UInt64) (k : Nat) (v : UInt64) (written : List UInt8)
    (e : Nat → UInt64) (m0 : Nat) (POST : Assertion Unit)
    (hn32 : n.toNat < 4294967296)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hL5 : (lebList 10 n).length ≤ 5)
    (hsplit : lebList 10 n = written ++ lebList (10 - k) v)
    (hwlen : written.length = k)
    (hkL : k < (lebList 10 n).length)
    (hcont : ¬ v / 128 = 0)
    (hbytes : ∀ i : Nat, i < k →
      stL.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!)
    (hlen : stL.globals.globals.length = st.globals.globals.length)
    (h0L : stL.globals.globals[0]? =
      some (.i64 (g0 + UInt64.ofNat (56 * k))))
    (h1L : stL.globals.globals[1]? = some (.i64 0))
    (h2L : stL.globals.globals[2]? = some (.i64 (g2 + UInt64.ofNat k)))
    (h3L : stL.globals.globals[3]? = st.globals.globals[3]?)
    (h4L : stL.globals.globals[4]? = st.globals.globals[4]?)
    (h5L : stL.globals.globals[5]? = st.globals.globals[5]?)
    (hpgL : stL.mem.pages = st.mem.pages)
    (hloL : ∀ a : Nat, a < g0.toNat → stL.mem.bytes a = st.mem.bytes a)
    (hm0 : 2 * (10 - k) + 1 ≤ m0)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hFT : ∀ (st' : Store Unit) (s' : Locals),
      lInv st n g0 g2 st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } ∧
      lMeasure st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } <
        m0 →
      POST (.Fallthrough st' s'))
    (hkU : (UInt64.ofNat k).toNat = k)
    (hcap8 : (UInt64.ofNat k + 1 + 7) / 8 * 8 = 8)
    (h56k : (g0 + UInt64.ofNat (56 * k)).toNat = g0.toNat + 56 * k)
    (h56kM : (56 * UInt64.ofNat k).toNat = 56 * k)
    (hnewtopN : (g0 + 56 * UInt64.ofNat k + 48 + 8).toNat =
      g0.toNat + 56 * k + 56)
    (h56kN : (g0 + 56 * UInt64.ofNat k).toNat = g0.toNat + 56 * k)
    (hno_wrap : ¬ (g0 + 56 * UInt64.ofNat k + 48 + 8 <
      g0 + 56 * UInt64.ofNat k))
    (hle_wrap : g0 + 56 * UInt64.ofNat k ≤
      g0 + 56 * UInt64.ofNat k + 48 + 8)
    (hsub1T : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1).toNat =
      g0.toNat + 56 * k + 55)
    (hp32L : ((UInt32.ofNat st.mem.pages).toUInt64).toNat = st.mem.pages)
    (hgeM : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1 ≤
      (UInt32.ofNat st.mem.pages).toUInt64)
    (h48kN : (g0 + 56 * UInt64.ofNat k + 48).toNat =
      g0.toNat + 56 * k + 48)
    (hsubHdr : ∀ c : UInt64, c.toNat ≤ 48 →
      (g0 + 56 * UInt64.ofNat k + 48 - c).toNat =
        g0.toNat + 56 * k + 48 - c.toNat)
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
    (hs40m : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat % 4294967296 =
      g0.toNat + 56 * k + 8)
    (hs32m : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat % 4294967296 =
      g0.toNat + 56 * k + 16)
    (hs24m : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat % 4294967296 =
      g0.toNat + 56 * k + 24)
    (hs16m : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat % 4294967296 =
      g0.toNat + 56 * k + 32)
    (hs8m : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat % 4294967296 =
      g0.toNat + 56 * k + 40)
    (hs0m : (g0.toNat + 56 * k) % 4294967296 = g0.toNat + 56 * k)
    (hcap : ¬ (UInt64.ofNat k + 1 + 7) / 8 * 8 < 8)
    (sL : Locals)
    (hsL : sL = lFrame (UInt64.ofNat (10 - k)) v (bufPtr g0 k)
      (bufPtr g0 k) (UInt64.ofNat k) 0 0 0 0 e) :
    wp «module» negProg POST stL sL env := by
  subst hsL
  rw [lFrame_eq_flat]
  unfold negProg
  wp_run_folded []
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by decide)]
  try wp_run_folded []
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by decide)]
  try wp_run_folded []
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hcap])]
  try wp_run_folded []
  try simp only [h1L]
  try wp_run_folded []
  try simp
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st1 s1 => st1 = stL ∧ s1 =
      lFrameFlat (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
        (UInt64.ofNat k) 0 0 0 0 (e 9) (e 10) (e 11) (e 12) (v / 128)
        (v % 128 + 128 &&& 255) (bufPtr g0 k) (UInt64.ofNat k) (e 17)
        (e 18) (e 19) (e 20) (e 21) (e 22) (e 23) (e 24) (bufPtr g0 k)
        (UInt64.ofNat k) (v % 128 + 128 &&& 255) (e 28)
        (UInt64.ofNat k + 1) (e 30) ((UInt64.ofNat k + 1 + 7) / 8 * 8)
        0 0 (e 34) (e 35) 0)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st1 s1 ⟨rfl, rfl⟩
    wp_run_folded []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    have hk5 : k < 5 := by omega
    have h2R : (st1.globals.globals.set 0
        (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8)))[2]? =
        some (.i64 (g2 + UInt64.ofNat k)) := by
      rw [List.getElem?_set]
      simp only [if_neg (by omega : ¬ (0 = 2))]
      exact h2L
    apply negFreshAllocationPreludeWp env st st1 g0 v k e
      _ hk5 hFit32 hFit h0L hpgL hcap8 hno_wrap hgeM hs40 hs32 hs24
      hs16 hs8 hs0m
    · intro st' msg
      simpa using hTrap st' msg
    · simp only [negFreshResultStore, negFreshHeaderStartStore,
        negFreshResultFrame, lFrameFlat_values, List.take_zero,
        List.drop_zero, List.nil_append]
      wp_run_folded [h2R]
      exact negIterAllocWp env st _ n g0 g2 k v written e m0 POST
        hn32 hFit32 hFit hPages hL5 hsplit hwlen hkL hcont hm0 hTrap hFT
        hkU hcap8 h56k h56kM hnewtopN h56kN hno_wrap hle_wrap hsub1T
        hp32L hgeM h48kN hsubHdr hs40 hs32 hs24 hs16 hs8 hs40m hs32m
        hs24m hs16m hs8m hs0m hcap hbytes hlen h0L h1L h2L h3L h4L
        h5L hpgL hloL

end Project.LebU32.Spec
