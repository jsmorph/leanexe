import Project.LebU32.Defs
import Project.LebU32.Copy
import Project.LebU32.Frame
import Project.LebU32.NegPrefix

/-!
# The final-byte iteration of the compiled fuel loop

Split from the main proof so each file elaborates in its own process;
the loop rule's postcondition stays generic and is only reached through
the repeat and trap hypotheses.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime
set_option maxHeartbeats 4000000 in
set_option Elab.async false in
/-- One final-byte iteration of the compiled fuel loop: pushes the last
byte, sets the done flag, and re-establishes the loop invariant.  Generic
over the loop rule's postcondition, which it only ever reaches through
the repeat case. -/
theorem negIterLemma (env : HostEnv Unit) (st stL : Store Unit)
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
    (sL : Locals)
    (hsL : sL = lFrame (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
        (UInt64.ofNat k) 0 0 0 0 e) :
    wp «module» negProg POST stL sL env := by
  subst hsL
  have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
  have hcap8 : (UInt64.ofNat k + 1 + 7) / 8 * 8 = (8 : UInt64) := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add,
      UInt64.toNat_add, hkU]
    rw [show (1 : UInt64).toNat = 1 from rfl,
      show (7 : UInt64).toNat = 7 from rfl,
      show (8 : UInt64).toNat = 8 from rfl]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have h56k : (g0 + UInt64.ofNat (56 * k)).toNat =
      g0.toNat + 56 * k := by
    rw [UInt64.toNat_add,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    rw [Nat.mod_eq_of_lt (by omega)]
  have h56kM : (56 * UInt64.ofNat k).toNat = 56 * k := by
    rw [UInt64.toNat_mul, hkU,
      show (56 : UInt64).toNat = 56 from rfl]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    rw [Nat.mod_eq_of_lt (by omega)]
  have hnewtopN : (g0 + 56 * UInt64.ofNat k + 48 + 8).toNat =
      g0.toNat + 56 * k + 56 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, h56kM]
    rw [show (48 : UInt64).toNat = 48 from rfl,
      show (8 : UInt64).toNat = 8 from rfl]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h56kN : (g0 + 56 * UInt64.ofNat k).toNat =
      g0.toNat + 56 * k := by
    rw [UInt64.toNat_add, h56kM]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    rw [Nat.mod_eq_of_lt (by omega)]
  have hno_wrap : ¬ (g0 + 56 * UInt64.ofNat k + 48 + 8 <
      g0 + 56 * UInt64.ofNat k) := by
    rw [UInt64.lt_iff_toNat_lt, hnewtopN, h56kN]
    omega
  have hle_wrap : g0 + 56 * UInt64.ofNat k ≤
      g0 + 56 * UInt64.ofNat k + 48 + 8 := by
    rw [UInt64.le_iff_toNat_le, hnewtopN, h56kN]
    omega
  have hsub1T : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1).toNat =
      g0.toNat + 56 * k + 55 := by
    rw [toNat_sub_le _ _ (by
      rw [hnewtopN, show (1 : UInt64).toNat = 1 from rfl]; omega)]
    rw [hnewtopN, show (1 : UInt64).toNat = 1 from rfl]
    omega
  have hp32L : ((UInt32.ofNat st.mem.pages).toUInt64).toNat =
      st.mem.pages := by
    have hlt : st.mem.pages < UInt32.size := by
      have hs : UInt32.size = 4294967296 := rfl
      omega
    have h1 : (UInt32.ofNat st.mem.pages).toNat = st.mem.pages :=
      UInt32.toNat_ofNat_of_lt' hlt
    simp [h1]
  have hgeM : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1 ≤
      (UInt32.ofNat st.mem.pages).toUInt64 := by
    rw [UInt64.le_iff_toNat_le, hp32L, toNat_add_one]
    · rw [UInt64.toNat_div, hsub1T,
        show (65536 : UInt64).toNat = 65536 from rfl]
      omega
    · rw [UInt64.toNat_div, hsub1T,
        show (65536 : UInt64).toNat = 65536 from rfl]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
  have h48kN : (g0 + 56 * UInt64.ofNat k + 48).toNat =
      g0.toNat + 56 * k + 48 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, h56kM]
    rw [show (48 : UInt64).toNat = 48 from rfl]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hsubHdr : ∀ c : UInt64, c.toNat ≤ 48 →
      (g0 + 56 * UInt64.ofNat k + 48 - c).toNat =
      g0.toNat + 56 * k + 48 - c.toNat := by
    intro c hc
    rw [toNat_sub_le _ _ (by rw [h48kN]; omega), h48kN]
  have hs40 : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat =
      g0.toNat + 56 * k + 8 := by
    rw [hsubHdr 40 (by decide),
      show (40 : UInt64).toNat = 40 from rfl]
    omega
  have hs32 : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat =
      g0.toNat + 56 * k + 16 := by
    rw [hsubHdr 32 (by decide),
      show (32 : UInt64).toNat = 32 from rfl]
    omega
  have hs24 : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat =
      g0.toNat + 56 * k + 24 := by
    rw [hsubHdr 24 (by decide),
      show (24 : UInt64).toNat = 24 from rfl]
    omega
  have hs16 : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat =
      g0.toNat + 56 * k + 32 := by
    rw [hsubHdr 16 (by decide),
      show (16 : UInt64).toNat = 16 from rfl]
    omega
  have hs8 : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat =
      g0.toNat + 56 * k + 40 := by
    rw [hsubHdr 8 (by decide),
      show (8 : UInt64).toNat = 8 from rfl]
    omega
  have hs40m : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat %
      4294967296 = g0.toNat + 56 * k + 8 := by
    rw [hs40]
    exact Nat.mod_eq_of_lt (by omega)
  have hs32m : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat %
      4294967296 = g0.toNat + 56 * k + 16 := by
    rw [hs32]
    exact Nat.mod_eq_of_lt (by omega)
  have hs24m : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat %
      4294967296 = g0.toNat + 56 * k + 24 := by
    rw [hs24]
    exact Nat.mod_eq_of_lt (by omega)
  have hs16m : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat %
      4294967296 = g0.toNat + 56 * k + 32 := by
    rw [hs16]
    exact Nat.mod_eq_of_lt (by omega)
  have hs8m : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat %
      4294967296 = g0.toNat + 56 * k + 40 := by
    rw [hs8]
    exact Nat.mod_eq_of_lt (by omega)
  have hs0m : (g0.toNat + 56 * k) % 4294967296 =
      g0.toNat + 56 * k :=
    Nat.mod_eq_of_lt (by omega)
  have hcap : ¬ ((UInt64.ofNat k + 1 + 7) / 8 * 8 < (8 : UInt64)) := by
    have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mul, UInt64.toNat_div,
      UInt64.toNat_add, UInt64.toNat_add, hkU]
    rw [show (1 : UInt64).toNat = 1 from rfl,
      show (7 : UInt64).toNat = 7 from rfl,
      show (8 : UInt64).toNat = 8 from rfl]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  exact negPrefixWp env st stL n g0 g2 k v written e m0 POST
    hn32 hFit32 hFit hPages hL5 hsplit hwlen hkL hcont hbytes hlen h0L
    h1L h2L h3L h4L h5L hpgL hloL hm0 hTrap hFT hkU hcap8 h56k
    h56kM hnewtopN h56kN hno_wrap hle_wrap hsub1T hp32L hgeM h48kN
    hsubHdr hs40 hs32 hs24 hs16 hs8 hs40m hs32m hs24m hs16m hs8m
    hs0m hcap _ rfl


end Project.LebU32.Spec
