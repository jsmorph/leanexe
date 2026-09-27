import Project.LebU32.Defs
import Project.LebU32.Copy
import Project.LebU32.Frame
import Project.LebU32.IterAlloc
import Project.LebU32.IterResult

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
theorem posIterLemma (env : HostEnv Unit) (st stL : Store Unit)
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
    (hrest : v / 128 = 0)
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
    (hFT : ∀ (st' : Store Unit) (s' : Locals) (k' : Nat) (v' : UInt64)
      (written' : List UInt8) (done' : Bool) (e' : Nat → UInt64),
      lebList 10 n = written' ++
        (if done' then [] else lebList (10 - k') v') →
      written'.length = k' →
      k' ≤ (lebList 10 n).length →
      (if done' then
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } =
          lFrame (UInt64.ofNat (11 - k')) (e' 1) (e' 2) (e' 3) (e' 4)
            (bufPtr g0 k') (bufPtr g0 k') (UInt64.ofNat k') 1 e'
       else
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } =
          lFrame (UInt64.ofNat (10 - k')) v' (bufPtr g0 k') (bufPtr g0 k')
            (UInt64.ofNat k') 0 0 0 0 e') →
      (∀ i : Nat, i < k' →
        st'.mem.bytes (objBase g0 (k' - 1) + 48 + i) = written'[i]!) →
      st'.globals.globals.length = st.globals.globals.length →
      st'.globals.globals[0]? = some (.i64 (g0 + UInt64.ofNat (56 * k'))) →
      st'.globals.globals[1]? = some (.i64 0) →
      st'.globals.globals[2]? = some (.i64 (g2 + UInt64.ofNat k')) →
      st'.globals.globals[3]? = st.globals.globals[3]? →
      st'.globals.globals[4]? = st.globals.globals[4]? →
      st'.globals.globals[5]? = st.globals.globals[5]? →
      st'.mem.pages = st.mem.pages →
      (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a) →
      lMeasure st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } <
        m0 →
      POST (.Fallthrough st' s'))
    (sL : Locals)
    (hsL : sL = lFrame (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
        (UInt64.ofNat k) 0 0 0 0 e) :
    wp «module» posProg POST stL sL env := by
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
  have hb1 : (g0.toNat + 56 * k) % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by omega
  have hb2 : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by rw [hs40m]; omega
  have hb3 : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by rw [hs32m]; omega
  have hb4 : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by rw [hs24m]; omega
  have hb5 : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by rw [hs16m]; omega
  have hb6 : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by rw [hs8m]; omega
  apply wp.conseq (Q := posPOST st n g0 g2 m0 POST)
  · intro cont h
    cases cont with
    | Fallthrough st' s' =>
      simp only [posPOST] at h
      rcases h with ⟨h⟩
      exact hFT st' s' h.k h.v h.written h.done h.e h.split
        h.writtenLength h.indexBound h.frame h.bytes h.globalsLength h.global0
        h.global1 h.global2 h.global3 h.global4 h.global5 h.pages h.below
        h.measure
    | Break k st' s' => simpa only [posPOST] using h
    | Return st' values => simpa only [posPOST] using h
    | Trap st' message => simpa only [posPOST] using h
    | Invalid message => simpa only [posPOST] using h
    | OutOfFuel => simpa only [posPOST] using h
    | ReturnCall id st' values => simpa only [posPOST] using h
    | Throwing tag args st' s' => simpa only [posPOST] using h
  rw [lFrame_eq_flat]
  unfold posProg
  wp_run_folded []
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by decide)]
  try wp_run_folded []
  try simp
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
        (UInt64.ofNat k) 0 0 0 0 (v % 128 &&& 255) (bufPtr g0 k)
        (UInt64.ofNat k) (e 12) (e 13) (e 14) (e 15) (e 16) (e 17)
        (e 18) (e 19) (e 20) (e 21) (e 22) (e 23) (e 24) (bufPtr g0 k)
        (UInt64.ofNat k) (v % 128 &&& 255) (e 28) (UInt64.ofNat k + 1)
        (e 30) ((UInt64.ofNat k + 1 + 7) / 8 * 8) 0 0 (e 34) (e 35) 0)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st1 s1 ⟨rfl, rfl⟩
    wp_run_folded []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by decide)]
    try wp_run_folded []
    try simp [posPOST]
    try simp only [h0L]
    try wp_run_folded []
    try simp only [hcap8]
    try wp_run_folded []
    try simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hno_wrap])]
    try wp_run_folded []
    try simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hpgL, hgeM])]
    try wp_run_folded []
    try simp only [h0L]
    try wp_run_folded []
    simp [hTrap]
    simp only [h2L, hpgL]
    refine and6_and ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ ?_
    try simp only [h2L]
    try wp_run_folded []
    try simp [posPOST, hTrap]
    exact posIterAllocWp env st st1 n g0 g2 k v written e m0 POST
      hn32 hFit32 hFit hPages hL5 hsplit hwlen hkL hrest hm0 hTrap hkU
      hcap8 h56k h56kM hnewtopN h56kN hno_wrap hle_wrap hsub1T hp32L
      hgeM h48kN hsubHdr hs40 hs32 hs24 hs16 hs8 hs40m hs32m hs24m
      hs16m hs8m hs0m hcap hbytes hlen h0L h1L h2L h3L h4L h5L hpgL
      hloL


end Project.LebU32.Spec
