import Project.LebU32.Copy
import Project.LebU32.CopyExit
import Project.LebU32.Frame
import Project.LebU32.IterDone
import Project.LebU32.IterResult

/-!
# The allocation continuation of the final-byte iteration

Split from `posIterLemma` at the state after the five header writes.  In
the parent proof the goal at this point is internally large, and context
extension or constructor splitting there stalls the elaborator.  This
lemma restates that goal from scratch, so the bound conjuncts and the
copy-loop phase elaborate against a term of ordinary size.
-/

set_option maxRecDepth 1048576

namespace Project.LebU32.Spec

open Wasm Project.Common Project.Runtime

def posBlockPOST (env : HostEnv Unit) (st : Store Unit)
    (n g0 g2 : UInt64) (m0 : Nat) (POST : Assertion Unit) : Assertion Unit :=
  fun cont => match cont with
    | .Fallthrough st' s' =>
      wp «module» posAllocTail (posPOST st n g0 g2 m0 POST) st'
        { s' with values := [] } env
    | .Break 0 st' s' =>
      wp «module» posAllocTail (posPOST st n g0 g2 m0 POST) st'
        { s' with values := [] } env
    | .Break (k + 1) st' s' => posPOST st n g0 g2 m0 POST (.Break k st' s')
    | other => posPOST st n g0 g2 m0 POST other

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem posIterAllocWp (env : HostEnv Unit) (st st1 : Store Unit)
    (n g0 g2 : UInt64) (k : Nat) (v : UInt64) (written : List UInt8)
    (e : Nat → UInt64) (m0 : Nat) (POST : Assertion Unit)
    (_hn32 : n.toNat < 4294967296)
    (hFit32 : g0.toNat + 560 < 4294967296)
    (hFit : g0.toNat + 560 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hL5 : (lebList 10 n).length ≤ 5)
    (hsplit : lebList 10 n = written ++ lebList (10 - k) v)
    (hwlen : written.length = k)
    (hkL : k < (lebList 10 n).length)
    (hrest : v / 128 = 0)
    (hm0 : 2 * (10 - k) + 1 ≤ m0)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
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
    (_hp32L : ((UInt32.ofNat st.mem.pages).toUInt64).toNat = st.mem.pages)
    (hgeM : (g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1 ≤
      (UInt32.ofNat st.mem.pages).toUInt64)
    (h48kN : (g0 + 56 * UInt64.ofNat k + 48).toNat = g0.toNat + 56 * k + 48)
    (hsubHdr : ∀ (c : UInt64), c.toNat ≤ 48 →
      (g0 + 56 * UInt64.ofNat k + 48 - c).toNat =
        g0.toNat + 56 * k + 48 - c.toNat)
    (hs40 : (g0 + 56 * UInt64.ofNat k + 48 - 40).toNat = g0.toNat + 56 * k + 8)
    (hs32 : (g0 + 56 * UInt64.ofNat k + 48 - 32).toNat = g0.toNat + 56 * k + 16)
    (hs24 : (g0 + 56 * UInt64.ofNat k + 48 - 24).toNat = g0.toNat + 56 * k + 24)
    (hs16 : (g0 + 56 * UInt64.ofNat k + 48 - 16).toNat = g0.toNat + 56 * k + 32)
    (hs8 : (g0 + 56 * UInt64.ofNat k + 48 - 8).toNat = g0.toNat + 56 * k + 40)
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
    (hbytes : ∀ i < k,
      st1.mem.bytes (objBase g0 (k - 1) + 48 + i) = written[i]!)
    (hlen : st1.globals.globals.length = st.globals.globals.length)
    (h0L : st1.globals.globals[0]? = some (.i64 (g0 + UInt64.ofNat (56 * k))))
    (h1L : st1.globals.globals[1]? = some (.i64 0))
    (h2L : st1.globals.globals[2]? = some (.i64 (g2 + UInt64.ofNat k)))
    (h3L : st1.globals.globals[3]? = st.globals.globals[3]?)
    (h4L : st1.globals.globals[4]? = st.globals.globals[4]?)
    (h5L : st1.globals.globals[5]? = st.globals.globals[5]?)
    (hpgL : st1.mem.pages = st.mem.pages)
    (hloL : ∀ a < g0.toNat, st1.mem.bytes a = st.mem.bytes a) :
    wp «module»
      [Instruction.block 0 0
          [Instruction.loop 0 0
              [Instruction.localGet 30, Instruction.localGet 26,
                Instruction.geUI64, Instruction.br_if 1,
                Instruction.localGet 28, Instruction.localGet 30,
                Instruction.addI64, Instruction.wrapI64,
                Instruction.localGet 25, Instruction.localGet 30,
                Instruction.addI64, Instruction.wrapI64,
                Instruction.load8U 0, Instruction.store8 0,
                Instruction.localGet 30, Instruction.constI64 1,
                Instruction.addI64, Instruction.localSet 30,
                Instruction.br 0]],
        Instruction.localGet 28, Instruction.localGet 26,
        Instruction.addI64, Instruction.wrapI64, Instruction.localGet 27,
        Instruction.wrapI64, Instruction.store8 0, Instruction.localGet 28,
        Instruction.localSet 12, Instruction.localGet 12,
        Instruction.localSet 5, Instruction.localGet 12,
        Instruction.localSet 6, Instruction.localGet 11,
        Instruction.constI64 1, Instruction.addI64, Instruction.localSet 7,
        Instruction.constI64 1, Instruction.localSet 8]
      (posPOST st n g0 g2 m0 POST)
      { st1 with
        globals :=
          { globals :=
              (st1.globals.globals.set 0
                (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8))).set 2
                (.i64 (g2 + UInt64.ofNat k + 1)) }
        mem :=
          (((((st1.mem.write64
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
      (lFrameFlat (UInt64.ofNat (10 - k)) v (bufPtr g0 k) (bufPtr g0 k)
        (UInt64.ofNat k) 0 0 0 0 (v % 128 &&& 255) (bufPtr g0 k)
        (UInt64.ofNat k) (e 12) (e 13) (e 14) (e 15) (e 16) (e 17)
        (e 18) (e 19) (e 20) (e 21) (e 22) (e 23) (e 24) (bufPtr g0 k)
        (UInt64.ofNat k) (v % 128 &&& 255)
        (g0 + 56 * UInt64.ofNat k + 48) (UInt64.ofNat k + 1) 0 8 0 0
        (g0 + 56 * UInt64.ofNat k + 48 + 8)
        ((g0 + 56 * UInt64.ofNat k + 48 + 8 - 1) / 65536 + 1)
        (g0 + 56 * UInt64.ofNat k + 48))
      env := by
  try simp only [h2L]
  try wp_run_folded []
  try simp [posPOST, hTrap]
  apply wp_block_cons
  apply wp.conseq (Q := posBlockPOST env st n g0 g2 m0 POST)
  · intro cont h
    cases cont with
    | Fallthrough st' s' =>
      simpa only [posBlockPOST, posAllocTail, lFrameFlat_values,
        List.take_zero, List.drop_zero, List.nil_append] using h
    | Break k st' s' =>
      cases k with
      | zero =>
        simpa only [posBlockPOST, posAllocTail, lFrameFlat_values,
          List.take_zero, List.drop_zero, List.nil_append] using h
      | succ k => simpa only [posBlockPOST] using h
    | Return st' values => simpa only [posBlockPOST] using h
    | Trap st' message => simpa only [posBlockPOST] using h
    | Invalid message => simpa only [posBlockPOST] using h
    | OutOfFuel => simpa only [posBlockPOST] using h
    | ReturnCall id st' values => simpa only [posBlockPOST] using h
    | Throwing tag args st' s' => simpa only [posBlockPOST] using h
  apply wp_loop_cons
    (Q := posBlockPOST env st n g0 g2 m0 POST)
    (Inv := fun stC sC =>
      ∃ j : Nat, j ≤ k ∧
        sC = cFramePos g0 v k j e ∧
        stC.globals.globals =
          (st1.globals.globals.set 0
            (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8))).set 2
            (.i64 (g2 + UInt64.ofNat k + 1)) ∧
        stC.mem.pages = st1.mem.pages ∧
        (∀ i : Nat, i < j →
          stC.mem.bytes (g0.toNat + 56 * k + 48 + i) =
            written[i]!) ∧
        (∀ i : Nat, i < k →
          stC.mem.bytes (objBase g0 (k - 1) + 48 + i) =
            written[i]!) ∧
        (∀ a : Nat, a < g0.toNat →
          stC.mem.bytes a = st.mem.bytes a))
    (μ := fun _ sC =>
      match sC.locals with
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
          _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
          _ :: _ :: _ :: _ :: .i64 l30 :: _ =>
          k + 1 - l30.toNat
      | _ => 0)
  · refine ⟨0, Nat.zero_le _, by rw [cFramePos_eq_flat]; rfl, rfl, ?_, ?_,
      ?_, ?_⟩
    · simp [Mem.write64_pages]
    · intro i hi
      omega
    · intro i hi
      dsimp only
      rw [write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs8m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs16m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs24m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs32m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs40m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs0m]
          try simp only [objBase]
          omega)]
      exact hbytes i hi
    · intro a ha
      dsimp only
      rw [write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs8m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs16m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs24m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs32m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs40m]
          try simp only [objBase]
          omega),
        write64_bytes_lo _ _ _ (by
          rw [toUInt32_ofNat_mod_toNat, hs0m]
          try simp only [objBase]
          omega)]
      exact hloL a ha
  · rintro stC sC ⟨j, hjk, rfl, hglC, hpgC, hdst, hsrc, hloC⟩
    have hjU : (UInt64.ofNat j).toNat = j := by u64_omega
    by_cases hjend : j = k
    · subst hjend
      change wp «module» copyBody _ stC (cFramePos g0 v j j e) env
      refine copyExitPos env stC g0 v j e _ ?_
      simp only [posBlockPOST]
      exact posAllocDone env st st1 stC n g0 g2 v j written e m0 POST
        hFit32 hFit hL5 hsplit hwlen hkL hrest hm0 hTrap hkU hglC hpgC
        hdst hloC hlen h0L h1L h2L h3L h4L h5L hpgL
    · have hjlt : j < k := Nat.lt_of_le_of_ne hjk hjend
      have hnge : ¬ (UInt64.ofNat j ≥ UInt64.ofNat k) := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hjU, hkU]
        omega
      change wp «module» copyBody _ stC (cFramePos g0 v k j e) env
      refine copyStepPos env st stC n g0 v k j written e
        ((st1.globals.globals.set 0
          (.i64 (g0 + 56 * UInt64.ofNat k + 48 + 8))).set 2
          (.i64 (g2 + UInt64.ofNat k + 1)))
        (cFramePos g0 v k j e).values _ hFit32 hFit hPages (by omega)
        hwlen hjlt hglC (hpgC.trans hpgL) hdst hsrc hloC
        (hvals := by rfl) (hTrap := ?_) (hB0 := ?_)
      · intro st' msg
        simp [posBlockPOST, posPOST, hTrap]
      · rintro st' s' ⟨hframe', hgl', hpg', hdst', hsrc', hlo'⟩
        refine ⟨⟨j + 1, by omega, hframe', hgl',
          hpg'.trans hpgL.symm, hdst', hsrc', hlo'⟩, ?_⟩
        have hlocals' := congrArg (fun s : Locals => s.locals) hframe'
        change s'.locals = (cFramePos g0 v k (j + 1) e).locals at hlocals'
        have hlocals : s'.locals = (cFramePos g0 v k (j + 1) e).locals :=
          hlocals'
        rw [hlocals]
        simp only [cFramePos]
        rw [toNat_ofNat_lt (by rw [size_eq]; omega), hjU]
        omega


end Project.LebU32.Spec
