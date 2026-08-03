import Project.SharedPair.CopyExit

/-!
# Shared-pair construction suffix

The copy-loop proof composes the generic body theorem with the allocation and
retain suffix.
-/

namespace Project.SharedPair.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

theorem copySuffix_correct
    (env : HostEnv Unit) (st1 : Store Unit) (ptr g0 g2 g3 : UInt64)
    (bytes : List UInt8)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hg0_32 : g0.toNat < 4294967296)
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hadd17 : (UInt64.ofNat bytes.length + 1 + 7).toNat = bytes.length + 8)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hraw : ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8).toNat =
      allocSize (bytes.length + 1))
    (hnot_lt8 : ¬ ((UInt64.ofNat bytes.length + 1 + 7) / 8 * 8 <
      (8 : UInt64)))
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hg0 : st1.globals.globals[0]? = some (.i64 g0))
    (hg1 : st1.globals.globals[1]? = some (.i64 0))
    (hg2 : st1.globals.globals[2]? = some (.i64 g2))
    (hg3 : st1.globals.globals[3]? = some (.i64 g3))
    (hInput : BytesAt st1 ptr bytes)
    (hno_wrap : ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) < g0))
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hsub1 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1) - 1)
    (hpn : ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) /
      65536 + 1).toNat =
      (g0.toNat + 48 + allocSize (bytes.length + 1) - 1) / 65536 + 1)
    (hp32 : ((UInt32.ofNat st1.mem.pages).toUInt64).toNat = st1.mem.pages)
    (hng : ¬ ((UInt32.ofNat st1.mem.pages).toUInt64 <
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16)
    (hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24)
    (hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32)
    (hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40) :
    wp «module» copySuffix (copyPost st1 ptr g0 g2 g3 bytes)
      (copyStore st1 g0 g2 bytes) (copyLocals ptr g0 bytes) env := by
  unfold copySuffix copyPost copyResult copyStore copyLocals
  simp only [Project.SharedPair.func0, List.drop]
  apply wp_block_cons
  apply wp_loop_cons (Inv := vInv st1 ptr g0 g2 bytes) (μ := vMeasure bytes)
  · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [vFrame]
    · rfl
    · rfl
    · intro a ha
      rw [write64_bytes_lo _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        write64_bytes_lo _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        write64_bytes_lo _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        write64_bytes_lo _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        write64_bytes_lo _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        write64_bytes_lo _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    · intro i hi
      omega
    · rw [read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    · rw [read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    · rw [read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
    · rw [read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega),
        Mem.read64_write64_same]
  · rintro st2 s2 ⟨k, hk, rfl, hpg, hgl, hlo, hpref, hh0, hh8, hh16,
      hh24⟩
    refine copyBody env st1 st2 ptr g0 g2 bytes k _
      (bytes.length - k) hLen hPtr32 hBelow hFit32 hg0_32 hlenU hFit
      hPages hszU hszN_ge hszN_ge8 hInput hk hpg hgl hlo hpref hh0 hh8
      hh16 hh24 rfl ?_ ?_ ?_ _ rfl
    · intro st' msg
      rfl
    · intro st' s' h
      wp_run
      exact ⟨h.1, by
        have := h.2
        simp only [vMeasure, vFrame] at this ⊢
        u64_omega⟩
    · intro st' s' hx
      obtain ⟨hkeq, hst', hs'⟩ := hx
      subst hkeq
      rw [hst', hs']
      simp only [List.take, List.drop, List.nil_append,
        Project.Common.Locals.values_values]
      exact copyExit_correct env st1 st2 ptr g0 g2 g3 bytes hLen hPtr32
        hBelow hFit32 hg0_32 hszN_ge hszN_ge8 hlenU hszU hFit hPages
        hg1 hg2 hg3 h17 hsub40 hsub32 hsub24 hsub16 hsub8 hpg hgl hlo
        hpref hh0 hh8 hh16 hh24

/-! The exported retain increments a live object header and its global counter. -/
theorem func3_retains (env : HostEnv Unit) (st4 : Store Unit)
    (p c r3 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 (UInt32.ofNat ((p.toNat - 48) % 4294967296)) =
      5501223100278326855)
    (hrc : st4.mem.read64 (UInt32.ofNat ((p.toNat - 40) % 4294967296)) = c)
    (hc0 : 0 < c.toNat)
    (hg3 : st4.globals.globals[3]? = some (.i64 r3)) :
    TerminatesWith (m := «module») (id := 3) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [.i64 p] ∧
        st'.mem = st4.mem.write64 (p.toUInt32 - 40) (c + 1) ∧
        st'.globals.globals =
          st4.globals.globals.set 3 (.i64 (r3 + 1))) :=
  Project.Runtime.retain_spec env «module» 3 st4 p c r3 (by rfl) rfl
    hp48 hp32 hfit hmagic hrc hc0 hg3

end Project.SharedPair.Spec
