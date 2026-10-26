import Verified.Wasi.CompactCode
import Verified.Heap

/-! The move loop of the compaction: a downward, word-at-a-time copy of a byte range. -/

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- Byte `j` of a word written at `a` is byte `j` of the memory from which the word was read at
`b`. -/
theorem write64_read64_byte (mem source : Mem) (a b : UInt32) {j : Nat} (hj : j < 8) :
    (mem.write64 a (source.read64 b)).bytes (a.toNat + j) = source.bytes (b.toNat + j) := by
  interval_cases j <;>
    simp only [Mem.write64, Mem.read64, Nat.add_zero, Nat.add_eq_left, OfNat.ofNat_ne_zero,
      Nat.succ_ne_self, reduceIte, Nat.reduceEqDiff] <;>
    apply UInt8.toBitVec_inj.mp <;>
    simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_and, UInt8.toBitVec_toUInt64] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit hbit <;>
    interval_cases bit <;> simp [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']

/-- The 32-bit address of `p + k` is `p + k` when that sum lies below `2 ^ 32`. -/
theorem address_toNat {p : UInt64} {k : Nat} (h : p.toNat + k < 4294967296) :
    (p + UInt64.ofNat k).toUInt32.toNat = p.toNat + k := by
  have hk : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  rw [Memory.toUInt32_toNat, UInt64.toNat_add, hk]
  omega

/-- The move loop: the bytes from `psrc`, as many as `n` rounded up to a word, go to the bytes
from `pdst`, which lies at or below `psrc`.  The loop writes only that range and changes no local
but `index`. -/
theorem wp_moveCode {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {dst src count index : Nat} {pdst psrc n : UInt64} {rest : Program} {Q : Assertion Unit}
    (hDst : s.get dst = some (.i64 pdst)) (hSrc : s.get src = some (.i64 psrc))
    (hCount : s.get count = some (.i64 n))
    (hDstI : dst ≠ index) (hSrcI : src ≠ index) (hCountI : count ≠ index)
    (hLow : s.params.length ≤ index) (hHigh : index < s.params.length + s.locals.length)
    (hOrder : pdst.toNat ≤ psrc.toNat)
    (hEnd : psrc.toNat + roundWord n.toNat ≤ store.mem.pages * 65536)
    (hFit : store.mem.pages * 65536 ≤ 4294967296)
    (hNext : ∀ (store' : Store Unit) (s' : Locals),
      Memory.WritesRange store store' pdst.toNat (pdst.toNat + roundWord n.toNat) →
      (∀ j, j < roundWord n.toNat →
        store'.mem.bytes (pdst.toNat + j) = store.mem.bytes (psrc.toNat + j)) →
      s'.params = s.params → s'.locals.length = s.locals.length →
      (∀ j, j ≠ index → s'.get j = s.get j) → s'.values = s.values →
      wp m rest Q store' s' host) :
    wp m (moveCode dst src count index ++ rest) Q store s host := by
  have hSize : UInt64.size = 18446744073709551616 := rfl
  have hRound := roundWord_mod n.toNat
  have hRoundLe := roundWord_lt n.toNat
  have hRoundGe := roundWord_le n.toNat
  simp only [moveCode, List.cons_append, List.nil_append, wp_constI64_cons]
  refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ index := hLow
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ k, 8 * k ≤ roundWord n.toNat ∧
      Memory.WritesRange store st pdst.toNat (pdst.toNat + 8 * k) ∧
      (∀ j, j < 8 * k → st.mem.bytes (pdst.toNat + j) = store.mem.bytes (psrc.toNat + j)) ∧
      si.params = s.params ∧ si.locals.length = s.locals.length ∧
      (∀ j, j ≠ index → si.get j = s.get j) ∧
      si.get index = some (.i64 (UInt64.ofNat (8 * k))))
    (fun _ si => match si.get index with
      | some (.i64 i) => roundWord n.toNat - i.toNat
      | _ => 0)
    ⟨0, Nat.zero_le _, Memory.WritesRange.refl .., fun j hj => absurd hj (by omega), rfl,
      by simp [setLocal], fun j hj => Locals.get_setLocal_ne hLow0 hj,
      Locals.get_setLocal_same hLow0 hHigh⟩ ?_
  rintro st si ⟨k, hk, hW, hMoved, hp, hl, hOther, hIdx⟩
  have hk64 : (UInt64.ofNat (8 * k)).toNat = 8 * k :=
    UInt64.toNat_ofNat_of_lt' (by rw [hSize]; omega)
  simp only [wp_localGet_cons, Locals.get_values, hIdx, hOther count hCountI, hCount,
    wp_geUI64_cons, wp_br_if_cons]
  by_cases hDone : n ≤ UInt64.ofNat (8 * k)
  · -- The move is complete: `8 * k` is the least multiple of 8 at least `n`.
    have hkEq : 8 * k = roundWord n.toNat := by
      rw [UInt64.le_iff_toNat_le, hk64] at hDone
      have := roundWord_le_of_mod hDone (by omega)
      omega
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    rw [hkEq] at hW hMoved
    exact hNext st _ hW hMoved hp hl (fun j hj => hOther j hj) rfl
  · -- One more word.
    have hLess : 8 * k < n.toNat := by
      rw [UInt64.le_iff_toNat_le, hk64] at hDone; omega
    have hNextWord : 8 * k + 8 ≤ roundWord n.toNat := by omega
    have hSrcAddr : (psrc + UInt64.ofNat (8 * k)).toUInt32.toNat = psrc.toNat + 8 * k :=
      address_toNat (by omega)
    have hDstAddr : (pdst + UInt64.ofNat (8 * k)).toUInt32.toNat = pdst.toNat + 8 * k :=
      address_toNat (by omega)
    have hPages : st.mem.pages = store.mem.pages := hW.2.1
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
    simp only [wp_localGet_cons, Locals.get_values, hOther dst hDstI, hDst, hIdx,
      hOther src hSrcI, hSrc, wp_addI64_cons, wp_wrapI64_cons, wrap_toUInt32]
    simp only [wp_load64_cons, wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (show ¬((psrc + UInt64.ofNat (8 * k)).toUInt32.toNat + 8 >
        st.mem.pages * 65536) by rw [hSrcAddr, hPages]; omega),
      ite_eq_right (show ¬((pdst + UInt64.ofNat (8 * k)).toUInt32.toNat + 8 >
        st.mem.pages * 65536) by rw [hDstAddr, hPages]; omega)]
    simp only [wp_localGet_cons, Locals.get_values, hIdx, wp_constI64_cons, wp_addI64_cons]
    have hLowI : si.params.length ≤ index := by rw [hp]; exact hLow
    have hHighI : index < si.params.length + si.locals.length := by rw [hp, hl]; exact hHigh
    refine wp_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
    rw [wp_br_cons]
    dsimp only
    have hLowI' : ({ si with values := si.values } : Locals).params.length ≤ index := hLowI
    have hSucc : UInt64.ofNat (8 * k) + 8 = UInt64.ofNat (8 * (k + 1)) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, hk64,
        UInt64.toNat_ofNat_of_lt' (by rw [hSize]; omega)]
      simp only [UInt64.reduceToNat]
      omega
    have hSucc64 : (UInt64.ofNat (8 * (k + 1))).toNat = 8 * (k + 1) :=
      UInt64.toNat_ofNat_of_lt' (by rw [hSize]; omega)
    let st' : Store Unit := { st with mem := st.mem.write64 (pdst + UInt64.ofNat (8 * k)).toUInt32
      (st.mem.read64 (psrc + UInt64.ofNat (8 * k)).toUInt32) }
    have hWrite : Memory.WritesRange st st' pdst.toNat (pdst.toNat + 8 * (k + 1)) :=
      Memory.WritesRange.write64 _ _ _ _ _ (by rw [hDstAddr]; omega) (by rw [hDstAddr]; omega)
    refine ⟨⟨k + 1, by omega, (hW.mono le_rfl (by omega)).trans hWrite, fun j hj => ?_, hp,
      by simp [setLocal, hl], fun j hj => ?_, ?_⟩, ?_⟩
    · by_cases hj' : j < 8 * k
      · rw [show st'.mem.bytes (pdst.toNat + j) = st.mem.bytes (pdst.toNat + j) from
          Memory.write64_bytes_outside _ _ _ (by rw [hDstAddr]; omega)]
        exact hMoved j hj'
      · have hByte := write64_read64_byte st.mem st.mem (pdst + UInt64.ofNat (8 * k)).toUInt32
          (psrc + UInt64.ofNat (8 * k)).toUInt32 (j := j - 8 * k) (by omega)
        rw [hDstAddr, hSrcAddr] at hByte
        rw [show pdst.toNat + j = pdst.toNat + 8 * k + (j - 8 * k) by omega]
        change (st.mem.write64 _ _).bytes _ = _
        rw [hByte, show psrc.toNat + 8 * k + (j - 8 * k) = psrc.toNat + j by omega]
        exact hW.2.2 _ (Or.inr (by omega))
    · rw [Locals.get_values, Locals.get_setLocal_ne hLowI' hj, Locals.get_values]
      exact hOther j hj
    · rw [Locals.get_setLocal_same hLowI' hHighI, hSucc]
    · simp only [Locals.get_setLocal_same hLowI' hHighI, hSucc, hSucc64, hk64]
      omega

end Verified.Wasi
