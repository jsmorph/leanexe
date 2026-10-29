import Verified.After
import LeanExe.ProofKit.AlignedExec
import LeanExe.Pipeline.AlignedHeap

/-!
Aligned accesses to an array's words.  The code of an array read and of an array write computes
the address of word `w + j` of the array at `p` as `p + (w + j + 1) * 8` (`wordAddrCode`).  When
`p` is a multiple of 8, so is the address, and `wpA` holds of the access: `wpA_wordLoad` is the
aligned form of the `true` branch of `wp_loadWordsCode`, and `wpA_wordStore` the aligned form of
one store of `wp_storeWordsCode`.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section

variable {m : Module} {store : Store Unit} {env' : HostEnv Unit} {ptr w0 j : Nat}
  {p w : UInt64} {ws : Array UInt64} {s : Locals} {rest : Program} {Q : Assertion Unit}

/-- The load of word `w + j` of the array at `p`, whose address is a multiple of 8. -/
theorem wpA_wordLoad (hA : UInt64Array.At store p ws) (hp : p.toNat % 8 = 0)
    (hP : s.get ptr = some (.i64 p)) (hW : s.get w0 = some (.i64 w))
    (hn : w.toNat + j < ws.size)
    (hk : wpA m rest Q store { s with values := .i64 ws[w.toNat + j] :: s.values } env') :
    wpA m (wordAddrCode ptr w0 j ++ .load64 0 :: rest) Q store s env' := by
  have hOffset := word_offset hn (by have := hA.1; omega)
  have hElement := hA.elementBound _ hn
  have hAligned := elementAddress_mod8 hp (w.toNat + j)
  simp only [wordAddrCode, List.cons_append, List.nil_append, wpA_localGet_cons,
    Locals.get_values, hP, hW, wpA_constI64_cons, wpA_addI64_cons, wpA_mulI64_cons,
    wpA_wrapI64_cons, wrap_toUInt32, hOffset]
  rw [wpA_load64_i32 rfl]
  simp only [UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.elementRead _ hn]
  exact ⟨hAligned, hk⟩

/-- The store of the word in local `v` as word `w + j` of the array at `p`, whose address is a
multiple of 8. -/
theorem wpA_wordStore {v : Nat} {x : UInt64} (hA : UInt64Array.At store p ws)
    (hp : p.toNat % 8 = 0) (hP : s.get ptr = some (.i64 p)) (hW : s.get w0 = some (.i64 w))
    (hV : s.get v = some (.i64 x)) (hn : w.toNat + j < ws.size)
    (hk : wpA m rest Q
      { store with mem := store.mem.write64 (p + UInt64.ofNat (8 * (w.toNat + j + 1))).toUInt32 x }
      s env') :
    wpA m (wordAddrCode ptr w0 j ++ .localGet v :: .store64 0 :: rest) Q store s env' := by
  have hOffset := word_offset hn (by have := hA.1; omega)
  have hElement := hA.elementBound _ hn
  have hAligned := elementAddress_mod8 hp (w.toNat + j)
  simp only [wordAddrCode, List.cons_append, List.nil_append, wpA_localGet_cons,
    Locals.get_values, hP, hW, hV, wpA_constI64_cons, wpA_addI64_cons, wpA_mulI64_cons,
    wpA_wrapI64_cons, wrap_toUInt32, hOffset]
  rw [wpA_store64_i32 rfl]
  simp only [UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega)]
  exact ⟨hAligned, hk⟩

/-! ## A port of `wp_loadWordsCode`

`wpA_loadWordsCode` is `wp_loadWordsCode` of `After.lean` with `wpA` for `wp`.  Its statement adds
one premise, that the array's address is a multiple of 8 when the flag is set, and its proof differs
in the rules it names, the dropped `wp_iff_control_types` step, and the alignment conjunct of the
`load64`. -/

theorem wpA_ofWordCode {st : Store Unit} {vs : List Value} (ty : ValueType) (x : UInt64) :
    wpA m (ofWordCode ty ++ rest) Q st { s with values := .i64 x :: vs } env' ↔
      wpA m rest Q st { s with values := typedValue ty x :: vs } env' := by
  cases ty <;> simp [ofWordCode, typedValue, wrap_toUInt32_num, wpA_cons_wp, AlignedOne]

/-- The loads of words `w + j` on of the array at `p`, each under the flag: the array's words
when the flag is 1, and zeros when it is 0.  `w` is the word in local `w0`. -/
theorem wpA_loadWordsCode {flag : Nat} (b : Bool)
    (hA : b = true → UInt64Array.At store p ws) (hp : b = true → p.toNat % 8 = 0) :
    (j : Nat) → (tys : List ValueType) → (s : Locals) → (vals : List UInt64) →
    s.get ptr = some (.i64 p) → s.get w0 = some (.i64 w) →
    s.get flag = some (.i64 (boolWord b)) → vals.length = tys.length →
    (b = true → w.toNat + j + tys.length ≤ ws.size ∧
      ∀ i, i < vals.length → ws[w.toNat + j + i]! = vals[i]!) →
    (b = false → vals = List.replicate tys.length 0) →
    wpA m rest Q store
      { s with values := (List.zipWith typedValue tys vals).reverse ++ s.values } env' →
    wpA m (loadWordsCode ptr w0 flag j tys ++ rest) Q store s env'
  | _, [], s, vals, _, _, _, hl, _, _, hk => by
    obtain rfl : vals = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simpa [loadWordsCode] using hk
  | j, ty :: tys, s, v :: vals, hP, hW, hF, hl, hT, hZ, hk => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [loadWordsCode, List.append_assoc, List.cons_append, List.nil_append]
    simp only [wpA_localGet_cons, hF, wpA_wrapI64_cons]
    refine wpA_iff_cons rfl ?_
    have hNext : wpA m (ofWordCode ty ++ loadWordsCode ptr w0 flag (j + 1) tys ++ rest) Q store
        { s with values := .i64 v :: s.values } env' := by
      rw [List.append_assoc, wpA_ofWordCode]
      refine wpA_loadWordsCode b hA hp (j + 1) tys { s with values := typedValue ty v :: s.values }
        vals hP hW hF hl (fun hb => ?_) (fun hb => ?_) ?_
      · obtain ⟨hFit, hRead⟩ := hT hb
        refine ⟨by simp only [List.length_cons] at hFit; omega, fun i hi => ?_⟩
        have := hRead (i + 1) (by simp; omega)
        rw [show w.toNat + (j + 1) + i = w.toNat + j + (i + 1) by omega, this]
        rfl
      · have := hZ hb
        simp only [List.length_cons, List.replicate_succ, List.cons.injEq] at this
        exact this.2
      · simpa [List.zipWith_cons_cons, List.reverse_cons, List.append_assoc] using hk
    cases b with
    | false =>
      have hv : v = 0 := by
        have := hZ rfl
        simp only [List.length_cons, List.replicate_succ, List.cons.injEq] at this
        exact this.1
      subst hv
      simp only [boolWord, Bool.cond_false]
      simpa [wpA_constI64_cons, wpA_nil] using hNext
    | true =>
      obtain ⟨hFit, hRead⟩ := hT rfl
      have hAt := hA rfl
      simp only [List.length_cons] at hFit
      have hn : w.toNat + j < ws.size := by omega
      have hv : ws[w.toNat + j]! = v := by simpa using hRead 0 (by simp)
      have hOffset := word_offset hn (by have := hAt.1; omega)
      have hElement := hAt.elementBound _ hn
      simp (config := { decide := true }) only [↓reduceIte]
      simp only [wordAddrCode, List.cons_append, List.nil_append, wpA_localGet_cons,
        Locals.get_values, hP, hW, wpA_constI64_cons, wpA_addI64_cons, wpA_mulI64_cons,
        wpA_wrapI64_cons, wrap_toUInt32, hOffset]
      rw [wpA_load64_i32 rfl]
      simp only [UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
      rw [ite_eq_right (by omega), hAt.elementRead _ hn, ← getElem!_pos ws _ hn, hv]
      exact ⟨elementAddress_mod8 (hp rfl) _, by simpa [wpA_nil] using hNext⟩

end

end Verified
