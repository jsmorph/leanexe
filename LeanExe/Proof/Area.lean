import LeanExe.Area
import LeanExe.ProofKit.Typed

/-!
Facts about the area of `LeanExe/Area.lean` and the store in which a module starts.  The module's
initial memory starts as `Mem.empty`, whose bytes are 0, and each data segment with an offset writes
only the bytes from its offset below its end, so every byte at or past `dataEnd` keeps the value 0.
`areaByte` reads the memory's byte `j - 4096` for `j` at or past 4096, so every byte of the area
from `areaPrefix` on is 0, and `areaPrefixBytes_getElem` states that the area's prefix holds the
area's bytes.  `initStore m cap` is the module's initial store with a memory cap of `cap` pages,
whose memory has the pages of the module's declaration and whose globals have the types that
`globalTypesOf` gives.
-/

namespace LeanExe

open Wasm LeanExe.ProofKit

theorem roundUp_ge (n a : Nat) (ha : 0 < a) : n ≤ roundUp n a := by
  unfold roundUp
  have h1 := Nat.div_add_mod (n + a - 1) a
  have h2 := Nat.mod_lt (n + a - 1) ha
  rw [Nat.mul_comm]
  omega

theorem roundUp_dvd (n a : Nat) : a ∣ roundUp n a := Nat.dvd_mul_left a _

theorem le_foldl_segEnd (segs : List DataSegment) (acc : Nat) : acc ≤ segs.foldl segEnd acc := by
  induction segs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons seg segs ih =>
      simp only [List.foldl_cons, segEnd]
      split
      · exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
      · exact ih _

theorem end_le_foldl_segEnd (segs : List DataSegment) (acc : Nat) {seg : DataSegment}
    (hs : seg ∈ segs) {off : UInt32} (ho : seg.offset = some off) :
    off.toNat + seg.bytes.length ≤ segs.foldl segEnd acc := by
  induction segs generalizing acc with
  | nil => cases hs
  | cons s segs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hs with rfl | hs
      · have : segEnd acc seg = max acc (off.toNat + seg.bytes.length) := by
          simp only [segEnd, ho]
        rw [this]
        exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_segEnd _ _)
      · exact ih _ hs

/-- A fold whose every step keeps the byte at `i` keeps it. -/
theorem foldl_bytes {f : Mem → DataSegment → Mem} (segs : List DataSegment) (m0 : Mem) (i : Nat)
    (hf : ∀ acc seg, seg ∈ segs → (f acc seg).bytes i = acc.bytes i) :
    (segs.foldl f m0).bytes i = m0.bytes i := by
  induction segs generalizing m0 with
  | nil => rfl
  | cons seg segs ih =>
      simp only [List.foldl_cons]
      rw [ih _ fun acc s hs => hf acc s (List.mem_cons_of_mem _ hs), hf _ _ List.mem_cons_self]

/-- Every byte of the initial memory of `m` at or past `dataEnd m` is 0. -/
theorem initialStore_bytes (m : Module) (i : Nat) (hi : dataEnd m ≤ i) :
    (m.initialStore : Store Unit).mem.bytes i = 0 := by
  unfold Module.initialStore
  unfold dataEnd at hi
  cases hm : m.memory with
  | none => rfl
  | some d =>
      rw [hm] at hi
      simp only at hi ⊢
      rw [foldl_bytes]
      · rfl
      · intro acc seg hs
        split
        · rename_i off ho
          have hle := Nat.le_trans (end_le_foldl_segEnd d.data 0 hs ho) hi
          split
          · split
            · simp only [Mem.writeBytes]
              rw [dif_neg (by omega)]
            · rfl
          · rfl
        · rfl

/-- Every byte of the area of `m` from `areaPrefix m` on is 0. -/
theorem areaByte_tail (m : Module) (j : Nat) (hj : areaPrefix m ≤ j) :
    areaByte m.initialStore j = 0 := by
  have h1 : 4096 + dataEnd m ≤ areaPrefix m := by
    unfold areaPrefix roundUp
    omega
  unfold areaByte
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact initialStore_bytes m _ (by omega)

/-- A list of `n` bytes that agrees with a memory of `pages` pages on its first `n` bytes. -/
def AgreesWith (n pages : Nat) (acc : List UInt8) (mem : Mem) : Prop :=
  acc.length = n ∧ mem.pages = pages ∧ ∀ j < n, acc[j]? = some (mem.bytes j)

/-- The write of a segment that ends at or below `n` keeps a list and a memory in agreement. -/
theorem agrees_segWrite {n pages : Nat} {acc : List UInt8} {mem : Mem} {seg : DataSegment}
    (hend : ∀ off, seg.offset = some off → off.toNat + seg.bytes.length ≤ n)
    (h : AgreesWith n pages acc mem) :
    AgreesWith n pages (segWrite pages acc seg) (match seg.offset with
      | some off =>
          if seg.memIdx = 0 && seg.offsetExpr.isEmpty then
            if off.toNat + seg.bytes.length ≤ mem.pages * 65536 then
              mem.writeBytes off.toNat seg.bytes
            else mem
          else mem
      | none => mem) := by
  obtain ⟨hl, hp, hb⟩ := h
  unfold segWrite
  cases ho : seg.offset with
  | none => exact ⟨hl, hp, hb⟩
  | some off =>
      have hle := hend off ho
      simp only
      rw [hp]
      split
      · split
        · refine ⟨?_, hp, fun j hj => ?_⟩
          · simp only [List.length_append, List.length_take, List.length_drop, hl]
            omega
          · simp only [Mem.writeBytes]
            by_cases h1 : j < off.toNat
            · rw [List.append_assoc, List.getElem?_append_left (by simp [hl]; omega),
                List.getElem?_take_of_lt h1, hb j hj, dif_neg (by omega)]
            · by_cases h2 : j < off.toNat + seg.bytes.length
              · rw [List.getElem?_append_left (by simp [hl]; omega),
                  List.getElem?_append_right (by simp [hl]; omega), dif_pos ⟨by omega, h2⟩]
                simp [hl, show min off.toNat n = off.toNat by omega]
              · rw [List.getElem?_append_right (by simp [hl]; omega), List.getElem?_drop,
                  dif_neg (by omega)]
                simp only [List.length_append, List.length_take, hl]
                rw [show off.toNat + seg.bytes.length + (j - (min off.toNat n + seg.bytes.length))
                  = j by omega]
                exact hb j hj
        · exact ⟨hl, hp, hb⟩
      · exact ⟨hl, hp, hb⟩

/-- `memPrefix` has `n` bytes, those of the initial memory of `m`. -/
theorem memPrefix_agrees (m : Module) (n : Nat) (hn : dataEnd m ≤ n) :
    (memPrefix m n).length = n ∧
      ∀ j < n, (memPrefix m n)[j]? = some ((m.initialStore : Store Unit).mem.bytes j) := by
  unfold memPrefix Module.initialStore
  unfold dataEnd at hn
  cases hm : m.memory with
  | none => exact ⟨by simp, fun j hj => by simp [List.getElem?_replicate, hj]; rfl⟩
  | some d =>
      rw [hm] at hn
      simp only at hn ⊢
      suffices H : ∀ (G : Mem → DataSegment → Mem), (∀ acc mem seg, seg ∈ d.data →
          AgreesWith n d.pagesMin.toNat acc mem →
          AgreesWith n d.pagesMin.toNat (segWrite d.pagesMin.toNat acc seg) (G mem seg)) →
          (d.data.foldl (segWrite d.pagesMin.toNat) (List.replicate n 0)).length = n ∧
          ∀ j < n, (d.data.foldl (segWrite d.pagesMin.toNat) (List.replicate n 0))[j]? =
            some ((d.data.foldl G (Mem.empty d.pagesMin.toNat)).bytes j) by
        apply H
        intro acc mem seg hs h
        exact agrees_segWrite (fun off ho =>
          Nat.le_trans (end_le_foldl_segEnd d.data 0 hs ho) hn) h
      intro G hG
      have key : ∀ (segs : List DataSegment) (acc : List UInt8) (mem : Mem),
          (∀ s ∈ segs, s ∈ d.data) → AgreesWith n d.pagesMin.toNat acc mem →
          AgreesWith n d.pagesMin.toNat (segs.foldl (segWrite d.pagesMin.toNat) acc)
            (segs.foldl G mem) := by
        intro segs
        induction segs with
        | nil => intro acc mem _ h; exact h
        | cons s segs ih =>
            intro acc mem hs h
            exact ih _ _ (fun x hx => hs x (List.mem_cons_of_mem _ hx))
              (hG acc mem s (hs s List.mem_cons_self) h)
      have k := key d.data (List.replicate n 0) (Mem.empty d.pagesMin.toNat) (fun _ h => h)
        ⟨by simp, rfl, fun i hi => by simp [List.getElem?_replicate, hi]; rfl⟩
      exact ⟨k.1, k.2.2⟩

theorem memPrefix_getElem (m : Module) (n : Nat) (hn : dataEnd m ≤ n) (j : Nat) (hj : j < n) :
    (memPrefix m n)[j]? = some ((m.initialStore : Store Unit).mem.bytes j) :=
  (memPrefix_agrees m n hn).2 j hj

theorem memPrefix_length (m : Module) (n : Nat) (hn : dataEnd m ≤ n) :
    (memPrefix m n).length = n :=
  (memPrefix_agrees m n hn).1

theorem areaPrefixBytes_length (m : Module) : (areaPrefixBytes m).length = areaPrefix m := by
  have h1 : 4096 + dataEnd m ≤ areaPrefix m := by
    unfold areaPrefix roundUp
    omega
  unfold areaPrefixBytes
  rw [List.length_append, List.length_map, List.length_range, memPrefix_length m _ (by omega)]
  omega

/-- The area's prefix in an image holds the area's bytes. -/
theorem areaPrefixBytes_getElem (m : Module) (j : Nat) (hj : j < areaPrefix m) :
    (areaPrefixBytes m)[j]? = some (areaByte m.initialStore j) := by
  have h1 : 4096 + dataEnd m ≤ areaPrefix m := by
    unfold areaPrefix roundUp
    omega
  unfold areaPrefixBytes
  by_cases hj4 : j < 4096
  · rw [List.getElem?_append_left (by simp; omega)]
    simp [hj4]
  · rw [List.getElem?_append_right (by simp; omega), List.length_map, List.length_range,
      memPrefix_getElem m _ (by omega) _ (by omega)]
    unfold areaByte
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The store in which the program's function starts: the module's initial store with a memory
of `cap` pages. -/
def initStore (m : Module) (cap : Nat) : Store Unit :=
  { (m.initialStore : Store Unit) with memoryCaps := [cap] }

theorem memIs64_of_areaOk {m : Module} {cap : Nat} (h : areaOk m cap = true) :
    m.memIs64 = false := by
  unfold areaOk at h
  unfold Module.memIs64
  cases hd : m.memory with
  | none => rfl
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      exact h.1.1.1

theorem cap_lt_of_areaOk {m : Module} {cap : Nat} (h : areaOk m cap = true) : cap < 4096 := by
  unfold areaOk at h
  cases hd : m.memory with
  | none => rw [hd] at h; cases h
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2

/-- The memory of `m` starts with at most `cap` pages when `areaOk m cap` holds. -/
theorem pages_le_of_areaOk {m : Module} {cap : Nat} (h : areaOk m cap = true) :
    (m.memory.map (·.pagesMin.toNat)).getD 0 ≤ cap := by
  unfold areaOk at h
  cases hd : m.memory with
  | none => rw [hd] at h; cases h
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simpa using h.1.2

theorem foldl_pages {β : Type} (f : Mem → β → Mem) (hf : ∀ acc b, (f acc b).pages = acc.pages) :
    ∀ (l : List β) (m0 : Mem), (l.foldl f m0).pages = m0.pages
  | [], _ => rfl
  | b :: l, m0 => by rw [List.foldl_cons, foldl_pages f hf l, hf]

theorem initialStore_pages {m : Module} {d : MemDecl} (h : m.memory = some d) :
    (m.initialStore : Store Unit).mem.pages = d.pagesMin.toNat := by
  unfold Module.initialStore
  simp only [h]
  rw [foldl_pages]
  · rfl
  · intro acc seg
    split
    · split
      · split
        · rfl
        · rfl
      · rfl
    · rfl

theorem hasType_of_valueType {v : Value} {t : ValueType} (h : valueType v = some t) :
    HasType t v := by
  cases v <;> simp [valueType] at h <;> subst h <;> trivial

theorem typed_of_valueTypes : ∀ (gs : List GlobalDecl) (gts : List ValueType),
    gs.mapM (fun g => valueType g.init) = some gts → Typed gts (gs.map (·.init))
  | [], gts, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      trivial
  | g :: gs, gts, h => by
      rw [List.mapM_cons] at h
      cases hv : valueType g.init with
      | none => simp [hv] at h
      | some t =>
          cases hr : gs.mapM (fun g => valueType g.init) with
          | none => simp [hv, hr] at h
          | some ts =>
              simp [hv, hr] at h
              subst h
              exact ⟨hasType_of_valueType hv, typed_of_valueTypes gs ts hr⟩

end LeanExe
