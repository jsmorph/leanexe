import LeanExe.A64.Table
import LeanExe.A64.Proof.Bits

/-!
Under the covered configuration, with memory holding `tableBytes` at `TTBR0_EL1`, translation
gives the GiB from 0 the type of writable Device memory and the GiB from `0x40000000` the type of
writable and executable Normal memory.  The model gives no type of memory to an address from
`0x80000000`.  `classify_table` reduces `classify` at an address below 2 ^ 32 to the descriptor of
its GiB, `a >>> 30`, and decides the four GiBs by evaluation in the kernel.
-/

namespace LeanExe.A64

theorem length_tableBytes : tableBytes.length = 32 := rfl

/-- Byte `k` of descriptor `i` is byte `8 i + k` of the table. -/
theorem getElem_tableBytes : ∀ i (hi : i < 4) k (hk : k < 8),
    tableBytes[8 * i + k]'(by rw [length_tableBytes]; omega) = byteOf tableWords[i] k := by
  decide +kernel

/-- A memory that holds the table at `p` holds descriptor `i` at `p + 8 i`. -/
theorem load64_table {mem : UInt64 → UInt8} {p : UInt64}
    (hm : ∀ j (hj : j < 32), mem (p + UInt64.ofNat j) = tableBytes[j]) (i : Nat) (hi : i < 4) :
    load64 mem (p + 8 * UInt64.ofNat i) = tableWords[i] := by
  apply load64_bytes
  intro k hk
  have e : p + 8 * UInt64.ofNat i + UInt64.ofNat k = p + UInt64.ofNat (8 * i + k) := by
    rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.ofNat_mul]
    rfl
  rw [e, hm _ (by omega)]
  exact getElem_tableBytes i hi k hk

theorem toNat_shiftRight_30 (a : UInt64) : (a >>> 30).toNat = a.toNat / 2 ^ 30 := by
  rw [UInt64.toNat_shiftRight, show (30 : UInt64).toNat % 64 = 30 from rfl,
    Nat.shiftRight_eq_div_pow]

/-- An address `a` below 2 ^ 32 lies in a GiB `n` below 4: `a >>> 30` is `n`, and bits 30 and 31
of `a`, which `classify` compares with the output address of the descriptor, form `n * 2 ^ 30`. -/
theorem gib_of_lt {a : UInt64} (ha : a < 0x100000000) :
    ∃ n < 4, a >>> 30 = UInt64.ofNat n ∧ a &&& 0xC0000000 = UInt64.ofNat (n * 2 ^ 30) := by
  have hx : a.toNat < 2 ^ 32 := UInt64.lt_iff_toNat_lt.mp ha
  have hlo : (a.toNat &&& 0xC0000000) % 2 ^ 30 = 0 := by
    rw [Nat.and_mod_two_pow, show 0xC0000000 % 2 ^ 30 = 0 from rfl, Nat.and_zero]
  have hhi : (a.toNat &&& 0xC0000000) / 2 ^ 30 = a.toNat / 2 ^ 30 := by
    rw [Nat.and_div_two_pow, show 0xC0000000 / 2 ^ 30 = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  refine ⟨a.toNat / 2 ^ 30, by omega, UInt64.toNat_inj.mp ?_, UInt64.toNat_inj.mp ?_⟩
  · rw [toNat_shiftRight_30, UInt64.toNat_ofNat']
    omega
  · rw [UInt64.toNat_and, UInt64.toNat_ofNat',
      show (0xC0000000 : UInt64).toNat = 0xC0000000 from rfl]
    omega

/-- The covered configuration sets `MAIR_EL1` to `mairValue`. -/
theorem Sys.mair_of_covered {h : Hw} {s : Sys} (hc : s.covered h = true) :
    s.mair = mairValue := by
  simp only [Sys.covered, Bool.and_eq_true, beq_iff_eq] at hc
  exact hc.1.1.1.1.2

/-- With `CPACR_EL1` at `cpacrValue`, EL1 may access floating point. -/
theorem Sys.fpAccess_of_cpacr {s : Sys} (hc : s.cpacr = cpacrValue) : s.fpAccess = true := by
  unfold Sys.fpAccess
  rw [hc]
  decide

/-- Under the covered configuration with the table at `TTBR0_EL1`, the type of memory at an
address below 2 ^ 32 depends only on its GiB, `a >>> 30`: writable Device memory in the first,
writable and executable Normal memory in the second, and none in the other two. -/
theorem classify_table {h : Hw} {s : Sys} {mem : UInt64 → UInt8} {a : UInt64}
    (hc : s.covered h = true)
    (hm : ∀ j (hj : j < 32), mem (s.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    (ha : a < 0x100000000) :
    classify h s mem a =
      [some (MemType.device true), some (MemType.normal true true), none, none].getD
        (a >>> 30).toNat none := by
  obtain ⟨n, hn, hq, hk⟩ := gib_of_lt ha
  have hg : (!s.covered h || decide (0x100000000 ≤ a)) = false := by
    simp only [hc, decide_eq_false (UInt64.not_le.mpr ha), Bool.not_true, Bool.false_or]
  rw [classify, hg, ite_eq_right Bool.false_ne_true, hq, hk, load64_table hm n hn,
    Sys.mair_of_covered hc]
  clear hq hk
  revert n
  decide +kernel

/-- The table maps the GiB from 0 as Device memory that EL1 may write. -/
theorem classify_device {h : Hw} {s : Sys} {mem : UInt64 → UInt8} {a : UInt64}
    (hc : s.covered h = true)
    (hm : ∀ j (hj : j < 32), mem (s.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    (ha : a < 0x40000000) :
    classify h s mem a = some (.device true) := by
  have hx : a.toNat < 2 ^ 30 := UInt64.lt_iff_toNat_lt.mp ha
  have := classify_table hc hm (UInt64.lt_iff_toNat_lt.mpr (show a.toNat < 2 ^ 32 by omega))
  rw [toNat_shiftRight_30, show a.toNat / 2 ^ 30 = 0 by omega] at this
  exact this

/-- The table maps the UART as Device memory that EL1 may write. -/
theorem classify_uart {h : Hw} {s : Sys} {mem : UInt64 → UInt8} (hc : s.covered h = true)
    (hm : ∀ j (hj : j < 32), mem (s.ttbr0 + UInt64.ofNat j) = tableBytes[j]) :
    classify h s mem uartAddr = some (.device true) :=
  classify_device hc hm (by decide)

/-- The table maps the GiB from `0x40000000` as Normal memory that EL1 may write and execute. -/
theorem classify_normal {h : Hw} {s : Sys} {mem : UInt64 → UInt8} {a : UInt64}
    (hc : s.covered h = true)
    (hm : ∀ j (hj : j < 32), mem (s.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    (ha : 0x40000000 ≤ a) (ha' : a < 0x80000000) :
    classify h s mem a = some (.normal true true) := by
  have hx : 2 ^ 30 ≤ a.toNat := UInt64.le_iff_toNat_le.mp ha
  have hx' : a.toNat < 2 ^ 31 := UInt64.lt_iff_toNat_lt.mp ha'
  have := classify_table hc hm (UInt64.lt_iff_toNat_lt.mpr (show a.toNat < 2 ^ 32 by omega))
  rw [toNat_shiftRight_30, show a.toNat / 2 ^ 30 = 1 by omega] at this
  exact this

/-- The model gives no type of memory to an address from `0x80000000`: the table's descriptors
of the GiBs from `0x80000000` are invalid, and translation faults from 2 ^ 32. -/
theorem classify_none {h : Hw} {s : Sys} {mem : UInt64 → UInt8} {a : UInt64}
    (hc : s.covered h = true)
    (hm : ∀ j (hj : j < 32), mem (s.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    (ha : 0x80000000 ≤ a) :
    classify h s mem a = none := by
  by_cases hb : a < 0x100000000
  · have hx : 2 ^ 31 ≤ a.toNat := UInt64.le_iff_toNat_le.mp ha
    have hx' : a.toNat < 2 ^ 32 := UInt64.lt_iff_toNat_lt.mp hb
    have := classify_table hc hm hb
    rw [toNat_shiftRight_30] at this
    rcases (show a.toNat / 2 ^ 30 = 2 ∨ a.toNat / 2 ^ 30 = 3 by omega) with e | e <;>
      rw [e] at this <;> exact this
  · have hg : (!s.covered h || decide (0x100000000 ≤ a)) = true := by
      simp only [decide_eq_true (UInt64.not_lt.mp hb), Bool.or_true]
    rw [classify, hg, ite_eq_left rfl]

end LeanExe.A64
