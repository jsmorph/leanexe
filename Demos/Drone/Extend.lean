import Demos.Drone.Program
import LeanExe.IR.Combinators

/-! The table that `extend` builds and its size: below `count`, `extend` builds the table
extended by the next row, entry by entry, and otherwise it returns the table that it consumed. -/

namespace Demos.Drone

open LeanExe.IR (build_size)

/-- Entry `j` of the table that `extend` builds. -/
def extendChoice (terrain : Array UInt64) (count i : UInt64) (table : Array Choice) (j : UInt64) :
    Choice :=
  let size := table.size.toUInt64
  let target := j - size
  let c := best (floorAt terrain (i - 1)) (floorAt terrain i) table (size - stateCount) target
    (if (decide (j < size) || (i + 1 == count && target != 0)) = true then 0 else stateCount)
  ⟨if j < size then table[j.toNat]!.time else c.time,
    if j < size then table[j.toNat]!.excess else c.excess,
    if j < size then table[j.toNat]!.parent else c.parent⟩

theorem extend_lt (terrain : Array UInt64) (count i : UInt64) (table : Array Choice)
    (h : i < count) :
    extend terrain count i table = (0, i + 1,
      LeanExe.build (table.size.toUInt64 + stateCount) (extendChoice terrain count i table)) := by
  simp only [extend, h, ite_true]
  rfl

theorem extend_ge (terrain : Array UInt64) (count i : UInt64) (table : Array Choice)
    (h : ¬i < count) : extend terrain count i table = (1, i, table) := by
  simp only [extend, h, ite_false]

/-- The size of the table `extend` builds. -/
theorem extend_size (terrain : Array UInt64) (count i : UInt64) (table : Array Choice)
    (hlt : i < count) (hsize : table.size ≤ 2835) :
    (extend terrain count i table).2.2.size = table.size + 45 := by
  rw [extend_lt terrain count i table hlt, build_size, UInt64.toNat_add]
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have hS : stateCount.toNat = 45 := rfl
  rw [Nat.mod_eq_of_lt (by omega), hS, Nat.mod_eq_of_lt (by omega)]

end Demos.Drone
