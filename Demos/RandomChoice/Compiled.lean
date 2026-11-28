module

public import Demos.RandomChoice.PicksProof
public import LeanExe.Pipeline.BytesSize
public import Verified.Call
public import Verified.ChargeFacts
public import Verified.Congr
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compiler's module of the pure core.  The call theorems compose the generated
`trapFree` theorems with the programs' equations: from a ready store with room for the generated
bound, export `parseArg`, function 3, returns `parseSpec` of a borrowed buffer and a position,
export `pick`, function 4, returns `pickSpec` of two words, and export `render`, function 9,
returns `renderSpec` of a borrowed array, each without a trap.  A buffer that a store holds has
fewer than `2^32` bytes, which `parseArg_eq` and `putPicks_eq` need, and an array that a store holds
lies below byte `2^32`, so it has fewer than `2^29` words, which `render_eq` needs.  Export
`putPicks`, function 12, consumes the buffer that the caller moves to it, so `putPicks_implements`
states its theorem as `ImplementsA` of a moved buffer, as straight insertion's theorem states it of
a moved array: it returns `putPicksSpec` without a trap, writing the lines into the moved buffer's
block, and it allocates nothing (`putPicks_bound`). -/

namespace Demos.RandomChoice

open LeanExe.Pipeline Library.Numerics.Decimal.Int64Text

verified_compile compiled :=
  [parseStep, parseArg, pick, digitCount, digitByte, textSize, putLine, render,
    RandomHistogram.wordAt, putLineBytes, putPicks]

theorem exports :
    ({ name := "parseArg", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "pick", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "render", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "putPicks", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `parseArg` cannot abort and allocates nothing. -/
theorem parseArg_bound (args : LeanExe.Bytes) (index : UInt64) :
    compiled.parseArg.bound (args, index) = 0 :=
  compiled.parseArg.bound_eq args index

/-- `pick` cannot abort and allocates nothing. -/
theorem pick_bound (n w : UInt64) : compiled.pick.bound (n, w) = 0 :=
  compiled.pick.bound_eq n w

/-- `render` charges the block of its array of `textSize values` words and the output buffer of as
many bytes, at most 21 of each for every value: at most `189 · values.size + 112` bytes. -/
theorem render_bound (values : Array UInt64) (h : values.size < 2 ^ 59) :
    compiled.render.bound values ≤ 189 * values.size + 112 := by
  have hT := textSize_eq values h
  have hlen : (textWords values.toList).length ≤ 21 * values.size := by
    simpa using textWords_length_le values.toList
  rw [compiled.render.bound_eq, Verified.blockCost_eq, hT]
  unfold Verified.Bytes.allocationCost
  split
  · omega
  · rw [Nat.max_def]
    split <;> omega

/-- Function 3, called with a borrowed buffer and a word, returns `parseSpec` of them without a
trap. -/
theorem parseArg_callSpec :
    Verified.CallSpec compiled.module compiled.tables 3 parseSpec compiled.parseArg.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.parseArg.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, hb, _⟩ =>
      parseArg_eq x.1 x.2 (by have := Bytes.size_lt_of_borrowed hb; omega)

/-- Function 4, called with two words, returns `pickSpec` of them without a trap. -/
theorem pick_callSpec :
    Verified.CallSpec compiled.module compiled.tables 4 pickSpec compiled.pick.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.pick.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ => pick_eq x.1 x.2

/-- Function 9, called with a borrowed array of values, returns `renderSpec` of it without a
trap. -/
theorem render_callSpec :
    Verified.CallSpec compiled.module compiled.tables 9 renderSpec compiled.render.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.render.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ values ⟨_, _, hvalues⟩ => render_eq values (by have := hvalues.values.1; omega)

/-- `putPicks` allocates nothing: every `Bytes.set` writes into the moved buffer's block. -/
theorem putPicks_bound (out : LeanExe.Bytes) (n : UInt64) (draw : LeanExe.Bytes)
    (limit : UInt64) : compiled.putPicks.bound ({ val := out }, n, draw, limit) = 0 :=
  compiled.putPicks.bound_eq out n draw limit

/-- Function 12, called with a buffer that the caller moves, a word, a borrowed buffer, and a word,
returns `putPicksSpec` of them without a trap. -/
theorem putPicks_implements :
    ImplementsA false compiled.module 12
      (fun x : Moved LeanExe.Bytes × UInt64 × LeanExe.Bytes × UInt64 =>
        putPicksSpec (x.1.val, x.2.1, x.2.2.1, x.2.2.2))
      (fun x heap store => heap.Within store compiled.module (compiled.putPicks.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.putPicks.bound x) :=
  Verified.implementsA_congr compiled.putPicks.trapFree fun _ _ _ x ⟨_, _, _, _, _, _, _, _, _, _, _, hdraw, _⟩ =>
    putPicks_eq x.1.val x.2.1 x.2.2.1 x.2.2.2 (Bytes.size_lt_of_borrowed hdraw)

#print axioms parseArg_callSpec
#print axioms pick_callSpec
#print axioms render_callSpec
#print axioms render_bound
#print axioms putPicks_implements
#print axioms putPicks_bound

end Demos.RandomChoice
