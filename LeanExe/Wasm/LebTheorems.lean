import LeanExe.Wasm.Leb

/-!
# LEB128 encoder characterization

`lebList` is the pure recursion the Talos artifact proof states its loop
invariant against; the theorem identifies it with the shipped
`u32lebU64`, so the artifact theorem composes with this one into a
statement about the source function.
-/

namespace LeanExe.Wasm.Leb

def lebList : Nat → UInt64 → List UInt8
  | 0, _ => []
  | fuel + 1, v =>
      let low := v % 128
      let rest := v / 128
      if rest == 0 then
        [low.toUInt8]
      else
        (low + 128).toUInt8 :: lebList fuel rest

theorem u32lebFuel_eq (fuel : Nat) (v : UInt64) (out : ByteArray) :
    (u32lebFuel fuel v out).data.toList =
    out.data.toList ++ lebList fuel v := by
  induction fuel generalizing v out with
  | zero => simp [u32lebFuel, lebList]
  | succ fuel ih =>
      unfold u32lebFuel lebList
      by_cases h : v / 128 == 0
      · simp [h, ByteArray.push]
      · simp [h, ih, ByteArray.push]

theorem u32lebU64_eq_lebList (n : UInt64) :
    (u32lebU64 n).data.toList = lebList 10 n := by
  unfold u32lebU64
  rw [u32lebFuel_eq]
  rfl

end LeanExe.Wasm.Leb
