import Demos.ManifestCheck.Proof
import Library.Hashing.Words.Encoding
import LeanExe.Pipeline.BytesSize
import Verified.Call
import Verified.ChargeFacts
import Verified.Reflect.Command

/-! The verified compiler's module of the pure core.  The call theorems compose the generated
`trapFree` theorems with the programs' equations: from a ready store with room for the generated
bound, export `parse`, function 6, returns `parseSpec` of a borrowed manifest, export `hexMatches`,
function 8, returns `hexMatchesSpec` of a borrowed manifest, a position, and a digest, and export
`render`, function 10, returns `renderSpec` of a borrowed name and a verdict, each without a trap.
A buffer that a store holds has fewer than `2^32` bytes, which the equations need. -/

namespace Demos.ManifestCheck

open LeanExe.Pipeline

verified_compile compiled :=
  [isHex, hexDigit, lineOk, parseStep, parse, digestByte, hexMatches, suffixByte, render]

theorem exports :
    ({ name := "parse", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "hexMatches", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports ∧
    ({ name := "render", funcIdx := 10 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `hexMatches` allocates nothing. -/
theorem hexMatches_bound (m : LeanExe.Bytes) (start : UInt64) (d : Library.Hashing.Words.Words4) :
    compiled.hexMatches.bound (m, start, d) = 0 :=
  compiled.hexMatches.bound_eq m start d

/-- `render` allocates one buffer of the name's bytes and at most nine more. -/
theorem render_bound (name : LeanExe.Bytes) (ok : Bool) (hn : name.data.size < 2 ^ 32) :
    compiled.render.bound (name, ok) ≤ name.data.size + 64 := by
  rw [compiled.render.bound_eq]
  have hs : name.size.toNat = name.data.size := LeanExe.Bytes.size_toNat name (by omega)
  have hc : (name.size + if ok = true then 5 else 9).toNat ≤ name.data.size + 9 := by
    rw [UInt64.toNat_add, hs]
    cases ok <;> simp <;> omega
  exact (Verified.allocationCost_mono hc).trans
    ((Verified.allocationCost_le _).trans (by omega))

/-- Function 6, called with a borrowed manifest, returns `parseSpec` of it without a trap. -/
theorem parse_callSpec :
    Verified.CallSpec compiled.module compiled.tables 6 parseSpec compiled.parse.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.parse.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ m hm => parse_eq m (by have := Bytes.size_lt_of_borrowed hm; omega)

/-- Function 8, called with a borrowed manifest, a position, and a digest, returns
`hexMatchesSpec` of them without a trap. -/
theorem hexMatches_callSpec :
    Verified.CallSpec compiled.module compiled.tables 8 hexMatchesSpec compiled.hexMatches.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.hexMatches.trapFree) compiled.tables nofun).spec
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x hx => hexMatches_eq x.1 x.2.1 x.2.2 (by
      obtain ⟨_, _, _, h1, _⟩ := hx
      have := Bytes.size_lt_of_borrowed h1
      omega)

/-- Function 10, called with a borrowed name and a verdict, returns `renderSpec` of them without a
trap. -/
theorem render_callSpec :
    Verified.CallSpec compiled.module compiled.tables 10 renderSpec compiled.render.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.render.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x hx => render_eq x.1 x.2 (by
      obtain ⟨_, _, _, h1, _⟩ := hx
      have := Bytes.size_lt_of_borrowed h1
      omega)

theorem parseStep_cost_le (m : LeanExe.Bytes) (st : Array UInt64) (i : UInt64) :
    compiled.parseStep.cost (m, ⟨st⟩, i) ≤ 160 := by
  rw [compiled.parseStep.cost_eq, Verified.paidGrowCost_eq]
  split
  · split <;> omega
  · omega

/-- `parse` charges the blocks of its state and its result and at most 160 bytes for each
position: at most `176 n + 464` bytes for a manifest of `n` bytes. -/
theorem parse_bound (m : LeanExe.Bytes) (hn : m.data.size < 2 ^ 32) :
    compiled.parse.bound m ≤ 176 * m.data.size + 464 := by
  have hs : m.size.toNat = m.data.size := LeanExe.Bytes.size_toNat m (by omega)
  have hcount : (m.size + 1).toNat = m.data.size + 1 := by
    rw [UInt64.toNat_add, hs]
    simp only [UInt64.reduceToNat]
    omega
  have hsize := parse_loop_size m (by omega)
  rw [compiled.parse.bound_eq, hcount]
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Verified.loopCost_const_le 160 (fun a b => parseStep_cost_le m b a) _ _ _) _) _) ?_
  simp only [Verified.blockCost_eq, Verified.growCost_eq, Verified.paidGrowCost_eq,
    UInt64.reduceToNat]
  have h0 : (Array.mk ([] : List UInt64)).size = 0 := rfl
  split
  · have hres : ((LeanExe.loop (m.size + 1) #[0, 1] fun i st => parseStep m st i).size.toUInt64 -
        2).toNat ≤ 2 * m.data.size + 2 := by
      generalize (LeanExe.loop (m.size + 1) #[0, 1] fun i st => parseStep m st i).size = z
        at hsize ⊢
      have hz : z.toUInt64.toNat = z := by
        show (UInt64.ofNat z).toNat = z
        exact toNat_ofNat (by omega)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hz]; simp; omega), hz]
      simp
      omega
    omega
  · omega

#print axioms parse_callSpec
#print axioms hexMatches_callSpec
#print axioms render_callSpec
#print axioms render_bound
#print axioms parse_bound

end Demos.ManifestCheck
