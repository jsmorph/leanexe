import Project.ProofKit.Memory

namespace Project.ProofKit.Memory
open Wasm

def WritesRange (initial final : Store α) (start stop : Nat) : Prop :=
  final = { initial with mem := final.mem } ∧
  final.mem.pages = initial.mem.pages ∧
  ∀ address : Nat, address < start ∨ stop ≤ address →
    final.mem.bytes address = initial.mem.bytes address

theorem WritesRange.refl (store : Store α) (start stop : Nat) :
    WritesRange store store start stop := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem WritesRange.trans {initial middle final : Store α} {start stop : Nat}
    (hFirst : WritesRange initial middle start stop)
    (hSecond : WritesRange middle final start stop) :
    WritesRange initial final start stop := by
  refine ⟨?_, hSecond.2.1.trans hFirst.2.1, ?_⟩
  · calc
      final = { middle with mem := final.mem } := hSecond.1
      _ = { initial with mem := final.mem } := by rw [hFirst.1]
  · intro address hOutside
    exact (hSecond.2.2 address hOutside).trans (hFirst.2.2 address hOutside)

theorem WritesRange.mono {initial final : Store α} {start stop lower upper : Nat}
    (h : WritesRange initial final start stop) (hLower : lower ≤ start) (hUpper : stop ≤ upper) :
    WritesRange initial final lower upper :=
  ⟨h.1, h.2.1, fun address hOutside => h.2.2 address (by omega)⟩

theorem WritesRange.write64 (store : Store α) (address : UInt32) (value : UInt64)
    (start stop : Nat) (hStart : start ≤ address.toNat) (hStop : address.toNat + 8 ≤ stop) :
    WritesRange store { store with mem := store.mem.write64 address value } start stop :=
  ⟨rfl, Mem.write64_pages .., fun _ hOutside => write64_bytes_outside _ _ _ (by omega)⟩

theorem WritesRange.read64 {initial final : Store α} {start stop : Nat}
    (h : WritesRange initial final start stop) (address : UInt32)
    (hOutside : address.toNat + 8 ≤ start ∨ stop ≤ address.toNat) :
    final.mem.read64 address = initial.mem.read64 address := by
  apply read64_congr
  intro byte hByte
  exact h.2.2 (address.toNat + byte) (by omega)

#print axioms WritesRange.trans
#print axioms WritesRange.mono
#print axioms WritesRange.write64
#print axioms WritesRange.read64

end Project.ProofKit.Memory
