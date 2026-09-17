import Interpreter.Wasm.Mem
import LeanExe.WGSL.Output

namespace Project.WGSL.HostMemory

open LeanExe.WGSL

/-- Byte-addressed buffer transfer. Addresses used in the theorem are natural
numbers; `word_address` separately checks the Wasm i32 address conversion. -/
def word (bytes : Nat → UInt8) (address : Nat) : UInt32 :=
  (bytes address).toUInt32 ||| ((bytes (address + 1)).toUInt32 <<< 8) |||
    ((bytes (address + 2)).toUInt32 <<< 16) ||| ((bytes (address + 3)).toUInt32 <<< 24)

def upload (memory : Wasm.Mem) (base size : Nat) : Nat → UInt8 :=
  fun i => if i < size then memory.bytes (base + i) else 0

def download (memory : Wasm.Mem) (base size : Nat) (buffer : Nat → UInt8) : Wasm.Mem :=
  { memory with bytes := fun address =>
      if base ≤ address ∧ address < base + size then buffer (address - base)
      else memory.bytes address }

def words (buffer : Nat → UInt8) : WordBuffer := fun i => word buffer (4 * i)

def region (memory : Wasm.Mem) (base : UInt32) : WordBuffer :=
  fun i => word memory.bytes (base.toNat + 4 * i)

def Fits (memory : Wasm.Mem) (base : UInt32) (elements : Nat) : Prop :=
  base.toNat % 4 = 0 ∧ base.toNat + 4 * elements ≤ memory.pages * 65536 ∧
    base.toNat + 4 * elements ≤ 2 ^ 32

theorem word_address (memory : Wasm.Mem) (base : UInt32) {elements i : Nat}
    (h : Fits memory base elements) (hi : i < elements) :
    memory.read32 (UInt32.ofNat (base.toNat + 4 * i)) = region memory base i := by
  have bound : base.toNat + 4 * i < UInt32.size := by
    have := h.2.2
    change _ ≤ 4294967296 at this
    change _ < 4294967296
    omega
  simp only [Wasm.Mem.read32, UInt32.toNat_ofNat_of_lt' bound, region, word]

theorem upload_word (memory : Wasm.Mem) (base : UInt32) {elements i : Nat}
    (hi : i < elements) :
    words (upload memory base.toNat (4 * elements)) i = region memory base i := by
  have h0 : 4 * i < 4 * elements := by omega
  have h1 : 4 * i + 1 < 4 * elements := by omega
  have h2 : 4 * i + 2 < 4 * elements := by omega
  have h3 : 4 * i + 3 < 4 * elements := by omega
  simp only [words, word, upload, h0, h1, h2, h3, ite_true, region, Nat.add_assoc]

theorem download_word (memory : Wasm.Mem) (base : UInt32) (buffer : Nat → UInt8)
    {elements i : Nat} (hi : i < elements) :
    region (download memory base.toNat (4 * elements) buffer) base i = words buffer i := by
  have h0 : base.toNat ≤ base.toNat + 4 * i ∧ base.toNat + 4 * i < base.toNat + 4 * elements := by omega
  have h1 : base.toNat ≤ base.toNat + 4 * i + 1 ∧ base.toNat + 4 * i + 1 < base.toNat + 4 * elements := by omega
  have h2 : base.toNat ≤ base.toNat + 4 * i + 2 ∧ base.toNat + 4 * i + 2 < base.toNat + 4 * elements := by omega
  have h3 : base.toNat ≤ base.toNat + 4 * i + 3 ∧ base.toNat + 4 * i + 3 < base.toNat + 4 * elements := by omega
  simp only [region, word, download, words, h0, h1, h2, h3, and_self, ite_true]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]

theorem download_outside (memory : Wasm.Mem) (base size : Nat) (buffer : Nat → UInt8)
    {address : Nat} (h : address < base ∨ base + size ≤ address) :
    (download memory base size buffer).bytes address = memory.bytes address := by
  have hn : ¬ (base ≤ address ∧ address < base + size) := by omega
  simp only [download, hn, ite_false]

theorem download_pages (memory : Wasm.Mem) (base size : Nat) (buffer : Nat → UInt8) :
    (download memory base size buffer).pages = memory.pages := rfl

#print axioms word_address
#print axioms upload_word
#print axioms download_word
#print axioms download_outside

end Project.WGSL.HostMemory
