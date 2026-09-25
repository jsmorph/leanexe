import Project.Gpt2CachedStep.CachedScore.Source
import Project.ProofKit.F32DotError

namespace Project.Gpt2CachedStep.CachedScore.Error
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

def query (qkv : ByteArray) (head i : Nat) : UInt32 := word qkv (head * 64 + i)
def key (cache qkv : ByteArray) (layer position source head i : Nat) : UInt32 :=
  cachedKv cache qkv layer position source (head * 64 + i)

structure Bounds where
  mulBound : Nat → Nat
  addBound : Nat → Nat
  scaleBound : Nat

structure Ranges (cache qkv : ByteArray) (layer position source head : Nat) (b : Bounds) : Prop where
  queryFinite : ∀ i < 64, CodeLib.IEEE32.Finite (query qkv head i)
  keyFinite : ∀ i < 64, CodeLib.IEEE32.Finite (key cache qkv layer position source head i)
  mulLower : ∀ i < 64, 173 ≤ b.mulBound i
  mulUpper : ∀ i < 64, b.mulBound i ≤ 425
  mulRange : ∀ i < 64, Wasm.IEEE32.scaledMagnitude (query qkv head i) *
    Wasm.IEEE32.scaledMagnitude (key cache qkv layer position source head i) < 2 ^ b.mulBound i
  addUpper : ∀ i < 64, b.addBound i ≤ 276
  addRange : ∀ i < 64, (Wasm.IEEE32.scaledValue (dotPrefix cache qkv layer position source head i) +
    Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (query qkv head i)
      (key cache qkv layer position source head i))).natAbs < 2 ^ b.addBound i
  scaleLower : 173 ≤ b.scaleBound
  scaleUpper : b.scaleBound ≤ 425
  scaleRange : Wasm.IEEE32.scaledMagnitude (dotPrefix cache qkv layer position source head 64) *
    Wasm.IEEE32.scaledMagnitude 0x3E000000 < 2 ^ b.scaleBound

noncomputable def dotError (qkv : ByteArray) (head : Nat) (K eq ek : Nat → ℝ) (b : Bounds) : ℝ :=
  ∑ i ∈ Finset.range 64, (F32MultiplicationBounds.epsilon (b.mulBound i) +
    (|value (query qkv head i)| * ek i + eq i * |K i|) + F32AdditionBounds.epsilon (b.addBound i))

noncomputable def error (qkv : ByteArray) (head : Nat) (K eq ek : Nat → ℝ) (b : Bounds) : ℝ :=
  F32MultiplicationBounds.epsilon b.scaleBound + dotError qkv head K eq ek b / 8

theorem dot_compute (cache qkv : ByteArray) (layer position source head count : Nat) :
    dotPrefix cache qkv layer position source head count =
      F32DotError.compute (query qkv head) (key cache qkv layer position source head) count := rfl

theorem score_error (cache qkv : ByteArray) (layer position source head : Nat) (b : Bounds)
    (Q K eq ek : Nat → ℝ) (h : Ranges cache qkv layer position source head b)
    (hQ : ∀ i < 64, |value (query qkv head i) - Q i| ≤ eq i)
    (hK : ∀ i < 64, |value (key cache qkv layer position source head i) - K i| ≤ ek i) :
    CodeLib.IEEE32.Finite (cachedScore cache qkv layer position source head) ∧
      |value (cachedScore cache qkv layer position source head) -
        (∑ i ∈ Finset.range 64, Q i * K i) / 8| ≤ error qkv head K eq ek b := by
  have hd := F32DotError.error (query qkv head) (key cache qkv layer position source head)
    Q K eq ek b.mulBound b.addBound 64 h.queryFinite h.keyFinite hQ hK
    h.mulLower h.mulUpper h.mulRange h.addUpper h.addRange
  rw [← dot_compute] at hd
  have hf : CodeLib.IEEE32.Finite 0x3E000000 := by
    change Wasm.IEEE32.isFinite 0x3E000000 = true
    decide
  have hv : value 0x3E000000 = (1 : ℝ) / 8 := by
    norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
      Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
  have hs := F32ErrorPropagation.mul (dotPrefix cache qkv layer position source head 64) 0x3E000000
    (∑ i ∈ Finset.range 64, Q i * K i) ((1 : ℝ) / 8) (dotError qkv head K eq ek b) 0 b.scaleBound
    hd.1 hf h.scaleLower h.scaleUpper h.scaleRange hd.2 (by rw [hv]; simp)
  rw [cachedScore_eq, ← F32Mul.mul_eq]
  simpa only [error, mul_zero, zero_add, mul_one_div, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] using hs

#print axioms score_error
end Project.Gpt2CachedStep.CachedScore.Error
