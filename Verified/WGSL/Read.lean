import Verified.WGSL.Scalar

namespace Verified.WGSL

def Rep.readWord : Rep (.array .word) → Rep .word → Rep .word
  | .words index _, .word position => .word (.read index position)

def Rep.readBool : Rep (.array .bool) → Rep .word → Rep .bool
  | .bools index _, .word position => .bool (.ne (.read index position) (.const 0))

def Rep.readFloat32 : Rep (.array .float32) → Rep .word → Rep .float32
  | .floats32 index _, .word position => .float32 (.ofBits32 (.read index position))

theorem Rep.readWord_locals (array : Rep (.array .word)) (position : Rep .word) :
    (array.readWord position).locals = position.locals := by cases array; cases position; rfl

theorem Rep.readBool_locals (array : Rep (.array .bool)) (position : Rep .word) :
    (array.readBool position).locals = position.locals := by
  cases array; cases position
  simp [Rep.readBool, Rep.locals, LeanExe.WGSL.Source.Expr.denoteLocals]

theorem Rep.readFloat32_locals (array : Rep (.array .float32)) (position : Rep .word) :
    (array.readFloat32 position).locals = position.locals := by cases array; cases position; rfl

theorem boolArray_read (xs : Array Bool) (k : Nat) :
    ((xs.map boolWord)[k]! != 0) = xs[k]! := by
  by_cases hk : k < xs.size
  · rw [getElem!_pos (xs.map boolWord) k (by simpa using hk), getElem!_pos xs k hk]
    simp only [Array.getElem_map]
    cases xs[k] <;> decide +kernel
  · rw [getElem!_neg (xs.map boolWord) k (by simpa using hk), getElem!_neg xs k hk]
    rfl

variable {ctx : Context Γ} {base : Nat} {S : List Sig}

def Code.readWord (x : Var Γ (.array .word)) {position : Funs S → Verified.Env Γ → UInt64}
    (a : Code ctx base (t := .word) position) :
    Code ctx base (t := .word) (fun funs env => (env.get x)[(position funs env).toNat]!) :=
  a.contextMap _ ((ctx.get x).readWord a.result)
    (by rw [Rep.readWord_locals]; exact a.resultBound)
    (by
      intro funs env locals arrays agree hIndex
      have hArray := agree _ x
      cases hx : ctx.get x with
      | words index size =>
          simp only [hx, Rep.Holds] at hArray
          cases hi : a.result with
          | word e =>
              simp only [hi, Rep.Holds] at hIndex
              simp [Rep.readWord, Rep.Holds, LeanExe.WGSL.Source.Expr.denote, hArray.1, hIndex])

def Code.readBool (x : Var Γ (.array .bool)) {position : Funs S → Verified.Env Γ → UInt64}
    (a : Code ctx base (t := .word) position) :
    Code ctx base (t := .bool) (fun funs env => (env.get x)[(position funs env).toNat]!) :=
  a.contextMap _ ((ctx.get x).readBool a.result)
    (by rw [Rep.readBool_locals]; exact a.resultBound)
    (by
      intro funs env locals arrays agree hIndex
      have hArray := agree _ x
      cases hx : ctx.get x with
      | bools index size =>
          simp only [hx, Rep.Holds] at hArray
          cases hi : a.result with
          | word e =>
              simp only [hi, Rep.Holds] at hIndex
              simp [Rep.readBool, Rep.Holds, LeanExe.WGSL.Source.Expr.denote, hArray.1, hIndex,
                boolArray_read])

def Code.readFloat32 (x : Var Γ (.array .float32))
    {position : Funs S → Verified.Env Γ → UInt64} (a : Code ctx base (t := .word) position) :
    Code ctx base (t := .float32) (fun funs env => (env.get x)[(position funs env).toNat]!) :=
  a.contextMap _ ((ctx.get x).readFloat32 a.result)
    (by rw [Rep.readFloat32_locals]; exact a.resultBound)
    (by
      intro funs env locals arrays agree hIndex
      have hArray := agree _ x
      cases hx : ctx.get x with
      | floats32 index size =>
          simp only [hx, Rep.Holds] at hArray
          cases hi : a.result with
          | word e =>
              simp only [hi, Rep.Holds] at hIndex
              simp [Rep.readFloat32, Rep.Holds, LeanExe.WGSL.Source.Expr.denote, hArray.1, hIndex,
                LeanExe.WGSL.Source.getElem!_map_toBits32])

end Verified.WGSL
