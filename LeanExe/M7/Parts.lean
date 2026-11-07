import LeanExe.M7.Boot

/-!
The kernel's check of a generated image in parts.  The memory of the kernel's evaluation of
`fileOk` or `bootFileOk` grows with the code that one declaration evaluates, and the check of the
gateway's whole image as one declaration exceeds 16 GiB.  These checks divide the image into
`main`, each function that calls reach from the step, and the trap stubs with `udivmod64`, and each
states one part's bytes as a slice of the number that `file_nat%` reads: the `len` bytes from byte
`off`, `n / 256 ^ off % 256 ^ len`.  A function's part takes the layout from the list `ns` of the
functions' sizes in units, so that its check evaluates the generator on that function alone, and
it checks that the function's size under the layout's table is its entry of `ns`.
`LeanExe/M7/Proof/Parts.lean` proves that parts whose checks pass give `fileOk` and `bootFileOk`,
so each part's check can be a declaration of its own.
-/

namespace LeanExe.M7

open Wasm LeanExe.CallGraph LeanExe.FileNat

/-- The generator's result `g` is code of `len` bytes, which are the bytes of the number `n` from
byte `off` in the order of `natOfBytes`. -/
def sliceOk (g : GenM (List Instr)) (n off len : Nat) : Bool :=
  match g with
  | .ok is =>
      (imageBytes is).length == len && natOfBytes (imageBytes is) == n / 256 ^ off % 256 ^ len
  | .error _ => false

/-- The functions that calls reach from function `k` of `m` with their indices, as `genProgram`
takes them, or none when `m` lacks one of them. -/
def reachedFns (m : Module) (k : Nat) : List (Nat × Function) :=
  match (reachFrom m k).mapM (funcOf m) with
  | .ok fs => fs
  | .error _ => []

/-- The entries of the functions of `fs` laid out one after another from `a` with the sizes `ns`
in units, as `entriesFrom` lays them out from their sizes. -/
def entriesOfSizes : UInt32 → List (Nat × Function) → List Nat →
    List (Nat × UInt32 × List ValueType × List ValueType)
  | a, (j, f) :: rest, n :: ns => (j, a, f.params, f.results) :: entriesOfSizes (after a n) rest ns
  | _, _, _ => []

/-- The part of the program of step `k` of `m` from the state `s0` at `base` that holds `main`,
at byte `off` of the number `n`: step `k` comes first among the functions that calls reach from
it, with `s0.length + 1` parameters and results of type `i64`, and `main`'s code for the entry
after `main` has `mainSize s0` instructions and the bytes of `n` from `off`. -/
def mainPartOk (m : Module) (k : Nat) (s0 : List UInt64) (base dev : UInt32) (n off : Nat) :
    Bool :=
  match (reachFrom m k).mapM (funcOf m) with
  | .ok (x :: _) =>
      x.1 == k && decide (x.2.params = List.replicate (s0.length + 1) .i64) &&
        decide (x.2.results = List.replicate (s0.length + 1) .i64) &&
        sliceOk (do
            let main ← genMain base (after base (mainSize s0)) dev s0
            if main.length = mainSize s0 then pure main else throw "main")
          n off (4 * mainSize s0)
  | _ => false

/-- The part of that program that holds function `i` of the functions that calls reach from step
`k`, laid out with the sizes `ns`: under the table of that layout, the function's size is its
entry of `ns`, and its code at its entry has the bytes of `n` that follow `main` and the functions
before it, from byte `off` on. -/
def functionPartOk (m : Module) (k : Nat) (s0 : List UInt64) (base limit : UInt32)
    (ns : List Nat) (n off i : Nat) : Bool :=
  let fs := reachedFns m k
  let first := after base (mainSize s0)
  let callee := tableOf (callTargets m k) (entriesOfSizes first fs ns)
  match fs[i]?, ns[i]? with
  | some x, some size =>
      functionSize (sigOf callee) x.2 == size &&
        sliceOk (genFunction callee (progShared (after first ns.sum) limit)
            (after first (ns.take i).sum) x.2)
          n (off + 4 * (mainSize s0 + (ns.take i).sum)) (4 * size)
  | _, _ => false

/-- The parts of the functions from `lo` up to `hi`. -/
def functionsPartOk (m : Module) (k : Nat) (s0 : List UInt64) (base limit : UInt32)
    (ns : List Nat) (n off lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (functionPartOk m k s0 base limit ns n off)

/-- The part of that program that holds the trap stubs and the code `div` of `udivmod64`, `len`
bytes of `n` after the functions. -/
def tailPartOk (s0 : List UInt64) (ns : List Nat) (div : List Instr) (n off len : Nat) : Bool :=
  sliceOk (pure ([.bTo (-4), .bTo (-4), .bTo (-4)] ++ div)) n (off + 4 * (mainSize s0 + ns.sum)) len

/-- The bytes of an image from reset before the program: the vector table, the self-loop, and the
initialization. -/
def bootHead (B : Boot) : List UInt8 :=
  (B.table.flatMap wordHalfs).flatMap halfBytes ++ imageBytes (.bTo (-4) :: B.init)

/-- The image's first bytes are those of `bootHead`. -/
def bootHeadOk (B : Boot) (n : Nat) : Bool :=
  natOfBytes (bootHead B) == n % 256 ^ (bootHead B).length

end LeanExe.M7
