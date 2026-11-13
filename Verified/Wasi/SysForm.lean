import Verified.Source
import LeanExe.Wasi.Sys

/-! The forms of flat call that `Command.sys` compiles, with the result type and the action of
each.  A `flat` call takes word arguments and inputs, passes at most one output buffer, and returns
at most two result words, which the code places in the scratch area; its result holds the errno,
the result words, and the buffer's bytes when it has a buffer.  A `reported` call writes two regions
whose sizes its reporter returns: the code runs the reporter, tests the sizes, and runs the call,
and the result holds the errno, the reporter's two words, and the bytes of the shown region. -/

namespace Verified.Wasi

open LeanExe.Wasi

inductive SysForm where
  | flat (words : Nat) (bytes : Bool)
  | reported
  deriving DecidableEq, Repr

/-- `count + 1` words as nested products. -/
def wordsElem : Nat → Elem
  | 0 => .word
  | count + 1 => .prod .word (wordsElem count)

/-- `count` words followed by bytes, as nested pairs. -/
def wordsBytesTy : Nat → Ty
  | 0 => .bytes
  | count + 1 => .pair .word (wordsBytesTy count)

def wordsValue : (count : Nat) → List UInt64 → (wordsElem count).denote
  | 0, words => words.headD 0
  | count + 1, words => (words.headD 0, wordsValue count words.tail)

def wordsBytesValue : (count : Nat) → List UInt64 → LeanExe.Bytes → (wordsBytesTy count).denote
  | 0, _, bytes => bytes
  | count + 1, words, bytes => (words.headD 0, wordsBytesValue count words.tail bytes)

def SysForm.ty : SysForm → Ty
  | .flat words false => .elem (wordsElem words)
  | .flat words true => wordsBytesTy (words + 1)
  | .reported => wordsBytesTy 3

/-- The result of a form from its words, the errno first, and its bytes. -/
def SysForm.value : (form : SysForm) → List UInt64 → LeanExe.Bytes → form.ty.denote
  | .flat words false, values, _ => wordsValue words values
  | .flat words true, values, bytes => wordsBytesValue (words + 1) values bytes
  | .reported, values, bytes => wordsBytesValue 3 values bytes

/-- The arguments of a flat call from the words of its argument variables, in order. -/
def flatArgs : List Param → List UInt64 → List Arg
  | [], _ => []
  | .word32 :: params, values
  | .word64 :: params, values
  | .enum32 _ :: params, values
  | .flags32 _ :: params, values
  | .flags64 _ :: params, values => .word (values.headD 0) :: flatArgs params values.tail
  | .output :: params, values => .space (values.headD 0) :: flatArgs params values.tail
  | _ :: params, values => flatArgs params values

/-- The arguments of a flat call from the words of its word variables and the bytes of its input
variables, each in order.  An `input` parameter takes the next input; with no input left it takes
no argument, as in `flatArgs`, so that `flatArgsWith params values []` is `flatArgs params values`.
-/
def flatArgsWith : List Param → List UInt64 → List LeanExe.Bytes → List Arg
  | [], _, _ => []
  | .input :: params, values, input :: inputs => .bytes input :: flatArgsWith params values inputs
  | .word32 :: params, values, inputs
  | .word64 :: params, values, inputs
  | .enum32 _ :: params, values, inputs
  | .flags32 _ :: params, values, inputs
  | .flags64 _ :: params, values, inputs =>
    .word (values.headD 0) :: flatArgsWith params values.tail inputs
  | .output :: params, values, inputs =>
    .space (values.headD 0) :: flatArgsWith params values.tail inputs
  | _ :: params, values, inputs => flatArgsWith params values inputs

theorem flatArgsWith_nil : ∀ (params : List Param) (values : List UInt64),
    flatArgsWith params values [] = flatArgs params values
  | [], _ => rfl
  | param :: params, values => by
    cases param <;> simp only [flatArgsWith, flatArgs, flatArgsWith_nil params]

/-- The result words of a reply whose outputs follow `params` from position `index`. -/
def resultWords : List Param → Reply → Nat → List UInt64
  | [], _, _ => []
  | .output :: params, reply, index => resultWords params reply (index + 1)
  | .result32 :: params, reply, index
  | .result64 :: params, reply, index => reply.word index :: resultWords params reply (index + 1)
  | .record .. :: params, reply, index => resultWords params reply (index + 1)
  | _ :: params, reply, index => resultWords params reply index

/-- The buffer of a reply whose outputs follow `params` from position `index`. -/
def resultBytes : List Param → Reply → Nat → LeanExe.Bytes
  | [], _, _ => LeanExe.Bytes.empty
  | .output :: _, reply, index => reply.bytes index
  | .result32 :: params, reply, index
  | .result64 :: params, reply, index
  | .record .. :: params, reply, index => resultBytes params reply (index + 1)
  | _ :: params, reply, index => resultBytes params reply index

end Verified.Wasi

namespace LeanExe.Wasi

def Param.isResult : Param → Bool
  | .result32 | .result64 => true
  | _ => false

/-- The parameters that a flat call without inputs may have. -/
def Param.flatKind : Param → Bool
  | .word32 | .word64 | .flags32 _ | .flags64 _ | .output | .result32 | .result64 => true
  | .enum32 count => decide (count < 4294967296)
  | .input | .reported .. | .record .. => false

/-- The parameters that a flat call may have: the kinds of `flatKind` and inputs. -/
def Param.inputKind : Param → Bool
  | .input => true
  | param => param.flatKind

/-- Whether the parameter takes a word argument: each parameter that takes an argument, except an
input. -/
def Param.takesWord : Param → Bool
  | .input => false
  | param => param.takesArg

namespace Call

/-- The description of a call's reporter: two result words. -/
def reporterCall (call : Call) : Call :=
  { name := call.reporter.getD "", params := [.result32, .result32] }

def argCount (call : Call) : Nat := call.params.countP Param.takesArg

/-- The number of word arguments of a call. -/
def wordCount (call : Call) : Nat := call.params.countP Param.takesWord

/-- The number of inputs of a call. -/
def inputCount (call : Call) : Nat := call.params.count .input

def form (call : Call) : Verified.Wasi.SysForm :=
  match call.reporter with
  | some _ => .reported
  | none => Verified.Wasi.SysForm.flat (call.params.countP Param.isResult) (call.params.contains .output)

/-- Whether `Command.sys` compiles the call: a flat call has flat parameters or inputs, at most
one output, and at most two result words; a reported call writes the argument pointers and the
argument bytes that `args_get` and `environ_get` write. -/
def compiled (call : Call) : Bool :=
  match call.reporter with
  | some _ => call.params == [.reported 4 4 false, .reported 1 1 true]
  | none => call.params.all Param.inputKind && decide (call.params.count .output ≤ 1) &&
      decide (call.params.countP Param.isResult ≤ 2)

/-- The calls that a module must import for a `sys` command of `call`, in order of use. -/
def uses (call : Call) : List Call :=
  match call.reporter with
  | some _ => [call.reporterCall, call]
  | none => [call]

end Call

end LeanExe.Wasi

namespace Verified.Wasi

open LeanExe.Wasi

/-- The action of a `sys` command of `call` in `form` on the words of its argument variables. -/
def SysForm.run : (form : SysForm) → LeanExe.Wasi.Call → List UInt64 → Action form.ty.denote
  | .flat words bytes, call, values =>
    .sys call (flatArgs call.params values) fun reply =>
      .pure (SysForm.value (.flat words bytes) (reply.errno :: resultWords call.params reply 0)
        (resultBytes call.params reply 0))
  | .reported, call, _ =>
    .sys call.reporterCall [] fun sizes =>
      if sizes.errno != 0 then .pure (SysForm.value .reported [sizes.errno, 0, 0] .empty)
      else if 4294967296 ≤ sizes.word 1 + 4 * sizes.word 0 + 3 then
        .pure (SysForm.value .reported [61, 0, 0] .empty)
      else .sys call [] fun got =>
        if got.errno != 0 then .pure (SysForm.value .reported [got.errno, 0, 0] .empty)
        else .pure (SysForm.value .reported [0, sizes.word 0, sizes.word 1] (got.bytes 0))

/-- The action of a `sys` command of `call` in `form` on the words of its word variables and the
bytes of its input variables.  A reported call takes no inputs. -/
def SysForm.runWith : (form : SysForm) → LeanExe.Wasi.Call → List UInt64 → List LeanExe.Bytes →
    Action form.ty.denote
  | .flat words bytes, call, values, inputs =>
    .sys call (flatArgsWith call.params values inputs) fun reply =>
      .pure (SysForm.value (.flat words bytes) (reply.errno :: resultWords call.params reply 0)
        (resultBytes call.params reply 0))
  | .reported, call, values, _ => SysForm.run .reported call values

theorem SysForm.runWith_nil (form : SysForm) (call : LeanExe.Wasi.Call) (values : List UInt64) :
    form.runWith call values [] = form.run call values := by
  cases form with
  | flat words bytes => simp only [SysForm.runWith, SysForm.run, flatArgsWith_nil]
  | reported => rfl

end Verified.Wasi
