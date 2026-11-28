module

public import Verified.Source
public import Verified.Wasi.ABI
public import LeanExe.Wasi.Sys

@[expose] public section

/-! The forms of flat call that `Command.sys` compiles, with the result type and the action of
each.  A `flat` call takes word arguments and inputs and returns at most two result words, which
the code places in the scratch area; its result holds the errno and the result words.  A `flat`
call with an output fills a window of a buffer that the command takes: the output's two word
arguments are the window's start and count, and the result holds the errno, the count of the
fill, and the buffer, as `FillResult.of` states.  A `reported` call writes two regions whose sizes
its reporter returns: the code runs the reporter, tests the sizes, and runs the call, and the
result holds the errno, the reporter's two words, and the bytes of the shown region.  A `record`
call takes word arguments and inputs and writes one record into the call area; its result holds
the errno and one word for each of the record's fields.

An `iovecRead` call reads into a window of a buffer that the command takes, through an array of
one iovec, and its result is a fill's, whose count is the reply's count clamped to the window's
length.  An `iovecWrite` call writes the bytes of a window of its input through an array of one
ciovec, and its result holds the errno and the count written.  A `poll` call is a `poll_oneoff` of
the subscriptions that its description fixes, and its result holds the errno, the number of
events, and the fields of the first event.

A command's word arguments hold two words, the start and the count, for each window: each
`output` and `iovec` parameter.  `lowerWords` and `lowerInputs` replace them by the window's length
and the window's bytes, which `flatArgsWith` turns into the call's arguments.
-/

namespace Verified.Wasi

open LeanExe.Wasi

inductive SysForm where
  | flat (words : Nat) (bytes : Bool)
  | reported
  | record (fields : Nat)
  | iovecRead
  | iovecWrite
  | poll
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
  | .flat _ true => wordsBytesTy 2
  | .reported => wordsBytesTy 3
  | .record fields => .elem (wordsElem fields)
  | .iovecRead => wordsBytesTy 2
  | .iovecWrite => .elem (wordsElem 1)
  | .poll => .elem (wordsElem 6)

/-- The result of a form from its words, the errno first, and its bytes. -/
def SysForm.value : (form : SysForm) → List UInt64 → LeanExe.Bytes → form.ty.denote
  | .flat words false, values, _ => wordsValue words values
  | .flat _ true, values, bytes => wordsBytesValue 2 values bytes
  | .reported, values, bytes => wordsBytesValue 3 values bytes
  | .record fields, values, _ => wordsValue fields values
  | .iovecRead, values, bytes => wordsBytesValue 2 values bytes
  | .iovecWrite, values, _ => wordsValue 1 values
  | .poll, values, _ => wordsValue 6 values

/-- The value of a fill's result: the errno, the count, and the buffer. -/
def fillValue (result : FillResult) : (wordsBytesTy 2).denote :=
  wordsBytesValue 2 [result.errno, result.count] result.buffer

/-- The i64 locals that the code of a `sys` command uses from its base: six for a flat, reported,
or iovec read call, eight for an iovec write, whose window takes two before the six, for a record
call the errno, the record pointer, and one for each field, and for a `poll` call the errno, the
subscriptions' pointer, the number of events, and the five fields of the first event. -/
def SysForm.width : SysForm → Nat
  | .record fields => fields + 2
  | .poll => 8
  | .iovecWrite => 8
  | _ => 6

/-- The offset and width of each field of an event of `poll_oneoff` that a `poll` result holds: the
userdata, the error, the type, and the `nbytes` and flags of `fd_readwrite`. -/
def eventFields : List (Nat × Nat) := [(0, 8), (8, 2), (10, 1), (16, 8), (24, 2)]

/-- The words of a `poll` result after the errno: the number of events, which is output 1, and the
fields of the first event, at the start of output 0. -/
def pollWords (reply : Reply) : List UInt64 :=
  reply.word 1 :: eventFields.map fun field => reply.field 0 field.1 field.2

/-- The arguments of a flat call from the words of its argument variables, in order.  A
`subscriptions` parameter takes a word for each field of `argFields`. -/
def flatArgs : List Param → List UInt64 → List Arg
  | [], _ => []
  | .word32 :: params, values
  | .handle :: params, values
  | .word64 :: params, values
  | .enum32 _ :: params, values
  | .flags32 _ :: params, values
  | .flags64 _ :: params, values => .word (values.headD 0) :: flatArgs params values.tail
  | .output :: params, values
  | .iovec false :: params, values => .space (values.headD 0) :: flatArgs params values.tail
  | .subscriptions records :: params, values =>
    (values.take (argFields records).length).map .word ++
      flatArgs params (values.drop (argFields records).length)
  | _ :: params, values => flatArgs params values

/-- The arguments of a flat call from the words of its word variables and the bytes of its input
variables, each in order.  An `input` or `iovec true` parameter takes the next input; with no input
left it takes no argument, as in `flatArgs`, so that `flatArgsWith params values []` is
`flatArgs params values`. -/
def flatArgsWith : List Param → List UInt64 → List LeanExe.Bytes → List Arg
  | [], _, _ => []
  | .input :: params, values, input :: inputs
  | .iovec true :: params, values, input :: inputs =>
    .bytes input :: flatArgsWith params values inputs
  | .word32 :: params, values, inputs
  | .handle :: params, values, inputs
  | .word64 :: params, values, inputs
  | .enum32 _ :: params, values, inputs
  | .flags32 _ :: params, values, inputs
  | .flags64 _ :: params, values, inputs =>
    .word (values.headD 0) :: flatArgsWith params values.tail inputs
  | .output :: params, values, inputs
  | .iovec false :: params, values, inputs =>
    .space (values.headD 0) :: flatArgsWith params values.tail inputs
  | .subscriptions records :: params, values, inputs =>
    (values.take (argFields records).length).map .word ++
      flatArgsWith params (values.drop (argFields records).length) inputs
  | _ :: params, values, inputs => flatArgsWith params values inputs

theorem flatArgsWith_nil : ∀ (params : List Param) (values : List UInt64),
    flatArgsWith params values [] = flatArgs params values
  | [], _ => rfl
  | param :: params, values => by
    cases param with
    | iovec isInput =>
      cases isInput <;> simp only [flatArgsWith, flatArgs, flatArgsWith_nil params]
    | _ => simp only [flatArgsWith, flatArgs, flatArgsWith_nil params]

/-- The result words of a reply whose outputs follow `params` from position `index`. -/
def resultWords : List Param → Reply → Nat → List UInt64
  | [], _, _ => []
  | .output :: params, reply, index => resultWords params reply (index + 1)
  | .result32 :: params, reply, index
  | .result64 :: params, reply, index => reply.word index :: resultWords params reply (index + 1)
  | .record .. :: params, reply, index => resultWords params reply (index + 1)
  | _ :: params, reply, index => resultWords params reply index

/-- The size, alignment, and fields of the first record parameter. -/
def recordOf : List Param → Option (Nat × Nat × List (Nat × Nat))
  | [] => none
  | .record size align fields :: _ => some (size, align, fields)
  | _ :: params => recordOf params

/-- The fields of a reply's record, which is its output 0, in the order of the record parameter of
`params`. -/
def recordWords (params : List Param) (reply : Reply) : List UInt64 :=
  match recordOf params with
  | some (_, _, fields) => fields.map fun field => reply.field 0 field.1 field.2
  | none => []

/-- The buffer of a reply whose outputs follow `params` from position `index`. -/
def resultBytes : List Param → Reply → Nat → LeanExe.Bytes
  | [], _, _ => LeanExe.Bytes.empty
  | .output :: _, reply, index => reply.bytes index
  | .result32 :: params, reply, index
  | .result64 :: params, reply, index
  | .record .. :: params, reply, index => resultBytes params reply (index + 1)
  | _ :: params, reply, index => resultBytes params reply index

/-- The count of a fill of a flat call with result words `words`: the first word clamped to the
window's `length`, or the length for a call without result words. -/
def fillCount (words : List UInt64) (length : UInt64) : UInt64 :=
  match words with
  | [] => length
  | word :: _ => min word length

end Verified.Wasi

namespace LeanExe.Wasi

def Param.isResult : Param → Bool
  | .result32 | .result64 => true
  | _ => false

/-- The parameters that a flat call without inputs may have. -/
def Param.flatKind : Param → Bool
  | .word32 | .handle | .word64 | .flags32 _ | .flags64 _ | .output | .result32 | .result64 =>
    true
  | .enum32 count => decide (count < 4294967296)
  | .input | .reported .. | .record .. | .iovec _ | .subscriptions _ => false

/-- The parameters that a flat call may have: the kinds of `flatKind` and inputs. -/
def Param.inputKind : Param → Bool
  | .input => true
  | param => param.flatKind

/-- The parameters that may precede a call's record: words, handles, enums, flags, and inputs. -/
def Param.argKind : Param → Bool
  | .word32 | .handle | .word64 | .flags32 _ | .flags64 _ | .input => true
  | .enum32 count => decide (count < 4294967296)
  | _ => false

/-- Whether the code compiles a record of `size` bytes at alignment `align`: the size and the
alignment are positive, and each field lies inside the record with a width of 1, 2, 4, or 8
bytes. -/
def recordFits (size align : Nat) (fields : List (Nat × Nat)) : Bool :=
  decide (0 < size) && decide (0 < align) &&
    fields.all fun field =>
      (field.2 == 1 || field.2 == 2 || field.2 == 4 || field.2 == 8) &&
        decide (field.1 + field.2 ≤ size)

/-- Whether the parameter is a `subscriptions` parameter. -/
def Param.isSubscriptions : Param → Bool
  | .subscriptions _ => true
  | _ => false

/-- The records of the first `subscriptions` parameter. -/
def subscriptionsOf : List Param → Option (List (List Field))
  | [] => none
  | .subscriptions records :: _ => some records
  | _ :: params => subscriptionsOf params

/-- The parameters of an iovec call that the code compiles: a handle, the iovec, a 64-bit word when
`offset` holds, and the result word. -/
def iovecParams (isInput offset : Bool) : List Param :=
  [.handle, .iovec isInput] ++ (if offset then [.word64] else []) ++ [.result32]

/-- Whether the code compiles a `poll` call of `records`: there is at least one record, the
records fit, and each field has a width of 1, 2, 4, or 8 bytes. -/
def subscriptionsFit (records : List (List Field)) : Bool :=
  decide (0 < records.length) && recordsFit records &&
    records.all (fun fields => fields.all fun field =>
      field.width == 1 || field.width == 2 || field.width == 4 || field.width == 8)

/-- Whether the record or the subscriptions and events of `call` fit the call area from its start:
a record of at most 160 bytes whose alignment divides the area's start, 16, and subscriptions and
events, 80 bytes for each record, of at most 160 bytes. -/
def callFits (call : Call) : Bool :=
  (match Verified.Wasi.recordOf call.params with
    | some (size, align, _) =>
      decide (size ≤ Verified.Wasi.ABI.callArea.2) && Verified.Wasi.ABI.callArea.1 % align == 0
    | none => true) &&
  (match subscriptionsOf call.params with
    | some records => decide (80 * records.length ≤ Verified.Wasi.ABI.callArea.2)
    | none => true)

/-- Whether the parameter takes one word argument: each parameter that takes one argument, except
an input and `iovec true`, which take bytes. -/
def Param.takesWord : Param → Bool
  | .input | .iovec true => false
  | param => param.takesArg

/-- Whether the parameter takes bytes: an input or `iovec true`. -/
def Param.takesBytes : Param → Bool
  | .input | .iovec true => true
  | _ => false

/-- Whether the parameter takes a buffer that the call fills: an output or `iovec false`. -/
def Param.takesBuffer : Param → Bool
  | .output | .iovec false => true
  | _ => false

/-- Whether the parameter is a window's: an output or an iovec. -/
def Param.isWindow : Param → Bool
  | .output | .iovec _ => true
  | _ => false

/-- The number of word arguments that the parameter takes after its window's words become the
window's length: one for an output and for `iovec false`. -/
def Param.wordCount (param : Param) : Nat := if param.takesBytes then 0 else param.argCount

/-- The number of word arguments of a command that the parameter takes: two, the start and the
count of the window, for an output and an iovec, none for an input, and `argCount` otherwise. -/
def Param.argWords : Param → Nat
  | .output | .iovec _ => 2
  | .input => 0
  | param => param.argCount

namespace Call

/-- The description of a call's reporter: two result words. -/
def reporterCall (call : Call) : Call :=
  { name := call.reporter.getD "", params := [.result32, .result32] }

/-- The number of arguments of a call. -/
def argCount (call : Call) : Nat := (call.params.map Param.argCount).sum

/-- The number of word arguments of a call. -/
def wordCount (call : Call) : Nat := (call.params.map Param.wordCount).sum

/-- The number of inputs of a call. -/
def inputCount (call : Call) : Nat := call.params.countP Param.takesBytes

/-- The number of word arguments of a `sys` command of the call. -/
def argWords (call : Call) : Nat := (call.params.map Param.argWords).sum

/-- The number of buffers of a `sys` command of the call. -/
def bufferCount (call : Call) : Nat := call.params.countP Param.takesBuffer

def form (call : Call) : Verified.Wasi.SysForm :=
  match call.reporter with
  | some _ => .reported
  | none =>
    match Verified.Wasi.recordOf call.params with
    | some (_, _, fields) => .record fields.length
    | none =>
      if call.params.contains (.iovec false) then .iovecRead
      else if call.params.contains (.iovec true) then .iovecWrite
      else if call.params.any Param.isSubscriptions then .poll
      else
        Verified.Wasi.SysForm.flat (call.params.countP Param.isResult)
          (call.params.contains .output)

/-- Whether `Command.sys` compiles the call: a flat call has flat parameters or inputs, at most
one output, and at most two result words, or one with an output; a record call has words, enums,
flags, and inputs followed by one record that `recordFits` admits and the call area holds; a
reported call writes the argument pointers and the argument bytes that `args_get` and
`environ_get` write; an iovec call has the parameters of `iovecParams`; and a `poll` call has
subscriptions that `subscriptionsFit` admits and the call area holds, and the result word. -/
def compiled (call : Call) : Bool :=
  match call.reporter with
  | some _ => call.params == [.reported 4 4 false, .reported 1 1 true]
  | none =>
    match Verified.Wasi.recordOf call.params with
    | some (size, align, fields) =>
      call.params.getLast? == some (.record size align fields) &&
        call.params.dropLast.all Param.argKind && recordFits size align fields &&
        callFits call
    | none =>
      if call.params.contains (.iovec false) then
        call.params == iovecParams false false || call.params == iovecParams false true
      else if call.params.contains (.iovec true) then
        call.params == iovecParams true false || call.params == iovecParams true true
      else
        match subscriptionsOf call.params with
        | some records =>
          call.params == [.subscriptions records, .result32] && subscriptionsFit records &&
            callFits call
        | none => call.params.all Param.inputKind && decide (call.params.count .output ≤ 1) &&
            decide (call.params.countP Param.isResult ≤
              (if call.params.contains .output then 1 else 2))

/-- The calls that a module must import for a `sys` command of `call`, in order of use. -/
def uses (call : Call) : List Call :=
  match call.reporter with
  | some _ => [call.reporterCall, call]
  | none => [call]

end Call

theorem wordCount_of_inputKind : ∀ {params : List Param}, params.all Param.inputKind = true →
    (params.map Param.wordCount).sum = params.countP Param.takesWord
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    rw [List.map_cons, List.sum_cons, List.countP_cons, wordCount_of_inputKind kinds.2]
    cases param <;> simp_all [Param.inputKind, Param.flatKind, Param.wordCount, Param.takesBytes,
      Param.argCount, Param.takesWord, Param.takesArg] <;> omega

theorem inputCount_of_inputKind : ∀ {params : List Param}, params.all Param.inputKind = true →
    params.countP Param.takesBytes = params.count .input
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    rw [List.countP_cons, List.count_cons, inputCount_of_inputKind kinds.2]
    cases param <;> simp_all [Param.inputKind, Param.flatKind, Param.takesBytes]

theorem argCount_of_inputKind : ∀ {params : List Param}, params.all Param.inputKind = true →
    (params.map Param.argCount).sum = params.countP Param.takesArg
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    rw [List.map_cons, List.sum_cons, List.countP_cons, argCount_of_inputKind kinds.2]
    cases param <;> simp_all [Param.inputKind, Param.flatKind, Param.argCount, Param.takesArg] <;>
      omega

theorem Call.wordCount_of_inputKind {call : Call} (kinds : call.params.all Param.inputKind = true) :
    call.wordCount = call.params.countP Param.takesWord :=
  LeanExe.Wasi.wordCount_of_inputKind kinds

theorem Call.inputCount_of_inputKind {call : Call}
    (kinds : call.params.all Param.inputKind = true) :
    call.inputCount = call.params.count .input :=
  LeanExe.Wasi.inputCount_of_inputKind kinds

theorem Call.argCount_of_inputKind {call : Call} (kinds : call.params.all Param.inputKind = true) :
    call.argCount = call.params.countP Param.takesArg :=
  LeanExe.Wasi.argCount_of_inputKind kinds

end LeanExe.Wasi

namespace Verified.Wasi

open LeanExe.Wasi

/-- The words of the call's arguments from the words of a command's word variables: the words
of each parameter in turn, with the start and the count of a window replaced by the length of the
window of the next of `buffers` for an output or `iovec false`, and dropped for `iovec true`, whose
window becomes an input. -/
def lowerWords : List Param → List UInt64 → List LeanExe.Bytes → List UInt64
  | [], _, _ => []
  | .output :: params, values, buffers | .iovec false :: params, values, buffers =>
    (buffers.headD .empty).windowLength (values.headD 0) (values.tail.headD 0) ::
      lowerWords params (values.drop 2) buffers.tail
  | .iovec true :: params, values, buffers => lowerWords params (values.drop 2) buffers
  | .word32 :: params, values, buffers
  | .handle :: params, values, buffers
  | .word64 :: params, values, buffers
  | .enum32 _ :: params, values, buffers
  | .flags32 _ :: params, values, buffers
  | .flags64 _ :: params, values, buffers =>
    values.headD 0 :: lowerWords params values.tail buffers
  | .subscriptions records :: params, values, buffers =>
    values.take (argFields records).length ++
      lowerWords params (values.drop (argFields records).length) buffers
  | _ :: params, values, buffers => lowerWords params values buffers

/-- The inputs of the call's arguments from a command's word variables and input variables: each
input, and for `iovec true` the window of the next input that its start and count name. -/
def lowerInputs : List Param → List UInt64 → List LeanExe.Bytes → List LeanExe.Bytes
  | [], _, _ => []
  | .iovec true :: params, values, inputs =>
    (inputs.headD .empty).range (values.headD 0) (values.tail.headD 0) ::
      lowerInputs params (values.drop 2) inputs.tail
  | .input :: params, values, inputs =>
    inputs.headD .empty :: lowerInputs params values inputs.tail
  | param :: params, values, inputs => lowerInputs params (values.drop param.argWords) inputs

/-- The start and the count of the first window that a buffer fills, from a command's word
variables. -/
def windowWords : List Param → List UInt64 → UInt64 × UInt64
  | [], _ => (0, 0)
  | .output :: _, values | .iovec false :: _, values => (values.headD 0, values.tail.headD 0)
  | param :: params, values => windowWords params (values.drop param.argWords)

/-- The arguments of a call from the words of a command's word variables, the bytes of its input
variables, and its buffers. -/
def sysArgs (params : List Param) (values : List UInt64) (inputs buffers : List LeanExe.Bytes) :
    List Arg :=
  flatArgsWith params (lowerWords params values buffers) (lowerInputs params values inputs)

/-- The result of a fill of a flat call from its reply: the window of `buffer` that the words name,
filled with the bytes of the output, and the count, the first result word clamped to the window's
length, or the length for a call without a result word. -/
def flatFill (params : List Param) (values : List UInt64) (buffer : LeanExe.Bytes) (reply : Reply) :
    FillResult :=
  FillResult.of buffer (windowWords params values).1 (windowWords params values).2 reply.errno
    (fillCount (resultWords params reply 0)
      (buffer.windowLength (windowWords params values).1 (windowWords params values).2))
    (resultBytes params reply 0)

/-- The result of a fill of a read through an iovec from its reply: the window filled with the
bytes of the buffer region, and the count that the host returns clamped to the window's length. -/
def readFill (params : List Param) (values : List UInt64) (buffer : LeanExe.Bytes) (reply : Reply) :
    FillResult :=
  FillResult.of buffer (windowWords params values).1 (windowWords params values).2 reply.errno
    (min (reply.word 1)
      (buffer.windowLength (windowWords params values).1 (windowWords params values).2))
    (reply.bytes 0)

/-- The action of a `sys` command of `call` in `form` on the words of its word variables, the
bytes of its input variables, and its buffers.  A reported call takes no arguments.  A fill
returns the first buffer with the window that `windowWords` names filled, as `FillResult.of`
states. -/
def SysForm.runWith : (form : SysForm) → LeanExe.Wasi.Call → List UInt64 → List LeanExe.Bytes →
    List LeanExe.Bytes → Action form.ty.denote
  | .flat words false, call, values, inputs, buffers =>
    .sys call (sysArgs call.params values inputs buffers) fun reply =>
      .pure (SysForm.value (.flat words false) (reply.errno :: resultWords call.params reply 0)
        .empty)
  | .flat _ true, call, values, inputs, buffers =>
    .sys call (sysArgs call.params values inputs buffers) fun reply =>
      .pure (fillValue (flatFill call.params values (buffers.headD .empty) reply))
  | .reported, call, _, _, _ =>
    .sys call.reporterCall [] fun sizes =>
      if sizes.errno != 0 then .pure (SysForm.value .reported [sizes.errno, 0, 0] .empty)
      else if 4294967296 ≤ sizes.word 1 + 4 * sizes.word 0 + 3 then
        .pure (SysForm.value .reported [61, 0, 0] .empty)
      else .sys call [] fun got =>
        if got.errno != 0 then .pure (SysForm.value .reported [got.errno, 0, 0] .empty)
        else .pure (SysForm.value .reported [0, sizes.word 0, sizes.word 1] (got.bytes 0))
  | .record fields, call, values, inputs, buffers =>
    .sys call (sysArgs call.params values inputs buffers) fun reply =>
      .pure (SysForm.value (.record fields) (reply.errno :: recordWords call.params reply) .empty)
  | .iovecRead, call, values, inputs, buffers =>
    .sys call (sysArgs call.params values inputs buffers) fun reply =>
      .pure (fillValue (readFill call.params values (buffers.headD .empty) reply))
  | .iovecWrite, call, values, inputs, buffers =>
    .sys call (sysArgs call.params values inputs buffers) fun reply =>
      .pure (SysForm.value .iovecWrite [reply.errno, reply.word 0] .empty)
  | .poll, call, values, inputs, buffers =>
    .sys call (sysArgs call.params values inputs buffers) fun reply =>
      .pure (SysForm.value .poll (reply.errno :: pollWords reply) .empty)

end Verified.Wasi
