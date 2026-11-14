import Verified.Source
import LeanExe.Wasi.Sys

/-! The forms of flat call that `Command.sys` compiles, with the result type and the action of
each.  A `flat` call takes word arguments and inputs, passes at most one output buffer, and returns
at most two result words, which the code places in the scratch area; its result holds the errno,
the result words, and the buffer's bytes when it has a buffer.  A `reported` call writes two regions
whose sizes its reporter returns: the code runs the reporter, tests the sizes, and runs the call,
and the result holds the errno, the reporter's two words, and the bytes of the shown region.  A
`record` call takes word arguments and inputs and writes one record into a block that the code
allocates and releases; its result holds the errno and one word for each of the record's fields.

An `iovecRead` call reads into a fresh buffer of the capacity that its argument gives, through an
array of one iovec, and its result holds the errno and the bytes read: the prefix of the buffer
whose length is the reply's count, clamped to the capacity.  An `iovecWrite` call writes the bytes
of its input through an array of one ciovec, and its result holds the errno and the count written.
A `poll` call is a `poll_oneoff` of the subscriptions that its description fixes, and its result
holds the errno, the number of events, and the fields of the first event.
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
  | .flat words true => wordsBytesTy (words + 1)
  | .reported => wordsBytesTy 3
  | .record fields => .elem (wordsElem fields)
  | .iovecRead => wordsBytesTy 1
  | .iovecWrite => .elem (wordsElem 1)
  | .poll => .elem (wordsElem 6)

/-- The result of a form from its words, the errno first, and its bytes. -/
def SysForm.value : (form : SysForm) → List UInt64 → LeanExe.Bytes → form.ty.denote
  | .flat words false, values, _ => wordsValue words values
  | .flat words true, values, bytes => wordsBytesValue (words + 1) values bytes
  | .reported, values, bytes => wordsBytesValue 3 values bytes
  | .record fields, values, _ => wordsValue fields values
  | .iovecRead, values, bytes => wordsBytesValue 1 values bytes
  | .iovecWrite, values, _ => wordsValue 1 values
  | .poll, values, _ => wordsValue 6 values

/-- The i64 locals that the code of a `sys` command uses from its base: six for a flat, reported,
or iovec call, for a record call the errno, the block's root, the record pointer, and one for each
field, and for a `poll` call the errno, the block's root, the subscriptions' pointer, the number of
events, and the five fields of the first event. -/
def SysForm.width : SysForm → Nat
  | .record fields => fields + 3
  | .poll => 9
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
    | iovec shown =>
      cases shown <;> simp only [flatArgsWith, flatArgs, flatArgsWith_nil params]
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
alignment are positive, the block of `size + align - 1` bytes lies below `2^32`, and each field
lies inside the record with a width of 1, 2, 4, or 8 bytes. -/
def recordFits (size align : Nat) (fields : List (Nat × Nat)) : Bool :=
  decide (0 < size) && decide (0 < align) && decide (size + align ≤ 4294967296) &&
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
def iovecParams (shown offset : Bool) : List Param :=
  [.handle, .iovec shown] ++ (if offset then [.word64] else []) ++ [.result32]

/-- Whether the code compiles a `poll` call of `records`: there is at least one record, the
records fit, each field has a width of 1, 2, 4, or 8 bytes, and the block of the subscriptions and
the events, `80 n + 7` bytes for `n` records, lies below `2^32`. -/
def subscriptionsFit (records : List (List Field)) : Bool :=
  decide (0 < records.length) && recordsFit records &&
    records.all (fun fields => fields.all fun field =>
      field.width == 1 || field.width == 2 || field.width == 4 || field.width == 8) &&
    decide (80 * records.length + 8 ≤ 4294967296)

/-- Whether the parameter takes one word argument: each parameter that takes one argument, except
an input and `iovec true`, which take bytes. -/
def Param.takesWord : Param → Bool
  | .input | .iovec true => false
  | param => param.takesArg

/-- Whether the parameter takes bytes: an input or `iovec true`. -/
def Param.takesBytes : Param → Bool
  | .input | .iovec true => true
  | _ => false

/-- The number of word arguments that the parameter takes. -/
def Param.wordCount (param : Param) : Nat := if param.takesBytes then 0 else param.argCount

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
one output, and at most two result words; a record call has words, enums, flags, and inputs
followed by one record that `recordFits` admits; a reported call writes the argument pointers and
the argument bytes that `args_get` and `environ_get` write; an iovec call has the parameters of
`iovecParams`; and a `poll` call has subscriptions that `subscriptionsFit` admits and the result
word. -/
def compiled (call : Call) : Bool :=
  match call.reporter with
  | some _ => call.params == [.reported 4 4 false, .reported 1 1 true]
  | none =>
    match Verified.Wasi.recordOf call.params with
    | some (size, align, fields) =>
      call.params.getLast? == some (.record size align fields) &&
        call.params.dropLast.all Param.argKind && recordFits size align fields
    | none =>
      if call.params.contains (.iovec false) then
        call.params == iovecParams false false || call.params == iovecParams false true
      else if call.params.contains (.iovec true) then
        call.params == iovecParams true false || call.params == iovecParams true true
      else
        match subscriptionsOf call.params with
        | some records =>
          call.params == [.subscriptions records, .result32] && subscriptionsFit records
        | none => call.params.all Param.inputKind && decide (call.params.count .output ≤ 1) &&
            decide (call.params.countP Param.isResult ≤ 2)

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
  | .record fields, call, values =>
    .sys call (flatArgs call.params values) fun reply =>
      .pure (SysForm.value (.record fields) (reply.errno :: recordWords call.params reply) .empty)
  | .iovecRead, call, values =>
    .sys call (flatArgs call.params values) fun reply =>
      .pure (SysForm.value .iovecRead [reply.errno] (reply.prefixBytes 0 (reply.word 1)))
  | .iovecWrite, call, values =>
    .sys call (flatArgs call.params values) fun reply =>
      .pure (SysForm.value .iovecWrite [reply.errno, reply.word 0] .empty)
  | .poll, call, values =>
    .sys call (flatArgs call.params values) fun reply =>
      .pure (SysForm.value .poll (reply.errno :: pollWords reply) .empty)

/-- The action of a `sys` command of `call` in `form` on the words of its word variables and the
bytes of its input variables.  A reported call takes no inputs. -/
def SysForm.runWith : (form : SysForm) → LeanExe.Wasi.Call → List UInt64 → List LeanExe.Bytes →
    Action form.ty.denote
  | .flat words bytes, call, values, inputs =>
    .sys call (flatArgsWith call.params values inputs) fun reply =>
      .pure (SysForm.value (.flat words bytes) (reply.errno :: resultWords call.params reply 0)
        (resultBytes call.params reply 0))
  | .reported, call, values, _ => SysForm.run .reported call values
  | .record fields, call, values, inputs =>
    .sys call (flatArgsWith call.params values inputs) fun reply =>
      .pure (SysForm.value (.record fields) (reply.errno :: recordWords call.params reply) .empty)
  | .iovecRead, call, values, inputs =>
    .sys call (flatArgsWith call.params values inputs) fun reply =>
      .pure (SysForm.value .iovecRead [reply.errno] (reply.prefixBytes 0 (reply.word 1)))
  | .iovecWrite, call, values, inputs =>
    .sys call (flatArgsWith call.params values inputs) fun reply =>
      .pure (SysForm.value .iovecWrite [reply.errno, reply.word 0] .empty)
  | .poll, call, values, inputs =>
    .sys call (flatArgsWith call.params values inputs) fun reply =>
      .pure (SysForm.value .poll (reply.errno :: pollWords reply) .empty)

theorem SysForm.runWith_nil (form : SysForm) (call : LeanExe.Wasi.Call) (values : List UInt64) :
    form.runWith call values [] = form.run call values := by
  cases form with
  | flat words bytes => simp only [SysForm.runWith, SysForm.run, flatArgsWith_nil]
  | reported => rfl
  | record fields => simp only [SysForm.runWith, SysForm.run, flatArgsWith_nil]
  | iovecRead | iovecWrite | poll => simp only [SysForm.runWith, SysForm.run, flatArgsWith_nil]

end Verified.Wasi
