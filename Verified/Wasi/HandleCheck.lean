import Verified.Wasi.Source

/-! The handle check of a command.  `Command.HandleCheck helpers marks command` holds when the
command opens and closes descriptors only in the shape that `reflect` gives `LeanExe.Wasi.withOpen`
and passes only marked variables at `.handle` positions and for the marked parameters of helpers.

`marks` marks the variables of the command's context that hold handles, by index, and `helpers`
holds the marks of the parameters of each effect function that the command may call, in the
order of their signatures.  A variable is marked when it is the handle of a bracket, when a `ret`
of the literal 3, `Handle.preopened`, binds it, or when it is a marked parameter of the function
whose body the check reads; every other binding, the components that `Command.letPair` binds
among them, gives an unmarked variable.  The literal may stand as the body of `Expr.letPair`
bindings: the reflector puts around an operand that is not a variable a `letPair` of each variable
of type `.pair` that the operand names and of each component of such a variable that is itself a
`.pair`.  The check refuses

1. a `sys` command whose call, or whose reporter in the form `reported`, is not one of the
   descriptions of `Call.table`, which `tools/wasi-calls.py` generates from the witx;
2. a `sys` command whose call or reporter is `fd_close`, `fd_renumber`, or `path_open`, except the
   open and the close of a bracket, which are `Call.pathOpen` and `Call.fdClose` of the table;
3. a `sys` command, the open of a bracket included, whose `.handle` position, the argument of a
   `handle` parameter or of a handle field of a `subscriptions` parameter, does not take a marked
   variable, or whose input variables do not match its `input` and `iovec true` parameters;
4. a call of a helper whose argument for a marked parameter is not a marked variable, or which
   marks more parameters than it has.

A bracket is a `bind` whose first command is the open, `Call.pathOpen` in the form `.flat 1 false`
with one input, and whose second command has the shape that the docstring of
`LeanExe.Wasi.withOpen` shows.  The check reads the bracket in stages, one command at a time:
`opened` is the test of the errno, the first component of variable 0, against the word 0, with
the error continuation and the success branch; `success` binds the handle, the second component of
variable 0; `body` reads the body, which must have a result, with the handle marked; and `closing`
is the close, `Call.fdClose` in the form `.flat 0 false` of variable 1, the handle, followed by
`ret` of the pair, `mk` or `pair`, of the body's result and the close's errno, variables 1 and 0
after the close.  The check reads the error branch, the pair after the error continuation
included, as a command outside a bracket, so it does not fix the pair's second component.  A
command that differs from a stage's shape fails the check. -/

namespace Verified

variable {pureSigs : List Sig}

/-- Whether an expression is a variable that `marks` marks. -/
def Expr.markedVar (marks : List Bool) : Expr pureSigs context type → Bool
  | .var x => marks.getD x.index false
  | _ => false

def Path.isHere : Path e e' → Bool
  | .here => true
  | _ => false

/-- Whether the path is the first component of a pair, or with `first` false the second. -/
def Path.isPart (first : Bool) : Path e e' → Bool
  | .fst path => first && path.isHere
  | .snd path => !first && path.isHere
  | .here => false

/-- Whether the expression is the first component of variable 0, the errno of an open, or with
`first` false its second, the descriptor. -/
def Expr.isOpenedPart (first : Bool) : Expr pureSigs context type → Bool
  | .proj x path => x.index == 0 && path.isPart first
  | _ => false

/-- Whether the expression is the literal `word`. -/
def Expr.isWord (word : UInt64) : Expr pureSigs context type → Bool
  | .word value => value == word
  | _ => false

/-- Whether the expression is the literal 3, `Handle.preopened`, alone or as the body of `letPair`
bindings, which do not change its value. -/
def Expr.isPreopened : {context : List Ty} → {type : Ty} → Expr pureSigs context type → Bool
  | _, _, .word value => value == 3
  | _, _, .letPair _ body => body.isPreopened
  | _, _, _ => false

/-- Whether the expression is the variable with index `index`. -/
def Expr.isVar (index : Nat) : Expr pureSigs context type → Bool
  | .var x => x.index == index
  | _ => false

/-- Whether the expression is the pair of the variables with indices `first` and `second`, built
with `mk` or `pair`. -/
def Expr.isVarPair (first second : Nat) : Expr pureSigs context type → Bool
  | .mk left right => left.isVar first && right.isVar second
  | .pair left right => left.isVar first && right.isVar second
  | _ => false

/-- Whether the expression is the bracket's test: the errno of variable 0 differs from 0. -/
def Expr.isErrnoTest : Expr pureSigs context type → Bool
  | .cmp op left right => op == .ne && left.isOpenedPart true && right.isWord 0
  | _ => false

end Verified

namespace Verified.Wasi

open LeanExe.Wasi

variable {pureSigs : List Sig} {effectSigs : List EffectSig}

/-- The stage of a bracket at which the check reads a command, or `plain` outside the stages. -/
inductive Stage where
  | plain
  | opened
  | success
  | body
  | closing
  deriving DecidableEq

/-- The calls that only a bracket makes. -/
def bracketCallNames : List String := ["fd_close", "fd_renumber", "path_open"]

/-- Whether `indices` holds an index for each field of `fields`, in order, and each handle field
takes a variable whose index `marks` marks. -/
def fieldsMarked (marks : List Bool) : List Field → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | field :: fields, index :: indices =>
    (field.source != .handle || marks.getD index false) && fieldsMarked marks fields indices

/-- Whether each `.handle` position of `params` takes a variable whose index `marks` marks, among
the word arguments `indices`, which the parameters take in order, `Param.argWords` of each, and
the `subscriptions` parameters one for each field of `argFields`. -/
def handlesMarked (marks : List Bool) : List Param → List Nat → Bool
  | [], _ => true
  | param :: params, indices =>
    if param = .handle then
      match indices with
      | [] => false
      | index :: rest => marks.getD index false && handlesMarked marks params rest
    else
      match param with
      | .subscriptions records =>
        fieldsMarked marks (argFields records) indices &&
          handlesMarked marks params (indices.drop (argFields records).length)
      | _ => handlesMarked marks params (indices.drop param.argWords)

/-- Whether a `sys` command of `call` in `form` with the word arguments `args`, `inputs` input
variables, and `buffers` buffer variables passes the check outside a bracket.  The call is one of
the generated descriptions of `Call.table`, and so is its reporter when the form is `reported`, so
that the call's `.handle` positions are the descriptor parameters of the witx whatever source
produced the command. -/
def sysMarked (marks : List Bool) (call : Call) (form : SysForm) (args : List Nat)
    (inputs buffers : Nat) : Bool :=
  Call.table.contains call && (form != .reported || Call.table.contains call.reporterCall) &&
    !bracketCallNames.contains call.name && !bracketCallNames.contains call.reporterCall.name &&
    handlesMarked marks call.params args && inputs == call.inputCount &&
    buffers == call.bufferCount

/-- The marks of the context that a `bind` gives its second command: `mark` for the variable that
the first command's value binds, if it binds one, before `marks`. -/
def ResultTy.marks : ResultTy → Bool → List Bool → List Bool
  | .unit, _, marks => marks
  | .value _, mark, marks => mark :: marks

/-- Whether a command with this result has a value, which a `bind` binds to a variable. -/
def ResultTy.hasValue : ResultTy → Bool
  | .unit => false
  | .value _ => true

/-- Whether the command is `ret` of the literal 3, alone or under `letPair` bindings, which binds
`Handle.preopened`. -/
def Command.preopened : Command pureSigs effectSigs context result → Bool
  | .ret value => value.isPreopened
  | _ => false

/-- Whether the command is the open of a bracket: `Call.pathOpen` in the form `.flat 1 false` with
one input. -/
def Command.isOpen : Command pureSigs effectSigs context result → Bool
  | .sys operation form _ inputs buffers =>
    operation == Call.pathOpen && form == .flat 1 false && inputs.length == 1 &&
      buffers.isEmpty
  | _ => false

/-- Whether the `.handle` positions of a `sys` command take marked variables. -/
def Command.openMarked (marks : List Bool) : Command pureSigs effectSigs context result → Bool
  | .sys operation _ args _ _ => handlesMarked marks operation.params (args.map Var.index)
  | _ => false

/-- Whether the command is `ret` of the descriptor of the open, the binding of a bracket's handle.
-/
def Command.isHandleRet : Command pureSigs effectSigs context result → Bool
  | .ret value => value.isOpenedPart false
  | _ => false

/-- Whether the command is the close of a bracket: `Call.fdClose` in the form `.flat 0 false` of
variable 1, the handle after the body's result. -/
def Command.isClose : Command pureSigs effectSigs context result → Bool
  | .sys operation form args inputs buffers =>
    operation == Call.fdClose && form == .flat 0 false && inputs.isEmpty && buffers.isEmpty &&
      args.map Var.index == [1]
  | _ => false

/-- Whether the last command of a bracket returns the body's result with the close's errno: `ret`
of the pair of variable 1, the body's result, and variable 0, the errno. -/
def Command.returnsBody : Command pureSigs effectSigs context result → Bool
  | .ret value => value.isVarPair 1 0
  | _ => false

/-- The marks of the parameters of the helper `callee`, from the marks of the helpers in the order
of their signatures. -/
def EffectVar.marks : EffectVar signatures signature → List (List Bool) → List Bool
  | .here, marks => marks.headD []
  | .there callee, marks => callee.marks marks.tail

/-- The handle check of a command at a stage, whose context's handles `marks` marks, with the
helpers' marks `helpers`. -/
def Command.handleCheck (helpers : List (List Bool)) :
    {context : List Ty} → {result : ResultTy} → Stage → List Bool →
      Command pureSigs effectSigs context result → Bool
  | _, _, .plain, marks, .bind (intermediate := intermediate) first next =>
    if first.isOpen then
      first.openMarked marks && handleCheck helpers .opened (false :: marks) next
    else
      handleCheck helpers .plain marks first &&
        handleCheck helpers .plain (intermediate.marks first.preopened marks) next
  | _, _, .plain, marks, .ite _ yes no =>
    handleCheck helpers .plain marks yes && handleCheck helpers .plain marks no
  | _, _, .plain, marks, .call (signature := signature) callee args =>
    decide ((callee.marks helpers).length ≤ signature.params.length) &&
      (List.range signature.params.length).all fun index =>
        if bounded : index < signature.params.length then
          !(callee.marks helpers).getD index false || (args ⟨index, bounded⟩).markedVar marks
        else true
  | _, _, .plain, marks, .loop _ _ _ step =>
    handleCheck helpers .plain (false :: false :: marks) step
  | _, _, .plain, marks, .sys operation form args inputs buffers =>
    sysMarked marks operation form (args.map Var.index) inputs.length buffers.length
  | _, _, .plain, marks, .letPair _ body =>
    handleCheck helpers .plain (false :: false :: marks) body
  | _, _, .plain, _, .unit | _, _, .plain, _, .ret _ | _, _, .plain, _, .read _ _ _
  | _, _, .plain, _, .readAll _ | _, _, .plain, _, .write _ _ _ _ | _, _, .plain, _, .exit _ => true
  | _, _, .opened, marks, .ite condition yes no =>
    condition.isErrnoTest && handleCheck helpers .plain marks yes &&
      handleCheck helpers .success marks no
  | _, _, .success, marks, .bind first rest =>
    first.isHandleRet && handleCheck helpers .body (true :: marks) rest
  | _, _, .body, marks, .bind (intermediate := intermediate) body rest =>
    intermediate.hasValue && handleCheck helpers .plain marks body &&
      handleCheck helpers .closing (false :: marks) rest
  | _, _, .closing, _, .bind first tail => first.isClose && tail.returnsBody
  | _, _, _, _, _ => false

/-- A command passes the handle check. -/
def Command.HandleCheck (helpers : List (List Bool)) (marks : List Bool)
    (command : Command pureSigs effectSigs context result) : Prop :=
  command.handleCheck helpers .plain marks = true

/-- The handle check of a program: each function's body passes it with its own marks and the marks
of the functions after it as the helpers' marks.  `helpers` holds the marks of the functions in the
order of the program's signatures. -/
def EffectProg.handleCheck (helpers : List (List Bool)) :
    {effectSigs : List EffectSig} → EffectProg pureSigs effectSigs → Bool
  | _, .nil => true
  | _, .cons function rest =>
    function.body.handleCheck helpers.tail .plain (helpers.headD []) &&
      rest.handleCheck helpers.tail

/-- A program passes the handle check. -/
def EffectProg.HandleCheck (helpers : List (List Bool))
    (program : EffectProg pureSigs effectSigs) : Prop :=
  program.handleCheck helpers = true

end Verified.Wasi
