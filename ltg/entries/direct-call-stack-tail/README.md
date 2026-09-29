# Direct calls with retained stack operands

`Wasm.TerminatesWith.append_args` extends a callee theorem on `args` to a call on `args ++ rest`.  Its postcondition supplies the results `out`, the equation `values = out ++ rest`, and the callee's postcondition on `out`, and it keeps the callee's termination bound and store relation.  `Wasm.wp_call_tw` then composes the extended theorem with the caller's continuation, given the internal-function lookup and the exact argument count.

Operand lists put the top of the stack first, so `rest` is the part of the stack under the arguments.  `Triple` quantifies over every operand stack under a statement's code, so the rule for an IR call statement must hold for any `rest`.  State a runtime function's specification on its arguments alone, and extend it with `append_args` at the call.
