# CompCert proofs in Rocq

[The composition proof](Clight2Asm.v) relates termination of the Clight program produced by
CompCert's `SimplExpr` and `SimplLocals` passes to the behavior of the assembly program produced
by the same CompCert compilation.  It composes CompCert 3.18's forward simulations.
LeanExe's [bare-metal proofs](../docs/native-bare-metal.md#the-program-level-theorem) establish
whole-program termination in a Lean copy of Clight.  Applying the Rocq theorem also trusts the
agreement of that copy with CompCert and the build's comparison with `clightgen`, as
[the translator design](../docs/native-translator.md#trust-argument-and-validation) explains.

[The Clight evaluator](ClightEval.v) runs a Clight program in Rocq and is sound for the
big-step semantics from which the composition starts.
[The comparison script](../tests/native/clight-rocq.sh) checks, by computation in the Rocq
kernel, that the evaluator gives the output of the Lean copy on the programs of the differential
test.  Where `tests/native/clight.sh` compares the Lean copy with CompCert's reference
interpreter for C, the script compares its terminating runs with CompCert's Clight semantics.

## Theorems and premises

`clight2_bigstep_to_asm` takes these premises for programs `p`, `p1`, `p2`, and `tp`, trace `t`,
and result `r`:

```coq
SimplExpr.transl_program p = OK p1
SimplLocals.transf_program p1 = OK p2
transf_c_program p = OK tp
ClightBigstep.Clight2.bigstep_program_terminates p2 t r
```

It concludes `program_behaves (Asm.semantics tp) (Terminates t r)`: the assembly semantics has
the same terminating trace and result.  The assembly theorem states its conclusion in CompCert's Asm semantics.
The startup code, linker, machine, UART, and input-loading procedure have the assumptions
described in [Trusted base](../docs/trusted-base.md).

`clight2_bigstep_asm_unique` uses assembly determinacy to show that the termination is the only behavior
when the trace has no inputs.  `clight2_bigstep_asm_reads` assumes a Clight termination for every
sequence of values read by volatile loads.  It proves an Asm termination for each sequence and
that every Asm behavior that satisfies `int_loads`, described below, is one of those
terminations.  The
[bare-metal input procedure](../docs/native-bare-metal.md#arguments-not-fixed-in-advance)
applies that theorem to a message loaded into memory before execution.

`clight2_loop_to_asm` concerns a `main` that runs an initialization and then a loop forever.  It
takes the compilation premises above and, for every sequence `sigma` of values read by volatile
loads, two more:

```coq
loop_reacts p2 t0 (W sigma)
forall n, reads sigma (t0 ** windows (W sigma) n)
```

`loop_reacts` restates the Lean definition `LoopReacts` over CompCert's Clight: `main` runs the
initialization with the trace `t0`, and iteration `n` of the loop runs with the nonempty trace
`W sigma n` from a state of an invariant that every iteration preserves.  The theorem concludes
that the Asm program has the behavior `Reacts (t0 *** concat (W sigma) (NE sigma))` for every
`sigma`, where `concat` joins the traces of all iterations, and that every Asm behavior that
satisfies `int_loads` is bisimilar, by CompCert's `same_behaviors`, to one of those behaviors.
The proof builds the reactive behavior of the Clight program by cofixpoint from the invariant,
carries it to Asm by the forward simulation, and obtains uniqueness from the determinacy of Asm
and the values read.

## Integer loads and pointer width

`int_loads beh` holds when every volatile load of the behavior `beh` whose value has the type
`Tint` reads an integer:

```coq
Definition int_loads (beh: program_behavior) : Prop :=
  forall t chunk id ofs ev,
  behavior_prefix (t ** Event_vload chunk id ofs ev :: nil) beh ->
  eventval_type ev = Tint -> exists i, ev = EVint i.
```

CompCert's `ev_match_ptr` (`common/Events.v`) lets a volatile load of a chunk of type `Tptr`
read a pointer event `EVptr_global id ofs` for every public symbol `id`.  With 32-bit pointers,
as on ARMv7-M, `Tptr` is `Tint`, the type of the chunks `Mint32` and `Mint8unsigned`, so the Asm
program has behaviors in which such a load reads a pointer.  The Lean copy of Clight omits
`ev_match_ptr`, `reads sigma` requires `EVint` at every load, and no `sigma` describes those
behaviors.  The uniqueness halves of `clight2_bigstep_asm_reads` and `clight2_loop_to_asm`
therefore take `int_loads beh` as a premise, and `reads_int_loads` and `reacts_int_loads` prove
that every behavior their conclusions describe satisfies it, which makes it the weakest premise
on behaviors under which they hold.  A premise about the program would have to exclude pointer
events through the chunks of its volatile loads or through its public symbols, but the input
program and the controller load with `Mint8unsigned`, whose type is `Tint`, and `clightgen` makes
`main` public.  With 32-bit pointers, applying the theorems to a machine assumes that each of
its runs is a behavior with `int_loads`: a device returns bits, which the Asm semantics
represents as `EVint` and then `Vint`.

With 64-bit pointers `Tptr` is `Tlong`, and `int_loads_ptr64` proves `int_loads` of every
behavior from `Archi.ptr64 = true`.  The corollaries `clight2_bigstep_asm_reads_ptr64` and
`clight2_loop_to_asm_ptr64` take that equation in place of `int_loads` and conclude that every
Asm behavior is one of the terminations or bisimilar to one of the reactive behaviors.
`aarch64/Archi.v` defines `ptr64` as `true`, and `arm/Archi.v` defines it as `false`.

## The Clight evaluator

`run_program p fuel` runs the `main` of the Clight program `p` from its initial memory, and
`run p name args fuel` calls the function `name` with the arguments `args`.  Expressions
evaluate by structural recursion.  Statements and calls take fuel, which each statement and each
call consumes.  The result is `Done` with the trace and the result, `Stuck` when the evaluator
applies no rule, or `OutOfFuel`.  The semantics lets a volatile load return any value of its
type, and the evaluator takes the value from a parameter.  `run` and `run_program` pass
`world_vload`, which reads the value from the initial memory of `world_program`, the program in
which each volatile global is an ordinary global and the other globals have no initialization
data.  CompCert's reference interpreter starts its world from that memory.  The soundness
theorems hold for every choice of the values.

```coq
Theorem run_sound:
  forall p name args fuel t m v,
  run p name args fuel = Done (t, m, v) ->
  exists m0 b fd,
    Genv.init_mem p = Some m0 /\
    Genv.find_symbol (globalenv p) name = Some b /\
    Genv.find_funct_ptr (globalenv p) b = Some fd /\
    Clight2.eval_funcall (globalenv p) m0 fd args t m v.

Theorem run_program_sound:
  forall p fuel t r,
  run_program p fuel = Done (t, r) -> Clight2.bigstep_program_terminates p t r.
```

`exec_call_sound` states the soundness of the execution of statements and calls, from which
both follow.  CompCert decides permissions over a range of addresses with `Mem.range_perm_dec`,
which recurs on an opaque proof of well-foundedness, and defines `store_zeros` of the initial
memory by well-founded recursion, so `vm_compute` cannot reduce `Mem.load`, `Mem.store`,
`Mem.free`, `Mem.drop_perm`, or `Genv.init_mem`.  The module `MemExec` restates them with
decisions by structural recursion and proves each equal to CompCert's operation; `init_mem_eq`
states this of the initial memory.

The evaluator omits these rules of CompCert's semantics: bit-field accesses, assignment of a
struct or union, volatile accesses whose event value is a pointer, and external calls other than
built-in functions, `EF_vload`, and `EF_vstore`.  `ClightBigstep.v` has no rule for `Slabel` and
`Sgoto`.  A program that reaches an omitted rule is `Stuck`, and no theorem relates `Stuck` to
the semantics, so a `Stuck` result does not show that the program has no execution.

## Comparison with the Lean copy

`tests/native/clight-rocq.sh DIR TREE` takes a directory of C programs with their `.expected`
files, as `tests/native/clight.sh` leaves them under `build/native/clight/SEED`, and the
CompCert tree of the target for which the expected outputs were computed.  `clightgen` prints
each program as Clight in Coq, the form whose termination `clight2_bigstep_to_asm` assumes.
For each program, a lemma states that the output of [the printer](ClightPrint.v) equals the
lines of the `.expected` file, and `coqc` checks its proof, `vm_compute; reflexivity`.  The
printer gives the lines that `main` prints for a random program or a NaN program, and the
events and the exit code for a trace program or an input program, in the format of
`tests/TestSupport/Native/ClightDiff.lean`.  An agreement on a program that terminates is a
kernel-checked execution of CompCert's semantics with the output that the Lean copy computed.
An agreement on `UB` shows only that both evaluators are stuck.  The script reports each
difference with the lines that the evaluator computes.

## Checking the proofs

[The checker](check.sh) requires `coqc` and a CompCert 3.18 source tree with its proofs built,
configured for AArch64 (`aarch64-linux`) or for ARMv7-M (`armv7m-eabihf`).  The tree must
contain `_CoqProject`, `Makefile.config`, and `driver/Compiler.vo`.  From the repository root,
the command for either target is:

```sh
rocq/check.sh /path/to/CompCert
```

The checker obtains the load paths from that tree's `_CoqProject`, which select the back end
whose `Archi`, `Asm`, and `Asmgenproof` the composition uses, so the same files check against
each target.  It compiles the composition and the evaluator in a temporary directory and
compares the printed assumptions of every theorem above with those of CompCert's
`transf_c_program_correct`.  For the composition, it permits the additional
`ClassicalEpsilon.constructive_indefinite_description` used by CompCert's behavior argument.  An
unexpected assumption causes failure.  The last line of the output names the architecture and
model of the tree's `Makefile.config` and the value of `Archi.ptr64`, which Rocq computes: `true`
for AArch64, where the corollaries for 64-bit pointers apply, and `false` for ARMv7-M, where the
uniqueness theorems keep the premise `int_loads`.
