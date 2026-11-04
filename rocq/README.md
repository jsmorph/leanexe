# CompCert proof composition

[The composition proof](Clight2Asm.v) relates termination of the Clight program produced by
CompCert's `SimplExpr` and `SimplLocals` passes to the behavior of the assembly program produced
by the same CompCert compilation.  It composes CompCert 3.18's forward simulations.
LeanExe's [bare-metal proofs](../docs/native-bare-metal.md#the-program-level-theorem) establish
whole-program termination in a Lean copy of Clight.  Applying the Rocq theorem also trusts the
agreement of that copy with CompCert and the build's comparison with `clightgen`, as
[the translator design](../docs/native-translator.md#trust-argument-and-validation) explains.

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
that every Asm behavior is one of those terminations.  The
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
`sigma`, where `concat` joins the traces of all iterations, and that every Asm behavior is
bisimilar, by CompCert's `same_behaviors`, to one of those behaviors.  The proof builds the
reactive behavior of the Clight program by cofixpoint from the invariant, carries it to Asm by
the forward simulation, and obtains uniqueness from the determinacy of Asm and the values read.

## Checking the composition

[The checker](check.sh) requires `coqc` and a CompCert 3.18 source tree for AArch64 with its
proofs built.  The tree must contain `_CoqProject` and `driver/Compiler.vo`.  From the repository
root, the command is:

```sh
rocq/check.sh /path/to/CompCert
```

The checker obtains the load paths from that tree's `_CoqProject`, compiles the composition in
a temporary directory, and compares the printed assumptions of every theorem above with those of
CompCert's `transf_c_program_correct`.  It permits the additional
`ClassicalEpsilon.constructive_indefinite_description` used by CompCert's behavior argument.
An unexpected assumption causes failure.
