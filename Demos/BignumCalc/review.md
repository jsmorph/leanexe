# Reviews of the calculator

The reviews below were written when the library was developed in another repository.  This copy gives the present paths and names of the library and of the calculator, and the request and the design that the reviews cite stayed in that repository.

## Review of the bare-metal program

A fresh agent reviewed the message's specification, `Message.lean` with its definitions in full, and the statements of the equations, the bounds, and `Bare.lean`, with their proofs omitted, against the request for the bare-metal program and the message format that the report proposed, after writing its own reading of what the theorems must state.  It found that `calc_program` names the program that the build compares with `clightgen`'s reading, covers every sequence of input values and every length with the premise `PrefixOk` alone, excludes a trap through `InResultRoom`, and gives the premise `Reads` of leanexe's Rocq theorem; that `calcSpec` matches the names exactly, splits at single spaces, reads operands with the library's grammar, orders the statuses as the text exports do, answers 65,536 bytes and rejects 65,537, and writes `cmp` as the sign of the difference; that the corollaries' premises can hold; and that the room of `2^25` bytes and `main`'s allocation fit the 256 MiB of `lx_mem`.  It found no wrong program that `calc_program` accepts beyond `calcSpec`'s own choices.

| Finding | Response |
|---|---|
| An empty part where an operand belongs, as in `add  1`, `add  `, `add 1 `, or `neg `, gives the status of an operand outside the grammar, while the proposal named wrong separators among the causes of the status 4. | The tests include six such messages, and the report put the rule to the user, whose choice of the format names wrong separators among the causes of the status 4; an empty part now gives `4`, as the next review records. |
| A length above `inMax` gives no line and the status 64, and the input's layout was not stated. | The README states both. |
| The output records a number of words, so the line is recovered by dropping zeros, which needs a line without the byte 0. | `zero_not_mem_calcSpec` states it. |
| The corollaries cover the status 0 and the zero divisor, and the statuses 1, 2, and 4 follow from `calc_line` and `calcSpec`. | Kept; the README points to `calc_line`. |
| The premise on `inLen` is redundant in the three corollaries. | Removed: `inLen_le_of_msgMax` derives it from the message's length. |

## Review of the AArch64 Image

A fresh agent reviewed the statements of `BytesBare.lean` and `Image.lean`, with their proofs omitted, against the request for the Image, after writing its own reading: the kernel must compare the bytes of the file that QEMU boots with the generator's output, every theorem of runs must take the file's bytes as its premise on memory, the theorems must cover every record that the receiver can deliver with no trap, and the output must be `calcSpec`'s line.  It found that `output_eq` and `calc_runs` state this with the trap predicate `False` and the parameters of `calc_file_image`, that `calc_uart`, `calc_uart_over`, and `calc_uart_flag` together cover every record of the receiver, that `calc_fits` shows the premises on the base satisfiable at `imageBase`, and that the corollaries restate the specification's lemmas.

| Finding | Response |
|---|---|
| leanexe's `BytesRuns` does not state the number of bytes that the program reads, so an Image that waited for bytes after the message would meet the theorems. | The README states the gap and that the QEMU runs, whose inputs hold the length and the message alone, show that this Image stops. |
| The journal said that the Image's limit and the specification's agree, while a length above 65,536 gives the status 64 and `calcSpec` the line `4`. | Corrected. |
| No sentence stated that the three theorems of runs cover every record. | The README states the case split. |
| The README's count of eleven theorems did not name them. | It names the nine theorems of `Image.lean` and `output_eq` and `calc_runs`, which `image.sh` counts. |
| `calc_runs`'s docstring could be read as saying that the run with the status 0 writes nothing. | Reworded. |
| The project's root README named only the WebAssembly module. | Its paragraph names the C form, the bare-metal program, and the Image. |

A fresh agent then reviewed the revised `calcSpec`, which gives `4` for an empty part of the split, against the user's words for the format, case by case.  It found no message whose line contradicts the format, and it listed the choices that the definition makes where the format is silent: a tab or a newline belongs to the part that holds it, so `add 1 2\n` gives `2`; a byte above 127 in an operand gives `1` or `2`; a remainder by zero gives `3`, as the four divisions do; the line ends without a newline; and the faults are tested in the order length, separators, name, first operand, second operand, divisor.  The README states these choices.  It also noted that `calcSpec` writes the binary cases inline while `binaryOps` lists them for the corollaries, which `calcSpec_binary` ties together.
