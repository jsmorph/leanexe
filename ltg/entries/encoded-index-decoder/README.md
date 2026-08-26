# Encoded optional-index decoder

Use `EncodedIndexDecoder.program_spec` when a checked `leanexe.option.encoded-index.v1` equality selects the complete six-top-level-instruction decoder region.  The outer branch maps encoded zero to zero, while the nonzero branch implements the compiler's saturating predecessor sequence through two consecutive scratch locals.  The final instruction writes the decoded word to the recorded destination local and continues from `resultFrame`.

The theorem accepts arbitrary combined-local roles, stores, environments, continuations, and postconditions.  Its frame premises require the two scratch locals and destination local to lie in the valid internal-local range, while the source premise fixes the encoded word read from the input local.  `resultFrame_params`, `resultFrame_locals_length`, `resultFrame_values`, and `resultFrame_decoded` expose the exact frame shape and destination value without reducing the nested local updates.

The compiler descriptor and certificate establish agreement between successful IR recognition and structured instruction emission.  The artifact consumer separately matches every opcode, branch body, constant, and local role against the decoded WASM, then generates a Lean equality between that exact interval and `EncodedIndexDecoder.program`.  A proof may use the generated equality and neutral ProofKit theorem without importing the compiler or trusting the sidecar.

The decoder theorem assumes the meaning of the encoded source word.  It proves neither that a preceding search produced the word nor that the decoded result names a valid array index.  Combine it with a search theorem such as `FixedArrayFindIdxEq.program_spec`, or with application facts about another producer, before using the destination as an index.
