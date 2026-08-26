# Residual singleton specification normalization

Use this entry after a checked singleton-wrapper theorem has discharged artifact semantics and left equations about the generated formal result.  Unfold the expected function in the invalid-size branch and reduce the singleton branch through `Array.size_eq_one_iff`.  The technique concerns the residual theorem interface rather than a generated function body or local-frame layout.

The established starter uses `simp_all [FormalSpec.expected]` for the non-singleton branch.  For the singleton branch, it obtains `input = #[value]` from the size equation and then simplifies the expected definition.  The complete starter should receive a full artifact check before an agent session begins.

Earlier runs retained this method as a worked example when an agent spent time confirming an unchanged proof.  Direct acceptance later removed that unnecessary agent session for the checked counter-transfer wrapper motif.  A failed direct check returns the same starter to ordinary proof generation, preserving the technique and its diagnostic.
