# Quantized GPT-2 report: second-version review

Accept version two.  No remaining remarks.

Reviewed PDF: `paper/gpt2-quantized-report/main.pdf`, SHA-256 `dbf1e0bbc88fd783b98fe3b51199c9cfed4b5b32e83cf9b8a2d3b3a4cf15cc69`, 393,839 bytes, 20 pages.  Review date: 2026-09-24.  No Lean or inference run was performed.

## Exponent definition

For a finite binary32 word representing x, let M(x) be `Wasm.IEEE32.scaledMagnitude`.  `Interpreter/Wasm/IEEE32.lean:32` defines its integer representation, and `CodeLib/IEEE32/Roundoff.lean:17` decodes the real value by division by `2^149`.  Thus `|x| = M(x) / 2^149`.

`Project/ProofKit/F32DivisionBounds.lean:47` assumes finite operands, a nonzero denominator, `24 ≤ b ≤ 275`, and

```
M(x) * 2^149 ≤ M(s) * 2^b.
```

For positive s, the magnitude premise is equivalent to `|x/s| ≤ 2^(b−149)`.  It states the integer representation used by the checker.  The exponent b is therefore shifted by 149 relative to a bound stated in real units.

`F32DivisionBounds.lean:45` defines

```
εdiv(b) = 2^(b−24) / 2^149.
```

The theorem bounds the real division-rounding error by this expression.  At `b = 156`, the quotient bound is `2^7 = 128`, and `εdiv(156) = 2^132 / 2^149 = 2^-17`.

`QuantizedScalarError.lean:8` carries the same quotient premise into the reconstruction theorem.  `QuantizedRangeCertificate.lean:9` uses the measured rounded-quotient bound `127 + 2^-17`.  Its clipping allowance is at most `2^-17`, so adding division rounding gives the stated reconstruction allowance `s * (1/2 + 2^-16)`.

## Archive remarks

The exponent clarification at `sections/04-export.tex:16–27` addresses the missing notation definition.  Its displayed magnitude premise, equivalent real quotient bound, division-error formula, and `b = 156` derivation match the formal statements examined above.

`sections/05-accuracy.tex:14` replaces “The approved experiment” with “The experiment.”  The six trace times at `sections/06-runtime.tex:18–20` now use three decimal places, each correctly rounded from the recorded value.  Comparing the preserved version-one section sources with version two shows only these three requested revisions.

## Final PDF and metadata

Direct extraction from the final PDF succeeds.  Its title and 1,801-character abstract equal the submission metadata after whitespace normalization.  The author, classifications, comments, and related-paper fields remain consistent with the paper.  ASCII double hyphens remain present in the command options.  The PDF hash equals the refreshed build record.

Root inspected rendered page 8 and reported that the revised equations and layout are legible.  The first-version review continues to cover the unchanged theorem statements, numerical evidence, trust assumptions, inventory, and limitations.
