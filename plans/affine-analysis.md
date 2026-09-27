# Transformer affine calculations

The [tiny model](tiny-transformer.md) needs dot products of widths two,
four, and eight.  Two-coordinate products form attention scores.  Four-
and eight-coordinate products form projection and feed-forward outputs.

## Operation order and error

Use a balanced binary tree of rounded products and additions, followed by
one rounded bias addition for an affine output.  The existing arithmetic
lemmas include multiplication underflow and separate every rounded
operation.  The generic F64Approximation rules compose these errors.

For decoded inputs x and coefficients w, a local theorem compares the
computed output to sum(x_i*w_i)+b.  Parameter and upstream-input errors
then enter through

```text
|sum(x_i*w_i)-sum(y_i*v_i)|
  <= sum(|w_i|*|x_i-y_i| + |y_i|*|w_i-v_i|).
```

This bound retains each coefficient's magnitude.  Uniform coordinate
bounds follow by summing the magnitudes.  The frozen checkpoint will supply
the weight bounds and certified intermediate ranges.

The first reusable numerical proof will accept input magnitudes at most
64 and coefficient magnitudes at most 16.  Each product then has magnitude
at most 1024.  A rounded two-term sum has error at most 4097 times 2^-52
and magnitude at most 2050.  Four-term and eight-term bounds follow from
two more addition levels.  These limits leave every operation far below
overflow and include zero and subnormal values.

## Work

- [x] Prove real input and coefficient perturbation bounds.
- [x] Prove the bounded binary64 dot and affine calculations.
- [ ] Connect these calculations to generated-WAT execution in the model.

The checked four-term and eight-term dot bounds are 12294 and 32790 times
2^-52.  Affine outputs, including a bias of magnitude at most sixteen,
have absolute error at most 1/10000000000.  These source numerical theorems
still require an execution theorem when used by a compiled model.
