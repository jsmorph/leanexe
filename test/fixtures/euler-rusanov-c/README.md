# Euler Rusanov C comparison fixtures

These programs are regression oracles for the frozen
`euler-rusanov-interface-v1` rows.  They are not formal evidence and are not
part of the exact-byte WebAssembly theorem.  The fixed-alpha program mirrors
the verified kernel closely enough to require bit equality.  The Lanyon
program deliberately computes a different, dynamic-speed flux and is only
reported side by side.

## Conservative build contract

Build both programs as separate translation units from the repository root:

```sh
mkdir -p build/tests/euler-rusanov-c
cc -std=c11 -O0 -Wall -Wextra -Wpedantic -Werror \
  -fno-fast-math -ffp-contract=off -frounding-math \
  -fno-associative-math -fno-reciprocal-math \
  -fno-finite-math-only -fno-unsafe-math-optimizations \
  -fexcess-precision=standard \
  test/fixtures/euler-rusanov-c/fixed-alpha-mirror.c -lm \
  -o build/tests/euler-rusanov-c/fixed-alpha-mirror
cc -std=c11 -O0 -Wall -Wextra -Wpedantic -Werror \
  -fno-fast-math -ffp-contract=off -frounding-math \
  -fno-associative-math -fno-reciprocal-math \
  -fno-finite-math-only -fno-unsafe-math-optimizations \
  -fexcess-precision=standard \
  test/fixtures/euler-rusanov-c/lanyon-driver.c -lm \
  -o build/tests/euler-rusanov-c/lanyon-driver
```

`-fno-fast-math` forbids algebraic reassociation assumptions,
`-ffp-contract=off` keeps multiplication and addition separate,
`-frounding-math` retains rounding-mode sensitivity, and
`-fexcess-precision=standard` prevents an extended intermediate format.
`-O0` makes the comparison build deliberately conservative.  Each local
mirror operation also materializes its result through a `volatile double`.

Both executables reject platforms that do not advertise IEC 60559 arithmetic
or the expected 64-bit, radix-two, 53-significand-bit format.  They set and
check `FE_TONEAREST`, require `FLT_EVAL_METHOD == 0`, and confirm that the
integer word `3ff0000000000000` has the platform's `double` layout for `1.0`
before evaluating a row.  Raw-word conversion in both directions uses
`memcpy`, never pointer punning.

## Fixed-alpha mirror CLI

Invoke the mirror with exactly six lowercase, fixed-width hexadecimal words:

```text
fixed-alpha-mirror rho_l_bits u_l_bits p_l_bits rho_r_bits u_r_bits p_r_bits
```

It first applies the literal unsigned-word guard from
`LeanExe.Examples.EulerRusanov.rusanovFluxCheckedBits`.  A rejected tuple
produces the exact zero payload without evaluating the numerical graph.  An
accepted tuple follows the same dyadic conservative conversion and the same
22-multiply, 27-add, three-sign-XOR fixed-`alpha = 7/4` graph.

Standard output is exactly one LF-terminated, comma-separated line:

```text
status_u64,mass_bits,momentum_bits,energy_bits
```

`status_u64` is minimal unsigned decimal.  The other fields are lowercase
fixed-width 16-hex words without `0x`.  Diagnostics go to standard error and a
CLI or platform error returns status 2.

## Pinned Lanyon driver CLI

The vendored upstream files live under
`lanyon/a736aa5f8b17efd225c4692404e2442361d06729/`.  The driver renames the
upstream placeholder `main` with a preprocessor macro and includes the exact
source; it does not patch that file.  `upstream.json` records the commit, tree,
Git blob identities, byte lengths, and SHA-256 digests.

The Lanyon driver has the same six-word primitive-state CLI.  Its adapter is
named `verified-dyadic-conservative-v1`: it constructs `(rho, momentum,
energy)` in the same dyadic operation order as the verified kernel, then calls
the pinned upstream physical-flux, speed-family, and left/right fluctuation
functions with C expression `7.0 / 5.0`.  On the supported host this is the
binary64 word `3ff6666666666666`, an approximation to the verified model's
exact real parameter `7/5`; the driver checks that word before calling the
upstream kernel.

The driver accepts only raw-guard-approved tuples.  It exits with status 2 and
does not pass a rejected tuple to the upstream floating-point code.  In
particular, the `nan_rejected` dataset row is never evaluated by Lanyon.

Standard output is exactly one LF-terminated line of 13 lowercase fixed-width
16-hex words, in this order:

```text
rho_l_bits,mom_l_bits,energy_l_bits,rho_r_bits,mom_r_bits,energy_r_bits,dynamic_alpha_bits,flux_from_left_mass_bits,flux_from_left_momentum_bits,flux_from_left_energy_bits,flux_from_right_mass_bits,flux_from_right_momentum_bits,flux_from_right_energy_bits
```

The two numerical-flux reconstructions are computed entirely in C as
`F_L + A^- delta-U` and `F_R - A^+ delta-U`, using the upstream fluctuation
functions.  They are both retained because their independently rounded words
can differ.  The reported positive dynamic speed is the upstream
`speed_family.speed2`.  No equality with the fixed-`7/4` verified kernel is
required or implied: upstream uses division, square root, `fabs`, and `fmax`.
The compiler and system `libm` are intentionally not proof inputs, so the
checked Lanyon words are a supported-host snapshot rather than portable
numerical truth.  `check` may report a changed snapshot on another otherwise
conforming compiler/libm combination; such a change requires review, not an
equivalence claim.

## Vendored identities

At the pinned commit, GitHub reports:

| Vendored file | Upstream Git blob | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `compressible_euler_1d.c` | `fbd70a9407d02ce2e49b6d6f37152c70ca679de4` | 27,229 | `f1f284f550d790c88f293e1d67a91434dc9b8c6187f88caed0f776c5039cf756` |
| `LICENSE` | `16b2ed3f9bee8eeb7bd7291ea6dfef76675b7e32` | 1,070 | `cfa90e3adf9a116fe3959a57353acdf5b6a783d3442d0e5a0834627990370116` |

The source's unusual trailing whitespace and missing final newline are part of
its pinned byte identity.  Verify the local copy without rewriting it:

```sh
git hash-object \
  test/fixtures/euler-rusanov-c/lanyon/a736aa5f8b17efd225c4692404e2442361d06729/compressible_euler_1d.c \
  test/fixtures/euler-rusanov-c/lanyon/a736aa5f8b17efd225c4692404e2442361d06729/LICENSE
sha256sum \
  test/fixtures/euler-rusanov-c/lanyon/a736aa5f8b17efd225c4692404e2442361d06729/compressible_euler_1d.c \
  test/fixtures/euler-rusanov-c/lanyon/a736aa5f8b17efd225c4692404e2442361d06729/LICENSE
```
