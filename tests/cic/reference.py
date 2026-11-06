# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Computes the outputs of a CIC decimation filter over Python's integers, as a reference for
compiled programs that is independent of the Lean specification.

A filter of order N, decimation R, and differential delay M maps an input x, read as 0 before
time 0, to the outputs y(m) = (S^N x)(mR + R - 1), where (S x)(n) is the sum of x(n - i) over
i < RM.  Each output is the N-fold moving sum of length RM at the last input of a block of R
inputs, and an input of length T has the T // R outputs of its complete blocks.  The script
computes y from this definition, as a cascade of N integrators at the input rate, decimation
by R, and N combs of delay M at the output rate, with every register starting at 0, and as the
same cascade in 64-bit words that wrap, whose outputs it reads as two's complement.

`uv run tests/cic/reference.py [test]` runs the self-test that `self_test` describes.
`uv run tests/cic/reference.py outputs N R M x0 x1 ...` prints y(0), y(1), and so on in
decimal, one per line.  With `--hex`, it prints for each output the eight bytes, in
hexadecimal, that a program writing y(m) modulo 2^64 as a little-endian word would write.
"""

import argparse
import itertools
import random
from collections import deque

WIDTH = 64
MASK = (1 << WIDTH) - 1


def moving_sum(x, length):
    """(S x)(n), the sum of x(n - i) over i < length, with x read as 0 before time 0."""
    return [sum(x[max(0, n - length + 1):n + 1]) for n in range(len(x))]


def cic(order, decimation, delay, x):
    """The outputs by the definition: the order-fold moving sum of length decimation * delay,
    at the times m * decimation + decimation - 1."""
    s = list(x)
    for _ in range(order):
        s = moving_sum(s, decimation * delay)
    return s[decimation - 1::decimation]


def cascade(order, decimation, delay, x, width=None):
    """The outputs of the integrators, the decimation, and the combs, over the integers, or in
    words of `width` bits whose additions and subtractions wrap.  Each comb keeps its last
    `delay` inputs, oldest first."""
    reduce = (lambda v: v) if width is None else (lambda v: v & ((1 << width) - 1))
    integrators = [0] * order
    combs = [deque([0] * delay) for _ in range(order)]
    y = []
    for n, sample in enumerate(x):
        v = reduce(sample)
        for j in range(order):
            integrators[j] = reduce(integrators[j] + v)
            v = integrators[j]
        if n % decimation == decimation - 1:
            for line in combs:
                line.append(v)
                v = reduce(v - line.popleft())
            y.append(v)
    return y


def signed(word, width=WIDTH):
    """The two's-complement reading of a word."""
    return word - (1 << width) if word >> (width - 1) else word


def input_width(order, decimation, delay, width=WIDTH):
    """The widest two's-complement input, in bits, whose register width by Hogenauer, the input
    width plus ceil(N log2(RM)), does not exceed `width`.  E. B. Hogenauer, "An economical class
    of digital filters for decimation and interpolation," IEEE Transactions on Acoustics,
    Speech, and Signal Processing 29(2), 1981, https://doi.org/10.1109/TASSP.1981.1163535."""
    return width - ((decimation * delay) ** order - 1).bit_length()


def integrator_range(order, x):
    """The least and greatest values that the integrators hold over the integers."""
    integrators = [0] * order
    least = greatest = 0
    for sample in x:
        v = sample
        for j in range(order):
            integrators[j] += v
            v = integrators[j]
            least, greatest = min(least, v), max(greatest, v)
    return least, greatest


def fail(message):
    raise SystemExit(f'fail: {message}')


def compare(config, kind, x):
    """The exact outputs and the readings of the 64-bit cascade's words, after a check that the
    cascade over the integers gives the exact outputs and that each word is its exact output
    modulo 2^64."""
    y = cic(*config, x)
    if cascade(*config, x) != y:
        fail(f'N, R, M = {config}, {kind}: '
             'the cascade over the integers differs from the definition')
    words = cascade(*config, [s & MASK for s in x], WIDTH)
    if words != [v & MASK for v in y]:
        fail(f'N, R, M = {config}, {kind}: a word differs from its output modulo 2^64')
    return y, [signed(w) for w in words]


def wraps(least, greatest):
    """Whether a range of integers extends past the signed 64-bit range."""
    return least < -(1 << (WIDTH - 1)) or greatest >= 1 << (WIDTH - 1)


def self_test():
    """Compares the definition, the cascade over the integers, and the 64-bit cascade over a
    grid of N, R, and M, and exits with status 1 at the first difference.

    For each configuration, B is the widest input that Hogenauer's bound admits in 64 bits:
    B + ceil(N log2(RM)) <= 64.  The test checks that random inputs of B bits, constant inputs
    of -2^(B-1) and 2^(B-1) - 1, random choices between those extremes, and random 1-bit inputs
    with weights +1 and -1, entered as the words 1 and 2^64 - 1, give two's-complement readings
    equal to the exact outputs.  It checks that random inputs of 100 bits give words equal to
    the exact outputs modulo 2^64, and that a constant input of -2^B, one bit past the bound,
    gives a reading that differs from an exact output.  A run of 20,480 1-bit inputs at N = 5,
    R = 64, and M = 1 must make the integrators leave the signed 64-bit range and give exact
    readings."""
    rng = random.Random(1)
    orders = range(6)
    decimations = (1, 2, 3, 4, 5, 8, 16, 64)
    delays = (1, 2, 3)
    bounded_inputs = bounded_outputs = bounded_wraps = least_outputs = 0
    bit_inputs = bit_outputs = wide_inputs = witnesses = 0
    for config in itertools.product(orders, decimations, delays):
        order, decimation, delay = config
        b = input_width(*config)
        lo, hi = -(1 << (b - 1)), (1 << (b - 1)) - 1
        fill = order * (decimation * delay - 1)

        def length():
            return fill + 8 * decimation + rng.randrange(decimation)

        bounded = [[rng.randint(lo, hi) for _ in range(length())] for _ in range(4)]
        bounded += [[lo] * length(), [hi] * length(),
                    [rng.choice((lo, hi)) for _ in range(length())]]
        for x in bounded:
            y, readings = compare(config, f'{b}-bit input', x)
            if readings != y:
                fail(f'N, R, M = {config}: a reading differs from its output within the bound')
            bounded_inputs += 1
            bounded_outputs += len(y)
            bounded_wraps += wraps(*integrator_range(order, x))
            least_outputs += y.count(-(1 << (WIDTH - 1)))
        for p in (0.5, 0.875):
            x = [1 if rng.random() < p else -1 for _ in range(length())]
            y, readings = compare(config, '1-bit input', x)
            if readings != y:
                fail(f'N, R, M = {config}: a reading differs from its output for a 1-bit input')
            bit_inputs += 1
            bit_outputs += len(y)
        for _ in range(2):
            x = [rng.randint(-(1 << 99), (1 << 99) - 1) for _ in range(length())]
            compare(config, '100-bit input', x)
            wide_inputs += 1
        y, readings = compare(config, f'constant input of -2^{b}', [-(1 << b)] * length())
        if readings == y:
            fail(f'N, R, M = {config}: every reading equals its output for the input -2^{b}')
        witnesses += 1

    config, p, samples = (5, 64, 1), 0.875, 20480
    x = [1 if rng.random() < p else -1 for _ in range(samples)]
    y, readings = compare(config, 'long 1-bit input', x)
    if readings != y:
        fail(f'N, R, M = {config}: a reading differs from its output for the long 1-bit input')
    least, greatest = integrator_range(config[0], x)
    if not wraps(least, greatest):
        fail(f'N, R, M = {config}: the integrators stay within the signed 64-bit range')

    print(f'grid: N in {list(orders)}, R in {list(decimations)}, M in {list(delays)}, '
          f'{len(orders) * len(decimations) * len(delays)} configurations')
    print(f'within the bound: {bounded_inputs} inputs and {bounded_outputs} outputs agree in the '
          f'definition, the cascade, and the 64-bit readings')
    print(f'within the bound: integrators leave [-2^63, 2^63) in {bounded_wraps} inputs, '
          f'and {least_outputs} outputs equal -2^63')
    print(f'1-bit inputs as the words 1 and 2^64 - 1: {bit_inputs} inputs and '
          f'{bit_outputs} outputs agree')
    print(f'100-bit inputs: {wide_inputs} inputs give words equal to the outputs modulo 2^64')
    print(f'past the bound: a reading differs from its output for the constant input -2^B '
          f'in {witnesses} of {witnesses} configurations')
    print(f'long 1-bit input at N, R, M = {config}: {samples} samples and {len(y)} outputs agree, '
          f'and the integrators range from {least} to {greatest} over the integers')


def main():
    parser = argparse.ArgumentParser(description='Reference outputs of a CIC decimation filter.')
    commands = parser.add_subparsers(dest='command')
    commands.add_parser('test', help='run the self-test, the default command')
    outputs = commands.add_parser('outputs', help='print the outputs of the filter for an input')
    outputs.add_argument('order', type=int, metavar='N')
    outputs.add_argument('decimation', type=int, metavar='R')
    outputs.add_argument('delay', type=int, metavar='M')
    outputs.add_argument('x', type=int, nargs='*', help='the input samples from time 0')
    outputs.add_argument('--hex', action='store_true',
                         help='print each output modulo 2^64 as eight little-endian bytes '
                         'in hexadecimal')
    args = parser.parse_args()
    if args.command != 'outputs':
        self_test()
        return
    if args.order < 0 or args.decimation < 1 or args.delay < 1:
        outputs.error('N must be at least 0, and R and M at least 1')
    for v in cic(args.order, args.decimation, args.delay, args.x):
        print((v & MASK).to_bytes(8, 'little').hex() if args.hex else v)


main()
