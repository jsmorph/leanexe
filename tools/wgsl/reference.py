"""Finite binary32 reference arithmetic using integer/rational nearest-even rounding.

This executable reference is test evidence, not the Lean floating-point model.
"""

from fractions import Fraction
import struct

SIGN = 0x80000000
STRICT_PROFILE = "leanexe-f32-rne-separate-v1"
FUSION_PROFILE = "leanexe-f32-rne-fusion-v1"
PROFILES = (STRICT_PROFILE, FUSION_PROFILE)


def rational(word):
    """Decode a finite binary32 bit pattern exactly (zero sign is separate)."""
    exponent = (word >> 23) & 255
    if exponent == 255:
        raise ValueError("reference domain excludes infinities and NaNs")
    significand = word & 0x7fffff
    if exponent:
        significand |= 1 << 23
    shift = max(exponent, 1) - 150
    result = Fraction(significand << max(shift, 0), 1 << max(-shift, 0))
    return -result if word & SIGN else result


def round_binary32(value, negative_zero=False):
    """Round an exact rational to binary32, preserving signed underflow to zero."""
    if not value:
        return SIGN if negative_zero else 0
    sign = SIGN if value < 0 else 0
    value = abs(value)
    numerator, denominator = value.numerator, value.denominator
    exponent = numerator.bit_length() - denominator.bit_length()
    below_power = (numerator < denominator << exponent) if exponent >= 0 else (numerator << -exponent < denominator)
    if below_power:
        exponent -= 1
    shift = max(exponent - 23, -149)
    scaled_n = numerator << max(-shift, 0)
    scaled_d = denominator << max(shift, 0)
    significand, remainder = divmod(scaled_n, scaled_d)
    if 2 * remainder > scaled_d or (2 * remainder == scaled_d and significand & 1):
        significand += 1
    if significand >= 1 << 24:
        significand >>= 1
        shift += 1
    if shift > 104:
        raise ValueError("reference domain excludes overflow")
    if significand < 1 << 23:
        return sign | significand
    return sign | ((shift + 150) << 23) | (significand - (1 << 23))


def multiply(a, b):
    return round_binary32(rational(a) * rational(b), bool((a ^ b) & SIGN))


def add(a, b):
    return round_binary32(rational(a) + rational(b), a == SIGN and b == SIGN)


def fused(a, b, accumulator):
    product = rational(a) * rational(b)
    negative_zero = not product and bool((a ^ b) & SIGN) and accumulator == SIGN
    return round_binary32(product + rational(accumulator), negative_zero)


def gemm_results(a, b, rows, cols, inner, profile, max_choices=256, max_work=1000000):
    """All source-ordered results; fail if exhaustive fusion enumeration is too large."""
    if profile not in PROFILES:
        raise ValueError("unknown numerical profile")
    if len(a) != rows * inner or len(b) != inner * cols:
        raise ValueError("input lengths do not match dimensions")
    outputs = []
    work = 0
    for row in range(rows):
        for col in range(cols):
            choices = {0}
            for k in range(inner):
                work += len(choices)
                if work > max_work:
                    raise ValueError("fusion reference exceeded exhaustive work limit")
                x, y = a[row * inner + k], b[k * cols + col]
                product = multiply(x, y)
                next_choices = {add(product, acc) for acc in choices}
                if profile == FUSION_PROFILE:
                    next_choices.update(fused(x, y, acc) for acc in choices)
                if len(next_choices) > max_choices:
                    raise ValueError("fusion reference exceeded exhaustive choice limit")
                choices = next_choices
            outputs.append(sorted(choices))
    return outputs


def deterministic_inputs(count, seed):
    """LCG bit patterns: mixed signs, normal values in [1/16, 16), and signed zero."""
    state = seed
    result = []
    for index in range(count):
        state = (1664525 * state + 1013904223) & 0xffffffff
        word = (state & SIGN) | ((123 + ((state >> 24) % 8)) << 23) | (state & 0x7fffff)
        if index % 17 == 0:
            word = state & SIGN
        result.append(word)
    return result


def words_to_bytes(words):
    return struct.pack("<" + "I" * len(words), *words)


def bytes_to_words(data):
    if len(data) % 4:
        raise ValueError("binary32 buffer size must be divisible by four")
    return list(struct.unpack("<" + "I" * (len(data) // 4), data))


def hex_words(words):
    return [f"{word:08x}" for word in words]
