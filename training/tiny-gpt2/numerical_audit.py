import argparse
import hashlib
import json
import math
import struct
import subprocess
from decimal import Decimal, localcontext
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EPSILON = Decimal(1) / 100000


def word(value):
    return struct.unpack("<Q", struct.pack("<d", value))[0]


def number(bits):
    return struct.unpack("<d", struct.pack("<Q", bits))[0]


def pi():
    total = Decimal(0)
    for k in range(9):
        total += Decimal((-1)**k * math.factorial(6*k) * (13591409+545140134*k)) / Decimal(
            math.factorial(3*k) * math.factorial(k)**3 * 640320**(3*k))
    return Decimal(426880) * Decimal(10005).sqrt() / total


def real_gelu(x):
    z = 2 * (2/pi()).sqrt() * (x + Decimal(44715)/1000000*x**3)
    return x / (1 + (-z).exp())


def proposed_exp(x):
    if x < -64:
        return 0.0
    squarings = 0
    while x < -1:
        x /= 2
        squarings += 1
    result = 1/math.factorial(18)
    for k in range(17, -1, -1):
        result = result*x+1/math.factorial(k)
    for _ in range(squarings):
        result *= result
    return result


def proposed_gelu(x):
    a = abs(x)
    if a > 8:
        return x if x > 0 else 0.0
    factor = (a*a)*number(0x3FA6E4E26D4801F7)+1
    z = (factor*a)*number(0x3FF9884533D43651)
    e = proposed_exp(-z)
    return a/(1+e) if x >= 0 else (-a*e)/(1+e)


def approximation_samples():
    points = set(-i/4 for i in range(257))
    for x in [-64, -32, -16, -8, -4, -2, -1, 0]:
        points.add(math.nextafter(x, -math.inf))
        if x:
            points.add(math.nextafter(x, math.inf))
    points.update(-2.0**(-k) for k in [10, 52, 100, 1022, 1074])
    exp_errors = [(abs(Decimal.from_float(proposed_exp(x))-Decimal.from_float(x).exp()), x)
                  for x in points]
    gelu_points = set(i/32 for i in range(-256, 257))
    gelu_points.update([3.01, -3.01])
    for x in [-8, 8]:
        gelu_points.add(math.nextafter(x, -math.inf))
        gelu_points.add(math.nextafter(x, math.inf))
    gelu_errors = [(abs(Decimal.from_float(proposed_gelu(x))-real_gelu(Decimal.from_float(x))), x)
                   for x in gelu_points]
    exp_error, exp_x = max(exp_errors)
    gelu_error, gelu_x = max(gelu_errors)
    return {
        "status": "Proposed arithmetic, evaluated in Python binary64; numerical measurements",
        "exp_points": len(exp_errors), "exp_maximum_error": str(exp_error), "exp_witness": exp_x,
        "gelu_points": len(gelu_errors), "gelu_maximum_error": str(gelu_error), "gelu_witness": gelu_x,
    }


def cancellation_weights(bound):
    weights = [0.0]*2488
    weights[1140] = 3.01
    for j, sign in enumerate([1, -1, 1, -1]):
        weights[1148+j] = 3.0*sign
        weights[1180+j] = -9.019430618323202*sign
        weights[2480+j] = 10.0
        weights[1184+256*j] = 10.0*sign
    return [max(-bound, min(bound, value)) for value in weights]


def cancellation_reference(weights):
    a = Decimal.from_float(weights[1140])
    residual = Decimal.from_float(weights[1148])*real_gelu(a) + Decimal.from_float(weights[1180])
    output = 4*Decimal.from_float(weights[2480])*Decimal.from_float(weights[1184])
    return residual, output*residual/(residual**2+EPSILON).sqrt()


def cancellation_native(weights, activation=None):
    a = weights[1140]
    z = 2*math.sqrt(2/math.pi)*(a+0.044715*a*a*a)
    result = a/(1+math.exp(-z)) if activation is None else activation(a)
    residual = weights[1148]*result+weights[1180]
    normalized = residual/math.sqrt(residual*residual+float(EPSILON))
    return 4*weights[1184]*(weights[2480]*normalized)


def wasm_logits(wasm, weights):
    command = [str(ROOT/"build/tools/leanexe-wasmtime-host"), "call", str(wasm), "infer", "array-u64",
               "array-u64:"+",".join(str(word(x)) for x in weights), *["i64:0"]*4]
    result = subprocess.run(command, check=True, capture_output=True, text=True, timeout=30)
    words = json.loads(result.stdout)
    if len(words) != 256 or any(type(x) is not int or x < 0 or x >= 2**64 for x in words):
        raise ValueError("WASM inference returned an invalid 256-word array")
    values = [number(x) for x in words]
    if not all(map(math.isfinite, values)):
        raise ValueError("WASM inference returned a nonfinite logit")
    return values


def sensitivity(bound, length):
    lower = EPSILON.sqrt()
    norm = 2*bound/lower
    first_residual = 48*bound**3+3*bound
    expansion = 12*bound**2+bound
    second_residual = first_residual+8*bound*expansion+bound
    gelu_multiplier = 8*bound*norm*4*bound
    probability_multiplier = length*12*bound**2*4*bound*(1+4*bound*norm*4*8*bound)*norm*4*bound
    return {
        "context_length": length,
        "normalized_magnitude": str(3*bound),
        "projection_magnitude": str(12*bound**2),
        "score_spread": str(288*Decimal(2).sqrt()*bound**4),
        "first_residual_magnitude": str(first_residual),
        "expansion_magnitude": str(expansion),
        "second_residual_magnitude": str(second_residual),
        "real_logit_magnitude": str(expansion),
        "gelu_local_error_multiplier": str(gelu_multiplier),
        "softmax_coordinate_error_multiplier": str(probability_multiplier),
        "gelu_contribution_at_error_0_01": str(gelu_multiplier/100),
        "softmax_contribution_at_error_1e_16": str(probability_multiplier*Decimal("1e-16")),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=float, default=10.0)
    parser.add_argument("--wasm", type=Path, default=ROOT/"data/tiny-gpt2-v1/inference.wasm")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not math.isfinite(args.bound) or not 0 <= args.bound <= 10:
        parser.error("bound must be finite and in [0, 10]")
    with localcontext() as context:
        context.prec = 80
        weights = cancellation_weights(args.bound)
        residual, reference = cancellation_reference(weights)
        native = cancellation_native(weights)
        proposed = cancellation_native(weights, proposed_gelu)
        actual = wasm_logits(args.wasm, weights)
        if any(x != 0 for x in actual[1:]):
            raise ValueError("A zero vocabulary column produced a nonzero logit")
        record = {
            "format": "leanexe-tiny-gpt2-numerical-audit-v1",
            "bound": args.bound,
            "wasm_sha256": hashlib.sha256(args.wasm.read_bytes()).hexdigest(),
            "reference": "80-digit Decimal tanh-GELU formula on decoded binary64 weights",
            "cancellation_case": {
                "tokens": [0, 0, 0, 0],
                "nonzero_weight_words": {str(i): f"{word(x):016x}" for i, x in enumerate(weights) if x},
                "reference_residual": str(residual),
                "reference_logit": str(reference),
                "wasm_logit": actual[0],
                "wasm_absolute_error": str(abs(Decimal.from_float(actual[0])-reference)),
                "native_exp_logit": native,
                "native_exp_absolute_error": str(abs(Decimal.from_float(native)-reference)),
                "proposed_logit": proposed,
                "proposed_absolute_error": str(abs(Decimal.from_float(proposed)-reference)),
            },
            "approximation_samples": approximation_samples(),
            "sensitivity_scope": "Conservative real perturbation estimates. Binary64 roundoff is omitted. These are numerical calculations, not Lean certificates.",
            "sensitivity": [sensitivity(Decimal.from_float(args.bound), n) for n in [4, 64]],
        }
    output = json.dumps(record, indent=2)+"\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
