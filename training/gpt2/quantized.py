import argparse
import json
from pathlib import Path
import struct

from reference import MANIFEST, ROOT, digest, load_model


MODEL_BYTES = 127_695_972
HEADER = struct.pack("<8s6I", b"LXQGPT2\0", 1, 32, MODEL_BYTES - 32, 1, 128, 0)
GROUPED_HEADER = struct.pack("<8s6I", b"LXQGPT2\0", 1, 32, MODEL_BYTES - 32, 2, 128, 0)


def model_tensors():
    yield "wte.weight", "i8", (50257, 768)
    yield "wte.scale", "f32", (50257,)
    yield "wpe.weight", "f32", (1024, 768)
    for layer in range(12):
        prefix = f"h.{layer}."
        for name in ("ln_1.weight", "ln_1.bias"):
            yield prefix + name, "f32", (768,)
        for name, output, input_ in (("attn.c_attn", 2304, 768), ("attn.c_proj", 768, 768)):
            yield prefix + name + ".weight", "i8", (output, input_)
            yield prefix + name + ".scale", "f32", (output,)
            yield prefix + name + ".bias", "f32", (output,)
        for name in ("ln_2.weight", "ln_2.bias"):
            yield prefix + name, "f32", (768,)
        for name, output, input_ in (("mlp.c_fc", 3072, 768), ("mlp.c_proj", 768, 3072)):
            yield prefix + name + ".weight", "i8", (output, input_)
            yield prefix + name + ".scale", "f32", (output,)
            yield prefix + name + ".bias", "f32", (output,)
    yield "ln_f.weight", "f32", (768,)
    yield "ln_f.bias", "f32", (768,)


def model_layout():
    import math

    offset = len(HEADER)
    records = []
    for name, dtype, shape in model_tensors():
        length = math.prod(shape) * (1 if dtype == "i8" else 4)
        records.append({"name": name, "dtype": dtype, "shape": list(shape),
                        "offset_bytes": offset, "byte_length": length})
        offset += length
    if offset != MODEL_BYTES:
        raise ValueError(f"Model layout has {offset} bytes, expected {MODEL_BYTES}")
    return records


def pack_f32(tensor):
    return tensor.detach().contiguous().numpy().astype("<f4").tobytes()


def quantize_rows(tensor):
    import torch

    if tensor.dtype != torch.float32 or tensor.ndim != 2:
        raise ValueError("Quantization requires a matrix of FP32 rows")
    if not torch.isfinite(tensor).all():
        raise ValueError("Quantization requires finite values")
    maximum = tensor.abs().amax(dim=1)
    scale = torch.where(maximum == 0, torch.ones_like(maximum),
                        (maximum / 127).clamp_min(2 ** -126))
    values = (tensor / scale[:, None]).clamp(-127, 127).round().to(torch.int8)
    return values, scale


def projection_reference(weights, input_, bias):
    import torch

    qw, sw = quantize_rows(weights)
    qx, sx = quantize_rows(input_)
    accumulators = qx.to(torch.int64) @ qw.to(torch.int64).T
    if (accumulators.abs() > input_.shape[1] * 127 ** 2).any():
        raise ValueError("Accumulator exceeds the specified range")
    result = accumulators.to(torch.float32) * (sx[:, None] * sw[None, :])
    if bias is not None:
        result = result + bias
    return qw, sw, qx, sx, accumulators, result


def export_model(model_dir, output, scheme="row"):
    import torch

    _, model = load_model(model_dir)
    output.mkdir(parents=True, exist_ok=True)
    records = model_layout()
    partial = output / "weights.bin.partial"
    scales = None
    with torch.inference_mode(), partial.open("wb") as stream:
        stream.write(GROUPED_HEADER if scheme == "group64" else HEADER)
        for record in records:
            name, dtype = record["name"], record["dtype"]
            if name.endswith(".scale"):
                if scales is None:
                    raise ValueError(f"Missing scales for {name}")
                tensor, scales = scales, None
            else:
                tensor = model.transformer.get_parameter(name).detach()
                if dtype == "i8":
                    if name != "wte.weight":
                        tensor = tensor.T
                    tensor, scales = quantize_rows(tensor)
                elif not torch.isfinite(tensor).all():
                    raise ValueError(f"Nonfinite parameter: {name}")
            if list(tensor.shape) != record["shape"] or stream.tell() != record["offset_bytes"]:
                raise ValueError(f"Tensor layout mismatch: {name}")
            data = tensor.contiguous().numpy().tobytes() if dtype == "i8" else pack_f32(tensor)
            if len(data) != record["byte_length"]:
                raise ValueError(f"Tensor byte length mismatch: {name}")
            stream.write(data)
    if partial.stat().st_size != MODEL_BYTES or scales is not None:
        raise ValueError("Incomplete quantized checkpoint")
    destination = output / "weights.bin"
    partial.replace(destination)
    record = {
        "format": "leanexe-gpt2-q8-v1", "schema": 1,
        "checkpoint_sha256": MANIFEST["files"]["model.safetensors"],
        "quantization": ("symmetric-rne-per-output-channel-and-activation-group64-v1" if scheme == "group64"
                         else "symmetric-rne-per-output-channel-and-input-row-v1"),
        "scheme": 2 if scheme == "group64" else 1,
        "range": [-127, 127], "scale_floor_f32_bits": "00800000",
        "matrix_order": "output-major", "byte_order": "little-endian",
        "header_bytes": len(HEADER), "model_bytes": MODEL_BYTES,
        "weights_sha256": digest(destination), "torch": torch.__version__,
        "tensors": records,
    }
    (output / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: value for key, value in record.items() if key != "tensors"}))


def export_kernels(model_dir, output):
    import torch

    tokenizer, model = load_model(model_dir)
    first = model.transformer.h[0]
    projections = {
        "qkv": (first.attn.c_attn, True),
        "feedforward_up": (first.mlp.c_fc, True),
        "feedforward_down": (first.mlp.c_proj, True),
        "vocabulary": (model.lm_head, False),
    }
    inputs = {}
    handles = []
    for name, (module, _) in projections.items():
        def capture(_module, arguments, name=name):
            inputs[name] = arguments[0].detach().reshape(1, -1).clone()
        handles.append(module.register_forward_pre_hook(capture))
    token = tokenizer.encode("Once")[0]
    with torch.inference_mode():
        model(torch.tensor([[token]]), use_cache=False)
    for handle in handles:
        handle.remove()
    output.mkdir(parents=True, exist_ok=True)
    records = []
    with torch.inference_mode():
        for name, (module, transpose) in projections.items():
            weights = (module.weight.T if transpose else module.weight).contiguous()
            input_ = inputs[name]
            bias = module.bias
            qw, sw, qx, sx, accumulators, result = projection_reference(weights, input_, bias)
            serial = torch.zeros((1, weights.shape[0]), dtype=torch.float32)
            for index in range(weights.shape[1]):
                serial = serial + input_[:, index:index + 1] * weights[None, :, index]
            if bias is not None:
                serial = serial + bias
            directory = output / name
            directory.mkdir(exist_ok=True)
            coefficient_bytes = qw.numpy().tobytes()
            scale_bytes = pack_f32(sw)
            bias_bytes = pack_f32(bias) if bias is not None else b""
            files = {
                "weights.bin": coefficient_bytes + scale_bytes + bias_bytes,
                "input.bin": pack_f32(input_),
                "quantized-input.bin": qx.numpy().tobytes(),
                "input-scales.bin": pack_f32(sx),
                "accumulators.bin": accumulators.numpy().astype("<i4").tobytes(),
                "quantized-output.bin": pack_f32(result),
                "fp32-input-major.bin": pack_f32(weights.T) + bias_bytes,
                "fp32-output-major.bin": pack_f32(weights) + bias_bytes,
                "fp32-serial-output.bin": pack_f32(serial),
            }
            for filename, data in files.items():
                (directory / filename).write_bytes(data)
            record = {
                "name": name, "input_token": token, "position": 0, "rows": 1,
                "input_width": weights.shape[1], "output_width": weights.shape[0],
                "weight_offset": 0, "scale_offset": len(coefficient_bytes),
                "bias_offset": len(coefficient_bytes) + len(scale_bytes),
                "with_bias": bias is not None,
                "weight_bytes": len(files["weights.bin"]),
                "fp32_weight_bytes": len(files["fp32-input-major.bin"]),
                "max_abs_difference": (result - serial).abs().max().item(),
                "rms_difference": (result - serial).square().mean().sqrt().item(),
                "files": {filename: digest(directory / filename) for filename in files},
            }
            (directory / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
            records.append(record)
    manifest = {
        "schema": 1, "checkpoint_sha256": MANIFEST["files"]["model.safetensors"],
        "torch": torch.__version__, "input_source": "FP32 PyTorch on the retained first token",
        "quantization": "symmetric-rne-per-output-channel-and-input-row-v1", "cases": records,
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest))


def main():
    parser = argparse.ArgumentParser(description="Export specified quantized GPT-2 weights and projection cases")
    parser.add_argument("command", choices=["export-kernels", "export-model"])
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--scheme", choices=["row", "group64"], default="row")
    args = parser.parse_args()
    if args.command == "export-model":
        directory = "quantized-group64" if args.scheme == "group64" else "quantized"
        export_model(args.model_dir, args.output or args.model_dir / directory, args.scheme)
    else:
        export_kernels(args.model_dir, args.output or args.model_dir / "quantized-kernels")


if __name__ == "__main__":
    main()
