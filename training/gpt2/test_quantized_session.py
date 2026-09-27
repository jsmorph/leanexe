import argparse
import struct
from pathlib import Path
from tempfile import TemporaryDirectory

from quantized_wasm import QuantizedModel


def validate(model, length=None):
    model.send(f"arg-ptr 0\narg-u64 {model.weight_bytes if length is None else length}\n"
               "call validateModel 1")
    return model.read("results", 1)[0]


def rejected_step(model, status, token=7454, position=None, cache_size=None,
                  cache_argument=None, extra_live=0):
    tokens = list(model.tokens)
    position = len(tokens) if position is None else position
    cache_size = model.cache_size if cache_size is None else cache_size
    cache_argument = f"arg-u64 {model.cache_pointer}" if cache_argument is None else cache_argument
    model.send(f"arg-ptr 0\narg-u64 {model.weight_bytes}\n{cache_argument}\n"
               f"arg-u64 {cache_size}\narg-u64 {token}\narg-u64 {position}\ncall cachedStep 5")
    assert model.read("results", 5) == [status, 0, 0, 0, 0]
    model.update_stats((2 if model.cache_pointer else 1) + extra_live)
    assert model.tokens == tokens


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("wasm", type=Path)
    parser.add_argument("weights", type=Path)
    args = parser.parse_args()
    source = args.weights.read_bytes()
    with QuantizedModel(args.wasm, args.weights) as model:
        for length in [0, 31, len(source) - 1, len(source) + 1]:
            assert validate(model, length) == 1
        for offset, value, status in [
            (0, b"!", 1),
            (8, struct.pack("<I", 2), 1),
            (20, struct.pack("<I", 3 - struct.unpack_from("<I", source, 20)[0]), 1),
            (28, struct.pack("<I", 1), 1),
            (32, b"\x80", 2),
            (38597408, struct.pack("<I", 0), 2),
            (38597408, struct.pack("<I", 0xBF800000), 2),
            (38798436, struct.pack("<I", 0x7F800000), 2),
        ]:
            model.send(f"write-bytes 0 {offset} {value.hex()}")
            assert validate(model) == status
            if status == 1:
                rejected_step(model, 1)
            model.send(f"write-bytes 0 {offset} {source[offset:offset + len(value)].hex()}")
        assert validate(model) == 0
        for token in [7454, 2402, 257]:
            model.step(token)
        rejected_step(model, 3, token=50257)
        rejected_step(model, 3, position=128)
        rejected_step(model, 3, cache_size=model.cache_size - 1)

        model.send(f"read-memory {model.cache_pointer} {model.cache_size}")
        original_cache = model.line("memory")
        invalid_cache = bytearray.fromhex(original_cache[2])
        invalid_cache[-4:] = struct.pack("<I", 0x7FC00000)
        with TemporaryDirectory(prefix="quantized-session-") as directory:
            cache_file = Path(directory) / "invalid-cache.bin"
            cache_file.write_bytes(invalid_cache)
            model.send(f"bytes-file 1 {cache_file}")
            rejected_step(model, 3, cache_argument="arg-ptr 1", extra_live=1)
        model.send("arg-ptr 1\ncall release 0")
        model.read("results", 0)
        model.update_stats(2)
        model.send(f"read-memory {model.cache_pointer} {model.cache_size}")
        assert model.line("memory") == original_cache
        for layer in [0, 5, 11]:
            offset = 41944164 + layer * 7145472
            size = 768 * 4
            model.send(f"write-bytes 0 {offset} " + (struct.pack("<I", 0x7F7FFFFF) * 768).hex())
            assert validate(model) == 0
            rejected_step(model, 4)
            model.send(f"read-memory {model.cache_pointer} {model.cache_size}")
            assert model.line("memory") == original_cache
            model.send(f"write-bytes 0 {offset} {source[offset:offset + size].hex()}")
        model.step(640)
        model.reset()
        assert model.stats[0] - model.stats[3] == 1
        model.step(7454)
    assert model.stats[0] == model.stats[3]
    assert model.process.poll() == 0
    print("Checked model validation, cached steps, failure cleanup, cache preservation, reset, and close")


if __name__ == "__main__":
    main()
