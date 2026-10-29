# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes the inputs of tests/native/bench.sh into the directory given as the argument.

The files hold little-endian 64-bit words from a fixed linear congruential sequence: 1 MiB of
words for the hashes, 4,096 words to sort, and the vectors and the matrix of GPT-2's width 768
as the bits of binary32 values in [-1, 1) in the low half of each word.
"""

import struct
import sys

state = 1


def word() -> int:
    global state
    state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
    return state


def floats(n: int) -> list[int]:
    return [struct.unpack("<I", struct.pack("<f", (word() >> 40) / 2**23 - 1.0))[0]
            for _ in range(n)]


def write(directory: str, name: str, words: list[int]) -> None:
    with open(f"{directory}/{name}", "wb") as f:
        f.write(b"".join(struct.pack("<Q", w) for w in words))


def main() -> None:
    d = sys.argv[1]
    write(d, "words-1m.bin", [word() for _ in range(131072)])
    write(d, "words-4k.bin", [word() for _ in range(4096)])
    write(d, "x-768.bin", floats(768))
    write(d, "g-768.bin", floats(768))
    write(d, "b-768.bin", floats(768))
    write(d, "w-768x768.bin", floats(768 * 768))


if __name__ == "__main__":
    main()
