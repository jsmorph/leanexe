# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Lists the input table of the CIC filter's arm64 Image, `TestSupport.A64.CicTable.input`, whose
filter has order N = 3, decimation R = 8, and differential delay M = 1, with signed 16-bit samples.

The table has 64 samples, which give 8 outputs, one at the last sample of each block of 8.  An
output reads the N(RM - 1) + 1 = 22 samples that end at its time.  Samples 0 to 23 hold -32768 and
samples 24 to 47 hold 32767, each for 24 samples, so that the input steps from the 0 before time 0
to the most negative sample and then to the most positive, and output 2, at time 23, and output 5,
at time 47, read 22 equal samples and equal (RM)^N = 512 times the extreme: -2^24 and 16,776,704.
Samples 48 to 63 are segments of 4 samples that alternate between 16384 and -16384, a square wave
of period RM = 8 with zero sum over each period.

`uv run tests/cic/table.py` prints the samples in decimal, separated by spaces, in the form that
`uv run tests/cic/reference.py outputs 3 8 1` takes.  `uv run tests/cic/table.py lean` prints the
table as the Lean literal of the samples' two's-complement words, four to a line.
"""

import sys

SAMPLES = [-32768] * 24 + [32767] * 24 + ([16384] * 4 + [-16384] * 4) * 2


def main():
    if sys.argv[1:] == []:
        print(' '.join(map(str, SAMPLES)))
    elif sys.argv[1:] == ['lean']:
        words = [f'0x{s & 0xFFFFFFFFFFFFFFFF:016X}' for s in SAMPLES]
        lines = [', '.join(words[i:i + 4]) for i in range(0, len(words), 4)]
        print('  #[' + ',\n    '.join(lines) + ']')
    else:
        raise SystemExit('usage: table.py [lean]')


main()
