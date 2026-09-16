#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

/* SplitMix64: https://prng.di.unimi.it/splitmix64.c (public domain). */
static uint64_t next(uint64_t *state) {
  uint64_t z = (*state += UINT64_C(0x9e3779b97f4a7c15));
  z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
  return z ^ (z >> 31);
}

int main(int argc, char **argv) {
  if (argc != 4) return 2;
  uint64_t state = strtoull(argv[1], NULL, 10);
  uint64_t count = strtoull(argv[2], NULL, 10);
  uint64_t modulus = strtoull(argv[3], NULL, 10);
  if (modulus == 0) return 2;
  for (uint64_t i = 0; i < count; ++i) {
    if (printf("%" PRIu64 "\n", next(&state) % modulus) < 0) return 1;
  }
  return 0;
}
