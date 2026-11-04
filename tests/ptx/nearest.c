/* Checks cvt.rni.f32.f32 followed by the replacement of a NaN by 0x7fc00000, the sequence that the
   PTX translation emits for the source operation nearest, against C's nearbyintf on every binary32
   input.

   ptx-nearest [CHUNK_BITS]

   The kernel runs on device 0 in chunks of 2^CHUNK_BITS inputs (default 26).  The host computes
   nearbyintf under the default rounding mode, round to nearest with ties to even, replaces a NaN
   result by 0x7fc00000, and compares each output word.  The program prints the device, the number
   of inputs and of mismatches, and the first mismatches, and ends with status 1 when there is a
   mismatch.  Any error ends the process with a message on standard error. */

#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <cuda.h>

static const char *kernel =
    ".version 7.0\n"
    ".target sm_80\n"
    ".address_size 64\n"
    ".visible .entry nearest(.param .u64 out, .param .u32 base) {\n"
    "  .reg .b32 %w<5>;\n"
    "  .reg .b64 %d<3>;\n"
    "  .reg .f32 %f<2>;\n"
    "  .reg .pred %p<1>;\n"
    "  mov.u32 %w0, %ctaid.x;\n"
    "  mov.u32 %w1, %ntid.x;\n"
    "  mov.u32 %w2, %tid.x;\n"
    "  mad.lo.u32 %w3, %w0, %w1, %w2;\n"
    "  ld.param.u32 %w4, [base];\n"
    "  add.u32 %w4, %w4, %w3;\n"
    "  mov.b32 %f0, %w4;\n"
    "  cvt.rni.f32.f32 %f1, %f0;\n"
    "  testp.notanumber.f32 %p0, %f1;\n"
    "  selp.b32 %f1, 0x7fc00000, %f1, %p0;\n"
    "  mov.b32 %w4, %f1;\n"
    "  ld.param.u64 %d0, [out];\n"
    "  cvta.to.global.u64 %d0, %d0;\n"
    "  mul.wide.u32 %d1, %w3, 4;\n"
    "  add.u64 %d2, %d0, %d1;\n"
    "  st.global.u32 [%d2], %w4;\n"
    "  ret;\n"
    "}\n";

static void check(CUresult result, const char *call) {
  if (result != CUDA_SUCCESS) {
    const char *text = NULL;
    cuGetErrorString(result, &text);
    fprintf(stderr, "%s failed: %s\n", call, text == NULL ? "unknown error" : text);
    exit(1);
  }
}

static uint32_t expected(uint32_t bits) {
  float x;
  memcpy(&x, &bits, sizeof x);
  float r = nearbyintf(x);
  if (isnan(r)) {
    return 0x7fc00000u;
  }
  uint32_t out;
  memcpy(&out, &r, sizeof out);
  return out;
}

int main(int argc, char **argv) {
  unsigned chunkBits = 26;
  if (argc == 2) {
    char *end;
    unsigned long v = strtoul(argv[1], &end, 10);
    if (*end != 0 || v < 8 || v > 30) {
      fprintf(stderr, "bad chunk bits: %s\n", argv[1]);
      return 2;
    }
    chunkBits = (unsigned)v;
  } else if (argc != 1) {
    fprintf(stderr, "usage: ptx-nearest [CHUNK_BITS]\n");
    return 2;
  }
  check(cuInit(0), "cuInit");
  CUdevice device;
  check(cuDeviceGet(&device, 0), "cuDeviceGet");
  char name[256];
  check(cuDeviceGetName(name, sizeof name, device), "cuDeviceGetName");
  CUcontext context;
  check(cuDevicePrimaryCtxRetain(&context, device), "cuDevicePrimaryCtxRetain");
  check(cuCtxSetCurrent(context), "cuCtxSetCurrent");
  CUmodule module;
  check(cuModuleLoadData(&module, kernel), "cuModuleLoadData");
  CUfunction function;
  check(cuModuleGetFunction(&function, module, "nearest"), "cuModuleGetFunction");

  size_t chunk = (size_t)1 << chunkBits;
  CUdeviceptr out;
  check(cuMemAlloc(&out, chunk * sizeof(uint32_t)), "cuMemAlloc");
  uint32_t *host = malloc(chunk * sizeof *host);
  if (host == NULL) {
    fprintf(stderr, "out of memory\n");
    return 1;
  }
  uint64_t mismatches = 0;
  for (uint64_t base = 0; base < ((uint64_t)1 << 32); base += chunk) {
    uint32_t base32 = (uint32_t)base;
    void *params[] = {&out, &base32};
    check(cuLaunchKernel(function, (unsigned)(chunk / 256), 1, 1, 256, 1, 1, 0, NULL, params, NULL),
          "cuLaunchKernel");
    check(cuMemcpyDtoH(host, out, chunk * sizeof *host), "cuMemcpyDtoH");
    for (size_t i = 0; i < chunk; i++) {
      uint32_t bits = base32 + (uint32_t)i;
      uint32_t want = expected(bits);
      if (host[i] != want) {
        if (mismatches < 10) {
          printf("mismatch: input 0x%08" PRIx32 " device 0x%08" PRIx32 " expected 0x%08" PRIx32 "\n",
                 bits, host[i], want);
        }
        mismatches++;
      }
    }
  }
  printf("device %s: cvt.rni.f32.f32 with NaN replacement, 4294967296 inputs, %" PRIu64
         " mismatches\n", name, mismatches);
  free(host);
  check(cuMemFree(out), "cuMemFree");
  check(cuModuleUnload(module), "cuModuleUnload");
  return mismatches == 0 ? 0 : 1;
}
