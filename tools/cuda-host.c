/* Runs PTX kernels with the CUDA driver API.

   cuda-host info
   cuda-host run IMAGE ENTRY BLOCKS OUTPUT [INPUT...]

   IMAGE is a cubin that ptxas wrote or a PTX text, which the driver compiles.  Each INPUT is a
   global buffer at the next parameter, given as u32:W,W,... (32-bit words), u64:W,W,... (64-bit
   words, least significant half first), or file:PATH (the file's bytes).  The output is the buffer
   at the parameter after the inputs.  OUTPUT is either a number of 32-bit words, filled with
   0x7fc00001 before the launch so a word the kernel does not write keeps that value, or a buffer
   specification as for an input, which gives the output's initial words.  Every buffer holds a
   whole number of 64-bit words.  The launch is BLOCKS blocks of 64 threads along x.  The copies
   to the device, the launch, and the copy back are queued on one stream, and the host reads the
   output after synchronizing that stream.  The output is printed as 32-bit words in decimal,
   separated by commas, least significant half of each 64-bit word first.  Any error ends the
   process with a message on standard error. */

#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <cuda.h>

#define FILL_WORD 0x7fc00001u
#define BLOCK 64

static void die(const char *message) {
  fprintf(stderr, "%s\n", message);
  exit(1);
}

static void check(CUresult result, const char *call) {
  if (result != CUDA_SUCCESS) {
    const char *text = NULL;
    cuGetErrorString(result, &text);
    fprintf(stderr, "%s failed: %s\n", call, text == NULL ? "unknown error" : text);
    exit(1);
  }
}

static char *read_file(const char *path, size_t *length) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    fprintf(stderr, "cannot open %s: %s\n", path, strerror(errno));
    exit(1);
  }
  size_t capacity = 1 << 16, n = 0;
  char *bytes = malloc(capacity + 1);
  if (bytes == NULL) {
    die("out of memory");
  }
  for (;;) {
    if (n == capacity) {
      capacity *= 2;
      bytes = realloc(bytes, capacity + 1);
      if (bytes == NULL) {
        die("out of memory");
      }
    }
    size_t got = fread(bytes + n, 1, capacity - n, file);
    n += got;
    if (got == 0) {
      break;
    }
  }
  if (ferror(file)) {
    fprintf(stderr, "cannot read %s\n", path);
    exit(1);
  }
  fclose(file);
  bytes[n] = 0;
  *length = n;
  return bytes;
}

static uint64_t parse_word(const char *text, char **end, uint64_t limit) {
  errno = 0;
  unsigned long long value = strtoull(text, end, 10);
  if (*end == text || errno != 0 || value > limit) {
    fprintf(stderr, "bad word: %s\n", text);
    exit(1);
  }
  return (uint64_t)value;
}

/* The 32-bit words of a buffer specification; an even number, at least two. */
static uint32_t *parse_buffer(const char *spec, size_t *count) {
  uint32_t *words;
  size_t n;
  if (strncmp(spec, "file:", 5) == 0) {
    size_t length;
    char *bytes = read_file(spec + 5, &length);
    if (length % 8 != 0) {
      fprintf(stderr, "buffer file length is not a multiple of 8: %s\n", spec + 5);
      exit(1);
    }
    n = length / 4;
    words = calloc(n == 0 ? 2 : n, sizeof *words);
    if (words == NULL) {
      die("out of memory");
    }
    memcpy(words, bytes, length);
    free(bytes);
  } else {
    bool wide;
    if (strncmp(spec, "u32:", 4) == 0) {
      wide = false;
    } else if (strncmp(spec, "u64:", 4) == 0) {
      wide = true;
    } else {
      fprintf(stderr, "unknown buffer: %s\n", spec);
      exit(1);
    }
    const char *text = spec + 4;
    size_t capacity = 16;
    n = 0;
    words = malloc(capacity * sizeof *words);
    if (words == NULL) {
      die("out of memory");
    }
    while (*text != 0) {
      char *end;
      uint64_t value = parse_word(text, &end, wide ? UINT64_MAX : UINT32_MAX);
      if (n + 2 > capacity) {
        capacity *= 2;
        words = realloc(words, capacity * sizeof *words);
        if (words == NULL) {
          die("out of memory");
        }
      }
      words[n++] = (uint32_t)value;
      if (wide) {
        words[n++] = (uint32_t)(value >> 32);
      }
      if (*end == ',') {
        end++;
      } else if (*end != 0) {
        fprintf(stderr, "bad buffer: %s\n", spec);
        exit(1);
      }
      text = end;
    }
    if (n % 2 != 0) {
      fprintf(stderr, "buffer is not a whole number of 64-bit words: %s\n", spec);
      exit(1);
    }
  }
  if (n == 0) {
    words[0] = 0;
    words[1] = 0;
    n = 2;
  }
  *count = n;
  return words;
}

static CUdevice open_device(CUcontext *context) {
  check(cuInit(0), "cuInit");
  CUdevice device;
  check(cuDeviceGet(&device, 0), "cuDeviceGet");
  check(cuDevicePrimaryCtxRetain(context, device), "cuDevicePrimaryCtxRetain");
  check(cuCtxSetCurrent(*context), "cuCtxSetCurrent");
  return device;
}

static void info(void) {
  CUcontext context;
  CUdevice device = open_device(&context);
  char name[256];
  check(cuDeviceGetName(name, sizeof name, device), "cuDeviceGetName");
  int major, minor, version;
  check(cuDeviceGetAttribute(&major, CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, device),
        "cuDeviceGetAttribute");
  check(cuDeviceGetAttribute(&minor, CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR, device),
        "cuDeviceGetAttribute");
  check(cuDriverGetVersion(&version), "cuDriverGetVersion");
  printf("device %s\ncompute capability %d.%d\ndriver %d\n", name, major, minor, version);
}

static CUdeviceptr upload(CUstream stream, const uint32_t *words, size_t count) {
  CUdeviceptr buffer;
  check(cuMemAlloc(&buffer, count * sizeof *words), "cuMemAlloc");
  check(cuMemcpyHtoDAsync(buffer, words, count * sizeof *words, stream), "cuMemcpyHtoDAsync");
  return buffer;
}

static void run(const char *imagePath, const char *entry, unsigned blocks, const char *outputSpec,
                int inputCount, char **inputs) {
  CUcontext context;
  open_device(&context);
  size_t imageLength;
  char *image = read_file(imagePath, &imageLength);
  CUmodule module;
  check(cuModuleLoadData(&module, image), "cuModuleLoadData");
  CUfunction function;
  check(cuModuleGetFunction(&function, module, entry), "cuModuleGetFunction");

  size_t outputWords;
  uint32_t *output;
  if (strchr(outputSpec, ':') != NULL) {
    output = parse_buffer(outputSpec, &outputWords);
  } else {
    char *end;
    outputWords = (size_t)parse_word(outputSpec, &end, SIZE_MAX / 8);
    if (*end != 0 || outputWords == 0 || outputWords % 2 != 0) {
      fprintf(stderr, "bad output size: %s\n", outputSpec);
      exit(1);
    }
    output = malloc(outputWords * sizeof *output);
    if (output == NULL) {
      die("out of memory");
    }
    for (size_t i = 0; i < outputWords; i++) {
      output[i] = FILL_WORD;
    }
  }

  CUstream stream;
  check(cuStreamCreate(&stream, CU_STREAM_DEFAULT), "cuStreamCreate");
  CUdeviceptr *buffers = calloc((size_t)inputCount + 1, sizeof *buffers);
  void **params = calloc((size_t)inputCount + 1, sizeof *params);
  uint32_t **words = calloc((size_t)inputCount, sizeof *words);
  if (buffers == NULL || params == NULL || (inputCount > 0 && words == NULL)) {
    die("out of memory");
  }
  for (int i = 0; i < inputCount; i++) {
    size_t count;
    words[i] = parse_buffer(inputs[i], &count);
    buffers[i] = upload(stream, words[i], count);
    params[i] = &buffers[i];
  }
  buffers[inputCount] = upload(stream, output, outputWords);
  params[inputCount] = &buffers[inputCount];

  check(cuLaunchKernel(function, blocks, 1, 1, BLOCK, 1, 1, 0, stream, params, NULL),
        "cuLaunchKernel");
  check(cuMemcpyDtoHAsync(output, buffers[inputCount], outputWords * sizeof *output, stream),
        "cuMemcpyDtoHAsync");
  check(cuStreamSynchronize(stream), "cuStreamSynchronize");
  for (size_t i = 0; i < outputWords; i++) {
    printf(i == 0 ? "%" PRIu32 : ",%" PRIu32, output[i]);
  }
  printf("\n");

  for (int i = 0; i <= inputCount; i++) {
    check(cuMemFree(buffers[i]), "cuMemFree");
  }
  for (int i = 0; i < inputCount; i++) {
    free(words[i]);
  }
  check(cuStreamDestroy(stream), "cuStreamDestroy");
  check(cuModuleUnload(module), "cuModuleUnload");
  free(words);
  free(buffers);
  free(params);
  free(output);
  free(image);
}

int main(int argc, char **argv) {
  if (argc == 2 && strcmp(argv[1], "info") == 0) {
    info();
    return 0;
  }
  if (argc >= 6 && strcmp(argv[1], "run") == 0) {
    char *end;
    uint64_t blocks = parse_word(argv[4], &end, UINT32_MAX);
    if (*end != 0) {
      fprintf(stderr, "bad block count: %s\n", argv[4]);
      return 1;
    }
    run(argv[2], argv[3], (unsigned)blocks, argv[5], argc - 6, argv + 6);
    return 0;
  }
  fprintf(stderr,
          "usage: cuda-host info\n"
          "       cuda-host run IMAGE ENTRY BLOCKS OUTPUT [INPUT...]\n");
  return 2;
}
