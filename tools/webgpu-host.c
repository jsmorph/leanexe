/* Runs one WGSL compute entry point with wgpu-native and prints its output buffer.

   webgpu-host info
   webgpu-host run SHADER ENTRY WORKGROUPS OUTPUT [INPUT...]

   Each INPUT is a read-only storage buffer at the next binding of group 0, given as
   u32:W,W,... (32-bit words), u64:W,W,... (64-bit words, least significant half first), or
   file:PATH (the file's bytes, whose length must be a multiple of 4).
   The output is a read-write storage buffer at the binding after the inputs.  OUTPUT is either
   a number of 32-bit words, filled with 0x7fc00001 before the dispatch so a word the kernel does
   not write keeps that value, or a buffer specification as for an input, which gives the
   output's initial words.  The dispatch is WORKGROUPS workgroups along x.  The output words are
   printed in decimal, separated by commas.  The Vulkan driver is chosen by the loader, for
   example through VK_ICD_FILENAMES. */

#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <webgpu/webgpu.h>
#include <webgpu/wgpu.h>

#define FILL_WORD 0x7fc00001u

static void die(const char *message) {
  fprintf(stderr, "%s\n", message);
  exit(1);
}

static WGPUStringView view(const char *text) {
  WGPUStringView result = {text, strlen(text)};
  return result;
}

static void print_view(FILE *out, WGPUStringView text) {
  if (text.data != NULL) {
    fwrite(text.data, 1, text.length == WGPU_STRLEN ? strlen(text.data) : text.length, out);
  }
}

typedef struct {
  bool done;
  WGPUAdapter adapter;
  WGPUDevice device;
} Request;

static void on_adapter(WGPURequestAdapterStatus status, WGPUAdapter adapter, WGPUStringView message,
                       void *userdata1, void *userdata2) {
  (void)userdata2;
  Request *request = userdata1;
  if (status != WGPURequestAdapterStatus_Success) {
    fprintf(stderr, "no adapter: ");
    print_view(stderr, message);
    fprintf(stderr, "\n");
    exit(1);
  }
  request->adapter = adapter;
  request->done = true;
}

static void on_device(WGPURequestDeviceStatus status, WGPUDevice device, WGPUStringView message,
                      void *userdata1, void *userdata2) {
  (void)userdata2;
  Request *request = userdata1;
  if (status != WGPURequestDeviceStatus_Success) {
    fprintf(stderr, "no device: ");
    print_view(stderr, message);
    fprintf(stderr, "\n");
    exit(1);
  }
  request->device = device;
  request->done = true;
}

static void on_error(WGPUDevice const *device, WGPUErrorType type, WGPUStringView message,
                     void *userdata1, void *userdata2) {
  (void)device;
  (void)userdata1;
  (void)userdata2;
  fprintf(stderr, "WebGPU error %d: ", (int)type);
  print_view(stderr, message);
  fprintf(stderr, "\n");
  exit(1);
}

static void on_map(WGPUMapAsyncStatus status, WGPUStringView message, void *userdata1,
                   void *userdata2) {
  (void)userdata2;
  if (status != WGPUMapAsyncStatus_Success) {
    fprintf(stderr, "map failed: ");
    print_view(stderr, message);
    fprintf(stderr, "\n");
    exit(1);
  }
  *(bool *)userdata1 = true;
}

typedef struct {
  WGPUInstance instance;
  WGPUAdapter adapter;
  WGPUDevice device;
  WGPUQueue queue;
} Gpu;

static Gpu open_gpu(void) {
  WGPUInstanceExtras extras = {0};
  extras.chain.sType = (WGPUSType)WGPUSType_InstanceExtras;
  extras.backends = WGPUInstanceBackend_Vulkan;
  WGPUInstanceDescriptor descriptor = {0};
  descriptor.nextInChain = &extras.chain;
  Gpu gpu = {0};
  gpu.instance = wgpuCreateInstance(&descriptor);
  if (gpu.instance == NULL) {
    die("wgpuCreateInstance failed");
  }

  Request request = {0};
  WGPURequestAdapterCallbackInfo adapterCallback = {0};
  adapterCallback.mode = WGPUCallbackMode_AllowProcessEvents;
  adapterCallback.callback = on_adapter;
  adapterCallback.userdata1 = &request;
  wgpuInstanceRequestAdapter(gpu.instance, NULL, adapterCallback);
  while (!request.done) {
    wgpuInstanceProcessEvents(gpu.instance);
  }
  gpu.adapter = request.adapter;

  request.done = false;
  WGPUDeviceDescriptor deviceDescriptor = {0};
  deviceDescriptor.uncapturedErrorCallbackInfo.callback = on_error;
  WGPURequestDeviceCallbackInfo deviceCallback = {0};
  deviceCallback.mode = WGPUCallbackMode_AllowProcessEvents;
  deviceCallback.callback = on_device;
  deviceCallback.userdata1 = &request;
  wgpuAdapterRequestDevice(gpu.adapter, &deviceDescriptor, deviceCallback);
  while (!request.done) {
    wgpuInstanceProcessEvents(gpu.instance);
  }
  gpu.device = request.device;
  gpu.queue = wgpuDeviceGetQueue(gpu.device);
  return gpu;
}

static void print_info(Gpu *gpu) {
  WGPUAdapterInfo info = {0};
  if (wgpuAdapterGetInfo(gpu->adapter, &info) != WGPUStatus_Success) {
    die("wgpuAdapterGetInfo failed");
  }
  printf("vendor: ");
  print_view(stdout, info.vendor);
  printf("\narchitecture: ");
  print_view(stdout, info.architecture);
  printf("\ndevice: ");
  print_view(stdout, info.device);
  printf("\ndescription: ");
  print_view(stdout, info.description);
  printf("\nbackend: %d\nadapter type: %d\n", (int)info.backendType, (int)info.adapterType);
}

static char *read_file(const char *path, size_t *length) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    fprintf(stderr, "cannot open %s\n", path);
    exit(1);
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    die("fseek failed");
  }
  long size = ftell(file);
  if (size < 0) {
    die("ftell failed");
  }
  rewind(file);
  char *text = malloc((size_t)size + 1);
  if (text == NULL) {
    die("out of memory");
  }
  if (fread(text, 1, (size_t)size, file) != (size_t)size) {
    die("short read");
  }
  text[size] = 0;
  fclose(file);
  if (length != NULL) {
    *length = (size_t)size;
  }
  return text;
}

static uint64_t parse_word(const char *text, char **end, uint64_t limit) {
  errno = 0;
  unsigned long long value = strtoull(text, end, 10);
  if (*end == text || errno == ERANGE || value > limit) {
    fprintf(stderr, "bad word: %s\n", text);
    exit(1);
  }
  return value;
}

/* The 32-bit words of an input specification; at least one word, since a binding may not
   be empty. */
static uint32_t *parse_input(const char *spec, size_t *count) {
  if (strncmp(spec, "file:", 5) == 0) {
    size_t length;
    char *bytes = read_file(spec + 5, &length);
    if (length % 4 != 0) {
      fprintf(stderr, "input file length is not a multiple of 4: %s\n", spec + 5);
      exit(1);
    }
    uint32_t *words = calloc(length == 0 ? 1 : length / 4, sizeof *words);
    if (words == NULL) {
      die("out of memory");
    }
    memcpy(words, bytes, length);
    free(bytes);
    *count = length == 0 ? 1 : length / 4;
    return words;
  }
  bool wide;
  if (strncmp(spec, "u32:", 4) == 0) {
    wide = false;
  } else if (strncmp(spec, "u64:", 4) == 0) {
    wide = true;
  } else {
    fprintf(stderr, "unknown input: %s\n", spec);
    exit(1);
  }
  const char *text = spec + 4;
  size_t capacity = 16, n = 0;
  uint32_t *words = malloc(capacity * sizeof *words);
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
      fprintf(stderr, "bad input: %s\n", spec);
      exit(1);
    }
    text = end;
  }
  if (n == 0) {
    words[n++] = 0;
  }
  *count = n;
  return words;
}

static WGPUBuffer make_buffer(Gpu *gpu, WGPUBufferUsage usage, size_t bytes) {
  WGPUBufferDescriptor descriptor = {0};
  descriptor.usage = usage;
  descriptor.size = bytes;
  WGPUBuffer buffer = wgpuDeviceCreateBuffer(gpu->device, &descriptor);
  if (buffer == NULL) {
    die("wgpuDeviceCreateBuffer failed");
  }
  return buffer;
}

static void run(Gpu *gpu, const char *shaderPath, const char *entry, uint32_t workgroups,
                const char *outputSpec, int inputCount, char **inputs) {
  size_t outputWords;
  uint32_t *initial;
  if (strchr(outputSpec, ':') != NULL) {
    initial = parse_input(outputSpec, &outputWords);
  } else {
    char *end;
    outputWords = (size_t)parse_word(outputSpec, &end, SIZE_MAX / 4);
    if (outputWords == 0) {
      die("the output needs at least one word");
    }
    initial = malloc(outputWords * 4);
    if (initial == NULL) {
      die("out of memory");
    }
    for (size_t j = 0; j < outputWords; j++) {
      initial[j] = FILL_WORD;
    }
  }
  char *code = read_file(shaderPath, NULL);
  WGPUShaderSourceWGSL source = {0};
  source.chain.sType = WGPUSType_ShaderSourceWGSL;
  source.code = view(code);
  WGPUShaderModuleDescriptor moduleDescriptor = {0};
  moduleDescriptor.nextInChain = &source.chain;
  WGPUShaderModule module = wgpuDeviceCreateShaderModule(gpu->device, &moduleDescriptor);

  WGPUComputePipelineDescriptor pipelineDescriptor = {0};
  pipelineDescriptor.compute.module = module;
  pipelineDescriptor.compute.entryPoint = view(entry);
  WGPUComputePipeline pipeline = wgpuDeviceCreateComputePipeline(gpu->device, &pipelineDescriptor);

  WGPUBindGroupEntry *entries = calloc((size_t)inputCount + 1, sizeof *entries);
  if (entries == NULL) {
    die("out of memory");
  }
  for (int i = 0; i < inputCount; i++) {
    size_t count;
    uint32_t *words = parse_input(inputs[i], &count);
    WGPUBuffer buffer =
        make_buffer(gpu, WGPUBufferUsage_Storage | WGPUBufferUsage_CopyDst, count * 4);
    wgpuQueueWriteBuffer(gpu->queue, buffer, 0, words, count * 4);
    free(words);
    entries[i].binding = (uint32_t)i;
    entries[i].buffer = buffer;
    entries[i].size = count * 4;
  }
  size_t outputBytes = outputWords * 4;
  WGPUBuffer output = make_buffer(
      gpu, WGPUBufferUsage_Storage | WGPUBufferUsage_CopySrc | WGPUBufferUsage_CopyDst, outputBytes);
  wgpuQueueWriteBuffer(gpu->queue, output, 0, initial, outputBytes);
  free(initial);
  entries[inputCount].binding = (uint32_t)inputCount;
  entries[inputCount].buffer = output;
  entries[inputCount].size = outputBytes;
  WGPUBuffer readback = make_buffer(gpu, WGPUBufferUsage_MapRead | WGPUBufferUsage_CopyDst,
                                    outputBytes);

  WGPUBindGroupDescriptor groupDescriptor = {0};
  groupDescriptor.layout = wgpuComputePipelineGetBindGroupLayout(pipeline, 0);
  groupDescriptor.entryCount = (size_t)inputCount + 1;
  groupDescriptor.entries = entries;
  WGPUBindGroup group = wgpuDeviceCreateBindGroup(gpu->device, &groupDescriptor);

  WGPUCommandEncoder encoder = wgpuDeviceCreateCommandEncoder(gpu->device, NULL);
  WGPUComputePassEncoder pass = wgpuCommandEncoderBeginComputePass(encoder, NULL);
  wgpuComputePassEncoderSetPipeline(pass, pipeline);
  wgpuComputePassEncoderSetBindGroup(pass, 0, group, 0, NULL);
  wgpuComputePassEncoderDispatchWorkgroups(pass, workgroups, 1, 1);
  wgpuComputePassEncoderEnd(pass);
  wgpuCommandEncoderCopyBufferToBuffer(encoder, output, 0, readback, 0, outputBytes);
  WGPUCommandBuffer commands = wgpuCommandEncoderFinish(encoder, NULL);
  wgpuQueueSubmit(gpu->queue, 1, &commands);

  bool mapped = false;
  WGPUBufferMapCallbackInfo mapCallback = {0};
  mapCallback.mode = WGPUCallbackMode_AllowProcessEvents;
  mapCallback.callback = on_map;
  mapCallback.userdata1 = &mapped;
  wgpuBufferMapAsync(readback, WGPUMapMode_Read, 0, outputBytes, mapCallback);
  while (!mapped) {
    wgpuDevicePoll(gpu->device, true, NULL);
    wgpuInstanceProcessEvents(gpu->instance);
  }
  const uint32_t *words = wgpuBufferGetConstMappedRange(readback, 0, outputBytes);
  if (words == NULL) {
    die("wgpuBufferGetConstMappedRange failed");
  }
  for (size_t j = 0; j < outputWords; j++) {
    printf(j == 0 ? "%" PRIu32 : ",%" PRIu32, words[j]);
  }
  printf("\n");
  free(entries);
  free(code);
}

int main(int argc, char **argv) {
  if (argc >= 2 && strcmp(argv[1], "info") == 0) {
    Gpu gpu = open_gpu();
    print_info(&gpu);
    return 0;
  }
  if (argc >= 6 && strcmp(argv[1], "run") == 0) {
    char *end;
    uint32_t workgroups = (uint32_t)parse_word(argv[4], &end, UINT32_MAX);
    Gpu gpu = open_gpu();
    run(&gpu, argv[2], argv[3], workgroups, argv[5], argc - 6, argv + 6);
    return 0;
  }
  fprintf(stderr,
          "usage: webgpu-host info\n"
          "       webgpu-host run SHADER ENTRY WORKGROUPS OUTPUT_WORDS|BUFFER "
          "[u32:W,...|u64:W,...|file:PATH]...\n");
  return 2;
}
