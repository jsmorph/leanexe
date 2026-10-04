/* Runs WGSL compute entry points with wgpu-native.

   webgpu-host info
   webgpu-host run SHADER ENTRY WORKGROUPS OUTPUT [INPUT...]
   webgpu-host session

   Each INPUT is a read-only storage buffer at the next binding of group 0, given as
   u32:W,W,... (32-bit words), u64:W,W,... (64-bit words, least significant half first), or
   file:PATH (the file's bytes, whose length must be a multiple of 4).
   The output is a read-write storage buffer at the binding after the inputs.  OUTPUT is either
   a number of 32-bit words, filled with 0x7fc00001 before the dispatch so a word the kernel does
   not write keeps that value, or a buffer specification as for an input, which gives the
   output's initial words.  The dispatch is WORKGROUPS workgroups along x.  The output words are
   printed in decimal, separated by commas.  The Vulkan driver is chosen by the loader, for
   example through VK_ICD_FILENAMES.

   A session keeps one device and named buffers, and reads commands from standard input, one
   per line, answering each with a line `ok` or with the requested data:
     load NAME PATH           a buffer holding the file's bytes
     words NAME SPEC          a buffer holding u32:W,... or u64:W,... as for an input
     output NAME N            a buffer of 2 + 2N words: the length N as a 64-bit word, then zeros
     shader NAME PATH         compiles the entry point `main` of a WGSL file
     run SHADER WORKGROUPS OUT IN...   dispatches with IN... at bindings 0, 1, ... and OUT after
     read NAME PATH           writes the buffer's bytes to the file
     free NAME                releases the buffer
     quit
   The device has the adapter's limits, so buffers and bindings may be as large as it allows.
   Any error ends the process with a message on standard error. */

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
  WGPULimits limits = WGPU_LIMITS_INIT;
  if (wgpuAdapterGetLimits(gpu.adapter, &limits) != WGPUStatus_Success) {
    die("wgpuAdapterGetLimits failed");
  }
  WGPUDeviceDescriptor deviceDescriptor = {0};
  deviceDescriptor.requiredLimits = &limits;
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

/* A named buffer or pipeline of a session. */
typedef struct {
  char name[64];
  WGPUBuffer buffer;
  size_t bytes;
  WGPUComputePipeline pipeline;
} Entry;

#define MAX_ENTRIES 4096
static Entry entries_[MAX_ENTRIES];
static int entryCount_ = 0;

static Entry *find_entry(const char *name) {
  for (int i = 0; i < entryCount_; i++) {
    if (strcmp(entries_[i].name, name) == 0) {
      return &entries_[i];
    }
  }
  return NULL;
}

static Entry *new_entry(const char *name) {
  if (strlen(name) >= sizeof entries_[0].name) {
    fprintf(stderr, "name too long: %s\n", name);
    exit(1);
  }
  Entry *entry = find_entry(name);
  if (entry != NULL) {
    if (entry->buffer != NULL) {
      wgpuBufferRelease(entry->buffer);
    }
    if (entry->pipeline != NULL) {
      wgpuComputePipelineRelease(entry->pipeline);
    }
  } else {
    if (entryCount_ == MAX_ENTRIES) {
      die("too many names");
    }
    entry = &entries_[entryCount_++];
  }
  memset(entry, 0, sizeof *entry);
  strcpy(entry->name, name);
  return entry;
}

static Entry *need_buffer(const char *name) {
  Entry *entry = find_entry(name);
  if (entry == NULL || entry->buffer == NULL) {
    fprintf(stderr, "no buffer named %s\n", name);
    exit(1);
  }
  return entry;
}

static void store_buffer(Gpu *gpu, const char *name, const uint32_t *words, size_t count) {
  Entry *entry = new_entry(name);
  entry->bytes = count * 4;
  entry->buffer = make_buffer(gpu, WGPUBufferUsage_Storage | WGPUBufferUsage_CopySrc |
                                       WGPUBufferUsage_CopyDst, entry->bytes);
  wgpuQueueWriteBuffer(gpu->queue, entry->buffer, 0, words, entry->bytes);
}

static void wait_map(Gpu *gpu, WGPUBuffer buffer, size_t bytes) {
  bool mapped = false;
  WGPUBufferMapCallbackInfo mapCallback = {0};
  mapCallback.mode = WGPUCallbackMode_AllowProcessEvents;
  mapCallback.callback = on_map;
  mapCallback.userdata1 = &mapped;
  wgpuBufferMapAsync(buffer, WGPUMapMode_Read, 0, bytes, mapCallback);
  while (!mapped) {
    wgpuDevicePoll(gpu->device, true, NULL);
    wgpuInstanceProcessEvents(gpu->instance);
  }
}

static void session(Gpu *gpu) {
  char line[65536];
  while (fgets(line, sizeof line, stdin) != NULL) {
    size_t length = strlen(line);
    if (length > 0 && line[length - 1] == '\n') {
      line[--length] = 0;
    }
    char *words[64];
    int count = 0;
    for (char *token = strtok(line, " "); token != NULL && count < 64; token = strtok(NULL, " ")) {
      words[count++] = token;
    }
    if (count == 0) {
      continue;
    }
    const char *command = words[0];
    if (strcmp(command, "quit") == 0) {
      return;
    } else if (strcmp(command, "load") == 0 && count == 3) {
      size_t n;
      char spec[4096];
      snprintf(spec, sizeof spec, "file:%s", words[2]);
      uint32_t *data = parse_input(spec, &n);
      store_buffer(gpu, words[1], data, n);
      free(data);
    } else if (strcmp(command, "words") == 0 && count == 3) {
      size_t n;
      uint32_t *data = parse_input(words[2], &n);
      store_buffer(gpu, words[1], data, n);
      free(data);
    } else if (strcmp(command, "output") == 0 && count == 3) {
      char *end;
      uint64_t n = parse_word(words[2], &end, (SIZE_MAX / 8) - 1);
      size_t total = 2 + 2 * (size_t)n;
      uint32_t *data = calloc(total, sizeof *data);
      if (data == NULL) {
        die("out of memory");
      }
      data[0] = (uint32_t)n;
      data[1] = (uint32_t)(n >> 32);
      store_buffer(gpu, words[1], data, total);
      free(data);
    } else if (strcmp(command, "shader") == 0 && count == 3) {
      char *code = read_file(words[2], NULL);
      WGPUShaderSourceWGSL source = {0};
      source.chain.sType = WGPUSType_ShaderSourceWGSL;
      source.code = view(code);
      WGPUShaderModuleDescriptor moduleDescriptor = {0};
      moduleDescriptor.nextInChain = &source.chain;
      WGPUShaderModule module = wgpuDeviceCreateShaderModule(gpu->device, &moduleDescriptor);
      WGPUComputePipelineDescriptor pipelineDescriptor = {0};
      pipelineDescriptor.compute.module = module;
      pipelineDescriptor.compute.entryPoint = view("main");
      Entry *entry = new_entry(words[1]);
      entry->pipeline = wgpuDeviceCreateComputePipeline(gpu->device, &pipelineDescriptor);
      wgpuShaderModuleRelease(module);
      free(code);
    } else if (strcmp(command, "run") == 0 && count >= 4) {
      Entry *shader = find_entry(words[1]);
      if (shader == NULL || shader->pipeline == NULL) {
        fprintf(stderr, "no shader named %s\n", words[1]);
        exit(1);
      }
      char *end;
      uint32_t workgroups = (uint32_t)parse_word(words[2], &end, UINT32_MAX);
      int inputs = count - 4;
      WGPUBindGroupEntry bindings[64];
      memset(bindings, 0, sizeof bindings);
      for (int i = 0; i <= inputs; i++) {
        Entry *buffer = need_buffer(i < inputs ? words[4 + i] : words[3]);
        bindings[i].binding = (uint32_t)i;
        bindings[i].buffer = buffer->buffer;
        bindings[i].size = buffer->bytes;
      }
      WGPUBindGroupDescriptor groupDescriptor = {0};
      groupDescriptor.layout = wgpuComputePipelineGetBindGroupLayout(shader->pipeline, 0);
      groupDescriptor.entryCount = (size_t)inputs + 1;
      groupDescriptor.entries = bindings;
      WGPUBindGroup group = wgpuDeviceCreateBindGroup(gpu->device, &groupDescriptor);
      WGPUCommandEncoder encoder = wgpuDeviceCreateCommandEncoder(gpu->device, NULL);
      WGPUComputePassEncoder pass = wgpuCommandEncoderBeginComputePass(encoder, NULL);
      wgpuComputePassEncoderSetPipeline(pass, shader->pipeline);
      wgpuComputePassEncoderSetBindGroup(pass, 0, group, 0, NULL);
      wgpuComputePassEncoderDispatchWorkgroups(pass, workgroups, 1, 1);
      wgpuComputePassEncoderEnd(pass);
      WGPUCommandBuffer commands = wgpuCommandEncoderFinish(encoder, NULL);
      wgpuQueueSubmit(gpu->queue, 1, &commands);
      wgpuCommandBufferRelease(commands);
      wgpuComputePassEncoderRelease(pass);
      wgpuCommandEncoderRelease(encoder);
      wgpuBindGroupRelease(group);
      wgpuBindGroupLayoutRelease(groupDescriptor.layout);
    } else if (strcmp(command, "read") == 0 && count == 3) {
      Entry *buffer = need_buffer(words[1]);
      WGPUBuffer readback =
          make_buffer(gpu, WGPUBufferUsage_MapRead | WGPUBufferUsage_CopyDst, buffer->bytes);
      WGPUCommandEncoder encoder = wgpuDeviceCreateCommandEncoder(gpu->device, NULL);
      wgpuCommandEncoderCopyBufferToBuffer(encoder, buffer->buffer, 0, readback, 0, buffer->bytes);
      WGPUCommandBuffer commands = wgpuCommandEncoderFinish(encoder, NULL);
      wgpuQueueSubmit(gpu->queue, 1, &commands);
      wgpuCommandBufferRelease(commands);
      wgpuCommandEncoderRelease(encoder);
      wait_map(gpu, readback, buffer->bytes);
      const void *data = wgpuBufferGetConstMappedRange(readback, 0, buffer->bytes);
      if (data == NULL) {
        die("wgpuBufferGetConstMappedRange failed");
      }
      FILE *file = fopen(words[2], "wb");
      if (file == NULL || fwrite(data, 1, buffer->bytes, file) != buffer->bytes ||
          fclose(file) != 0) {
        fprintf(stderr, "cannot write %s\n", words[2]);
        exit(1);
      }
      wgpuBufferUnmap(readback);
      wgpuBufferRelease(readback);
    } else if (strcmp(command, "free") == 0 && count == 2) {
      Entry *buffer = need_buffer(words[1]);
      wgpuBufferRelease(buffer->buffer);
      buffer->buffer = NULL;
      buffer->bytes = 0;
    } else {
      fprintf(stderr, "bad command: %s\n", command);
      exit(1);
    }
    printf("ok\n");
    fflush(stdout);
  }
}

int main(int argc, char **argv) {
  if (argc >= 2 && strcmp(argv[1], "info") == 0) {
    Gpu gpu = open_gpu();
    print_info(&gpu);
    return 0;
  }
  if (argc == 2 && strcmp(argv[1], "session") == 0) {
    Gpu gpu = open_gpu();
    session(&gpu);
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
          "[u32:W,...|u64:W,...|file:PATH]...\n"
          "       webgpu-host session\n");
  return 2;
}
