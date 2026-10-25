#include <errno.h>
#include <stdint.h>
#include <unistd.h>
#include <lean/lean.h>

LEAN_EXPORT lean_obj_res leanexe_running_sum_read_stdin(uint64_t requested) {
  if (requested > SIZE_MAX || lean_alloc_sarray_would_overflow(1, (size_t)requested)) {
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, NULL));
  }
  size_t capacity = (size_t)requested;
  lean_object *bytes = lean_alloc_sarray(1, 0, capacity);
  if (capacity == 0) {
    return lean_io_result_mk_ok(bytes);
  }
  ssize_t count;
  do {
    count = read(STDIN_FILENO, lean_sarray_cptr(bytes), capacity);
  } while (count < 0 && errno == EINTR);
  if (count < 0) {
    int error = errno;
    lean_dec(bytes);
    return lean_io_result_mk_error(lean_decode_io_error(error, NULL));
  }
  lean_sarray_set_size(bytes, (size_t)count);
  return lean_io_result_mk_ok(bytes);
}
