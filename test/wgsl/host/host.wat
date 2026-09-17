(module
  (type (func (param i32 i32 i32) (result i32)))
  (import "leanexe.webgpu" "gemm_f32" (func (type 0)))
  (func (type 0)
    local.get 0
    local.get 1
    local.get 2
    call 0)
  (memory 1 256)
  (export "memory" (memory 0))
  (export "run" (func 1)))
