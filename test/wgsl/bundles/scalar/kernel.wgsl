// leanexe WGSL GEMM v1; row-major f32 storage buffers
const M: u32 = 1u;
const N: u32 = 1u;
const K: u32 = 1u;

@group(0) @binding(0) var<storage, read> a: array<f32>;
@group(0) @binding(1) var<storage, read> b: array<f32>;
@group(0) @binding(2) var<storage, read_write> c: array<f32>;

@compute @workgroup_size(8, 8, 1)
fn gemm_f32(@builtin(global_invocation_id) gid: vec3<u32>) {
  let col: u32 = gid.x;
  let row: u32 = gid.y;
  if (col >= N || row >= M) { return; }
  var acc: f32 = 0.0f;
  for (var k: u32 = 0u; k < K; k = k + 1u) {
    let product: f32 = a[row * K + k] * b[k * N + col];
    acc = acc + product;
  }
  c[row * N + col] = acc;
}
