// Lean body compiler: binary32 word interface
const M: u32 = 2u;
const N: u32 = 3u;
@group(0) @binding(0) var<storage, read> a: array<f32>;
@group(0) @binding(1) var<storage, read> b: array<f32>;
@group(0) @binding(2) var<storage, read_write> c: array<f32>;
@compute @workgroup_size(8, 8, 1)
fn lean_kernel(@builtin(global_invocation_id) gid: vec3<u32>) {
  let col: u32 = gid.x;
  let row: u32 = gid.y;
  if (col >= N || row >= M) { return; }
  let v0: f32 = a[((row * 3u) + col)];
  let v1: f32 = b[((row * 3u) + col)];
  let v2: f32 = v0 + v1;
  c[row * N + col] = v2;
}
