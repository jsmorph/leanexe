// Two-pass mean and uncentered Gram reduction. One workgroup handles one
// output entry and one 256-observation block. No floating-point atomics.
struct Params { rows: u32, width: u32, blocks: u32, entries: u32 }
@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> samples: array<f32>;
@group(0) @binding(2) var<storage, read_write> partials: array<f32>;
@group(0) @binding(3) var<storage, read_write> moments: array<f32>;
var<workgroup> scratch: array<f32, 256>;

@compute @workgroup_size(256)
fn partial(@builtin(workgroup_id) group: vec3<u32>,
           @builtin(local_invocation_index) lane: u32) {
  let entry = group.x;
  let row = group.y * 256u + lane;
  var term = 0.0;
  if row < params.rows {
    if entry < params.width {
      term = samples[row * params.width + entry];
    } else {
      let index = entry - params.width;
      let j = index / params.width;
      let k = index % params.width;
      term = samples[row * params.width + j] * samples[row * params.width + k];
    }
  }
  scratch[lane] = term;
  workgroupBarrier();
  for (var stride = 128u; stride > 0u; stride = stride / 2u) {
    if lane < stride { scratch[lane] = scratch[lane] + scratch[lane + stride]; }
    workgroupBarrier();
  }
  if lane == 0u { partials[entry * params.blocks + group.y] = scratch[0]; }
}

@compute @workgroup_size(256)
fn finish(@builtin(workgroup_id) group: vec3<u32>,
          @builtin(local_invocation_index) lane: u32) {
  let entry = group.x;
  var total = 0.0;
  for (var block = lane; block < params.blocks; block = block + 256u) {
    total = total + partials[entry * params.blocks + block];
  }
  scratch[lane] = total;
  workgroupBarrier();
  for (var stride = 128u; stride > 0u; stride = stride / 2u) {
    if lane < stride { scratch[lane] = scratch[lane] + scratch[lane + stride]; }
    workgroupBarrier();
  }
  if lane == 0u { moments[entry] = scratch[0] / f32(params.rows); }
}
