# Body compiler development journal

## First implementation, 2026-09-17

The original implementation selected a fixed GEMM template. It did not read
Lean function bodies, and the earlier description as a body compiler was
false. This implementation is separate: it traverses elaborated expressions,
recognizes only a documented arithmetic/index/fold grammar, and makes Lean
check a per-definition equality to the extracted tree.

Initial builds caught reserved identifiers and command-elaborator API mistakes.
Those were ordinary compiler errors, not proof failures. The first extraction
run compiled addition and multiplication but rejected the elaborated UInt32
zero in the two folds. Recognizing the elaborated literal before unfolding its
representation fixed this. All four equality theorems then checked, depending
only on `propext`.

The source operation mutation is material: two elementwise definitions and two
fold definitions differing at the arithmetic operation produced different
shader computations and different outputs. All four executed on the existing
native SwiftShader Vulkan CPU route. Their 24 output words matched the original
Lean definitions evaluated with the pure integer-defined IEEE32 operations.
Intermediate shaders, vectors and execution reports are ignored under
`build/wgsl/body-v1/`; no generated artifact is committed.

This checkpoint does not claim a proof about emitted text or arbitrary WebGPU
devices. The next check will parse actual emitted WGSL independently and make
the source equality refer to that parsed computation.
