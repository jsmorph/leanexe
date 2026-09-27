# Singleton fold result from source frame

Rewrite the compiler-matched suffix to FixedArrayFold.singletonResultProgram, then apply singletonResultProgram_spec_to_fromFrame with generated source-frame accessors and local bounds. The theorem derives the result getter and preserved root getter on FixedArrayFold.resultFrame.
