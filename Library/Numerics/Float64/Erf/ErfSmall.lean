import Library.Numerics.Float64.Erf.ErfSmallPieces1

/-!
One step for `erf` on the first range `[2^-28, 0.84375]` for positive arguments, from the intervals
of `ErfSmallPieces0` and `ErfSmallPieces1`.
-/

namespace Library.Numerics.Float64.Erf.ErfSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner ErfSmallBase RealErf ErfSmallPieces0 ErfSmallPieces1

theorem small_erf (X : UInt64) (hX : Finite X) (hlo : 1 / (2 : ℝ) ^ 28 ≤ value X)
    (hhi : value X ≤ 27 / 32) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) := by
  have hx0 : 0 < value X := lt_of_lt_of_le (by positivity) hlo
  rcases le_or_gt (value X) ((1 / 134217728 : ℚ) : ℝ) with h0 | h0
  · exact erf0 X hX hx0 (by rw [show ((1 / 268435456 : ℚ) : ℝ) = 1 / 2 ^ 28 by norm_num]; exact hlo) h0
  rcases le_or_gt (value X) ((1 / 67108864 : ℚ) : ℝ) with h1 | h1
  · exact erf1 X hX hx0 (le_of_lt h0) h1
  rcases le_or_gt (value X) ((1 / 33554432 : ℚ) : ℝ) with h2 | h2
  · exact erf2 X hX hx0 (le_of_lt h1) h2
  rcases le_or_gt (value X) ((1 / 16777216 : ℚ) : ℝ) with h3 | h3
  · exact erf3 X hX hx0 (le_of_lt h2) h3
  rcases le_or_gt (value X) ((1 / 8388608 : ℚ) : ℝ) with h4 | h4
  · exact erf4 X hX hx0 (le_of_lt h3) h4
  rcases le_or_gt (value X) ((1 / 4194304 : ℚ) : ℝ) with h5 | h5
  · exact erf5 X hX hx0 (le_of_lt h4) h5
  rcases le_or_gt (value X) ((1 / 2097152 : ℚ) : ℝ) with h6 | h6
  · exact erf6 X hX hx0 (le_of_lt h5) h6
  rcases le_or_gt (value X) ((1 / 1048576 : ℚ) : ℝ) with h7 | h7
  · exact erf7 X hX hx0 (le_of_lt h6) h7
  rcases le_or_gt (value X) ((1 / 524288 : ℚ) : ℝ) with h8 | h8
  · exact erf8 X hX hx0 (le_of_lt h7) h8
  rcases le_or_gt (value X) ((1 / 262144 : ℚ) : ℝ) with h9 | h9
  · exact erf9 X hX hx0 (le_of_lt h8) h9
  rcases le_or_gt (value X) ((1 / 131072 : ℚ) : ℝ) with h10 | h10
  · exact erf10 X hX hx0 (le_of_lt h9) h10
  rcases le_or_gt (value X) ((1 / 65536 : ℚ) : ℝ) with h11 | h11
  · exact erf11 X hX hx0 (le_of_lt h10) h11
  rcases le_or_gt (value X) ((1 / 32768 : ℚ) : ℝ) with h12 | h12
  · exact erf12 X hX hx0 (le_of_lt h11) h12
  rcases le_or_gt (value X) ((1 / 16384 : ℚ) : ℝ) with h13 | h13
  · exact erf13 X hX hx0 (le_of_lt h12) h13
  rcases le_or_gt (value X) ((1 / 8192 : ℚ) : ℝ) with h14 | h14
  · exact erf14 X hX hx0 (le_of_lt h13) h14
  rcases le_or_gt (value X) ((1 / 4096 : ℚ) : ℝ) with h15 | h15
  · exact erf15 X hX hx0 (le_of_lt h14) h15
  rcases le_or_gt (value X) ((1 / 2048 : ℚ) : ℝ) with h16 | h16
  · exact erf16 X hX hx0 (le_of_lt h15) h16
  rcases le_or_gt (value X) ((1 / 1024 : ℚ) : ℝ) with h17 | h17
  · exact erf17 X hX hx0 (le_of_lt h16) h17
  rcases le_or_gt (value X) ((1 / 512 : ℚ) : ℝ) with h18 | h18
  · exact erf18 X hX hx0 (le_of_lt h17) h18
  rcases le_or_gt (value X) ((1 / 256 : ℚ) : ℝ) with h19 | h19
  · exact erf19 X hX hx0 (le_of_lt h18) h19
  rcases le_or_gt (value X) ((1 / 128 : ℚ) : ℝ) with h20 | h20
  · exact erf20 X hX hx0 (le_of_lt h19) h20
  rcases le_or_gt (value X) ((1 / 64 : ℚ) : ℝ) with h21 | h21
  · exact erf21 X hX hx0 (le_of_lt h20) h21
  rcases le_or_gt (value X) ((1 / 32 : ℚ) : ℝ) with h22 | h22
  · exact erf22 X hX hx0 (le_of_lt h21) h22
  rcases le_or_gt (value X) ((1 / 16 : ℚ) : ℝ) with h23 | h23
  · exact erf23 X hX hx0 (le_of_lt h22) h23
  rcases le_or_gt (value X) ((1 / 8 : ℚ) : ℝ) with h24 | h24
  · exact erf24 X hX hx0 (le_of_lt h23) h24
  rcases le_or_gt (value X) ((1 / 4 : ℚ) : ℝ) with h25 | h25
  · exact erf25 X hX hx0 (le_of_lt h24) h25
  rcases le_or_gt (value X) ((17 / 64 : ℚ) : ℝ) with h26 | h26
  · exact erf26 X hX hx0 (le_of_lt h25) h26
  rcases le_or_gt (value X) ((9 / 32 : ℚ) : ℝ) with h27 | h27
  · exact erf27 X hX hx0 (le_of_lt h26) h27
  rcases le_or_gt (value X) ((19 / 64 : ℚ) : ℝ) with h28 | h28
  · exact erf28 X hX hx0 (le_of_lt h27) h28
  rcases le_or_gt (value X) ((5 / 16 : ℚ) : ℝ) with h29 | h29
  · exact erf29 X hX hx0 (le_of_lt h28) h29
  rcases le_or_gt (value X) ((21 / 64 : ℚ) : ℝ) with h30 | h30
  · exact erf30 X hX hx0 (le_of_lt h29) h30
  rcases le_or_gt (value X) ((11 / 32 : ℚ) : ℝ) with h31 | h31
  · exact erf31 X hX hx0 (le_of_lt h30) h31
  rcases le_or_gt (value X) ((23 / 64 : ℚ) : ℝ) with h32 | h32
  · exact erf32 X hX hx0 (le_of_lt h31) h32
  rcases le_or_gt (value X) ((3 / 8 : ℚ) : ℝ) with h33 | h33
  · exact erf33 X hX hx0 (le_of_lt h32) h33
  rcases le_or_gt (value X) ((25 / 64 : ℚ) : ℝ) with h34 | h34
  · exact erf34 X hX hx0 (le_of_lt h33) h34
  rcases le_or_gt (value X) ((13 / 32 : ℚ) : ℝ) with h35 | h35
  · exact erf35 X hX hx0 (le_of_lt h34) h35
  rcases le_or_gt (value X) ((27 / 64 : ℚ) : ℝ) with h36 | h36
  · exact erf36 X hX hx0 (le_of_lt h35) h36
  rcases le_or_gt (value X) ((7 / 16 : ℚ) : ℝ) with h37 | h37
  · exact erf37 X hX hx0 (le_of_lt h36) h37
  rcases le_or_gt (value X) ((29 / 64 : ℚ) : ℝ) with h38 | h38
  · exact erf38 X hX hx0 (le_of_lt h37) h38
  rcases le_or_gt (value X) ((15 / 32 : ℚ) : ℝ) with h39 | h39
  · exact erf39 X hX hx0 (le_of_lt h38) h39
  rcases le_or_gt (value X) ((31 / 64 : ℚ) : ℝ) with h40 | h40
  · exact erf40 X hX hx0 (le_of_lt h39) h40
  rcases le_or_gt (value X) ((1 / 2 : ℚ) : ℝ) with h41 | h41
  · exact erf41 X hX hx0 (le_of_lt h40) h41
  rcases le_or_gt (value X) ((33 / 64 : ℚ) : ℝ) with h42 | h42
  · exact erf42 X hX hx0 (le_of_lt h41) h42
  rcases le_or_gt (value X) ((17 / 32 : ℚ) : ℝ) with h43 | h43
  · exact erf43 X hX hx0 (le_of_lt h42) h43
  rcases le_or_gt (value X) ((35 / 64 : ℚ) : ℝ) with h44 | h44
  · exact erf44 X hX hx0 (le_of_lt h43) h44
  rcases le_or_gt (value X) ((9 / 16 : ℚ) : ℝ) with h45 | h45
  · exact erf45 X hX hx0 (le_of_lt h44) h45
  rcases le_or_gt (value X) ((37 / 64 : ℚ) : ℝ) with h46 | h46
  · exact erf46 X hX hx0 (le_of_lt h45) h46
  rcases le_or_gt (value X) ((19 / 32 : ℚ) : ℝ) with h47 | h47
  · exact erf47 X hX hx0 (le_of_lt h46) h47
  rcases le_or_gt (value X) ((39 / 64 : ℚ) : ℝ) with h48 | h48
  · exact erf48 X hX hx0 (le_of_lt h47) h48
  rcases le_or_gt (value X) ((5 / 8 : ℚ) : ℝ) with h49 | h49
  · exact erf49 X hX hx0 (le_of_lt h48) h49
  rcases le_or_gt (value X) ((41 / 64 : ℚ) : ℝ) with h50 | h50
  · exact erf50 X hX hx0 (le_of_lt h49) h50
  rcases le_or_gt (value X) ((21 / 32 : ℚ) : ℝ) with h51 | h51
  · exact erf51 X hX hx0 (le_of_lt h50) h51
  rcases le_or_gt (value X) ((43 / 64 : ℚ) : ℝ) with h52 | h52
  · exact erf52 X hX hx0 (le_of_lt h51) h52
  rcases le_or_gt (value X) ((11 / 16 : ℚ) : ℝ) with h53 | h53
  · exact erf53 X hX hx0 (le_of_lt h52) h53
  rcases le_or_gt (value X) ((45 / 64 : ℚ) : ℝ) with h54 | h54
  · exact erf54 X hX hx0 (le_of_lt h53) h54
  rcases le_or_gt (value X) ((23 / 32 : ℚ) : ℝ) with h55 | h55
  · exact erf55 X hX hx0 (le_of_lt h54) h55
  rcases le_or_gt (value X) ((47 / 64 : ℚ) : ℝ) with h56 | h56
  · exact erf56 X hX hx0 (le_of_lt h55) h56
  rcases le_or_gt (value X) ((3 / 4 : ℚ) : ℝ) with h57 | h57
  · exact erf57 X hX hx0 (le_of_lt h56) h57
  rcases le_or_gt (value X) ((97 / 128 : ℚ) : ℝ) with h58 | h58
  · exact erf58 X hX hx0 (le_of_lt h57) h58
  rcases le_or_gt (value X) ((49 / 64 : ℚ) : ℝ) with h59 | h59
  · exact erf59 X hX hx0 (le_of_lt h58) h59
  rcases le_or_gt (value X) ((99 / 128 : ℚ) : ℝ) with h60 | h60
  · exact erf60 X hX hx0 (le_of_lt h59) h60
  rcases le_or_gt (value X) ((25 / 32 : ℚ) : ℝ) with h61 | h61
  · exact erf61 X hX hx0 (le_of_lt h60) h61
  rcases le_or_gt (value X) ((101 / 128 : ℚ) : ℝ) with h62 | h62
  · exact erf62 X hX hx0 (le_of_lt h61) h62
  rcases le_or_gt (value X) ((51 / 64 : ℚ) : ℝ) with h63 | h63
  · exact erf63 X hX hx0 (le_of_lt h62) h63
  rcases le_or_gt (value X) ((103 / 128 : ℚ) : ℝ) with h64 | h64
  · exact erf64 X hX hx0 (le_of_lt h63) h64
  rcases le_or_gt (value X) ((13 / 16 : ℚ) : ℝ) with h65 | h65
  · exact erf65 X hX hx0 (le_of_lt h64) h65
  rcases le_or_gt (value X) ((209 / 256 : ℚ) : ℝ) with h66 | h66
  · exact erf66 X hX hx0 (le_of_lt h65) h66
  rcases le_or_gt (value X) ((105 / 128 : ℚ) : ℝ) with h67 | h67
  · exact erf67 X hX hx0 (le_of_lt h66) h67
  rcases le_or_gt (value X) ((211 / 256 : ℚ) : ℝ) with h68 | h68
  · exact erf68 X hX hx0 (le_of_lt h67) h68
  rcases le_or_gt (value X) ((53 / 64 : ℚ) : ℝ) with h69 | h69
  · exact erf69 X hX hx0 (le_of_lt h68) h69
  rcases le_or_gt (value X) ((213 / 256 : ℚ) : ℝ) with h70 | h70
  · exact erf70 X hX hx0 (le_of_lt h69) h70
  rcases le_or_gt (value X) ((107 / 128 : ℚ) : ℝ) with h71 | h71
  · exact erf71 X hX hx0 (le_of_lt h70) h71
  rcases le_or_gt (value X) ((215 / 256 : ℚ) : ℝ) with h72 | h72
  · exact erf72 X hX hx0 (le_of_lt h71) h72
  exact erf73 X hX hx0 (le_of_lt h72) (by rw [show ((27 / 32 : ℚ) : ℝ) = 27 / 32 by norm_num]; exact hhi)

#print axioms small_erf

end Library.Numerics.Float64.Erf.ErfSmall
