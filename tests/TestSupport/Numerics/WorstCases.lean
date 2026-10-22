/-! The double-precision inputs that give the largest known errors of the libraries compared in
B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, "Accuracy of Mathematical
Functions in Single, Double, Double Extended, and Quadruple Precision", August 2026, Tables 4 to
11 (https://members.loria.fr/PZimmermann/papers/accuracy.pdf): GNU libc 2.44, the Intel Math
Library, AMD LibM, Newlib, OpenLibm, Musl, Apple's library, LLVM libc, MSVC, FreeBSD 15.1, the Arm
Performance Library, CUDA, and ROCm.  Each entry is the bit pattern of an input, with the
hexadecimal form and the tables that list it in its comment.  The pairs of `atan2` and `pow` are
the report's `(x, y)`, the first and second arguments in C's order.  The accuracy checks add these
inputs to their arguments. -/

namespace TestSupport.Numerics.WorstCases

/-- Inputs of `exp`. -/
def exp : Array UInt64 :=
  #[
    0xC0849F33AD2C1C58,  -- -0x1.49f33ad2c1c58p+9, Tables 4, 10
    0x404FCE66609F7428,  -- 0x1.fce66609f7428p+5, Table 4
    0x404B97DC8345C550,  -- 0x1.b97dc8345c55p+5, Table 6
    0x4072E8F20CF3CBE7,  -- 0x1.2e8f20cf3cbe7p+8, Tables 6, 7, 9
    0xC0518209ECD19A8C,  -- -0x1.18209ecd19a8cp+6, Table 7
    0xBF24133F4FD79C1C,  -- -0x1.4133f4fd79c1cp-13, Table 8
    0x3CA0000000000000,  -- 0x1p-53, Table 8
    0xBE4FFFFFFA000001,  -- -0x1.ffffffa000001p-27, Table 9
    0xC08625F1B359729E,  -- -0x1.625f1b359729ep+9, Table 11
    0xC08625F1C27780C8  -- -0x1.625f1c27780c8p+9, Table 11
  ]

/-- Inputs of `log`. -/
def log : Array UInt64 :=
  #[
    0x3FF1211BEF8F68E9,  -- 0x1.1211bef8f68e9p+0, Tables 4, 10
    0x3FF008000DB2E8BE,  -- 0x1.008000db2e8bep+0, Table 4
    0x3FF108058FED54B3,  -- 0x1.108058fed54b3p+0, Table 6
    0x3FF48AE5A67204F5,  -- 0x1.48ae5a67204f5p+0, Tables 6, 7, 9
    0x3FEDC0B586F2B260,  -- 0x1.dc0b586f2b26p-1, Table 7
    0x3FE490AF72A25A81,  -- 0x1.490af72a25a81p-1, Table 8
    0x4015B6E7E4E96F86,  -- 0x1.5b6e7e4e96f86p+2, Table 8
    0x3FF0FFC349469A2F,  -- 0x1.0ffc349469a2fp+0, Table 9
    0x3FE69E7AA6DA2DF5,  -- 0x1.69e7aa6da2df5p-1, Table 11
    0x3FE5556123E8A2B0  -- 0x1.5556123e8a2bp-1, Table 11
  ]

/-- Inputs of `expm1`. -/
def expm1 : Array UInt64 :=
  #[
    0x3FD63E063D879380,  -- 0x1.63e063d87938p-2, Table 4
    0xBF762FE464C64F65,  -- -0x1.62fe464c64f65p-8, Table 4
    0x3FD9A5796C0B73B8,  -- 0x1.9a5796c0b73b8p-2, Table 6
    0x3FD62FF47A01658F,  -- 0x1.62ff47a01658fp-2, Tables 6, 7, 9
    0x3FAE7F93188565EC,  -- 0x1.e7f93188565ecp-5, Table 8
    0x3CB0000000000000,  -- 0x1p-52, Table 8
    0xBFE62D7C116D2E32,  -- -0x1.62d7c116d2e32p-1, Table 9
    0x3FD633F993A730C9,  -- 0x1.633f993a730c9p-2, Table 10
    0x3FDA0E95D59498E9,  -- 0x1.a0e95d59498e9p-2, Table 11
    0x3FD6339EA76A70CA  -- 0x1.6339ea76a70cap-2, Table 11
  ]

/-- Inputs of `tanh`. -/
def tanh : Array UInt64 :=
  #[
    0x3E4D12ED0AF1A27F,  -- 0x1.d12ed0af1a27fp-27, Table 4
    0x3FF002629FD74484,  -- 0x1.002629fd74484p+0, Table 4
    0xBFEFDE5BD2769A01,  -- -0x1.fde5bd2769a01p-1, Table 6
    0xBFCE134557098E37,  -- -0x1.e134557098e37p-3, Tables 6, 7, 9
    0x40000CF9F273D840,  -- 0x1.00cf9f273d84p+1, Table 8
    0x3FEFEFC7206BC932,  -- 0x1.fefc7206bc932p-1, Table 9
    0xBFCC416448380DEB,  -- -0x1.c416448380debp-3, Table 10
    0xBFE19398A9A24319,  -- -0x1.19398a9a24319p-1, Table 11
    0x3FB004A396A065E3  -- 0x1.004a396a065e3p-4, Table 11
  ]

/-- Inputs of `sin`. -/
def sin : Array UInt64 :=
  #[
    0xC03F8B791CAFCDEF,  -- -0x1.f8b791cafcdefp+4, Table 4
    0xFAF0E16EB809A35D,  -- -0x1.0e16eb809a35dp+944, Table 4
    0x4149EB7148F354D6,  -- 0x1.9eb7148f354d6p+21, Table 6
    0xC14842D8EC8F752F,  -- -0x1.842d8ec8f752fp+21, Table 6
    0x4144D84DB080B9FD,  -- 0x1.4d84db080b9fdp+21, Tables 7, 9
    0xC0307E4C92B5349D,  -- -0x1.07e4c92b5349dp+4, Table 8
    0x3F71031FB0196180,  -- 0x1.1031fb019618p-8, Table 8
    0xC0811B624B546894,  -- -0x1.11b624b546894p+9, Table 9
    0xC121C49AD613FF3B,  -- -0x1.1c49ad613ff3bp+19, Table 11
    0xC04F05ED802C1CC7  -- -0x1.f05ed802c1cc7p+5, Table 11
  ]

/-- Inputs of `cos`. -/
def cos : Array UInt64 :=
  #[
    0xBFF7120161C92674,  -- -0x1.7120161c92674p+0, Table 4
    0xD36D19EBC5567DCD,  -- -0x1.d19ebc5567dcdp+311, Table 4
    0x4139EB7148F354D6,  -- 0x1.9eb7148f354d6p+20, Table 6
    0xC144AE182C1AB422,  -- -0x1.4ae182c1ab422p+21, Table 6
    0xC1434E729FD08086,  -- -0x1.34e729fd08086p+21, Tables 7, 9
    0x4062F29EB4E99FA2,  -- 0x1.2f29eb4e99fa2p+7, Table 8
    0x3FB16E534EE36580,  -- 0x1.16e534ee3658p-4, Table 8
    0xBFE9200634D4471F,  -- -0x1.9200634d4471fp-1, Table 9
    0x41325133CA3904DF,  -- 0x1.25133ca3904dfp+20, Table 11
    0x4002A33AE1A620B1  -- 0x1.2a33ae1a620b1p+1, Table 11
  ]

/-- Inputs of `log1p`. -/
def log1p : Array UInt64 :=
  #[
    0xBFD2BF183E0344B2,  -- -0x1.2bf183e0344b2p-2, Table 4
    0x3F6000AEE2A2757F,  -- 0x1.000aee2a2757fp-9, Table 4
    0x3FBE0013FD35CBB0,  -- 0x1.e0013fd35cbbp-4, Table 6
    0xBFD2BF1DE6B04A8A,  -- -0x1.2bf1de6b04a8ap-2, Tables 6, 7, 9
    0xBFD2BF32AAF122E2,  -- -0x1.2bf32aaf122e2p-2, Table 7
    0xBE3FFFFFF3FFFFFD,  -- -0x1.ffffff3fffffdp-28, Table 8
    0x3CA0000000000000,  -- 0x1p-53, Table 8
    0xBCA8000000000000,  -- -0x1.8000000000000p-53, Table 9
    0xBFD2E496D25897EC,  -- -0x1.2e496d25897ecp-2, Table 10
    0xBFDFFFFFFBAEFE27,  -- -0x1.ffffffbaefe27p-2, Table 11
    0x8015EFAD5491A79B  -- -0x1.5efad5491a79bp-1022, Table 11
  ]

/-- Inputs of `atan`. -/
def atan : Array UInt64 :=
  #[
    0x3FBF9004C4FEF9EA,  -- 0x1.f9004c4fef9eap-4, Table 4
    0xBF8FFFF8020D3D1D,  -- -0x1.ffff8020d3d1dp-7, Table 4
    0xBFE60370D15396B7,  -- -0x1.60370d15396b7p-1, Tables 6, 9
    0x3FE62FF6A1682C25,  -- 0x1.62ff6a1682c25p-1, Tables 6, 7, 9
    0x40001E0BE37AF68F,  -- 0x1.01e0be37af68fp+1, Table 8
    0xBFF085B3FDB46CB0,  -- -0x1.085b3fdb46cbp+0, Table 8
    0x3FF032B4811F3DC5,  -- 0x1.032b4811f3dc5p+0, Table 10
    0x3FF52184B1B9BD9B,  -- 0x1.52184b1b9bd9bp+0, Table 11
    0x3FF00BB805435CCF  -- 0x1.00bb805435ccfp+0, Table 11
  ]

/-- Inputs of `asin`. -/
def asin : Array UInt64 :=
  #[
    0xBFC0000045B2C904,  -- -0x1.0000045b2c904p-3, Table 4
    0x3FE6C042A6378102,  -- 0x1.6c042a6378102p-1, Table 4
    0xBFE00D44CCCFA990,  -- -0x1.00d44cccfa99p-1, Table 6
    0xBFE004D1C5A9400B,  -- -0x1.004d1c5a9400bp-1, Tables 6, 7, 9
    0x3FDEAECA101513D2,  -- 0x1.eaeca101513d2p-2, Table 8
    0xBE57137449123EF6,  -- -0x1.7137449123ef6p-26, Table 8
    0x3FE003D8C089658B,  -- 0x1.003d8c089658bp-1, Table 9
    0x3FE0479B37D95E5C,  -- 0x1.0479b37d95e5cp-1, Table 10
    0xBFE2EF2481799C7C,  -- -0x1.2ef2481799c7cp-1, Table 11
    0x3FDDF2C6032ADCD8  -- 0x1.df2c6032adcd8p-2, Table 11
  ]

/-- Inputs of `acos`. -/
def acos : Array UInt64 :=
  #[
    0x3FEDFFFFB3488A40,  -- 0x1.dffffb3488a4p-1, Table 4
    0x3FE6C05EB219EC46,  -- 0x1.6c05eb219ec46p-1, Table 4
    0x3FE35B03E336A82B,  -- 0x1.35b03e336a82bp-1, Table 6
    0xBFE0068B067C6FEE,  -- -0x1.0068b067c6feep-1, Tables 6, 7, 9
    0xBCA8D313198A2E03,  -- -0x1.8d313198a2e03p-53, Table 8
    0xBC8CB3B399D747F3,  -- -0x1.cb3b399d747f3p-55, Table 8
    0xBFE01F97A9D82A5D,  -- -0x1.01f97a9d82a5dp-1, Table 9
    0x3FE251869C3F7881,  -- 0x1.251869c3f7881p-1, Table 10
    0x3FE266637A3D2BBC,  -- 0x1.266637a3d2bbcp-1, Table 11
    0xBFE3702DC3201849  -- -0x1.3702dc3201849p-1, Table 11
  ]

/-- Inputs of `tan`. -/
def tan : Array UInt64 :=
  #[
    0xC08317CD745DD37C,  -- -0x1.317cd745dd37cp+9, Table 4
    0x41149ADFD996A81D,  -- 0x1.49adfd996a81dp+18, Table 4
    0x41193C05C9ED3CBC,  -- 0x1.93c05c9ed3cbcp+18, Table 6
    0x4143F9605AAEB51B,  -- 0x1.3f9605aaeb51bp+21, Tables 6, 7, 9
    0xC05A81D98FC58537,  -- -0x1.a81d98fc58537p+6, Table 8
    0xFEF13A5CCD87C9BB,  -- -0x1.13a5ccd87c9bbp+1008, Table 8
    0xC0A4D7C8B8320237,  -- -0x1.4d7c8b8320237p+11, Table 9
    0x40ADA7A85A88BBEC,  -- 0x1.da7a85a88bbecp+11, Table 11
    0x40D5A7EE2AB3840C  -- 0x1.5a7ee2ab3840cp+14, Table 11
  ]

/-- Inputs of `sinh`. -/
def sinh : Array UInt64 :=
  #[
    0x4042B705C15ABEB9,  -- 0x1.2b705c15abeb9p+5, Table 4
    0xBFDADC135EB544C1,  -- -0x1.adc135eb544c1p-2, Table 4
    0x4021FEB2A79F3070,  -- 0x1.1feb2a79f307p+3, Table 6
    0xC08633CAE1335F26,  -- -0x1.633cae1335f26p+9, Table 6
    0xBFE63324AF2FB5B7,  -- -0x1.63324af2fb5b7p-1, Tables 7, 9
    0x3FDD7131E11FC6B3,  -- 0x1.d7131e11fc6b3p-2, Table 8
    0x4021FD8C752E39F5,  -- 0x1.1fd8c752e39f5p+3, Table 9
    0x3FD9FA32B1149D35,  -- 0x1.9fa32b1149d35p-2, Table 10
    0x3FFBDE0CD0EFDEF8,  -- 0x1.bde0cd0efdef8p+0, Table 11
    0x3FAFFA5D2E7B5000  -- 0x1.ffa5d2e7b5p-5, Table 11
  ]

/-- Inputs of `cosh`. -/
def cosh : Array UInt64 :=
  #[
    0x3E50000000000000,  -- 0x1p-26, Table 4
    0xC085A364E6B98134,  -- -0x1.5a364e6b98134p+9, Table 4
    0x3FFFF76FB3F476D5,  -- 0x1.ff76fb3f476d5p+0, Table 6
    0x408633CC2AE1C934,  -- 0x1.633cc2ae1c934p+9, Table 6
    0xC086310AB92794A8,  -- -0x1.6310ab92794a8p+9, Tables 7, 9
    0xBFF502BF5AD80729,  -- -0x1.502bf5ad80729p+0, Table 7
    0xBFD62DABD4848DC4,  -- -0x1.62dabd4848dc4p-2, Table 8
    0x3FFED991002DC978,  -- 0x1.ed991002dc978p+0, Table 9
    0xC08628AF341989DA,  -- -0x1.628af341989dap+9, Table 10
    0x400E7FFE229FE99E,  -- 0x1.e7ffe229fe99ep+1, Table 11
    0xC00E7F9C78A5C332  -- -0x1.e7f9c78a5c332p+1, Table 11
  ]

/-- Inputs of `asinh`. -/
def asinh : Array UInt64 :=
  #[
    0xBE57137449123EF7,  -- -0x1.7137449123ef7p-26, Table 4
    0xBFB000276D9CF31A,  -- -0x1.000276d9cf31ap-4, Table 4
    0x3FF005AE8D126F7E,  -- 0x1.005ae8d126f7ep+0, Table 6
    0xBFD02657FF36D5F3,  -- -0x1.02657ff36d5f3p-2, Tables 6, 7, 9
    0xBFD0240F2BDB3F25,  -- -0x1.0240f2bdb3f25p-2, Table 7
    0xBFCFDEFD03DF4CD7,  -- -0x1.fdefd03df4cd7p-3, Table 8
    0xBFB00212BB59C31E,  -- -0x1.00212bb59c31ep-4, Table 9
    0xBFF000EEED78380A,  -- -0x1.000eeed78380ap+0, Table 10
    0xBFE8190E51C77D16,  -- -0x1.8190e51c77d16p-1, Table 11
    0x3FD2AAB2F0A9D9D0  -- 0x1.2aab2f0a9d9dp-2, Table 11
  ]

/-- Inputs of `acosh`. -/
def acosh : Array UInt64 :=
  #[
    0x7B5C29124EA23A1C,  -- 0x1.c29124ea23a1cp+950, Table 4
    0x3FF01825CA7DA7E5,  -- 0x1.01825ca7da7e5p+0, Table 4
    0x3FF209FAE707A0ED,  -- 0x1.209fae707a0edp+0, Table 6
    0x3FF0001FF6AFC4BA,  -- 0x1.0001ff6afc4bap+0, Tables 6, 7, 9
    0xC1434E729FD08086,  -- -0x1.34e729fd08086p+21, Table 7
    0x3FF00007FB3703DD,  -- 0x1.00007fb3703ddp+0, Table 8
    0x3FF0007FD4307B75,  -- 0x1.0007fd4307b75p+0, Table 9
    0x3FF071334DAF83AD,  -- 0x1.071334daf83adp+0, Table 10
    0x3FF1D7BC19163966,  -- 0x1.1d7bc19163966p+0, Table 11
    0x3FF0AAADE11E199A  -- 0x1.0aaade11e199ap+0, Table 11
  ]

/-- Inputs of `atanh`. -/
def atanh : Array UInt64 :=
  #[
    0x3E5A6A58D55E307B,  -- 0x1.a6a58d55e307bp-26, Table 4
    0xBF6E2CFB2667F17E,  -- -0x1.e2cfb2667f17ep-9, Table 4
    0xBFDD8FB311A52173,  -- -0x1.d8fb311a52173p-2, Table 6
    0xBFBF97FABC0650C4,  -- -0x1.f97fabc0650c4p-4, Tables 6, 7, 9
    0xBFBF8A404597BAF4,  -- -0x1.f8a404597baf4p-4, Table 7
    0x3F5FFD834A270F00,  -- 0x1.ffd834a270fp-10, Table 8
    0xBF6FFBE8DD88527F,  -- -0x1.ffbe8dd88527fp-9, Table 9
    0xBFBE7C1F36602014,  -- -0x1.e7c1f36602014p-4, Table 10
    0xBFCF586714622A66,  -- -0x1.f586714622a66p-3, Table 11
    0xBFC2493FECD07E50  -- -0x1.2493fecd07e5p-3, Table 11
  ]

/-- Inputs of `exp2`. -/
def exp2 : Array UInt64 :=
  #[
    0xBFA1A4CE073EA908,  -- -0x1.1a4ce073ea908p-5, Tables 4, 7
    0xBF98002F29666B99,  -- -0x1.8002f29666b99p-6, Table 4
    0x408FFFBFF4152BAF,  -- 0x1.fffbff4152bafp+9, Table 6
    0xBFDFF95ECB4E6331,  -- -0x1.ff95ecb4e6331p-2, Table 6
    0xC08FF1EB5ACEE46B,  -- -0x1.ff1eb5acee46bp+9, Tables 7, 9
    0xBF2B3D9B47AD1B2F,  -- -0x1.b3d9b47ad1b2fp-13, Table 8
    0x3CA71547652B82FE,  -- 0x1.71547652b82fep-53, Table 8
    0xC08E383CA1FD4462,  -- -0x1.e383ca1fd4462p+9, Table 9
    0xC08F7087FB1CF9E8,  -- -0x1.f7087fb1cf9e8p+9, Table 10
    0xC08FF40169BD093B,  -- -0x1.ff40169bd093bp+9, Table 11
    0xC08FF3E09D141586  -- -0x1.ff3e09d141586p+9, Table 11
  ]

/-- Inputs of `exp10`. -/
def exp10 : Array UInt64 :=
  #[
    0xBF8585FADEAB79D4,  -- -0x1.585fadeab79d4p-7, Table 4
    0xC005CD9D94D49A85,  -- -0x1.5cd9d94d49a85p+1, Table 4
    0xC01285D82B75258F,  -- -0x1.285d82b75258fp+2, Table 6
    0x3FDCE7EF793D4B0A,  -- 0x1.ce7ef793d4b0ap-2, Table 6
    0xC02FE8C27141C94A,  -- -0x1.fe8c27141c94ap+3, Table 7
    0xBEFC37443E446523,  -- -0x1.c37443e446523p-16, Table 8
    0x3C8BCB7B1526E50D,  -- 0x1.bcb7b1526e50dp-55, Table 8
    0xBF85ACF96F42165B,  -- -0x1.5acf96f42165bp-7, Table 10
    0xBFFA7D980016DC5A,  -- -0x1.a7d980016dc5ap+0, Table 11
    0x3FF5C4992EE4319B  -- 0x1.5c4992ee4319bp+0, Table 11
  ]

/-- Inputs of `log2`. -/
def log2 : Array UInt64 :=
  #[
    0x3FF1406D79E1B574,  -- 0x1.1406d79e1b574p+0, Table 4
    0x3FEFEA11B9451F9B,  -- 0x1.fea11b9451f9bp-1, Table 4
    0x3FF0B541B6746BD1,  -- 0x1.0b541b6746bd1p+0, Table 6
    0x3FF68D778F076021,  -- 0x1.68d778f076021p+0, Table 6
    0x3FF67EAF07CE24D1,  -- 0x1.67eaf07ce24d1p+0, Tables 7, 9
    0x3FF0B53197BD66C8,  -- 0x1.0b53197bd66c8p+0, Table 7
    0x3FE6D0092BCF066D,  -- 0x1.6d0092bcf066dp-1, Table 8
    0x3FFB4EBE40C95A01,  -- 0x1.b4ebe40c95a01p+0, Table 8
    0x3FF160732376AD7F,  -- 0x1.160732376ad7fp+0, Table 9
    0x3FF0B53F741FB8C4,  -- 0x1.0b53f741fb8c4p+0, Table 10
    0x3FF670C5AA6680AB,  -- 0x1.670c5aa6680abp+0, Table 11
    0x3FF55571E90EE956  -- 0x1.55571e90ee956p+0, Table 11
  ]

/-- Inputs of `log10`. -/
def log10 : Array UInt64 :=
  #[
    0x3FEDE02157073B31,  -- 0x1.de02157073b31p-1, Tables 4, 10
    0x3FEFEDA7B62C1033,  -- 0x1.feda7b62c1033p-1, Table 4
    0x3FF10FDF4211FD45,  -- 0x1.10fdf4211fd45p+0, Table 6
    0x3FF55535A0140A21,  -- 0x1.55535a0140a21p+0, Table 6
    0x3FF553E1CB579EE9,  -- 0x1.553e1cb579ee9p+0, Tables 7, 9
    0x3FE2501EE5628B08,  -- 0x1.2501ee5628b08p-1, Table 8
    0x5ACE12D66744FF81,  -- 0x1.e12d66744ff81p+429, Table 8
    0x3FEE005E1E891807,  -- 0x1.e005e1e891807p-1, Table 9
    0x3FE803DEA263187F,  -- 0x1.803dea263187fp-1, Table 11
    0x3FF55558BF0B2328  -- 0x1.55558bf0b2328p+0, Table 11
  ]

/-- Inputs of `sinpi`. -/
def sinpi : Array UInt64 :=
  #[
    0xBF845F3E53E1D707,  -- -0x1.45f3e53e1d707p-7, Table 4
    0x00007F16EC91C164,  -- 0x0.07f16ec91c164p-1022, Table 4
    0xBF1FFFFED20CA4DE,  -- -0x1.ffffed20ca4dep-14, Table 6
    0x3FC54C657059AE8D,  -- 0x1.54c657059ae8dp-3, Table 8
    0x3FF400AD6F5900EF,  -- 0x1.400ad6f5900efp+0, Table 9
    0xBFE00000D362CD4D,  -- -0x1.00000d362cd4dp-1, Table 10
    0xBFB4778E04770C45,  -- -0x1.4778e04770c45p-4, Table 11
    0x3FD0092557AF9571  -- 0x1.0092557af9571p-2, Table 11
  ]

/-- Inputs of `cospi`. -/
def cospi : Array UInt64 :=
  #[
    0xC051A0A2FA299B92,  -- -0x1.1a0a2fa299b92p+6, Table 4
    0xBF7F01D619F61E5B,  -- -0x1.f01d619f61e5bp-8, Table 4
    0xBE3FFFFFFFFFFFFF,  -- -0x1.fffffffffffffp-28, Table 6
    0xBFE554BB66EDE184,  -- -0x1.554bb66ede184p-1, Table 8
    0xBFCFE3BB5207682D,  -- -0x1.fe3bb5207682dp-3, Table 9
    0x3E95A33CC2580000,  -- 0x1.5a33cc258p-22, Table 10
    0x3FDADD84BAC106B1,  -- 0x1.add84bac106b1p-2, Table 11
    0x3FCFF9AFE723DE93  -- 0x1.ff9afe723de93p-3, Table 11
  ]

/-- Inputs of `tanpi`. -/
def tanpi : Array UInt64 :=
  #[
    0xBFDFAE7D0EF22D4E,  -- -0x1.fae7d0ef22d4ep-2, Table 4
    0x42D49B79692667B0,  -- 0x1.49b79692667bp+46, Table 4
    0x3F0FFFFCE32E4A7C,  -- 0x1.ffffce32e4a7cp-15, Table 6
    0xBFCFE9EB8D802C61,  -- -0x1.fe9eb8d802c61p-3, Table 8
    0x3FFC9542A6E8F18F,  -- 0x1.c9542a6e8f18fp+0, Table 9
    0x3FD68BF660EEA820  -- 0x1.68bf660eea82p-2, Table 10
  ]

/-- Inputs of `erf`. -/
def erf : Array UInt64 :=
  #[
    0x9E46E9B204D2167D,  -- -0x1.6e9b204d2167dp-539, Table 4
    0xBFF386615790C013,  -- -0x1.386615790c013p+0, Table 4
    0x3FF11642F2EAB9ED,  -- 0x1.11642f2eab9edp+0, Table 6
    0xBEFC57541B55C8EB,  -- -0x1.c57541b55c8ebp-16, Tables 6, 7, 9
    0xBFDE057E7A0E494C,  -- -0x1.e057e7a0e494cp-2, Table 8
    0xBF7BF3C82E5F58DF,  -- -0x1.bf3c82e5f58dfp-8, Table 9
    0x3F70000187085E56,  -- 0x1.0000187085e56p-8, Table 10
    0x3FD340FF534D52BF,  -- 0x1.340ff534d52bfp-2, Table 11
    0xBFF10C4C3D3B6CDB  -- -0x1.10c4c3d3b6cdbp+0, Table 11
  ]

/-- Inputs of `erfc`. -/
def erfc : Array UInt64 :=
  #[
    0xBC9C5BF891B4EF6A,  -- -0x1.c5bf891b4ef6ap-54, Table 4
    0x403A8CF81FA2A28F,  -- 0x1.a8cf81fa2a28fp+4, Table 4
    0x3FF3BCE0A408603F,  -- 0x1.3bce0a408603fp+0, Table 6
    0x3FF5182D8799B84B,  -- 0x1.5182d8799b84bp+0, Tables 6, 7, 9
    0x3FF527F4FB0D9331,  -- 0x1.527f4fb0d9331p+0, Table 7
    0x400BBA14DC3507CC,  -- 0x1.bba14dc3507ccp+1, Table 8
    0x400F5C5A6822A341,  -- 0x1.f5c5a6822a341p+1, Table 9
    0x40346CFFDF330B13,  -- 0x1.46cffdf330b13p+4, Table 10
    0x3F88659A03B35ABC,  -- 0x1.8659a03b35abcp-7, Table 11
    0x3ECF1ED3A0316EAB  -- 0x1.f1ed3a0316eabp-19, Table 11
  ]

/-- Inputs of `lgamma`. -/
def lgamma : Array UInt64 :=
  #[
    0x00000000002F6806,  -- 0x0.00000002f6806p-1022, Table 4
    0xC013F62C60E23B31,  -- -0x1.3f62c60e23b31p+2, Table 4
    0xC003A7FC9600F86C,  -- -0x1.3a7fc9600f86cp+1, Tables 6, 7, 9, 11
    0xC01BFFCBF76B86F0,  -- -0x1.bffcbf76b86fp+2, Table 8
    0xC01BFFE071EEA741,  -- -0x1.bffe071eea741p+2, Table 9
    0xC00FA471547C2FE5  -- -0x1.fa471547c2fe5p+1, Table 11
  ]

/-- Inputs of `tgamma`. -/
def tgamma : Array UInt64 :=
  #[
    0x1418B9710D0ADF83,  -- 0x1.8b9710d0adf83p-702, Table 4
    0xC053E0001AD3BEE3,  -- -0x1.3e0001ad3bee3p+6, Table 4
    0xC06535175475CC8D,  -- -0x1.535175475cc8dp+7, Table 6
    0xC06540B170C4E65E,  -- -0x1.540b170c4e65ep+7, Table 7
    0xC01FC4B534C8ECC0,  -- -0x1.fc4b534c8eccp+2, Table 7
    0xC065456E56919A19,  -- -0x1.5456e56919a19p+7, Table 8
    0xC065C00000003C15,  -- -0x1.5c00000003c15p+7, Table 9
    0xC06547CF3DDAADDA,  -- -0x1.547cf3ddaaddap+7, Table 9
    0xC062BAA17692A3F2,  -- -0x1.2baa17692a3f2p+7, Table 11
    0xC02E7B39F8D17722  -- -0x1.e7b39f8d17722p+3, Table 11
  ]

/-- Inputs of `j0`. -/
def j0 : Array UInt64 :=
  #[
    0x40033D152E971B40,  -- 0x1.33d152e971b4p+1, Tables 4, 7, 9
    0x406AFF859518C846,  -- 0x1.aff859518c846p+7, Table 4
    0x74E45F3067A0F4B2,  -- 0x1.45f3067a0f4b2p+847, Table 6
    0xC0033D152E971B40,  -- -0x1.33d152e971b4p+1, Table 7
    0x4016148F5B2C2E45,  -- 0x1.6148f5b2c2e45p+2, Table 8
    0x441782B7A20DF6D4,  -- 0x1.782b7a20df6d4p+66, Table 9
    0xC180E126BBCB3E65,  -- -0x1.0e126bbcb3e65p+25, Table 11
    0x402DDCA13EF271D2  -- 0x1.ddca13ef271d2p+3, Table 11
  ]

/-- Inputs of `j1`. -/
def j1 : Array UInt64 :=
  #[
    0xC00EA75575AF6F09,  -- -0x1.ea75575af6f09p+1, Tables 4, 7, 8, 9
    0xC0667B5541C7D8B7,  -- -0x1.67b5541c7d8b7p+7, Table 4
    0x54445F3066F80258,  -- 0x1.45f3066f80258p+325, Table 6
    0x400EA75575AF6F09,  -- 0x1.ea75575af6f09p+1, Table 7
    0x44A99CAA5236FEEA,  -- 0x1.99caa5236feeap+75, Table 9
    0xC19635AB5A8BAF45,  -- -0x1.635ab5a8baf45p+26, Table 11
    0x402AA5BAF310E5A2  -- 0x1.aa5baf310e5a2p+3, Table 11
  ]

/-- Inputs of `y0`. -/
def y0 : Array UInt64 :=
  #[
    0x3FEC982EB8D417EA,  -- 0x1.c982eb8d417eap-1, Tables 4, 6, 7, 8, 9
    0x3E04CDEE58A47EDD,  -- 0x1.4cdee58a47eddp-31, Table 4
    0x44A99CAA5236FEEA,  -- 0x1.99caa5236feeap+75, Table 9
    0x41816BAD92479879,  -- 0x1.16bad92479879p+25, Table 11
    0x402AB8E1C4A1E74A  -- 0x1.ab8e1c4a1e74ap+3, Table 11
  ]

/-- Inputs of `y1`. -/
def y1 : Array UInt64 :=
  #[
    0x400193BED4DFF243,  -- 0x1.193bed4dff243p+1, Tables 4, 6, 7, 8, 9
    0x3FFC513C569FE78E,  -- 0x1.c513c569fe78ep+0, Table 4
    0x441782B7A20DF6D4,  -- 0x1.782b7a20df6d4p+66, Table 9
    0x4192391E4C8FAA60,  -- 0x1.2391e4c8faa6p+26, Table 11
    0x403E9E480605283C  -- 0x1.e9e480605283cp+4, Table 11
  ]

/-- Pairs of `atan2`, in C's argument order. -/
def atan2 : Array (UInt64 × UInt64) :=
  #[
    -- 0x1.ed6060626eecfp-429, 0x1.f42ebb62994dcp-426, Table 5
    (0x252ED6060626EECF, 0x255F42EBB62994DC),
    -- 0x1.b77ade79a36d5p-326, 0x1.ff6a37b72b52bp-319, Table 5
    (0x2B9B77ADE79A36D5, 0x2C0FF6A37B72B52B),
    -- -0x1.ec2003fe89e36p-433, 0x1.ec173ed5fd8f5p-427, Table 6
    (0xA4EEC2003FE89E36, 0x254EC173ED5FD8F5),
    -- -0x1.358bb5eb25bdcp+813, 0x1.2f86b82481a0ap+815, Tables 6, 7, 9
    (0xF2C358BB5EB25BDC, 0x72E2F86B82481A0A),
    -- -0x1.6a539153430d8p-416, 0x1.d2b5b9dc716d8p-415, Table 8
    (0xA5F6A539153430D8, 0x260D2B5B9DC716D8),
    -- -0x1.bdb2c358b0b81p-93, 0x1.c717a5969be93p-86, Table 8
    (0xBA2BDB2C358B0B81, 0x3A9C717A5969BE93),
    -- 0x1.fffffffffffffp-627, 0x1.0000000000000p+448, Table 9
    (0x18CFFFFFFFFFFFFF, 0x5BF0000000000000),
    -- 0x1.d5de7a294d493p-935, 0x1.d030d7b608be1p-935, Table 10
    (0x058D5DE7A294D493, 0x058D030D7B608BE1),
    -- 0x1.2632db402a593p+52, 0x1.255022bb76d28p+52, Table 11
    (0x4332632DB402A593, 0x433255022BB76D28),
    -- 0x1.401ec07d65549p+888, 0x1.3c3976605bb0cp+888, Table 11
    (0x777401EC07D65549, 0x7773C3976605BB0C)
  ]

/-- Pairs of `pow`, in C's argument order. -/
def pow : Array (UInt64 × UInt64) :=
  #[
    -- 0x1.010e2e7ee71aep+0, 0x1.44bf0047427f6p+17, Tables 5, 10
    (0x3FF010E2E7EE71AE, 0x41044BF0047427F6),
    -- 0x1.fffff9c61ce4p-1, 0x1.c4e304ed4c734p+31, Table 5
    (0x3FEFFFFF9C61CE40, 0x41EC4E304ED4C734),
    -- 0x1.156c99097c8cdp-753, 0x1.6d3023561e86dp+0, Table 6
    (0x10E156C99097C8CD, 0x3FF6D3023561E86D),
    -- 0x1.a26d96e778dc8p+163, 0x1.90d5de9f964f6p-9, Table 6
    (0x4A2A26D96E778DC8, 0x3F690D5DE9F964F6),
    -- 0x1.000002c5e2e99p+0, 0x1.c9eee35374af6p+31, Tables 7, 9
    (0x3FF000002C5E2E99, 0x41EC9EEE35374AF6),
    -- 0x1.010e2e7ec0c83p+0, 0x1.44bf00479249dp+17, Table 7
    (0x3FF010E2E7EC0C83, 0x41044BF00479249D),
    -- 0x1.111616f835fb1p-72, 0x1.c6cfa07925d49p+3, Table 8
    (0x3B7111616F835FB1, 0x402C6CFA07925D49),
    -- 0x1.b4234939ab74ap+997, 0x1.59ccddd614389p+62, Table 8
    (0x7E4B4234939AB74A, 0x43D59CCDDD614389),
    -- 0x1.b8fa241e68c0ep-434, 0x1.4ec0af8e9feb1p-18, Table 9
    (0x24DB8FA241E68C0E, 0x3ED4EC0AF8E9FEB1),
    -- 0x1.6b2d4fdb85ba1p-1, -0x1.f0d1d713b0262p+10, Table 11
    (0x3FE6B2D4FDB85BA1, 0xC09F0D1D713B0262),
    -- 0x1.17efb14831458p-421, 0x1.f8c34d6504b2p-7, Table 11
    (0x25A17EFB14831458, 0x3F8F8C34D6504B20)
  ]

end TestSupport.Numerics.WorstCases
