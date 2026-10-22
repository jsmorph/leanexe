import Library.Numerics.Float64.Tgamma.TgammaKernelBase
import Library.Numerics.Float64.Lgamma.Compiled

/-!
Bounds on the tables and kernel of `as_logd_accurate` (`lgamma.c` lines 1116-1247, commit
`ff2f71f6`), read from the port's `Lgamma.logAccurateTable`: the triple-double logarithms `h1` and
`h2` lie within `2 ^ -96` of `-log r1` and `-log r2` for `as_logd`'s reciprocals, by rational
bounds on the logarithms whose exponentials the kernel compares with the reciprocals
(`Library.Numerics.Float64.Tgamma.TgammaKernelBase.logClose`); the triple-double `ln 2` lies within `2 ^ -100` of `log 2`; and the
kernel `log (1 + X) ≈ X P (X)` holds within `2 ^ -80 |X|` on `|X| ≤ 1/2400`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaLogAcc

open Real LeanExe.ProofKit PolyBound TaylorModel TaylorRemainder TaylorCheck RatExpLog
  GammaThresholds Library.Numerics.Float64.Tgamma.TgammaFactsBase Library.Numerics.Float64.Tgamma.TgammaKernelBase

/-- `as_logd_accurate`'s logarithms `h1 ≈ -log r1` and `h2 ≈ -log r2`, as triple-doubles. -/
def h1 (i : ℕ) : ℚ :=
  q Lgamma.logAccurateTable (3 * i) + q Lgamma.logAccurateTable (3 * i + 1) +
    q Lgamma.logAccurateTable (3 * i + 2)

def h2 (i : ℕ) : ℚ :=
  q Lgamma.logAccurateTable (99 + 3 * i) + q Lgamma.logAccurateTable (100 + 3 * i) +
    q Lgamma.logAccurateTable (101 + 3 * i)

/-- `as_logd_accurate`'s `ln 2` as a triple-double. -/
def ln2Acc : ℚ :=
  ratOfWord 0x3FE62E42FEFA3800 + ratOfWord 0x3D2EF35793C76000 + ratOfWord 0x3A8CC01F97B57A08

/-- The kernel `log (1 + X) ≈ X P (X)`. -/
def logAccList : List ℚ :=
  ddCoeffs Lgamma.logAccurateTable 198 6 ++
    [q Lgamma.logAccurateTable 210, q Lgamma.logAccurateTable 212, q Lgamma.logAccurateTable 214]

/-- Lower and upper bounds on `log (r1 i)` and `log (r2 i)`. -/
def lo1 : List ℚ :=
  [-1 / 2 ^ 120,
    -28785961725443370982221615732925581 / 2 ^ 120,
    -28797381854962223735108512765111023 / 2 ^ 119,
    -86370670886439424994189945609334795 / 2 ^ 120,
    -115163896824595855795490115783623517 / 2 ^ 120,
    -35990411676594929468721215205348863 / 2 ^ 118,
    -172750260166825241538664685106393211 / 2 ^ 120,
    -6298086753096203873914745995162041 / 2 ^ 115,
    -230337357178154046173819832994216255 / 2 ^ 120,
    -64783178472382551939690712387088141 / 2 ^ 118,
    -287910669164148835227715550120636091 / 2 ^ 120,
    -316707598002974850394968985522985503 / 2 ^ 120,
    -345510811404224461678292687588460039 / 2 ^ 120,
    -23394172453922915954261353559514169 / 2 ^ 116,
    -100770248079928984316908188915468905 / 2 ^ 118,
    -215937130381782449778872443615361057 / 2 ^ 119,
    -230336942478663420971508755024983279 / 2 ^ 119,
    -489466324800985810585940210478815683 / 2 ^ 120,
    -259133547562955352897503375392956865 / 2 ^ 119,
    -273531393383770712631007136288824911 / 2 ^ 119,
    -143959774416980842744548258006799827 / 2 ^ 118,
    -604644723196206105656327223508330341 / 2 ^ 120,
    -633434991306902653724674933236663907 / 2 ^ 120,
    -331114148844071065017469825341269425 / 2 ^ 119,
    -691010888723503068355871487148584169 / 2 ^ 120,
    -179950740185375239759977322697524263 / 2 ^ 118,
    -748591194425345245355128955606401147 / 2 ^ 120,
    -777397782772516480647253600798525167 / 2 ^ 120,
    -50385798942150307948997513900168865 / 2 ^ 116,
    -208744042179651837665467120402604801 / 2 ^ 118,
    -53984814266832797294593592967680571 / 2 ^ 116,
    -111567450668621373339859895375450265 / 2 ^ 117,
    -115168829699957663153293038459059807 / 2 ^ 117]

def hi1 : List ℚ :=
  [1 / 2 ^ 120,
    -14392980862721685491110807866462789 / 2 ^ 119,
    -57594763709924447470217025530222043 / 2 ^ 120,
    -10796333860804928124273743201166849 / 2 ^ 117,
    -57581948412297927897745057891811757 / 2 ^ 119,
    -143961646706379717874884860821395449 / 2 ^ 120,
    -21593782520853155192333085638299151 / 2 ^ 117,
    -201538776099078523965271871845185309 / 2 ^ 120,
    -57584339294538511543454958248554063 / 2 ^ 118,
    -259132713889530207758762849548352561 / 2 ^ 120,
    -35988833645518604403464443765079511 / 2 ^ 117,
    -79176899500743712598742246380746375 / 2 ^ 118,
    -86377702851056115419573171897115009 / 2 ^ 118,
    -374306759262766655268181656952226701 / 2 ^ 120,
    -403080992319715937267632755661875617 / 2 ^ 120,
    -431874260763564899557744887230722111 / 2 ^ 120,
    -460673884957326841943017510049966555 / 2 ^ 120,
    -7647911325015403290405315788731495 / 2 ^ 114,
    -518267095125910705795006750785913727 / 2 ^ 120,
    -547062786767541425262014272577649819 / 2 ^ 120,
    -575839097667923370978193032027199305 / 2 ^ 120,
    -302322361598103052828163611754165169 / 2 ^ 119,
    -19794843478340707928896091663645747 / 2 ^ 115,
    -662228297688142130034939650682538847 / 2 ^ 120,
    -345505444361751534177935743574292083 / 2 ^ 119,
    -719802960741500959039909290790097049 / 2 ^ 120,
    -93573899303168155669391119450800143 / 2 ^ 117,
    -194349445693129120161813400199631291 / 2 ^ 118,
    -806172783074404927183960222402701837 / 2 ^ 120,
    -834976168718607350661868481610419201 / 2 ^ 120,
    -863757028269324756713497487482889133 / 2 ^ 120,
    -892539605348970986718879163003602117 / 2 ^ 120,
    -921350637599661305226344307672478453 / 2 ^ 120]

def lo2 : List ℚ :=
  [-1 / 2 ^ 120,
    -451436897495972141230685778617921 / 2 ^ 119,
    -1796206324122801538893942445630379 / 2 ^ 120,
    -675075356609740158786401567001355 / 2 ^ 118,
    -3594843174376378723380914664437613 / 2 ^ 120,
    -2250081446294987002901802752289393 / 2 ^ 119,
    -337244821086184429007177388600125 / 2 ^ 116,
    -1575616198381509302339008356858413 / 2 ^ 118,
    -3599717413279617352214724338369885 / 2 ^ 119,
    -8097010548426866934589605124795795 / 2 ^ 120,
    -4497596388838865794537685971538343 / 2 ^ 119,
    -9893982334521071060612504118268483 / 2 ^ 120,
    -5396690020415533241863850128262925 / 2 ^ 119,
    -11693386720151346987402426213469761 / 2 ^ 120,
    -12594003197699514223917240176773983 / 2 ^ 120,
    -13495230300371682236030901925042371 / 2 ^ 120,
    -224954200886672386327088896598915 / 2 ^ 114,
    -15299519697092385781711089017743473 / 2 ^ 120,
    -8096159057912646293935579693286345 / 2 ^ 119,
    -17095989040295596640188078465124757 / 2 ^ 120,
    -17989995309879463646566460030693099 / 2 ^ 120,
    -9447444810984505317618539418803289 / 2 ^ 119,
    -1236881688436910881006569346136999 / 2 ^ 116,
    -10348114015814317083129468237368421 / 2 ^ 119,
    -10796329916996468975706501495551571 / 2 ^ 119,
    -22489696598272306875537179220608897 / 2 ^ 120,
    -5849415099154867913540823962882619 / 2 ^ 118,
    -12147958257382223112134862989978877 / 2 ^ 119,
    -25194780060463316141134758693631365 / 2 ^ 120,
    -6523562963948312685765914889389825 / 2 ^ 118,
    -26994332724501417336599355891924219 / 2 ^ 120,
    -27895023492009507589244644920737705 / 2 ^ 120]

def hi2 : List ℚ :=
  [1 / 2 ^ 120,
    -902873794991944282461371557235839 / 2 ^ 120,
    -224525790515350192361742805703797 / 2 ^ 117,
    -2700301426438960635145606268005417 / 2 ^ 120,
    -1797421587188189361690457332218805 / 2 ^ 119,
    -4500162892589974005803605504578783 / 2 ^ 120,
    -5395917137378950864114838217601997 / 2 ^ 120,
    -6302464793526037209356033427433649 / 2 ^ 120,
    -7199434826559234704429448676739767 / 2 ^ 120,
    -506063159276679183411850320299737 / 2 ^ 116,
    -8995192777677731589075371943076683 / 2 ^ 120,
    -154593473976891735322070376847945 / 2 ^ 114,
    -10793380040831066483727700256525847 / 2 ^ 120,
    -5846693360075673493701213106734879 / 2 ^ 119,
    -3148500799424878555979310044193495 / 2 ^ 118,
    -210862973443307534937982842578787 / 2 ^ 114,
    -14397068856747032724933689382330557 / 2 ^ 120,
    -7649759848546192890855544508871735 / 2 ^ 119,
    -16192318115825292587871159386572687 / 2 ^ 120,
    -8547994520147798320094039232562377 / 2 ^ 119,
    -2248749413734932955820807503836637 / 2 ^ 117,
    -18894889621969010635237078837606575 / 2 ^ 120,
    -19790107014990574096105109538191981 / 2 ^ 120,
    -20696228031628634166258936474736839 / 2 ^ 120,
    -21592659833992937951413002991103139 / 2 ^ 120,
    -11244848299136153437768589610304447 / 2 ^ 119,
    -23397660396619471654163295851530473 / 2 ^ 120,
    -24295916514764446224269725979957751 / 2 ^ 120,
    -12597390030231658070567379346815681 / 2 ^ 119,
    -26094251855793250743063659557559297 / 2 ^ 120,
    -3374291590562677167074919486490527 / 2 ^ 117,
    -13947511746004753794622322460368851 / 2 ^ 119]

theorem h1_checked_0 :
    logCloseOk (r1 (0 : ℕ)) (h1 (0 : ℕ)) (lo1.getD (0 : ℕ) 0) (hi1.getD (0 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_1 :
    logCloseOk (r1 (1 : ℕ)) (h1 (1 : ℕ)) (lo1.getD (1 : ℕ) 0) (hi1.getD (1 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_2 :
    logCloseOk (r1 (2 : ℕ)) (h1 (2 : ℕ)) (lo1.getD (2 : ℕ) 0) (hi1.getD (2 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_3 :
    logCloseOk (r1 (3 : ℕ)) (h1 (3 : ℕ)) (lo1.getD (3 : ℕ) 0) (hi1.getD (3 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_4 :
    logCloseOk (r1 (4 : ℕ)) (h1 (4 : ℕ)) (lo1.getD (4 : ℕ) 0) (hi1.getD (4 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_5 :
    logCloseOk (r1 (5 : ℕ)) (h1 (5 : ℕ)) (lo1.getD (5 : ℕ) 0) (hi1.getD (5 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_6 :
    logCloseOk (r1 (6 : ℕ)) (h1 (6 : ℕ)) (lo1.getD (6 : ℕ) 0) (hi1.getD (6 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_7 :
    logCloseOk (r1 (7 : ℕ)) (h1 (7 : ℕ)) (lo1.getD (7 : ℕ) 0) (hi1.getD (7 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_8 :
    logCloseOk (r1 (8 : ℕ)) (h1 (8 : ℕ)) (lo1.getD (8 : ℕ) 0) (hi1.getD (8 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_9 :
    logCloseOk (r1 (9 : ℕ)) (h1 (9 : ℕ)) (lo1.getD (9 : ℕ) 0) (hi1.getD (9 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_10 :
    logCloseOk (r1 (10 : ℕ)) (h1 (10 : ℕ)) (lo1.getD (10 : ℕ) 0) (hi1.getD (10 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_11 :
    logCloseOk (r1 (11 : ℕ)) (h1 (11 : ℕ)) (lo1.getD (11 : ℕ) 0) (hi1.getD (11 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_12 :
    logCloseOk (r1 (12 : ℕ)) (h1 (12 : ℕ)) (lo1.getD (12 : ℕ) 0) (hi1.getD (12 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_13 :
    logCloseOk (r1 (13 : ℕ)) (h1 (13 : ℕ)) (lo1.getD (13 : ℕ) 0) (hi1.getD (13 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_14 :
    logCloseOk (r1 (14 : ℕ)) (h1 (14 : ℕ)) (lo1.getD (14 : ℕ) 0) (hi1.getD (14 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_15 :
    logCloseOk (r1 (15 : ℕ)) (h1 (15 : ℕ)) (lo1.getD (15 : ℕ) 0) (hi1.getD (15 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_16 :
    logCloseOk (r1 (16 : ℕ)) (h1 (16 : ℕ)) (lo1.getD (16 : ℕ) 0) (hi1.getD (16 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_17 :
    logCloseOk (r1 (17 : ℕ)) (h1 (17 : ℕ)) (lo1.getD (17 : ℕ) 0) (hi1.getD (17 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_18 :
    logCloseOk (r1 (18 : ℕ)) (h1 (18 : ℕ)) (lo1.getD (18 : ℕ) 0) (hi1.getD (18 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_19 :
    logCloseOk (r1 (19 : ℕ)) (h1 (19 : ℕ)) (lo1.getD (19 : ℕ) 0) (hi1.getD (19 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_20 :
    logCloseOk (r1 (20 : ℕ)) (h1 (20 : ℕ)) (lo1.getD (20 : ℕ) 0) (hi1.getD (20 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_21 :
    logCloseOk (r1 (21 : ℕ)) (h1 (21 : ℕ)) (lo1.getD (21 : ℕ) 0) (hi1.getD (21 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_22 :
    logCloseOk (r1 (22 : ℕ)) (h1 (22 : ℕ)) (lo1.getD (22 : ℕ) 0) (hi1.getD (22 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_23 :
    logCloseOk (r1 (23 : ℕ)) (h1 (23 : ℕ)) (lo1.getD (23 : ℕ) 0) (hi1.getD (23 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_24 :
    logCloseOk (r1 (24 : ℕ)) (h1 (24 : ℕ)) (lo1.getD (24 : ℕ) 0) (hi1.getD (24 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_25 :
    logCloseOk (r1 (25 : ℕ)) (h1 (25 : ℕ)) (lo1.getD (25 : ℕ) 0) (hi1.getD (25 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_26 :
    logCloseOk (r1 (26 : ℕ)) (h1 (26 : ℕ)) (lo1.getD (26 : ℕ) 0) (hi1.getD (26 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_27 :
    logCloseOk (r1 (27 : ℕ)) (h1 (27 : ℕ)) (lo1.getD (27 : ℕ) 0) (hi1.getD (27 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_28 :
    logCloseOk (r1 (28 : ℕ)) (h1 (28 : ℕ)) (lo1.getD (28 : ℕ) 0) (hi1.getD (28 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_29 :
    logCloseOk (r1 (29 : ℕ)) (h1 (29 : ℕ)) (lo1.getD (29 : ℕ) 0) (hi1.getD (29 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_30 :
    logCloseOk (r1 (30 : ℕ)) (h1 (30 : ℕ)) (lo1.getD (30 : ℕ) 0) (hi1.getD (30 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_31 :
    logCloseOk (r1 (31 : ℕ)) (h1 (31 : ℕ)) (lo1.getD (31 : ℕ) 0) (hi1.getD (31 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_checked_32 :
    logCloseOk (r1 (32 : ℕ)) (h1 (32 : ℕ)) (lo1.getD (32 : ℕ) 0) (hi1.getD (32 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h1_close : ∀ i < 33, |(h1 i : ℝ) + Real.log (r1 i)| ≤ 1 / 2 ^ 96 := by
  have hc : ∀ i < 33,
      logCloseOk (r1 i) (h1 i) (lo1.getD i 0) (hi1.getD i 0) (1 / 2 ^ 96) = true := by
    intro i hi
    interval_cases i
    exacts [h1_checked_0, h1_checked_1, h1_checked_2, h1_checked_3, h1_checked_4, h1_checked_5,
      h1_checked_6, h1_checked_7, h1_checked_8, h1_checked_9, h1_checked_10, h1_checked_11,
      h1_checked_12, h1_checked_13, h1_checked_14, h1_checked_15, h1_checked_16, h1_checked_17,
      h1_checked_18, h1_checked_19, h1_checked_20, h1_checked_21, h1_checked_22, h1_checked_23,
      h1_checked_24, h1_checked_25, h1_checked_26, h1_checked_27, h1_checked_28, h1_checked_29,
      h1_checked_30, h1_checked_31, h1_checked_32]
  intro i hi
  have h := logClose (hc i hi)
  push_cast at h
  exact h

theorem h2_checked_0 :
    logCloseOk (r2 (0 : ℕ)) (h2 (0 : ℕ)) (lo2.getD (0 : ℕ) 0) (hi2.getD (0 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_1 :
    logCloseOk (r2 (1 : ℕ)) (h2 (1 : ℕ)) (lo2.getD (1 : ℕ) 0) (hi2.getD (1 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_2 :
    logCloseOk (r2 (2 : ℕ)) (h2 (2 : ℕ)) (lo2.getD (2 : ℕ) 0) (hi2.getD (2 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_3 :
    logCloseOk (r2 (3 : ℕ)) (h2 (3 : ℕ)) (lo2.getD (3 : ℕ) 0) (hi2.getD (3 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_4 :
    logCloseOk (r2 (4 : ℕ)) (h2 (4 : ℕ)) (lo2.getD (4 : ℕ) 0) (hi2.getD (4 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_5 :
    logCloseOk (r2 (5 : ℕ)) (h2 (5 : ℕ)) (lo2.getD (5 : ℕ) 0) (hi2.getD (5 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_6 :
    logCloseOk (r2 (6 : ℕ)) (h2 (6 : ℕ)) (lo2.getD (6 : ℕ) 0) (hi2.getD (6 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_7 :
    logCloseOk (r2 (7 : ℕ)) (h2 (7 : ℕ)) (lo2.getD (7 : ℕ) 0) (hi2.getD (7 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_8 :
    logCloseOk (r2 (8 : ℕ)) (h2 (8 : ℕ)) (lo2.getD (8 : ℕ) 0) (hi2.getD (8 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_9 :
    logCloseOk (r2 (9 : ℕ)) (h2 (9 : ℕ)) (lo2.getD (9 : ℕ) 0) (hi2.getD (9 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_10 :
    logCloseOk (r2 (10 : ℕ)) (h2 (10 : ℕ)) (lo2.getD (10 : ℕ) 0) (hi2.getD (10 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_11 :
    logCloseOk (r2 (11 : ℕ)) (h2 (11 : ℕ)) (lo2.getD (11 : ℕ) 0) (hi2.getD (11 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_12 :
    logCloseOk (r2 (12 : ℕ)) (h2 (12 : ℕ)) (lo2.getD (12 : ℕ) 0) (hi2.getD (12 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_13 :
    logCloseOk (r2 (13 : ℕ)) (h2 (13 : ℕ)) (lo2.getD (13 : ℕ) 0) (hi2.getD (13 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_14 :
    logCloseOk (r2 (14 : ℕ)) (h2 (14 : ℕ)) (lo2.getD (14 : ℕ) 0) (hi2.getD (14 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_15 :
    logCloseOk (r2 (15 : ℕ)) (h2 (15 : ℕ)) (lo2.getD (15 : ℕ) 0) (hi2.getD (15 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_16 :
    logCloseOk (r2 (16 : ℕ)) (h2 (16 : ℕ)) (lo2.getD (16 : ℕ) 0) (hi2.getD (16 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_17 :
    logCloseOk (r2 (17 : ℕ)) (h2 (17 : ℕ)) (lo2.getD (17 : ℕ) 0) (hi2.getD (17 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_18 :
    logCloseOk (r2 (18 : ℕ)) (h2 (18 : ℕ)) (lo2.getD (18 : ℕ) 0) (hi2.getD (18 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_19 :
    logCloseOk (r2 (19 : ℕ)) (h2 (19 : ℕ)) (lo2.getD (19 : ℕ) 0) (hi2.getD (19 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_20 :
    logCloseOk (r2 (20 : ℕ)) (h2 (20 : ℕ)) (lo2.getD (20 : ℕ) 0) (hi2.getD (20 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_21 :
    logCloseOk (r2 (21 : ℕ)) (h2 (21 : ℕ)) (lo2.getD (21 : ℕ) 0) (hi2.getD (21 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_22 :
    logCloseOk (r2 (22 : ℕ)) (h2 (22 : ℕ)) (lo2.getD (22 : ℕ) 0) (hi2.getD (22 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_23 :
    logCloseOk (r2 (23 : ℕ)) (h2 (23 : ℕ)) (lo2.getD (23 : ℕ) 0) (hi2.getD (23 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_24 :
    logCloseOk (r2 (24 : ℕ)) (h2 (24 : ℕ)) (lo2.getD (24 : ℕ) 0) (hi2.getD (24 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_25 :
    logCloseOk (r2 (25 : ℕ)) (h2 (25 : ℕ)) (lo2.getD (25 : ℕ) 0) (hi2.getD (25 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_26 :
    logCloseOk (r2 (26 : ℕ)) (h2 (26 : ℕ)) (lo2.getD (26 : ℕ) 0) (hi2.getD (26 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_27 :
    logCloseOk (r2 (27 : ℕ)) (h2 (27 : ℕ)) (lo2.getD (27 : ℕ) 0) (hi2.getD (27 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_28 :
    logCloseOk (r2 (28 : ℕ)) (h2 (28 : ℕ)) (lo2.getD (28 : ℕ) 0) (hi2.getD (28 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_29 :
    logCloseOk (r2 (29 : ℕ)) (h2 (29 : ℕ)) (lo2.getD (29 : ℕ) 0) (hi2.getD (29 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_30 :
    logCloseOk (r2 (30 : ℕ)) (h2 (30 : ℕ)) (lo2.getD (30 : ℕ) 0) (hi2.getD (30 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_checked_31 :
    logCloseOk (r2 (31 : ℕ)) (h2 (31 : ℕ)) (lo2.getD (31 : ℕ) 0) (hi2.getD (31 : ℕ) 0)
      (1 / 2 ^ 96) = true := by
  decide +kernel

theorem h2_close : ∀ i < 32, |(h2 i : ℝ) + Real.log (r2 i)| ≤ 1 / 2 ^ 96 := by
  have hc : ∀ i < 32,
      logCloseOk (r2 i) (h2 i) (lo2.getD i 0) (hi2.getD i 0) (1 / 2 ^ 96) = true := by
    intro i hi
    interval_cases i
    exacts [h2_checked_0, h2_checked_1, h2_checked_2, h2_checked_3, h2_checked_4, h2_checked_5,
      h2_checked_6, h2_checked_7, h2_checked_8, h2_checked_9, h2_checked_10, h2_checked_11,
      h2_checked_12, h2_checked_13, h2_checked_14, h2_checked_15, h2_checked_16, h2_checked_17,
      h2_checked_18, h2_checked_19, h2_checked_20, h2_checked_21, h2_checked_22, h2_checked_23,
      h2_checked_24, h2_checked_25, h2_checked_26, h2_checked_27, h2_checked_28, h2_checked_29,
      h2_checked_30, h2_checked_31]
  intro i hi
  have h := logClose (hc i hi)
  push_cast at h
  exact h

theorem ln2_enc :
    logEncOk 2 (235865763225513294137944142764154484399 / 2 ^ 128)
      (943463052902053176551776571056617937599 / 2 ^ 130) = true := by
  decide +kernel

theorem ln2_gap :
    qabs (ln2Acc - (235865763225513294137944142764154484399 / 2 ^ 128)) ≤ 1 / 2 ^ 100 ∧
      qabs (ln2Acc - (943463052902053176551776571056617937599 / 2 ^ 130)) ≤ 1 / 2 ^ 100 := by
  decide +kernel

theorem ln2Acc_close : |(ln2Acc : ℝ) - Real.log 2| ≤ 1 / 2 ^ 100 := by
  obtain ⟨hl, hh⟩ := logEnc ln2_enc
  obtain ⟨g1, g2⟩ := ln2_gap
  have g1r :
      |((ln2Acc - (235865763225513294137944142764154484399 / 2 ^ 128) : ℚ) : ℝ)| ≤
        ((1 / 2 ^ 100 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast g1
  have g2r :
      |((ln2Acc - (943463052902053176551776571056617937599 / 2 ^ 130) : ℚ) : ℝ)| ≤
        ((1 / 2 ^ 100 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast g2
  push_cast at g1r g2r hl hh
  rw [abs_le] at g1r g2r ⊢
  constructor <;> linarith [g1r.1, g1r.2, g2r.1, g2r.2]

/-- The parameters for the kernel on `|X| ≤ 1/2400`. -/
def cfgL : Cfg := ⟨1 / 2400, 12, 120, 60, 1 / 2 ^ 120, Library.Numerics.Float64.Tgamma.GammaPi.piLo128, Library.Numerics.Float64.Tgamma.GammaPi.piHi128⟩

/-- `log (1 + X)/X - P (X)`. -/
def logErrExpr : TaylorModel.Expr := .add (.log1pDiv .var) (.neg (.poly logAccList))

theorem logErr_checked : exprOk cfgL logErrExpr (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem log_kernel_fact : ∀ X : ℝ, |X| ≤ 1 / 2400 →
    |Real.log (1 + X) - X * eval logAccList X| ≤ 1 / 2 ^ 80 * |X| := by
  intro X hX
  have h := exprOk_sound cfgL logErrExpr _ _ Library.Numerics.Float64.Tgamma.GammaPi.pi_bounds128 logErr_checked (t := X)
    (by simp only [cfgL]; push_cast; exact hX)
  simp only [logErrExpr, TaylorModel.Expr.eval] at h
  push_cast at h
  rcases eq_or_ne X 0 with h0 | h0
  · subst h0
    simp
  · simp only [h0, ↓reduceIte] at h
    have he : Real.log (1 + X) - X * eval logAccList X =
        X * (Real.log (1 + X) / X + -eval logAccList X) := by
      field_simp
      ring
    rw [he, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg X)

#print axioms h1_close
#print axioms h2_close
#print axioms ln2Acc_close
#print axioms log_kernel_fact

end Library.Numerics.Float64.Lgamma.LgammaLogAcc
