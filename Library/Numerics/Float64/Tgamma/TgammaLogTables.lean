import Library.Numerics.Float64.Tgamma.TgammaKernelBase

/-!
Bounds on `as_logd`'s tables and kernel (`tgamma.c`, commit `ff2f71f6`): the double-double
logarithms `l1` and `l2` against the reciprocals `r1` and `r2`, each from rational bounds on the
logarithm whose exponentials the kernel compares with the reciprocal, the split `ln 2`, and the
kernel `log (1 + z) ≈ z + z² P (z)` on `|z| ≤ 1/2400` by a Taylor model (`TaylorCheck.exprOk`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaLogTables

open Real LeanExe.ProofKit PolyBound TaylorModel TaylorRemainder TaylorCheck RatExpLog
  GammaThresholds TgammaFactsBase TgammaKernelBase

/-! ### `asLogd` -/

/-- Lower and upper bounds on `log (r1 i)` and `log (r2 i)`. -/
def lo1 : List ℚ :=
  [-1 / 1298074214633706907132624082305024,
    -28111290747503291974825796614187 / 1298074214633706907132624082305024,
    -56244886435473093232633813994359 / 1298074214633706907132624082305024,
    -42173179143769250485444309379559 / 649037107316853453566312041152512,
    -56232371496384695212641658097473 / 649037107316853453566312041152512,
    -140587545611698943237192246895895 / 1298074214633706907132624082305024,
    -84350712972082637470051115774607 / 649037107316853453566312041152512,
    -196815211034256371059835812348815 / 1298074214633706907132624082305024,
    -14058676585580691294788808166151 / 81129638414606681695789005144064,
    -253059290907744343514416845262065 / 1298074214633706907132624082305024,
    -281162762855614096902065966914685 / 1298074214633706907132624082305024,
    -38660595459347515917354612490599 / 162259276829213363391578010288128,
    -337412901761937950857707702723107 / 1298074214633706907132624082305024,
    -182766972296272780892666824683705 / 649037107316853453566312041152512,
    -98408445390555648746980653237763 / 324518553658426726783156020576256,
    -210876103888459423612180120718127 / 649037107316853453566312041152512,
    -112469210194659873521244509289543 / 324518553658426726783156020576256,
    -59749307226682838206291529599465 / 162259276829213363391578010288128,
    -253060105041948586813968140032185 / 649037107316853453566312041152512,
    -534241002702677173107435813064113 / 1298074214633706907132624082305024,
    -562342868816331416970891632839063 / 1298074214633706907132624082305024,
    -590473362496295025055007054207355 / 1298074214633706907132624082305024,
    -618588858698147122778002864488931 / 1298074214633706907132624082305024,
    -161676830490269074715561438154917 / 324518553658426726783156020576256,
    -674815321019045965191280749168541 / 1298074214633706907132624082305024,
    -351466289424561015156205708393603 / 649037107316853453566312041152512,
    -365523044153000608083559060354689 / 649037107316853453566312041152512,
    -759177522238785625632083594529811 / 1298074214633706907132624082305024,
    -196819527117774640425771538672535 / 324518553658426726783156020576256,
    -815406414764264990880730939072677 / 1298074214633706907132624082305024,
    -421756361459631228864012445060005 / 649037107316853453566312041152512,
    -871620708348604479217655432620707 / 1298074214633706907132624082305024,
    -449878241015459621692550931480703 / 649037107316853453566312041152512]

def hi1 : List ℚ :=
  [1 / 1298074214633706907132624082305024,
    -3513911343437911496853224576773 / 162259276829213363391578010288128,
    -14061221608868273308158453498589 / 324518553658426726783156020576256,
    -84346358287538500970888618759115 / 1298074214633706907132624082305024,
    -112464742992769390425283316194943 / 1298074214633706907132624082305024,
    -35146886402924735809298061723973 / 324518553658426726783156020576256,
    -168701425944165274940102231549211 / 1298074214633706907132624082305024,
    -49203802758564092764958953087203 / 324518553658426726783156020576256,
    -224938825369291060716620930658413 / 1298074214633706907132624082305024,
    -126529645453872171757208422631031 / 649037107316853453566312041152512,
    -140581381427807048451032983457341 / 649037107316853453566312041152512,
    -309284763674780127338836899924789 / 1298074214633706907132624082305024,
    -10544153180060560964303365710097 / 40564819207303340847894502572032,
    -365533944592545561785333649367407 / 1298074214633706907132624082305024,
    -393633781562222594987922612951049 / 1298074214633706907132624082305024,
    -421752207776918847224360241436251 / 1298074214633706907132624082305024,
    -449876840778639494084978037158169 / 1298074214633706907132624082305024,
    -477994457813462705650332236795717 / 1298074214633706907132624082305024,
    -506120210083897173627936280064367 / 1298074214633706907132624082305024,
    -267120501351338586553717906532055 / 649037107316853453566312041152512,
    -140585717204082854242722908209765 / 324518553658426726783156020576256,
    -73809170312036878131875881775919 / 162259276829213363391578010288128,
    -19330901834317097586812589515279 / 40564819207303340847894502572032,
    -646707321961076298862245752619665 / 1298074214633706907132624082305024,
    -337407660509522982595640374584269 / 649037107316853453566312041152512,
    -702932578849122030312411416787203 / 1298074214633706907132624082305024,
    -731046088306001216167118120709375 / 1298074214633706907132624082305024,
    -47448595139924101602005224658113 / 81129638414606681695789005144064,
    -787278108471098561703086154690137 / 1298074214633706907132624082305024,
    -407703207382132495440365469536337 / 649037107316853453566312041152512,
    -843512722919262457728024890120007 / 1298074214633706907132624082305024,
    -27238147135893889975551732269397 / 40564819207303340847894502572032,
    -899756482030919243385101862961403 / 1298074214633706907132624082305024]

def lo2 : List ℚ :=
  [-1 / 1298074214633706907132624082305024,
    -881712690421820588341183161365 / 1298074214633706907132624082305024,
    -877053869200586688913057834781 / 649037107316853453566312041152512,
    -2637013111756797495259381121101 / 1298074214633706907132624082305024,
    -3510589037476932347051674476991 / 1298074214633706907132624082305024,
    -4394690324794896490042583500567 / 1298074214633706907132624082305024,
    -2634725164735815851618573348439 / 649037107316853453566312041152512,
    -1538687693731942678065437848495 / 324518553658426726783156020576256,
    -1757674518202938160261095868345 / 324518553658426726783156020576256,
    -7907236863698112240810161254685 / 1298074214633706907132624082305024,
    -4392183973475454877478208956581 / 649037107316853453566312041152512,
    -4831046061777866728814699276499 / 649037107316853453566312041152512,
    -10540410196124088363015332281765 / 1298074214633706907132624082305024,
    -11419322968897799792385181849093 / 1298074214633706907132624082305024,
    -3074707811938357964823544965033 / 324518553658426726783156020576256,
    -1647366980025840116702990957647 / 162259276829213363391578010288128,
    -7029818777708512072721528018717 / 649037107316853453566312041152512,
    -3735234301047945747488058842223 / 324518553658426726783156020576256,
    -15812810659985637292842929088451 / 1298074214633706907132624082305024,
    -4173825449290917148483417594025 / 324518553658426726783156020576256,
    -17568354794804163717350058623725 / 1298074214633706907132624082305024,
    -1153252540403381996779606862647 / 81129638414606681695789005144064,
    -1207892273864170782232977877087 / 81129638414606681695789005144064,
    -2526395023392167256623405331389 / 162259276829213363391578010288128,
    -21086581869133728468176760733501 / 1298074214633706907132624082305024,
    -21962594334250299683141776582627 / 1298074214633706907132624082305024,
    -5712319432768425696817210901253 / 324518553658426726783156020576256,
    -2965810121431206814486050534663 / 162259276829213363391578010288128,
    -24604277402796207169076912786751 / 1298074214633706907132624082305024,
    -25482667827923096428773105036681 / 1298074214633706907132624082305024,
    -26361653051270915367772808488209 / 1298074214633706907132624082305024,
    -27241233878915534755121723555409 / 1298074214633706907132624082305024]

def hi2 : List ℚ :=
  [1 / 1298074214633706907132624082305024,
    -440856345210910294170591580681 / 649037107316853453566312041152512,
    -1754107738401173377826115669559 / 1298074214633706907132624082305024,
    -1318506555878398747629690560549 / 649037107316853453566312041152512,
    -877647259369233086762918619247 / 324518553658426726783156020576256,
    -1098672581198724122510645875141 / 324518553658426726783156020576256,
    -5269450329471631703237146696875 / 1298074214633706907132624082305024,
    -6154750774927770712261751393977 / 1298074214633706907132624082305024,
    -7030698072811752641044383473377 / 1298074214633706907132624082305024,
    -3953618431849056120405080627341 / 649037107316853453566312041152512,
    -8784367946950909754956417913159 / 1298074214633706907132624082305024,
    -9662092123555733457629398552995 / 1298074214633706907132624082305024,
    -5270205098062044181507666140881 / 649037107316853453566312041152512,
    -5709661484448899896192590924545 / 649037107316853453566312041152512,
    -12298831247753431859294179860129 / 1298074214633706907132624082305024,
    -13178935840206720933623927661173 / 1298074214633706907132624082305024,
    -14059637555417024145443056037431 / 1298074214633706907132624082305024,
    -14940937204191782989952235368889 / 1298074214633706907132624082305024,
    -247075166562275582700670767007 / 20282409603651670423947251286016,
    -16695301797163668593933670376097 / 1298074214633706907132624082305024,
    -8784177397402081858675029311861 / 649037107316853453566312041152512,
    -18452040646454111948473709802349 / 1298074214633706907132624082305024,
    -19326276381826732515727646033389 / 1298074214633706907132624082305024,
    -20211160187137338052987242651109 / 1298074214633706907132624082305024,
    -10543290934566864234088380366749 / 649037107316853453566312041152512,
    -686331072945321865098180518207 / 40564819207303340847894502572032,
    -22849277731073702787268843605009 / 1298074214633706907132624082305024,
    -23726480971449654515888404277301 / 1298074214633706907132624082305024,
    -6151069350699051792269228196687 / 324518553658426726783156020576256,
    -12741333913961548214386552518339 / 649037107316853453566312041152512,
    -13180826525635457683886404244103 / 649037107316853453566312041152512,
    -13620616939457767377560861777703 / 649037107316853453566312041152512]

theorem l1_checked_0 :
    logCloseOk (r1 (0 : ℕ)) (l1 (0 : ℕ)) (lo1.getD (0 : ℕ) 0) (hi1.getD (0 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_1 :
    logCloseOk (r1 (1 : ℕ)) (l1 (1 : ℕ)) (lo1.getD (1 : ℕ) 0) (hi1.getD (1 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_2 :
    logCloseOk (r1 (2 : ℕ)) (l1 (2 : ℕ)) (lo1.getD (2 : ℕ) 0) (hi1.getD (2 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_3 :
    logCloseOk (r1 (3 : ℕ)) (l1 (3 : ℕ)) (lo1.getD (3 : ℕ) 0) (hi1.getD (3 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_4 :
    logCloseOk (r1 (4 : ℕ)) (l1 (4 : ℕ)) (lo1.getD (4 : ℕ) 0) (hi1.getD (4 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_5 :
    logCloseOk (r1 (5 : ℕ)) (l1 (5 : ℕ)) (lo1.getD (5 : ℕ) 0) (hi1.getD (5 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_6 :
    logCloseOk (r1 (6 : ℕ)) (l1 (6 : ℕ)) (lo1.getD (6 : ℕ) 0) (hi1.getD (6 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_7 :
    logCloseOk (r1 (7 : ℕ)) (l1 (7 : ℕ)) (lo1.getD (7 : ℕ) 0) (hi1.getD (7 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_8 :
    logCloseOk (r1 (8 : ℕ)) (l1 (8 : ℕ)) (lo1.getD (8 : ℕ) 0) (hi1.getD (8 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_9 :
    logCloseOk (r1 (9 : ℕ)) (l1 (9 : ℕ)) (lo1.getD (9 : ℕ) 0) (hi1.getD (9 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_10 :
    logCloseOk (r1 (10 : ℕ)) (l1 (10 : ℕ)) (lo1.getD (10 : ℕ) 0) (hi1.getD (10 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_11 :
    logCloseOk (r1 (11 : ℕ)) (l1 (11 : ℕ)) (lo1.getD (11 : ℕ) 0) (hi1.getD (11 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_12 :
    logCloseOk (r1 (12 : ℕ)) (l1 (12 : ℕ)) (lo1.getD (12 : ℕ) 0) (hi1.getD (12 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_13 :
    logCloseOk (r1 (13 : ℕ)) (l1 (13 : ℕ)) (lo1.getD (13 : ℕ) 0) (hi1.getD (13 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_14 :
    logCloseOk (r1 (14 : ℕ)) (l1 (14 : ℕ)) (lo1.getD (14 : ℕ) 0) (hi1.getD (14 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_15 :
    logCloseOk (r1 (15 : ℕ)) (l1 (15 : ℕ)) (lo1.getD (15 : ℕ) 0) (hi1.getD (15 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_16 :
    logCloseOk (r1 (16 : ℕ)) (l1 (16 : ℕ)) (lo1.getD (16 : ℕ) 0) (hi1.getD (16 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_17 :
    logCloseOk (r1 (17 : ℕ)) (l1 (17 : ℕ)) (lo1.getD (17 : ℕ) 0) (hi1.getD (17 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_18 :
    logCloseOk (r1 (18 : ℕ)) (l1 (18 : ℕ)) (lo1.getD (18 : ℕ) 0) (hi1.getD (18 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_19 :
    logCloseOk (r1 (19 : ℕ)) (l1 (19 : ℕ)) (lo1.getD (19 : ℕ) 0) (hi1.getD (19 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_20 :
    logCloseOk (r1 (20 : ℕ)) (l1 (20 : ℕ)) (lo1.getD (20 : ℕ) 0) (hi1.getD (20 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_21 :
    logCloseOk (r1 (21 : ℕ)) (l1 (21 : ℕ)) (lo1.getD (21 : ℕ) 0) (hi1.getD (21 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_22 :
    logCloseOk (r1 (22 : ℕ)) (l1 (22 : ℕ)) (lo1.getD (22 : ℕ) 0) (hi1.getD (22 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_23 :
    logCloseOk (r1 (23 : ℕ)) (l1 (23 : ℕ)) (lo1.getD (23 : ℕ) 0) (hi1.getD (23 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_24 :
    logCloseOk (r1 (24 : ℕ)) (l1 (24 : ℕ)) (lo1.getD (24 : ℕ) 0) (hi1.getD (24 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_25 :
    logCloseOk (r1 (25 : ℕ)) (l1 (25 : ℕ)) (lo1.getD (25 : ℕ) 0) (hi1.getD (25 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_26 :
    logCloseOk (r1 (26 : ℕ)) (l1 (26 : ℕ)) (lo1.getD (26 : ℕ) 0) (hi1.getD (26 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_27 :
    logCloseOk (r1 (27 : ℕ)) (l1 (27 : ℕ)) (lo1.getD (27 : ℕ) 0) (hi1.getD (27 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_28 :
    logCloseOk (r1 (28 : ℕ)) (l1 (28 : ℕ)) (lo1.getD (28 : ℕ) 0) (hi1.getD (28 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_29 :
    logCloseOk (r1 (29 : ℕ)) (l1 (29 : ℕ)) (lo1.getD (29 : ℕ) 0) (hi1.getD (29 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_30 :
    logCloseOk (r1 (30 : ℕ)) (l1 (30 : ℕ)) (lo1.getD (30 : ℕ) 0) (hi1.getD (30 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_31 :
    logCloseOk (r1 (31 : ℕ)) (l1 (31 : ℕ)) (lo1.getD (31 : ℕ) 0) (hi1.getD (31 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked_32 :
    logCloseOk (r1 (32 : ℕ)) (l1 (32 : ℕ)) (lo1.getD (32 : ℕ) 0) (hi1.getD (32 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l1_checked :
    ∀ i < 33, logCloseOk (r1 i) (l1 i) (lo1.getD i 0) (hi1.getD i 0) (1 / 2 ^ 80) = true := by
  intro i hi
  interval_cases i
  exacts [l1_checked_0, l1_checked_1, l1_checked_2, l1_checked_3, l1_checked_4, l1_checked_5,
    l1_checked_6, l1_checked_7, l1_checked_8, l1_checked_9, l1_checked_10, l1_checked_11,
    l1_checked_12, l1_checked_13, l1_checked_14, l1_checked_15, l1_checked_16, l1_checked_17,
    l1_checked_18, l1_checked_19, l1_checked_20, l1_checked_21, l1_checked_22, l1_checked_23,
    l1_checked_24, l1_checked_25, l1_checked_26, l1_checked_27, l1_checked_28, l1_checked_29,
    l1_checked_30, l1_checked_31, l1_checked_32]

theorem l2_checked_0 :
    logCloseOk (r2 (0 : ℕ)) (l2 (0 : ℕ)) (lo2.getD (0 : ℕ) 0) (hi2.getD (0 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_1 :
    logCloseOk (r2 (1 : ℕ)) (l2 (1 : ℕ)) (lo2.getD (1 : ℕ) 0) (hi2.getD (1 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_2 :
    logCloseOk (r2 (2 : ℕ)) (l2 (2 : ℕ)) (lo2.getD (2 : ℕ) 0) (hi2.getD (2 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_3 :
    logCloseOk (r2 (3 : ℕ)) (l2 (3 : ℕ)) (lo2.getD (3 : ℕ) 0) (hi2.getD (3 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_4 :
    logCloseOk (r2 (4 : ℕ)) (l2 (4 : ℕ)) (lo2.getD (4 : ℕ) 0) (hi2.getD (4 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_5 :
    logCloseOk (r2 (5 : ℕ)) (l2 (5 : ℕ)) (lo2.getD (5 : ℕ) 0) (hi2.getD (5 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_6 :
    logCloseOk (r2 (6 : ℕ)) (l2 (6 : ℕ)) (lo2.getD (6 : ℕ) 0) (hi2.getD (6 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_7 :
    logCloseOk (r2 (7 : ℕ)) (l2 (7 : ℕ)) (lo2.getD (7 : ℕ) 0) (hi2.getD (7 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_8 :
    logCloseOk (r2 (8 : ℕ)) (l2 (8 : ℕ)) (lo2.getD (8 : ℕ) 0) (hi2.getD (8 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_9 :
    logCloseOk (r2 (9 : ℕ)) (l2 (9 : ℕ)) (lo2.getD (9 : ℕ) 0) (hi2.getD (9 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_10 :
    logCloseOk (r2 (10 : ℕ)) (l2 (10 : ℕ)) (lo2.getD (10 : ℕ) 0) (hi2.getD (10 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_11 :
    logCloseOk (r2 (11 : ℕ)) (l2 (11 : ℕ)) (lo2.getD (11 : ℕ) 0) (hi2.getD (11 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_12 :
    logCloseOk (r2 (12 : ℕ)) (l2 (12 : ℕ)) (lo2.getD (12 : ℕ) 0) (hi2.getD (12 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_13 :
    logCloseOk (r2 (13 : ℕ)) (l2 (13 : ℕ)) (lo2.getD (13 : ℕ) 0) (hi2.getD (13 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_14 :
    logCloseOk (r2 (14 : ℕ)) (l2 (14 : ℕ)) (lo2.getD (14 : ℕ) 0) (hi2.getD (14 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_15 :
    logCloseOk (r2 (15 : ℕ)) (l2 (15 : ℕ)) (lo2.getD (15 : ℕ) 0) (hi2.getD (15 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_16 :
    logCloseOk (r2 (16 : ℕ)) (l2 (16 : ℕ)) (lo2.getD (16 : ℕ) 0) (hi2.getD (16 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_17 :
    logCloseOk (r2 (17 : ℕ)) (l2 (17 : ℕ)) (lo2.getD (17 : ℕ) 0) (hi2.getD (17 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_18 :
    logCloseOk (r2 (18 : ℕ)) (l2 (18 : ℕ)) (lo2.getD (18 : ℕ) 0) (hi2.getD (18 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_19 :
    logCloseOk (r2 (19 : ℕ)) (l2 (19 : ℕ)) (lo2.getD (19 : ℕ) 0) (hi2.getD (19 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_20 :
    logCloseOk (r2 (20 : ℕ)) (l2 (20 : ℕ)) (lo2.getD (20 : ℕ) 0) (hi2.getD (20 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_21 :
    logCloseOk (r2 (21 : ℕ)) (l2 (21 : ℕ)) (lo2.getD (21 : ℕ) 0) (hi2.getD (21 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_22 :
    logCloseOk (r2 (22 : ℕ)) (l2 (22 : ℕ)) (lo2.getD (22 : ℕ) 0) (hi2.getD (22 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_23 :
    logCloseOk (r2 (23 : ℕ)) (l2 (23 : ℕ)) (lo2.getD (23 : ℕ) 0) (hi2.getD (23 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_24 :
    logCloseOk (r2 (24 : ℕ)) (l2 (24 : ℕ)) (lo2.getD (24 : ℕ) 0) (hi2.getD (24 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_25 :
    logCloseOk (r2 (25 : ℕ)) (l2 (25 : ℕ)) (lo2.getD (25 : ℕ) 0) (hi2.getD (25 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_26 :
    logCloseOk (r2 (26 : ℕ)) (l2 (26 : ℕ)) (lo2.getD (26 : ℕ) 0) (hi2.getD (26 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_27 :
    logCloseOk (r2 (27 : ℕ)) (l2 (27 : ℕ)) (lo2.getD (27 : ℕ) 0) (hi2.getD (27 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_28 :
    logCloseOk (r2 (28 : ℕ)) (l2 (28 : ℕ)) (lo2.getD (28 : ℕ) 0) (hi2.getD (28 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_29 :
    logCloseOk (r2 (29 : ℕ)) (l2 (29 : ℕ)) (lo2.getD (29 : ℕ) 0) (hi2.getD (29 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_30 :
    logCloseOk (r2 (30 : ℕ)) (l2 (30 : ℕ)) (lo2.getD (30 : ℕ) 0) (hi2.getD (30 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked_31 :
    logCloseOk (r2 (31 : ℕ)) (l2 (31 : ℕ)) (lo2.getD (31 : ℕ) 0) (hi2.getD (31 : ℕ) 0)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem l2_checked :
    ∀ i < 32, logCloseOk (r2 i) (l2 i) (lo2.getD i 0) (hi2.getD i 0) (1 / 2 ^ 80) = true := by
  intro i hi
  interval_cases i
  exacts [l2_checked_0, l2_checked_1, l2_checked_2, l2_checked_3, l2_checked_4, l2_checked_5,
    l2_checked_6, l2_checked_7, l2_checked_8, l2_checked_9, l2_checked_10, l2_checked_11,
    l2_checked_12, l2_checked_13, l2_checked_14, l2_checked_15, l2_checked_16, l2_checked_17,
    l2_checked_18, l2_checked_19, l2_checked_20, l2_checked_21, l2_checked_22, l2_checked_23,
    l2_checked_24, l2_checked_25, l2_checked_26, l2_checked_27, l2_checked_28, l2_checked_29,
    l2_checked_30, l2_checked_31]

theorem l1_close : ∀ i < 33, |(l1 i : ℝ) + Real.log (r1 i)| ≤ 1 / 2 ^ 80 := by
  intro i hi
  have h := logClose (l1_checked i hi)
  push_cast at h
  exact h

theorem l2_close : ∀ i < 32, |(l2 i : ℝ) + Real.log (r2 i)| ≤ 1 / 2 ^ 80 := by
  intro i hi
  have h := logClose (l2_checked i hi)
  push_cast at h
  exact h

theorem ln2_checked : qabs (ln2 - log2Lo) ≤ 1 / 2 ^ 80 ∧ qabs (ln2 - log2Hi) ≤ 1 / 2 ^ 80 := by
  decide +kernel

theorem ln2_close : |(ln2 : ℝ) - Real.log 2| ≤ 1 / 2 ^ 80 := by
  obtain ⟨h1, h2⟩ := ln2_checked
  have h1r : |((ln2 - log2Lo : ℚ) : ℝ)| ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast h1
  have h2r : |((ln2 - log2Hi : ℚ) : ℝ)| ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast h2
  have hl := log_two_lo
  have hh := log_two_hi
  push_cast at h1r h2r
  rw [abs_le] at h1r h2r ⊢
  constructor <;> linarith

/-- The parameters for `log (1 + z)` on `|z| ≤ 1/2400`. -/
def cfgLog : Cfg := ⟨1 / 2400, 10, 100, 40, 1 / 2 ^ 100, GammaPi.piLo128, GammaPi.piHi128⟩

/-- `log (1 + z) - (z + z² P z)`. -/
def logErrExpr : TaylorModel.Expr := .add (.log1p .var) (.neg (.poly (0 :: 1 :: logPolyList)))

theorem logErr_checked : exprOk cfgLog logErrExpr (1 / 2 ^ 70) 1 = true := by
  decide +kernel

theorem log_poly : ∀ z : ℝ, |z| ≤ 1 / 2400 →
    |Real.log (1 + z) - (z + z ^ 2 * eval logPolyList z)| ≤ 1 / 2 ^ 70 := by
  intro z hz
  have h := exprOk_sound cfgLog logErrExpr _ _ GammaPi.pi_bounds128 logErr_checked (t := z)
    (by simp only [cfgLog]; push_cast; exact hz)
  simp only [logErrExpr, TaylorModel.Expr.eval, eval_cons] at h
  push_cast at h
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

#print axioms l1_close
#print axioms l2_close
#print axioms ln2_close
#print axioms log_poly

end Library.Numerics.Float64.Tgamma.TgammaLogTables
