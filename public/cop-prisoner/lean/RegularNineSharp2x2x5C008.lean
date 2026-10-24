import RegularNineSharp2x2x5Base
import RegularNineSharp2x2x5C000
import RegularNineSharp2x2x5C001
import RegularNineSharp2x2x5C002
import RegularNineSharp2x2x5C003
import RegularNineSharp2x2x5C004
import RegularNineSharp2x2x5C005
import RegularNineSharp2x2x5C006
import RegularNineSharp2x2x5C007
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Bounds BoundTreeRows Extremal
theorem node512 : UpperPrefix a [2,4,8] 30 :=
  branch_upper a [2,4,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut26 [2,4,8,0] [2,4,1,5] 30 (by decide +kernel) node81)
  (PrefixConjugacy.upper aut36 [2,4,8,1] [2,4,5,1] 30 (by decide +kernel) node143)
  (invalid_upper a [2,4,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,4] 30 (by decide +kernel))
  node446
  node490
  node511
  (invalid_upper a [2,4,8,8] 30 (by decide +kernel)))

theorem node513 : UpperPrefix a [2,4] 30 :=
  branch_upper a [2,4] 30 (by decide) (fin9_cases _
  node65
  node129
  (invalid_upper a [2,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,4] 30 (by decide +kernel))
  node215
  node310
  node402
  node512)

theorem node514 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0] 30 (by decide +kernel))
  (invalid_upper a [2,1] 30 (by decide +kernel))
  (invalid_upper a [2,2] 30 (by decide +kernel))
  node36
  node513
  (PrefixConjugacy.upper aut4 [2,5] [2,4] 30 (by decide +kernel) node513)
  (PrefixConjugacy.upper aut3 [2,6] [2,4] 30 (by decide +kernel) node513)
  (PrefixConjugacy.upper aut2 [2,7] [2,4] 30 (by decide +kernel) node513)
  (PrefixConjugacy.upper aut1 [2,8] [2,4] 30 (by decide +kernel) node513))

theorem node515 : UpperPrefix a [4,5,0] 30 :=
  branch_upper a [4,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut20 [4,5,0,1] [2,3,4,5] 30 (by decide +kernel) node6)
  (invalid_upper a [4,5,0,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,0,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut23 [4,5,0,6] [2,4,7,8] 30 (by decide +kernel) node401)
  (PrefixConjugacy.upper aut22 [4,5,0,7] [2,4,6,7] 30 (by decide +kernel) node271)
  (PrefixConjugacy.upper aut21 [4,5,0,8] [2,4,5,6] 30 (by decide +kernel) node160))

theorem node516 : UpperPrefix a [4,5,1] 30 :=
  branch_upper a [4,5,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut25 [4,5,1,0] [2,3,4,5] 30 (by decide +kernel) node6)
  (invalid_upper a [4,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [4,5,1,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,1,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut33 [4,5,1,6] [2,4,8,7] 30 (by decide +kernel) node511)
  (PrefixConjugacy.upper aut32 [4,5,1,7] [2,4,7,6] 30 (by decide +kernel) node383)
  (PrefixConjugacy.upper aut31 [4,5,1,8] [2,4,6,5] 30 (by decide +kernel) node254))

def cert517 : Leaf := ⟨⟨364,0,386,322,0,270,270,78,78⟩,[(1,4),(4,1)],[(5,1,0),(7,3,2),(0,4,0)],⟨19,35,76,140,49,366,462,398,286⟩,⟨19,35,76,140,49,96,192,384,272⟩,[⟨4,1212473369217464934605825,⟨3,39,76,140,39,108,204,492,494⟩⟩]⟩
theorem node517 : UpperPrefix a [4,5,6,7,0] 30 :=
  Boolean.leaf_sound a [4,5,6,7,0] 30 cert517 (by decide +kernel)

def cert518 : Leaf := ⟨⟨0,92,145,81,0,285,285,93,77⟩,[(0,4),(4,1)],[(5,1,0),(5,1,4),(7,3,2),(1,4,0)],⟨19,35,76,140,50,365,461,397,285⟩,⟨19,35,76,140,50,96,192,384,272⟩,[⟨8,1181745671567588746547,⟨19,55,76,140,55,127,204,129,19⟩⟩]⟩
theorem node518 : UpperPrefix a [4,5,6,7,1] 30 :=
  Boolean.leaf_sound a [4,5,6,7,1] 30 cert518 (by decide +kernel)

def cert519 : Leaf := ⟨⟨40,24,144,16,72,287,287,31,15⟩,[],[(5,1,0),(6,2,4),(7,3,2)],⟨19,35,76,140,52,363,459,395,283⟩,⟨19,35,76,140,52,96,192,384,272⟩,[⟨8,1181745671567588746547,⟨19,55,76,140,55,127,204,129,19⟩⟩,⟨0,1210107565286196763427840,⟨18,54,76,140,52,124,204,384,272⟩⟩,⟨1,1210107565286196763426817,⟨17,53,76,140,52,124,204,384,272⟩⟩,⟨2,1210107565283851685078289,⟨19,35,72,136,51,96,192,385,275⟩⟩]⟩
theorem node519 : UpperPrefix a [4,5,6,7,2] 30 :=
  Boolean.leaf_sound a [4,5,6,7,2] 30 cert519 (by decide +kernel)

def cert520 : Leaf := ⟨⟨32,16,128,64,68,287,287,95,79⟩,[],[(5,1,0),(7,3,2)],⟨19,35,76,140,56,359,455,391,279⟩,⟨19,35,76,140,56,96,192,384,272⟩,[⟨8,1181745671430149793075,⟨19,55,76,140,63,127,204,129,19⟩⟩,⟨0,1210107565286059324474368,⟨18,54,76,140,60,124,204,384,272⟩⟩,⟨1,1210107565286059324473345,⟨17,53,76,140,60,124,204,384,272⟩⟩,⟨2,1210107565283851685078289,⟨19,35,72,136,59,96,192,385,275⟩⟩,⟨3,1210107565283850612385041,⟨19,35,68,132,51,96,192,385,275⟩⟩,⟨4,1210107565282760789591041,⟨3,39,76,140,44,108,204,384,256⟩⟩,⟨6,1210106412362347079279889,⟨19,35,12,140,59,32,128,385,275⟩⟩]⟩
theorem node520 : UpperPrefix a [4,5,6,7,3] 30 :=
  Boolean.leaf_sound a [4,5,6,7,3] 30 cert520 (by decide +kernel)

def cert521 : Leaf := ⟨⟨32,16,128,64,79,31,31,95,79⟩,[],[(5,1,0),(7,3,2)],⟨19,35,76,140,304,111,207,399,287⟩,⟨19,35,76,140,304,96,192,384,272⟩,[⟨8,1184056015857183171857,⟨19,39,76,238,55,108,238,239,19⟩⟩,⟨0,1210107565283860301218816,⟨18,38,76,140,308,108,204,384,272⟩⟩,⟨1,1210107565283860301217793,⟨17,37,76,140,308,108,204,384,272⟩⟩,⟨2,1210107565283851685078289,⟨19,35,72,136,307,96,192,385,275⟩⟩,⟨3,1210107565283850612385041,⟨19,35,68,132,307,96,192,385,275⟩⟩,⟨4,1210107565282760789591041,⟨3,39,76,140,292,108,204,384,256⟩⟩,⟨6,1210106412362347079279889,⟨19,35,12,140,307,32,128,385,275⟩⟩]⟩
theorem node521 : UpperPrefix a [4,5,6,7,8] 30 :=
  Boolean.leaf_sound a [4,5,6,7,8] 30 cert521 (by decide +kernel)

theorem node522 : UpperPrefix a [4,5,6,7] 30 :=
  branch_upper a [4,5,6,7] 30 (by decide) (fin9_cases _
  node517
  node518
  node519
  node520
  (invalid_upper a [4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,7] 30 (by decide +kernel))
  node521)

def cert523 : Leaf := ⟨⟨492,0,386,194,0,398,270,78,206⟩,[(1,4),(4,1)],[(5,1,0),(0,4,0)],⟨19,35,76,268,49,238,206,398,414⟩,⟨19,35,76,268,49,96,192,384,272⟩,[⟨4,1212473369217456338379777,⟨3,35,76,492,35,100,204,492,494⟩⟩]⟩
theorem node523 : UpperPrefix a [4,5,6,8,0] 30 :=
  Boolean.leaf_sound a [4,5,6,8,0] 30 cert523 (by decide +kernel)

def cert524 : Leaf := ⟨⟨0,272,401,209,0,413,285,29,205⟩,[(0,4),(4,1)],[(5,1,0),(5,1,4),(1,4,0)],⟨19,35,76,268,50,237,205,397,413⟩,⟨19,35,76,268,50,96,192,384,272⟩,[⟨6,1210180199340978379711795,⟨19,51,140,397,51,51,128,385,275⟩⟩,⟨2,1210107565286188147303731,⟨19,51,72,265,51,115,192,385,275⟩⟩,⟨3,1210107565286187074610483,⟨19,51,68,261,51,115,192,385,275⟩⟩,⟨7,1208926973665470737048883,⟨19,51,76,269,51,115,64,257,275⟩⟩]⟩
theorem node524 : UpperPrefix a [4,5,6,8,1] 30 :=
  Boolean.leaf_sound a [4,5,6,8,1] 30 cert524 (by decide +kernel)

def cert525 : Leaf := ⟨⟨416,0,402,146,450,402,282,26,142⟩,[(1,5)],[(5,1,0),(6,2,4),(0,5,1)],⟨19,35,76,268,52,97,202,394,410⟩,⟨19,35,76,268,52,97,192,384,272⟩,[⟨2,1210181569277353567352593,⟨51,35,234,491,115,99,192,387,307⟩⟩,⟨3,1210107565425412734483741,⟨19,35,119,311,55,99,192,385,275⟩⟩]⟩
theorem node525 : UpperPrefix a [4,5,6,8,2,0] 30 :=
  Boolean.leaf_sound a [4,5,6,8,2,0] 30 cert525 (by decide +kernel)

def cert526 : Leaf := ⟨⟨288,272,401,145,321,273,281,25,141⟩,[],[(5,1,0),(6,2,4),(1,5,1)],⟨19,35,76,268,52,98,201,393,409⟩,⟨19,35,76,268,52,98,192,384,272⟩,[⟨2,1210181496797547064210705,⟨19,35,234,491,51,98,192,385,275⟩⟩,⟨3,1210107565425412734467357,⟨19,35,119,311,55,98,192,385,275⟩⟩,⟨7,1208926973804696396905757,⟨19,35,127,319,55,98,64,257,275⟩⟩]⟩
theorem node526 : UpperPrefix a [4,5,6,8,2,1] 30 :=
  Boolean.leaf_sound a [4,5,6,8,2,1] 30 cert526 (by decide +kernel)

def cert527 : Leaf := ⟨⟨416,400,0,147,459,0,275,19,131⟩,[(2,5),(5,2)],[(5,1,0),(6,2,4),(3,5,4)],⟨19,35,76,268,52,104,195,387,403⟩,⟨19,35,76,268,52,104,192,384,272⟩,[⟨2,1293003108276056203736337,⟨467,483,234,491,499,234,192,449,467⟩⟩]⟩
theorem node527 : UpperPrefix a [4,5,6,8,2,3] 30 :=
  Boolean.leaf_sound a [4,5,6,8,2,3] 30 cert527 (by decide +kernel)

def cert528 : Leaf := ⟨⟨288,272,275,19,323,0,283,27,15⟩,[(5,6)],[(5,1,0),(6,2,4),(7,5,5)],⟨19,35,76,268,52,224,203,395,283⟩,⟨19,35,76,268,52,224,192,384,272⟩,[⟨2,1210181499049346877895953,⟨19,35,234,491,51,224,224,385,275⟩⟩,⟨3,1210107567535925303979293,⟨19,35,119,279,55,224,224,385,275⟩⟩]⟩
theorem node528 : UpperPrefix a [4,5,6,8,2,7] 30 :=
  Boolean.leaf_sound a [4,5,6,8,2,7] 30 cert528 (by decide +kernel)

theorem node529 : UpperPrefix a [4,5,6,8,2] 30 :=
  branch_upper a [4,5,6,8,2] 30 (by decide) (fin9_cases _
  node525
  node526
  (invalid_upper a [4,5,6,8,2,2] 30 (by decide +kernel))
  node527
  (invalid_upper a [4,5,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,2,6] 30 (by decide +kernel))
  node528
  (invalid_upper a [4,5,6,8,2,8] 30 (by decide +kernel)))

def cert530 : Leaf := ⟨⟨352,0,402,210,322,274,278,86,206⟩,[(1,5)],[(5,1,0),(0,5,1)],⟨19,35,76,268,56,97,198,390,406⟩,⟨19,35,76,268,56,97,192,384,272⟩,[⟨3,1210181569277352494659345,⟨51,35,230,487,243,99,192,387,307⟩⟩,⟨2,1210107565425413807176989,⟨19,35,123,315,59,99,192,385,275⟩⟩,⟨7,1208926973804696396922141,⟨19,35,127,319,59,99,64,257,275⟩⟩]⟩
theorem node530 : UpperPrefix a [4,5,6,8,3,0] 30 :=
  Boolean.leaf_sound a [4,5,6,8,3,0] 30 cert530 (by decide +kernel)

def cert531 : Leaf := ⟨⟨96,80,401,209,65,17,277,85,205⟩,[],[(5,1,0),(1,5,1)],⟨19,35,76,268,56,98,197,389,405⟩,⟨19,35,76,268,56,98,192,384,272⟩,[⟨3,1210181497360495945070353,⟨51,35,230,487,243,98,192,387,307⟩⟩,⟨2,1210107565425413807160605,⟨19,35,123,315,59,98,192,385,275⟩⟩,⟨7,1208926973804696396905757,⟨19,35,127,319,59,98,64,257,275⟩⟩,⟨8,1181745810784633503005,⟨19,35,127,63,59,98,192,129,19⟩⟩]⟩
theorem node531 : UpperPrefix a [4,5,6,8,3,1] 30 :=
  Boolean.leaf_sound a [4,5,6,8,3,1] 30 cert531 (by decide +kernel)

def cert532 : Leaf := ⟨⟨416,400,403,147,391,0,275,19,131⟩,[(5,2)],[(5,1,0),(6,2,5),(2,5,4)],⟨19,35,76,268,56,100,195,387,403⟩,⟨19,35,76,268,56,100,192,384,272⟩,[⟨3,1293003108276055131043089,⟨467,483,230,487,499,100,192,449,467⟩⟩]⟩
theorem node532 : UpperPrefix a [4,5,6,8,3,2] 30 :=
  Boolean.leaf_sound a [4,5,6,8,3,2] 30 cert532 (by decide +kernel)

def cert533 : Leaf := ⟨⟨96,80,275,83,67,0,279,87,79⟩,[(5,6)],[(5,1,0),(7,5,5)],⟨19,35,76,268,56,224,199,391,279⟩,⟨19,35,76,268,56,224,192,384,272⟩,[⟨3,1210181499612295758755601,⟨51,35,230,487,243,224,224,387,307⟩⟩,⟨2,1210107567535926376672541,⟨19,35,123,283,59,224,224,385,275⟩⟩,⟨8,1181747921297203014941,⟨19,35,127,31,59,224,224,129,19⟩⟩]⟩
theorem node533 : UpperPrefix a [4,5,6,8,3,7] 30 :=
  Boolean.leaf_sound a [4,5,6,8,3,7] 30 cert533 (by decide +kernel)

theorem node534 : UpperPrefix a [4,5,6,8,3] 30 :=
  branch_upper a [4,5,6,8,3] 30 (by decide) (fin9_cases _
  node530
  node531
  node532
  (invalid_upper a [4,5,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,3,6] 30 (by decide +kernel))
  node533
  (invalid_upper a [4,5,6,8,3,8] 30 (by decide +kernel)))

def cert535 : Leaf := ⟨⟨480,0,386,194,322,386,270,94,206⟩,[(1,5)],[(5,1,0),(0,5,1)],⟨19,35,76,268,176,97,206,398,286⟩,⟨19,35,76,268,176,97,192,384,272⟩,[⟨4,1210107853548364325996033,⟨103,35,76,268,238,103,204,396,332⟩⟩,⟨2,1210107567680787033685365,⟨19,35,123,299,179,115,243,385,275⟩⟩,⟨3,1210107567680785960992117,⟨19,35,119,295,179,115,243,385,275⟩⟩]⟩
theorem node535 : UpperPrefix a [4,5,6,8,7,0] 30 :=
  Boolean.leaf_sound a [4,5,6,8,7,0] 30 cert535 (by decide +kernel)

def cert536 : Leaf := ⟨⟨32,16,401,209,65,17,285,29,205⟩,[],[(5,1,0),(1,5,1)],⟨19,35,76,268,176,98,205,397,285⟩,⟨19,35,76,268,176,98,192,384,272⟩,[⟨2,1210107567680787033685365,⟨19,35,123,299,179,115,243,385,275⟩⟩,⟨3,1210107567680785960992117,⟨19,35,119,295,179,115,243,385,275⟩⟩,⟨8,1181748066157860027765,⟨19,35,127,47,179,115,243,129,19⟩⟩,⟨6,1210180199338641917486353,⟨19,35,140,397,179,34,128,385,275⟩⟩,⟨7,1208926973803871763182865,⟨19,35,110,303,51,98,64,257,275⟩⟩]⟩
theorem node536 : UpperPrefix a [4,5,6,8,7,1] 30 :=
  Boolean.leaf_sound a [4,5,6,8,7,1] 30 cert536 (by decide +kernel)

def cert537 : Leaf := ⟨⟨300,284,274,18,270,0,286,30,14⟩,[(5,2)],[(5,1,0),(6,2,5)],⟨19,35,76,268,176,100,193,394,282⟩,⟨19,35,76,268,176,100,193,384,272⟩,[⟨0,1224302337245652857127936,⟨410,446,124,300,180,124,508,384,272⟩⟩,⟨7,1289207206264466576553233,⟨283,303,110,303,319,110,367,257,283⟩⟩]⟩
theorem node537 : UpperPrefix a [4,5,6,8,7,2,0] 30 :=
  Boolean.leaf_sound a [4,5,6,8,7,2,0] 30 cert537 (by decide +kernel)

def cert538 : Leaf := ⟨⟨424,408,401,145,269,0,281,25,141⟩,[(5,2)],[(5,1,0),(6,2,5)],⟨19,35,76,268,176,100,194,393,281⟩,⟨19,35,76,268,176,100,194,384,272⟩,[⟨1,1224302337245652857126913,⟨409,445,124,300,180,124,508,384,272⟩⟩,⟨2,1210181640490522674996497,⟨83,35,200,393,243,96,194,385,339⟩⟩]⟩
theorem node538 : UpperPrefix a [4,5,6,8,7,2,1] 30 :=
  Boolean.leaf_sound a [4,5,6,8,7,2,1] 30 cert538 (by decide +kernel)

def cert539 : Local := ⟨⟨164,148,0,147,7,0,279,23,135⟩,[(2,6),(5,2)],[(5,1,0),(6,2,5),(8,3,6),(3,6,2),(3,6,5)]⟩
theorem node539 : UpperPrefix a [4,5,6,8,7,2,3] 30 :=
  local_sound a [4,5,6,8,7,2,3] 30 cert539 (by decide +kernel)

theorem node540 : UpperPrefix a [4,5,6,8,7,2] 30 :=
  branch_upper a [4,5,6,8,7,2] 30 (by decide) (fin9_cases _
  node537
  node538
  (invalid_upper a [4,5,6,8,7,2,2] 30 (by decide +kernel))
  node539
  (invalid_upper a [4,5,6,8,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,2,8] 30 (by decide +kernel)))

def cert541 : Leaf := ⟨⟨96,80,0,83,335,0,31,95,79⟩,[(2,5),(5,2)],[(5,1,0)],⟨19,35,76,268,176,104,199,391,279⟩,⟨19,35,76,268,176,104,192,384,272⟩,[⟨7,1284484837529788242474257,⟨283,39,110,303,319,110,64,257,283⟩⟩,⟨8,1182034040336159880465,⟨83,39,110,47,247,110,192,129,83⟩⟩,⟨2,1210107565424589173437713,⟨19,35,106,299,179,106,192,385,275⟩⟩,⟨3,1210107565283850612385041,⟨19,35,68,261,179,96,192,385,275⟩⟩]⟩
theorem node541 : UpperPrefix a [4,5,6,8,7,3] 30 :=
  Boolean.leaf_sound a [4,5,6,8,7,3] 30 cert541 (by decide +kernel)

theorem node542 : UpperPrefix a [4,5,6,8,7] 30 :=
  branch_upper a [4,5,6,8,7] 30 (by decide) (fin9_cases _
  node535
  node536
  node540
  node541
  (invalid_upper a [4,5,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,7,8] 30 (by decide +kernel)))

theorem node543 : UpperPrefix a [4,5,6,8] 30 :=
  branch_upper a [4,5,6,8] 30 (by decide) (fin9_cases _
  node523
  node524
  node529
  node534
  (invalid_upper a [4,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,8,6] 30 (by decide +kernel))
  node542
  (invalid_upper a [4,5,6,8,8] 30 (by decide +kernel)))

theorem node544 : UpperPrefix a [4,5,6] 30 :=
  branch_upper a [4,5,6] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut28 [4,5,6,0] [2,4,7,8] 30 (by decide +kernel) node401)
  (PrefixConjugacy.upper aut38 [4,5,6,1] [2,4,8,7] 30 (by decide +kernel) node511)
  (invalid_upper a [4,5,6,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,6] 30 (by decide +kernel))
  node522
  node543)

theorem node545 : UpperPrefix a [4,5,7] 30 :=
  branch_upper a [4,5,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut27 [4,5,7,0] [2,4,6,7] 30 (by decide +kernel) node271)
  (PrefixConjugacy.upper aut37 [4,5,7,1] [2,4,7,6] 30 (by decide +kernel) node383)
  (invalid_upper a [4,5,7,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,5,7,6] [4,5,6,7] 30 (by decide +kernel) node522)
  (invalid_upper a [4,5,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut22 [4,5,7,8] [4,5,6,7] 30 (by decide +kernel) node522))

theorem node546 : UpperPrefix a [4,5,8] 30 :=
  branch_upper a [4,5,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut26 [4,5,8,0] [2,4,5,6] 30 (by decide +kernel) node160)
  (PrefixConjugacy.upper aut36 [4,5,8,1] [2,4,6,5] 30 (by decide +kernel) node254)
  (invalid_upper a [4,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,5,8,6] [4,5,6,8] 30 (by decide +kernel) node543)
  (PrefixConjugacy.upper aut27 [4,5,8,7] [4,5,6,7] 30 (by decide +kernel) node522)
  (invalid_upper a [4,5,8,8] 30 (by decide +kernel)))

theorem node547 : UpperPrefix a [4,5] 30 :=
  branch_upper a [4,5] 30 (by decide) (fin9_cases _
  node515
  node516
  (invalid_upper a [4,5,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,5] 30 (by decide +kernel))
  node544
  node545
  node546)

theorem node548 : UpperPrefix a [4,6,0] 30 :=
  branch_upper a [4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut20 [4,6,0,1] [2,3,4,6] 30 (by decide +kernel) node34)
  (invalid_upper a [4,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [4,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,0,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut24 [4,6,0,5] [2,4,8,5] 30 (by decide +kernel) node446)
  (invalid_upper a [4,6,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut22 [4,6,0,7] [2,4,6,8] 30 (by decide +kernel) node309)
  (PrefixConjugacy.upper aut21 [4,6,0,8] [2,4,5,7] 30 (by decide +kernel) node185))

theorem node549 : UpperPrefix a [4,6,1] 30 :=
  branch_upper a [4,6,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut25 [4,6,1,0] [2,3,4,6] 30 (by decide +kernel) node34)
  (invalid_upper a [4,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [4,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [4,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,1,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut34 [4,6,1,5] [2,4,5,8] 30 (by decide +kernel) node214)
  (invalid_upper a [4,6,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut32 [4,6,1,7] [2,4,8,6] 30 (by decide +kernel) node490)
  (PrefixConjugacy.upper aut31 [4,6,1,8] [2,4,7,5] 30 (by decide +kernel) node352))

def cert550 : Leaf := ⟨⟨172,188,144,48,142,0,316,60,172⟩,[(5,1)],[(6,1,5),(0,4,0),(1,5,4)],⟨19,67,44,140,49,98,460,396,284⟩,⟨19,67,44,140,49,98,192,384,272⟩,[⟨8,1181747998477791052919,⟨55,127,63,157,55,127,255,128,17⟩⟩]⟩
theorem node550 : UpperPrefix a [4,6,5,7,0,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,1] 30 cert550 (by decide +kernel)

def cert551 : Leaf := ⟨⟨104,56,144,48,72,152,314,58,42⟩,[],[(0,4,0),(2,5,2)],⟨19,67,44,140,49,100,458,394,282⟩,⟨19,67,44,140,49,100,192,384,272⟩,[⟨8,1181747998477791052919,⟨55,127,63,157,55,127,255,128,17⟩⟩,⟨1,1210107567606235018035201,⟨53,125,44,140,53,108,236,384,272⟩⟩,⟨6,1214856448961329574708225,⟨415,395,44,140,445,36,128,384,284⟩⟩,⟨7,1227816439597086756848693,⟨19,67,319,285,51,375,64,256,273⟩⟩]⟩
theorem node551 : UpperPrefix a [4,6,5,7,0,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,2] 30 cert551 (by decide +kernel)

def cert552 : Leaf := ⟨⟨100,52,0,112,68,148,310,118,102⟩,[(2,5)],[(7,3,5),(0,4,0),(3,5,2)],⟨19,67,44,140,49,104,454,390,278⟩,⟨19,67,44,140,49,104,192,384,272⟩,[⟨8,1181747998477791052919,⟨55,127,63,157,55,127,255,128,17⟩⟩,⟨1,1210107567606235018035201,⟨53,125,44,140,53,108,236,384,272⟩⟩]⟩
theorem node552 : UpperPrefix a [4,6,5,7,0,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,3] 30 cert552 (by decide +kernel)

def cert553 : Leaf := ⟨⟨480,416,448,352,448,128,288,108,236⟩,[],[(0,4,0),(1,6,1)],⟨19,67,44,140,49,352,194,396,284⟩,⟨19,67,44,140,49,352,194,384,272⟩,[⟨4,1212768809856627052127745,⟨79,79,172,172,239,492,238,492,494⟩⟩,⟨2,1210110019761866398620927,⟨19,83,123,251,51,371,243,499,273⟩⟩,⟨3,1210110019761865325927679,⟨19,83,119,247,51,371,243,499,273⟩⟩]⟩
theorem node553 : UpperPrefix a [4,6,5,7,0,8,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,8,1] 30 cert553 (by decide +kernel)

def cert554 : Leaf := ⟨⟨360,312,466,0,330,26,0,122,106⟩,[(3,6),(6,3)],[(0,4,0)],⟨19,67,44,140,49,352,196,394,282⟩,⟨19,67,44,140,49,352,196,384,272⟩,[⟨2,1229033926962286885389431,⟨19,115,443,409,51,371,499,384,273⟩⟩,⟨7,1227816441853422056031351,⟨19,115,319,285,51,371,375,256,273⟩⟩]⟩
theorem node554 : UpperPrefix a [4,6,5,7,0,8,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,8,2] 30 cert554 (by decide +kernel)

def cert555 : Leaf := ⟨⟨356,292,322,354,326,14,0,102,102⟩,[(6,3)],[(7,3,6),(0,4,0)],⟨19,67,44,140,49,352,200,390,278⟩,⟨19,67,44,140,49,352,200,384,272⟩,[⟨3,1229033924705950513513525,⟨19,67,439,405,51,371,192,384,273⟩⟩,⟨4,1212476400140018456208385,⟨7,79,108,236,111,492,236,492,494⟩⟩]⟩
theorem node555 : UpperPrefix a [4,6,5,7,0,8,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,0,8,3] 30 cert555 (by decide +kernel)

theorem node556 : UpperPrefix a [4,6,5,7,0,8] 30 :=
  branch_upper a [4,6,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,5,7,0,8,0] 30 (by decide +kernel))
  node553
  node554
  node555
  (invalid_upper a [4,6,5,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,8,8] 30 (by decide +kernel)))

theorem node557 : UpperPrefix a [4,6,5,7,0] 30 :=
  branch_upper a [4,6,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,5,7,0,0] 30 (by decide +kernel))
  node550
  node551
  node552
  (invalid_upper a [4,6,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,0,7] 30 (by decide +kernel))
  node556)

def cert558 : Local := ⟨⟨0,0,400,304,461,0,316,60,172⟩,[(0,4),(1,5),(5,1)],[(6,1,4),(1,4,0),(0,5,4)]⟩
theorem node558 : UpperPrefix a [4,6,5,7,1,0] 30 :=
  local_sound a [4,6,5,7,1,0] 30 cert558 (by decide +kernel)

def cert559 : Leaf := ⟨⟨0,184,144,48,200,152,313,57,169⟩,[(0,4)],[(6,1,4),(1,4,0),(2,5,2)],⟨19,67,44,140,50,100,457,393,281⟩,⟨19,67,44,140,50,100,192,384,272⟩,[⟨8,1181747998477791052919,⟨55,127,63,157,55,127,255,128,17⟩⟩,⟨0,1210107567606235018036224,⟨54,126,44,140,54,108,236,384,272⟩⟩]⟩
theorem node559 : UpperPrefix a [4,6,5,7,1,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,1,2] 30 cert559 (by decide +kernel)

def cert560 : Local := ⟨⟨0,308,0,305,325,405,309,53,37⟩,[(0,4),(2,5)],[(6,1,4),(7,3,5),(1,4,0),(3,5,2)]⟩
theorem node560 : UpperPrefix a [4,6,5,7,1,3] 30 :=
  local_sound a [4,6,5,7,1,3] 30 cert560 (by decide +kernel)

def cert561 : Local := ⟨⟨0,0,400,304,460,156,316,60,172⟩,[(0,4),(1,6)],[(6,1,4),(1,4,0),(0,6,1)]⟩
theorem node561 : UpperPrefix a [4,6,5,7,1,8,0] 30 :=
  local_sound a [4,6,5,7,1,8,0] 30 cert561 (by decide +kernel)

def cert562 : Leaf := ⟨⟨0,440,401,0,457,153,0,57,169⟩,[(0,4),(3,6),(6,3)],[(6,1,4),(1,4,0)],⟨19,67,44,140,50,352,196,393,281⟩,⟨19,67,44,140,50,352,196,384,272⟩,[⟨2,1266886645801538885305463,⟨19,115,443,409,51,371,499,384,273⟩⟩]⟩
theorem node562 : UpperPrefix a [4,6,5,7,1,8,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,1,8,2] 30 cert562 (by decide +kernel)

def cert563 : Local := ⟨⟨0,316,273,305,333,29,0,61,45⟩,[(0,4),(6,3)],[(6,1,4),(7,3,6),(1,4,0)]⟩
theorem node563 : UpperPrefix a [4,6,5,7,1,8,3] 30 :=
  local_sound a [4,6,5,7,1,8,3] 30 cert563 (by decide +kernel)

theorem node564 : UpperPrefix a [4,6,5,7,1,8] 30 :=
  branch_upper a [4,6,5,7,1,8] 30 (by decide) (fin9_cases _
  node561
  (invalid_upper a [4,6,5,7,1,8,1] 30 (by decide +kernel))
  node562
  node563
  (invalid_upper a [4,6,5,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,8,8] 30 (by decide +kernel)))

theorem node565 : UpperPrefix a [4,6,5,7,1] 30 :=
  branch_upper a [4,6,5,7,1] 30 (by decide) (fin9_cases _
  node558
  (invalid_upper a [4,6,5,7,1,1] 30 (by decide +kernel))
  node559
  node560
  (invalid_upper a [4,6,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,1,7] 30 (by decide +kernel))
  node564)

def cert566 : Leaf := ⟨⟨460,0,466,338,0,0,286,94,206⟩,[(1,5),(4,2),(5,1)],[(5,2,4)],⟨19,67,44,140,52,97,458,394,282⟩,⟨19,67,44,140,52,97,192,384,272⟩,[⟨0,1214857655928505767035904,⟨478,458,60,156,60,508,192,384,276⟩⟩]⟩
theorem node566 : UpperPrefix a [4,6,5,7,2,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,0] 30 cert566 (by decide +kernel)

def cert567 : Leaf := ⟨⟨396,412,401,273,0,0,285,29,141⟩,[(4,2),(5,1)],[(6,1,5),(5,2,4)],⟨19,67,44,140,52,98,457,393,281⟩,⟨19,67,44,140,52,98,192,384,272⟩,[⟨1,1214857655928505767034881,⟨477,457,60,156,60,252,192,384,276⟩⟩]⟩
theorem node567 : UpperPrefix a [4,6,5,7,2,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,1] 30 cert567 (by decide +kernel)

def cert568 : Leaf := ⟨⟨320,272,0,339,0,403,275,83,67⟩,[(2,5),(4,2)],[(5,2,4),(7,3,5),(3,5,2),(3,5,4)],⟨19,67,44,140,52,104,451,387,275⟩,⟨19,67,44,140,52,104,192,384,272⟩,[⟨2,1292931482886845015205649,⟨467,451,40,234,499,104,194,451,467⟩⟩]⟩
theorem node568 : UpperPrefix a [4,6,5,7,2,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,3] 30 cert568 (by decide +kernel)

def cert569 : Leaf := ⟨⟨452,0,450,322,0,158,278,78,206⟩,[(1,6),(4,2)],[(5,2,4),(0,6,1)],⟨19,67,44,140,52,352,193,394,282⟩,⟨19,67,44,140,52,352,193,384,272⟩,[⟨4,1210402713187938519254017,⟨15,67,172,140,172,494,195,384,268⟩⟩,⟨3,1210107709399313566178333,⟨19,67,119,215,55,354,195,384,273⟩⟩]⟩
theorem node569 : UpperPrefix a [4,6,5,7,2,8,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,8,0] 30 cert569 (by decide +kernel)

def cert570 : Local := ⟨⟨460,396,448,320,0,140,269,92,204⟩,[(4,2)],[(4,0,7),(5,2,4),(1,6,1),(0,7,6)]⟩
theorem node570 : UpperPrefix a [4,6,5,7,2,8,1,0] 30 :=
  local_sound a [4,6,5,7,2,8,1,0] 30 cert570 (by decide +kernel)

def cert571 : Leaf := ⟨⟨452,404,401,273,0,149,277,21,133⟩,[(4,2)],[(5,2,4),(1,6,1),(3,7,3)],⟨19,67,44,140,52,352,194,392,273⟩,⟨19,67,44,140,52,352,194,392,272⟩,[⟨6,1217512780110456851268609,⟨415,395,188,156,188,444,130,392,412⟩⟩]⟩
theorem node571 : UpperPrefix a [4,6,5,7,2,8,1,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,8,1,3] 30 cert571 (by decide +kernel)

theorem node572 : UpperPrefix a [4,6,5,7,2,8,1] 30 :=
  branch_upper a [4,6,5,7,2,8,1] 30 (by decide) (fin9_cases _
  node570
  (invalid_upper a [4,6,5,7,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,1,2] 30 (by decide +kernel))
  node571
  (invalid_upper a [4,6,5,7,2,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,1,8] 30 (by decide +kernel)))

def cert573 : Leaf := ⟨⟨328,280,339,339,0,27,0,91,75⟩,[(4,2),(6,3)],[(5,2,4),(7,3,6)],⟨19,67,44,140,52,352,200,387,275⟩,⟨19,67,44,140,52,352,200,384,272⟩,[⟨2,1293219587514050881283345,⟨435,483,234,200,499,483,200,385,435⟩⟩]⟩
theorem node573 : UpperPrefix a [4,6,5,7,2,8,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,2,8,3] 30 cert573 (by decide +kernel)

theorem node574 : UpperPrefix a [4,6,5,7,2,8] 30 :=
  branch_upper a [4,6,5,7,2,8] 30 (by decide) (fin9_cases _
  node569
  node572
  (invalid_upper a [4,6,5,7,2,8,2] 30 (by decide +kernel))
  node573
  (invalid_upper a [4,6,5,7,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,8,8] 30 (by decide +kernel)))

theorem node575 : UpperPrefix a [4,6,5,7,2] 30 :=
  branch_upper a [4,6,5,7,2] 30 (by decide) (fin9_cases _
  node566
  node567
  (invalid_upper a [4,6,5,7,2,2] 30 (by decide +kernel))
  node568
  (invalid_upper a [4,6,5,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,2,7] 30 (by decide +kernel))
  node574)

#print axioms node575
end Delivery.FiniteExclusion.Sharp2x2x5
