import RegularNineSharp2x7Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert64 : Leaf := ⟨⟨312,308,336,292,262,276,308,52,176⟩,[],[(3,1,0),(6,3,2),(1,5,4)],⟨7,11,44,88,49,98,464,400,404⟩,⟨7,11,44,88,49,98,192,384,260⟩,[⟨0,1323666154217542809814016,⟨38,494,492,476,508,102,192,384,260⟩⟩,⟨7,1208926976203981124599167,⟨23,63,63,127,63,127,127,257,279⟩⟩]⟩
theorem node64 : UpperPrefix a [2,3,5,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,0,1] 30 cert64 (by decide +kernel)

def cert65 : Leaf := ⟨⟨392,388,467,0,390,0,263,7,131⟩,[(3,5),(5,3)],[(3,1,0),(6,3,2),(4,5,2)],⟨7,11,44,88,49,112,450,386,390⟩,⟨7,11,44,88,49,112,192,384,260⟩,[⟨5,1236297743387773075729669,⟨455,459,463,218,475,218,192,449,455⟩⟩]⟩
theorem node65 : UpperPrefix a [2,3,5,6,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,0,4] 30 cert65 (by decide +kernel)

def cert66 : Leaf := ⟨⟨40,36,67,39,6,0,311,55,51⟩,[(5,6)],[(3,1,0),(6,3,2),(7,5,5)],⟨7,11,44,88,49,224,466,402,278⟩,⟨7,11,44,88,49,224,192,384,260⟩,[⟨8,1181747928456945007999,⟨23,31,63,127,63,255,255,129,23⟩⟩,⟨4,1210107567534551990279439,⟨7,15,47,111,33,224,224,385,263⟩⟩]⟩
theorem node66 : UpperPrefix a [2,3,5,6,0,7] 30 :=
  Boolean.leaf_sound a [2,3,5,6,0,7] 30 cert66 (by decide +kernel)

def cert67 : Leaf := ⟨⟨312,308,336,293,260,148,308,52,176⟩,[],[(3,1,0),(6,3,2)],⟨7,11,44,88,49,352,194,400,404⟩,⟨7,11,44,88,49,352,194,384,260⟩,[⟨1,1640682244613764032233473,⟨405,445,428,508,437,492,508,384,260⟩⟩,⟨0,1247960320503744428508160,⟨102,494,428,508,48,352,230,384,260⟩⟩,⟨7,1208926973665612483558717,⟨23,11,63,95,63,383,66,257,279⟩⟩]⟩
theorem node67 : UpperPrefix a [2,3,5,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,0,8,1] 30 cert67 (by decide +kernel)

def cert68 : Leaf := ⟨⟨424,420,450,0,390,134,294,38,162⟩,[(3,6)],[(3,1,0),(6,3,2),(4,6,3)],⟨7,11,44,88,49,352,208,386,390⟩,⟨7,11,44,88,49,352,208,384,260⟩,[⟨0,1224302623641908060095488,⟨390,398,44,124,508,364,252,384,260⟩⟩]⟩
theorem node68 : UpperPrefix a [2,3,5,6,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,0,8,4] 30 cert68 (by decide +kernel)

theorem node69 : UpperPrefix a [2,3,5,6,0,8] 30 :=
  branch_upper a [2,3,5,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,6,0,8,0] 30 (by decide +kernel))
  node67
  (invalid_upper a [2,3,5,6,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,0,8,3] 30 (by decide +kernel))
  node68
  (invalid_upper a [2,3,5,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,0,8,8] 30 (by decide +kernel)))

theorem node70 : UpperPrefix a [2,3,5,6,0] 30 :=
  branch_upper a [2,3,5,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,6,0,0] 30 (by decide +kernel))
  node64
  (invalid_upper a [2,3,5,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,0,3] 30 (by decide +kernel))
  node65
  (invalid_upper a [2,3,5,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,0,6] 30 (by decide +kernel))
  node66
  node69)

def cert71 : Leaf := ⟨⟨312,308,336,292,261,276,308,52,176⟩,[],[(3,1,0),(6,3,2),(0,5,4)],⟨7,11,44,88,50,97,464,400,404⟩,⟨7,11,44,88,50,97,192,384,260⟩,[⟨1,1323666154217542809812993,⟨37,493,492,476,508,97,192,384,260⟩⟩,⟨7,1208926976203981124599167,⟨23,63,63,127,63,127,127,257,279⟩⟩]⟩
theorem node71 : UpperPrefix a [2,3,5,6,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,1,0] 30 cert71 (by decide +kernel)

def cert72 : Leaf := ⟨⟨392,388,467,0,389,0,263,7,131⟩,[(3,5),(5,3)],[(3,1,0),(6,3,2),(4,5,2)],⟨7,11,44,88,50,112,449,385,389⟩,⟨7,11,44,88,50,112,192,384,260⟩,[⟨5,1236152187047816461290757,⟨455,459,463,88,218,88,192,449,455⟩⟩]⟩
theorem node72 : UpperPrefix a [2,3,5,6,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,1,4] 30 cert72 (by decide +kernel)

def cert73 : Leaf := ⟨⟨40,36,67,39,5,0,311,55,51⟩,[(5,6)],[(3,1,0),(6,3,2),(7,5,5)],⟨7,11,44,88,50,224,465,401,277⟩,⟨7,11,44,88,50,224,192,384,260⟩,[⟨8,1181747928456945007999,⟨23,31,63,127,63,255,255,129,23⟩⟩,⟨4,1210107567534551990279439,⟨7,15,47,111,35,224,224,385,263⟩⟩]⟩
theorem node73 : UpperPrefix a [2,3,5,6,1,7] 30 :=
  Boolean.leaf_sound a [2,3,5,6,1,7] 30 cert73 (by decide +kernel)

def cert74 : Leaf := ⟨⟨184,180,208,165,132,148,52,52,176⟩,[],[(3,1,0),(6,3,2)],⟨7,11,44,88,50,352,193,400,404⟩,⟨7,11,44,88,50,352,193,384,260⟩,[⟨1,1323665758745200533438465,⟨101,493,428,508,508,352,193,384,260⟩⟩,⟨8,1184051514709933849917,⟨23,11,63,95,63,127,193,193,23⟩⟩,⟨0,1337860493899739417805824,⟨406,446,428,508,438,352,480,384,260⟩⟩]⟩
theorem node74 : UpperPrefix a [2,3,5,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,1,8,0] 30 cert74 (by decide +kernel)

def cert75 : Leaf := ⟨⟨424,420,449,0,389,133,293,37,161⟩,[(3,6)],[(3,1,0),(6,3,2),(4,6,3)],⟨7,11,44,88,50,352,208,385,389⟩,⟨7,11,44,88,50,352,208,384,260⟩,[⟨1,1224302623641908060094465,⟨389,397,44,124,508,364,252,384,260⟩⟩]⟩
theorem node75 : UpperPrefix a [2,3,5,6,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,1,8,4] 30 cert75 (by decide +kernel)

theorem node76 : UpperPrefix a [2,3,5,6,1,8] 30 :=
  branch_upper a [2,3,5,6,1,8] 30 (by decide) (fin9_cases _
  node74
  (invalid_upper a [2,3,5,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,8,3] 30 (by decide +kernel))
  node75
  (invalid_upper a [2,3,5,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,8,8] 30 (by decide +kernel)))

theorem node77 : UpperPrefix a [2,3,5,6,1] 30 :=
  branch_upper a [2,3,5,6,1] 30 (by decide) (fin9_cases _
  node71
  (invalid_upper a [2,3,5,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,3] 30 (by decide +kernel))
  node72
  (invalid_upper a [2,3,5,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,1,6] 30 (by decide +kernel))
  node73
  node76)

def cert78 : Leaf := ⟨⟨8,4,67,167,7,6,311,55,51⟩,[],[(3,1,0),(6,3,2),(7,4,3)],⟨7,11,44,88,176,97,466,402,278⟩,⟨7,11,44,88,176,97,192,384,260⟩,[⟨8,1181748206908265266559,⟨7,47,47,127,191,127,255,129,7⟩⟩,⟨4,1210107565564227153829135,⟨7,47,47,111,160,97,192,385,263⟩⟩,⟨5,1210107564157951779278085,⟨7,11,15,88,144,65,192,385,263⟩⟩]⟩
theorem node78 : UpperPrefix a [2,3,5,6,7,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,0] 30 cert78 (by decide +kernel)

def cert79 : Leaf := ⟨⟨8,4,67,167,7,5,311,55,51⟩,[],[(3,1,0),(6,3,2),(7,4,3)],⟨7,11,44,88,176,98,465,401,277⟩,⟨7,11,44,88,176,98,192,384,260⟩,[⟨8,1181748206908265266559,⟨7,47,47,127,191,127,255,129,7⟩⟩,⟨4,1210107565564227153829167,⟨7,47,47,111,161,103,192,385,263⟩⟩,⟨5,1210107564157951779278085,⟨7,11,15,88,144,66,192,385,263⟩⟩]⟩
theorem node79 : UpperPrefix a [2,3,5,6,7,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,1] 30 cert79 (by decide +kernel)

def cert80 : Local := ⟨⟨296,292,339,0,263,0,295,39,35⟩,[(3,5),(5,3)],[(3,1,0),(6,3,2),(7,4,3),(7,4,5),(4,5,2)]⟩
theorem node80 : UpperPrefix a [2,3,5,6,7,4] 30 :=
  local_sound a [2,3,5,6,7,4] 30 cert80 (by decide +kernel)

def cert81 : Leaf := ⟨⟨8,4,83,135,263,7,6,55,51⟩,[],[(3,1,0),(6,3,2),(7,4,3),(8,5,4)],⟨7,11,44,88,176,352,193,402,278⟩,⟨7,11,44,88,176,352,193,384,260⟩,[⟨4,1210109875629361015557381,⟨7,11,47,72,224,353,225,481,263⟩⟩,⟨5,1210109870000963140455685,⟨7,11,15,88,216,321,193,449,263⟩⟩]⟩
theorem node81 : UpperPrefix a [2,3,5,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,8,0] 30 cert81 (by decide +kernel)

def cert82 : Local := ⟨⟨56,48,82,162,258,18,49,54,50⟩,[],[(2,0,7),(3,1,0),(6,3,2),(7,4,3),(8,5,4),(0,7,6)]⟩
theorem node82 : UpperPrefix a [2,3,5,6,7,8,1,0] 30 :=
  local_sound a [2,3,5,6,7,8,1,0] 30 cert82 (by decide +kernel)

def cert83 : Leaf := ⟨⟨56,52,81,165,261,21,53,37,49⟩,[],[(3,1,0),(6,3,2),(7,4,3),(8,5,4)],⟨7,11,44,88,176,352,194,400,261⟩,⟨7,11,44,88,176,352,194,400,260⟩,[⟨1,1227548964064778500702209,⟨405,413,188,252,188,508,508,404,404⟩⟩]⟩
theorem node83 : UpperPrefix a [2,3,5,6,7,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,8,1,4] 30 cert83 (by decide +kernel)

theorem node84 : UpperPrefix a [2,3,5,6,7,8,1] 30 :=
  branch_upper a [2,3,5,6,7,8,1] 30 (by decide) (fin9_cases _
  node82
  (invalid_upper a [2,3,5,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,3] 30 (by decide +kernel))
  node83
  (invalid_upper a [2,3,5,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,8] 30 (by decide +kernel)))

def cert85 : Local := ⟨⟨40,36,67,0,263,7,0,39,35⟩,[(3,6),(6,4)],[(3,1,0),(6,3,2),(7,4,3),(7,4,6),(8,5,4),(4,6,3)]⟩
theorem node85 : UpperPrefix a [2,3,5,6,7,8,4] 30 :=
  local_sound a [2,3,5,6,7,8,4] 30 cert85 (by decide +kernel)

theorem node86 : UpperPrefix a [2,3,5,6,7,8] 30 :=
  branch_upper a [2,3,5,6,7,8] 30 (by decide) (fin9_cases _
  node81
  node84
  (invalid_upper a [2,3,5,6,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,3] 30 (by decide +kernel))
  node85
  (invalid_upper a [2,3,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,8] 30 (by decide +kernel)))

theorem node87 : UpperPrefix a [2,3,5,6,7] 30 :=
  branch_upper a [2,3,5,6,7] 30 (by decide) (fin9_cases _
  node78
  node79
  (invalid_upper a [2,3,5,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,3] 30 (by decide +kernel))
  node80
  (invalid_upper a [2,3,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,7] 30 (by decide +kernel))
  node86)

def cert88 : Leaf := ⟨⟨8,4,67,391,135,6,279,23,179⟩,[],[(3,1,0),(6,3,2)],⟨7,11,44,88,304,97,210,402,406⟩,⟨7,11,44,88,304,97,192,384,260⟩,[⟨5,1210255570456107830750469,⟨7,75,79,218,475,65,192,385,263⟩⟩,⟨4,1210107565564227153829135,⟨7,47,47,111,289,97,192,385,263⟩⟩,⟨7,1208926973944609254153487,⟨7,47,47,127,305,97,64,257,263⟩⟩,⟨8,1181745950697490750735,⟨7,47,47,127,49,97,192,129,7⟩⟩]⟩
theorem node88 : UpperPrefix a [2,3,5,6,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,0] 30 cert88 (by decide +kernel)

def cert89 : Leaf := ⟨⟨8,4,67,391,135,5,279,23,179⟩,[],[(3,1,0),(6,3,2)],⟨7,11,44,88,304,98,209,401,405⟩,⟨7,11,44,88,304,98,192,384,260⟩,[⟨5,1210255426340919754894597,⟨7,11,15,218,475,66,192,385,263⟩⟩,⟨4,1210107565564227153829167,⟨7,47,47,111,289,103,192,385,263⟩⟩,⟨7,1208926973944609254153519,⟨7,47,47,127,305,103,64,257,263⟩⟩,⟨8,1181745950697490750767,⟨7,47,47,127,49,103,192,129,7⟩⟩]⟩
theorem node89 : UpperPrefix a [2,3,5,6,8,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,1] 30 cert89 (by decide +kernel)

def cert90 : Leaf := ⟨⟨392,388,467,0,135,0,263,7,131⟩,[(3,5),(5,3)],[(3,1,0),(6,3,2),(4,5,2)],⟨7,11,44,88,304,112,195,387,391⟩,⟨7,11,44,88,304,112,192,384,260⟩,[⟨5,1236297743387773075729669,⟨455,459,463,218,475,218,192,449,455⟩⟩]⟩
theorem node90 : UpperPrefix a [2,3,5,6,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,4] 30 cert90 (by decide +kernel)

def cert91 : Leaf := ⟨⟨264,260,323,263,7,0,279,23,51⟩,[(5,6)],[(3,1,0),(6,3,2),(7,5,5)],⟨7,11,44,88,304,224,211,403,279⟩,⟨7,11,44,88,304,224,192,384,260⟩,[⟨5,1210255426340919754894597,⟨7,11,15,218,475,192,192,385,263⟩⟩,⟨4,1210107567534551990279439,⟨7,15,47,111,289,224,224,385,263⟩⟩]⟩
theorem node91 : UpperPrefix a [2,3,5,6,8,7] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,7] 30 cert91 (by decide +kernel)

theorem node92 : UpperPrefix a [2,3,5,6,8] 30 :=
  branch_upper a [2,3,5,6,8] 30 (by decide) (fin9_cases _
  node88
  node89
  (invalid_upper a [2,3,5,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,3] 30 (by decide +kernel))
  node90
  (invalid_upper a [2,3,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,6] 30 (by decide +kernel))
  node91
  (invalid_upper a [2,3,5,6,8,8] 30 (by decide +kernel)))

theorem node93 : UpperPrefix a [2,3,5,6] 30 :=
  branch_upper a [2,3,5,6] 30 (by decide) (fin9_cases _
  node70
  node77
  (invalid_upper a [2,3,5,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,6] 30 (by decide +kernel))
  node87
  node92)

def cert94 : Leaf := ⟨⟨56,52,208,100,6,148,308,116,240⟩,[],[(3,1,0),(1,5,4)],⟨7,11,44,152,49,98,464,464,340⟩,⟨7,11,44,152,49,98,192,384,260⟩,[⟨0,1323666154217542809814016,⟨38,494,492,476,508,102,192,384,260⟩⟩,⟨8,1181747927902887927157,⟨23,11,63,155,55,127,255,129,23⟩⟩,⟨6,1210106412362621957180677,⟨23,11,63,152,49,34,128,385,279⟩⟩,⟨7,1208926973663409152724229,⟨23,11,63,24,49,98,64,257,279⟩⟩]⟩
theorem node94 : UpperPrefix a [2,3,5,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,0,1] 30 cert94 (by decide +kernel)

def cert95 : Leaf := ⟨⟨200,196,210,70,198,134,262,70,194⟩,[],[(3,1,0),(4,5,2)],⟨7,11,44,152,49,112,450,450,326⟩,⟨7,11,44,152,49,112,192,384,260⟩,[⟨0,1224302389454718830117888,⟨454,462,44,188,508,124,192,384,260⟩⟩,⟨5,1236297743387773075729669,⟨455,459,463,218,475,218,192,449,455⟩⟩,⟨8,1181747927902887927157,⟨23,11,63,155,55,127,255,129,23⟩⟩]⟩
theorem node95 : UpperPrefix a [2,3,5,7,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,0,4] 30 cert95 (by decide +kernel)

def cert96 : Leaf := ⟨⟨424,420,386,0,390,134,293,38,226⟩,[(3,7)],[(3,1,0),(4,7,3)],⟨7,11,44,152,49,352,194,400,324⟩,⟨7,11,44,152,49,352,194,400,260⟩,[⟨6,1212762743511493687639997,⟨31,11,191,159,191,447,139,415,415⟩⟩,⟨0,1663602323843746465055744,⟨6,10,300,156,444,356,494,412,260⟩⟩]⟩
theorem node96 : UpperPrefix a [2,3,5,7,0,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,0,8,1,4] 30 cert96 (by decide +kernel)

def cert97 : Leaf := ⟨⟨360,356,322,358,326,0,292,0,114⟩,[(5,7),(7,5)],[(3,1,0)],⟨7,11,44,152,49,352,194,448,276⟩,⟨7,11,44,152,49,352,194,448,260⟩,[⟨7,1279762477677796192689423,⟨279,287,319,319,305,369,371,369,279⟩⟩,⟨0,1323905588654681917752320,⟨230,494,428,444,508,480,230,480,260⟩⟩,⟨4,1212768737798965775310095,⟨71,79,239,239,161,481,227,481,487⟩⟩]⟩
theorem node97 : UpperPrefix a [2,3,5,7,0,8,1,6] 30 :=
  Boolean.leaf_sound a [2,3,5,7,0,8,1,6] 30 cert97 (by decide +kernel)

theorem node98 : UpperPrefix a [2,3,5,7,0,8,1] 30 :=
  branch_upper a [2,3,5,7,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,1,3] 30 (by decide +kernel))
  node96
  (invalid_upper a [2,3,5,7,0,8,1,5] 30 (by decide +kernel))
  node97
  (invalid_upper a [2,3,5,7,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,1,8] 30 (by decide +kernel)))

def cert99 : Leaf := ⟨⟨408,404,402,0,390,150,0,86,210⟩,[(3,6),(6,3)],[(3,1,0)],⟨7,11,44,152,49,352,208,450,326⟩,⟨7,11,44,152,49,352,208,384,260⟩,[⟨0,1219570889179230104978432,⟨422,494,108,216,52,364,216,384,260⟩⟩,⟨5,1229329503828332097072389,⟨391,75,463,218,219,459,218,385,391⟩⟩,⟨6,1210106412364829578812725,⟨23,11,63,155,55,319,155,385,279⟩⟩]⟩
theorem node99 : UpperPrefix a [2,3,5,7,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,0,8,4] 30 cert99 (by decide +kernel)

theorem node100 : UpperPrefix a [2,3,5,7,0,8] 30 :=
  branch_upper a [2,3,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,0,8,0] 30 (by decide +kernel))
  node98
  (invalid_upper a [2,3,5,7,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,3] 30 (by decide +kernel))
  node99
  (invalid_upper a [2,3,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,8,8] 30 (by decide +kernel)))

theorem node101 : UpperPrefix a [2,3,5,7,0] 30 :=
  branch_upper a [2,3,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,0,0] 30 (by decide +kernel))
  node94
  (invalid_upper a [2,3,5,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,3] 30 (by decide +kernel))
  node95
  (invalid_upper a [2,3,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,7] 30 (by decide +kernel))
  node100)

def cert102 : Leaf := ⟨⟨56,52,208,100,5,148,308,116,240⟩,[],[(3,1,0),(0,5,4)],⟨7,11,44,152,50,97,464,464,340⟩,⟨7,11,44,152,50,97,192,384,260⟩,[⟨1,1323666154217542809812993,⟨37,493,492,476,508,97,192,384,260⟩⟩,⟨8,1181747927902887927157,⟨23,11,63,155,55,127,255,129,23⟩⟩,⟨6,1210106412362621957180677,⟨23,11,63,152,50,33,128,385,279⟩⟩,⟨7,1208926973663409152724229,⟨23,11,63,24,50,97,64,257,279⟩⟩]⟩
theorem node102 : UpperPrefix a [2,3,5,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,0] 30 cert102 (by decide +kernel)

def cert103 : Leaf := ⟨⟨200,196,209,69,197,133,261,69,193⟩,[],[(3,1,0),(4,5,2)],⟨7,11,44,152,50,112,449,449,325⟩,⟨7,11,44,152,50,112,192,384,260⟩,[⟨1,1224302389454718830116865,⟨453,461,44,188,508,124,192,384,260⟩⟩,⟨5,1236152187047812166323461,⟨455,459,463,216,218,88,192,449,455⟩⟩,⟨8,1181747927902887927157,⟨23,11,63,155,55,127,255,129,23⟩⟩]⟩
theorem node103 : UpperPrefix a [2,3,5,7,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,4] 30 cert103 (by decide +kernel)

def cert104 : Leaf := ⟨⟨424,420,385,0,389,133,292,37,225⟩,[(3,7)],[(3,1,0),(4,7,3)],⟨7,11,44,152,50,352,193,400,324⟩,⟨7,11,44,152,50,352,193,400,260⟩,[⟨1,1753401110691864687149057,⟨357,493,428,444,508,356,493,444,260⟩⟩,⟨6,1212762743511493687639997,⟨31,11,191,159,191,447,139,415,415⟩⟩]⟩
theorem node104 : UpperPrefix a [2,3,5,7,1,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,8,0,4] 30 cert104 (by decide +kernel)

def cert105 : Leaf := ⟨⟨360,356,321,357,325,0,292,0,113⟩,[(5,7),(7,5)],[(3,1,0)],⟨7,11,44,152,50,352,193,448,276⟩,⟨7,11,44,152,50,352,193,448,260⟩,[⟨7,1279762477662403029900559,⟨279,287,319,319,307,353,353,353,279⟩⟩,⟨1,1323905588654681917751297,⟨229,493,428,444,508,480,225,480,260⟩⟩,⟨4,1212771908333103444139279,⟨71,79,239,239,227,481,225,481,487⟩⟩]⟩
theorem node105 : UpperPrefix a [2,3,5,7,1,8,0,6] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,8,0,6] 30 cert105 (by decide +kernel)

theorem node106 : UpperPrefix a [2,3,5,7,1,8,0] 30 :=
  branch_upper a [2,3,5,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,0,3] 30 (by decide +kernel))
  node104
  (invalid_upper a [2,3,5,7,1,8,0,5] 30 (by decide +kernel))
  node105
  (invalid_upper a [2,3,5,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,0,8] 30 (by decide +kernel)))

def cert107 : Leaf := ⟨⟨408,404,401,0,389,149,0,85,209⟩,[(3,6),(6,3)],[(3,1,0)],⟨7,11,44,152,50,352,208,449,325⟩,⟨7,11,44,152,50,352,208,384,260⟩,[⟨1,1219571177972558380662785,⟨421,493,108,252,508,364,252,384,260⟩⟩,⟨5,1229329503828332097064197,⟨391,75,463,216,218,459,216,385,391⟩⟩,⟨6,1210106412364829578812725,⟨23,11,63,155,55,319,155,385,279⟩⟩]⟩
theorem node107 : UpperPrefix a [2,3,5,7,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,8,4] 30 cert107 (by decide +kernel)

theorem node108 : UpperPrefix a [2,3,5,7,1,8] 30 :=
  branch_upper a [2,3,5,7,1,8] 30 (by decide) (fin9_cases _
  node106
  (invalid_upper a [2,3,5,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,3] 30 (by decide +kernel))
  node107
  (invalid_upper a [2,3,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,8,8] 30 (by decide +kernel)))

theorem node109 : UpperPrefix a [2,3,5,7,1] 30 :=
  branch_upper a [2,3,5,7,1] 30 (by decide) (fin9_cases _
  node102
  (invalid_upper a [2,3,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,3] 30 (by decide +kernel))
  node103
  (invalid_upper a [2,3,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,7] 30 (by decide +kernel))
  node108)

def cert110 : Leaf := ⟨⟨8,4,147,39,0,150,311,55,51⟩,[(4,5)],[(3,1,0),(6,4,4)],⟨7,11,44,152,112,97,466,402,278⟩,⟨7,11,44,152,112,97,192,384,260⟩,[⟨8,1181748490577969741183,⟨7,15,63,191,127,127,255,129,7⟩⟩,⟨7,1227816439596811878927621,⟨263,11,319,24,112,113,64,257,263⟩⟩,⟨4,1210107565282752174492933,⟨7,11,47,136,96,97,192,385,263⟩⟩,⟨5,1210107564157951779278085,⟨7,11,15,152,80,65,192,385,263⟩⟩]⟩
theorem node110 : UpperPrefix a [2,3,5,7,6,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,0] 30 cert110 (by decide +kernel)

def cert111 : Leaf := ⟨⟨8,4,147,39,0,149,311,55,51⟩,[(4,5)],[(3,1,0),(6,4,4)],⟨7,11,44,152,112,98,465,401,277⟩,⟨7,11,44,152,112,98,192,384,260⟩,[⟨8,1181748490577969741183,⟨7,15,63,191,127,127,255,129,7⟩⟩,⟨7,1227816439596811878927621,⟨263,11,319,24,112,114,64,257,263⟩⟩,⟨4,1210107565282752174492933,⟨7,11,47,136,96,98,192,385,263⟩⟩,⟨5,1210107564157951779278085,⟨7,11,15,152,80,66,192,385,263⟩⟩]⟩
theorem node111 : UpperPrefix a [2,3,5,7,6,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,1] 30 cert111 (by decide +kernel)

def cert112 : Leaf := ⟨⟨392,388,403,295,0,0,263,7,131⟩,[(4,5),(5,4)],[(3,1,0),(6,4,4),(6,4,5),(4,5,2)],⟨7,11,44,152,112,112,451,387,263⟩,⟨7,11,44,152,112,112,192,384,260⟩,[⟨5,1236149881204800805145861,⟨455,459,463,152,80,80,192,449,455⟩⟩]⟩
theorem node112 : UpperPrefix a [2,3,5,7,6,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,4] 30 cert112 (by decide +kernel)

def cert113 : Leaf := ⟨⟨264,260,387,295,0,135,262,55,51⟩,[(4,5)],[(3,1,0),(6,4,4)],⟨7,11,44,152,112,352,193,402,278⟩,⟨7,11,44,152,112,352,193,384,260⟩,[⟨4,1210110019744549093514511,⟨7,79,111,239,96,353,225,481,263⟩⟩,⟨5,1210109870000960992972037,⟨7,11,15,216,80,321,193,449,263⟩⟩,⟨7,1227816439596811878927621,⟨263,11,319,24,112,369,65,257,263⟩⟩]⟩
theorem node113 : UpperPrefix a [2,3,5,7,6,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,8,0] 30 cert113 (by decide +kernel)

def cert114 : Leaf := ⟨⟨424,416,386,290,0,130,289,38,178⟩,[(4,5)],[(2,0,7),(3,1,0),(6,4,4),(0,7,6)],⟨7,11,44,152,112,352,194,385,276⟩,⟨7,11,44,152,112,352,194,385,260⟩,[⟨4,1212768737798965775310095,⟨71,79,239,239,224,481,227,481,487⟩⟩]⟩
theorem node114 : UpperPrefix a [2,3,5,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,8,1,0] 30 cert114 (by decide +kernel)

def cert115 : Local := ⟨⟨424,420,387,0,0,135,293,39,163⟩,[(3,7),(4,5)],[(3,1,0),(6,4,4),(4,7,3)]⟩
theorem node115 : UpperPrefix a [2,3,5,7,6,8,1,4] 30 :=
  local_sound a [2,3,5,7,6,8,1,4] 30 cert115 (by decide +kernel)

theorem node116 : UpperPrefix a [2,3,5,7,6,8,1] 30 :=
  branch_upper a [2,3,5,7,6,8,1] 30 (by decide) (fin9_cases _
  node114
  (invalid_upper a [2,3,5,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,3] 30 (by decide +kernel))
  node115
  (invalid_upper a [2,3,5,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,8] 30 (by decide +kernel)))

def cert117 : Local := ⟨⟨440,436,403,0,0,151,0,55,179⟩,[(3,6),(4,5),(6,3)],[(3,1,0),(6,4,4)]⟩
theorem node117 : UpperPrefix a [2,3,5,7,6,8,4] 30 :=
  local_sound a [2,3,5,7,6,8,4] 30 cert117 (by decide +kernel)

theorem node118 : UpperPrefix a [2,3,5,7,6,8] 30 :=
  branch_upper a [2,3,5,7,6,8] 30 (by decide) (fin9_cases _
  node113
  node116
  (invalid_upper a [2,3,5,7,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,3] 30 (by decide +kernel))
  node117
  (invalid_upper a [2,3,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,8] 30 (by decide +kernel)))

theorem node119 : UpperPrefix a [2,3,5,7,6] 30 :=
  branch_upper a [2,3,5,7,6] 30 (by decide) (fin9_cases _
  node110
  node111
  (invalid_upper a [2,3,5,7,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,3] 30 (by decide +kernel))
  node112
  (invalid_upper a [2,3,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,7] 30 (by decide +kernel))
  node118)

def cert120 : Leaf := ⟨⟨232,228,192,356,196,134,36,116,240⟩,[],[(3,1,0),(8,4,3),(1,6,5)],⟨7,11,44,152,304,97,194,464,340⟩,⟨7,11,44,152,304,97,194,384,260⟩,[⟨0,1366250084541442741502976,⟨478,458,444,156,444,508,194,384,284⟩⟩,⟨4,1210107712142321275903311,⟨39,111,111,239,289,97,231,385,295⟩⟩]⟩
theorem node120 : UpperPrefix a [2,3,5,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,0,1] 30 cert120 (by decide +kernel)

def cert121 : Leaf := ⟨⟨216,208,211,0,199,146,0,83,211⟩,[(3,6),(6,3)],[(3,1,0),(8,4,3),(8,4,6)],⟨7,11,44,152,304,97,208,450,326⟩,⟨7,11,44,152,304,97,208,384,260⟩,[⟨5,1229181929875742420659461,⟨391,75,463,218,475,75,218,385,391⟩⟩,⟨2,1210255571652385070662657,⟨35,107,106,216,506,107,216,384,256⟩⟩]⟩
theorem node121 : UpperPrefix a [2,3,5,7,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,0,4] 30 cert121 (by decide +kernel)

theorem node122 : UpperPrefix a [2,3,5,7,8,0] 30 :=
  branch_upper a [2,3,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,8,0,0] 30 (by decide +kernel))
  node120
  (invalid_upper a [2,3,5,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,3] 30 (by decide +kernel))
  node121
  (invalid_upper a [2,3,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,8] 30 (by decide +kernel)))

def cert123 : Leaf := ⟨⟨232,228,192,356,196,133,36,116,240⟩,[],[(3,1,0),(8,4,3),(0,6,5)],⟨7,11,44,152,304,98,193,464,340⟩,⟨7,11,44,152,304,98,193,384,260⟩,[⟨1,1366250084541442741501953,⟨477,457,444,156,444,508,457,384,284⟩⟩,⟨4,1210110015733530675911983,⟨39,111,111,239,289,103,193,449,295⟩⟩]⟩
theorem node123 : UpperPrefix a [2,3,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,1,0] 30 cert123 (by decide +kernel)

def cert124 : Leaf := ⟨⟨152,148,147,0,199,149,0,87,211⟩,[(3,6),(6,3)],[(3,1,0),(8,4,3),(8,4,6)],⟨7,11,44,152,304,98,208,449,325⟩,⟨7,11,44,152,304,98,208,384,260⟩,[⟨5,1229181929875742420643077,⟨391,75,463,218,475,74,218,385,391⟩⟩,⟨6,1210106412362355677650229,⟨7,11,47,155,311,47,155,385,263⟩⟩]⟩
theorem node124 : UpperPrefix a [2,3,5,7,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,1,4] 30 cert124 (by decide +kernel)

theorem node125 : UpperPrefix a [2,3,5,7,8,1] 30 :=
  branch_upper a [2,3,5,7,8,1] 30 (by decide) (fin9_cases _
  node123
  (invalid_upper a [2,3,5,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,3] 30 (by decide +kernel))
  node124
  (invalid_upper a [2,3,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,8] 30 (by decide +kernel)))

def cert126 : Leaf := ⟨⟨200,196,209,325,197,133,6,69,193⟩,[],[(3,1,0),(8,4,3),(4,5,2),(1,7,6)],⟨7,11,44,152,304,112,193,386,324⟩,⟨7,11,44,152,304,112,193,386,260⟩,[⟨5,1236300049230782289423621,⟨455,459,463,218,475,218,449,451,455⟩⟩]⟩
theorem node126 : UpperPrefix a [2,3,5,7,8,4,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,4,0,1] 30 cert126 (by decide +kernel)

def cert127 : Leaf := ⟨⟨200,196,210,326,198,134,6,6,194⟩,[],[(3,1,0),(8,4,3),(4,5,2)],⟨7,11,44,152,304,112,193,448,262⟩,⟨7,11,44,152,304,112,193,448,260⟩,[⟨0,1224864967311443037783040,⟨262,270,44,188,316,252,508,508,260⟩⟩,⟨5,1236890345041140995075333,⟨455,459,463,218,475,218,449,449,455⟩⟩]⟩
theorem node127 : UpperPrefix a [2,3,5,7,8,4,0,6] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,4,0,6] 30 cert127 (by decide +kernel)

#print axioms node127
end Delivery.FiniteExclusion.Sharp2x7
