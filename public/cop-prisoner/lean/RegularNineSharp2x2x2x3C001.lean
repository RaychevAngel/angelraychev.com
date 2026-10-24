import RegularNineSharp2x2x2x3Base
import RegularNineSharp2x2x2x3C000
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x2x3
open Bounds BoundTreeRows Extremal
def cert64 : Leaf := ⟨⟨0,0,497,465,396,0,316,124,188⟩,[(0,2),(1,5),(5,1)],[(1,2,0)],⟨7,19,14,44,112,49,456,392,456⟩,⟨7,19,14,44,112,49,192,384,320⟩,[⟨0,1266886859716061555590144,⟨454,18,478,508,112,48,192,384,320⟩⟩]⟩
theorem node64 : UpperPrefix a [2,4,1,5,6,0] 30 :=
  Boolean.leaf_sound a [2,4,1,5,6,0] 30 cert64 (by decide +kernel)

def cert65 : Leaf := ⟨⟨488,488,480,416,448,0,296,104,168⟩,[(5,1)],[(2,0,2),(4,1,5),(0,2,0)],⟨7,19,13,76,56,50,480,416,480⟩,⟨7,19,13,76,56,50,192,384,320⟩,[⟨1,1437224743012695728193537,⟨13,477,13,76,504,508,192,384,320⟩⟩]⟩
theorem node65 : UpperPrefix a [2,4,0,6,3,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,3,1] 30 cert65 (by decide +kernel)

def cert66 : Leaf := ⟨⟨0,108,113,81,141,77,269,77,13⟩,[(0,2)],[(1,2,0),(7,5,4)],⟨7,19,14,44,112,176,457,393,329⟩,⟨7,19,14,44,112,176,192,384,320⟩,[⟨8,1181752446678889915903,⟨7,31,15,47,127,191,255,191,127⟩⟩,⟨4,1266886859714412288148485,⟨455,3,463,493,96,160,192,384,320⟩⟩,⟨5,1266886858589611892933637,⟨455,19,463,461,80,144,192,384,320⟩⟩]⟩
theorem node66 : UpperPrefix a [2,4,1,5,6,7] 30 :=
  Boolean.leaf_sound a [2,4,1,5,6,7] 30 cert66 (by decide +kernel)

def cert67 : Leaf := ⟨⟨0,300,305,273,269,77,269,13,141⟩,[(0,2)],[(1,2,0),(6,4,5)],⟨7,19,14,44,112,304,201,393,457⟩,⟨7,19,14,44,112,304,192,384,320⟩,[⟨7,1208926987195990094374399,⟨7,31,15,47,127,319,127,319,383⟩⟩,⟨4,1266886859714412288148485,⟨455,3,463,493,96,288,192,384,320⟩⟩,⟨5,1266886858589611892933637,⟨455,19,463,461,80,272,192,384,320⟩⟩]⟩
theorem node67 : UpperPrefix a [2,4,1,5,6,8] 30 :=
  Boolean.leaf_sound a [2,4,1,5,6,8] 30 cert67 (by decide +kernel)

theorem node68 : UpperPrefix a [2,4,1,5,6] 30 :=
  branch_upper a [2,4,1,5,6] 30 (by decide) (fin9_cases _
  node64
  (invalid_upper a [2,4,1,5,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,6,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut129 [2,4,1,5,6,3] [2,4,0,6,3,1] 30 (by decide +kernel) node65)
  (invalid_upper a [2,4,1,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,6,6] 30 (by decide +kernel))
  node66
  node67)

theorem node69 : UpperPrefix a [2,4,1,5] 30 :=
  branch_upper a [2,4,1,5] 30 (by decide) (fin9_cases _
  node62
  (invalid_upper a [2,4,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,2] 30 (by decide +kernel))
  node63
  (invalid_upper a [2,4,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,5] 30 (by decide +kernel))
  node68
  (PrefixConjugacy.upper aut2 [2,4,1,5,7] [2,4,1,5,6] 30 (by decide +kernel) node68)
  (PrefixConjugacy.upper aut1 [2,4,1,5,8] [2,4,1,5,6] 30 (by decide +kernel) node68))

def cert70 : Leaf := ⟨⟨0,0,480,416,460,460,300,108,172⟩,[(0,2),(1,4)],[(1,2,0),(0,4,1)],⟨7,19,14,76,49,440,488,424,488⟩,⟨7,19,14,76,49,48,192,384,320⟩,[⟨4,1437224743009395045827591,⟨15,463,15,77,493,488,192,384,320⟩⟩]⟩
theorem node70 : UpperPrefix a [2,4,1,6,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,0] 30 cert70 (by decide +kernel)

def cert71 : Leaf := ⟨⟨0,264,273,433,449,449,305,113,177⟩,[(0,2)],[(1,2,0)],⟨7,19,14,76,56,433,481,417,481⟩,⟨7,19,14,76,56,48,192,384,320⟩,[⟨2,1224302388997594707658241,⟨499,499,506,88,56,48,192,384,320⟩⟩,⟨3,1243228820439354422854661,⟨487,499,487,453,48,48,192,384,320⟩⟩,⟨5,1210107564157951783494711,⟨7,23,15,77,31,23,192,384,320⟩⟩,⟨6,1210106412362347083490359,⟨7,23,15,13,63,55,128,384,256⟩⟩,⟨7,1208926973663134279033911,⟨7,23,15,77,63,55,64,256,320⟩⟩]⟩
theorem node71 : UpperPrefix a [2,4,1,6,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,3] 30 cert71 (by decide +kernel)

def cert72 : Leaf := ⟨⟨0,0,496,432,332,0,316,124,188⟩,[(0,2),(1,5),(5,1)],[(1,2,0)],⟨7,19,14,76,176,49,488,424,360⟩,⟨7,19,14,76,176,49,192,384,320⟩,[⟨0,1437224743012695728194560,⟨14,478,14,76,504,508,192,384,320⟩⟩]⟩
theorem node72 : UpperPrefix a [2,4,1,6,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,0] 30 cert72 (by decide +kernel)

def cert73 : Leaf := ⟨⟨0,232,241,177,72,192,56,120,184⟩,[(0,2)],[(1,2,0)],⟨7,19,14,76,176,56,193,416,352⟩,⟨7,19,14,76,176,56,193,384,320⟩,[⟨2,1271913435771315907757569,⟨499,467,506,506,176,440,467,384,322⟩⟩,⟨8,1184356433261360051711,⟨47,127,47,127,255,127,255,255,127⟩⟩,⟨0,1248292325941735299482624,⟨182,18,446,508,176,440,208,384,320⟩⟩]⟩
theorem node73 : UpperPrefix a [2,4,1,6,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,3,0] 30 cert73 (by decide +kernel)

def cert74 : Leaf := ⟨⟨0,460,465,401,0,453,0,93,157⟩,[(0,2),(4,6),(6,4)],[(1,2,0)],⟨7,19,14,76,176,56,224,385,321⟩,⟨7,19,14,76,176,56,224,384,320⟩,[⟨5,1553475258346024347919477,⟨135,19,399,461,151,415,463,392,461⟩⟩]⟩
theorem node74 : UpperPrefix a [2,4,1,6,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,3,5] 30 cert74 (by decide +kernel)

def cert75 : Leaf := ⟨⟨0,140,145,145,77,197,0,125,189⟩,[(0,2),(6,7)],[(1,2,0),(8,6,6)],⟨7,19,14,76,176,56,448,417,353⟩,⟨7,19,14,76,176,56,448,384,320⟩,[⟨5,1210109870000963153585207,⟨7,31,15,77,223,31,448,448,320⟩⟩,⟨6,1210106412362347087684661,⟨7,19,15,13,183,63,384,384,256⟩⟩]⟩
theorem node75 : UpperPrefix a [2,4,1,6,7,3,8] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,3,8] 30 cert75 (by decide +kernel)

theorem node76 : UpperPrefix a [2,4,1,6,7,3] 30 :=
  branch_upper a [2,4,1,6,7,3] 30 (by decide) (fin9_cases _
  node73
  (invalid_upper a [2,4,1,6,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,4] 30 (by decide +kernel))
  node74
  (invalid_upper a [2,4,1,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,7] 30 (by decide +kernel))
  node75)

def cert77 : Leaf := ⟨⟨0,164,177,177,256,128,61,125,189⟩,[(0,2)],[(1,2,0),(8,5,4)],⟨7,19,14,76,176,304,233,425,361⟩,⟨7,19,14,76,176,304,192,384,320⟩,[⟨6,1210106425886340103017485,⟨7,19,15,31,176,304,176,432,304⟩⟩,⟨3,1210107578807843634025485,⟨7,19,7,87,176,304,240,432,368⟩⟩,⟨0,1210107578807844707763200,⟨6,18,14,92,176,304,240,432,368⟩⟩,⟨2,1210107578807844706714625,⟨3,19,10,88,176,304,240,432,368⟩⟩]⟩
theorem node77 : UpperPrefix a [2,4,1,6,7,8] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,8] 30 cert77 (by decide +kernel)

theorem node78 : UpperPrefix a [2,4,1,6,7] 30 :=
  branch_upper a [2,4,1,6,7] 30 (by decide) (fin9_cases _
  node72
  (invalid_upper a [2,4,1,6,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,2] 30 (by decide +kernel))
  node76
  (invalid_upper a [2,4,1,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,7] 30 (by decide +kernel))
  node77)

def cert79 : Leaf := ⟨⟨0,0,496,432,204,0,316,124,188⟩,[(0,2),(1,5),(5,1)],[(1,2,0)],⟨7,19,14,76,304,49,232,424,488⟩,⟨7,19,14,76,304,49,192,384,320⟩,[⟨0,1437224743012695728194560,⟨14,478,14,76,504,508,192,384,320⟩⟩]⟩
theorem node79 : UpperPrefix a [2,4,1,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,0] 30 cert79 (by decide +kernel)

def cert80 : Leaf := ⟨⟨0,360,369,305,72,320,312,120,184⟩,[(0,2)],[(1,2,0)],⟨7,19,14,76,304,56,193,416,480⟩,⟨7,19,14,76,304,56,193,384,320⟩,[⟨2,1272061009723905584170497,⟨499,467,506,506,432,440,467,384,322⟩⟩,⟨7,1208926990015114285147647,⟨7,55,15,111,319,63,127,319,383⟩⟩,⟨0,1248439899894256256418816,⟨182,146,446,508,432,440,192,384,320⟩⟩]⟩
theorem node80 : UpperPrefix a [2,4,1,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,3,0] 30 cert80 (by decide +kernel)

def cert81 : Leaf := ⟨⟨0,448,465,401,193,449,273,81,145⟩,[(0,2)],[(1,2,0)],⟨7,19,14,76,304,56,224,385,449⟩,⟨7,19,14,76,304,56,224,384,320⟩,[⟨2,1224302425343119794898433,⟨499,467,506,120,304,56,224,384,320⟩⟩,⟨3,1408881320747833410737165,⟨391,467,391,471,498,499,498,384,336⟩⟩,⟨5,1553622832298614028526711,⟨135,151,399,461,415,415,463,392,461⟩⟩]⟩
theorem node81 : UpperPrefix a [2,4,1,6,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,3,5] 30 cert81 (by decide +kernel)

theorem node82 : UpperPrefix a [2,4,1,6,8,3] 30 :=
  branch_upper a [2,4,1,6,8,3] 30 (by decide) (fin9_cases _
  node80
  (invalid_upper a [2,4,1,6,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,4] 30 (by decide +kernel))
  node81
  (invalid_upper a [2,4,1,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,8] 30 (by decide +kernel)))

def cert83 : Leaf := ⟨⟨0,232,241,177,200,328,56,120,184⟩,[(0,2)],[(1,2,0),(8,4,5)],⟨7,19,14,76,304,176,193,424,360⟩,⟨7,19,14,76,304,176,193,384,320⟩,[⟨2,1247997202865658804602369,⟨243,115,442,506,304,176,243,432,370⟩⟩,⟨0,1247997184851260296135680,⟨182,50,446,508,304,176,240,432,368⟩⟩]⟩
theorem node83 : UpperPrefix a [2,4,1,6,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,7,0] 30 cert83 (by decide +kernel)

def cert84 : Leaf := ⟨⟨0,224,241,177,193,321,49,113,177⟩,[(0,2)],[(1,2,0),(8,4,5),(3,6,3)],⟨7,19,14,76,304,176,200,417,353⟩,⟨7,19,14,76,304,176,200,384,320⟩,[⟨2,1214857680968710415713793,⟨499,435,250,104,304,176,248,432,368⟩⟩]⟩
theorem node84 : UpperPrefix a [2,4,1,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,7,3] 30 cert84 (by decide +kernel)

def cert85 : Leaf := ⟨⟨0,76,81,17,77,333,0,93,29⟩,[(0,2),(6,5)],[(1,2,0),(8,4,5),(7,5,6)],⟨7,19,14,76,304,176,224,393,329⟩,⟨7,19,14,76,304,176,224,384,320⟩,[⟨5,1553327684393434667312247,⟨135,151,399,461,415,151,463,392,461⟩⟩]⟩
theorem node85 : UpperPrefix a [2,4,1,6,8,7,5] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,7,5] 30 cert85 (by decide +kernel)

theorem node86 : UpperPrefix a [2,4,1,6,8,7] 30 :=
  branch_upper a [2,4,1,6,8,7] 30 (by decide) (fin9_cases _
  node83
  (invalid_upper a [2,4,1,6,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,7,2] 30 (by decide +kernel))
  node84
  (invalid_upper a [2,4,1,6,8,7,4] 30 (by decide +kernel))
  node85
  (invalid_upper a [2,4,1,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,7,8] 30 (by decide +kernel)))

theorem node87 : UpperPrefix a [2,4,1,6,8] 30 :=
  branch_upper a [2,4,1,6,8] 30 (by decide) (fin9_cases _
  node79
  (invalid_upper a [2,4,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,2] 30 (by decide +kernel))
  node82
  (invalid_upper a [2,4,1,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,6] 30 (by decide +kernel))
  node86
  (invalid_upper a [2,4,1,6,8,8] 30 (by decide +kernel)))

theorem node88 : UpperPrefix a [2,4,1,6] 30 :=
  branch_upper a [2,4,1,6] 30 (by decide) (fin9_cases _
  node70
  (invalid_upper a [2,4,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,2] 30 (by decide +kernel))
  node71
  (invalid_upper a [2,4,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,6] 30 (by decide +kernel))
  node78
  node87)

theorem node89 : UpperPrefix a [2,4,1] 30 :=
  branch_upper a [2,4,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut54 [2,4,1,0] [2,3,1,4] 30 (by decide +kernel) node5)
  (invalid_upper a [2,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,4] 30 (by decide +kernel))
  node69
  node88
  (PrefixConjugacy.upper aut2 [2,4,1,7] [2,4,1,6] 30 (by decide +kernel) node88)
  (PrefixConjugacy.upper aut1 [2,4,1,8] [2,4,1,6] 30 (by decide +kernel) node88))

def cert90 : Leaf := ⟨⟨0,0,450,0,462,462,300,108,172⟩,[(0,3),(1,4),(3,0)],[(0,4,1)],⟨7,19,44,14,49,504,456,456,456⟩,⟨7,19,44,14,49,48,192,384,320⟩,[⟨4,1356787409231207874954251,⟨463,463,493,463,493,484,192,384,320⟩⟩,⟨1,1266886859715511799775233,⟨453,17,492,460,49,48,192,384,320⟩⟩]⟩
theorem node90 : UpperPrefix a [2,4,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,1,0] 30 cert90 (by decide +kernel)

def cert91 : Leaf := ⟨⟨0,488,0,0,0,459,315,123,187⟩,[(0,3),(2,4),(3,0),(4,2)],[],⟨7,19,44,14,56,497,449,449,449⟩,⟨7,19,44,14,56,48,192,384,320⟩,[⟨2,1224302388998144463472129,⟨499,499,56,506,56,48,192,384,320⟩⟩]⟩
theorem node91 : UpperPrefix a [2,4,5,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,1,3] 30 cert91 (by decide +kernel)

def cert92 : Leaf := ⟨⟨0,488,0,0,0,395,315,123,187⟩,[(0,3),(2,4),(3,0),(4,2)],[],⟨7,19,44,14,56,112,449,385,449⟩,⟨7,19,44,14,56,112,192,384,320⟩,[⟨2,1224302389279619440182785,⟨499,499,56,506,56,112,192,384,320⟩⟩]⟩
theorem node92 : UpperPrefix a [2,4,5,1,3,6] 30 :=
  Boolean.leaf_sound a [2,4,5,1,3,6] 30 cert92 (by decide +kernel)

def cert93 : Leaf := ⟨⟨0,0,496,432,452,0,316,124,188⟩,[(0,2),(1,5),(5,1)],[(1,2,0)],⟨7,19,14,76,56,49,480,416,480⟩,⟨7,19,14,76,56,49,192,384,320⟩,[⟨0,1437224743012695728194560,⟨14,478,14,76,504,508,192,384,320⟩⟩]⟩
theorem node93 : UpperPrefix a [2,4,1,6,3,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,3,0] 30 cert93 (by decide +kernel)

def cert94 : Leaf := ⟨⟨0,108,83,0,142,78,271,79,15⟩,[(0,3),(3,0)],[(7,5,4)],⟨7,19,44,14,112,176,457,393,329⟩,⟨7,19,44,14,112,176,192,384,320⟩,[⟨8,1181752446679826818559,⟨15,31,47,15,127,191,255,191,127⟩⟩,⟨4,1281081683322327450780681,⟨463,459,493,463,96,160,192,384,320⟩⟩,⟨5,1281081682197527055565833,⟨463,475,461,463,80,144,192,384,320⟩⟩,⟨0,1210107572061241493947392,⟨14,26,44,14,112,176,240,432,368⟩⟩]⟩
theorem node94 : UpperPrefix a [2,4,5,1,6,7] 30 :=
  Boolean.leaf_sound a [2,4,5,1,6,7] 30 cert94 (by decide +kernel)

theorem node95 : UpperPrefix a [2,4,5,1,6] 30 :=
  branch_upper a [2,4,5,1,6] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut81 [2,4,5,1,6,0] [2,4,5,1,3,6] 30 (by decide +kernel) node92)
  (invalid_upper a [2,4,5,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,6,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut123 [2,4,5,1,6,3] [2,4,1,6,3,0] 30 (by decide +kernel) node93)
  (invalid_upper a [2,4,5,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,6,6] 30 (by decide +kernel))
  node94
  (PrefixConjugacy.upper aut82 [2,4,5,1,6,8] [2,4,5,1,6,7] 30 (by decide +kernel) node94))

theorem node96 : UpperPrefix a [2,4,5,1] 30 :=
  branch_upper a [2,4,5,1] 30 (by decide) (fin9_cases _
  node90
  (invalid_upper a [2,4,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,2] 30 (by decide +kernel))
  node91
  (invalid_upper a [2,4,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,5] 30 (by decide +kernel))
  node95
  (PrefixConjugacy.upper aut2 [2,4,5,1,7] [2,4,5,1,6] 30 (by decide +kernel) node95)
  (PrefixConjugacy.upper aut1 [2,4,5,1,8] [2,4,5,1,6] 30 (by decide +kernel) node95))

def cert97 : Leaf := ⟨⟨288,0,450,386,262,462,270,78,142⟩,[(1,4)],[(0,4,1)],⟨7,19,44,76,49,442,458,394,458⟩,⟨7,19,44,76,49,48,192,384,320⟩,[⟨4,1224302388890669765624835,⟨463,463,44,76,493,44,192,384,320⟩⟩,⟨5,1300008113674747093459969,⟨463,475,12,76,475,466,192,384,320⟩⟩,⟨3,1210107565284125490298381,⟨23,19,55,87,51,50,192,384,320⟩⟩,⟨6,1210106412362621957193229,⟨23,19,63,31,51,50,128,384,256⟩⟩,⟨7,1208926973663409152736781,⟨23,19,63,95,51,50,64,256,320⟩⟩]⟩
theorem node97 : UpperPrefix a [2,4,5,6,0] 30 :=
  Boolean.leaf_sound a [2,4,5,6,0] 30 cert97 (by decide +kernel)

def cert98 : Leaf := ⟨⟨32,36,449,385,5,461,269,77,141⟩,[],[(4,1,4),(1,4,1)],⟨7,19,44,76,50,441,457,393,457⟩,⟨7,19,44,76,50,48,192,384,320⟩,[⟨5,1224302387765866941907969,⟨463,475,12,76,466,16,192,384,320⟩⟩,⟨3,1210107565284125490290189,⟨23,19,55,87,50,48,192,384,320⟩⟩,⟨6,1210106412362621957185037,⟨23,19,63,31,50,48,128,384,256⟩⟩,⟨7,1208926973663409152728589,⟨23,19,63,95,50,48,64,256,320⟩⟩,⟨8,1181745669497389325837,⟨23,19,63,95,50,48,192,128,64⟩⟩]⟩
theorem node98 : UpperPrefix a [2,4,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,1] 30 cert98 (by decide +kernel)

def cert99 : Leaf := ⟨⟨488,488,0,387,0,451,259,67,131⟩,[(2,4),(4,2)],[],⟨7,19,44,76,56,435,451,387,451⟩,⟨7,19,44,76,56,48,192,384,320⟩,[⟨2,1224302388997594707658241,⟨499,499,56,88,56,48,192,384,320⟩⟩,⟨4,1224302388890667609752579,⟨463,463,44,76,44,36,192,384,320⟩⟩,⟨3,1224302388962134384968705,⟨487,499,36,68,48,48,192,384,320⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,24,16,192,384,320⟩⟩]⟩
theorem node99 : UpperPrefix a [2,4,5,6,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,3] 30 cert99 (by decide +kernel)

def cert100 : Leaf := ⟨⟨456,0,450,386,334,0,270,78,142⟩,[(1,5),(5,1)],[],⟨7,19,44,76,176,49,458,394,330⟩,⟨7,19,44,76,176,49,192,384,320⟩,[⟨0,1224302388893970447991808,⟨462,478,60,76,188,508,192,384,320⟩⟩,⟨4,1224302388890671913108483,⟨463,463,44,76,172,493,192,384,320⟩⟩,⟨5,1394640271060847819768837,⟨463,475,463,461,466,475,192,384,320⟩⟩]⟩
theorem node100 : UpperPrefix a [2,4,5,6,7,0] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,0] 30 cert100 (by decide +kernel)

def cert101 : Leaf := ⟨⟨232,236,193,129,77,0,269,77,141⟩,[(5,1)],[(4,1,5)],⟨7,19,44,76,176,50,457,393,329⟩,⟨7,19,44,76,176,50,192,384,320⟩,[⟨1,1224302388893970447990785,⟨461,477,60,76,188,508,192,384,320⟩⟩,⟨8,1181762359852090521053,⟨39,51,47,127,183,51,255,191,127⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,144,466,192,384,320⟩⟩]⟩
theorem node101 : UpperPrefix a [2,4,5,6,7,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,1] 30 cert101 (by decide +kernel)

def cert102 : Leaf := ⟨⟨240,228,0,130,70,198,263,71,135⟩,[(2,5)],[(3,5,2)],⟨7,19,44,76,176,56,451,387,323⟩,⟨7,19,44,76,176,56,192,384,320⟩,[⟨8,1181761726533401310717,⟨7,19,47,127,183,63,255,191,127⟩⟩,⟨4,1224302388890667345511425,⟨463,459,44,76,164,44,192,384,320⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,144,24,192,384,320⟩⟩,⟨0,1210107581341162575758336,⟨6,18,44,124,180,60,252,444,380⟩⟩]⟩
theorem node102 : UpperPrefix a [2,4,5,6,7,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,3] 30 cert102 (by decide +kernel)

def cert103 : Leaf := ⟨⟨176,164,208,128,260,132,15,79,143⟩,[],[(8,5,4)],⟨7,19,44,76,176,304,203,395,331⟩,⟨7,19,44,76,176,304,192,384,320⟩,[⟨0,1210107578807887783265280,⟨6,18,44,92,180,316,252,444,380⟩⟩,⟨1,1210107578807887783264257,⟨5,17,44,92,180,316,252,444,380⟩⟩,⟨3,1210107578807843634025485,⟨7,19,39,87,176,304,240,432,368⟩⟩,⟨4,1224302388890667337122817,⟨463,459,44,76,160,288,192,384,320⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,144,272,192,384,320⟩⟩,⟨6,1210106425886340100920333,⟨7,19,47,31,176,304,176,432,304⟩⟩]⟩
theorem node103 : UpperPrefix a [2,4,5,6,7,8] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,8] 30 cert103 (by decide +kernel)

theorem node104 : UpperPrefix a [2,4,5,6,7] 30 :=
  branch_upper a [2,4,5,6,7] 30 (by decide) (fin9_cases _
  node100
  node101
  (invalid_upper a [2,4,5,6,7,2] 30 (by decide +kernel))
  node102
  (invalid_upper a [2,4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,7] 30 (by decide +kernel))
  node103)

def cert105 : Leaf := ⟨⟨456,0,450,386,206,0,270,78,142⟩,[(1,5),(5,1)],[],⟨7,19,44,76,304,49,202,394,458⟩,⟨7,19,44,76,304,49,192,384,320⟩,[⟨0,1224302388893970447991808,⟨462,478,60,76,316,508,192,384,320⟩⟩,⟨4,1224302388890671913108483,⟨463,463,44,76,300,493,192,384,320⟩⟩,⟨5,1394640271060847819768837,⟨463,475,463,461,466,475,192,384,320⟩⟩]⟩
theorem node105 : UpperPrefix a [2,4,5,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,0] 30 cert105 (by decide +kernel)

def cert106 : Leaf := ⟨⟨360,364,321,257,77,0,269,77,141⟩,[(5,1)],[(4,1,5)],⟨7,19,44,76,304,50,201,393,457⟩,⟨7,19,44,76,304,50,192,384,320⟩,[⟨1,1224302388893970447990785,⟨461,477,60,76,316,508,192,384,320⟩⟩,⟨7,1208926990085483020936703,⟨39,55,47,111,319,55,127,319,383⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,272,466,192,384,320⟩⟩]⟩
theorem node106 : UpperPrefix a [2,4,5,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,1] 30 cert106 (by decide +kernel)

def cert107 : Leaf := ⟨⟨368,356,0,258,70,326,263,71,135⟩,[(2,5)],[(3,5,2)],⟨7,19,44,76,304,56,195,387,451⟩,⟨7,19,44,76,304,56,192,384,320⟩,[⟨7,1208926990015114285147647,⟨7,55,47,111,319,63,127,319,383⟩⟩,⟨4,1224302388890667345511425,⟨463,459,44,76,292,44,192,384,320⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,272,24,192,384,320⟩⟩,⟨0,1210107581635831696196608,⟨6,54,44,108,316,60,252,444,380⟩⟩]⟩
theorem node107 : UpperPrefix a [2,4,5,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,3] 30 cert107 (by decide +kernel)

def cert108 : Leaf := ⟨⟨120,108,144,128,12,268,15,79,15⟩,[],[(8,4,5)],⟨7,19,44,76,304,176,203,395,331⟩,⟨7,19,44,76,304,176,192,384,320⟩,[⟨0,1210107572065682479645696,⟨6,22,44,108,316,180,252,444,380⟩⟩,⟨1,1210107572065682479644673,⟨5,21,44,108,316,180,252,444,380⟩⟩,⟨4,1224302388890667337122817,⟨463,459,44,76,288,160,192,384,320⟩⟩,⟨5,1224302387765866941907969,⟨463,475,12,76,272,144,192,384,320⟩⟩,⟨7,1246705905526366314438157,⟨23,19,319,351,304,48,64,256,320⟩⟩,⟨6,1210106419144134801490945,⟨7,19,44,44,304,176,176,432,304⟩⟩]⟩
theorem node108 : UpperPrefix a [2,4,5,6,8,7] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,7] 30 cert108 (by decide +kernel)

theorem node109 : UpperPrefix a [2,4,5,6,8] 30 :=
  branch_upper a [2,4,5,6,8] 30 (by decide) (fin9_cases _
  node105
  node106
  (invalid_upper a [2,4,5,6,8,2] 30 (by decide +kernel))
  node107
  (invalid_upper a [2,4,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,6] 30 (by decide +kernel))
  node108
  (invalid_upper a [2,4,5,6,8,8] 30 (by decide +kernel)))

theorem node110 : UpperPrefix a [2,4,5,6] 30 :=
  branch_upper a [2,4,5,6] 30 (by decide) (fin9_cases _
  node97
  node98
  (invalid_upper a [2,4,5,6,2] 30 (by decide +kernel))
  node99
  (invalid_upper a [2,4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,6] 30 (by decide +kernel))
  node104
  node109)

theorem node111 : UpperPrefix a [2,4,5] 30 :=
  branch_upper a [2,4,5] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut57 [2,4,5,0] [2,4,1,5] 30 (by decide +kernel) node69)
  node96
  (invalid_upper a [2,4,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,5] 30 (by decide +kernel))
  node110
  (PrefixConjugacy.upper aut2 [2,4,5,7] [2,4,5,6] 30 (by decide +kernel) node110)
  (PrefixConjugacy.upper aut1 [2,4,5,8] [2,4,5,6] 30 (by decide +kernel) node110))

theorem node112 : UpperPrefix a [2,4,6,0,1] 30 :=
  branch_upper a [2,4,6,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut90 [2,4,6,0,1,3] [2,4,0,5,3,6] 30 (by decide +kernel) node41)
  (invalid_upper a [2,4,6,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,0,1,7] [2,4,0,6,8,1] 30 (by decide +kernel) node53)
  (PrefixConjugacy.upper aut37 [2,4,6,0,1,8] [2,4,0,6,7,1] 30 (by decide +kernel) node49))

def cert113 : Leaf := ⟨⟨0,456,465,465,0,393,281,89,153⟩,[(0,2),(4,3)],[(1,2,0),(5,3,4)],⟨7,19,14,44,56,112,449,385,449⟩,⟨7,19,14,44,56,112,192,384,320⟩,[⟨2,1224302389138881951827457,⟨499,499,506,56,56,112,192,384,320⟩⟩]⟩
theorem node113 : UpperPrefix a [2,4,1,5,3,6] 30 :=
  Boolean.leaf_sound a [2,4,1,5,3,6] 30 cert113 (by decide +kernel)

theorem node114 : UpperPrefix a [2,4,6,0,3] 30 :=
  branch_upper a [2,4,6,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,3,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut93 [2,4,6,0,3,1] [2,4,1,5,3,6] 30 (by decide +kernel) node113)
  (invalid_upper a [2,4,6,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,3,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut38 [2,4,6,0,3,7] [2,4,5,6,8,1] 30 (by decide +kernel) node106)
  (PrefixConjugacy.upper aut37 [2,4,6,0,3,8] [2,4,5,6,7,1] 30 (by decide +kernel) node101))

def cert115 : Local := ⟨⟨480,480,0,0,323,0,291,99,163⟩,[(2,6),(3,0),(5,1)],[(2,0,3),(4,1,5),(3,6,2)]⟩
theorem node115 : UpperPrefix a [2,4,6,0,7,1,3] 30 :=
  local_sound a [2,4,6,0,7,1,3] 30 cert115 (by decide +kernel)

def cert116 : Local := ⟨⟨488,488,419,0,0,0,0,107,171⟩,[(3,0),(4,6),(5,1),(6,4)],[(2,0,3),(4,1,5)]⟩
theorem node116 : UpperPrefix a [2,4,6,0,7,1,5] 30 :=
  local_sound a [2,4,6,0,7,1,5] 30 cert116 (by decide +kernel)

def cert117 : Local := ⟨⟨232,232,163,0,75,0,0,107,171⟩,[(3,0),(5,1),(6,7)],[(2,0,3),(4,1,5),(8,6,6)]⟩
theorem node117 : UpperPrefix a [2,4,6,0,7,1,8] 30 :=
  local_sound a [2,4,6,0,7,1,8] 30 cert117 (by decide +kernel)

theorem node118 : UpperPrefix a [2,4,6,0,7,1] 30 :=
  branch_upper a [2,4,6,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,1,2] 30 (by decide +kernel))
  node115
  (invalid_upper a [2,4,6,0,7,1,4] 30 (by decide +kernel))
  node116
  (invalid_upper a [2,4,6,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,1,7] 30 (by decide +kernel))
  node117)

def cert119 : Leaf := ⟨⟨248,232,178,0,72,192,56,120,184⟩,[(3,0)],[(2,0,3)],⟨7,19,76,13,176,56,194,416,352⟩,⟨7,19,76,13,176,56,194,384,320⟩,[⟨0,1271913435771315910870016,⟨502,466,508,508,176,444,194,384,320⟩⟩,⟨8,1184356292524540423679,⟨47,127,127,47,255,127,255,255,127⟩⟩,⟨1,1531938686301218955853825,⟨445,185,508,445,176,184,496,384,464⟩⟩]⟩
theorem node119 : UpperPrefix a [2,4,6,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,3,1] 30 cert119 (by decide +kernel)

def cert120 : Leaf := ⟨⟨504,488,434,0,0,450,0,122,186⟩,[(3,0),(4,6),(6,4)],[(2,0,3)],⟨7,19,76,13,176,56,224,386,322⟩,⟨7,19,76,13,176,56,224,384,320⟩,[⟨0,1224302785635762920489984,⟨502,466,124,508,244,124,244,384,336⟩⟩]⟩
theorem node120 : UpperPrefix a [2,4,6,0,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,3,5] 30 cert120 (by decide +kernel)

def cert121 : Leaf := ⟨⟨248,232,178,0,74,194,0,122,186⟩,[(3,0),(6,7)],[(2,0,3),(8,6,6)],⟨7,19,76,13,176,56,448,418,354⟩,⟨7,19,76,13,176,56,448,384,320⟩,[⟨0,1214841659562981954946048,⟨502,466,124,508,244,124,448,448,320⟩⟩]⟩
theorem node121 : UpperPrefix a [2,4,6,0,7,3,8] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,3,8] 30 cert121 (by decide +kernel)

theorem node122 : UpperPrefix a [2,4,6,0,7,3] 30 :=
  branch_upper a [2,4,6,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,7,3,0] 30 (by decide +kernel))
  node119
  (invalid_upper a [2,4,6,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,3,4] 30 (by decide +kernel))
  node120
  (invalid_upper a [2,4,6,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,3,7] 30 (by decide +kernel))
  node121)

def cert123 : Leaf := ⟨⟨176,160,179,0,256,128,59,123,187⟩,[(3,0)],[(2,0,3),(8,5,4)],⟨7,19,76,13,176,304,234,426,362⟩,⟨7,19,76,13,176,304,192,384,320⟩,[⟨3,1210107578807843634023437,⟨7,19,87,7,176,304,240,432,368⟩⟩,⟨6,1210106425886340772006925,⟨15,27,31,15,176,304,176,432,304⟩⟩,⟨0,1210107578807844707763200,⟨6,18,92,12,176,304,240,432,368⟩⟩,⟨1,1210107578807844841979905,⟨13,25,92,13,176,304,240,432,368⟩⟩]⟩
theorem node123 : UpperPrefix a [2,4,6,0,7,8] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,8] 30 cert123 (by decide +kernel)

theorem node124 : UpperPrefix a [2,4,6,0,7] 30 :=
  branch_upper a [2,4,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,7,0] 30 (by decide +kernel))
  node118
  (invalid_upper a [2,4,6,0,7,2] 30 (by decide +kernel))
  node122
  (invalid_upper a [2,4,6,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,7] 30 (by decide +kernel))
  node123)

def cert125 : Leaf := ⟨⟨376,360,306,0,72,320,312,120,184⟩,[(3,0)],[(2,0,3)],⟨7,19,76,13,304,56,194,416,480⟩,⟨7,19,76,13,304,56,194,384,320⟩,[⟨0,1272061009723905587282944,⟨502,466,508,508,432,444,194,384,320⟩⟩,⟨7,1208926990085502979532245,⟨47,59,111,13,319,59,127,319,383⟩⟩,⟨1,1532086260251472170057729,⟨445,185,508,445,432,184,496,384,464⟩⟩]⟩
theorem node125 : UpperPrefix a [2,4,6,0,8,3,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,8,3,1] 30 cert125 (by decide +kernel)

def cert126 : Leaf := ⟨⟨464,448,402,0,194,450,274,82,146⟩,[(3,0)],[(2,0,3)],⟨7,19,76,13,304,56,224,386,450⟩,⟨7,19,76,13,304,56,224,384,320⟩,[⟨0,1224302497400988722267136,⟨502,466,124,508,308,124,228,384,320⟩⟩,⟨3,1768519043208874829040653,⟨391,467,471,391,498,499,498,384,464⟩⟩,⟨5,1513076888824603307172945,⟨15,155,461,13,415,155,463,396,461⟩⟩]⟩
theorem node126 : UpperPrefix a [2,4,6,0,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,6,0,8,3,5] 30 cert126 (by decide +kernel)

theorem node127 : UpperPrefix a [2,4,6,0,8,3] 30 :=
  branch_upper a [2,4,6,0,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,8,3,0] 30 (by decide +kernel))
  node125
  (invalid_upper a [2,4,6,0,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,3,4] 30 (by decide +kernel))
  node126
  (invalid_upper a [2,4,6,0,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,3,8] 30 (by decide +kernel)))

#print axioms node127
end Delivery.FiniteExclusion.Sharp2x2x2x3
