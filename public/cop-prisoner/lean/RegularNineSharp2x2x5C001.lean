import RegularNineSharp2x2x5Base
import RegularNineSharp2x2x5C000
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Bounds BoundTreeRows Extremal
theorem node64 : UpperPrefix a [2,4,0,6] 30 :=
  branch_upper a [2,4,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,0] 30 (by decide +kernel))
  node51
  (invalid_upper a [2,4,0,6,2] 30 (by decide +kernel))
  node52
  (invalid_upper a [2,4,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,6] 30 (by decide +kernel))
  node59
  node63)

theorem node65 : UpperPrefix a [2,4,0] 30 :=
  branch_upper a [2,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut20 [2,4,0,1] [2,3,0,4] 30 (by decide +kernel) node1)
  (invalid_upper a [2,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,4] 30 (by decide +kernel))
  node50
  node64
  (PrefixConjugacy.upper aut22 [2,4,0,7] [2,4,0,6] 30 (by decide +kernel) node64)
  (PrefixConjugacy.upper aut21 [2,4,0,8] [2,4,0,5] 30 (by decide +kernel) node50))

def cert66 : Leaf := ⟨⟨0,0,304,272,268,412,316,124,236⟩,[(0,2),(1,4)],[(1,2,0),(0,4,1)],⟨7,19,14,44,49,488,456,456,472⟩,⟨7,19,14,44,49,96,192,384,272⟩,[⟨6,1210106412365102383267263,⟨7,31,31,63,63,63,129,391,287⟩⟩,⟨7,1208926973665889578810815,⟨7,31,31,63,63,127,65,263,287⟩⟩]⟩
theorem node66 : UpperPrefix a [2,4,1,5,0] 30 :=
  Boolean.leaf_sound a [2,4,1,5,0] 30 cert66 (by decide +kernel)

def cert67 : Leaf := ⟨⟨0,456,465,465,0,401,273,81,193⟩,[(0,2),(4,3)],[(1,2,0),(5,3,4)],⟨7,19,14,44,56,481,449,449,465⟩,⟨7,19,14,44,56,96,192,384,272⟩,[⟨2,1224302388998144463472129,⟨499,499,506,56,56,96,192,384,272⟩⟩,⟨3,1219616988200928057230341,⟨487,499,487,229,48,96,192,384,272⟩⟩]⟩
theorem node67 : UpperPrefix a [2,4,1,5,3] 30 :=
  Boolean.leaf_sound a [2,4,1,5,3] 30 cert67 (by decide +kernel)

def cert68 : Leaf := ⟨⟨0,44,49,17,0,413,317,61,173⟩,[(0,2),(4,5)],[(1,2,0),(6,4,4)],⟨7,19,14,44,112,489,457,393,409⟩,⟨7,19,14,44,112,96,192,384,272⟩,[⟨7,1208926973665339822994879,⟨7,31,15,63,127,127,65,263,287⟩⟩,⟨8,1181745671428059592127,⟨7,31,15,63,127,127,193,135,31⟩⟩]⟩
theorem node68 : UpperPrefix a [2,4,1,5,6] 30 :=
  Boolean.leaf_sound a [2,4,1,5,6] 30 cert68 (by decide +kernel)

def cert69 : Leaf := ⟨⟨0,232,241,209,72,152,312,120,232⟩,[(0,2)],[(1,2,0)],⟨7,19,14,44,176,97,456,456,344⟩,⟨7,19,14,44,176,97,192,384,272⟩,[⟨2,1266886859751314646124033,⟨499,51,474,506,178,115,192,384,272⟩⟩,⟨8,1181747925435503273471,⟨7,31,15,47,191,127,255,135,31⟩⟩,⟨0,1266886859716061555590144,⟨454,18,478,508,176,96,192,384,272⟩⟩]⟩
theorem node69 : UpperPrefix a [2,4,1,5,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,5,7,0] 30 cert69 (by decide +kernel)

def cert70 : Leaf := ⟨⟨0,224,241,209,65,145,305,113,225⟩,[(0,2)],[(1,2,0),(3,5,3)],⟨7,19,14,44,176,104,449,449,337⟩,⟨7,19,14,44,176,104,192,384,272⟩,[⟨2,1224302389032847799223809,⟨499,467,506,56,176,104,192,384,272⟩⟩,⟨8,1181747925435503273471,⟨7,31,15,47,191,127,255,135,31⟩⟩]⟩
theorem node70 : UpperPrefix a [2,4,1,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,1,5,7,3] 30 cert70 (by decide +kernel)

def cert71 : Leaf := ⟨⟨0,200,209,209,329,153,24,81,201⟩,[(0,2)],[(1,2,0),(8,5,4)],⟨7,19,14,44,176,352,193,392,336⟩,⟨7,19,14,44,176,352,193,392,272⟩,[⟨2,1677732547929431657711105,⟨499,371,442,440,432,370,499,408,272⟩⟩,⟨5,1295149882598318834590869,⟨455,339,463,205,471,322,197,463,339⟩⟩]⟩
theorem node71 : UpperPrefix a [2,4,1,5,7,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,1,5,7,8,0,3] 30 cert71 (by decide +kernel)

def cert72 : Local := ⟨⟨0,172,177,145,333,0,60,0,173⟩,[(0,2),(5,7),(7,5)],[(1,2,0),(8,5,4),(6,7,4)]⟩
theorem node72 : UpperPrefix a [2,4,1,5,7,8,0,6] 30 :=
  local_sound a [2,4,1,5,7,8,0,6] 30 cert72 (by decide +kernel)

theorem node73 : UpperPrefix a [2,4,1,5,7,8,0] 30 :=
  branch_upper a [2,4,1,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,5,7,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,0,2] 30 (by decide +kernel))
  node71
  (invalid_upper a [2,4,1,5,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,0,5] 30 (by decide +kernel))
  node72
  (invalid_upper a [2,4,1,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,0,8] 30 (by decide +kernel)))

def cert74 : Leaf := ⟨⟨0,36,49,17,325,149,53,117,229⟩,[(0,2)],[(1,2,0),(8,5,4)],⟨7,19,14,44,176,352,200,449,337⟩,⟨7,19,14,44,176,352,200,384,272⟩,[⟨3,1512929318256263495193613,⟨7,19,7,55,176,498,499,384,272⟩⟩,⟨6,1210106412362353602078135,⟨7,31,15,45,191,303,137,391,287⟩⟩,⟨7,1208926973663140797621687,⟨7,31,15,45,63,367,73,263,287⟩⟩]⟩
theorem node74 : UpperPrefix a [2,4,1,5,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,1,5,7,8,3] 30 cert74 (by decide +kernel)

theorem node75 : UpperPrefix a [2,4,1,5,7,8] 30 :=
  branch_upper a [2,4,1,5,7,8] 30 (by decide) (fin9_cases _
  node73
  (invalid_upper a [2,4,1,5,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,2] 30 (by decide +kernel))
  node74
  (invalid_upper a [2,4,1,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,8,8] 30 (by decide +kernel)))

theorem node76 : UpperPrefix a [2,4,1,5,7] 30 :=
  branch_upper a [2,4,1,5,7] 30 (by decide) (fin9_cases _
  node69
  (invalid_upper a [2,4,1,5,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,2] 30 (by decide +kernel))
  node70
  (invalid_upper a [2,4,1,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,7] 30 (by decide +kernel))
  node75)

def cert77 : Leaf := ⟨⟨0,232,225,193,201,136,41,105,233⟩,[(0,2)],[(1,2,0)],⟨7,19,14,44,304,97,200,456,472⟩,⟨7,19,14,44,304,97,192,384,272⟩,[⟨2,1266886859751314646124033,⟨499,51,474,506,306,115,192,384,272⟩⟩,⟨4,1210255463740810861478919,⟨111,239,111,45,488,109,192,384,448⟩⟩,⟨8,1184058267659188970903,⟨7,31,15,45,63,105,237,239,31⟩⟩]⟩
theorem node77 : UpperPrefix a [2,4,1,5,8,0] 30 :=
  Boolean.leaf_sound a [2,4,1,5,8,0] 30 cert77 (by decide +kernel)

def cert78 : Leaf := ⟨⟨0,224,241,209,193,145,49,113,225⟩,[(0,2)],[(1,2,0),(3,5,3)],⟨7,19,14,44,304,104,193,449,465⟩,⟨7,19,14,44,304,104,192,384,272⟩,[⟨2,1224302389032847799223809,⟨499,467,506,56,304,104,192,384,272⟩⟩,⟨8,1184058267659188970903,⟨7,31,15,45,63,104,237,239,31⟩⟩]⟩
theorem node78 : UpperPrefix a [2,4,1,5,8,3] 30 :=
  Boolean.leaf_sound a [2,4,1,5,8,3] 30 cert78 (by decide +kernel)

def cert79 : Leaf := ⟨⟨0,44,49,17,77,0,61,125,109⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5)],⟨7,19,14,44,304,224,201,457,345⟩,⟨7,19,14,44,304,224,192,384,272⟩,[⟨8,1184634728415787361687,⟨7,31,15,109,127,237,237,239,31⟩⟩,⟨6,1210106412362349298722199,⟨7,31,15,45,319,161,129,391,287⟩⟩]⟩
theorem node79 : UpperPrefix a [2,4,1,5,8,7] 30 :=
  Boolean.leaf_sound a [2,4,1,5,8,7] 30 cert79 (by decide +kernel)

theorem node80 : UpperPrefix a [2,4,1,5,8] 30 :=
  branch_upper a [2,4,1,5,8] 30 (by decide) (fin9_cases _
  node77
  (invalid_upper a [2,4,1,5,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,8,2] 30 (by decide +kernel))
  node78
  (invalid_upper a [2,4,1,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,8,6] 30 (by decide +kernel))
  node79
  (invalid_upper a [2,4,1,5,8,8] 30 (by decide +kernel)))

theorem node81 : UpperPrefix a [2,4,1,5] 30 :=
  branch_upper a [2,4,1,5] 30 (by decide) (fin9_cases _
  node66
  (invalid_upper a [2,4,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,2] 30 (by decide +kernel))
  node67
  (invalid_upper a [2,4,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,5] 30 (by decide +kernel))
  node68
  node76
  node80)

def cert82 : Leaf := ⟨⟨0,0,112,48,76,412,316,124,236⟩,[(0,2),(1,4)],[(1,2,0),(0,4,1)],⟨7,19,14,76,49,488,488,424,440⟩,⟨7,19,14,76,49,96,192,384,272⟩,[⟨7,1208926973665337605776695,⟨7,23,15,77,63,127,64,259,279⟩⟩,⟨8,1181745671425842373943,⟨7,23,15,77,63,127,192,131,23⟩⟩]⟩
theorem node82 : UpperPrefix a [2,4,1,6,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,0] 30 cert82 (by decide +kernel)

def cert83 : Leaf := ⟨⟨0,296,305,305,321,401,305,49,161⟩,[(0,2)],[(1,2,0),(6,3,4)],⟨7,19,14,76,56,481,481,417,433⟩,⟨7,19,14,76,56,96,192,384,272⟩,[⟨2,1224302388997594707658241,⟨499,499,506,88,56,96,192,384,272⟩⟩,⟨3,1219616988200928057230341,⟨487,499,487,229,48,96,192,384,272⟩⟩,⟨7,1208926973665337605776695,⟨7,23,15,77,63,127,64,259,279⟩⟩]⟩
theorem node83 : UpperPrefix a [2,4,1,6,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,3] 30 cert83 (by decide +kernel)

def cert84 : Leaf := ⟨⟨0,480,496,432,320,400,304,112,224⟩,[(0,2)],[(1,2,0),(3,6,3)],⟨7,19,14,76,176,97,200,416,304⟩,⟨7,19,14,76,176,97,200,384,272⟩,[⟨0,1437224779041493418247168,⟨78,478,78,76,504,508,200,384,464⟩⟩,⟨2,1451418719979266776253953,⟨499,435,474,72,434,499,200,384,400⟩⟩]⟩
theorem node84 : UpperPrefix a [2,4,1,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,0,3] 30 cert84 (by decide +kernel)

def cert85 : Leaf := ⟨⟨0,492,496,432,0,412,0,124,236⟩,[(0,2),(4,6),(6,4)],[(1,2,0)],⟨7,19,14,76,176,97,224,392,280⟩,⟨7,19,14,76,176,97,224,384,272⟩,[⟨0,1787408509140359047808000,⟨398,478,398,476,504,508,504,384,464⟩⟩]⟩
theorem node85 : UpperPrefix a [2,4,1,6,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,0,5] 30 cert85 (by decide +kernel)

def cert86 : Leaf := ⟨⟨0,236,240,176,76,156,0,124,236⟩,[(0,2),(6,7)],[(1,2,0),(8,6,6)],⟨7,19,14,76,176,97,448,424,312⟩,⟨7,19,14,76,176,97,448,384,272⟩,[⟨0,1437231696570521059329024,⟨78,478,78,76,504,508,448,448,464⟩⟩]⟩
theorem node86 : UpperPrefix a [2,4,1,6,7,0,8] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,0,8] 30 cert86 (by decide +kernel)

theorem node87 : UpperPrefix a [2,4,1,6,7,0] 30 :=
  branch_upper a [2,4,1,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,6,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,0,2] 30 (by decide +kernel))
  node84
  (invalid_upper a [2,4,1,6,7,0,4] 30 (by decide +kernel))
  node85
  (invalid_upper a [2,4,1,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,0,7] 30 (by decide +kernel))
  node86)

def cert88 : Leaf := ⟨⟨0,424,433,433,265,0,312,57,169⟩,[(0,2),(5,3)],[(1,2,0),(6,3,5)],⟨7,19,14,76,176,104,193,416,304⟩,⟨7,19,14,76,176,104,193,384,272⟩,[⟨2,1498734600901648554427905,⟨499,467,506,506,432,506,467,384,400⟩⟩]⟩
theorem node88 : UpperPrefix a [2,4,1,6,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,3,0] 30 cert88 (by decide +kernel)

def cert89 : Local := ⟨⟨0,428,433,433,0,0,0,61,173⟩,[(0,2),(4,6),(5,3),(6,4)],[(1,2,0),(6,3,5)]⟩
theorem node89 : UpperPrefix a [2,4,1,6,7,3,5] 30 :=
  local_sound a [2,4,1,6,7,3,5] 30 cert89 (by decide +kernel)

def cert90 : Local := ⟨⟨0,172,177,177,13,0,0,61,173⟩,[(0,2),(5,3),(6,7)],[(1,2,0),(6,3,5),(8,6,6)]⟩
theorem node90 : UpperPrefix a [2,4,1,6,7,3,8] 30 :=
  local_sound a [2,4,1,6,7,3,8] 30 cert90 (by decide +kernel)

theorem node91 : UpperPrefix a [2,4,1,6,7,3] 30 :=
  branch_upper a [2,4,1,6,7,3] 30 (by decide) (fin9_cases _
  node88
  (invalid_upper a [2,4,1,6,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,4] 30 (by decide +kernel))
  node89
  (invalid_upper a [2,4,1,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,3,7] 30 (by decide +kernel))
  node90)

def cert92 : Leaf := ⟨⟨0,232,241,177,328,152,56,120,232⟩,[(0,2)],[(1,2,0),(8,5,4)],⟨7,19,14,76,176,352,193,424,312⟩,⟨7,19,14,76,176,352,193,384,272⟩,[⟨2,1266886661879078942967297,⟨499,115,442,506,176,370,243,384,272⟩⟩,⟨0,1266886643825029296423936,⟨406,18,446,508,176,352,192,384,272⟩⟩]⟩
theorem node92 : UpperPrefix a [2,4,1,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,8,0] 30 cert92 (by decide +kernel)

def cert93 : Leaf := ⟨⟨0,224,241,177,321,145,49,113,225⟩,[(0,2)],[(1,2,0),(8,5,4),(3,6,3)],⟨7,19,14,76,176,352,200,417,305⟩,⟨7,19,14,76,176,352,200,384,272⟩,[⟨2,1224302407082568119748097,⟨499,435,506,120,176,352,200,384,272⟩⟩]⟩
theorem node93 : UpperPrefix a [2,4,1,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,8,3] 30 cert93 (by decide +kernel)

def cert94 : Leaf := ⟨⟨0,204,209,145,0,157,0,93,205⟩,[(0,2),(4,6),(6,4)],[(1,2,0),(8,5,4),(8,5,6)],⟨7,19,14,76,176,352,224,393,281⟩,⟨7,19,14,76,176,352,224,384,272⟩,[⟨5,1286108149741648029558071,⟨7,407,15,77,415,463,205,387,407⟩⟩]⟩
theorem node94 : UpperPrefix a [2,4,1,6,7,8,5] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,8,5] 30 cert94 (by decide +kernel)

theorem node95 : UpperPrefix a [2,4,1,6,7,8] 30 :=
  branch_upper a [2,4,1,6,7,8] 30 (by decide) (fin9_cases _
  node92
  (invalid_upper a [2,4,1,6,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,8,2] 30 (by decide +kernel))
  node93
  (invalid_upper a [2,4,1,6,7,8,4] 30 (by decide +kernel))
  node94
  (invalid_upper a [2,4,1,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,8,8] 30 (by decide +kernel)))

theorem node96 : UpperPrefix a [2,4,1,6,7] 30 :=
  branch_upper a [2,4,1,6,7] 30 (by decide) (fin9_cases _
  node87
  (invalid_upper a [2,4,1,6,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,2] 30 (by decide +kernel))
  node91
  (invalid_upper a [2,4,1,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,7] 30 (by decide +kernel))
  node95)

def cert97 : Leaf := ⟨⟨0,480,496,432,192,400,304,112,224⟩,[(0,2)],[(1,2,0),(3,6,3)],⟨7,19,14,76,304,97,200,416,432⟩,⟨7,19,14,76,304,97,200,384,272⟩,[⟨0,1437224779041493418247168,⟨78,478,78,76,504,508,200,384,464⟩⟩,⟨2,1451418719979266776253953,⟨499,435,474,72,434,499,200,384,400⟩⟩]⟩
theorem node97 : UpperPrefix a [2,4,1,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,0,3] 30 cert97 (by decide +kernel)

def cert98 : Leaf := ⟨⟨0,488,480,416,200,392,264,104,232⟩,[(0,2)],[(1,2,0)],⟨7,19,14,76,304,97,224,392,408⟩,⟨7,19,14,76,304,97,224,384,272⟩,[⟨0,1787408509140359047808000,⟨398,478,398,476,504,508,504,384,464⟩⟩,⟨2,1266886733720618946020865,⟨499,115,506,472,306,115,226,384,272⟩⟩,⟨4,1210255464022285838189575,⟨111,239,111,109,488,109,232,384,448⟩⟩]⟩
theorem node98 : UpperPrefix a [2,4,1,6,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,0,5] 30 cert98 (by decide +kernel)

theorem node99 : UpperPrefix a [2,4,1,6,8,0] 30 :=
  branch_upper a [2,4,1,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,6,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,0,2] 30 (by decide +kernel))
  node97
  (invalid_upper a [2,4,1,6,8,0,4] 30 (by decide +kernel))
  node98
  (invalid_upper a [2,4,1,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,0,8] 30 (by decide +kernel)))

def cert100 : Leaf := ⟨⟨0,424,433,433,137,0,312,57,169⟩,[(0,2),(5,3)],[(1,2,0),(6,3,5)],⟨7,19,14,76,304,104,193,416,432⟩,⟨7,19,14,76,304,104,193,384,272⟩,[⟨2,1498734600901648554427905,⟨499,467,506,506,432,506,467,384,400⟩⟩]⟩
theorem node100 : UpperPrefix a [2,4,1,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,3,0] 30 cert100 (by decide +kernel)

def cert101 : Leaf := ⟨⟨0,424,433,433,137,0,281,57,169⟩,[(0,2),(5,3)],[(1,2,0),(6,3,5)],⟨7,19,14,76,304,104,224,385,401⟩,⟨7,19,14,76,304,104,224,384,272⟩,[⟨2,1224302425343119794898433,⟨499,467,506,120,304,104,224,384,272⟩⟩]⟩
theorem node101 : UpperPrefix a [2,4,1,6,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,3,5] 30 cert101 (by decide +kernel)

theorem node102 : UpperPrefix a [2,4,1,6,8,3] 30 :=
  branch_upper a [2,4,1,6,8,3] 30 (by decide) (fin9_cases _
  node100
  (invalid_upper a [2,4,1,6,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,4] 30 (by decide +kernel))
  node101
  (invalid_upper a [2,4,1,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,3,8] 30 (by decide +kernel)))

def cert103 : Leaf := ⟨⟨0,360,369,305,73,0,312,121,105⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5)],⟨7,19,14,76,304,224,193,424,312⟩,⟨7,19,14,76,304,224,193,384,272⟩,[⟨2,1266886664126480710141441,⟨499,115,442,506,304,226,243,384,272⟩⟩]⟩
theorem node103 : UpperPrefix a [2,4,1,6,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,7,0] 30 cert103 (by decide +kernel)

def cert104 : Local := ⟨⟨0,356,369,305,69,0,309,117,101⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5),(3,6,3)]⟩
theorem node104 : UpperPrefix a [2,4,1,6,8,7,3] 30 :=
  local_sound a [2,4,1,6,8,7,3] 30 cert104 (by decide +kernel)

def cert105 : Local := ⟨⟨0,364,369,305,77,0,0,125,109⟩,[(0,2),(5,6),(6,5)],[(1,2,0),(7,5,5),(7,5,6)]⟩
theorem node105 : UpperPrefix a [2,4,1,6,8,7,5] 30 :=
  local_sound a [2,4,1,6,8,7,5] 30 cert105 (by decide +kernel)

theorem node106 : UpperPrefix a [2,4,1,6,8,7] 30 :=
  branch_upper a [2,4,1,6,8,7] 30 (by decide) (fin9_cases _
  node103
  (invalid_upper a [2,4,1,6,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,7,2] 30 (by decide +kernel))
  node104
  (invalid_upper a [2,4,1,6,8,7,4] 30 (by decide +kernel))
  node105
  (invalid_upper a [2,4,1,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,7,8] 30 (by decide +kernel)))

theorem node107 : UpperPrefix a [2,4,1,6,8] 30 :=
  branch_upper a [2,4,1,6,8] 30 (by decide) (fin9_cases _
  node99
  (invalid_upper a [2,4,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,2] 30 (by decide +kernel))
  node102
  (invalid_upper a [2,4,1,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,6] 30 (by decide +kernel))
  node106
  (invalid_upper a [2,4,1,6,8,8] 30 (by decide +kernel)))

theorem node108 : UpperPrefix a [2,4,1,6] 30 :=
  branch_upper a [2,4,1,6] 30 (by decide) (fin9_cases _
  node82
  (invalid_upper a [2,4,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,2] 30 (by decide +kernel))
  node83
  (invalid_upper a [2,4,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,6] 30 (by decide +kernel))
  node96
  node107)

def cert109 : Leaf := ⟨⟨0,0,176,48,140,412,316,124,236⟩,[(0,2),(1,4)],[(1,2,0),(0,4,1)],⟨7,19,14,140,49,360,488,488,376⟩,⟨7,19,14,140,49,96,192,384,272⟩,[⟨6,1210106412364571914429621,⟨7,19,15,141,55,63,141,399,275⟩⟩,⟨8,1181745671447346570421,⟨7,19,15,141,55,127,205,143,19⟩⟩]⟩
theorem node109 : UpperPrefix a [2,4,1,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,7,0] 30 cert109 (by decide +kernel)

def cert110 : Leaf := ⟨⟨0,168,177,49,129,401,305,113,225⟩,[(0,2)],[(1,2,0)],⟨7,19,14,140,56,353,481,481,369⟩,⟨7,19,14,140,56,96,192,384,272⟩,[⟨2,1224302388997594707658241,⟨499,499,506,152,56,96,192,384,272⟩⟩,⟨3,1219616988200928057230341,⟨487,499,487,229,48,96,192,384,272⟩⟩,⟨6,1210106412364571918624183,⟨7,23,15,141,63,63,141,399,279⟩⟩,⟨8,1181745671447350764983,⟨7,23,15,141,63,127,205,143,23⟩⟩]⟩
theorem node110 : UpperPrefix a [2,4,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,1,7,3] 30 cert110 (by decide +kernel)

def cert111 : Leaf := ⟨⟨0,140,145,17,0,413,317,61,173⟩,[(0,2),(4,5)],[(1,2,0),(6,4,4)],⟨7,19,14,140,112,361,489,425,313⟩,⟨7,19,14,140,112,96,192,384,272⟩,[⟨5,1210107564157977586967959,⟨7,23,15,141,95,72,205,399,279⟩⟩,⟨8,1181745671447350764983,⟨7,23,15,141,127,127,205,143,23⟩⟩]⟩
theorem node111 : UpperPrefix a [2,4,1,7,6] 30 :=
  Boolean.leaf_sound a [2,4,1,7,6] 30 cert111 (by decide +kernel)

def cert112 : Leaf := ⟨⟨0,364,368,368,76,284,0,124,108⟩,[(0,2),(6,3)],[(1,2,0),(7,3,6)],⟨7,19,14,140,304,97,200,480,368⟩,⟨7,19,14,140,304,97,200,384,272⟩,[⟨0,1437224923156680823014400,⟨78,478,78,204,504,508,200,384,464⟩⟩]⟩
theorem node112 : UpperPrefix a [2,4,1,7,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,0,3] 30 cert112 (by decide +kernel)

def cert113 : Leaf := ⟨⟨0,488,496,368,200,400,272,120,232⟩,[(0,2)],[(1,2,0)],⟨7,19,14,140,304,97,224,456,344⟩,⟨7,19,14,140,304,97,224,384,272⟩,[⟨0,1749509673440923445101568,⟨398,478,398,140,504,508,504,384,464⟩⟩,⟨2,1266886733720618946020865,⟨499,115,506,472,306,115,226,384,272⟩⟩,⟨3,1210107709821251153298437,⟨39,19,103,229,304,97,224,384,272⟩⟩]⟩
theorem node113 : UpperPrefix a [2,4,1,7,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,0,5] 30 cert113 (by decide +kernel)

theorem node114 : UpperPrefix a [2,4,1,7,8,0] 30 :=
  branch_upper a [2,4,1,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,7,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,2] 30 (by decide +kernel))
  node112
  (invalid_upper a [2,4,1,7,8,0,4] 30 (by decide +kernel))
  node113
  (invalid_upper a [2,4,1,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,8] 30 (by decide +kernel)))

def cert115 : Leaf := ⟨⟨0,360,369,369,65,401,304,113,97⟩,[(0,2)],[(1,2,0),(7,3,5)],⟨7,19,14,140,304,104,193,480,368⟩,⟨7,19,14,140,304,104,193,384,272⟩,[⟨2,1385176444102417577969153,⟨499,467,506,440,432,506,467,384,272⟩⟩,⟨3,1361518584758245711152133,⟨7,19,71,197,432,496,193,384,272⟩⟩]⟩
theorem node115 : UpperPrefix a [2,4,1,7,8,3,0] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,3,0] 30 cert115 (by decide +kernel)

def cert116 : Leaf := ⟨⟨0,360,369,369,73,384,264,121,105⟩,[(0,2)],[(1,2,0),(7,3,5)],⟨7,19,14,140,304,104,224,449,337⟩,⟨7,19,14,140,304,104,224,384,272⟩,[⟨2,1224302569458307870754305,⟨499,467,506,248,304,104,224,384,272⟩⟩,⟨0,1210107709821252227040256,⟨38,18,110,236,304,104,224,384,272⟩⟩,⟨4,1210107709820152715412485,⟨39,3,111,237,288,104,224,384,256⟩⟩]⟩
theorem node116 : UpperPrefix a [2,4,1,7,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,3,5] 30 cert116 (by decide +kernel)

theorem node117 : UpperPrefix a [2,4,1,7,8,3] 30 :=
  branch_upper a [2,4,1,7,8,3] 30 (by decide) (fin9_cases _
  node115
  (invalid_upper a [2,4,1,7,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,4] 30 (by decide +kernel))
  node116
  (invalid_upper a [2,4,1,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,8] 30 (by decide +kernel)))

theorem node118 : UpperPrefix a [2,4,1,7,8] 30 :=
  branch_upper a [2,4,1,7,8] 30 (by decide) (fin9_cases _
  node114
  (invalid_upper a [2,4,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,2] 30 (by decide +kernel))
  node117
  (invalid_upper a [2,4,1,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,8] 30 (by decide +kernel)))

theorem node119 : UpperPrefix a [2,4,1,7] 30 :=
  branch_upper a [2,4,1,7] 30 (by decide) (fin9_cases _
  node109
  (invalid_upper a [2,4,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,2] 30 (by decide +kernel))
  node110
  (invalid_upper a [2,4,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,5] 30 (by decide +kernel))
  node111
  (invalid_upper a [2,4,1,7,7] 30 (by decide +kernel))
  node118)

def cert120 : Leaf := ⟨⟨0,0,496,240,456,408,312,120,236⟩,[(0,2),(1,4)],[(1,2,0),(0,4,1)],⟨7,19,14,268,49,232,232,488,504⟩,⟨7,19,14,268,49,96,192,384,272⟩,[⟨2,1210181568855209821611521,⟨115,19,234,488,51,96,192,384,274⟩⟩]⟩
theorem node120 : UpperPrefix a [2,4,1,8,0] 30 :=
  Boolean.leaf_sound a [2,4,1,8,0] 30 cert120 (by decide +kernel)

def cert121 : Leaf := ⟨⟨0,232,241,241,449,129,33,97,225⟩,[(0,2)],[(1,2,0)],⟨7,19,14,268,56,225,225,481,497⟩,⟨7,19,14,268,56,96,192,384,272⟩,[⟨2,1224302388997594707658241,⟨499,499,506,280,56,96,192,384,272⟩⟩,⟨3,1219690919573885948003333,⟨487,499,487,485,240,96,192,384,272⟩⟩,⟨8,1184056015831358907679,⟨7,23,15,15,63,96,224,227,23⟩⟩,⟨4,1210181568854041591546885,⟨103,3,239,493,232,96,192,384,256⟩⟩]⟩
theorem node121 : UpperPrefix a [2,4,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,1,8,3] 30 cert121 (by decide +kernel)

def cert122 : Leaf := ⟨⟨0,396,401,145,0,397,301,45,173⟩,[(0,2),(4,5)],[(1,2,0),(6,4,4)],⟨7,19,14,268,112,233,233,425,441⟩,⟨7,19,14,268,112,96,192,384,272⟩,[⟨4,1210181568854041591546885,⟨103,3,239,493,96,96,192,384,256⟩⟩,⟨5,1210107564158003421775245,⟨7,19,15,271,80,64,205,399,287⟩⟩]⟩
theorem node122 : UpperPrefix a [2,4,1,8,6] 30 :=
  Boolean.leaf_sound a [2,4,1,8,6] 30 cert122 (by decide +kernel)

def cert123 : Leaf := ⟨⟨0,332,336,80,332,268,300,108,236⟩,[(0,2)],[(1,2,0)],⟨7,19,14,268,176,97,232,488,376⟩,⟨7,19,14,268,176,97,192,384,272⟩,[⟨0,1437224743012695728194560,⟨14,478,14,268,504,508,192,384,464⟩⟩,⟨7,1208926975914985735202207,⟨7,23,15,271,63,97,109,271,287⟩⟩,⟨4,1210181568889225963635717,⟨103,35,239,493,160,97,192,384,256⟩⟩,⟨5,1210107564158003425977759,⟨7,23,15,271,159,65,205,399,287⟩⟩]⟩
theorem node123 : UpperPrefix a [2,4,1,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,8,7,0] 30 cert123 (by decide +kernel)

def cert124 : Leaf := ⟨⟨0,328,337,81,329,273,280,121,233⟩,[(0,2)],[(1,2,0)],⟨7,19,14,268,176,104,193,480,368⟩,⟨7,19,14,268,176,104,193,384,272⟩,[⟨2,1385176444102417577969153,⟨499,467,506,440,432,506,467,384,272⟩⟩,⟨5,1210110158231388791383455,⟨7,87,15,271,223,77,205,463,351⟩⟩,⟨7,1208926975914985735202207,⟨7,23,15,271,63,109,109,271,287⟩⟩]⟩
theorem node124 : UpperPrefix a [2,4,1,8,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,1,8,7,3,0] 30 cert124 (by decide +kernel)

def cert125 : Leaf := ⟨⟨0,488,497,241,0,401,0,121,233⟩,[(0,2),(4,6),(6,4)],[(1,2,0)],⟨7,19,14,268,176,104,224,449,337⟩,⟨7,19,14,268,176,104,224,384,272⟩,[⟨2,1224302713577893993121281,⟨499,467,506,376,240,120,240,384,336⟩⟩]⟩
theorem node125 : UpperPrefix a [2,4,1,8,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,1,8,7,3,5] 30 cert125 (by decide +kernel)

theorem node126 : UpperPrefix a [2,4,1,8,7,3] 30 :=
  branch_upper a [2,4,1,8,7,3] 30 (by decide) (fin9_cases _
  node124
  (invalid_upper a [2,4,1,8,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,3,4] 30 (by decide +kernel))
  node125
  (invalid_upper a [2,4,1,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,3,8] 30 (by decide +kernel)))

theorem node127 : UpperPrefix a [2,4,1,8,7] 30 :=
  branch_upper a [2,4,1,8,7] 30 (by decide) (fin9_cases _
  node123
  (invalid_upper a [2,4,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,2] 30 (by decide +kernel))
  node126
  (invalid_upper a [2,4,1,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,8] 30 (by decide +kernel)))

#print axioms node127
end Delivery.FiniteExclusion.Sharp2x2x5
