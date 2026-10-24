import RegularNineSharp3x6Base
import RegularNineSharp3x6C000
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node64 : UpperPrefix a [2,3,5,1] 30 :=
  branch_upper a [2,3,5,1] 30 (by decide) (fin9_cases _
  node52
  (invalid_upper a [2,3,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,5] 30 (by decide +kernel))
  node53
  node59
  node63)

def cert65 : Leaf := ⟨⟨0,305,0,291,0,411,315,59,179⟩,[(0,1),(2,4),(4,2)],[(2,0,0)],⟨7,14,37,88,49,498,466,402,410⟩,⟨7,14,37,88,49,96,192,384,264⟩,[⟨6,1257431534283723816047627,⟨407,415,181,415,181,32,128,384,395⟩⟩,⟨7,1208926973665612483558463,⟨23,31,63,95,63,127,64,256,267⟩⟩]⟩
theorem node65 : UpperPrefix a [2,3,5,6,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,0] 30 cert65 (by decide +kernel)

def cert66 : Leaf := ⟨⟨0,49,26,3,73,411,283,27,147⟩,[(0,1)],[(2,0,0)],⟨7,14,37,88,50,497,465,401,409⟩,⟨7,14,37,88,50,96,192,384,264⟩,[⟨5,1285813290066834078303235,⟨7,15,5,472,475,64,192,384,264⟩⟩,⟨6,1247959131201599083385883,⟨7,399,37,415,55,32,128,384,395⟩⟩,⟨7,1208926973665612483558463,⟨23,31,63,95,63,127,64,256,267⟩⟩,⟨8,1181745671700720155711,⟨23,31,63,95,63,127,192,128,11⟩⟩]⟩
theorem node66 : UpperPrefix a [2,3,5,6,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,1] 30 cert66 (by decide +kernel)

def cert67 : Local := ⟨⟨0,368,0,418,330,282,314,122,114⟩,[(0,1),(2,5)],[(2,0,0),(7,4,3),(0,5,2)]⟩
theorem node67 : UpperPrefix a [2,3,5,6,7,0] 30 :=
  local_sound a [2,3,5,6,7,0] 30 cert67 (by decide +kernel)

def cert68 : Leaf := ⟨⟨0,49,26,161,9,25,313,57,49⟩,[(0,1)],[(2,0,0),(7,4,3),(1,5,2)],⟨7,14,37,88,176,98,465,401,281⟩,⟨7,14,37,88,176,98,192,384,264⟩,[⟨6,1257726682191102200517675,⟨407,415,181,415,181,439,128,384,395⟩⟩,⟨8,1181748206908332506623,⟨7,47,47,127,191,127,255,135,47⟩⟩]⟩
theorem node68 : UpperPrefix a [2,3,5,6,7,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,1] 30 cert68 (by decide +kernel)

def cert69 : Leaf := ⟨⟨0,337,346,0,331,0,283,91,83⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(7,4,3),(7,4,5)],⟨7,14,37,88,176,112,451,387,267⟩,⟨7,14,37,88,176,112,192,384,264⟩,[⟨5,1238506452760221495331847,⟨455,463,463,88,152,88,192,384,264⟩⟩]⟩
theorem node69 : UpperPrefix a [2,3,5,6,7,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,4] 30 cert69 (by decide +kernel)

def cert70 : Leaf := ⟨⟨0,113,90,163,266,27,58,58,50⟩,[(0,1)],[(2,0,0),(7,4,3),(8,5,4)],⟨7,14,37,88,176,352,193,402,282⟩,⟨7,14,37,88,176,352,193,384,264⟩,[⟨0,1219579968365976418780160,⟨406,414,180,88,176,352,192,384,264⟩⟩,⟨6,1219578815444471811933187,⟨407,415,181,24,176,288,129,384,264⟩⟩]⟩
theorem node70 : UpperPrefix a [2,3,5,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,8,0] 30 cert70 (by decide +kernel)

def cert71 : Leaf := ⟨⟨0,112,90,162,330,26,57,122,114⟩,[(0,1)],[(2,0,0),(7,4,3),(8,5,4)],⟨7,14,37,88,176,352,194,385,280⟩,⟨7,14,37,88,176,352,194,385,264⟩,[⟨0,1776791545765894833572864,⟨6,302,302,376,440,376,506,384,296⟩⟩]⟩
theorem node71 : UpperPrefix a [2,3,5,6,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,8,1,0] 30 cert71 (by decide +kernel)

def cert72 : Leaf := ⟨⟨0,112,90,162,330,27,56,106,115⟩,[(0,1)],[(2,0,0),(7,4,3),(8,5,4)],⟨7,14,37,88,176,352,194,400,265⟩,⟨7,14,37,88,176,352,194,400,264⟩,[⟨0,1210402785249104212528640,⟨94,94,254,88,184,504,202,400,264⟩⟩]⟩
theorem node72 : UpperPrefix a [2,3,5,6,7,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,8,1,4] 30 cert72 (by decide +kernel)

theorem node73 : UpperPrefix a [2,3,5,6,7,8,1] 30 :=
  branch_upper a [2,3,5,6,7,8,1] 30 (by decide) (fin9_cases _
  node71
  (invalid_upper a [2,3,5,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,3] 30 (by decide +kernel))
  node72
  (invalid_upper a [2,3,5,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,1,8] 30 (by decide +kernel)))

def cert74 : Local := ⟨⟨0,97,74,0,331,11,0,107,99⟩,[(0,1),(3,6),(6,4)],[(2,0,0),(7,4,3),(7,4,6),(8,5,4),(4,6,3)]⟩
theorem node74 : UpperPrefix a [2,3,5,6,7,8,4] 30 :=
  local_sound a [2,3,5,6,7,8,4] 30 cert74 (by decide +kernel)

theorem node75 : UpperPrefix a [2,3,5,6,7,8] 30 :=
  branch_upper a [2,3,5,6,7,8] 30 (by decide) (fin9_cases _
  node70
  node73
  (invalid_upper a [2,3,5,6,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,3] 30 (by decide +kernel))
  node74
  (invalid_upper a [2,3,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,8,8] 30 (by decide +kernel)))

theorem node76 : UpperPrefix a [2,3,5,6,7] 30 :=
  branch_upper a [2,3,5,6,7] 30 (by decide) (fin9_cases _
  node67
  node68
  (invalid_upper a [2,3,5,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,3] 30 (by decide +kernel))
  node69
  (invalid_upper a [2,3,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,7] 30 (by decide +kernel))
  node75)

def cert77 : Leaf := ⟨⟨0,368,0,418,74,282,314,122,242⟩,[(0,1),(2,5)],[(2,0,0),(0,5,2)],⟨7,14,37,88,304,97,210,402,410⟩,⟨7,14,37,88,304,97,192,384,264⟩,[⟨7,1208926976214001350481307,⟨7,47,37,127,311,101,101,279,319⟩⟩]⟩
theorem node77 : UpperPrefix a [2,3,5,6,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,0] 30 cert77 (by decide +kernel)

def cert78 : Leaf := ⟨⟨0,305,274,417,73,281,305,49,177⟩,[(0,1)],[(2,0,0),(1,5,2)],⟨7,14,37,88,304,98,209,401,409⟩,⟨7,14,37,88,304,98,192,384,264⟩,[⟨6,1248106705154188768187435,⟨7,399,37,415,437,39,128,384,395⟩⟩,⟨7,1208926973962201520018875,⟨7,47,37,127,311,103,65,279,319⟩⟩,⟨3,1210255427466816453084195,⟨7,7,37,212,501,103,192,384,256⟩⟩]⟩
theorem node78 : UpperPrefix a [2,3,5,6,8,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,1] 30 cert78 (by decide +kernel)

def cert79 : Leaf := ⟨⟨0,465,474,0,203,0,267,75,195⟩,[(0,1),(3,5),(5,3)],[(2,0,0)],⟨7,14,37,88,304,112,195,387,395⟩,⟨7,14,37,88,304,112,192,384,264⟩,[⟨5,1238506452760221495331847,⟨455,463,463,88,280,88,192,384,264⟩⟩,⟨4,1219580022407797557691395,⟨455,463,229,72,288,96,192,384,264⟩⟩]⟩
theorem node79 : UpperPrefix a [2,3,5,6,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,4] 30 cert79 (by decide +kernel)

def cert80 : Leaf := ⟨⟨0,113,90,35,75,0,58,123,115⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,14,37,88,304,224,193,402,282⟩,⟨7,14,37,88,304,224,193,384,264⟩,[⟨8,1184634728385682224539,⟨7,15,101,127,127,229,229,231,15⟩⟩]⟩
theorem node80 : UpperPrefix a [2,3,5,6,8,7,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,7,0] 30 cert80 (by decide +kernel)

def cert81 : Leaf := ⟨⟨0,97,74,291,75,0,41,123,115⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,14,37,88,304,224,194,401,281⟩,⟨7,14,37,88,304,224,194,384,264⟩,[⟨4,1210109877881160894387675,⟨7,15,37,111,295,229,231,487,271⟩⟩,⟨8,1184058267631231309275,⟨7,15,37,127,55,229,231,231,15⟩⟩]⟩
theorem node81 : UpperPrefix a [2,3,5,6,8,7,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,7,1] 30 cert81 (by decide +kernel)

def cert82 : Local := ⟨⟨0,97,74,0,75,0,299,107,99⟩,[(0,1),(3,6),(5,6)],[(2,0,0),(8,4,6),(7,5,5),(4,6,3)]⟩
theorem node82 : UpperPrefix a [2,3,5,6,8,7,4] 30 :=
  local_sound a [2,3,5,6,8,7,4] 30 cert82 (by decide +kernel)

theorem node83 : UpperPrefix a [2,3,5,6,8,7] 30 :=
  branch_upper a [2,3,5,6,8,7] 30 (by decide) (fin9_cases _
  node80
  node81
  (invalid_upper a [2,3,5,6,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,7,3] 30 (by decide +kernel))
  node82
  (invalid_upper a [2,3,5,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,7,8] 30 (by decide +kernel)))

theorem node84 : UpperPrefix a [2,3,5,6,8] 30 :=
  branch_upper a [2,3,5,6,8] 30 (by decide) (fin9_cases _
  node77
  node78
  (invalid_upper a [2,3,5,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,3] 30 (by decide +kernel))
  node79
  (invalid_upper a [2,3,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,6] 30 (by decide +kernel))
  node83
  (invalid_upper a [2,3,5,6,8,8] 30 (by decide +kernel)))

theorem node85 : UpperPrefix a [2,3,5,6] 30 :=
  branch_upper a [2,3,5,6] 30 (by decide) (fin9_cases _
  node65
  node66
  (invalid_upper a [2,3,5,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,6] 30 (by decide +kernel))
  node76
  node84)

def cert86 : Local := ⟨⟨0,497,0,353,0,409,313,121,241⟩,[(0,1),(2,4),(4,2)],[(2,0,0),(1,5,2),(1,5,4)]⟩
theorem node86 : UpperPrefix a [2,3,5,7,0,1] 30 :=
  local_sound a [2,3,5,7,0,1] 30 cert86 (by decide +kernel)

def cert87 : Leaf := ⟨⟨0,497,0,354,0,394,314,122,242⟩,[(0,1),(2,4),(4,2)],[(2,0,0)],⟨7,14,37,152,49,112,450,450,330⟩,⟨7,14,37,152,49,112,192,384,264⟩,[⟨0,1219580022971849170224128,⟨454,462,228,184,248,120,192,384,264⟩⟩]⟩
theorem node87 : UpperPrefix a [2,3,5,7,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,0,4] 30 cert87 (by decide +kernel)

def cert88 : Leaf := ⟨⟨0,161,0,355,0,155,59,123,243⟩,[(0,1),(2,4),(4,2)],[(2,0,0)],⟨7,14,37,152,49,352,210,466,346⟩,⟨7,14,37,152,49,352,192,384,264⟩,[⟨8,1181889784685469373451,⟨23,95,53,223,53,96,192,128,75⟩⟩,⟨4,1210107565282752178689035,⟨7,15,37,143,37,352,192,384,267⟩⟩,⟨6,1210106412362621961376779,⟨23,31,53,159,53,288,128,384,267⟩⟩]⟩
theorem node88 : UpperPrefix a [2,3,5,7,0,8] 30 :=
  Boolean.leaf_sound a [2,3,5,7,0,8] 30 cert88 (by decide +kernel)

theorem node89 : UpperPrefix a [2,3,5,7,0] 30 :=
  branch_upper a [2,3,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,0,0] 30 (by decide +kernel))
  node86
  (invalid_upper a [2,3,5,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,3] 30 (by decide +kernel))
  node87
  (invalid_upper a [2,3,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,0,7] 30 (by decide +kernel))
  node88)

def cert90 : Leaf := ⟨⟨0,496,0,352,456,410,312,120,240⟩,[(0,1),(2,5)],[(2,0,0),(0,5,2)],⟨7,14,37,152,50,97,464,464,344⟩,⟨7,14,37,152,50,97,192,384,264⟩,[⟨1,1323666154147174069305345,⟨5,460,37,472,508,101,192,384,456⟩⟩]⟩
theorem node90 : UpperPrefix a [2,3,5,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,0] 30 cert90 (by decide +kernel)

def cert91 : Leaf := ⟨⟨0,193,202,67,201,139,267,75,195⟩,[(0,1)],[(2,0,0)],⟨7,14,37,152,50,112,449,449,329⟩,⟨7,14,37,152,50,112,192,384,264⟩,[⟨4,1259946542472656724169755,⟨455,463,229,463,487,229,192,448,459⟩⟩,⟨5,1314212178669103794359303,⟨455,463,463,472,475,472,192,384,264⟩⟩,⟨8,1181747927902892119167,⟨23,31,55,159,55,127,255,128,11⟩⟩]⟩
theorem node91 : UpperPrefix a [2,3,5,7,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,4] 30 cert91 (by decide +kernel)

def cert92 : Leaf := ⟨⟨0,33,2,323,457,147,19,91,211⟩,[(0,1)],[(2,0,0)],⟨7,14,37,152,50,352,209,465,345⟩,⟨7,14,37,152,50,352,192,384,264⟩,[⟨5,1285813290066834078303235,⟨7,15,5,472,475,320,192,384,264⟩⟩,⟨3,1210107718406237947167763,⟨7,71,37,213,55,352,192,416,352⟩⟩,⟨8,1181889784410591466523,⟨7,79,37,223,55,96,192,128,75⟩⟩,⟨4,1210107565282752178689051,⟨7,15,37,143,39,352,192,384,267⟩⟩,⟨6,1210106412362347083469851,⟨7,15,37,159,55,288,128,384,267⟩⟩,⟨7,1208926973663134279013403,⟨7,15,37,31,55,352,64,256,267⟩⟩]⟩
theorem node92 : UpperPrefix a [2,3,5,7,1,8] 30 :=
  Boolean.leaf_sound a [2,3,5,7,1,8] 30 cert92 (by decide +kernel)

theorem node93 : UpperPrefix a [2,3,5,7,1] 30 :=
  branch_upper a [2,3,5,7,1] 30 (by decide) (fin9_cases _
  node90
  (invalid_upper a [2,3,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,3] 30 (by decide +kernel))
  node91
  (invalid_upper a [2,3,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,1,7] 30 (by decide +kernel))
  node92)

def cert94 : Local := ⟨⟨0,432,0,290,0,410,314,58,178⟩,[(0,1),(2,5),(4,5)],[(2,0,0),(6,4,4),(0,5,2)]⟩
theorem node94 : UpperPrefix a [2,3,5,7,6,0] 30 :=
  local_sound a [2,3,5,7,6,0] 30 cert94 (by decide +kernel)

def cert95 : Leaf := ⟨⟨0,177,154,33,0,153,313,57,177⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(1,5,2)],⟨7,14,37,152,112,98,465,401,281⟩,⟨7,14,37,152,112,98,192,384,264⟩,[⟨8,1181748490577969870207,⟨7,15,55,191,127,127,255,131,15⟩⟩]⟩
theorem node95 : UpperPrefix a [2,3,5,7,6,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,1] 30 cert95 (by decide +kernel)

def cert96 : Local := ⟨⟨0,433,410,291,0,0,315,59,179⟩,[(0,1),(4,5),(5,4)],[(2,0,0),(6,4,4),(6,4,5)]⟩
theorem node96 : UpperPrefix a [2,3,5,7,6,4] 30 :=
  local_sound a [2,3,5,7,6,4] 30 cert96 (by decide +kernel)

def cert97 : Leaf := ⟨⟨0,432,410,290,0,154,314,58,178⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,37,152,112,352,193,402,282⟩,⟨7,14,37,152,112,352,193,384,264⟩,[⟨0,1531855678238856091536896,⟨398,398,446,184,504,504,506,384,264⟩⟩]⟩
theorem node97 : UpperPrefix a [2,3,5,7,6,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,8,0] 30 cert97 (by decide +kernel)

def cert98 : Leaf := ⟨⟨0,417,394,291,0,139,297,59,179⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,37,152,112,352,194,401,281⟩,⟨7,14,37,152,112,352,194,384,264⟩,[⟨4,1210110028751748478408171,⟨7,79,37,239,101,359,231,487,367⟩⟩]⟩
theorem node98 : UpperPrefix a [2,3,5,7,6,8,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,8,1] 30 cert98 (by decide +kernel)

def cert99 : Local := ⟨⟨0,433,410,0,0,155,0,59,179⟩,[(0,1),(3,6),(4,5),(6,3)],[(2,0,0),(6,4,4)]⟩
theorem node99 : UpperPrefix a [2,3,5,7,6,8,4] 30 :=
  local_sound a [2,3,5,7,6,8,4] 30 cert99 (by decide +kernel)

theorem node100 : UpperPrefix a [2,3,5,7,6,8] 30 :=
  branch_upper a [2,3,5,7,6,8] 30 (by decide) (fin9_cases _
  node97
  node98
  (invalid_upper a [2,3,5,7,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,3] 30 (by decide +kernel))
  node99
  (invalid_upper a [2,3,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,8] 30 (by decide +kernel)))

theorem node101 : UpperPrefix a [2,3,5,7,6] 30 :=
  branch_upper a [2,3,5,7,6] 30 (by decide) (fin9_cases _
  node94
  node95
  (invalid_upper a [2,3,5,7,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,3] 30 (by decide +kernel))
  node96
  (invalid_upper a [2,3,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,7] 30 (by decide +kernel))
  node100)

def cert102 : Local := ⟨⟨0,240,0,354,202,154,58,122,242⟩,[(0,1),(2,5)],[(2,0,0),(8,4,3),(0,5,2)]⟩
theorem node102 : UpperPrefix a [2,3,5,7,8,0] 30 :=
  local_sound a [2,3,5,7,8,0] 30 cert102 (by decide +kernel)

def cert103 : Leaf := ⟨⟨0,161,130,353,201,153,49,113,241⟩,[(0,1)],[(2,0,0),(8,4,3),(1,5,2)],⟨7,14,37,152,304,98,209,465,345⟩,⟨7,14,37,152,304,98,192,384,264⟩,[⟨3,1210255427466816453084195,⟨7,7,37,212,501,103,192,384,256⟩⟩,⟨4,1210107565282752187077675,⟨7,15,37,143,293,103,192,384,267⟩⟩,⟨6,1210106412362347091858475,⟨7,15,37,159,309,39,128,384,267⟩⟩]⟩
theorem node103 : UpperPrefix a [2,3,5,7,8,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,1] 30 cert103 (by decide +kernel)

def cert104 : Local := ⟨⟨0,241,208,353,193,129,50,121,241⟩,[(0,1)],[(2,0,0),(3,1,7),(8,4,3),(1,7,6)]⟩
theorem node104 : UpperPrefix a [2,3,5,7,8,4,0,1] 30 :=
  local_sound a [2,3,5,7,8,4,0,1] 30 cert104 (by decide +kernel)

def cert105 : Leaf := ⟨⟨0,112,90,354,74,10,58,58,114⟩,[(0,1)],[(2,0,0),(8,4,3)],⟨7,14,37,152,304,112,193,448,266⟩,⟨7,14,37,152,304,112,193,448,264⟩,[⟨0,1546281036054234785648128,⟨286,286,446,184,440,504,506,504,264⟩⟩,⟨7,1256150645256576081991067,⟨263,287,37,319,311,117,117,375,287⟩⟩]⟩
theorem node105 : UpperPrefix a [2,3,5,7,8,4,0,6] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,4,0,6] 30 cert105 (by decide +kernel)

theorem node106 : UpperPrefix a [2,3,5,7,8,4,0] 30 :=
  branch_upper a [2,3,5,7,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,8,4,0,0] 30 (by decide +kernel))
  node104
  (invalid_upper a [2,3,5,7,8,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,5] 30 (by decide +kernel))
  node105
  (invalid_upper a [2,3,5,7,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,8] 30 (by decide +kernel)))

def cert107 : Leaf := ⟨⟨0,209,218,321,201,137,25,88,209⟩,[(0,1)],[(2,0,0),(8,4,3)],⟨7,14,37,152,304,112,194,385,328⟩,⟨7,14,37,152,304,112,194,385,264⟩,[⟨1,1663491643386166336552961,⟨157,156,445,152,304,376,504,393,264⟩⟩,⟨5,1390212476022408847821831,⟨455,463,463,152,280,472,451,449,264⟩⟩]⟩
theorem node107 : UpperPrefix a [2,3,5,7,8,4,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,4,1,0] 30 cert107 (by decide +kernel)

def cert108 : Leaf := ⟨⟨0,81,90,323,75,11,25,27,83⟩,[(0,1)],[(2,0,0),(8,4,3)],⟨7,14,37,152,304,112,194,448,265⟩,⟨7,14,37,152,304,112,194,448,264⟩,[⟨5,1239096748570580200983559,⟨455,463,463,152,280,216,451,448,264⟩⟩,⟨7,1256150645260974128502235,⟨263,287,37,319,311,117,375,375,287⟩⟩]⟩
theorem node108 : UpperPrefix a [2,3,5,7,8,4,1,6] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,4,1,6] 30 cert108 (by decide +kernel)

theorem node109 : UpperPrefix a [2,3,5,7,8,4,1] 30 :=
  branch_upper a [2,3,5,7,8,4,1] 30 (by decide) (fin9_cases _
  node107
  (invalid_upper a [2,3,5,7,8,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,1,5] 30 (by decide +kernel))
  node108
  (invalid_upper a [2,3,5,7,8,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,1,8] 30 (by decide +kernel)))

theorem node110 : UpperPrefix a [2,3,5,7,8,4] 30 :=
  branch_upper a [2,3,5,7,8,4] 30 (by decide) (fin9_cases _
  node106
  node109
  (invalid_upper a [2,3,5,7,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,8] 30 (by decide +kernel)))

theorem node111 : UpperPrefix a [2,3,5,7,8] 30 :=
  branch_upper a [2,3,5,7,8] 30 (by decide) (fin9_cases _
  node102
  node103
  (invalid_upper a [2,3,5,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,3] 30 (by decide +kernel))
  node110
  (invalid_upper a [2,3,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,8] 30 (by decide +kernel)))

theorem node112 : UpperPrefix a [2,3,5,7] 30 :=
  branch_upper a [2,3,5,7] 30 (by decide) (fin9_cases _
  node89
  node93
  (invalid_upper a [2,3,5,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,5] 30 (by decide +kernel))
  node101
  (invalid_upper a [2,3,5,7,7] 30 (by decide +kernel))
  node111)

def cert113 : Local := ⟨⟨0,497,0,225,0,409,313,121,241⟩,[(0,1),(2,4),(4,2)],[(2,0,0),(1,5,2),(1,5,4)]⟩
theorem node113 : UpperPrefix a [2,3,5,8,0,1] 30 :=
  local_sound a [2,3,5,8,0,1] 30 cert113 (by decide +kernel)

def cert114 : Leaf := ⟨⟨0,497,0,227,0,394,314,122,242⟩,[(0,1),(2,4),(4,2)],[(2,0,0)],⟨7,14,37,280,49,112,194,450,458⟩,⟨7,14,37,280,49,112,192,384,264⟩,[⟨0,1219580022971847022740480,⟨454,462,228,312,240,112,192,384,264⟩⟩]⟩
theorem node114 : UpperPrefix a [2,3,5,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,0,4] 30 cert114 (by decide +kernel)

def cert115 : Local := ⟨⟨0,369,0,99,0,0,315,123,115⟩,[(0,1),(2,4),(4,2),(5,6)],[(2,0,0),(7,5,5)]⟩
theorem node115 : UpperPrefix a [2,3,5,8,0,7] 30 :=
  local_sound a [2,3,5,8,0,7] 30 cert115 (by decide +kernel)

theorem node116 : UpperPrefix a [2,3,5,8,0] 30 :=
  branch_upper a [2,3,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,8,0,0] 30 (by decide +kernel))
  node113
  (invalid_upper a [2,3,5,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,0,3] 30 (by decide +kernel))
  node114
  (invalid_upper a [2,3,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,0,6] 30 (by decide +kernel))
  node115
  (invalid_upper a [2,3,5,8,0,8] 30 (by decide +kernel)))

def cert117 : Leaf := ⟨⟨0,33,2,195,449,403,275,83,211⟩,[(0,1)],[(2,0,0)],⟨7,14,37,280,50,241,209,465,473⟩,⟨7,14,37,280,50,96,192,384,264⟩,[⟨3,1210181532756180431799315,⟨119,247,53,501,119,96,192,384,484⟩⟩,⟨5,1285813290066834078303235,⟨7,15,5,472,475,64,192,384,264⟩⟩,⟨4,1210107565282752178689051,⟨7,15,37,271,39,96,192,384,267⟩⟩,⟨6,1210106412362347083469851,⟨7,15,37,287,55,32,128,384,267⟩⟩,⟨7,1208926973663134279013403,⟨7,15,37,287,55,96,64,256,267⟩⟩,⟨8,1181745669222515610651,⟨7,15,37,31,55,96,192,128,11⟩⟩]⟩
theorem node117 : UpperPrefix a [2,3,5,8,1] 30 :=
  Boolean.leaf_sound a [2,3,5,8,1] 30 cert117 (by decide +kernel)

def cert118 : Local := ⟨⟨0,432,0,162,0,410,314,58,178⟩,[(0,1),(2,5),(4,5)],[(2,0,0),(6,4,4),(0,5,2)]⟩
theorem node118 : UpperPrefix a [2,3,5,8,6,0] 30 :=
  local_sound a [2,3,5,8,6,0] 30 cert118 (by decide +kernel)

def cert119 : Leaf := ⟨⟨0,417,394,161,0,409,313,57,177⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4),(1,5,2)],⟨7,14,37,280,112,98,209,401,409⟩,⟨7,14,37,280,112,98,192,384,264⟩,[⟨4,1210107565282752187077675,⟨7,15,37,271,101,103,192,384,267⟩⟩]⟩
theorem node119 : UpperPrefix a [2,3,5,8,6,1] 30 :=
  Boolean.leaf_sound a [2,3,5,8,6,1] 30 cert119 (by decide +kernel)

def cert120 : Local := ⟨⟨0,433,410,163,0,0,315,59,179⟩,[(0,1),(4,5),(5,4)],[(2,0,0),(6,4,4),(6,4,5)]⟩
theorem node120 : UpperPrefix a [2,3,5,8,6,4] 30 :=
  local_sound a [2,3,5,8,6,4] 30 cert120 (by decide +kernel)

def cert121 : Local := ⟨⟨0,305,282,35,0,0,315,59,51⟩,[(0,1),(4,5),(5,6)],[(2,0,0),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node121 : UpperPrefix a [2,3,5,8,6,7] 30 :=
  local_sound a [2,3,5,8,6,7] 30 cert121 (by decide +kernel)

theorem node122 : UpperPrefix a [2,3,5,8,6] 30 :=
  branch_upper a [2,3,5,8,6] 30 (by decide) (fin9_cases _
  node118
  node119
  (invalid_upper a [2,3,5,8,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,3] 30 (by decide +kernel))
  node120
  (invalid_upper a [2,3,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,6] 30 (by decide +kernel))
  node121
  (invalid_upper a [2,3,5,8,6,8] 30 (by decide +kernel)))

def cert123 : Leaf := ⟨⟨0,240,0,226,74,154,58,122,242⟩,[(0,1),(2,5)],[(2,0,0),(0,5,2)],⟨7,14,37,280,176,97,210,466,346⟩,⟨7,14,37,280,176,97,192,384,264⟩,[⟨8,1184058843775324263819,⟨7,15,37,63,245,117,245,247,15⟩⟩]⟩
theorem node123 : UpperPrefix a [2,3,5,8,7,0] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,0] 30 cert123 (by decide +kernel)

def cert124 : Leaf := ⟨⟨0,161,130,225,73,153,49,121,241⟩,[(0,1)],[(2,0,0),(1,5,2)],⟨7,14,37,280,176,98,209,465,345⟩,⟨7,14,37,280,176,98,192,384,264⟩,[⟨8,1184344540876753212843,⟨7,47,37,127,245,119,245,247,47⟩⟩,⟨3,1210107853514226776671267,⟨7,7,37,340,245,103,192,384,256⟩⟩,⟨4,1210107565282752187077675,⟨7,15,37,271,165,103,192,384,267⟩⟩,⟨6,1210106412362347091858475,⟨7,15,37,287,181,39,128,384,267⟩⟩]⟩
theorem node124 : UpperPrefix a [2,3,5,8,7,1] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,1] 30 cert124 (by decide +kernel)

def cert125 : Leaf := ⟨⟨0,113,90,99,75,139,11,75,67⟩,[(0,1)],[(2,0,0),(7,4,5)],⟨7,14,37,280,176,112,195,451,331⟩,⟨7,14,37,280,176,112,192,384,264⟩,[⟨8,1184058843775315875211,⟨7,15,37,63,245,116,245,247,15⟩⟩,⟨4,1219580022407797557691395,⟨455,463,229,264,160,96,192,384,264⟩⟩,⟨5,1219580021282997162476547,⟨455,463,197,280,144,80,192,384,264⟩⟩]⟩
theorem node125 : UpperPrefix a [2,3,5,8,7,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,4] 30 cert125 (by decide +kernel)

theorem node126 : UpperPrefix a [2,3,5,8,7] 30 :=
  branch_upper a [2,3,5,8,7] 30 (by decide) (fin9_cases _
  node123
  node124
  (invalid_upper a [2,3,5,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,3] 30 (by decide +kernel))
  node125
  (invalid_upper a [2,3,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,8] 30 (by decide +kernel)))

theorem node127 : UpperPrefix a [2,3,5,8] 30 :=
  branch_upper a [2,3,5,8] 30 (by decide) (fin9_cases _
  node116
  node117
  (invalid_upper a [2,3,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,5] 30 (by decide +kernel))
  node122
  node126
  (invalid_upper a [2,3,5,8,8] 30 (by decide +kernel)))

#print axioms node127
end Delivery.FiniteExclusion.Sharp3x6
