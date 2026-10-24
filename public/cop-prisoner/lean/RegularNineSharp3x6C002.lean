import RegularNineSharp3x6Base
import RegularNineSharp3x6C000
import RegularNineSharp3x6C001
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node128 : UpperPrefix a [2,3,5] 30 :=
  branch_upper a [2,3,5] 30 (by decide) (fin9_cases _
  node51
  node64
  (invalid_upper a [2,3,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,5] 30 (by decide +kernel))
  node85
  node112
  node127)

def cert129 : Leaf := ⟨⟨0,113,56,98,72,408,312,120,240⟩,[(0,1)],[(2,0,0),(0,3,1),(1,4,3)],⟨7,14,69,25,50,496,496,432,440⟩,⟨7,14,69,25,50,96,192,384,264⟩,[⟨7,1208926973665339748934707,⟨7,15,69,27,63,127,64,256,264⟩⟩,⟨8,1181745671427985531955,⟨7,15,69,27,63,127,192,128,8⟩⟩]⟩
theorem node129 : UpperPrefix a [2,3,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,0,1] 30 cert129 (by decide +kernel)

def cert130 : Leaf := ⟨⟨0,113,58,34,10,152,314,58,50⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,69,25,176,98,496,432,312⟩,⟨7,14,69,25,176,98,192,384,264⟩,[⟨8,1181748066173454446199,⟨47,47,127,27,191,127,255,128,8⟩⟩,⟨6,1437222725400062396990467,⟨7,15,5,409,440,443,128,384,264⟩⟩,⟨7,1284484837389050754114611,⟨7,15,69,283,319,103,64,256,264⟩⟩]⟩
theorem node130 : UpperPrefix a [2,3,6,0,7,1] 30 :=
  Boolean.leaf_sound a [2,3,6,0,7,1] 30 cert130 (by decide +kernel)

def cert131 : Leaf := ⟨⟨0,113,58,96,72,136,314,122,114⟩,[(0,1)],[(2,0,0),(0,3,1),(7,4,5)],⟨7,14,69,25,176,112,482,418,298⟩,⟨7,14,69,25,176,112,192,384,264⟩,[⟨8,1181748066173454446199,⟨47,47,127,27,191,127,255,128,8⟩⟩,⟨1,1210107567680787571539969,⟨45,44,125,25,176,112,240,384,264⟩⟩]⟩
theorem node131 : UpperPrefix a [2,3,6,0,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,0,7,4] 30 cert131 (by decide +kernel)

def cert132 : Local := ⟨⟨0,241,186,224,328,152,56,120,240⟩,[(0,1)],[(2,0,0),(0,3,1),(8,5,4),(1,6,2)]⟩
theorem node132 : UpperPrefix a [2,3,6,0,7,8,1] 30 :=
  local_sound a [2,3,6,0,7,8,1] 30 cert132 (by decide +kernel)

def cert133 : Local := ⟨⟨0,113,58,98,330,26,0,122,114⟩,[(0,1),(6,4)],[(2,0,0),(0,3,1),(7,4,6),(8,5,4)]⟩
theorem node133 : UpperPrefix a [2,3,6,0,7,8,4] 30 :=
  local_sound a [2,3,6,0,7,8,4] 30 cert133 (by decide +kernel)

def cert134 : Local := ⟨⟨0,241,186,226,0,154,0,122,242⟩,[(0,1),(4,6),(6,4)],[(2,0,0),(0,3,1),(8,5,4),(8,5,6)]⟩
theorem node134 : UpperPrefix a [2,3,6,0,7,8,5] 30 :=
  local_sound a [2,3,6,0,7,8,5] 30 cert134 (by decide +kernel)

theorem node135 : UpperPrefix a [2,3,6,0,7,8] 30 :=
  branch_upper a [2,3,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,7,8,0] 30 (by decide +kernel))
  node132
  (invalid_upper a [2,3,6,0,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,8,3] 30 (by decide +kernel))
  node133
  node134
  (invalid_upper a [2,3,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,8,8] 30 (by decide +kernel)))

theorem node136 : UpperPrefix a [2,3,6,0,7] 30 :=
  branch_upper a [2,3,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,7,0] 30 (by decide +kernel))
  node130
  (invalid_upper a [2,3,6,0,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,3] 30 (by decide +kernel))
  node131
  (invalid_upper a [2,3,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,7] 30 (by decide +kernel))
  node135)

def cert137 : Leaf := ⟨⟨0,497,432,418,138,408,304,48,178⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,69,25,304,98,240,432,440⟩,⟨7,14,69,25,304,98,192,384,264⟩,[⟨6,1437222725400062396990467,⟨7,15,5,409,440,443,128,384,264⟩⟩,⟨1,1210255427466817516339201,⟨5,12,69,221,496,96,192,384,268⟩⟩,⟨3,1210255427466816455181347,⟨7,7,69,213,501,103,192,384,260⟩⟩]⟩
theorem node137 : UpperPrefix a [2,3,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,6,0,8,1] 30 cert137 (by decide +kernel)

def cert138 : Leaf := ⟨⟨0,321,266,322,202,394,298,106,242⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,69,25,304,112,226,418,426⟩,⟨7,14,69,25,304,112,192,384,264⟩,[⟨4,1210255427465718017430811,⟨7,15,69,207,487,229,192,387,271⟩⟩,⟨5,1210107564157958230139955,⟨7,15,69,27,287,95,192,384,264⟩⟩,⟨7,1208926973663140725679155,⟨7,15,69,27,319,127,64,256,264⟩⟩]⟩
theorem node138 : UpperPrefix a [2,3,6,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,0,8,4] 30 cert138 (by decide +kernel)

def cert139 : Local := ⟨⟨0,369,314,352,72,0,312,120,112⟩,[(0,1),(5,6)],[(2,0,0),(0,3,1),(7,5,5),(1,6,2)]⟩
theorem node139 : UpperPrefix a [2,3,6,0,8,7,1] 30 :=
  local_sound a [2,3,6,0,8,7,1] 30 cert139 (by decide +kernel)

def cert140 : Local := ⟨⟨0,113,58,98,74,0,298,122,114⟩,[(0,1),(5,6)],[(2,0,0),(0,3,1),(8,4,6),(7,5,5)]⟩
theorem node140 : UpperPrefix a [2,3,6,0,8,7,4] 30 :=
  local_sound a [2,3,6,0,8,7,4] 30 cert140 (by decide +kernel)

def cert141 : Local := ⟨⟨0,369,314,354,74,0,0,122,114⟩,[(0,1),(5,6),(6,5)],[(2,0,0),(0,3,1),(7,5,5),(7,5,6)]⟩
theorem node141 : UpperPrefix a [2,3,6,0,8,7,5] 30 :=
  local_sound a [2,3,6,0,8,7,5] 30 cert141 (by decide +kernel)

theorem node142 : UpperPrefix a [2,3,6,0,8,7] 30 :=
  branch_upper a [2,3,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,8,7,0] 30 (by decide +kernel))
  node139
  (invalid_upper a [2,3,6,0,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,7,3] 30 (by decide +kernel))
  node140
  node141
  (invalid_upper a [2,3,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,7,8] 30 (by decide +kernel)))

theorem node143 : UpperPrefix a [2,3,6,0,8] 30 :=
  branch_upper a [2,3,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,8,0] 30 (by decide +kernel))
  node137
  (invalid_upper a [2,3,6,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,3] 30 (by decide +kernel))
  node138
  (invalid_upper a [2,3,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,6] 30 (by decide +kernel))
  node142
  (invalid_upper a [2,3,6,0,8,8] 30 (by decide +kernel)))

theorem node144 : UpperPrefix a [2,3,6,0] 30 :=
  branch_upper a [2,3,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,0] 30 (by decide +kernel))
  node129
  (invalid_upper a [2,3,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,6] 30 (by decide +kernel))
  node136
  node143)

def cert145 : Leaf := ⟨⟨0,113,56,97,72,408,312,120,240⟩,[(0,1)],[(2,0,0)],⟨7,14,69,26,49,496,496,432,440⟩,⟨7,14,69,26,49,96,192,384,264⟩,[⟨1,1257432885750708839907329,⟨501,508,245,508,245,96,192,384,488⟩⟩,⟨0,1247960428519766738600960,⟨6,494,68,506,48,96,192,384,488⟩⟩,⟨7,1208926973665339748934707,⟨7,15,69,27,63,127,64,256,264⟩⟩,⟨8,1181745671427985531955,⟨7,15,69,27,63,127,192,128,8⟩⟩]⟩
theorem node145 : UpperPrefix a [2,3,6,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,1,0] 30 cert145 (by decide +kernel)

def cert146 : Leaf := ⟨⟨0,497,0,481,329,0,313,121,241⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,14,69,26,176,97,496,432,312⟩,⟨7,14,69,26,176,97,192,384,264⟩,[⟨1,1219580022587498998005761,⟨501,508,245,472,180,245,192,384,264⟩⟩]⟩
theorem node146 : UpperPrefix a [2,3,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,3,6,1,7,0] 30 cert146 (by decide +kernel)

def cert147 : Leaf := ⟨⟨0,80,26,64,74,138,315,123,115⟩,[(0,1)],[(2,0,0),(7,4,5)],⟨7,14,69,26,176,112,481,417,297⟩,⟨7,14,69,26,176,112,192,384,264⟩,[⟨8,1181748066173454446199,⟨47,47,127,27,191,127,255,128,8⟩⟩,⟨0,1210107567680787571543552,⟨46,46,126,26,176,112,240,384,264⟩⟩,⟨5,1210107564157958230139955,⟨7,15,69,27,159,95,192,384,264⟩⟩]⟩
theorem node147 : UpperPrefix a [2,3,6,1,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,1,7,4] 30 cert147 (by decide +kernel)

def cert148 : Local := ⟨⟨0,240,0,224,330,154,58,122,242⟩,[(0,1),(2,6)],[(2,0,0),(8,5,4),(0,6,2)]⟩
theorem node148 : UpperPrefix a [2,3,6,1,7,8,0] 30 :=
  local_sound a [2,3,6,1,7,8,0] 30 cert148 (by decide +kernel)

def cert149 : Leaf := ⟨⟨0,112,58,96,330,26,0,123,115⟩,[(0,1),(6,4)],[(2,0,0),(7,4,6),(8,5,4)],⟨7,14,69,26,176,352,208,417,297⟩,⟨7,14,69,26,176,352,208,384,264⟩,[⟨0,1210110163874031355301376,⟨14,14,94,90,240,368,240,496,264⟩⟩]⟩
theorem node149 : UpperPrefix a [2,3,6,1,7,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,1,7,8,4] 30 cert149 (by decide +kernel)

def cert150 : Leaf := ⟨⟨0,177,186,161,0,155,0,59,179⟩,[(0,1),(4,6),(6,4)],[(2,0,0),(8,5,4),(8,5,6)],⟨7,14,69,26,176,352,224,401,281⟩,⟨7,14,69,26,176,352,224,384,264⟩,[⟨6,1266885490625623662530055,⟨399,399,415,411,176,304,176,384,392⟩⟩]⟩
theorem node150 : UpperPrefix a [2,3,6,1,7,8,5] 30 :=
  Boolean.leaf_sound a [2,3,6,1,7,8,5] 30 cert150 (by decide +kernel)

theorem node151 : UpperPrefix a [2,3,6,1,7,8] 30 :=
  branch_upper a [2,3,6,1,7,8] 30 (by decide) (fin9_cases _
  node148
  (invalid_upper a [2,3,6,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,3] 30 (by decide +kernel))
  node149
  node150
  (invalid_upper a [2,3,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,8] 30 (by decide +kernel)))

theorem node152 : UpperPrefix a [2,3,6,1,7] 30 :=
  branch_upper a [2,3,6,1,7] 30 (by decide) (fin9_cases _
  node146
  (invalid_upper a [2,3,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,3] 30 (by decide +kernel))
  node147
  (invalid_upper a [2,3,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,7] 30 (by decide +kernel))
  node151)

def cert153 : Leaf := ⟨⟨0,497,0,481,201,0,313,121,241⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,14,69,26,304,97,240,432,440⟩,⟨7,14,69,26,304,97,192,384,264⟩,[⟨1,1219728533286337266319361,⟨501,508,245,472,500,245,192,384,264⟩⟩]⟩
theorem node153 : UpperPrefix a [2,3,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,0] 30 cert153 (by decide +kernel)

def cert154 : Leaf := ⟨⟨0,496,0,480,200,392,312,120,240⟩,[(0,1),(2,6)],[(2,0,0),(0,6,2)],⟨7,14,69,26,304,112,193,416,424⟩,⟨7,14,69,26,304,112,193,384,264⟩,[⟨1,1257580353728382114201601,⟨501,508,245,440,432,244,245,384,408⟩⟩]⟩
theorem node154 : UpperPrefix a [2,3,6,1,8,4,0] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,4,0] 30 cert154 (by decide +kernel)

def cert155 : Leaf := ⟨⟨0,449,386,449,195,387,259,67,195⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,69,26,304,112,224,385,393⟩,⟨7,14,69,26,304,112,224,384,264⟩,[⟨3,1212475970918101201978379,⟨7,39,101,119,500,112,240,500,501⟩⟩,⟨4,1259942309089006998131995,⟨391,399,197,463,487,229,228,387,399⟩⟩]⟩
theorem node155 : UpperPrefix a [2,3,6,1,8,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,4,5] 30 cert155 (by decide +kernel)

theorem node156 : UpperPrefix a [2,3,6,1,8,4] 30 :=
  branch_upper a [2,3,6,1,8,4] 30 (by decide) (fin9_cases _
  node154
  (invalid_upper a [2,3,6,1,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,4,4] 30 (by decide +kernel))
  node155
  (invalid_upper a [2,3,6,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,4,8] 30 (by decide +kernel)))

def cert157 : Local := ⟨⟨0,368,0,352,74,0,314,122,114⟩,[(0,1),(2,6),(5,6)],[(2,0,0),(7,5,5),(0,6,2)]⟩
theorem node157 : UpperPrefix a [2,3,6,1,8,7,0] 30 :=
  local_sound a [2,3,6,1,8,7,0] 30 cert157 (by decide +kernel)

def cert158 : Leaf := ⟨⟨0,113,50,97,67,0,291,115,115⟩,[(0,1),(5,6)],[(2,0,0),(8,4,6),(7,5,5)],⟨7,14,69,26,304,224,208,417,297⟩,⟨7,14,69,26,304,224,208,384,264⟩,[⟨3,1212476547097378528691211,⟨7,7,101,119,500,240,240,500,501⟩⟩]⟩
theorem node158 : UpperPrefix a [2,3,6,1,8,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,7,4] 30 cert158 (by decide +kernel)

def cert159 : Local := ⟨⟨0,369,314,353,75,0,0,123,115⟩,[(0,1),(5,6),(6,5)],[(2,0,0),(7,5,5),(7,5,6)]⟩
theorem node159 : UpperPrefix a [2,3,6,1,8,7,5] 30 :=
  local_sound a [2,3,6,1,8,7,5] 30 cert159 (by decide +kernel)

theorem node160 : UpperPrefix a [2,3,6,1,8,7] 30 :=
  branch_upper a [2,3,6,1,8,7] 30 (by decide) (fin9_cases _
  node157
  (invalid_upper a [2,3,6,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,3] 30 (by decide +kernel))
  node158
  node159
  (invalid_upper a [2,3,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,8] 30 (by decide +kernel)))

theorem node161 : UpperPrefix a [2,3,6,1,8] 30 :=
  branch_upper a [2,3,6,1,8] 30 (by decide) (fin9_cases _
  node153
  (invalid_upper a [2,3,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,3] 30 (by decide +kernel))
  node156
  (invalid_upper a [2,3,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,6] 30 (by decide +kernel))
  node160
  (invalid_upper a [2,3,6,1,8,8] 30 (by decide +kernel)))

theorem node162 : UpperPrefix a [2,3,6,1] 30 :=
  branch_upper a [2,3,6,1] 30 (by decide) (fin9_cases _
  node145
  (invalid_upper a [2,3,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,6] 30 (by decide +kernel))
  node152
  node161)

def cert163 : Leaf := ⟨⟨0,81,26,0,74,411,283,91,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,49,498,466,402,410⟩,⟨7,14,69,56,49,96,192,384,264⟩,[⟨7,1208926973665889504752699,⟨7,31,69,63,63,127,64,256,283⟩⟩,⟨8,1181745671977741349947,⟨7,31,69,63,63,127,192,128,27⟩⟩]⟩
theorem node163 : UpperPrefix a [2,3,6,5,0] 30 :=
  Boolean.leaf_sound a [2,3,6,5,0] 30 cert163 (by decide +kernel)

def cert164 : Leaf := ⟨⟨0,81,26,0,73,411,283,91,211⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,50,497,465,401,409⟩,⟨7,14,69,56,50,96,192,384,264⟩,[⟨7,1208926973665889504752699,⟨7,31,69,63,63,127,64,256,283⟩⟩,⟨8,1181745671977741349947,⟨7,31,69,63,63,127,192,128,27⟩⟩]⟩
theorem node164 : UpperPrefix a [2,3,6,5,1] 30 :=
  Boolean.leaf_sound a [2,3,6,5,1] 30 cert164 (by decide +kernel)

def cert165 : Local := ⟨⟨0,465,0,0,331,0,283,91,211⟩,[(0,1),(2,5),(3,4),(5,2)],[(2,0,0),(5,3,3)]⟩
theorem node165 : UpperPrefix a [2,3,6,5,7,0] 30 :=
  local_sound a [2,3,6,5,7,0] 30 cert165 (by decide +kernel)

def cert166 : Leaf := ⟨⟨0,209,154,0,11,153,283,27,147⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,176,98,465,401,281⟩,⟨7,14,69,56,176,98,192,384,264⟩,[⟨8,1181748066173454450303,⟨47,47,127,63,191,127,255,128,11⟩⟩,⟨6,1370980467431923300434947,⟨391,415,5,440,440,443,128,384,280⟩⟩]⟩
theorem node166 : UpperPrefix a [2,3,6,5,7,1] 30 :=
  Boolean.leaf_sound a [2,3,6,5,7,1] 30 cert166 (by decide +kernel)

def cert167 : Local := ⟨⟨0,321,266,0,331,395,267,75,67⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(7,4,5),(4,5,3)]⟩
theorem node167 : UpperPrefix a [2,3,6,5,7,4] 30 :=
  local_sound a [2,3,6,5,7,4] 30 cert167 (by decide +kernel)

def cert168 : Local := ⟨⟨0,208,0,0,330,154,26,90,210⟩,[(0,1),(2,6),(3,4)],[(2,0,0),(5,3,3),(8,5,4),(0,6,2)]⟩
theorem node168 : UpperPrefix a [2,3,6,5,7,8,0] 30 :=
  local_sound a [2,3,6,5,7,8,0] 30 cert168 (by decide +kernel)

def cert169 : Local := ⟨⟨0,209,154,0,329,153,25,89,209⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(8,5,4),(1,6,2)]⟩
theorem node169 : UpperPrefix a [2,3,6,5,7,8,1] 30 :=
  local_sound a [2,3,6,5,7,8,1] 30 cert169 (by decide +kernel)

def cert170 : Local := ⟨⟨0,81,26,0,331,27,0,91,83⟩,[(0,1),(3,4),(6,4)],[(2,0,0),(5,3,3),(7,4,6),(8,5,4)]⟩
theorem node170 : UpperPrefix a [2,3,6,5,7,8,4] 30 :=
  local_sound a [2,3,6,5,7,8,4] 30 cert170 (by decide +kernel)

theorem node171 : UpperPrefix a [2,3,6,5,7,8] 30 :=
  branch_upper a [2,3,6,5,7,8] 30 (by decide) (fin9_cases _
  node168
  node169
  (invalid_upper a [2,3,6,5,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,8,3] 30 (by decide +kernel))
  node170
  (invalid_upper a [2,3,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,8,8] 30 (by decide +kernel)))

theorem node172 : UpperPrefix a [2,3,6,5,7] 30 :=
  branch_upper a [2,3,6,5,7] 30 (by decide) (fin9_cases _
  node165
  node166
  (invalid_upper a [2,3,6,5,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,3] 30 (by decide +kernel))
  node167
  (invalid_upper a [2,3,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,7] 30 (by decide +kernel))
  node171)

def cert173 : Local := ⟨⟨0,465,0,0,203,0,283,91,211⟩,[(0,1),(2,5),(3,4),(5,2)],[(2,0,0),(5,3,3)]⟩
theorem node173 : UpperPrefix a [2,3,6,5,8,0] 30 :=
  local_sound a [2,3,6,5,8,0] 30 cert173 (by decide +kernel)

def cert174 : Leaf := ⟨⟨0,465,402,0,139,401,275,19,147⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,304,98,209,401,409⟩,⟨7,14,69,56,304,98,192,384,264⟩,[⟨3,1210255571652373275739171,⟨39,103,69,245,501,103,192,384,324⟩⟩,⟨6,1370980467431923300434947,⟨391,415,5,440,440,443,128,384,280⟩⟩]⟩
theorem node174 : UpperPrefix a [2,3,6,5,8,1] 30 :=
  Boolean.leaf_sound a [2,3,6,5,8,1] 30 cert174 (by decide +kernel)

def cert175 : Local := ⟨⟨0,449,394,0,203,395,267,75,195⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(4,5,3)]⟩
theorem node175 : UpperPrefix a [2,3,6,5,8,4] 30 :=
  local_sound a [2,3,6,5,8,4] 30 cert175 (by decide +kernel)

def cert176 : Local := ⟨⟨0,337,282,0,75,0,283,91,83⟩,[(0,1),(3,4),(5,6)],[(2,0,0),(5,3,3),(7,5,5)]⟩
theorem node176 : UpperPrefix a [2,3,6,5,8,7] 30 :=
  local_sound a [2,3,6,5,8,7] 30 cert176 (by decide +kernel)

theorem node177 : UpperPrefix a [2,3,6,5,8] 30 :=
  branch_upper a [2,3,6,5,8] 30 (by decide) (fin9_cases _
  node173
  node174
  (invalid_upper a [2,3,6,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,8,3] 30 (by decide +kernel))
  node175
  (invalid_upper a [2,3,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,8,6] 30 (by decide +kernel))
  node176
  (invalid_upper a [2,3,6,5,8,8] 30 (by decide +kernel)))

theorem node178 : UpperPrefix a [2,3,6,5] 30 :=
  branch_upper a [2,3,6,5] 30 (by decide) (fin9_cases _
  node163
  node164
  (invalid_upper a [2,3,6,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,6] 30 (by decide +kernel))
  node172
  node177)

def cert179 : Leaf := ⟨⟨0,241,184,32,138,153,312,56,176⟩,[(0,1)],[(2,0,0),(1,5,4)],⟨7,14,69,152,49,98,496,432,312⟩,⟨7,14,69,152,49,98,192,384,264⟩,[⟨8,1181748068846534708343,⟨55,63,127,153,55,127,255,128,8⟩⟩,⟨0,1285813291192733985145856,⟨6,14,68,472,504,98,192,384,264⟩⟩,⟨6,1437222725400064544474115,⟨7,15,5,408,441,443,128,384,264⟩⟩]⟩
theorem node179 : UpperPrefix a [2,3,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,1] 30 cert179 (by decide +kernel)

def cert180 : Leaf := ⟨⟨0,241,58,97,72,9,57,121,113⟩,[(0,1)],[(2,0,0),(1,6,2)],⟨7,14,69,152,49,112,194,416,296⟩,⟨7,14,69,152,49,112,194,384,264⟩,[⟨8,1184211916641745493503,⟨55,127,127,255,55,127,255,255,127⟩⟩,⟨7,1218371709028488998552643,⟨311,319,117,24,53,117,375,256,264⟩⟩]⟩
theorem node180 : UpperPrefix a [2,3,6,7,0,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,4,1] 30 cert180 (by decide +kernel)

def cert181 : Leaf := ⟨⟨0,209,154,66,202,138,26,90,210⟩,[(0,1)],[(2,0,0),(5,6,5)],⟨7,14,69,152,49,112,224,386,266⟩,⟨7,14,69,152,49,112,224,384,264⟩,[⟨8,1184211916641745493503,⟨55,127,127,255,55,127,255,255,127⟩⟩,⟨0,1219580437584489865020416,⟨454,494,196,248,248,120,224,384,360⟩⟩]⟩
theorem node181 : UpperPrefix a [2,3,6,7,0,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,4,5] 30 cert181 (by decide +kernel)

def cert182 : Leaf := ⟨⟨0,241,186,99,74,10,0,122,114⟩,[(0,1),(6,7)],[(2,0,0),(8,6,6)],⟨7,14,69,152,49,112,448,418,298⟩,⟨7,14,69,152,49,112,448,384,264⟩,[⟨0,1219573105724294358369280,⟨454,494,68,248,112,112,448,448,296⟩⟩,⟨7,1218371706770092089934851,⟨311,319,117,24,49,112,320,256,264⟩⟩]⟩
theorem node182 : UpperPrefix a [2,3,6,7,0,4,8] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,4,8] 30 cert182 (by decide +kernel)

theorem node183 : UpperPrefix a [2,3,6,7,0,4] 30 :=
  branch_upper a [2,3,6,7,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,4,0] 30 (by decide +kernel))
  node180
  (invalid_upper a [2,3,6,7,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,4,4] 30 (by decide +kernel))
  node181
  (invalid_upper a [2,3,6,7,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,4,7] 30 (by decide +kernel))
  node182)

def cert184 : Leaf := ⟨⟨0,225,170,352,200,137,41,120,240⟩,[(0,1)],[(2,0,0),(1,6,2)],⟨7,14,69,152,49,352,194,432,312⟩,⟨7,14,69,152,49,352,194,384,264⟩,[⟨4,1210110028751748474738155,⟨7,79,69,239,37,359,231,487,367⟩⟩,⟨8,1184195629618952803819,⟨7,79,69,223,53,119,199,199,79⟩⟩,⟨0,1285813002962357833434112,⟨6,14,68,408,440,352,194,384,264⟩⟩]⟩
theorem node184 : UpperPrefix a [2,3,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,1] 30 cert184 (by decide +kernel)

def cert185 : Leaf := ⟨⟨0,496,442,0,458,154,0,122,242⟩,[(0,1),(3,6),(6,3)],[(2,0,0)],⟨7,14,69,152,49,352,208,418,298⟩,⟨7,14,69,152,49,352,208,384,264⟩,[⟨0,1238506769349207993093120,⟨422,494,494,216,248,360,216,416,360⟩⟩]⟩
theorem node185 : UpperPrefix a [2,3,6,7,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,4] 30 cert185 (by decide +kernel)

def cert186 : Leaf := ⟨⟨0,225,162,99,202,128,256,123,243⟩,[(0,1)],[(2,0,0),(8,5,6)],⟨7,14,69,152,49,352,224,402,282⟩,⟨7,14,69,152,49,352,224,384,264⟩,[⟨4,1210110028751748474738091,⟨7,79,69,239,37,359,229,487,367⟩⟩,⟨3,1210110028752846784562179,⟨7,71,69,240,49,352,224,480,352⟩⟩,⟨0,1210110028752847857779712,⟨6,78,68,248,48,352,224,480,360⟩⟩,⟨1,1210110028752847857778689,⟨5,76,69,248,49,352,224,480,360⟩⟩]⟩
theorem node186 : UpperPrefix a [2,3,6,7,0,8,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,5] 30 cert186 (by decide +kernel)

theorem node187 : UpperPrefix a [2,3,6,7,0,8] 30 :=
  branch_upper a [2,3,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,8,0] 30 (by decide +kernel))
  node184
  (invalid_upper a [2,3,6,7,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,3] 30 (by decide +kernel))
  node185
  node186
  (invalid_upper a [2,3,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,8] 30 (by decide +kernel)))

theorem node188 : UpperPrefix a [2,3,6,7,0] 30 :=
  branch_upper a [2,3,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,0] 30 (by decide +kernel))
  node179
  (invalid_upper a [2,3,6,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,3] 30 (by decide +kernel))
  node183
  (invalid_upper a [2,3,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,7] 30 (by decide +kernel))
  node187)

def cert189 : Leaf := ⟨⟨0,497,0,354,457,0,314,122,242⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,14,69,152,50,97,496,432,312⟩,⟨7,14,69,152,50,97,192,384,264⟩,[⟨0,1285813291192733985145856,⟨6,14,68,472,506,96,192,384,264⟩⟩]⟩
theorem node189 : UpperPrefix a [2,3,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,0] 30 cert189 (by decide +kernel)

def cert190 : Leaf := ⟨⟨0,241,50,35,65,3,315,59,51⟩,[(0,1)],[(2,0,0)],⟨7,14,69,152,50,112,481,417,297⟩,⟨7,14,69,152,50,112,192,384,264⟩,[⟨8,1181748068846534708343,⟨55,63,127,153,55,127,255,128,8⟩⟩,⟨7,1218371706769817220416531,⟨311,319,117,25,311,117,64,256,264⟩⟩,⟨3,1210107565424794267550739,⟨55,55,117,145,55,117,192,384,256⟩⟩,⟨6,1285811850040857521554435,⟨7,15,5,408,443,440,128,384,264⟩⟩]⟩
theorem node190 : UpperPrefix a [2,3,6,7,1,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,4] 30 cert190 (by decide +kernel)

def cert191 : Leaf := ⟨⟨0,496,0,352,456,154,314,120,240⟩,[(0,1),(2,6)],[(2,0,0),(0,6,2)],⟨7,14,69,152,50,352,193,432,312⟩,⟨7,14,69,152,50,352,193,384,264⟩,[⟨1,1285813002962357850210305,⟨5,12,69,408,440,356,197,384,264⟩⟩]⟩
theorem node191 : UpperPrefix a [2,3,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8,0] 30 cert191 (by decide +kernel)

#print axioms node191
end Delivery.FiniteExclusion.Sharp3x6
