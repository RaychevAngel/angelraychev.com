import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C001
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert128 : Leaf := ⟨⟨0,449,465,336,193,400,273,81,225⟩,[(0,1)],[(2,0,0),(1,2,0)],⟨7,22,14,137,304,97,224,392,336⟩,⟨7,22,14,137,304,97,224,392,272⟩,[⟨3,2324588505637920592367111,⟨311,311,375,499,304,371,496,496,272⟩⟩,⟨5,1212616321352038929540503,⟨15,159,15,141,415,77,205,399,415⟩⟩]⟩
theorem node128 : UpperPrefix a [2,4,1,7,8,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,0,5,3] 30 cert128 (by decide +kernel)

def cert129 : Leaf := ⟨⟨0,425,417,288,137,392,265,41,169⟩,[(0,1)],[(2,0,0),(1,2,0),(6,7,6)],⟨7,22,14,137,304,97,224,448,280⟩,⟨7,22,14,137,304,97,224,448,272⟩,[⟨4,1212616791378903770596359,⟨111,239,111,237,480,101,224,448,448⟩⟩]⟩
theorem node129 : UpperPrefix a [2,4,1,7,8,0,5,6] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,0,5,6] 30 cert129 (by decide +kernel)

theorem node130 : UpperPrefix a [2,4,1,7,8,0,5] 30 :=
  branch_upper a [2,4,1,7,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,7,8,0,5,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,5,2] 30 (by decide +kernel))
  node128
  (invalid_upper a [2,4,1,7,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,5,5] 30 (by decide +kernel))
  node129
  (invalid_upper a [2,4,1,7,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,5,8] 30 (by decide +kernel)))

theorem node131 : UpperPrefix a [2,4,1,7,8,0] 30 :=
  branch_upper a [2,4,1,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,7,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,2] 30 (by decide +kernel))
  node127
  (invalid_upper a [2,4,1,7,8,0,4] 30 (by decide +kernel))
  node130
  (invalid_upper a [2,4,1,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,0,8] 30 (by decide +kernel)))

def cert132 : Local := ⟨⟨0,360,368,0,72,401,0,120,104⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(1,2,0),(7,3,5),(0,6,5)]⟩
theorem node132 : UpperPrefix a [2,4,1,7,8,3,0] 30 :=
  local_sound a [2,4,1,7,8,3,0] 30 cert132 (by decide +kernel)

def cert133 : Leaf := ⟨⟨0,361,369,368,73,384,264,121,105⟩,[(0,1)],[(2,0,0),(1,2,0),(7,3,5)],⟨7,22,14,137,304,104,224,449,337⟩,⟨7,22,14,137,304,104,224,384,272⟩,[⟨0,1210107709821252227040256,⟨38,54,110,232,304,104,224,384,272⟩⟩,⟨4,1210107709820152715412487,⟨39,39,111,233,288,104,224,384,256⟩⟩]⟩
theorem node133 : UpperPrefix a [2,4,1,7,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,3,5] 30 cert133 (by decide +kernel)

theorem node134 : UpperPrefix a [2,4,1,7,8,3] 30 :=
  branch_upper a [2,4,1,7,8,3] 30 (by decide) (fin9_cases _
  node132
  (invalid_upper a [2,4,1,7,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,4] 30 (by decide +kernel))
  node133
  (invalid_upper a [2,4,1,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,3,8] 30 (by decide +kernel)))

theorem node135 : UpperPrefix a [2,4,1,7,8] 30 :=
  branch_upper a [2,4,1,7,8] 30 (by decide) (fin9_cases _
  node131
  (invalid_upper a [2,4,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,2] 30 (by decide +kernel))
  node134
  (invalid_upper a [2,4,1,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,8] 30 (by decide +kernel)))

theorem node136 : UpperPrefix a [2,4,1,7] 30 :=
  branch_upper a [2,4,1,7] 30 (by decide) (fin9_cases _
  node124
  (invalid_upper a [2,4,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,2] 30 (by decide +kernel))
  node125
  (invalid_upper a [2,4,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,5] 30 (by decide +kernel))
  node126
  (invalid_upper a [2,4,1,7,7] 30 (by decide +kernel))
  node135)

def cert137 : Leaf := ⟨⟨0,265,273,16,457,393,297,105,233⟩,[(0,1)],[(2,0,0),(1,2,0)],⟨7,22,14,265,249,233,233,489,505⟩,⟨7,22,14,265,48,96,192,384,272⟩,[⟨4,1210181568854041591546887,⟨103,103,239,489,32,96,192,384,256⟩⟩,⟨5,1210107564158003421775247,⟨7,23,15,271,16,64,205,399,287⟩⟩,⟨6,1210106412362398721770895,⟨7,23,15,271,48,32,141,399,287⟩⟩,⟨7,1208926973663185917314447,⟨7,23,15,271,48,96,77,271,287⟩⟩]⟩
theorem node137 : UpperPrefix a [2,4,1,8] 30 :=
  Boolean.leaf_sound a [2,4,1,8] 30 cert137 (by decide +kernel)

theorem node138 : UpperPrefix a [2,4,1] 30 :=
  branch_upper a [2,4,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,4] 30 (by decide +kernel))
  node105
  node119
  node136
  node137)

def cert139 : Leaf := ⟨⟨0,41,83,18,10,411,283,27,139⟩,[(0,1)],[(2,0,0),(5,2,1),(6,3,2)],⟨7,22,44,73,49,490,458,394,410⟩,⟨7,22,44,73,49,96,192,384,272⟩,[⟨7,1208926973665612483686199,⟨23,23,63,75,63,127,64,259,279⟩⟩,⟨8,1181745671700720283447,⟨23,23,63,75,63,127,192,131,23⟩⟩]⟩
theorem node139 : UpperPrefix a [2,4,5,6,0] 30 :=
  Boolean.leaf_sound a [2,4,5,6,0] 30 cert139 (by decide +kernel)

def cert140 : Leaf := ⟨⟨0,41,83,18,9,411,283,27,139⟩,[(0,1)],[(2,0,0),(5,2,1),(6,3,2)],⟨7,22,44,73,50,489,457,393,409⟩,⟨7,22,44,73,50,96,192,384,272⟩,[⟨7,1208926973665612483686199,⟨23,23,63,75,63,127,64,259,279⟩⟩,⟨8,1181745671700720283447,⟨23,23,63,75,63,127,192,131,23⟩⟩]⟩
theorem node140 : UpperPrefix a [2,4,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,1] 30 cert140 (by decide +kernel)

def cert141 : Local := ⟨⟨0,425,0,402,0,403,275,19,131⟩,[(0,1),(2,4),(4,2)],[(2,0,0),(5,2,1),(6,3,2),(6,3,4),(3,4,1)]⟩
theorem node141 : UpperPrefix a [2,4,5,6,3] 30 :=
  local_sound a [2,4,5,6,3] 30 cert141 (by decide +kernel)

def cert142 : Local := ⟨⟨0,424,467,0,266,0,282,26,138⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(5,2,1),(6,3,2),(0,5,2)]⟩
theorem node142 : UpperPrefix a [2,4,5,6,7,0] 30 :=
  local_sound a [2,4,5,6,7,0] 30 cert142 (by decide +kernel)

def cert143 : Leaf := ⟨⟨0,169,211,144,9,153,281,25,137⟩,[(0,1)],[(2,0,0),(5,2,1),(6,3,2)],⟨7,22,44,73,176,98,457,393,281⟩,⟨7,22,44,73,176,98,192,384,272⟩,[⟨1,1214913104244914621775873,⟨477,20,252,457,176,96,192,384,272⟩⟩,⟨8,1181748206908264871295,⟨7,23,47,127,191,127,255,131,23⟩⟩]⟩
theorem node143 : UpperPrefix a [2,4,5,6,7,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,1] 30 cert143 (by decide +kernel)

def cert144 : Local := ⟨⟨0,417,0,402,259,0,275,19,131⟩,[(0,1),(2,5),(5,3)],[(2,0,0),(5,2,1),(6,3,2),(6,3,5),(3,5,2)]⟩
theorem node144 : UpperPrefix a [2,4,5,6,7,3] 30 :=
  local_sound a [2,4,5,6,7,3] 30 cert144 (by decide +kernel)

def cert145 : Leaf := ⟨⟨0,41,83,18,267,155,27,27,11⟩,[(0,1)],[(2,0,0),(5,2,1),(6,3,2),(8,5,4)],⟨7,22,44,73,176,352,203,395,283⟩,⟨7,22,44,73,176,352,192,384,272⟩,[⟨7,1284484837389052905923891,⟨7,279,45,73,319,367,64,259,279⟩⟩]⟩
theorem node145 : UpperPrefix a [2,4,5,6,7,8] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,8] 30 cert145 (by decide +kernel)

theorem node146 : UpperPrefix a [2,4,5,6,7] 30 :=
  branch_upper a [2,4,5,6,7] 30 (by decide) (fin9_cases _
  node142
  node143
  (invalid_upper a [2,4,5,6,7,2] 30 (by decide +kernel))
  node144
  (invalid_upper a [2,4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,7] 30 (by decide +kernel))
  node145)

def cert147 : Local := ⟨⟨0,424,467,0,138,0,282,26,138⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(5,2,1),(6,3,2),(0,5,2)]⟩
theorem node147 : UpperPrefix a [2,4,5,6,8,0] 30 :=
  local_sound a [2,4,5,6,8,0] 30 cert147 (by decide +kernel)

def cert148 : Leaf := ⟨⟨0,169,195,130,139,137,11,11,139⟩,[(0,1)],[(2,0,0),(5,2,1),(6,3,2)],⟨7,22,44,73,304,98,201,393,409⟩,⟨7,22,44,73,304,98,192,384,272⟩,[⟨4,1210255463600074998416419,⟨111,239,45,109,493,111,192,384,460⟩⟩,⟨8,1184056015861480302003,⟨7,23,45,77,63,111,237,239,23⟩⟩]⟩
theorem node148 : UpperPrefix a [2,4,5,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,1] 30 cert148 (by decide +kernel)

def cert149 : Local := ⟨⟨0,417,0,402,131,0,275,19,131⟩,[(0,1),(2,5),(5,3)],[(2,0,0),(5,2,1),(6,3,2),(6,3,5),(3,5,2)]⟩
theorem node149 : UpperPrefix a [2,4,5,6,8,3] 30 :=
  local_sound a [2,4,5,6,8,3] 30 cert149 (by decide +kernel)

def cert150 : Local := ⟨⟨0,297,339,274,11,0,283,27,11⟩,[(0,1),(5,6)],[(2,0,0),(5,2,1),(6,3,2),(7,5,5)]⟩
theorem node150 : UpperPrefix a [2,4,5,6,8,7] 30 :=
  local_sound a [2,4,5,6,8,7] 30 cert150 (by decide +kernel)

theorem node151 : UpperPrefix a [2,4,5,6,8] 30 :=
  branch_upper a [2,4,5,6,8] 30 (by decide) (fin9_cases _
  node147
  node148
  (invalid_upper a [2,4,5,6,8,2] 30 (by decide +kernel))
  node149
  (invalid_upper a [2,4,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,6] 30 (by decide +kernel))
  node150
  (invalid_upper a [2,4,5,6,8,8] 30 (by decide +kernel)))

theorem node152 : UpperPrefix a [2,4,5,6] 30 :=
  branch_upper a [2,4,5,6] 30 (by decide) (fin9_cases _
  node139
  node140
  (invalid_upper a [2,4,5,6,2] 30 (by decide +kernel))
  node141
  (invalid_upper a [2,4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,6] 30 (by decide +kernel))
  node146
  node151)

def cert153 : Leaf := ⟨⟨0,225,209,80,194,153,281,89,201⟩,[(0,1)],[(2,0,0),(5,2,1),(1,5,4)],⟨7,22,44,137,49,98,456,456,344⟩,⟨7,22,44,137,49,98,192,384,272⟩,[⟨8,1181747927902887931511,⟨23,23,63,139,55,127,255,128,19⟩⟩,⟨3,1210107565286324513541639,⟨23,23,55,131,51,115,192,384,272⟩⟩]⟩
theorem node153 : UpperPrefix a [2,4,5,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,7,0,1] 30 cert153 (by decide +kernel)

def cert154 : Local := ⟨⟨0,353,0,338,322,403,275,83,67⟩,[(0,1),(2,5)],[(2,0,0),(5,2,1),(7,3,5),(3,5,2)]⟩
theorem node154 : UpperPrefix a [2,4,5,7,0,3] 30 :=
  local_sound a [2,4,5,7,0,3] 30 cert154 (by decide +kernel)

def cert155 : Leaf := ⟨⟨0,161,147,18,130,155,17,91,203⟩,[(0,1)],[(2,0,0),(5,2,1)],⟨7,22,44,137,49,352,194,456,344⟩,⟨7,22,44,137,49,352,194,384,272⟩,[⟨8,1181889786893086780983,⟨23,23,127,203,55,127,203,128,19⟩⟩,⟨6,1210106412364829578784311,⟨23,23,63,139,55,319,139,384,275⟩⟩,⟨3,1210107709399313566141959,⟨23,23,119,195,51,352,195,384,272⟩⟩]⟩
theorem node155 : UpperPrefix a [2,4,5,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,7,0,8,1] 30 cert155 (by decide +kernel)

def cert156 : Leaf := ⟨⟨0,353,339,338,322,27,0,91,75⟩,[(0,1),(6,3)],[(2,0,0),(5,2,1),(7,3,6)],⟨7,22,44,137,49,352,200,450,338⟩,⟨7,22,44,137,49,352,200,384,272⟩,[⟨3,1210107565284125490286087,⟨23,23,55,131,51,352,192,384,272⟩⟩]⟩
theorem node156 : UpperPrefix a [2,4,5,7,0,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,0,8,3] 30 cert156 (by decide +kernel)

theorem node157 : UpperPrefix a [2,4,5,7,0,8] 30 :=
  branch_upper a [2,4,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,0,8,0] 30 (by decide +kernel))
  node155
  (invalid_upper a [2,4,5,7,0,8,2] 30 (by decide +kernel))
  node156
  (invalid_upper a [2,4,5,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,8] 30 (by decide +kernel)))

theorem node158 : UpperPrefix a [2,4,5,7,0] 30 :=
  branch_upper a [2,4,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,0,0] 30 (by decide +kernel))
  node153
  (invalid_upper a [2,4,5,7,0,2] 30 (by decide +kernel))
  node154
  (invalid_upper a [2,4,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,7] 30 (by decide +kernel))
  node157)

def cert159 : Leaf := ⟨⟨0,224,211,82,192,154,282,90,202⟩,[(0,1)],[(2,0,0),(5,2,1),(0,5,2)],⟨7,22,44,137,50,97,456,456,344⟩,⟨7,22,44,137,50,97,192,384,272⟩,[⟨8,1181747927902887931511,⟨23,23,63,139,55,127,255,128,19⟩⟩,⟨3,1210107565286324513541639,⟨23,23,55,131,51,115,192,384,272⟩⟩]⟩
theorem node159 : UpperPrefix a [2,4,5,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,7,1,0] 30 cert159 (by decide +kernel)

def cert160 : Local := ⟨⟨0,353,0,338,321,403,275,83,67⟩,[(0,1),(2,5)],[(2,0,0),(5,2,1),(7,3,5),(3,5,2)]⟩
theorem node160 : UpperPrefix a [2,4,5,7,1,3] 30 :=
  local_sound a [2,4,5,7,1,3] 30 cert160 (by decide +kernel)

def cert161 : Leaf := ⟨⟨0,224,451,322,192,139,11,75,203⟩,[(0,1)],[(2,0,0),(5,2,1)],⟨7,22,44,137,50,352,201,457,345⟩,⟨7,22,44,137,50,352,192,384,272⟩,[⟨4,1212473517836226853340179,⟨7,7,108,237,39,492,228,492,493⟩⟩,⟨8,1181889784685465177607,⟨23,23,127,203,51,96,192,128,16⟩⟩,⟨0,1210107565284126564027904,⟨22,22,62,138,50,352,192,384,272⟩⟩,⟨3,1210107565284125490286087,⟨23,23,55,131,51,352,192,384,272⟩⟩]⟩
theorem node161 : UpperPrefix a [2,4,5,7,1,8] 30 :=
  Boolean.leaf_sound a [2,4,5,7,1,8] 30 cert161 (by decide +kernel)

theorem node162 : UpperPrefix a [2,4,5,7,1] 30 :=
  branch_upper a [2,4,5,7,1] 30 (by decide) (fin9_cases _
  node159
  (invalid_upper a [2,4,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,2] 30 (by decide +kernel))
  node160
  (invalid_upper a [2,4,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,7] 30 (by decide +kernel))
  node161)

def cert163 : Local := ⟨⟨0,489,0,338,0,403,275,83,195⟩,[(0,1),(2,4),(4,2)],[(2,0,0),(5,2,1),(3,4,1)]⟩
theorem node163 : UpperPrefix a [2,4,5,7,3] 30 :=
  local_sound a [2,4,5,7,3] 30 cert163 (by decide +kernel)

def cert164 : Leaf := ⟨⟨0,297,403,274,0,411,283,27,11⟩,[(0,1),(4,5)],[(2,0,0),(5,2,1),(6,4,4)],⟨7,22,44,137,112,363,459,395,283⟩,⟨7,22,44,137,112,96,192,384,272⟩,[⟨7,1227816439596811878927367,⟨263,279,319,9,112,112,64,256,272⟩⟩]⟩
theorem node164 : UpperPrefix a [2,4,5,7,6] 30 :=
  Boolean.leaf_sound a [2,4,5,7,6] 30 cert164 (by decide +kernel)

def cert165 : Local := ⟨⟨0,488,465,336,200,410,280,88,200⟩,[(0,1)],[(2,0,0),(5,2,1),(0,5,2),(1,6,5)]⟩
theorem node165 : UpperPrefix a [2,4,5,7,8,0,1] 30 :=
  local_sound a [2,4,5,7,8,0,1] 30 cert165 (by decide +kernel)

def cert166 : Local := ⟨⟨0,360,339,338,74,282,0,90,74⟩,[(0,1),(6,3)],[(2,0,0),(5,2,1),(7,3,6),(0,5,2)]⟩
theorem node166 : UpperPrefix a [2,4,5,7,8,0,3] 30 :=
  local_sound a [2,4,5,7,8,0,3] 30 cert166 (by decide +kernel)

theorem node167 : UpperPrefix a [2,4,5,7,8,0] 30 :=
  branch_upper a [2,4,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,8,0,0] 30 (by decide +kernel))
  node165
  (invalid_upper a [2,4,5,7,8,0,2] 30 (by decide +kernel))
  node166
  (invalid_upper a [2,4,5,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,8] 30 (by decide +kernel)))

def cert168 : Leaf := ⟨⟨0,489,465,0,201,409,0,89,201⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(5,2,1)],⟨7,22,44,137,304,98,193,456,344⟩,⟨7,22,44,137,304,98,193,384,272⟩,[⟨1,1385840634834114948628481,⟨477,404,508,457,436,508,457,384,272⟩⟩]⟩
theorem node168 : UpperPrefix a [2,4,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,1,0] 30 cert168 (by decide +kernel)

def cert169 : Leaf := ⟨⟨0,353,339,338,67,281,0,83,67⟩,[(0,1),(6,3)],[(2,0,0),(5,2,1),(7,3,6)],⟨7,22,44,137,304,98,200,449,337⟩,⟨7,22,44,137,304,98,200,384,272⟩,[⟨3,1361518440643332513205767,⟨23,23,439,131,432,499,192,384,272⟩⟩]⟩
theorem node169 : UpperPrefix a [2,4,5,7,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,1,3] 30 cert169 (by decide +kernel)

theorem node170 : UpperPrefix a [2,4,5,7,8,1] 30 :=
  branch_upper a [2,4,5,7,8,1] 30 (by decide) (fin9_cases _
  node168
  (invalid_upper a [2,4,5,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,2] 30 (by decide +kernel))
  node169
  (invalid_upper a [2,4,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,8] 30 (by decide +kernel)))

def cert171 : Local := ⟨⟨0,353,0,338,67,403,275,83,67⟩,[(0,1),(2,5)],[(2,0,0),(5,2,1),(7,3,5),(3,5,2)]⟩
theorem node171 : UpperPrefix a [2,4,5,7,8,3] 30 :=
  local_sound a [2,4,5,7,8,3] 30 cert171 (by decide +kernel)

theorem node172 : UpperPrefix a [2,4,5,7,8] 30 :=
  branch_upper a [2,4,5,7,8] 30 (by decide) (fin9_cases _
  node167
  node170
  (invalid_upper a [2,4,5,7,8,2] 30 (by decide +kernel))
  node171
  (invalid_upper a [2,4,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,8] 30 (by decide +kernel)))

theorem node173 : UpperPrefix a [2,4,5,7] 30 :=
  branch_upper a [2,4,5,7] 30 (by decide) (fin9_cases _
  node158
  node162
  (invalid_upper a [2,4,5,7,2] 30 (by decide +kernel))
  node163
  (invalid_upper a [2,4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,5] 30 (by decide +kernel))
  node164
  (invalid_upper a [2,4,5,7,7] 30 (by decide +kernel))
  node172)

def cert174 : Leaf := ⟨⟨0,489,448,208,458,392,264,72,201⟩,[(0,1)],[(2,0,0),(5,2,1),(1,5,4)],⟨7,22,44,265,49,98,200,456,472⟩,⟨7,22,44,265,49,98,192,384,272⟩,[⟨0,1210181568538481756472320,⟨102,118,236,492,48,98,192,384,272⟩⟩,⟨4,1210181568537382244844547,⟨103,103,236,493,33,99,192,384,256⟩⟩]⟩
theorem node174 : UpperPrefix a [2,4,5,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,8,0,1] 30 cert174 (by decide +kernel)

def cert175 : Local := ⟨⟨0,481,0,210,450,403,275,83,195⟩,[(0,1),(2,5)],[(2,0,0),(5,2,1),(3,5,2)]⟩
theorem node175 : UpperPrefix a [2,4,5,8,0,3] 30 :=
  local_sound a [2,4,5,8,0,3] 30 cert175 (by decide +kernel)

def cert176 : Leaf := ⟨⟨0,353,339,82,322,0,283,91,75⟩,[(0,1),(5,6)],[(2,0,0),(5,2,1),(7,5,5)],⟨7,22,44,265,49,224,202,458,346⟩,⟨7,22,44,265,49,224,192,384,272⟩,[⟨3,1210107567535925303971335,⟨23,23,55,259,51,224,224,384,272⟩⟩]⟩
theorem node176 : UpperPrefix a [2,4,5,8,0,7] 30 :=
  Boolean.leaf_sound a [2,4,5,8,0,7] 30 cert176 (by decide +kernel)

theorem node177 : UpperPrefix a [2,4,5,8,0] 30 :=
  branch_upper a [2,4,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,8,0,0] 30 (by decide +kernel))
  node174
  (invalid_upper a [2,4,5,8,0,2] 30 (by decide +kernel))
  node175
  (invalid_upper a [2,4,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,0,6] 30 (by decide +kernel))
  node176
  (invalid_upper a [2,4,5,8,0,8] 30 (by decide +kernel)))

def cert178 : Leaf := ⟨⟨0,480,449,210,448,393,265,73,203⟩,[(0,1)],[(2,0,0),(5,2,1)],⟨7,22,44,265,50,233,201,457,473⟩,⟨7,22,44,265,50,96,192,384,272⟩,[⟨1,1210181496656809578987521,⟨5,20,236,493,48,96,192,384,272⟩⟩,⟨4,1210181496655710067360771,⟨7,7,236,493,35,96,192,384,256⟩⟩,⟨0,1210107565284126564027904,⟨22,22,62,266,50,96,192,384,272⟩⟩,⟨3,1210107565284125490286087,⟨23,23,55,259,51,96,192,384,272⟩⟩]⟩
theorem node178 : UpperPrefix a [2,4,5,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,8,1] 30 cert178 (by decide +kernel)

def cert179 : Local := ⟨⟨0,489,0,210,0,403,275,83,195⟩,[(0,1),(2,4),(4,2)],[(2,0,0),(5,2,1),(3,4,1)]⟩
theorem node179 : UpperPrefix a [2,4,5,8,3] 30 :=
  local_sound a [2,4,5,8,3] 30 cert179 (by decide +kernel)

def cert180 : Leaf := ⟨⟨0,416,403,146,0,411,283,27,139⟩,[(0,1),(4,5)],[(2,0,0),(5,2,1),(6,4,4)],⟨7,22,44,265,112,235,203,395,411⟩,⟨7,22,44,265,112,96,192,384,272⟩,[⟨0,1210107565286050709376000,⟨6,22,62,264,112,112,192,384,272⟩⟩,⟨3,1210107565286049635634183,⟨7,23,55,257,112,112,192,384,272⟩⟩]⟩
theorem node180 : UpperPrefix a [2,4,5,8,6] 30 :=
  Boolean.leaf_sound a [2,4,5,8,6] 30 cert180 (by decide +kernel)

def cert181 : Leaf := ⟨⟨0,296,275,18,330,410,282,90,202⟩,[(0,1)],[(2,0,0),(5,2,1),(0,5,2)],⟨7,22,44,265,176,97,202,458,346⟩,⟨7,22,44,265,176,97,192,384,272⟩,[⟨6,1210106412362398623212819,⟨7,23,44,267,191,33,136,395,287⟩⟩,⟨7,1208926973663185818756371,⟨7,23,44,267,63,97,72,267,287⟩⟩]⟩
theorem node181 : UpperPrefix a [2,4,5,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,0] 30 cert181 (by decide +kernel)

def cert182 : Leaf := ⟨⟨0,297,275,16,329,409,281,89,201⟩,[(0,1)],[(2,0,0),(5,2,1)],⟨7,22,44,265,176,98,201,457,345⟩,⟨7,22,44,265,176,98,192,384,272⟩,[⟨1,1214913104244914621775873,⟨477,20,252,457,176,96,192,384,272⟩⟩,⟨6,1210106412362398623212819,⟨7,23,44,267,191,35,136,395,287⟩⟩,⟨7,1208926973663185818756371,⟨7,23,44,267,63,99,72,267,287⟩⟩]⟩
theorem node182 : UpperPrefix a [2,4,5,8,7,1] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,1] 30 cert182 (by decide +kernel)

def cert183 : Local := ⟨⟨0,481,0,210,323,403,275,83,195⟩,[(0,1),(2,5)],[(2,0,0),(5,2,1),(3,5,2)]⟩
theorem node183 : UpperPrefix a [2,4,5,8,7,3] 30 :=
  local_sound a [2,4,5,8,7,3] 30 cert183 (by decide +kernel)

theorem node184 : UpperPrefix a [2,4,5,8,7] 30 :=
  branch_upper a [2,4,5,8,7] 30 (by decide) (fin9_cases _
  node181
  node182
  (invalid_upper a [2,4,5,8,7,2] 30 (by decide +kernel))
  node183
  (invalid_upper a [2,4,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,8] 30 (by decide +kernel)))

theorem node185 : UpperPrefix a [2,4,5,8] 30 :=
  branch_upper a [2,4,5,8] 30 (by decide) (fin9_cases _
  node177
  node178
  (invalid_upper a [2,4,5,8,2] 30 (by decide +kernel))
  node179
  (invalid_upper a [2,4,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,5] 30 (by decide +kernel))
  node180
  node184
  (invalid_upper a [2,4,5,8,8] 30 (by decide +kernel)))

theorem node186 : UpperPrefix a [2,4,5] 30 :=
  branch_upper a [2,4,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [2,4,5,1] [2,3,4,5] 30 (by decide +kernel) node50)
  (invalid_upper a [2,4,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,5] 30 (by decide +kernel))
  node152
  node173
  node185)

def cert187 : Leaf := ⟨⟨0,41,51,0,0,411,315,59,171⟩,[(0,1),(3,4),(4,3)],[(2,0,0)],⟨7,22,76,41,49,490,458,394,410⟩,⟨7,22,76,41,49,96,192,384,272⟩,[⟨6,1238495951492337982508039,⟨391,415,415,57,57,32,128,384,280⟩⟩,⟨7,1208926973665889504754751,⟨7,31,95,63,63,127,64,256,283⟩⟩,⟨8,1181745671977741351999,⟨7,31,95,63,63,127,192,128,27⟩⟩]⟩
theorem node187 : UpperPrefix a [2,4,6,5,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,0] 30 cert187 (by decide +kernel)

def cert188 : Leaf := ⟨⟨0,488,432,0,456,410,312,120,232⟩,[(0,1),(3,5)],[(2,0,0),(0,5,3)],⟨7,22,76,41,50,97,456,392,408⟩,⟨7,22,76,41,50,97,192,384,272⟩,[⟨1,1285813291192736145211393,⟨5,468,76,45,508,109,192,384,468⟩⟩]⟩
theorem node188 : UpperPrefix a [2,4,6,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,1,0] 30 cert188 (by decide +kernel)

def cert189 : Leaf := ⟨⟨0,457,0,466,457,0,283,91,203⟩,[(0,1),(2,5),(5,2)],[(2,0,0)],⟨7,22,76,41,50,104,449,385,401⟩,⟨7,22,76,41,50,104,192,384,272⟩,[⟨5,1297651542119330574509075,⟨455,471,76,205,471,76,192,448,467⟩⟩]⟩
theorem node189 : UpperPrefix a [2,4,6,5,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,1,3] 30 cert189 (by decide +kernel)

def cert190 : Leaf := ⟨⟨0,105,51,18,73,0,315,59,43⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,22,76,41,50,224,457,393,281⟩,⟨7,22,76,41,50,224,192,384,272⟩,[⟨8,1181747928459623071359,⟨31,31,127,63,63,255,255,128,27⟩⟩,⟨6,1295275029750666226566147,⟨391,415,12,41,443,160,128,384,408⟩⟩]⟩
theorem node190 : UpperPrefix a [2,4,6,5,1,7] 30 :=
  Boolean.leaf_sound a [2,4,6,5,1,7] 30 cert190 (by decide +kernel)

def cert191 : Leaf := ⟨⟨0,105,35,2,73,139,299,43,171⟩,[(0,1)],[(2,0,0)],⟨7,22,76,41,50,352,201,393,409⟩,⟨7,22,76,41,50,352,192,384,272⟩,[⟨4,1212473373721040922870803,⟨7,15,76,45,47,492,228,492,493⟩⟩,⟨7,1208926973665889504754751,⟨7,31,95,63,63,383,64,256,283⟩⟩,⟨8,1181745671977741351999,⟨7,31,95,63,63,127,192,128,27⟩⟩,⟨6,1295275029750666226566147,⟨391,415,12,41,443,288,128,384,408⟩⟩]⟩
theorem node191 : UpperPrefix a [2,4,6,5,1,8] 30 :=
  Boolean.leaf_sound a [2,4,6,5,1,8] 30 cert191 (by decide +kernel)

#print axioms node191
end Delivery.FiniteExclusion.Sharp4x5
