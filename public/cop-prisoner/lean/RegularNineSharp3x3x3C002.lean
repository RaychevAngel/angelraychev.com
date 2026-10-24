import RegularNineSharp3x3x3Base
import RegularNineSharp3x3x3C000
import RegularNineSharp3x3x3C001
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def cert128 : Leaf := ⟨⟨0,81,26,67,74,339,43,91,27⟩,[(0,1)],[(2,0,0),(8,3,5),(5,7,6)],⟨7,14,69,280,49,168,208,416,322⟩,⟨7,14,69,280,49,168,208,416,320⟩,[⟨7,1530047894509291119549903,⟨263,271,335,287,49,59,351,319,335⟩⟩]⟩
theorem node128 : UpperPrefix a [2,3,6,8,0,7,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,4,5] 30 cert128 (by decide +kernel)

theorem node129 : UpperPrefix a [2,3,6,8,0,7,4] 30 :=
  branch_upper a [2,3,6,8,0,7,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,7,4,0] 30 (by decide +kernel))
  node127
  (invalid_upper a [2,3,6,8,0,7,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,4,4] 30 (by decide +kernel))
  node128
  (invalid_upper a [2,3,6,8,0,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,4,8] 30 (by decide +kernel)))

def cert130 : Leaf := ⟨⟨0,97,42,99,74,339,0,123,59⟩,[(0,1),(6,5)],[(2,0,0),(8,3,5),(7,5,6)],⟨7,14,69,280,49,168,224,402,338⟩,⟨7,14,69,280,49,168,224,384,320⟩,[⟨4,1210108141743504574403707,⟨7,15,69,271,103,239,231,388,325⟩⟩]⟩
theorem node130 : UpperPrefix a [2,3,6,8,0,7,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,5] 30 cert130 (by decide +kernel)

theorem node131 : UpperPrefix a [2,3,6,8,0,7] 30 :=
  branch_upper a [2,3,6,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,7,0] 30 (by decide +kernel))
  node126
  (invalid_upper a [2,3,6,8,0,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,3] 30 (by decide +kernel))
  node129
  node130
  (invalid_upper a [2,3,6,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,7,8] 30 (by decide +kernel)))

theorem node132 : UpperPrefix a [2,3,6,8,0] 30 :=
  branch_upper a [2,3,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,0,0] 30 (by decide +kernel))
  node124
  (invalid_upper a [2,3,6,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,3] 30 (by decide +kernel))
  node125
  (invalid_upper a [2,3,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,0,6] 30 (by decide +kernel))
  node131
  (invalid_upper a [2,3,6,8,0,8] 30 (by decide +kernel)))

def cert133 : Leaf := ⟨⟨0,369,306,96,329,338,304,112,176⟩,[(0,1)],[(2,0,0),(3,1,4)],⟨7,14,69,280,50,41,240,432,496⟩,⟨7,14,69,280,50,41,192,384,320⟩,[⟨7,1208926989811644456211919,⟨55,63,119,319,51,59,127,319,383⟩⟩,⟨0,1285813291192733985145856,⟨6,14,68,472,506,40,192,384,320⟩⟩,⟨1,1285813291192733985144833,⟨5,12,69,472,504,41,192,384,320⟩⟩]⟩
theorem node133 : UpperPrefix a [2,3,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,0] 30 cert133 (by decide +kernel)

def cert134 : Leaf := ⟨⟨0,353,290,99,329,0,291,99,163⟩,[(0,1),(5,3)],[(2,0,0),(3,1,4),(4,5,5)],⟨7,14,69,280,50,56,225,417,481⟩,⟨7,14,69,280,50,56,192,384,320⟩,[⟨7,1208926989811644456211919,⟨55,63,119,319,51,59,127,319,383⟩⟩]⟩
theorem node134 : UpperPrefix a [2,3,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,4] 30 cert134 (by decide +kernel)

def cert135 : Local := ⟨⟨0,240,0,226,200,338,50,114,178⟩,[(0,1),(2,6)],[(2,0,0),(3,1,4),(8,3,5),(0,6,2)]⟩
theorem node135 : UpperPrefix a [2,3,6,8,1,7,0] 30 :=
  local_sound a [2,3,6,8,1,7,0] 30 cert135 (by decide +kernel)

def cert136 : Leaf := ⟨⟨0,240,178,226,200,338,34,114,178⟩,[(0,1)],[(2,0,0),(3,1,4),(8,3,5)],⟨7,14,69,280,50,168,208,385,352⟩,⟨7,14,69,280,50,168,208,385,320⟩,[⟨0,2362367876172310199143936,⟨286,286,382,280,378,504,504,506,360⟩⟩]⟩
theorem node136 : UpperPrefix a [2,3,6,8,1,7,4,0] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,7,4,0] 30 cert136 (by decide +kernel)

def cert137 : Leaf := ⟨⟨0,81,18,67,73,339,35,83,19⟩,[(0,1)],[(2,0,0),(3,1,4),(8,3,5),(5,7,6)],⟨7,14,69,280,50,168,208,416,321⟩,⟨7,14,69,280,50,168,208,416,320⟩,[⟨7,1530047894509291119549903,⟨263,271,335,287,51,59,351,319,335⟩⟩]⟩
theorem node137 : UpperPrefix a [2,3,6,8,1,7,4,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,1,7,4,5] 30 cert137 (by decide +kernel)

theorem node138 : UpperPrefix a [2,3,6,8,1,7,4] 30 :=
  branch_upper a [2,3,6,8,1,7,4] 30 (by decide) (fin9_cases _
  node136
  (invalid_upper a [2,3,6,8,1,7,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,4,4] 30 (by decide +kernel))
  node137
  (invalid_upper a [2,3,6,8,1,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,4,8] 30 (by decide +kernel)))

def cert139 : Local := ⟨⟨0,113,50,99,73,339,0,115,51⟩,[(0,1),(6,5)],[(2,0,0),(3,1,4),(8,3,5),(7,5,6)]⟩
theorem node139 : UpperPrefix a [2,3,6,8,1,7,5] 30 :=
  local_sound a [2,3,6,8,1,7,5] 30 cert139 (by decide +kernel)

theorem node140 : UpperPrefix a [2,3,6,8,1,7] 30 :=
  branch_upper a [2,3,6,8,1,7] 30 (by decide) (fin9_cases _
  node135
  (invalid_upper a [2,3,6,8,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,3] 30 (by decide +kernel))
  node138
  node139
  (invalid_upper a [2,3,6,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,7,8] 30 (by decide +kernel)))

theorem node141 : UpperPrefix a [2,3,6,8,1] 30 :=
  branch_upper a [2,3,6,8,1] 30 (by decide) (fin9_cases _
  node133
  (invalid_upper a [2,3,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,3] 30 (by decide +kernel))
  node134
  (invalid_upper a [2,3,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,1,6] 30 (by decide +kernel))
  node140
  (invalid_upper a [2,3,6,8,1,8] 30 (by decide +kernel)))

def cert142 : Leaf := ⟨⟨0,225,170,225,73,192,41,121,185⟩,[(0,1)],[(2,0,0),(1,6,2)],⟨7,14,69,280,176,41,194,432,368⟩,⟨7,14,69,280,176,41,194,384,320⟩,[⟨8,1182034255840520721531,⟨39,47,85,127,247,47,247,132,85⟩⟩,⟨4,1210107853864972137288827,⟨39,47,69,367,231,47,231,388,325⟩⟩]⟩
theorem node142 : UpperPrefix a [2,3,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,0,1] 30 cert142 (by decide +kernel)

def cert143 : Leaf := ⟨⟨0,81,26,99,331,82,0,123,59⟩,[(0,1),(6,4)],[(2,0,0),(7,4,6)],⟨7,14,69,280,176,41,208,418,354⟩,⟨7,14,69,280,176,41,208,384,320⟩,[⟨8,1182034251442407101499,⟨39,47,69,127,247,47,213,128,68⟩⟩,⟨5,1210107852388327954076731,⟨7,15,69,351,215,15,213,384,324⟩⟩]⟩
theorem node143 : UpperPrefix a [2,3,6,8,7,0,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,0,4] 30 cert143 (by decide +kernel)

def cert144 : Leaf := ⟨⟨0,496,442,226,0,466,0,122,186⟩,[(0,1),(4,6),(6,4)],[(2,0,0)],⟨7,14,69,280,176,41,224,402,338⟩,⟨7,14,69,280,176,41,224,384,320⟩,[⟨0,1380445664758261139639808,⟨398,398,478,344,504,506,504,392,344⟩⟩]⟩
theorem node144 : UpperPrefix a [2,3,6,8,7,0,5] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,0,5] 30 cert144 (by decide +kernel)

theorem node145 : UpperPrefix a [2,3,6,8,7,0] 30 :=
  branch_upper a [2,3,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,8,7,0,0] 30 (by decide +kernel))
  node142
  (invalid_upper a [2,3,6,8,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,3] 30 (by decide +kernel))
  node143
  node144
  (invalid_upper a [2,3,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,0,8] 30 (by decide +kernel)))

def cert146 : Local := ⟨⟨0,496,0,226,322,0,306,114,178⟩,[(0,1),(2,6),(5,1)],[(2,0,0),(3,1,5),(0,6,2)]⟩
theorem node146 : UpperPrefix a [2,3,6,8,7,1,0] 30 :=
  local_sound a [2,3,6,8,7,1,0] 30 cert146 (by decide +kernel)

def cert147 : Local := ⟨⟨0,369,306,99,323,0,0,115,51⟩,[(0,1),(5,1),(6,4)],[(2,0,0),(3,1,5),(7,4,6)]⟩
theorem node147 : UpperPrefix a [2,3,6,8,7,1,4] 30 :=
  local_sound a [2,3,6,8,7,1,4] 30 cert147 (by decide +kernel)

def cert148 : Local := ⟨⟨0,497,434,227,0,0,0,115,179⟩,[(0,1),(4,6),(5,1),(6,4)],[(2,0,0),(3,1,5)]⟩
theorem node148 : UpperPrefix a [2,3,6,8,7,1,5] 30 :=
  local_sound a [2,3,6,8,7,1,5] 30 cert148 (by decide +kernel)

theorem node149 : UpperPrefix a [2,3,6,8,7,1] 30 :=
  branch_upper a [2,3,6,8,7,1] 30 (by decide) (fin9_cases _
  node146
  (invalid_upper a [2,3,6,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,3] 30 (by decide +kernel))
  node147
  node148
  (invalid_upper a [2,3,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,1,8] 30 (by decide +kernel)))

def cert150 : Leaf := ⟨⟨0,225,170,226,330,0,43,107,171⟩,[(0,1),(5,3)],[(2,0,0),(4,5,5)],⟨7,14,69,280,176,56,227,419,355⟩,⟨7,14,69,280,176,56,192,384,320⟩,[⟨8,1182034181073654535227,⟨7,47,69,127,247,127,192,128,64⟩⟩,⟨0,1210107581904120991187968,⟨6,46,116,312,184,56,248,440,376⟩⟩]⟩
theorem node150 : UpperPrefix a [2,3,6,8,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,7,4] 30 cert150 (by decide +kernel)

theorem node151 : UpperPrefix a [2,3,6,8,7] 30 :=
  branch_upper a [2,3,6,8,7] 30 (by decide) (fin9_cases _
  node145
  node149
  (invalid_upper a [2,3,6,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,3] 30 (by decide +kernel))
  node150
  (invalid_upper a [2,3,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,7,8] 30 (by decide +kernel)))

theorem node152 : UpperPrefix a [2,3,6,8] 30 :=
  branch_upper a [2,3,6,8] 30 (by decide) (fin9_cases _
  node132
  node141
  (invalid_upper a [2,3,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,8,6] 30 (by decide +kernel))
  node151
  (invalid_upper a [2,3,6,8,8] 30 (by decide +kernel)))

theorem node153 : UpperPrefix a [2,3,6] 30 :=
  branch_upper a [2,3,6] 30 (by decide) (fin9_cases _
  node54
  node75
  (invalid_upper a [2,3,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,4] 30 (by decide +kernel))
  node96
  (invalid_upper a [2,3,6,6] 30 (by decide +kernel))
  node123
  node152)

theorem node154 : UpperPrefix a [2,3] 30 :=
  branch_upper a [2,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [2,3,1] [2,0,3] 30 (by decide +kernel) node4)
  (invalid_upper a [2,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,3] 30 (by decide +kernel))
  node20
  node38
  node153
  (PrefixConjugacy.upper aut2 [2,3,7] [2,3,6] 30 (by decide +kernel) node153)
  (PrefixConjugacy.upper aut1 [2,3,8] [2,3,6] 30 (by decide +kernel) node153))

theorem node155 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
  node5
  (invalid_upper a [2,1] 30 (by decide +kernel))
  (invalid_upper a [2,2] 30 (by decide +kernel))
  node154
  (PrefixConjugacy.upper aut6 [2,4] [2,3] 30 (by decide +kernel) node154)
  (PrefixConjugacy.upper aut3 [2,5] [2,3] 30 (by decide +kernel) node154)
  (PrefixConjugacy.upper aut9 [2,6] [2,3] 30 (by decide +kernel) node154)
  (PrefixConjugacy.upper aut11 [2,7] [2,3] 30 (by decide +kernel) node154)
  (PrefixConjugacy.upper aut10 [2,8] [2,3] 30 (by decide +kernel) node154))

theorem node156 : UpperPrefix a [3,0] 30 :=
  branch_upper a [3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut36 [3,0,1] [2,0,3] 30 (by decide +kernel) node4)
  (invalid_upper a [3,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut42 [3,0,4] [2,3,5] 30 (by decide +kernel) node38)
  (PrefixConjugacy.upper aut39 [3,0,5] [2,3,4] 30 (by decide +kernel) node20)
  (PrefixConjugacy.upper aut45 [3,0,6] [2,3,6] 30 (by decide +kernel) node153)
  (PrefixConjugacy.upper aut47 [3,0,7] [2,3,6] 30 (by decide +kernel) node153)
  (PrefixConjugacy.upper aut46 [3,0,8] [2,3,6] 30 (by decide +kernel) node153))

def cert157 : Leaf := ⟨⟨20,32,10,6,454,455,262,70,134⟩,[],[(3,0,2),(4,1,0),(5,2,1)],⟨11,22,37,25,502,494,454,454,454⟩,⟨11,22,37,25,48,40,192,384,320⟩,[⟨0,1238497212499956620856320,⟨458,470,502,24,48,40,192,384,320⟩⟩,⟨6,1210106412362349507785787,⟨11,31,37,31,63,47,128,384,256⟩⟩,⟨7,1208926973663136703329339,⟨11,31,37,31,63,47,64,256,320⟩⟩,⟨8,1181745669224939926587,⟨11,31,37,31,63,47,192,128,64⟩⟩]⟩
theorem node157 : UpperPrefix a [3,4,5,0] 30 :=
  Boolean.leaf_sound a [3,4,5,0] 30 cert157 (by decide +kernel)

def cert158 : Local := ⟨⟨0,481,456,0,453,453,261,69,133⟩,[(0,3),(3,1)],[(3,0,2),(4,1,0),(4,1,3),(5,2,1),(1,3,0)]⟩
theorem node158 : UpperPrefix a [3,4,5,1] 30 :=
  local_sound a [3,4,5,1] 30 cert158 (by decide +kernel)

def cert159 : Local := ⟨⟨468,0,458,0,451,451,259,67,131⟩,[(1,3),(3,1)],[(3,0,2),(4,1,0),(5,2,1),(5,2,3),(2,3,0)]⟩
theorem node159 : UpperPrefix a [3,4,5,2] 30 :=
  local_sound a [3,4,5,2] 30 cert159 (by decide +kernel)

def cert160 : Local := ⟨⟨468,481,0,390,0,454,262,70,134⟩,[(2,4),(4,2)],[(3,0,2),(3,0,4),(4,1,0),(5,2,1),(0,4,1)]⟩
theorem node160 : UpperPrefix a [3,4,5,6,0] 30 :=
  local_sound a [3,4,5,6,0] 30 cert160 (by decide +kernel)

def cert161 : Leaf := ⟨⟨276,289,264,389,261,453,261,69,133⟩,[],[(3,0,2),(4,1,0),(5,2,1)],⟨11,22,37,88,50,429,453,389,453⟩,⟨11,22,37,88,50,40,192,384,320⟩,[⟨1,1233765604665561374261249,⟨493,476,485,88,56,40,192,384,320⟩⟩,⟨6,1210106412364820993047593,⟨11,22,55,31,55,63,128,384,256⟩⟩,⟨7,1208926973665608188591145,⟨11,22,55,95,55,63,64,256,320⟩⟩]⟩
theorem node161 : UpperPrefix a [3,4,5,6,1] 30 :=
  Boolean.leaf_sound a [3,4,5,6,1] 30 cert161 (by decide +kernel)

def cert162 : Local := ⟨⟨464,0,458,387,0,451,259,67,131⟩,[(1,4),(4,2)],[(3,0,2),(4,1,0),(5,2,1),(5,2,4),(2,4,1)]⟩
theorem node162 : UpperPrefix a [3,4,5,6,2] 30 :=
  local_sound a [3,4,5,6,2] 30 cert162 (by decide +kernel)

def cert163 : Local := ⟨⟨0,353,328,0,389,325,261,69,5⟩,[(0,3),(3,1)],[(3,0,2),(4,1,0),(4,1,3),(5,2,1),(1,3,0),(7,5,4)]⟩
theorem node163 : UpperPrefix a [3,4,5,1,6,7] 30 :=
  local_sound a [3,4,5,1,6,7] 30 cert163 (by decide +kernel)

def cert164 : Local := ⟨⟨340,0,330,0,387,323,259,67,3⟩,[(1,3),(3,1)],[(3,0,2),(4,1,0),(5,2,1),(5,2,3),(2,3,0),(7,5,4)]⟩
theorem node164 : UpperPrefix a [3,4,5,2,6,7] 30 :=
  local_sound a [3,4,5,2,6,7] 30 cert164 (by decide +kernel)

def cert165 : Leaf := ⟨⟨84,96,74,70,134,70,262,70,6⟩,[],[(3,0,2),(4,1,0),(5,2,1),(7,5,4)],⟨11,22,37,25,112,168,454,390,326⟩,⟨11,22,37,25,112,168,192,384,320⟩,[⟨0,1238497212535209712421888,⟨506,470,502,56,112,168,192,384,320⟩⟩,⟨8,1181752446674860750331,⟨11,31,37,31,127,175,255,191,127⟩⟩]⟩
theorem node165 : UpperPrefix a [3,4,5,0,6,7] 30 :=
  Boolean.leaf_sound a [3,4,5,0,6,7] 30 cert165 (by decide +kernel)

def cert166 : Local := ⟨⟨20,33,10,135,263,71,7,7,7⟩,[],[(3,0,2),(4,1,0),(5,2,1),(6,3,5),(7,4,3),(8,5,4)]⟩
theorem node166 : UpperPrefix a [3,4,5,6,7,8] 30 :=
  local_sound a [3,4,5,6,7,8] 30 cert166 (by decide +kernel)

theorem node167 : UpperPrefix a [3,4,5,6,7] 30 :=
  branch_upper a [3,4,5,6,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut21 [3,4,5,6,7,0] [3,4,5,1,6,7] 30 (by decide +kernel) node163)
  (PrefixConjugacy.upper aut21 [3,4,5,6,7,1] [3,4,5,2,6,7] 30 (by decide +kernel) node164)
  (PrefixConjugacy.upper aut21 [3,4,5,6,7,2] [3,4,5,0,6,7] 30 (by decide +kernel) node165)
  (invalid_upper a [3,4,5,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,7] 30 (by decide +kernel))
  node166)

def cert168 : Local := ⟨⟨0,481,456,0,389,197,261,69,133⟩,[(0,3),(3,1)],[(3,0,2),(4,1,0),(4,1,3),(5,2,1),(1,3,0)]⟩
theorem node168 : UpperPrefix a [3,4,5,1,6,8] 30 :=
  local_sound a [3,4,5,1,6,8] 30 cert168 (by decide +kernel)

def cert169 : Local := ⟨⟨468,0,458,0,387,195,259,67,131⟩,[(1,3),(3,1)],[(3,0,2),(4,1,0),(5,2,1),(5,2,3),(2,3,0)]⟩
theorem node169 : UpperPrefix a [3,4,5,2,6,8] 30 :=
  local_sound a [3,4,5,2,6,8] 30 cert169 (by decide +kernel)

def cert170 : Leaf := ⟨⟨340,352,330,326,262,70,262,70,134⟩,[],[(3,0,2),(4,1,0),(5,2,1)],⟨11,22,37,25,112,296,198,390,454⟩,⟨11,22,37,25,112,296,192,384,320⟩,[⟨0,1238497212535209712421888,⟨506,470,502,56,112,296,192,384,320⟩⟩,⟨7,1208926987195990360192511,⟨11,31,47,31,127,319,127,319,383⟩⟩]⟩
theorem node170 : UpperPrefix a [3,4,5,0,6,8] 30 :=
  Boolean.leaf_sound a [3,4,5,0,6,8] 30 cert170 (by decide +kernel)

def cert171 : Leaf := ⟨⟨20,33,10,135,71,263,7,7,7⟩,[],[(3,0,2),(4,1,0),(5,2,1)],⟨11,22,37,88,304,168,199,391,327⟩,⟨11,22,37,88,304,168,192,384,320⟩,[⟨6,1210253986596411747349545,⟨47,150,37,191,439,175,128,384,256⟩⟩,⟨7,1246705905528290472393769,⟨267,22,55,351,311,319,64,256,320⟩⟩,⟨8,1182322129976974914619,⟨11,31,101,95,127,239,192,128,64⟩⟩]⟩
theorem node171 : UpperPrefix a [3,4,5,6,8,7] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,7] 30 cert171 (by decide +kernel)

theorem node172 : UpperPrefix a [3,4,5,6,8] 30 :=
  branch_upper a [3,4,5,6,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut21 [3,4,5,6,8,0] [3,4,5,1,6,8] 30 (by decide +kernel) node168)
  (PrefixConjugacy.upper aut21 [3,4,5,6,8,1] [3,4,5,2,6,8] 30 (by decide +kernel) node169)
  (PrefixConjugacy.upper aut21 [3,4,5,6,8,2] [3,4,5,0,6,8] 30 (by decide +kernel) node170)
  (invalid_upper a [3,4,5,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,6] 30 (by decide +kernel))
  node171
  (invalid_upper a [3,4,5,6,8,8] 30 (by decide +kernel)))

theorem node173 : UpperPrefix a [3,4,5,6] 30 :=
  branch_upper a [3,4,5,6] 30 (by decide) (fin9_cases _
  node160
  node161
  node162
  (invalid_upper a [3,4,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,6] 30 (by decide +kernel))
  node167
  node172)

theorem node174 : UpperPrefix a [3,4,5] 30 :=
  branch_upper a [3,4,5] 30 (by decide) (fin9_cases _
  node157
  node158
  node159
  (invalid_upper a [3,4,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,5] 30 (by decide +kernel))
  node173
  (PrefixConjugacy.upper aut2 [3,4,5,7] [3,4,5,6] 30 (by decide +kernel) node173)
  (PrefixConjugacy.upper aut1 [3,4,5,8] [3,4,5,6] 30 (by decide +kernel) node173))

def cert175 : Leaf := ⟨⟨340,352,328,326,324,260,260,68,132⟩,[],[(3,0,2),(4,1,0),(5,2,1),(1,4,3)],⟨11,22,37,25,50,104,452,388,452⟩,⟨11,22,37,25,50,104,192,384,320⟩,[⟨0,1238497212535209712421888,⟨506,470,502,56,498,104,192,384,320⟩⟩,⟨7,1208926984955461077564927,⟨11,31,63,31,63,127,127,319,383⟩⟩]⟩
theorem node175 : UpperPrefix a [3,4,5,0,1,6] 30 :=
  Boolean.leaf_sound a [3,4,5,0,1,6] 30 cert175 (by decide +kernel)

def cert176 : Leaf := ⟨⟨240,232,168,226,200,64,40,104,168⟩,[],[(4,1,0),(1,4,3)],⟨11,22,69,25,50,168,196,416,352⟩,⟨11,22,69,25,50,168,196,384,320⟩,[⟨8,1184634761711203909119,⟨11,31,127,31,127,255,255,255,127⟩⟩,⟨0,1309544847616577027214336,⟨506,470,502,440,498,168,470,384,322⟩⟩,⟨2,1534235308464251833680915,⟨187,443,505,57,187,168,488,384,480⟩⟩]⟩
theorem node176 : UpperPrefix a [3,4,6,0,1,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,1,7,2] 30 cert176 (by decide +kernel)

def cert177 : Leaf := ⟨⟨116,105,40,102,77,69,0,109,45⟩,[(6,5)],[(4,1,0),(1,4,3),(7,5,6)],⟨11,22,69,25,50,168,224,388,324⟩,⟨11,22,69,25,50,168,224,384,320⟩,[⟨8,1184634761711203909119,⟨11,31,127,31,127,255,255,255,127⟩⟩]⟩
theorem node177 : UpperPrefix a [3,4,6,0,1,7,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,1,7,5] 30 cert177 (by decide +kernel)

def cert178 : Leaf := ⟨⟨212,193,128,198,197,69,0,101,165⟩,[(6,7)],[(4,1,0),(1,4,3),(8,6,6)],⟨11,22,69,25,50,168,448,420,356⟩,⟨11,22,69,25,50,168,448,384,320⟩,[⟨3,1361521611177195306243073,⟨7,86,69,87,498,502,448,448,320⟩⟩,⟨5,1210109870000963417285659,⟨11,31,69,27,31,205,448,448,320⟩⟩]⟩
theorem node178 : UpperPrefix a [3,4,6,0,1,7,8] 30 :=
  Boolean.leaf_sound a [3,4,6,0,1,7,8] 30 cert178 (by decide +kernel)

theorem node179 : UpperPrefix a [3,4,6,0,1,7] 30 :=
  branch_upper a [3,4,6,0,1,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,1,7,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,7,1] 30 (by decide +kernel))
  node176
  (invalid_upper a [3,4,6,0,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,7,4] 30 (by decide +kernel))
  node177
  (invalid_upper a [3,4,6,0,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,7,7] 30 (by decide +kernel))
  node178)

theorem node180 : UpperPrefix a [3,4,6,0,1] 30 :=
  branch_upper a [3,4,6,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut54 [3,4,6,0,1,2] [3,4,5,0,1,6] 30 (by decide +kernel) node175)
  (invalid_upper a [3,4,6,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,6] 30 (by decide +kernel))
  node179
  (PrefixConjugacy.upper aut55 [3,4,6,0,1,8] [3,4,6,0,1,7] 30 (by decide +kernel) node179))

def cert181 : Leaf := ⟨⟨464,0,418,450,450,450,290,98,162⟩,[(1,4)],[(4,1,0),(2,4,1)],⟨11,22,69,25,52,426,482,418,482⟩,⟨11,22,69,25,52,40,192,384,320⟩,[⟨0,1347324193810631187508224,⟨490,470,502,506,502,488,192,384,320⟩⟩,⟨3,1437224743012690092389377,⟨7,470,69,471,502,502,192,384,320⟩⟩,⟨5,1210107564157954195203099,⟨11,31,69,27,31,9,192,384,320⟩⟩]⟩
theorem node181 : UpperPrefix a [3,4,6,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,2] 30 cert181 (by decide +kernel)

def cert182 : Leaf := ⟨⟨0,232,170,102,78,0,302,110,46⟩,[(0,5),(5,0)],[(4,1,0),(4,1,5)],⟨11,22,69,25,176,42,484,420,356⟩,⟨11,22,69,25,176,42,192,384,320⟩,[⟨0,1229033996796530974002176,⟨42,470,502,56,176,42,192,384,320⟩⟩,⟨8,1181762254319071235575,⟨43,63,127,57,187,43,255,191,127⟩⟩,⟨7,1227816439700168387855395,⟨43,319,357,57,57,43,64,256,320⟩⟩]⟩
theorem node182 : UpperPrefix a [3,4,6,0,7,1] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,1] 30 cert182 (by decide +kernel)

def cert183 : Leaf := ⟨⟨52,224,162,38,70,3,294,102,166⟩,[],[(4,1,0),(0,3,5)],⟨11,22,69,25,176,44,482,418,354⟩,⟨11,22,69,25,176,44,192,384,320⟩,[⟨3,1437224743012690092381185,⟨7,470,69,471,498,502,192,384,320⟩⟩,⟨8,1181761656184745725431,⟨43,63,127,25,187,47,255,191,127⟩⟩,⟨6,1210106412432716091884547,⟨43,63,5,25,176,44,128,384,256⟩⟩,⟨7,1208926973733503287428099,⟨43,63,69,25,48,44,64,256,320⟩⟩]⟩
theorem node183 : UpperPrefix a [3,4,6,0,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,2] 30 cert183 (by decide +kernel)

def cert184 : Leaf := ⟨⟨212,193,130,196,325,197,5,101,165⟩,[],[(4,1,0),(8,5,4),(1,6,2)],⟨11,22,69,25,176,296,194,420,356⟩,⟨11,22,69,25,176,296,194,384,320⟩,[⟨3,1361519305334186092549121,⟨7,86,69,87,498,502,194,384,320⟩⟩,⟨5,1210107852388330437620859,⟨15,95,69,95,223,271,207,388,325⟩⟩]⟩
theorem node184 : UpperPrefix a [3,4,6,0,7,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,8,1] 30 cert184 (by decide +kernel)

def cert185 : Leaf := ⟨⟨180,160,162,166,262,134,34,38,166⟩,[],[(4,1,0),(8,5,4)],⟨11,22,69,25,176,296,196,418,354⟩,⟨11,22,69,25,176,296,196,384,320⟩,[⟨0,1233765622962327944989696,⟨506,470,502,440,176,312,470,384,322⟩⟩,⟨3,1437224634926299035751425,⟨71,470,69,471,498,502,196,384,320⟩⟩,⟨6,1212467609147631362673991,⟨11,31,31,25,184,441,191,441,443⟩⟩]⟩
theorem node185 : UpperPrefix a [3,4,6,0,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,8,2] 30 cert185 (by decide +kernel)

def cert186 : Leaf := ⟨⟨244,224,162,230,0,198,0,102,166⟩,[(4,6),(6,4)],[(4,1,0),(8,5,4),(8,5,6)],⟨11,22,69,25,176,296,224,390,326⟩,⟨11,22,69,25,176,296,224,384,320⟩,[⟨0,1238497482755585401162752,⟨506,470,502,120,240,296,240,384,336⟩⟩,⟨3,1427770786679311993691137,⟨391,470,471,471,498,502,498,384,336⟩⟩]⟩
theorem node186 : UpperPrefix a [3,4,6,0,7,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,8,5] 30 cert186 (by decide +kernel)

theorem node187 : UpperPrefix a [3,4,6,0,7,8] 30 :=
  branch_upper a [3,4,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,7,8,0] 30 (by decide +kernel))
  node184
  node185
  (invalid_upper a [3,4,6,0,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,8,4] 30 (by decide +kernel))
  node186
  (invalid_upper a [3,4,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,8,8] 30 (by decide +kernel)))

theorem node188 : UpperPrefix a [3,4,6,0,7] 30 :=
  branch_upper a [3,4,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,7,0] 30 (by decide +kernel))
  node182
  node183
  (invalid_upper a [3,4,6,0,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,7] 30 (by decide +kernel))
  node187)

def cert189 : Leaf := ⟨⟨0,360,298,322,78,0,302,110,174⟩,[(0,5),(5,0)],[(4,1,0),(4,1,5)],⟨11,22,69,25,304,42,228,420,484⟩,⟨11,22,69,25,304,42,192,384,320⟩,[⟨0,1229033996796530974002176,⟨42,470,502,56,304,42,192,384,320⟩⟩,⟨7,1208926990542899414017535,⟨43,63,111,59,319,43,127,319,383⟩⟩,⟨2,1210107565389407217255459,⟨43,59,97,57,313,43,192,384,320⟩⟩,⟨5,1210107564157954195194915,⟨11,31,69,25,281,11,192,384,320⟩⟩]⟩
theorem node189 : UpperPrefix a [3,4,6,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,1] 30 cert189 (by decide +kernel)

def cert190 : Leaf := ⟨⟨52,352,290,38,70,3,294,102,166⟩,[],[(4,1,0),(0,3,5)],⟨11,22,69,25,304,44,226,418,482⟩,⟨11,22,69,25,304,44,192,384,320⟩,[⟨3,1437224743012690092381185,⟨7,470,69,471,498,502,192,384,320⟩⟩,⟨7,1208926990226240065218015,⟨43,63,111,59,319,45,127,319,383⟩⟩,⟨6,1210106412432716091884547,⟨43,63,5,25,304,44,128,384,256⟩⟩,⟨8,1181745739591524025347,⟨43,63,69,25,48,44,192,128,64⟩⟩]⟩
theorem node190 : UpperPrefix a [3,4,6,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,2] 30 cert190 (by decide +kernel)

def cert191 : Leaf := ⟨⟨212,193,130,196,197,69,5,101,165⟩,[],[(4,1,0),(1,6,2)],⟨11,22,69,25,304,168,194,420,356⟩,⟨11,22,69,25,304,168,194,384,320⟩,[⟨3,1361519305334186092549121,⟨7,86,69,87,498,502,194,384,320⟩⟩,⟨8,1182324381777140921467,⟨11,31,101,31,127,239,239,132,101⟩⟩,⟨5,1210108140618706595099771,⟨11,31,69,31,351,207,207,388,325⟩⟩]⟩
theorem node191 : UpperPrefix a [3,4,6,0,8,7,1] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,7,1] 30 cert191 (by decide +kernel)

#print axioms node191
end Delivery.FiniteExclusion.Sharp3x3x3
