import RegularNineSharp2x7Base
import RegularNineSharp2x7C006
import RegularNineSharp2x7C007
import RegularNineSharp2x7C009
import RegularNineSharp2x7C011
import RegularNineSharp2x7C014
import RegularNineSharp2x7C015
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
theorem node1024 : UpperPrefix a [2,4,8,6,3] 30 :=
  branch_upper a [2,4,8,6,3] 30 (by decide) (fin9_cases _
  node1021
  node1022
  (invalid_upper a [2,4,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,6] 30 (by decide +kernel))
  node1023
  (invalid_upper a [2,4,8,6,3,8] 30 (by decide +kernel)))

def cert1025 : Leaf := ⟨⟨376,104,112,160,72,26,56,124,120⟩,[],[(7,4,3),(1,6,5)],⟨7,19,268,88,176,97,194,424,300⟩,⟨7,19,268,88,176,97,194,384,260⟩,[⟨0,1437223914350364306441216,⟨78,478,268,476,444,508,206,384,260⟩⟩,⟨2,1210107853589009928307713,⟨43,123,264,88,250,123,250,384,256⟩⟩,⟨8,1182033974380754650113,⟨47,123,12,88,250,123,250,128,4⟩⟩]⟩
theorem node1025 : UpperPrefix a [2,4,8,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,1] 30 cert1025 (by decide +kernel)

def cert1026 : Leaf := ⟨⟨344,332,80,384,329,280,272,92,120⟩,[],[(7,4,3)],⟨7,19,268,88,176,97,200,386,292⟩,⟨7,19,268,88,176,97,200,386,260⟩,[⟨1,2055413759870096633495553,⟨301,381,268,348,508,365,476,508,260⟩⟩,⟨5,1210147141791479560680661,⟨207,91,463,91,223,65,207,463,453⟩⟩,⟨0,1285686523870423069230080,⟨206,478,268,348,508,96,204,462,260⟩⟩,⟨2,1210110159436430073398273,⟨43,123,264,88,248,105,216,506,256⟩⟩]⟩
theorem node1026 : UpperPrefix a [2,4,8,6,7,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,3,1] 30 cert1026 (by decide +kernel)

def cert1027 : Leaf := ⟨⟨280,268,18,390,0,286,278,30,26⟩,[(4,7)],[(7,4,3),(5,7,4)],⟨7,19,268,88,176,97,200,416,262⟩,⟨7,19,268,88,176,97,200,416,260⟩,[⟨0,1224572983182805283111936,⟨270,350,268,88,252,508,220,508,260⟩⟩,⟨6,1725287080863902572082285,⟨263,403,271,415,435,439,415,435,261⟩⟩]⟩
theorem node1027 : UpperPrefix a [2,4,8,6,7,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,3,5] 30 cert1027 (by decide +kernel)

theorem node1028 : UpperPrefix a [2,4,8,6,7,0,3] 30 :=
  branch_upper a [2,4,8,6,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,7,0,3,0] 30 (by decide +kernel))
  node1026
  (invalid_upper a [2,4,8,6,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,3,4] 30 (by decide +kernel))
  node1027
  (invalid_upper a [2,4,8,6,7,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,3,8] 30 (by decide +kernel)))

def cert1029 : Leaf := ⟨⟨280,268,19,423,0,286,0,31,27⟩,[(4,6),(6,4)],[(7,4,3),(5,6,3)],⟨7,19,268,88,176,97,224,394,270⟩,⟨7,19,268,88,176,97,224,384,260⟩,[⟨6,1266885490625623127774221,⟨391,19,399,415,178,51,178,384,389⟩⟩]⟩
theorem node1029 : UpperPrefix a [2,4,8,6,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,5] 30 cert1029 (by decide +kernel)

theorem node1030 : UpperPrefix a [2,4,8,6,7,0] 30 :=
  branch_upper a [2,4,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,7,0,0] 30 (by decide +kernel))
  node1025
  (invalid_upper a [2,4,8,6,7,0,2] 30 (by decide +kernel))
  node1028
  (invalid_upper a [2,4,8,6,7,0,4] 30 (by decide +kernel))
  node1029
  (invalid_upper a [2,4,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,8] 30 (by decide +kernel)))

def cert1031 : Leaf := ⟨⟨376,104,112,160,72,25,312,120,120⟩,[],[(7,4,3),(0,6,5)],⟨7,19,268,88,176,98,193,424,300⟩,⟨7,19,268,88,176,98,193,384,260⟩,[⟨1,1437223914350364306440193,⟨77,477,268,476,444,508,193,384,260⟩⟩,⟨2,1210144479429980451800577,⟨251,123,440,122,184,122,251,384,400⟩⟩,⟨8,1181748206908233253889,⟨7,19,44,122,184,122,251,128,4⟩⟩]⟩
theorem node1031 : UpperPrefix a [2,4,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,0] 30 cert1031 (by decide +kernel)

def cert1032 : Leaf := ⟨⟨376,104,112,160,73,24,48,124,120⟩,[],[(2,0,7),(7,4,3)],⟨7,19,268,88,176,98,200,385,292⟩,⟨7,19,268,88,176,98,200,385,260⟩,[⟨1,1436800521942198098853889,⟨205,477,268,348,508,508,204,449,260⟩⟩,⟨0,1450948544210950919291904,⟨302,382,268,348,508,366,204,388,260⟩⟩,⟨8,1184347144552635761665,⟨47,123,12,120,250,122,250,251,4⟩⟩]⟩
theorem node1032 : UpperPrefix a [2,4,8,6,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,3,0] 30 cert1032 (by decide +kernel)

def cert1033 : Leaf := ⟨⟨280,268,17,389,0,285,277,29,25⟩,[(4,7)],[(7,4,3),(5,7,4)],⟨7,19,268,88,176,98,200,416,261⟩,⟨7,19,268,88,176,98,200,416,260⟩,[⟨1,1224572983182805283110913,⟨269,349,268,88,252,508,220,508,260⟩⟩,⟨6,1725287080863902572082285,⟨263,403,271,415,435,439,415,435,261⟩⟩]⟩
theorem node1033 : UpperPrefix a [2,4,8,6,7,1,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,3,5] 30 cert1033 (by decide +kernel)

theorem node1034 : UpperPrefix a [2,4,8,6,7,1,3] 30 :=
  branch_upper a [2,4,8,6,7,1,3] 30 (by decide) (fin9_cases _
  node1032
  (invalid_upper a [2,4,8,6,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,3,4] 30 (by decide +kernel))
  node1033
  (invalid_upper a [2,4,8,6,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,3,8] 30 (by decide +kernel)))

def cert1035 : Leaf := ⟨⟨280,268,19,423,0,285,0,31,27⟩,[(4,6),(6,4)],[(7,4,3),(5,6,3)],⟨7,19,268,88,176,98,224,393,269⟩,⟨7,19,268,88,176,98,224,384,260⟩,[⟨6,1266885490625623127757837,⟨391,19,399,415,176,50,176,384,389⟩⟩]⟩
theorem node1035 : UpperPrefix a [2,4,8,6,7,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,5] 30 cert1035 (by decide +kernel)

theorem node1036 : UpperPrefix a [2,4,8,6,7,1] 30 :=
  branch_upper a [2,4,8,6,7,1] 30 (by decide) (fin9_cases _
  node1031
  (invalid_upper a [2,4,8,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,2] 30 (by decide +kernel))
  node1034
  (invalid_upper a [2,4,8,6,7,1,4] 30 (by decide +kernel))
  node1035
  (invalid_upper a [2,4,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,8] 30 (by decide +kernel)))

def cert1037 : Leaf := ⟨⟨312,40,51,160,8,0,318,63,59⟩,[(5,3)],[(6,3,5),(7,4,3)],⟨7,19,268,88,176,104,193,418,294⟩,⟨7,19,268,88,176,104,193,384,260⟩,[⟨2,1210107567821537406911489,⟨3,19,296,122,184,122,251,384,256⟩⟩,⟨8,1181748206908233253889,⟨7,19,44,122,184,122,251,128,4⟩⟩,⟨0,1210107567821537407927296,⟨6,18,300,120,184,120,248,384,260⟩⟩,⟨1,1210107567821537407926273,⟨5,17,300,120,184,120,249,384,260⟩⟩]⟩
theorem node1037 : UpperPrefix a [2,4,8,6,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,3,0] 30 cert1037 (by decide +kernel)

def cert1038 : Leaf := ⟨⟨312,296,48,416,264,0,313,60,56⟩,[(5,3)],[(2,0,7),(6,3,5),(7,4,3),(0,7,6)],⟨7,19,268,88,176,104,194,385,292⟩,⟨7,19,268,88,176,104,194,385,260⟩,[⟨1,1795708681813484010209281,⟨389,405,300,380,444,380,508,385,260⟩⟩]⟩
theorem node1038 : UpperPrefix a [2,4,8,6,7,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,3,1,0] 30 cert1038 (by decide +kernel)

def cert1039 : Local := ⟨⟨280,268,19,391,0,0,285,31,27⟩,[(4,7),(5,3)],[(6,3,5),(7,4,3),(5,7,4)]⟩
theorem node1039 : UpperPrefix a [2,4,8,6,7,3,1,5] 30 :=
  local_sound a [2,4,8,6,7,3,1,5] 30 cert1039 (by decide +kernel)

theorem node1040 : UpperPrefix a [2,4,8,6,7,3,1] 30 :=
  branch_upper a [2,4,8,6,7,3,1] 30 (by decide) (fin9_cases _
  node1038
  (invalid_upper a [2,4,8,6,7,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,4] 30 (by decide +kernel))
  node1039
  (invalid_upper a [2,4,8,6,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,8] 30 (by decide +kernel)))

def cert1041 : Local := ⟨⟨280,268,19,423,0,0,0,31,27⟩,[(4,6),(5,3),(6,4)],[(6,3,5),(7,4,3),(5,6,3)]⟩
theorem node1041 : UpperPrefix a [2,4,8,6,7,3,5] 30 :=
  local_sound a [2,4,8,6,7,3,5] 30 cert1041 (by decide +kernel)

theorem node1042 : UpperPrefix a [2,4,8,6,7,3] 30 :=
  branch_upper a [2,4,8,6,7,3] 30 (by decide) (fin9_cases _
  node1037
  node1040
  (invalid_upper a [2,4,8,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,4] 30 (by decide +kernel))
  node1041
  (invalid_upper a [2,4,8,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,8] 30 (by decide +kernel)))

theorem node1043 : UpperPrefix a [2,4,8,6,7] 30 :=
  branch_upper a [2,4,8,6,7] 30 (by decide) (fin9_cases _
  node1030
  node1036
  (invalid_upper a [2,4,8,6,7,2] 30 (by decide +kernel))
  node1042
  (invalid_upper a [2,4,8,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,8] 30 (by decide +kernel)))

theorem node1044 : UpperPrefix a [2,4,8,6] 30 :=
  branch_upper a [2,4,8,6] 30 (by decide) (fin9_cases _
  node1006
  node1018
  (invalid_upper a [2,4,8,6,2] 30 (by decide +kernel))
  node1024
  (invalid_upper a [2,4,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,6] 30 (by decide +kernel))
  node1043
  (invalid_upper a [2,4,8,6,8] 30 (by decide +kernel)))

def cert1045 : Leaf := ⟨⟨248,0,240,96,202,152,56,120,248⟩,[(1,4)],[(0,4,1),(1,5,4)],⟨7,19,268,152,49,98,232,488,364⟩,⟨7,19,268,152,49,98,192,384,260⟩,[⟨2,1210144693909364066493953,⟨251,123,488,250,123,114,192,384,448⟩⟩,⟨8,1184202831789353545477,⟨55,19,127,250,51,106,250,251,55⟩⟩]⟩
theorem node1045 : UpperPrefix a [2,4,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,1] 30 cert1045 (by decide +kernel)

def cert1046 : Leaf := ⟨⟨120,0,114,98,74,146,56,122,122⟩,[(1,4)],[(7,3,5),(0,4,1)],⟨7,19,268,152,49,104,194,480,356⟩,⟨7,19,268,152,49,104,194,384,260⟩,[⟨2,1210144624244315920541185,⟨251,123,488,250,123,104,250,384,416⟩⟩,⟨8,1184202831789353545477,⟨55,19,127,250,51,104,250,251,55⟩⟩]⟩
theorem node1046 : UpperPrefix a [2,4,8,7,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,3,1] 30 cert1046 (by decide +kernel)

def cert1047 : Leaf := ⟨⟨88,0,82,70,78,150,30,94,90⟩,[(1,4)],[(7,3,5),(0,4,1)],⟨7,19,268,152,49,104,224,450,326⟩,⟨7,19,268,152,49,104,224,384,260⟩,[⟨5,1361518439514961939018815,⟨7,31,271,159,415,463,453,384,261⟩⟩,⟨8,1184202831789353545477,⟨55,19,127,250,51,104,250,251,55⟩⟩]⟩
theorem node1047 : UpperPrefix a [2,4,8,7,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,3,5] 30 cert1047 (by decide +kernel)

theorem node1048 : UpperPrefix a [2,4,8,7,0,3] 30 :=
  branch_upper a [2,4,8,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,0,3,0] 30 (by decide +kernel))
  node1046
  (invalid_upper a [2,4,8,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,4] 30 (by decide +kernel))
  node1047
  (invalid_upper a [2,4,8,7,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,3,8] 30 (by decide +kernel)))

theorem node1049 : UpperPrefix a [2,4,8,7,0] 30 :=
  branch_upper a [2,4,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,0,0] 30 (by decide +kernel))
  node1045
  (invalid_upper a [2,4,8,7,0,2] 30 (by decide +kernel))
  node1048
  (invalid_upper a [2,4,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,8] 30 (by decide +kernel)))

def cert1050 : Leaf := ⟨⟨120,108,112,100,77,28,0,124,120⟩,[(6,3)],[(7,3,6),(1,4,1),(0,5,4)],⟨7,19,268,152,50,97,200,480,356⟩,⟨7,19,268,152,50,97,200,384,260⟩,[⟨8,1184200305661388738309,⟨55,19,127,250,50,123,250,251,55⟩⟩]⟩
theorem node1050 : UpperPrefix a [2,4,8,7,1,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,0,3] 30 cert1050 (by decide +kernel)

def cert1051 : Leaf := ⟨⟨240,160,240,32,129,148,20,124,248⟩,[],[(1,4,1),(0,5,4)],⟨7,19,268,152,50,97,224,456,332⟩,⟨7,19,268,152,50,97,224,384,260⟩,[⟨8,1184200305661388738309,⟨55,19,127,250,50,123,250,251,55⟩⟩,⟨3,1210110019920263719898885,⟨55,19,375,242,50,115,242,499,311⟩⟩,⟨2,1210107565290457344787457,⟨3,19,264,152,50,123,250,384,256⟩⟩,⟨6,1210106412368952738989057,⟨7,19,268,152,50,59,186,384,260⟩⟩]⟩
theorem node1051 : UpperPrefix a [2,4,8,7,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,0,5] 30 cert1051 (by decide +kernel)

theorem node1052 : UpperPrefix a [2,4,8,7,1,0] 30 :=
  branch_upper a [2,4,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,2] 30 (by decide +kernel))
  node1050
  (invalid_upper a [2,4,8,7,1,0,4] 30 (by decide +kernel))
  node1051
  (invalid_upper a [2,4,8,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,0,8] 30 (by decide +kernel)))

def cert1053 : Leaf := ⟨⟨104,108,96,100,77,133,44,108,104⟩,[],[(7,3,5),(1,4,1)],⟨7,19,268,152,50,104,193,480,356⟩,⟨7,19,268,152,50,104,193,384,260⟩,[⟨4,1498735033243020905415697,⟨487,451,492,493,487,492,449,384,420⟩⟩,⟨8,1184058565349709418245,⟨23,19,63,250,50,122,251,251,23⟩⟩,⟨0,1361518440640861845849088,⟨6,30,268,156,446,492,192,384,260⟩⟩]⟩
theorem node1053 : UpperPrefix a [2,4,8,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,3,0] 30 cert1053 (by decide +kernel)

def cert1054 : Leaf := ⟨⟨72,76,65,69,77,133,13,77,73⟩,[],[(7,3,5),(1,4,1)],⟨7,19,268,152,50,104,224,449,325⟩,⟨7,19,268,152,50,104,224,384,260⟩,[⟨4,1328416857700009937732625,⟨487,451,492,493,487,492,228,384,356⟩⟩,⟨5,1664340190228977938347071,⟨7,31,271,159,415,463,453,384,261⟩⟩,⟨8,1184202836737155862277,⟨55,19,127,250,50,120,250,251,55⟩⟩]⟩
theorem node1054 : UpperPrefix a [2,4,8,7,1,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,3,5] 30 cert1054 (by decide +kernel)

theorem node1055 : UpperPrefix a [2,4,8,7,1,3] 30 :=
  branch_upper a [2,4,8,7,1,3] 30 (by decide) (fin9_cases _
  node1053
  (invalid_upper a [2,4,8,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,4] 30 (by decide +kernel))
  node1054
  (invalid_upper a [2,4,8,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,8] 30 (by decide +kernel)))

theorem node1056 : UpperPrefix a [2,4,8,7,1] 30 :=
  branch_upper a [2,4,8,7,1] 30 (by decide) (fin9_cases _
  node1052
  (invalid_upper a [2,4,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,2] 30 (by decide +kernel))
  node1055
  (invalid_upper a [2,4,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,8] 30 (by decide +kernel)))

def cert1057 : Leaf := ⟨⟨152,140,144,36,132,158,28,92,216⟩,[],[(1,6,5),(5,7,3)],⟨7,19,268,152,56,97,194,416,324⟩,⟨7,19,268,152,56,97,194,416,260⟩,[⟨0,1678064604985540271145984,⟨334,478,268,156,444,508,478,444,260⟩⟩,⟨8,1184200288000483217157,⟨55,19,127,250,122,123,250,251,55⟩⟩,⟨6,1210106412373367999034573,⟨7,19,271,159,59,59,159,447,261⟩⟩]⟩
theorem node1057 : UpperPrefix a [2,4,8,7,3,0,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,0,1,5] 30 cert1057 (by decide +kernel)

def cert1058 : Leaf := ⟨⟨104,108,96,100,68,14,44,44,104⟩,[],[(1,6,5)],⟨7,19,268,152,56,97,194,448,292⟩,⟨7,19,268,152,56,97,194,448,260⟩,[⟨0,1437094805156248996545536,⟨206,478,268,412,444,508,206,448,260⟩⟩,⟨4,1300745698689472521044995,⟨487,487,268,396,428,481,483,480,260⟩⟩,⟨7,1322263776007954963119391,⟨7,279,287,319,319,97,99,353,263⟩⟩,⟨8,1184200288000483217157,⟨55,19,127,250,122,123,250,251,55⟩⟩]⟩
theorem node1058 : UpperPrefix a [2,4,8,7,3,0,1,6] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,0,1,6] 30 cert1058 (by decide +kernel)

theorem node1059 : UpperPrefix a [2,4,8,7,3,0,1] 30 :=
  branch_upper a [2,4,8,7,3,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,3,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,1,4] 30 (by decide +kernel))
  node1057
  node1058
  (invalid_upper a [2,4,8,7,3,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,1,8] 30 (by decide +kernel)))

def cert1060 : Leaf := ⟨⟨232,232,224,96,192,134,7,101,224⟩,[],[],⟨7,19,268,152,56,97,224,386,324⟩,⟨7,19,268,152,56,97,224,386,260⟩,[⟨4,1356531681439119611790339,⟨487,487,332,492,364,481,224,483,260⟩⟩,⟨8,1184200288000483217157,⟨55,19,127,250,122,123,250,251,55⟩⟩,⟨0,1663454747645943315694592,⟨6,22,268,156,316,380,508,386,260⟩⟩,⟨1,1663454747645943315693569,⟨5,21,268,156,316,381,508,384,260⟩⟩,⟨3,1214860538335340983747585,⟨487,499,260,208,112,481,224,482,260⟩⟩,⟨2,1210107565290457344787457,⟨3,19,264,152,58,123,250,386,256⟩⟩]⟩
theorem node1060 : UpperPrefix a [2,4,8,7,3,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,0,5,1] 30 cert1060 (by decide +kernel)

def cert1061 : Leaf := ⟨⟨24,12,18,6,6,30,30,30,26⟩,[],[(6,7,6)],⟨7,19,268,152,56,97,224,448,262⟩,⟨7,19,268,152,56,97,224,448,260⟩,[⟨0,1224589124079471732458496,⟨398,478,268,220,252,508,252,476,260⟩⟩,⟨5,1356796073032092288037919,⟨263,287,271,415,415,449,192,448,261⟩⟩,⟨7,1355320339136242665930015,⟨263,279,287,319,319,353,96,353,263⟩⟩,⟨8,1184200288000483217157,⟨55,19,127,250,122,123,250,251,55⟩⟩]⟩
theorem node1061 : UpperPrefix a [2,4,8,7,3,0,5,6] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,0,5,6] 30 cert1061 (by decide +kernel)

theorem node1062 : UpperPrefix a [2,4,8,7,3,0,5] 30 :=
  branch_upper a [2,4,8,7,3,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,3,0,5,0] 30 (by decide +kernel))
  node1060
  (invalid_upper a [2,4,8,7,3,0,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,5,5] 30 (by decide +kernel))
  node1061
  (invalid_upper a [2,4,8,7,3,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,5,8] 30 (by decide +kernel)))

theorem node1063 : UpperPrefix a [2,4,8,7,3,0] 30 :=
  branch_upper a [2,4,8,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,3,0,0] 30 (by decide +kernel))
  node1059
  (invalid_upper a [2,4,8,7,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,4] 30 (by decide +kernel))
  node1062
  (invalid_upper a [2,4,8,7,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,0,8] 30 (by decide +kernel)))

def cert1064 : Leaf := ⟨⟨232,232,224,96,192,137,46,108,232⟩,[],[(0,6,5)],⟨7,19,268,152,56,98,193,480,356⟩,⟨7,19,268,152,56,98,193,384,260⟩,[⟨4,1300893846851014687196163,⟨487,487,268,396,492,483,481,384,260⟩⟩,⟨8,1184058565349709418245,⟨23,19,63,250,56,122,251,251,23⟩⟩,⟨1,1361518440643065164070913,⟨5,29,268,156,444,508,193,384,260⟩⟩,⟨2,1210107567542257158489089,⟨3,19,264,152,56,122,251,384,256⟩⟩]⟩
theorem node1064 : UpperPrefix a [2,4,8,7,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,1,0] 30 cert1064 (by decide +kernel)

def cert1065 : Leaf := ⟨⟨200,200,193,65,193,137,9,76,201⟩,[],[(2,0,7)],⟨7,19,268,152,56,98,224,385,324⟩,⟨7,19,268,152,56,98,224,385,260⟩,[⟨1,1739031634576688218112001,⟨141,413,268,412,380,508,508,385,260⟩⟩,⟨4,1337937503024408832246787,⟨487,487,268,460,492,483,224,481,260⟩⟩,⟨5,1666885840911150124905535,⟨143,159,399,159,415,463,453,385,389⟩⟩,⟨8,1184202821275273596677,⟨55,19,127,250,120,122,250,251,55⟩⟩]⟩
theorem node1065 : UpperPrefix a [2,4,8,7,3,1,5,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,1,5,0] 30 cert1065 (by decide +kernel)

def cert1066 : Leaf := ⟨⟨152,140,145,5,133,149,21,21,145⟩,[],[(6,7,6)],⟨7,19,268,152,56,98,224,448,261⟩,⟨7,19,268,152,56,98,224,448,260⟩,[⟨1,1224589124079471732457473,⟨397,477,268,220,252,508,252,476,260⟩⟩,⟨5,1508502096294279640527935,⟨263,287,271,415,415,455,449,448,261⟩⟩,⟨8,1184202821275273596677,⟨55,19,127,250,120,122,250,251,55⟩⟩,⟨3,1214858232492331770053633,⟨487,499,260,144,112,226,224,448,260⟩⟩]⟩
theorem node1066 : UpperPrefix a [2,4,8,7,3,1,5,6] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,1,5,6] 30 cert1066 (by decide +kernel)

theorem node1067 : UpperPrefix a [2,4,8,7,3,1,5] 30 :=
  branch_upper a [2,4,8,7,3,1,5] 30 (by decide) (fin9_cases _
  node1065
  (invalid_upper a [2,4,8,7,3,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,5] 30 (by decide +kernel))
  node1066
  (invalid_upper a [2,4,8,7,3,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,5,8] 30 (by decide +kernel)))

theorem node1068 : UpperPrefix a [2,4,8,7,3,1] 30 :=
  branch_upper a [2,4,8,7,3,1] 30 (by decide) (fin9_cases _
  node1064
  (invalid_upper a [2,4,8,7,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,4] 30 (by decide +kernel))
  node1067
  (invalid_upper a [2,4,8,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,8] 30 (by decide +kernel)))

theorem node1069 : UpperPrefix a [2,4,8,7,3] 30 :=
  branch_upper a [2,4,8,7,3] 30 (by decide) (fin9_cases _
  node1063
  node1068
  (invalid_upper a [2,4,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,8] 30 (by decide +kernel)))

def cert1070 : Leaf := ⟨⟨184,172,176,36,0,158,60,60,184⟩,[(4,5)],[(6,4,4),(1,6,5)],⟨7,19,268,152,112,97,194,424,300⟩,⟨7,19,268,152,112,97,194,384,260⟩,[⟨0,1437223914350366453924864,⟨78,478,268,412,508,508,206,384,260⟩⟩,⟨8,1184200288000483217157,⟨55,19,127,250,122,123,250,251,55⟩⟩]⟩
theorem node1070 : UpperPrefix a [2,4,8,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,0,1] 30 cert1070 (by decide +kernel)

def cert1071 : Leaf := ⟨⟨56,44,51,39,0,30,0,63,59⟩,[(4,5),(6,3)],[(7,3,6),(6,4,4)],⟨7,19,268,152,112,97,200,418,294⟩,⟨7,19,268,152,112,97,200,384,260⟩,[⟨8,1184200288000483217157,⟨55,19,127,250,122,123,250,251,55⟩⟩]⟩
theorem node1071 : UpperPrefix a [2,4,8,7,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,0,3] 30 cert1071 (by decide +kernel)

def cert1072 : Leaf := ⟨⟨152,140,146,6,0,158,30,30,154⟩,[(4,5)],[(6,4,4),(5,6,4)],⟨7,19,268,152,112,97,224,394,270⟩,⟨7,19,268,152,112,97,224,384,260⟩,[⟨0,1224302911315933721789440,⟨398,414,268,152,124,508,252,384,260⟩⟩,⟨8,1184200288000483217157,⟨55,19,127,250,122,123,250,251,55⟩⟩]⟩
theorem node1072 : UpperPrefix a [2,4,8,7,6,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,0,5] 30 cert1072 (by decide +kernel)

theorem node1073 : UpperPrefix a [2,4,8,7,6,0] 30 :=
  branch_upper a [2,4,8,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,6,0,0] 30 (by decide +kernel))
  node1070
  (invalid_upper a [2,4,8,7,6,0,2] 30 (by decide +kernel))
  node1071
  (invalid_upper a [2,4,8,7,6,0,4] 30 (by decide +kernel))
  node1072
  (invalid_upper a [2,4,8,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,0,8] 30 (by decide +kernel)))

def cert1074 : Leaf := ⟨⟨312,300,48,292,0,285,316,60,56⟩,[(4,5)],[(6,4,4),(0,6,5)],⟨7,19,268,152,112,98,193,424,300⟩,⟨7,19,268,152,112,98,193,384,260⟩,[⟨1,1437223914350366453923841,⟨77,477,268,412,508,508,193,384,260⟩⟩,⟨7,1246705908347438275531789,⟨7,51,271,319,114,114,115,256,261⟩⟩]⟩
theorem node1074 : UpperPrefix a [2,4,8,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,1,0] 30 cert1074 (by decide +kernel)

def cert1075 : Leaf := ⟨⟨56,44,51,39,0,29,0,63,59⟩,[(4,5),(6,3)],[(7,3,6),(6,4,4)],⟨7,19,268,152,112,98,200,417,293⟩,⟨7,19,268,152,112,98,200,384,260⟩,[⟨8,1184202821275273596677,⟨55,19,127,250,120,122,250,251,55⟩⟩]⟩
theorem node1075 : UpperPrefix a [2,4,8,7,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,1,3] 30 cert1075 (by decide +kernel)

def cert1076 : Leaf := ⟨⟨152,140,145,5,0,157,29,29,153⟩,[(4,5)],[(6,4,4),(5,6,4)],⟨7,19,268,152,112,98,224,393,269⟩,⟨7,19,268,152,112,98,224,384,260⟩,[⟨1,1224302911315933721788417,⟨397,413,268,152,124,508,252,384,260⟩⟩,⟨8,1184202821275273596677,⟨55,19,127,250,120,122,250,251,55⟩⟩]⟩
theorem node1076 : UpperPrefix a [2,4,8,7,6,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,1,5] 30 cert1076 (by decide +kernel)

theorem node1077 : UpperPrefix a [2,4,8,7,6,1] 30 :=
  branch_upper a [2,4,8,7,6,1] 30 (by decide) (fin9_cases _
  node1074
  (invalid_upper a [2,4,8,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,2] 30 (by decide +kernel))
  node1075
  (invalid_upper a [2,4,8,7,6,1,4] 30 (by decide +kernel))
  node1076
  (invalid_upper a [2,4,8,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,8] 30 (by decide +kernel)))

def cert1078 : Leaf := ⟨⟨56,44,51,32,0,144,63,63,59⟩,[(4,5)],[(7,3,5),(6,4,4)],⟨7,19,268,152,112,104,227,419,295⟩,⟨7,19,268,152,112,104,192,384,260⟩,[⟨8,1184059128024784768261,⟨7,51,63,250,120,120,250,251,7⟩⟩,⟨0,1210107568105207112926208,⟨6,50,268,184,120,120,248,384,260⟩⟩,⟨1,1210107568105207112925185,⟨5,49,268,184,120,120,248,384,260⟩⟩,⟨2,1210107568105207111877633,⟨3,51,264,184,120,120,248,384,256⟩⟩]⟩
theorem node1078 : UpperPrefix a [2,4,8,7,6,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,3] 30 cert1078 (by decide +kernel)

theorem node1079 : UpperPrefix a [2,4,8,7,6] 30 :=
  branch_upper a [2,4,8,7,6] 30 (by decide) (fin9_cases _
  node1073
  node1077
  (invalid_upper a [2,4,8,7,6,2] 30 (by decide +kernel))
  node1078
  (invalid_upper a [2,4,8,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,8] 30 (by decide +kernel)))

theorem node1080 : UpperPrefix a [2,4,8,7] 30 :=
  branch_upper a [2,4,8,7] 30 (by decide) (fin9_cases _
  node1049
  node1056
  (invalid_upper a [2,4,8,7,2] 30 (by decide +kernel))
  node1069
  (invalid_upper a [2,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,5] 30 (by decide +kernel))
  node1079
  (invalid_upper a [2,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,8] 30 (by decide +kernel)))

theorem node1081 : UpperPrefix a [2,4,8] 30 :=
  branch_upper a [2,4,8] 30 (by decide) (fin9_cases _
  node951
  node971
  (invalid_upper a [2,4,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,4] 30 (by decide +kernel))
  node997
  node1044
  node1080
  (invalid_upper a [2,4,8,8] 30 (by decide +kernel)))

theorem node1082 : UpperPrefix a [2,4] 30 :=
  branch_upper a [2,4] 30 (by decide) (fin9_cases _
  node447
  node477
  (invalid_upper a [2,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,4] 30 (by decide +kernel))
  node605
  node762
  node942
  node1081)

def cert1083 : Leaf := ⟨⟨8,28,2,36,460,412,284,92,216⟩,[],[(5,1,3),(0,2,0),(1,3,2)],⟨7,35,13,26,504,504,472,472,476⟩,⟨7,35,13,26,48,96,192,384,260⟩,[⟨6,1210106412362349233054745,⟨7,35,13,31,63,32,128,384,260⟩⟩,⟨7,1208926973663136428598297,⟨7,35,13,31,63,96,64,256,260⟩⟩,⟨8,1181745669224665195545,⟨7,35,13,31,63,96,192,128,4⟩⟩,⟨4,1210107565282752176587785,⟨7,35,13,15,32,96,192,384,260⟩⟩]⟩
theorem node1083 : UpperPrefix a [2,5,0,1] 30 :=
  Boolean.leaf_sound a [2,5,0,1] 30 cert1083 (by decide +kernel)

def cert1084 : Local := ⟨⟨408,412,402,390,0,0,286,30,154⟩,[(4,1),(5,3)],[(5,1,4),(0,2,0),(6,3,5)]⟩
theorem node1084 : UpperPrefix a [2,5,0,6,1,3] 30 :=
  local_sound a [2,5,0,6,1,3] 30 cert1084 (by decide +kernel)

def cert1085 : Leaf := ⟨⟨472,476,464,0,0,0,284,92,216⟩,[(3,5),(4,1),(5,3)],[(5,1,4),(0,2,0)],⟨7,35,13,88,50,112,456,392,396⟩,⟨7,35,13,88,50,112,192,384,260⟩,[⟨1,1314572594710407837908993,⟨453,493,493,504,508,504,192,384,452⟩⟩]⟩
theorem node1085 : UpperPrefix a [2,5,0,6,1,4] 30 :=
  Boolean.leaf_sound a [2,5,0,6,1,4] 30 cert1085 (by decide +kernel)

def cert1086 : Local := ⟨⟨344,348,338,262,0,0,286,94,90⟩,[(4,1),(5,6)],[(5,1,4),(0,2,0),(7,5,5)]⟩
theorem node1086 : UpperPrefix a [2,5,0,6,1,7] 30 :=
  local_sound a [2,5,0,6,1,7] 30 cert1086 (by decide +kernel)

def cert1087 : Leaf := ⟨⟨280,284,274,262,0,158,278,30,154⟩,[(4,1)],[(5,1,4),(0,2,0)],⟨7,35,13,88,50,352,200,400,404⟩,⟨7,35,13,88,50,352,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩,⟨7,1208926973665475063997499,⟨23,63,13,95,63,383,77,256,260⟩⟩]⟩
theorem node1087 : UpperPrefix a [2,5,0,6,1,8,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,1,8,3] 30 cert1087 (by decide +kernel)

#print axioms node1087
end Delivery.FiniteExclusion.Sharp2x7
