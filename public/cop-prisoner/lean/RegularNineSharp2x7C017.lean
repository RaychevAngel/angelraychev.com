import RegularNineSharp2x7Base
import RegularNineSharp2x7C016
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert1088 : Local := ⟨⟨456,460,450,0,0,142,270,78,202⟩,[(3,6),(4,1)],[(5,1,4),(0,2,0),(4,6,3)]⟩
theorem node1088 : UpperPrefix a [2,5,0,6,1,8,4] 30 :=
  local_sound a [2,5,0,6,1,8,4] 30 cert1088 (by decide +kernel)

theorem node1089 : UpperPrefix a [2,5,0,6,1,8] 30 :=
  branch_upper a [2,5,0,6,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,8,2] 30 (by decide +kernel))
  node1087
  node1088
  (invalid_upper a [2,5,0,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,8,8] 30 (by decide +kernel)))

theorem node1090 : UpperPrefix a [2,5,0,6,1] 30 :=
  branch_upper a [2,5,0,6,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,2] 30 (by decide +kernel))
  node1084
  node1085
  (invalid_upper a [2,5,0,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,1,6] 30 (by decide +kernel))
  node1086
  node1089)

def cert1091 : Leaf := ⟨⟨40,12,32,32,64,414,318,62,186⟩,[],[(0,2,0),(6,3,4)],⟨7,35,13,88,56,498,466,402,406⟩,⟨7,35,13,88,56,96,192,384,260⟩,[⟨7,1208926973665475047220283,⟨23,63,13,95,63,127,64,256,260⟩⟩,⟨8,1181745671563283817531,⟨23,63,13,95,63,127,192,128,4⟩⟩,⟨1,1210107565286192443817985,⟨21,61,13,88,56,120,192,384,260⟩⟩,⟨4,1210107565282752180790297,⟨7,35,13,79,47,96,192,384,260⟩⟩,⟨2,1210107565286192442246145,⟨19,59,9,88,56,120,192,384,256⟩⟩]⟩
theorem node1091 : UpperPrefix a [2,5,0,6,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,3] 30 cert1091 (by decide +kernel)

def cert1092 : Leaf := ⟨⟨104,76,96,164,76,12,316,124,120⟩,[],[(0,2,0),(7,4,3),(1,5,1)],⟨7,35,13,88,176,98,472,408,284⟩,⟨7,35,13,88,176,98,192,384,260⟩,[⟨8,1181748206908265266559,⟨7,47,47,127,191,127,255,129,7⟩⟩,⟨4,1210107565564227153304845,⟨7,35,47,111,160,98,192,385,263⟩⟩]⟩
theorem node1092 : UpperPrefix a [2,5,0,6,7,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,1] 30 cert1092 (by decide +kernel)

def cert1093 : Leaf := ⟨⟨56,24,50,162,10,0,314,58,58⟩,[(5,3)],[(0,2,0),(6,3,5),(7,4,3)],⟨7,35,13,88,176,104,466,402,278⟩,⟨7,35,13,88,176,104,192,384,260⟩,[⟨2,1212473376286229357661185,⟨3,43,43,120,184,120,248,504,506⟩⟩,⟨8,1181748206908265266559,⟨7,47,47,127,191,127,255,129,7⟩⟩]⟩
theorem node1093 : UpperPrefix a [2,5,0,6,7,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,3] 30 cert1093 (by decide +kernel)

def cert1094 : Leaf := ⟨⟨344,344,338,0,330,0,282,90,90⟩,[(3,5),(5,3)],[(0,2,0),(7,4,3),(7,4,5)],⟨7,35,13,88,176,112,458,394,270⟩,⟨7,35,13,88,176,112,192,384,260⟩,[⟨5,1219570779896566093710339,⟨455,463,13,88,152,88,192,384,260⟩⟩,⟨2,1212473376286229357661185,⟨3,43,43,120,184,120,248,504,506⟩⟩]⟩
theorem node1094 : UpperPrefix a [2,5,0,6,7,4] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,4] 30 cert1094 (by decide +kernel)

def cert1095 : Leaf := ⟨⟨120,92,112,160,328,28,56,120,120⟩,[],[(0,2,0),(7,4,3),(8,5,4)],⟨7,35,13,88,176,352,194,408,284⟩,⟨7,35,13,88,176,352,194,384,260⟩,[⟨1,1541687792549627694678017,⟨405,445,445,504,184,504,508,384,404⟩⟩,⟨2,1210402749220177806623745,⟨91,251,9,88,184,504,218,384,256⟩⟩]⟩
theorem node1095 : UpperPrefix a [2,5,0,6,7,8,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,8,1] 30 cert1095 (by decide +kernel)

def cert1096 : Leaf := ⟨⟨56,28,48,164,268,28,52,62,58⟩,[],[(0,2,0),(7,4,3),(8,5,4)],⟨7,35,13,88,176,352,200,402,278⟩,⟨7,35,13,88,176,352,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩,⟨1,1210110163874063031205889,⟨5,45,13,88,248,376,248,504,260⟩⟩]⟩
theorem node1096 : UpperPrefix a [2,5,0,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,8,3] 30 cert1096 (by decide +kernel)

def cert1097 : Local := ⟨⟨104,76,98,0,334,14,0,110,106⟩,[(3,6),(6,4)],[(0,2,0),(7,4,3),(7,4,6),(8,5,4),(4,6,3)]⟩
theorem node1097 : UpperPrefix a [2,5,0,6,7,8,4] 30 :=
  local_sound a [2,5,0,6,7,8,4] 30 cert1097 (by decide +kernel)

theorem node1098 : UpperPrefix a [2,5,0,6,7,8] 30 :=
  branch_upper a [2,5,0,6,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,7,8,0] 30 (by decide +kernel))
  node1095
  (invalid_upper a [2,5,0,6,7,8,2] 30 (by decide +kernel))
  node1096
  node1097
  (invalid_upper a [2,5,0,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,8,8] 30 (by decide +kernel)))

theorem node1099 : UpperPrefix a [2,5,0,6,7] 30 :=
  branch_upper a [2,5,0,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,7,0] 30 (by decide +kernel))
  node1092
  (invalid_upper a [2,5,0,6,7,2] 30 (by decide +kernel))
  node1093
  node1094
  (invalid_upper a [2,5,0,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,7] 30 (by decide +kernel))
  node1098)

def cert1100 : Leaf := ⟨⟨104,72,96,416,200,8,312,120,248⟩,[],[(0,2,0),(1,5,1)],⟨7,35,13,88,304,98,216,408,412⟩,⟨7,35,13,88,304,98,192,384,260⟩,[⟨2,1212623681526855351930369,⟨35,35,107,216,504,106,216,504,506⟩⟩,⟨4,1210107565564227153313037,⟨7,35,47,111,291,98,192,385,263⟩⟩,⟨7,1208926973944609253637389,⟨7,35,47,127,307,98,64,257,263⟩⟩,⟨8,1181745950697490234637,⟨7,35,47,127,51,98,192,129,7⟩⟩]⟩
theorem node1100 : UpperPrefix a [2,5,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,8,1] 30 cert1100 (by decide +kernel)

def cert1101 : Leaf := ⟨⟨424,392,418,418,130,0,306,50,178⟩,[(5,3)],[(0,2,0),(6,3,5)],⟨7,35,13,88,304,104,210,402,406⟩,⟨7,35,13,88,304,104,192,384,260⟩,[⟨2,1212473376844779117087745,⟨3,35,43,120,504,104,248,504,506⟩⟩,⟨3,1214857655926163789317121,⟨471,499,453,80,304,96,192,384,260⟩⟩,⟨4,1210107565564227161718079,⟨7,39,47,111,295,111,192,385,263⟩⟩]⟩
theorem node1101 : UpperPrefix a [2,5,0,6,8,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,8,3] 30 cert1101 (by decide +kernel)

def cert1102 : Leaf := ⟨⟨344,344,338,0,202,0,282,90,218⟩,[(3,5),(5,3)],[(0,2,0)],⟨7,35,13,88,304,112,202,394,398⟩,⟨7,35,13,88,304,112,192,384,260⟩,[⟨5,1219570779896566093710339,⟨455,463,13,88,280,88,192,384,260⟩⟩,⟨2,1212473376844783412055041,⟨3,43,43,120,504,120,248,504,506⟩⟩,⟨7,1208926973944613561728319,⟨7,47,47,127,319,127,64,257,263⟩⟩]⟩
theorem node1102 : UpperPrefix a [2,5,0,6,8,4] 30 :=
  Boolean.leaf_sound a [2,5,0,6,8,4] 30 cert1102 (by decide +kernel)

def cert1103 : Leaf := ⟨⟨376,344,368,288,72,0,312,120,120⟩,[(5,6)],[(0,2,0),(7,5,5)],⟨7,35,13,88,304,224,194,408,284⟩,⟨7,35,13,88,304,224,194,384,260⟩,[⟨1,1541835366502217371090945,⟨405,445,445,504,440,504,508,384,404⟩⟩,⟨2,1212620950797373088467969,⟨3,43,43,248,504,248,250,504,506⟩⟩]⟩
theorem node1103 : UpperPrefix a [2,5,0,6,8,7,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,8,7,1] 30 cert1103 (by decide +kernel)

def cert1104 : Leaf := ⟨⟨304,276,306,294,6,0,310,54,50⟩,[(5,6)],[(0,2,0),(7,5,5)],⟨7,35,13,88,304,224,200,402,278⟩,⟨7,35,13,88,304,224,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩,⟨3,1236292721030168428162309,⟨407,435,439,242,435,224,224,385,407⟩⟩]⟩
theorem node1104 : UpperPrefix a [2,5,0,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,8,7,3] 30 cert1104 (by decide +kernel)

def cert1105 : Local := ⟨⟨104,76,98,0,78,0,302,110,106⟩,[(3,6),(5,6)],[(0,2,0),(8,4,6),(7,5,5),(4,6,3)]⟩
theorem node1105 : UpperPrefix a [2,5,0,6,8,7,4] 30 :=
  local_sound a [2,5,0,6,8,7,4] 30 cert1105 (by decide +kernel)

theorem node1106 : UpperPrefix a [2,5,0,6,8,7] 30 :=
  branch_upper a [2,5,0,6,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,8,7,0] 30 (by decide +kernel))
  node1103
  (invalid_upper a [2,5,0,6,8,7,2] 30 (by decide +kernel))
  node1104
  node1105
  (invalid_upper a [2,5,0,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,8,7,8] 30 (by decide +kernel)))

theorem node1107 : UpperPrefix a [2,5,0,6,8] 30 :=
  branch_upper a [2,5,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,8,0] 30 (by decide +kernel))
  node1100
  (invalid_upper a [2,5,0,6,8,2] 30 (by decide +kernel))
  node1101
  node1102
  (invalid_upper a [2,5,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,8,6] 30 (by decide +kernel))
  node1106
  (invalid_upper a [2,5,0,6,8,8] 30 (by decide +kernel)))

theorem node1108 : UpperPrefix a [2,5,0,6] 30 :=
  branch_upper a [2,5,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,0] 30 (by decide +kernel))
  node1090
  (invalid_upper a [2,5,0,6,2] 30 (by decide +kernel))
  node1091
  (invalid_upper a [2,5,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,6] 30 (by decide +kernel))
  node1099
  node1107)

def cert1109 : Leaf := ⟨⟨88,88,82,66,0,146,282,90,90⟩,[(4,1)],[(5,1,4),(0,2,0),(7,3,5)],⟨7,35,13,152,50,104,464,464,340⟩,⟨7,35,13,152,50,104,192,384,260⟩,[⟨2,1212475682116443863780353,⟨19,51,59,248,50,104,232,504,506⟩⟩,⟨8,1181747927765451072635,⟨23,55,13,159,55,127,255,128,4⟩⟩]⟩
theorem node1109 : UpperPrefix a [2,5,0,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,0,7,1,3] 30 cert1109 (by decide +kernel)

def cert1110 : Leaf := ⟨⟨472,472,464,320,0,392,280,88,216⟩,[(4,1)],[(5,1,4),(0,2,0)],⟨7,35,13,152,50,112,456,456,332⟩,⟨7,35,13,152,50,112,192,384,260⟩,[⟨1,1314572594710407837908993,⟨453,493,493,504,508,504,192,384,452⟩⟩,⟨2,1212475679864644050095105,⟨19,51,59,248,50,112,232,504,506⟩⟩]⟩
theorem node1110 : UpperPrefix a [2,5,0,7,1,4] 30 :=
  Boolean.leaf_sound a [2,5,0,7,1,4] 30 cert1110 (by decide +kernel)

def cert1111 : Local := ⟨⟨344,348,338,326,0,30,0,94,90⟩,[(4,1),(6,3)],[(5,1,4),(0,2,0),(7,3,6)]⟩
theorem node1111 : UpperPrefix a [2,5,0,7,1,8,3] 30 :=
  local_sound a [2,5,0,7,1,8,3] 30 cert1111 (by decide +kernel)

def cert1112 : Leaf := ⟨⟨472,476,466,0,0,156,0,92,216⟩,[(3,6),(4,1),(6,3)],[(5,1,4),(0,2,0)],⟨7,35,13,152,50,352,208,456,332⟩,⟨7,35,13,152,50,352,208,384,260⟩,[⟨1,1229329505094969492242433,⟨421,161,493,216,248,488,216,384,420⟩⟩]⟩
theorem node1112 : UpperPrefix a [2,5,0,7,1,8,4] 30 :=
  Boolean.leaf_sound a [2,5,0,7,1,8,4] 30 cert1112 (by decide +kernel)

theorem node1113 : UpperPrefix a [2,5,0,7,1,8] 30 :=
  branch_upper a [2,5,0,7,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,8,2] 30 (by decide +kernel))
  node1111
  node1112
  (invalid_upper a [2,5,0,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,8,8] 30 (by decide +kernel)))

theorem node1114 : UpperPrefix a [2,5,0,7,1] 30 :=
  branch_upper a [2,5,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,2] 30 (by decide +kernel))
  node1109
  node1110
  (invalid_upper a [2,5,0,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,1,7] 30 (by decide +kernel))
  node1113)

def cert1115 : Leaf := ⟨⟨40,12,32,100,196,156,316,124,248⟩,[],[(0,2,0),(1,5,1)],⟨7,35,13,152,56,98,464,464,340⟩,⟨7,35,13,152,56,98,192,384,260⟩,[⟨8,1181747927628016313467,⟨7,55,13,159,63,127,255,128,4⟩⟩,⟨4,1210107565282752180790297,⟨7,35,13,143,47,98,192,384,260⟩⟩,⟨6,1210106412362347085571097,⟨7,35,13,159,63,34,128,384,260⟩⟩,⟨7,1208926973663134281114649,⟨7,35,13,31,63,98,64,256,260⟩⟩]⟩
theorem node1115 : UpperPrefix a [2,5,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,5,0,7,3,1] 30 cert1115 (by decide +kernel)

def cert1116 : Leaf := ⟨⟨104,76,98,96,192,136,302,110,106⟩,[],[(0,2,0),(4,5,4)],⟨7,35,13,152,56,112,450,450,326⟩,⟨7,35,13,152,56,112,192,384,260⟩,[⟨8,1181747927628016313467,⟨7,55,13,159,63,127,255,128,4⟩⟩,⟨7,1360042701114962927969337,⟨7,291,13,31,319,375,64,256,260⟩⟩,⟨1,1210107567542257159503873,⟨5,49,13,152,56,120,248,384,260⟩⟩,⟨2,1210107567542257158456321,⟨3,51,9,152,56,120,248,384,256⟩⟩]⟩
theorem node1116 : UpperPrefix a [2,5,0,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,0,7,3,4] 30 cert1116 (by decide +kernel)

def cert1117 : Leaf := ⟨⟨168,140,160,352,448,156,40,120,248⟩,[],[(0,2,0)],⟨7,35,13,152,56,352,194,464,340⟩,⟨7,35,13,152,56,352,194,384,260⟩,[⟨1,1513224466161596662284289,⟨29,189,13,152,184,504,508,384,260⟩⟩,⟨2,1210402749220179819889665,⟨91,251,9,152,184,504,218,384,256⟩⟩,⟨4,1210107709397940256646169,⟨7,35,77,207,111,352,194,384,260⟩⟩,⟨8,1181889784410593567769,⟨7,35,77,223,127,96,194,128,4⟩⟩,⟨6,1210106412362347085571097,⟨7,35,13,159,63,288,130,384,260⟩⟩]⟩
theorem node1117 : UpperPrefix a [2,5,0,7,3,8,1] 30 :=
  Boolean.leaf_sound a [2,5,0,7,3,8,1] 30 cert1117 (by decide +kernel)

def cert1118 : Leaf := ⟨⟨480,452,482,0,454,134,0,102,226⟩,[(3,6),(6,3)],[(0,2,0)],⟨7,35,13,152,56,352,208,450,326⟩,⟨7,35,13,152,56,352,208,384,260⟩,[⟨4,1513224466153747346678873,⟨7,163,13,143,175,483,487,384,260⟩⟩,⟨3,1229329505094957681233669,⟨423,163,487,208,242,483,208,387,423⟩⟩]⟩
theorem node1118 : UpperPrefix a [2,5,0,7,3,8,4] 30 :=
  Boolean.leaf_sound a [2,5,0,7,3,8,4] 30 cert1118 (by decide +kernel)

theorem node1119 : UpperPrefix a [2,5,0,7,3,8] 30 :=
  branch_upper a [2,5,0,7,3,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,3,8,0] 30 (by decide +kernel))
  node1117
  (invalid_upper a [2,5,0,7,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,3,8,3] 30 (by decide +kernel))
  node1118
  (invalid_upper a [2,5,0,7,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,3,8,8] 30 (by decide +kernel)))

theorem node1120 : UpperPrefix a [2,5,0,7,3] 30 :=
  branch_upper a [2,5,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,3,0] 30 (by decide +kernel))
  node1115
  (invalid_upper a [2,5,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,3,3] 30 (by decide +kernel))
  node1116
  (invalid_upper a [2,5,0,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,3,7] 30 (by decide +kernel))
  node1119)

def cert1121 : Leaf := ⟨⟨184,156,176,36,0,156,316,60,184⟩,[(4,5)],[(0,2,0),(6,4,4),(1,5,1)],⟨7,35,13,152,112,98,472,408,284⟩,⟨7,35,13,152,112,98,192,384,260⟩,[⟨8,1181748490577969738879,⟨7,55,15,191,127,127,255,128,5⟩⟩]⟩
theorem node1121 : UpperPrefix a [2,5,0,7,6,1] 30 :=
  Boolean.leaf_sound a [2,5,0,7,6,1] 30 cert1121 (by decide +kernel)

def cert1122 : Leaf := ⟨⟨56,28,50,38,0,150,310,54,50⟩,[(4,5)],[(0,2,0),(7,3,5),(6,4,4)],⟨7,35,13,152,112,104,466,402,278⟩,⟨7,35,13,152,112,104,192,384,260⟩,[⟨8,1181748490577969738879,⟨7,55,15,191,127,127,255,128,5⟩⟩,⟨3,1214857655928362812572673,⟨471,499,453,144,112,112,192,384,260⟩⟩]⟩
theorem node1122 : UpperPrefix a [2,5,0,7,6,3] 30 :=
  Boolean.leaf_sound a [2,5,0,7,6,3] 30 cert1122 (by decide +kernel)

def cert1123 : Leaf := ⟨⟨56,28,50,38,0,0,318,62,58⟩,[(4,5),(5,4)],[(0,2,0),(6,4,4),(6,4,5)],⟨7,35,13,152,112,112,458,394,270⟩,⟨7,35,13,152,112,112,192,384,260⟩,[⟨7,1265595374278916856353805,⟨263,51,271,319,112,112,112,256,261⟩⟩,⟨8,1181748490577969738879,⟨7,55,15,191,127,127,255,128,5⟩⟩]⟩
theorem node1123 : UpperPrefix a [2,5,0,7,6,4] 30 :=
  Boolean.leaf_sound a [2,5,0,7,6,4] 30 cert1123 (by decide +kernel)

def cert1124 : Leaf := ⟨⟨432,404,432,292,0,148,308,52,176⟩,[(4,5)],[(0,2,0),(6,4,4)],⟨7,35,13,152,112,352,194,392,276⟩,⟨7,35,13,152,112,352,194,392,260⟩,[⟨1,1522844443758848707919873,⟨397,445,141,184,504,504,508,392,260⟩⟩,⟨3,1233721852316951040446213,⟨311,307,375,242,114,371,242,499,311⟩⟩]⟩
theorem node1124 : UpperPrefix a [2,5,0,7,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,0,7,6,8,1,3] 30 cert1124 (by decide +kernel)

def cert1125 : Local := ⟨⟨424,396,418,0,0,142,300,46,170⟩,[(3,7),(4,5)],[(0,2,0),(6,4,4),(4,7,3)]⟩
theorem node1125 : UpperPrefix a [2,5,0,7,6,8,1,4] 30 :=
  local_sound a [2,5,0,7,6,8,1,4] 30 cert1125 (by decide +kernel)

theorem node1126 : UpperPrefix a [2,5,0,7,6,8,1] 30 :=
  branch_upper a [2,5,0,7,6,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,6,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,1,2] 30 (by decide +kernel))
  node1124
  node1125
  (invalid_upper a [2,5,0,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,1,8] 30 (by decide +kernel)))

def cert1127 : Local := ⟨⟨312,284,306,294,0,30,0,62,58⟩,[(4,5),(6,3)],[(0,2,0),(7,3,6),(6,4,4)]⟩
theorem node1127 : UpperPrefix a [2,5,0,7,6,8,3] 30 :=
  local_sound a [2,5,0,7,6,8,3] 30 cert1127 (by decide +kernel)

def cert1128 : Local := ⟨⟨440,412,434,0,0,158,0,62,186⟩,[(3,6),(4,5),(6,3)],[(0,2,0),(6,4,4)]⟩
theorem node1128 : UpperPrefix a [2,5,0,7,6,8,4] 30 :=
  local_sound a [2,5,0,7,6,8,4] 30 cert1128 (by decide +kernel)

theorem node1129 : UpperPrefix a [2,5,0,7,6,8] 30 :=
  branch_upper a [2,5,0,7,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,6,8,0] 30 (by decide +kernel))
  node1126
  (invalid_upper a [2,5,0,7,6,8,2] 30 (by decide +kernel))
  node1127
  node1128
  (invalid_upper a [2,5,0,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,8,8] 30 (by decide +kernel)))

theorem node1130 : UpperPrefix a [2,5,0,7,6] 30 :=
  branch_upper a [2,5,0,7,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,6,0] 30 (by decide +kernel))
  node1121
  (invalid_upper a [2,5,0,7,6,2] 30 (by decide +kernel))
  node1122
  node1123
  (invalid_upper a [2,5,0,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,6,7] 30 (by decide +kernel))
  node1129)

def cert1131 : Local := ⟨⟨120,92,112,356,76,28,0,124,120⟩,[(6,3)],[(0,2,0),(7,3,6),(8,4,3),(1,5,1)]⟩
theorem node1131 : UpperPrefix a [2,5,0,7,8,1,3] 30 :=
  local_sound a [2,5,0,7,8,1,3] 30 cert1131 (by decide +kernel)

def cert1132 : Leaf := ⟨⟨248,216,240,0,200,152,0,120,248⟩,[(3,6),(6,3)],[(0,2,0),(8,4,3),(8,4,6),(1,5,1)],⟨7,35,13,152,304,98,208,456,332⟩,⟨7,35,13,152,304,98,208,384,260⟩,[⟨2,1212623681526855351930369,⟨35,35,107,216,504,106,216,504,506⟩⟩]⟩
theorem node1132 : UpperPrefix a [2,5,0,7,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,0,7,8,1,4] 30 cert1132 (by decide +kernel)

theorem node1133 : UpperPrefix a [2,5,0,7,8,1] 30 :=
  branch_upper a [2,5,0,7,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,1,2] 30 (by decide +kernel))
  node1131
  node1132
  (invalid_upper a [2,5,0,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,1,8] 30 (by decide +kernel)))

def cert1134 : Leaf := ⟨⟨104,76,96,356,76,132,44,124,120⟩,[],[(0,2,0),(7,3,5),(8,4,3)],⟨7,35,13,152,304,104,194,464,340⟩,⟨7,35,13,152,304,104,194,384,260⟩,[⟨1,1513224466161459223330817,⟨13,189,13,152,440,504,508,384,260⟩⟩,⟨4,1210110015663161939754815,⟨39,39,111,239,295,111,195,451,295⟩⟩]⟩
theorem node1134 : UpperPrefix a [2,5,0,7,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,0,7,8,3,1] 30 cert1134 (by decide +kernel)

def cert1135 : Local := ⟨⟨104,76,98,0,78,150,0,110,106⟩,[(3,6),(6,3)],[(0,2,0),(7,3,5),(8,4,3),(8,4,6),(4,6,5)]⟩
theorem node1135 : UpperPrefix a [2,5,0,7,8,3,4] 30 :=
  local_sound a [2,5,0,7,8,3,4] 30 cert1135 (by decide +kernel)

theorem node1136 : UpperPrefix a [2,5,0,7,8,3] 30 :=
  branch_upper a [2,5,0,7,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,8,3,0] 30 (by decide +kernel))
  node1134
  (invalid_upper a [2,5,0,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,3,3] 30 (by decide +kernel))
  node1135
  (invalid_upper a [2,5,0,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,3,8] 30 (by decide +kernel)))

def cert1137 : Leaf := ⟨⟨208,212,208,324,196,132,20,92,216⟩,[],[(0,2,0),(8,4,3)],⟨7,35,13,152,304,112,194,456,332⟩,⟨7,35,13,152,304,112,194,384,260⟩,[⟨1,1513224466161459223330817,⟨13,189,13,152,440,504,508,384,260⟩⟩,⟨5,1389908032687600758686787,⟨455,463,461,152,412,477,455,384,388⟩⟩,⟨3,1210110022287718412791045,⟨7,35,103,242,307,114,242,499,263⟩⟩]⟩
theorem node1137 : UpperPrefix a [2,5,0,7,8,4,1] 30 :=
  Boolean.leaf_sound a [2,5,0,7,8,4,1] 30 cert1137 (by decide +kernel)

def cert1138 : Leaf := ⟨⟨120,88,114,354,74,10,0,122,122⟩,[(6,3)],[(0,2,0),(7,3,6),(8,4,3)],⟨7,35,13,152,304,112,200,450,326⟩,⟨7,35,13,152,304,112,200,384,260⟩,[⟨2,1212476115033352558349313,⟨3,35,107,248,504,120,248,504,506⟩⟩]⟩
theorem node1138 : UpperPrefix a [2,5,0,7,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,0,7,8,4,3] 30 cert1138 (by decide +kernel)

theorem node1139 : UpperPrefix a [2,5,0,7,8,4] 30 :=
  branch_upper a [2,5,0,7,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,8,4,0] 30 (by decide +kernel))
  node1137
  (invalid_upper a [2,5,0,7,8,4,2] 30 (by decide +kernel))
  node1138
  (invalid_upper a [2,5,0,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,4,8] 30 (by decide +kernel)))

theorem node1140 : UpperPrefix a [2,5,0,7,8] 30 :=
  branch_upper a [2,5,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,8,0] 30 (by decide +kernel))
  node1133
  (invalid_upper a [2,5,0,7,8,2] 30 (by decide +kernel))
  node1136
  node1139
  (invalid_upper a [2,5,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,8,8] 30 (by decide +kernel)))

theorem node1141 : UpperPrefix a [2,5,0,7] 30 :=
  branch_upper a [2,5,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,7,0] 30 (by decide +kernel))
  node1114
  (invalid_upper a [2,5,0,7,2] 30 (by decide +kernel))
  node1120
  (invalid_upper a [2,5,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,7,5] 30 (by decide +kernel))
  node1130
  (invalid_upper a [2,5,0,7,7] 30 (by decide +kernel))
  node1140)

def cert1142 : Leaf := ⟨⟨472,472,466,194,0,400,272,80,210⟩,[(4,1)],[(5,1,4),(0,2,0)],⟨7,35,13,280,50,104,208,464,468⟩,⟨7,35,13,280,50,104,192,384,260⟩,[⟨2,1212549685406327023603201,⟨115,51,251,504,50,232,232,504,506⟩⟩,⟨1,1210181496797547065245697,⟨37,33,237,504,48,232,192,384,292⟩⟩,⟨3,1214931875248022855091201,⟨471,499,453,464,242,224,192,384,260⟩⟩]⟩
theorem node1142 : UpperPrefix a [2,5,0,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,0,8,1,3] 30 cert1142 (by decide +kernel)

def cert1143 : Leaf := ⟨⟨472,472,464,192,0,392,280,88,216⟩,[(4,1)],[(5,1,4),(0,2,0)],⟨7,35,13,280,50,112,200,456,460⟩,⟨7,35,13,280,50,112,192,384,260⟩,[⟨1,1314572594710407837908993,⟨453,493,493,504,508,504,192,384,452⟩⟩,⟨2,1212549683189711582006785,⟨115,51,251,504,50,112,232,504,506⟩⟩]⟩
theorem node1143 : UpperPrefix a [2,5,0,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,0,8,1,4] 30 cert1143 (by decide +kernel)

def cert1144 : Local := ⟨⟨344,348,338,70,0,0,286,94,90⟩,[(4,1),(5,6)],[(5,1,4),(0,2,0),(7,5,5)]⟩
theorem node1144 : UpperPrefix a [2,5,0,8,1,7] 30 :=
  local_sound a [2,5,0,8,1,7] 30 cert1144 (by decide +kernel)

theorem node1145 : UpperPrefix a [2,5,0,8,1] 30 :=
  branch_upper a [2,5,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,1,2] 30 (by decide +kernel))
  node1142
  node1143
  (invalid_upper a [2,5,0,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,1,6] 30 (by decide +kernel))
  node1144
  (invalid_upper a [2,5,0,8,1,8] 30 (by decide +kernel)))

def cert1146 : Leaf := ⟨⟨416,384,416,224,448,400,304,112,248⟩,[],[(0,2,0),(1,5,1)],⟨7,35,13,280,56,98,208,464,468⟩,⟨7,35,13,280,56,98,192,384,260⟩,[⟨2,1212549966644152820043265,⟨115,35,251,504,248,98,216,504,506⟩⟩,⟨3,1210181785590872096775941,⟨39,35,231,499,242,98,192,387,295⟩⟩,⟨4,1210107565282752180790297,⟨7,35,13,271,47,98,192,384,260⟩⟩,⟨6,1210106412362347085571097,⟨7,35,13,287,63,34,128,384,260⟩⟩]⟩
theorem node1146 : UpperPrefix a [2,5,0,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,0,8,3,1] 30 cert1146 (by decide +kernel)

def cert1147 : Leaf := ⟨⟨480,448,482,226,450,386,258,66,194⟩,[],[(0,2,0),(4,5,4)],⟨7,35,13,280,56,112,194,450,454⟩,⟨7,35,13,280,56,112,192,384,260⟩,[⟨2,1212473376287041106480129,⟨19,35,59,504,56,112,248,504,506⟩⟩,⟨3,1236224102496983634156805,⟨455,483,487,499,242,112,192,449,455⟩⟩,⟨5,1214857654800127517262849,⟨455,451,461,280,24,80,192,384,260⟩⟩]⟩
theorem node1147 : UpperPrefix a [2,5,0,8,3,4] 30 :=
  Boolean.leaf_sound a [2,5,0,8,3,4] 30 cert1147 (by decide +kernel)

def cert1148 : Leaf := ⟨⟨352,320,354,98,322,0,306,114,122⟩,[(5,6)],[(0,2,0),(7,5,5)],⟨7,35,13,280,56,224,210,466,342⟩,⟨7,35,13,280,56,224,192,384,260⟩,[⟨2,1212473376289240129735681,⟨19,51,59,504,56,248,248,504,506⟩⟩,⟨3,1210181787842671910461189,⟨39,35,231,499,242,224,224,387,295⟩⟩,⟨4,1210107567534551994475545,⟨7,35,13,271,47,224,224,384,260⟩⟩]⟩
theorem node1148 : UpperPrefix a [2,5,0,8,3,7] 30 :=
  Boolean.leaf_sound a [2,5,0,8,3,7] 30 cert1148 (by decide +kernel)

theorem node1149 : UpperPrefix a [2,5,0,8,3] 30 :=
  branch_upper a [2,5,0,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,8,3,0] 30 (by decide +kernel))
  node1146
  (invalid_upper a [2,5,0,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,3,3] 30 (by decide +kernel))
  node1147
  (invalid_upper a [2,5,0,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,8,3,6] 30 (by decide +kernel))
  node1148
  (invalid_upper a [2,5,0,8,3,8] 30 (by decide +kernel)))

def cert1150 : Leaf := ⟨⟨440,408,432,160,0,408,312,56,184⟩,[(4,5)],[(0,2,0),(6,4,4),(1,5,1)],⟨7,35,13,280,112,98,216,408,412⟩,⟨7,35,13,280,112,98,192,384,260⟩,[⟨2,1212549678416044411063809,⟨115,51,251,504,112,114,216,504,506⟩⟩]⟩
theorem node1150 : UpperPrefix a [2,5,0,8,6,1] 30 :=
  Boolean.leaf_sound a [2,5,0,8,6,1] 30 cert1150 (by decide +kernel)

def cert1151 : Leaf := ⟨⟨424,392,418,162,0,402,306,50,178⟩,[(4,5)],[(0,2,0),(6,4,4)],⟨7,35,13,280,112,104,210,402,406⟩,⟨7,35,13,280,112,104,192,384,260⟩,[⟨2,1212473376288965251828737,⟨3,51,59,504,112,120,248,504,506⟩⟩,⟨3,1214857655928362812572673,⟨471,499,453,272,112,112,192,384,260⟩⟩,⟨4,1210107565282752185001019,⟨7,39,13,271,103,111,192,384,260⟩⟩]⟩
theorem node1151 : UpperPrefix a [2,5,0,8,6,3] 30 :=
  Boolean.leaf_sound a [2,5,0,8,6,3] 30 cert1151 (by decide +kernel)

#print axioms node1151
end Delivery.FiniteExclusion.Sharp2x7
