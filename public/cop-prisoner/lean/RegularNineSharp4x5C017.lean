import RegularNineSharp4x5Base
import RegularNineSharp4x5C016
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert1088 : Leaf := ⟨⟨352,328,83,278,322,0,270,78,79⟩,[(5,6)],[(5,1,0),(7,5,5)],⟨19,38,268,73,49,224,206,398,286⟩,⟨19,38,268,73,49,224,192,384,272⟩,[⟨0,1210144533292499189369856,⟨50,230,494,104,48,224,224,384,272⟩⟩,⟨4,1210144533291399677742081,⟨35,230,494,105,33,224,224,384,256⟩⟩,⟨2,1210107567536338693522435,⟨19,51,280,121,49,224,224,384,272⟩⟩,⟨3,1210107567536337620829187,⟨19,55,276,113,49,224,224,384,272⟩⟩]⟩
theorem node1088 : UpperPrefix a [4,5,8,6,0,7] 30 :=
  Boolean.leaf_sound a [4,5,8,6,0,7] 30 cert1088 (by decide +kernel)

theorem node1089 : UpperPrefix a [4,5,8,6,0] 30 :=
  branch_upper a [4,5,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,8,6,0,0] 30 (by decide +kernel))
  node1085
  node1086
  node1087
  (invalid_upper a [4,5,8,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,0,6] 30 (by decide +kernel))
  node1088
  (invalid_upper a [4,5,8,6,0,8] 30 (by decide +kernel)))

def cert1090 : Local := ⟨⟨0,473,209,0,0,0,285,93,205⟩,[(0,4),(3,5),(4,1),(5,3)],[(5,1,0),(5,1,4),(1,4,0)]⟩
theorem node1090 : UpperPrefix a [4,5,8,6,1,0] 30 :=
  local_sound a [4,5,8,6,1,0] 30 cert1090 (by decide +kernel)

def cert1091 : Local := ⟨⟨0,0,209,400,0,409,281,89,201⟩,[(0,4),(1,5),(4,1)],[(5,1,0),(5,1,4),(1,4,0),(2,5,1),(2,5,4)]⟩
theorem node1091 : UpperPrefix a [4,5,8,6,1,2] 30 :=
  local_sound a [4,5,8,6,1,2] 30 cert1091 (by decide +kernel)

def cert1092 : Local := ⟨⟨0,409,145,404,0,0,277,21,133⟩,[(0,4),(4,1),(5,3)],[(5,1,0),(5,1,4),(6,3,5),(1,4,0),(3,5,1)]⟩
theorem node1092 : UpperPrefix a [4,5,8,6,1,3] 30 :=
  local_sound a [4,5,8,6,1,3] 30 cert1092 (by decide +kernel)

def cert1093 : Local := ⟨⟨0,345,81,276,0,0,285,93,77⟩,[(0,4),(4,1),(5,6)],[(5,1,0),(5,1,4),(1,4,0),(7,5,5)]⟩
theorem node1093 : UpperPrefix a [4,5,8,6,1,7] 30 :=
  local_sound a [4,5,8,6,1,7] 30 cert1093 (by decide +kernel)

theorem node1094 : UpperPrefix a [4,5,8,6,1] 30 :=
  branch_upper a [4,5,8,6,1] 30 (by decide) (fin9_cases _
  node1090
  (invalid_upper a [4,5,8,6,1,1] 30 (by decide +kernel))
  node1091
  node1092
  (invalid_upper a [4,5,8,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,1,6] 30 (by decide +kernel))
  node1093
  (invalid_upper a [4,5,8,6,1,8] 30 (by decide +kernel)))

def cert1095 : Local := ⟨⟨492,0,211,0,0,0,283,91,203⟩,[(1,4),(3,5),(4,1),(5,3)],[(5,1,0),(2,4,0)]⟩
theorem node1095 : UpperPrefix a [4,5,8,6,2,0] 30 :=
  local_sound a [4,5,8,6,2,0] 30 cert1095 (by decide +kernel)

def cert1096 : Leaf := ⟨⟨492,0,209,400,0,409,281,89,201⟩,[(1,4),(4,1)],[(5,1,0),(2,4,0)],⟨19,38,268,73,52,98,201,393,409⟩,⟨19,38,268,73,52,98,192,384,272⟩,[⟨1,1214913104244777185181697,⟨477,52,460,461,52,112,192,384,272⟩⟩]⟩
theorem node1096 : UpperPrefix a [4,5,8,6,2,1] 30 :=
  Boolean.leaf_sound a [4,5,8,6,2,1] 30 cert1096 (by decide +kernel)

def cert1097 : Local := ⟨⟨420,0,147,402,0,0,275,19,131⟩,[(1,4),(4,1),(5,3)],[(5,1,0),(6,3,5),(2,4,0),(3,5,1),(3,5,4)]⟩
theorem node1097 : UpperPrefix a [4,5,8,6,2,3] 30 :=
  local_sound a [4,5,8,6,2,3] 30 cert1097 (by decide +kernel)

def cert1098 : Local := ⟨⟨364,0,83,274,0,0,283,91,75⟩,[(1,4),(4,1),(5,6)],[(5,1,0),(2,4,0),(7,5,5)]⟩
theorem node1098 : UpperPrefix a [4,5,8,6,2,7] 30 :=
  local_sound a [4,5,8,6,2,7] 30 cert1098 (by decide +kernel)

theorem node1099 : UpperPrefix a [4,5,8,6,2] 30 :=
  branch_upper a [4,5,8,6,2] 30 (by decide) (fin9_cases _
  node1095
  node1096
  (invalid_upper a [4,5,8,6,2,2] 30 (by decide +kernel))
  node1097
  (invalid_upper a [4,5,8,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,2,6] 30 (by decide +kernel))
  node1098
  (invalid_upper a [4,5,8,6,2,8] 30 (by decide +kernel)))

def cert1100 : Leaf := ⟨⟨428,400,146,0,455,0,278,22,142⟩,[(3,5),(5,3)],[(5,1,0),(6,3,4),(0,5,4)],⟨19,38,268,73,56,97,198,390,406⟩,⟨19,38,268,73,56,97,192,384,272⟩,[⟨3,1210144567175048437173249,⟨115,230,486,97,48,97,192,384,272⟩⟩]⟩
theorem node1100 : UpperPrefix a [4,5,8,6,3,0] 30 :=
  Boolean.leaf_sound a [4,5,8,6,3,0] 30 cert1100 (by decide +kernel)

def cert1101 : Leaf := ⟨⟨428,408,144,0,452,412,284,28,140⟩,[(3,6)],[(5,1,0),(6,3,4),(0,6,3)],⟨19,38,268,73,56,98,193,388,404⟩,⟨19,38,268,73,56,98,193,384,272⟩,[⟨1,1454480969532113335615489,⟨477,436,460,461,508,508,461,384,404⟩⟩]⟩
theorem node1101 : UpperPrefix a [4,5,8,6,3,1,0] 30 :=
  Boolean.leaf_sound a [4,5,8,6,3,1,0] 30 cert1101 (by decide +kernel)

def cert1102 : Leaf := ⟨⟨168,145,145,144,195,149,273,17,129⟩,[],[(5,1,0),(8,2,6),(6,3,4),(2,6,5)],⟨19,38,268,73,56,98,196,385,401⟩,⟨19,38,268,73,56,98,196,384,272⟩,[⟨1,1214913464532609935867905,⟨477,100,460,461,252,96,196,384,336⟩⟩,⟨3,1214913016917027011464193,⟨435,102,486,483,176,98,230,384,272⟩⟩]⟩
theorem node1102 : UpperPrefix a [4,5,8,6,3,1,2] 30 :=
  Boolean.leaf_sound a [4,5,8,6,3,1,2] 30 cert1102 (by decide +kernel)

theorem node1103 : UpperPrefix a [4,5,8,6,3,1] 30 :=
  branch_upper a [4,5,8,6,3,1] 30 (by decide) (fin9_cases _
  node1101
  (invalid_upper a [4,5,8,6,3,1,1] 30 (by decide +kernel))
  node1102
  (invalid_upper a [4,5,8,6,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,1,8] 30 (by decide +kernel)))

def cert1104 : Leaf := ⟨⟨288,0,147,274,323,411,275,19,131⟩,[(1,5)],[(5,1,0),(6,3,4),(2,5,1)],⟨19,38,268,73,56,100,195,387,403⟩,⟨19,38,268,73,56,100,192,384,272⟩,[⟨3,1290544899062035773408273,⟨467,38,260,449,499,102,192,384,465⟩⟩,⟨7,1208926973665475032007731,⟨19,63,268,73,59,127,64,256,273⟩⟩]⟩
theorem node1104 : UpperPrefix a [4,5,8,6,3,2] 30 :=
  Boolean.leaf_sound a [4,5,8,6,3,2] 30 cert1104 (by decide +kernel)

def cert1105 : Local := ⟨⟨300,280,18,0,326,0,286,30,14⟩,[(3,6),(5,6)],[(5,1,0),(6,3,4),(7,5,5),(0,6,3)]⟩
theorem node1105 : UpperPrefix a [4,5,8,6,3,7,0] 30 :=
  local_sound a [4,5,8,6,3,7,0] 30 cert1105 (by decide +kernel)

def cert1106 : Local := ⟨⟨300,281,17,278,325,0,285,29,13⟩,[(5,6)],[(5,1,0),(6,3,4),(7,5,5),(1,6,3)]⟩
theorem node1106 : UpperPrefix a [4,5,8,6,3,7,1] 30 :=
  local_sound a [4,5,8,6,3,7,1] 30 cert1106 (by decide +kernel)

def cert1107 : Local := ⟨⟨44,25,19,22,71,0,283,31,15⟩,[(5,6)],[(5,1,0),(8,2,6),(6,3,4),(7,5,5)]⟩
theorem node1107 : UpperPrefix a [4,5,8,6,3,7,2] 30 :=
  local_sound a [4,5,8,6,3,7,2] 30 cert1107 (by decide +kernel)

theorem node1108 : UpperPrefix a [4,5,8,6,3,7] 30 :=
  branch_upper a [4,5,8,6,3,7] 30 (by decide) (fin9_cases _
  node1105
  node1106
  node1107
  (invalid_upper a [4,5,8,6,3,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,7,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,7,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,7,8] 30 (by decide +kernel)))

theorem node1109 : UpperPrefix a [4,5,8,6,3] 30 :=
  branch_upper a [4,5,8,6,3] 30 (by decide) (fin9_cases _
  node1100
  node1103
  node1104
  (invalid_upper a [4,5,8,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,3,6] 30 (by decide +kernel))
  node1108
  (invalid_upper a [4,5,8,6,3,8] 30 (by decide +kernel)))

def cert1110 : Leaf := ⟨⟨364,345,81,0,332,0,284,92,77⟩,[(3,5),(5,3)],[(5,1,0),(1,6,3),(1,6,5)],⟨19,38,268,73,176,97,194,396,284⟩,⟨19,38,268,73,176,97,194,384,272⟩,[⟨7,1284484837670527874116881,⟨279,46,303,105,319,105,66,257,279⟩⟩,⟨0,1210144494800933563139072,⟨82,246,396,72,176,96,210,384,272⟩⟩]⟩
theorem node1110 : UpperPrefix a [4,5,8,6,7,0,1] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,0,1] 30 cert1110 (by decide +kernel)

def cert1111 : Leaf := ⟨⟨104,89,83,0,75,0,283,91,75⟩,[(3,5),(5,3)],[(5,1,0),(8,2,6)],⟨19,38,268,73,176,97,196,394,282⟩,⟨19,38,268,73,176,97,196,384,272⟩,[⟨2,1219570745275281395680259,⟨403,443,296,105,184,105,192,384,272⟩⟩,⟨7,1284484837670527874116881,⟨279,46,303,105,319,105,70,257,279⟩⟩]⟩
theorem node1111 : UpperPrefix a [4,5,8,6,7,0,2] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,0,2] 30 cert1111 (by decide +kernel)

def cert1112 : Leaf := ⟨⟨292,337,83,0,263,0,279,23,7⟩,[(3,5),(5,3)],[(5,1,0)],⟨19,38,268,73,176,97,200,390,278⟩,⟨19,38,268,73,176,97,200,384,272⟩,[⟨3,1238497104699574952397831,⟨403,439,439,113,176,113,240,384,272⟩⟩,⟨6,1219569592072297518203907,⟨403,439,268,9,176,33,136,384,272⟩⟩,⟨7,1289207204153397529869585,⟨279,46,303,367,319,367,110,257,279⟩⟩]⟩
theorem node1112 : UpperPrefix a [4,5,8,6,7,0,3] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,0,3] 30 cert1112 (by decide +kernel)

theorem node1113 : UpperPrefix a [4,5,8,6,7,0] 30 :=
  branch_upper a [4,5,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,8,6,7,0,0] 30 (by decide +kernel))
  node1110
  node1111
  node1112
  (invalid_upper a [4,5,8,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,0,8] 30 (by decide +kernel)))

def cert1114 : Leaf := ⟨⟨480,472,208,0,320,400,272,92,204⟩,[(3,6)],[(5,1,0),(0,6,3)],⟨19,38,268,73,176,98,193,396,284⟩,⟨19,38,268,73,176,98,193,384,272⟩,[⟨1,1366951168902498947956737,⟨477,436,460,461,436,508,461,384,272⟩⟩,⟨2,1210107853553825421984801,⟨123,43,264,121,249,123,249,384,344⟩⟩,⟨3,1210107853553809182688289,⟨115,39,260,113,241,115,241,384,336⟩⟩]⟩
theorem node1114 : UpperPrefix a [4,5,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,1,0] 30 cert1114 (by decide +kernel)

def cert1115 : Leaf := ⟨⟨224,208,209,144,66,148,281,89,201⟩,[],[(5,1,0),(8,2,6),(2,6,5)],⟨19,38,268,73,176,98,196,393,281⟩,⟨19,38,268,73,176,98,196,384,272⟩,[⟨1,1214913176302233784156161,⟨477,100,460,461,176,96,196,384,272⟩⟩,⟨3,1210107567821523449318505,⟨19,39,295,115,177,115,247,384,272⟩⟩,⟨0,1210107567821524523060224,⟨18,38,302,122,176,114,246,384,272⟩⟩]⟩
theorem node1115 : UpperPrefix a [4,5,8,6,7,1,2] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,1,2] 30 cert1115 (by decide +kernel)

def cert1116 : Leaf := ⟨⟨484,456,192,384,322,392,257,84,196⟩,[],[(4,0,7),(5,1,0),(0,7,6)],⟨19,38,268,73,176,98,200,385,276⟩,⟨19,38,268,73,176,98,200,385,272⟩,[⟨1,1290473634101550690598913,⟨477,100,460,461,508,96,204,461,340⟩⟩,⟨2,1210110159401234829673473,⟨123,34,264,105,248,98,216,505,336⟩⟩,⟨3,1219875116273216282166307,⟨403,439,260,193,177,499,192,385,272⟩⟩]⟩
theorem node1116 : UpperPrefix a [4,5,8,6,7,1,3,0] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,1,3,0] 30 cert1116 (by decide +kernel)

def cert1117 : Leaf := ⟨⟨236,216,209,148,76,156,20,0,205⟩,[(7,2)],[(5,1,0),(8,2,7)],⟨19,38,268,73,176,98,200,388,273⟩,⟨19,38,268,73,176,98,200,388,272⟩,[⟨1,1214950069790518642212865,⟨477,244,460,461,176,112,204,452,272⟩⟩,⟨0,1210144537809705273199616,⟨50,246,510,120,178,114,250,502,272⟩⟩]⟩
theorem node1117 : UpperPrefix a [4,5,8,6,7,1,3,2] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,1,3,2] 30 cert1117 (by decide +kernel)

theorem node1118 : UpperPrefix a [4,5,8,6,7,1,3] 30 :=
  branch_upper a [4,5,8,6,7,1,3] 30 (by decide) (fin9_cases _
  node1116
  (invalid_upper a [4,5,8,6,7,1,3,1] 30 (by decide +kernel))
  node1117
  (invalid_upper a [4,5,8,6,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,3,8] 30 (by decide +kernel)))

theorem node1119 : UpperPrefix a [4,5,8,6,7,1] 30 :=
  branch_upper a [4,5,8,6,7,1] 30 (by decide) (fin9_cases _
  node1114
  (invalid_upper a [4,5,8,6,7,1,1] 30 (by decide +kernel))
  node1115
  node1118
  (invalid_upper a [4,5,8,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,1,8] 30 (by decide +kernel)))

def cert1120 : Local := ⟨⟨488,0,210,0,330,410,282,90,202⟩,[(1,5),(3,6)],[(5,1,0),(2,5,1),(0,6,3)]⟩
theorem node1120 : UpperPrefix a [4,5,8,6,7,2,0] 30 :=
  local_sound a [4,5,8,6,7,2,0] 30 cert1120 (by decide +kernel)

def cert1121 : Leaf := ⟨⟨224,0,209,146,329,409,17,89,201⟩,[(1,5)],[(5,1,0),(2,5,1),(1,6,3)],⟨19,38,268,73,176,100,194,393,281⟩,⟨19,38,268,73,176,100,194,384,272⟩,[⟨8,1182033899635304580113,⟨91,38,12,73,251,102,194,136,89⟩⟩,⟨3,1210107853514226764104721,⟨83,38,260,65,243,102,194,384,337⟩⟩]⟩
theorem node1121 : UpperPrefix a [4,5,8,6,7,2,1] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,2,1] 30 cert1121 (by decide +kernel)

def cert1122 : Leaf := ⟨⟨416,0,147,402,259,411,275,19,131⟩,[(1,5)],[(5,1,0),(2,5,1),(3,6,5)],⟨19,38,268,73,176,100,200,387,275⟩,⟨19,38,268,73,176,100,200,384,272⟩,[⟨6,1451417494964915043058739,⟨403,439,268,397,435,439,140,384,401⟩⟩]⟩
theorem node1122 : UpperPrefix a [4,5,8,6,7,2,3] 30 :=
  Boolean.leaf_sound a [4,5,8,6,7,2,3] 30 cert1122 (by decide +kernel)

theorem node1123 : UpperPrefix a [4,5,8,6,7,2] 30 :=
  branch_upper a [4,5,8,6,7,2] 30 (by decide) (fin9_cases _
  node1120
  node1121
  (invalid_upper a [4,5,8,6,7,2,2] 30 (by decide +kernel))
  node1122
  (invalid_upper a [4,5,8,6,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,2,8] 30 (by decide +kernel)))

def cert1124 : Local := ⟨⟨420,408,146,0,262,0,278,22,134⟩,[(3,6),(5,3)],[(5,1,0),(6,3,5),(3,5,1),(0,6,3),(0,6,5)]⟩
theorem node1124 : UpperPrefix a [4,5,8,6,7,3,0] 30 :=
  local_sound a [4,5,8,6,7,3,0] 30 cert1124 (by decide +kernel)

def cert1125 : Local := ⟨⟨420,409,145,406,261,0,277,21,133⟩,[(5,3)],[(5,1,0),(6,3,5),(3,5,1),(1,6,3)]⟩
theorem node1125 : UpperPrefix a [4,5,8,6,7,3,1] 30 :=
  local_sound a [4,5,8,6,7,3,1] 30 cert1125 (by decide +kernel)

def cert1126 : Local := ⟨⟨164,153,147,150,7,0,275,23,135⟩,[(5,3)],[(5,1,0),(8,2,6),(6,3,5),(3,5,1)]⟩
theorem node1126 : UpperPrefix a [4,5,8,6,7,3,2] 30 :=
  local_sound a [4,5,8,6,7,3,2] 30 cert1126 (by decide +kernel)

theorem node1127 : UpperPrefix a [4,5,8,6,7,3] 30 :=
  branch_upper a [4,5,8,6,7,3] 30 (by decide) (fin9_cases _
  node1124
  node1125
  node1126
  (invalid_upper a [4,5,8,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,3,8] 30 (by decide +kernel)))

theorem node1128 : UpperPrefix a [4,5,8,6,7] 30 :=
  branch_upper a [4,5,8,6,7] 30 (by decide) (fin9_cases _
  node1113
  node1119
  node1123
  node1127
  (invalid_upper a [4,5,8,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,7,8] 30 (by decide +kernel)))

theorem node1129 : UpperPrefix a [4,5,8,6] 30 :=
  branch_upper a [4,5,8,6] 30 (by decide) (fin9_cases _
  node1089
  node1094
  node1099
  node1109
  (invalid_upper a [4,5,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,6,6] 30 (by decide +kernel))
  node1128
  (invalid_upper a [4,5,8,6,8] 30 (by decide +kernel)))

def cert1130 : Leaf := ⟨⟨32,456,209,340,2,396,268,76,205⟩,[],[(5,1,0),(1,5,4)],⟨19,38,268,137,49,98,204,460,348⟩,⟨19,38,268,137,49,98,192,384,272⟩,[⟨0,1210144531040699375684608,⟨50,230,494,136,48,98,192,384,272⟩⟩,⟨4,1210144531039599864056833,⟨35,230,494,137,33,98,192,384,256⟩⟩,⟨2,1210107565286188147278883,⟨19,51,264,137,49,115,192,384,272⟩⟩,⟨3,1210107565286187074585635,⟨19,55,260,129,49,115,192,384,272⟩⟩,⟨6,1210106412364683541480483,⟨19,55,268,137,49,51,128,384,272⟩⟩,⟨7,1208926973665470737024035,⟨19,55,268,9,49,115,64,256,272⟩⟩,⟨8,1181745671558973621283,⟨19,55,12,137,49,115,192,128,16⟩⟩]⟩
theorem node1130 : UpperPrefix a [4,5,8,7,0,1] 30 :=
  Boolean.leaf_sound a [4,5,8,7,0,1] 30 cert1130 (by decide +kernel)

def cert1131 : Leaf := ⟨⟨416,0,211,338,386,394,266,74,203⟩,[(1,5)],[(5,1,0),(2,5,1)],⟨19,38,268,137,49,100,202,458,346⟩,⟨19,38,268,137,49,100,192,384,272⟩,[⟨0,1210144531040699375700992,⟨50,230,494,136,50,230,192,384,272⟩⟩,⟨4,1210144531039599864073217,⟨35,230,494,137,35,230,192,384,256⟩⟩,⟨3,1210107565286187074602035,⟨19,55,260,129,51,119,192,384,273⟩⟩,⟨6,1210106412364683541496883,⟨19,55,268,137,51,55,128,384,273⟩⟩]⟩
theorem node1131 : UpperPrefix a [4,5,8,7,0,2] 30 :=
  Boolean.leaf_sound a [4,5,8,7,0,2] 30 cert1131 (by decide +kernel)

def cert1132 : Leaf := ⟨⟨288,328,83,342,258,390,262,70,71⟩,[],[(5,1,0),(7,3,5),(3,5,1)],⟨19,38,268,137,49,104,198,454,342⟩,⟨19,38,268,137,49,104,192,384,272⟩,[⟨0,1210144566999127650470912,⟨82,230,494,136,48,104,192,384,272⟩⟩,⟨4,1210144566998028138843137,⟨67,230,494,137,33,104,192,384,256⟩⟩,⟨2,1210107565283989124023299,⟨19,51,264,137,49,104,192,384,272⟩⟩,⟨6,1210106412362484518224899,⟨19,55,268,137,49,40,128,384,272⟩⟩]⟩
theorem node1132 : UpperPrefix a [4,5,8,7,0,3] 30 :=
  Boolean.leaf_sound a [4,5,8,7,0,3] 30 cert1132 (by decide +kernel)

theorem node1133 : UpperPrefix a [4,5,8,7,0] 30 :=
  branch_upper a [4,5,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,8,7,0,0] 30 (by decide +kernel))
  node1130
  node1131
  node1132
  (invalid_upper a [4,5,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,0,8] 30 (by decide +kernel)))

def cert1134 : Leaf := ⟨⟨0,473,209,340,0,412,268,76,205⟩,[(0,4),(4,1)],[(5,1,0),(5,1,4),(1,4,0)],⟨19,38,268,137,50,97,204,460,348⟩,⟨19,38,268,137,50,97,192,384,272⟩,[⟨0,1210144530829730582103040,⟨18,246,460,136,50,96,192,384,272⟩⟩,⟨4,1210144530828493631521793,⟨3,230,460,137,34,97,192,384,256⟩⟩]⟩
theorem node1134 : UpperPrefix a [4,5,8,7,1,0] 30 :=
  Boolean.leaf_sound a [4,5,8,7,1,0] 30 cert1134 (by decide +kernel)

def cert1135 : Local := ⟨⟨0,0,209,336,0,409,281,89,201⟩,[(0,4),(1,5),(4,1)],[(5,1,0),(5,1,4),(1,4,0),(2,5,1),(2,5,4)]⟩
theorem node1135 : UpperPrefix a [4,5,8,7,1,2] 30 :=
  local_sound a [4,5,8,7,1,2] 30 cert1135 (by decide +kernel)

def cert1136 : Local := ⟨⟨0,345,81,340,0,405,277,85,69⟩,[(0,4),(4,1)],[(5,1,0),(5,1,4),(7,3,5),(1,4,0),(3,5,1)]⟩
theorem node1136 : UpperPrefix a [4,5,8,7,1,3] 30 :=
  local_sound a [4,5,8,7,1,3] 30 cert1136 (by decide +kernel)

theorem node1137 : UpperPrefix a [4,5,8,7,1] 30 :=
  branch_upper a [4,5,8,7,1] 30 (by decide) (fin9_cases _
  node1134
  (invalid_upper a [4,5,8,7,1,1] 30 (by decide +kernel))
  node1135
  node1136
  (invalid_upper a [4,5,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,1,8] 30 (by decide +kernel)))

def cert1138 : Leaf := ⟨⟨164,0,147,18,0,411,283,91,203⟩,[(1,4),(4,1)],[(5,1,0),(2,4,0)],⟨19,38,268,137,52,107,203,459,347⟩,⟨19,38,268,137,52,96,192,384,272⟩,[⟨6,1210106412362501731656979,⟨19,55,269,141,55,32,140,397,275⟩⟩,⟨8,1181745669377130243347,⟨19,55,13,137,55,96,200,137,19⟩⟩,⟨3,1210107565283988051338515,⟨19,55,261,129,55,96,192,385,275⟩⟩]⟩
theorem node1138 : UpperPrefix a [4,5,8,7,2] 30 :=
  Boolean.leaf_sound a [4,5,8,7,2] 30 cert1138 (by decide +kernel)

def cert1139 : Leaf := ⟨⟨168,472,208,16,129,154,284,92,204⟩,[],[(5,1,0),(0,5,4),(1,6,5)],⟨19,38,268,137,56,97,194,452,340⟩,⟨19,38,268,137,56,97,194,384,272⟩,[⟨2,1210107567542257158456387,⟨19,51,264,137,56,121,251,384,272⟩⟩,⟨8,1181747927627984798787,⟨19,55,12,137,56,121,251,128,16⟩⟩,⟨6,1210106412364554692461571,⟨19,55,268,137,56,57,139,384,272⟩⟩]⟩
theorem node1139 : UpperPrefix a [4,5,8,7,3,0,1] 30 :=
  Boolean.leaf_sound a [4,5,8,7,3,0,1] 30 cert1139 (by decide +kernel)

def cert1140 : Leaf := ⟨⟨232,216,208,82,193,152,280,88,200⟩,[],[(5,1,0),(8,2,6),(0,5,4),(1,7,3)],⟨19,38,268,137,56,97,196,386,336⟩,⟨19,38,268,137,56,97,196,386,272⟩,[⟨2,1663473196641971829998723,⟨155,443,264,137,312,377,505,411,272⟩⟩]⟩
theorem node1140 : UpperPrefix a [4,5,8,7,3,0,2,1] 30 :=
  Boolean.leaf_sound a [4,5,8,7,3,0,2,1] 30 cert1140 (by decide +kernel)

def cert1141 : Leaf := ⟨⟨104,88,82,82,67,30,282,26,74⟩,[],[(5,1,0),(8,2,6),(0,5,4)],⟨19,38,268,137,56,97,196,448,274⟩,⟨19,38,268,137,56,97,196,448,272⟩,[⟨7,1345875608422303189218589,⟨279,295,287,319,319,355,359,355,279⟩⟩,⟨2,1224569812639980999148547,⟨283,443,264,393,184,505,192,448,272⟩⟩]⟩
theorem node1141 : UpperPrefix a [4,5,8,7,3,0,2,6] 30 :=
  Boolean.leaf_sound a [4,5,8,7,3,0,2,6] 30 cert1141 (by decide +kernel)

theorem node1142 : UpperPrefix a [4,5,8,7,3,0,2] 30 :=
  branch_upper a [4,5,8,7,3,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,8,7,3,0,2,0] 30 (by decide +kernel))
  node1140
  (invalid_upper a [4,5,8,7,3,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,2,5] 30 (by decide +kernel))
  node1141
  (invalid_upper a [4,5,8,7,3,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,2,8] 30 (by decide +kernel)))

theorem node1143 : UpperPrefix a [4,5,8,7,3,0] 30 :=
  branch_upper a [4,5,8,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,8,7,3,0,0] 30 (by decide +kernel))
  node1139
  node1142
  (invalid_upper a [4,5,8,7,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,0,8] 30 (by decide +kernel)))

def cert1144 : Leaf := ⟨⟨236,209,209,0,197,149,0,85,205⟩,[(3,6),(6,3)],[(5,1,0)],⟨19,38,268,137,56,98,193,452,340⟩,⟨19,38,268,137,56,98,193,384,272⟩,[⟨1,1442656606580865513029633,⟨477,436,460,461,508,508,461,384,404⟩⟩,⟨8,1181889927630566722599,⟨19,55,127,201,121,123,201,128,16⟩⟩,⟨3,1210144603027923595693057,⟨19,166,486,193,112,98,193,384,272⟩⟩]⟩
theorem node1144 : UpperPrefix a [4,5,8,7,3,1,0] 30 :=
  Boolean.leaf_sound a [4,5,8,7,3,1,0] 30 cert1144 (by decide +kernel)

def cert1145 : Leaf := ⟨⟨232,192,209,80,195,132,281,89,201⟩,[],[(5,1,0),(8,2,6),(2,6,5)],⟨19,38,268,137,56,98,196,449,337⟩,⟨19,38,268,137,56,98,196,384,272⟩,[⟨1,1214913464532609935867905,⟨477,100,460,461,252,96,196,384,336⟩⟩,⟨0,1210107567535651499836416,⟨18,38,268,136,56,98,230,384,272⟩⟩,⟨3,1210107567535650426094593,⟨19,38,260,129,48,98,230,384,272⟩⟩,⟨4,1210107567534551988208641,⟨3,38,268,137,40,98,230,384,256⟩⟩]⟩
theorem node1145 : UpperPrefix a [4,5,8,7,3,1,2] 30 :=
  Boolean.leaf_sound a [4,5,8,7,3,1,2] 30 cert1145 (by decide +kernel)

theorem node1146 : UpperPrefix a [4,5,8,7,3,1] 30 :=
  branch_upper a [4,5,8,7,3,1] 30 (by decide) (fin9_cases _
  node1144
  (invalid_upper a [4,5,8,7,3,1,1] 30 (by decide +kernel))
  node1145
  (invalid_upper a [4,5,8,7,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,1,8] 30 (by decide +kernel)))

def cert1147 : Leaf := ⟨⟨480,0,211,0,451,403,0,83,195⟩,[(1,5),(3,6),(6,3)],[(5,1,0),(2,5,1)],⟨19,38,268,137,56,100,193,450,338⟩,⟨19,38,268,137,56,100,193,384,272⟩,[⟨3,1290586548492127184112657,⟨467,166,486,449,499,230,449,448,465⟩⟩]⟩
theorem node1147 : UpperPrefix a [4,5,8,7,3,2,0] 30 :=
  Boolean.leaf_sound a [4,5,8,7,3,2,0] 30 cert1147 (by decide +kernel)

def cert1148 : Leaf := ⟨⟨160,0,211,18,131,403,273,83,195⟩,[(1,5)],[(5,1,0),(2,5,1)],⟨19,38,268,137,56,100,194,449,337⟩,⟨19,38,268,137,56,100,194,384,272⟩,[⟨3,1292979941548465704684561,⟨499,102,486,449,499,102,226,384,465⟩⟩,⟨6,1210106412364554692478003,⟨19,55,268,137,59,63,139,384,273⟩⟩,⟨8,1181745671430124618803,⟨19,55,12,137,59,127,203,128,17⟩⟩]⟩
theorem node1148 : UpperPrefix a [4,5,8,7,3,2,1] 30 :=
  Boolean.leaf_sound a [4,5,8,7,3,2,1] 30 cert1148 (by decide +kernel)

theorem node1149 : UpperPrefix a [4,5,8,7,3,2] 30 :=
  branch_upper a [4,5,8,7,3,2] 30 (by decide) (fin9_cases _
  node1147
  node1148
  (invalid_upper a [4,5,8,7,3,2,2] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,2,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,2,8] 30 (by decide +kernel)))

theorem node1150 : UpperPrefix a [4,5,8,7,3] 30 :=
  branch_upper a [4,5,8,7,3] 30 (by decide) (fin9_cases _
  node1143
  node1146
  node1149
  (invalid_upper a [4,5,8,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,8,7,3,8] 30 (by decide +kernel)))

def cert1151 : Leaf := ⟨⟨424,409,145,272,0,394,269,13,141⟩,[(4,5)],[(5,1,0),(6,4,4),(1,6,5)],⟨19,38,268,137,112,97,194,396,284⟩,⟨19,38,268,137,112,97,194,384,272⟩,[⟨2,1210107568105207111877699,⟨51,51,264,137,121,121,251,384,304⟩⟩,⟨4,1210144494834880984646657,⟨99,230,396,169,96,97,194,384,256⟩⟩]⟩
theorem node1151 : UpperPrefix a [4,5,8,7,6,0,1] 30 :=
  Boolean.leaf_sound a [4,5,8,7,6,0,1] 30 cert1151 (by decide +kernel)

#print axioms node1151
end Delivery.FiniteExclusion.Sharp4x5
