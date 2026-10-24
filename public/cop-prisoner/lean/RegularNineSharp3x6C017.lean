import RegularNineSharp3x6Base
import RegularNineSharp3x6C016
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node1088 : UpperPrefix a [3,6,4,1,8,0,5] 30 :=
  branch_upper a [3,6,4,1,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,1,8,0,5,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,1] 30 (by decide +kernel))
  node1087
  (invalid_upper a [3,6,4,1,8,0,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,8] 30 (by decide +kernel)))

theorem node1089 : UpperPrefix a [3,6,4,1,8,0] 30 :=
  branch_upper a [3,6,4,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,1] 30 (by decide +kernel))
  node1085
  (invalid_upper a [3,6,4,1,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,4] 30 (by decide +kernel))
  node1088
  (invalid_upper a [3,6,4,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,8] 30 (by decide +kernel)))

def cert1090 : Leaf := ⟨⟨0,0,456,453,205,0,301,109,229⟩,[(0,3),(1,5),(5,1)],[(1,3,0)],⟨11,70,21,26,304,100,225,417,425⟩,⟨11,70,21,26,304,100,192,384,264⟩,[⟨4,1252729001863344949316617,⟨491,230,487,491,290,230,192,384,457⟩⟩,⟨5,1210107564157953933067289,⟨15,70,29,31,287,70,192,384,269⟩⟩]⟩
theorem node1090 : UpperPrefix a [3,6,4,1,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,1,8,2] 30 cert1090 (by decide +kernel)

def cert1091 : Local := ⟨⟨0,313,360,356,76,0,316,124,116⟩,[(0,3),(5,6)],[(1,3,0),(7,5,5),(0,6,1)]⟩
theorem node1091 : UpperPrefix a [3,6,4,1,8,7,0] 30 :=
  local_sound a [3,6,4,1,8,7,0] 30 cert1091 (by decide +kernel)

def cert1092 : Local := ⟨⟨0,0,360,353,73,0,313,121,113⟩,[(0,3),(1,6),(5,6)],[(1,3,0),(7,5,5),(2,6,1)]⟩
theorem node1092 : UpperPrefix a [3,6,4,1,8,7,2] 30 :=
  local_sound a [3,6,4,1,8,7,2] 30 cert1092 (by decide +kernel)

def cert1093 : Local := ⟨⟨0,313,360,357,77,0,0,125,117⟩,[(0,3),(5,6),(6,5)],[(1,3,0),(7,5,5),(7,5,6)]⟩
theorem node1093 : UpperPrefix a [3,6,4,1,8,7,5] 30 :=
  local_sound a [3,6,4,1,8,7,5] 30 cert1093 (by decide +kernel)

theorem node1094 : UpperPrefix a [3,6,4,1,8,7] 30 :=
  branch_upper a [3,6,4,1,8,7] 30 (by decide) (fin9_cases _
  node1091
  (invalid_upper a [3,6,4,1,8,7,1] 30 (by decide +kernel))
  node1092
  (invalid_upper a [3,6,4,1,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,7,4] 30 (by decide +kernel))
  node1093
  (invalid_upper a [3,6,4,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,7,8] 30 (by decide +kernel)))

theorem node1095 : UpperPrefix a [3,6,4,1,8] 30 :=
  branch_upper a [3,6,4,1,8] 30 (by decide) (fin9_cases _
  node1089
  (invalid_upper a [3,6,4,1,8,1] 30 (by decide +kernel))
  node1090
  (invalid_upper a [3,6,4,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,6] 30 (by decide +kernel))
  node1094
  (invalid_upper a [3,6,4,1,8,8] 30 (by decide +kernel)))

theorem node1096 : UpperPrefix a [3,6,4,1] 30 :=
  branch_upper a [3,6,4,1] 30 (by decide) (fin9_cases _
  node1073
  (invalid_upper a [3,6,4,1,1] 30 (by decide +kernel))
  node1074
  (invalid_upper a [3,6,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,6] 30 (by decide +kernel))
  node1084
  node1095)

def cert1097 : Local := ⟨⟨484,424,0,0,458,394,298,106,226⟩,[(2,4),(3,2)],[(4,2,3),(2,3,0),(0,4,2),(0,4,3)]⟩
theorem node1097 : UpperPrefix a [3,6,4,2,0] 30 :=
  local_sound a [3,6,4,2,0] 30 cert1097 (by decide +kernel)

def cert1098 : Leaf := ⟨⟨292,297,298,0,329,393,297,41,161⟩,[(3,2)],[(6,1,4),(4,2,3),(2,3,0),(1,4,2)],⟨11,70,21,28,50,481,481,417,425⟩,⟨11,70,21,28,50,96,192,384,264⟩,[⟨7,1208926973665340292088883,⟨15,79,29,29,63,127,64,256,268⟩⟩]⟩
theorem node1098 : UpperPrefix a [3,6,4,2,1] 30 :=
  Boolean.leaf_sound a [3,6,4,2,1] 30 cert1098 (by decide +kernel)

def cert1099 : Leaf := ⟨⟨4,169,234,0,75,10,299,107,99⟩,[(3,2)],[(4,2,3),(2,3,0)],⟨11,70,21,28,176,97,482,418,298⟩,⟨11,70,21,28,176,97,192,384,264⟩,[⟨8,1181747995804985508979,⟨47,127,29,29,191,127,255,128,12⟩⟩,⟨7,1223094073182112491504643,⟨299,367,285,28,48,353,64,256,264⟩⟩,⟨5,1210107564157952316146691,⟨11,79,29,28,144,65,192,384,264⟩⟩,⟨6,1210106412362347616142339,⟨11,15,29,28,176,33,128,384,264⟩⟩]⟩
theorem node1099 : UpperPrefix a [3,6,4,2,7,0] 30 :=
  Boolean.leaf_sound a [3,6,4,2,7,0] 30 cert1099 (by decide +kernel)

def cert1100 : Leaf := ⟨⟨164,169,170,0,11,0,299,43,163⟩,[(3,2),(5,1)],[(6,1,5),(4,2,3),(2,3,0)],⟨11,70,21,28,176,98,481,417,297⟩,⟨11,70,21,28,176,98,192,384,264⟩,[⟨8,1181747995804985508979,⟨47,127,29,29,191,127,255,128,12⟩⟩]⟩
theorem node1100 : UpperPrefix a [3,6,4,2,7,1] 30 :=
  Boolean.leaf_sound a [3,6,4,2,7,1] 30 cert1100 (by decide +kernel)

def cert1101 : Leaf := ⟨⟨196,137,202,0,330,138,10,106,226⟩,[(3,2)],[(4,2,3),(2,3,0),(8,5,4),(0,6,1)],⟨11,70,21,28,176,352,193,418,298⟩,⟨11,70,21,28,176,352,193,384,264⟩,[⟨5,1210110158231339835342111,⟨15,79,95,95,223,321,193,449,271⟩⟩]⟩
theorem node1101 : UpperPrefix a [3,6,4,2,7,8,0] 30 :=
  Boolean.leaf_sound a [3,6,4,2,7,8,0] 30 cert1101 (by decide +kernel)

def cert1102 : Leaf := ⟨⟨68,137,202,0,331,11,9,107,99⟩,[(3,2)],[(4,2,3),(2,3,0),(8,5,4)],⟨11,70,21,28,176,352,194,417,297⟩,⟨11,70,21,28,176,352,194,384,264⟩,[⟨5,1210107852388330621648159,⟨15,79,95,95,223,321,195,385,271⟩⟩,⟨7,1223094075433912305189891,⟨299,367,285,28,48,352,355,256,264⟩⟩]⟩
theorem node1102 : UpperPrefix a [3,6,4,2,7,8,1] 30 :=
  Boolean.leaf_sound a [3,6,4,2,7,8,1] 30 cert1102 (by decide +kernel)

def cert1103 : Local := ⟨⟨228,169,234,0,0,139,0,107,227⟩,[(3,2),(4,6),(6,4)],[(4,2,3),(2,3,0),(8,5,4),(8,5,6)]⟩
theorem node1103 : UpperPrefix a [3,6,4,2,7,8,5] 30 :=
  local_sound a [3,6,4,2,7,8,5] 30 cert1103 (by decide +kernel)

theorem node1104 : UpperPrefix a [3,6,4,2,7,8] 30 :=
  branch_upper a [3,6,4,2,7,8] 30 (by decide) (fin9_cases _
  node1101
  node1102
  (invalid_upper a [3,6,4,2,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,8,4] 30 (by decide +kernel))
  node1103
  (invalid_upper a [3,6,4,2,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,8,8] 30 (by decide +kernel)))

theorem node1105 : UpperPrefix a [3,6,4,2,7] 30 :=
  branch_upper a [3,6,4,2,7] 30 (by decide) (fin9_cases _
  node1099
  node1100
  (invalid_upper a [3,6,4,2,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,7,7] 30 (by decide +kernel))
  node1104)

def cert1106 : Leaf := ⟨⟨420,425,424,0,137,394,297,41,161⟩,[(3,2)],[(4,2,3),(2,3,0),(1,6,5)],⟨11,70,21,28,304,97,194,416,424⟩,⟨11,70,21,28,304,97,194,384,264⟩,[⟨6,1437222725400065089733635,⟨11,15,413,412,444,445,131,384,264⟩⟩]⟩
theorem node1106 : UpperPrefix a [3,6,4,2,8,0,1] 30 :=
  Boolean.leaf_sound a [3,6,4,2,8,0,1] 30 cert1106 (by decide +kernel)

def cert1107 : Leaf := ⟨⟨420,424,426,0,138,394,266,42,162⟩,[(3,2)],[(4,2,3),(2,3,0)],⟨11,70,21,28,304,97,224,386,394⟩,⟨11,70,21,28,304,97,224,384,264⟩,[⟨0,1283443461042212023835648,⟨394,462,478,478,496,496,240,384,394⟩⟩,⟨6,1224301181929281180140547,⟨395,399,413,28,316,445,188,384,264⟩⟩]⟩
theorem node1107 : UpperPrefix a [3,6,4,2,8,0,5] 30 :=
  Boolean.leaf_sound a [3,6,4,2,8,0,5] 30 cert1107 (by decide +kernel)

theorem node1108 : UpperPrefix a [3,6,4,2,8,0] 30 :=
  branch_upper a [3,6,4,2,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,2,8,0,0] 30 (by decide +kernel))
  node1106
  (invalid_upper a [3,6,4,2,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,0,4] 30 (by decide +kernel))
  node1107
  (invalid_upper a [3,6,4,2,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,0,8] 30 (by decide +kernel)))

def cert1109 : Leaf := ⟨⟨388,425,426,0,139,0,299,43,163⟩,[(3,2),(5,1)],[(6,1,5),(4,2,3),(2,3,0)],⟨11,70,21,28,304,98,225,417,425⟩,⟨11,70,21,28,304,98,192,384,264⟩,[⟨5,1210107564157952316146691,⟨11,79,29,28,272,67,192,384,264⟩⟩]⟩
theorem node1109 : UpperPrefix a [3,6,4,2,8,1] 30 :=
  Boolean.leaf_sound a [3,6,4,2,8,1] 30 cert1109 (by decide +kernel)

def cert1110 : Leaf := ⟨⟨324,297,362,0,75,0,299,107,99⟩,[(3,2),(5,6)],[(4,2,3),(2,3,0),(7,5,5)],⟨11,70,21,28,304,224,227,419,299⟩,⟨11,70,21,28,304,224,192,384,264⟩,[⟨5,1210107564157952316146691,⟨11,79,29,28,272,192,192,384,264⟩⟩]⟩
theorem node1110 : UpperPrefix a [3,6,4,2,8,7] 30 :=
  Boolean.leaf_sound a [3,6,4,2,8,7] 30 cert1110 (by decide +kernel)

theorem node1111 : UpperPrefix a [3,6,4,2,8] 30 :=
  branch_upper a [3,6,4,2,8] 30 (by decide) (fin9_cases _
  node1108
  node1109
  (invalid_upper a [3,6,4,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,8,6] 30 (by decide +kernel))
  node1110
  (invalid_upper a [3,6,4,2,8,8] 30 (by decide +kernel)))

theorem node1112 : UpperPrefix a [3,6,4,2] 30 :=
  branch_upper a [3,6,4,2] 30 (by decide) (fin9_cases _
  node1097
  node1098
  (invalid_upper a [3,6,4,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,2,6] 30 (by decide +kernel))
  node1105
  node1111)

def cert1113 : Leaf := ⟨⟨84,24,0,0,78,414,286,94,214⟩,[(2,4),(3,4)],[(5,3,3),(0,4,2)],⟨11,70,21,56,49,486,454,390,398⟩,⟨11,70,21,56,49,96,192,384,264⟩,[⟨7,1208926973665889578402873,⟨31,70,29,63,63,127,64,260,285⟩⟩,⟨8,1181745671977815000121,⟨31,70,29,63,63,127,192,132,29⟩⟩]⟩
theorem node1113 : UpperPrefix a [3,6,4,5,0] 30 :=
  Boolean.leaf_sound a [3,6,4,5,0] 30 cert1113 (by decide +kernel)

def cert1114 : Leaf := ⟨⟨20,25,10,0,77,413,285,29,149⟩,[(3,4)],[(6,1,4),(5,3,3),(1,4,2)],⟨11,70,21,56,50,485,453,389,397⟩,⟨11,70,21,56,50,96,192,384,264⟩,[⟨7,1208926973665889578402873,⟨31,70,29,63,63,127,64,260,285⟩⟩,⟨8,1181745671977815000121,⟨31,70,29,63,63,127,192,132,29⟩⟩]⟩
theorem node1114 : UpperPrefix a [3,6,4,5,1] 30 :=
  Boolean.leaf_sound a [3,6,4,5,1] 30 cert1114 (by decide +kernel)

def cert1115 : Leaf := ⟨⟨64,9,74,0,75,395,267,75,195⟩,[(3,4)],[(5,3,3)],⟨11,70,21,56,52,483,451,387,395⟩,⟨11,70,21,56,52,96,192,384,264⟩,[⟨4,1252729002109635553930249,⟨491,230,487,491,230,96,192,384,489⟩⟩,⟨2,1224302388997322514105347,⟨491,491,505,56,56,96,192,384,264⟩⟩,⟨7,1208926973665889578402873,⟨31,70,29,63,63,127,64,260,285⟩⟩,⟨8,1181745671977815000121,⟨31,70,29,63,63,127,192,132,29⟩⟩]⟩
theorem node1115 : UpperPrefix a [3,6,4,5,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,2] 30 cert1115 (by decide +kernel)

def cert1116 : Leaf := ⟨⟨212,152,200,0,77,158,28,92,212⟩,[(3,4)],[(5,3,3),(1,6,5)],⟨11,70,21,56,176,97,194,388,268⟩,⟨11,70,21,56,176,97,194,384,264⟩,[⟨8,1184347566765703298559,⟨47,127,127,127,255,127,255,255,47⟩⟩,⟨0,1229052497548343109487616,⟨202,454,478,56,184,96,194,384,264⟩⟩]⟩
theorem node1116 : UpperPrefix a [3,6,4,5,7,0,1] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,0,1] 30 cert1116 (by decide +kernel)

def cert1117 : Leaf := ⟨⟨464,0,450,0,323,402,275,83,211⟩,[(1,6),(3,4)],[(5,3,3),(2,6,1)],⟨11,70,21,56,176,97,196,386,266⟩,⟨11,70,21,56,176,97,196,384,264⟩,[⟨3,1212469036900797130013697,⟨3,118,119,118,246,119,246,384,386⟩⟩]⟩
theorem node1117 : UpperPrefix a [3,6,4,5,7,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,0,2] 30 cert1117 (by decide +kernel)

def cert1118 : Leaf := ⟨⟨212,153,138,0,15,158,0,29,151⟩,[(3,4),(6,7)],[(5,3,3),(8,6,6)],⟨11,70,21,56,176,97,448,386,268⟩,⟨11,70,21,56,176,97,448,386,264⟩,[⟨6,1493476071452841830515713,⟨395,390,413,316,444,445,384,386,264⟩⟩]⟩
theorem node1118 : UpperPrefix a [3,6,4,5,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,0,8,1] 30 cert1118 (by decide +kernel)

def cert1119 : Leaf := ⟨⟨212,137,202,0,79,142,0,75,199⟩,[(3,4),(6,7)],[(5,3,3),(8,6,6)],⟨11,70,21,56,176,97,448,388,266⟩,⟨11,70,21,56,176,97,448,388,264⟩,[⟨4,1214869203295109978852353,⟨267,230,487,40,226,353,450,486,264⟩⟩]⟩
theorem node1119 : UpperPrefix a [3,6,4,5,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,0,8,2] 30 cert1119 (by decide +kernel)

theorem node1120 : UpperPrefix a [3,6,4,5,7,0,8] 30 :=
  branch_upper a [3,6,4,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,5,7,0,8,0] 30 (by decide +kernel))
  node1118
  node1119
  (invalid_upper a [3,6,4,5,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,8,8] 30 (by decide +kernel)))

theorem node1121 : UpperPrefix a [3,6,4,5,7,0] 30 :=
  branch_upper a [3,6,4,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,5,7,0,0] 30 (by decide +kernel))
  node1116
  node1117
  (invalid_upper a [3,6,4,5,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,0,7] 30 (by decide +kernel))
  node1120)

def cert1122 : Leaf := ⟨⟨148,153,138,0,15,0,287,31,151⟩,[(3,4),(5,1)],[(6,1,5),(5,3,3)],⟨11,70,21,56,176,98,453,389,269⟩,⟨11,70,21,56,176,98,192,384,264⟩,[⟨8,1181747995804448638075,⟨47,127,29,63,191,127,255,128,13⟩⟩]⟩
theorem node1122 : UpperPrefix a [3,6,4,5,7,1] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,1] 30 cert1122 (by decide +kernel)

def cert1123 : Leaf := ⟨⟨452,0,458,0,335,0,271,79,199⟩,[(1,5),(3,4),(5,1)],[(5,3,3)],⟨11,70,21,56,176,100,451,387,267⟩,⟨11,70,21,56,176,100,192,384,264⟩,[⟨4,1252729001863344949316617,⟨491,230,487,491,162,230,192,384,457⟩⟩]⟩
theorem node1123 : UpperPrefix a [3,6,4,5,7,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,2] 30 cert1123 (by decide +kernel)

def cert1124 : Leaf := ⟨⟨208,153,200,0,328,152,26,92,212⟩,[(3,4)],[(5,3,3),(8,5,4),(0,6,1),(1,7,6)],⟨11,70,21,56,176,352,193,386,268⟩,⟨11,70,21,56,176,352,193,386,264⟩,[⟨2,1210110163874063029634179,⟨11,91,89,120,249,376,249,507,264⟩⟩]⟩
theorem node1124 : UpperPrefix a [3,6,4,5,7,8,0,1] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,8,0,1] 30 cert1124 (by decide +kernel)

def cert1125 : Leaf := ⟨⟨212,137,202,0,334,142,14,74,198⟩,[(3,4)],[(5,3,3),(8,5,4),(0,6,1)],⟨11,70,21,56,176,352,193,388,266⟩,⟨11,70,21,56,176,352,193,388,264⟩,[⟨4,1214866904207500206214145,⟨267,230,487,40,162,352,483,486,264⟩⟩]⟩
theorem node1125 : UpperPrefix a [3,6,4,5,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,8,0,2] 30 cert1125 (by decide +kernel)

theorem node1126 : UpperPrefix a [3,6,4,5,7,8,0] 30 :=
  branch_upper a [3,6,4,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,5,7,8,0,0] 30 (by decide +kernel))
  node1124
  node1125
  (invalid_upper a [3,6,4,5,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,0,8] 30 (by decide +kernel)))

def cert1127 : Leaf := ⟨⟨212,145,192,0,325,149,21,92,213⟩,[(3,4)],[(3,0,7),(5,3,3),(8,5,4)],⟨11,70,21,56,176,352,194,385,268⟩,⟨11,70,21,56,176,352,194,385,264⟩,[⟨1,2225462478287797912600577,⟨445,508,413,312,444,376,508,413,264⟩⟩]⟩
theorem node1127 : UpperPrefix a [3,6,4,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,8,1,0] 30 cert1127 (by decide +kernel)

def cert1128 : Leaf := ⟨⟨208,153,200,0,329,153,29,89,209⟩,[(3,4)],[(5,3,3),(8,5,4),(2,7,6)],⟨11,70,21,56,176,352,194,388,265⟩,⟨11,70,21,56,176,352,194,388,264⟩,[⟨1,1233783961377446280036353,⟨445,508,413,56,184,376,248,388,264⟩⟩]⟩
theorem node1128 : UpperPrefix a [3,6,4,5,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,8,1,2] 30 cert1128 (by decide +kernel)

theorem node1129 : UpperPrefix a [3,6,4,5,7,8,1] 30 :=
  branch_upper a [3,6,4,5,7,8,1] 30 (by decide) (fin9_cases _
  node1127
  (invalid_upper a [3,6,4,5,7,8,1,1] 30 (by decide +kernel))
  node1128
  (invalid_upper a [3,6,4,5,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,1,8] 30 (by decide +kernel)))

def cert1130 : Leaf := ⟨⟨208,0,202,0,331,139,11,75,195⟩,[(1,6),(3,4)],[(5,3,3),(8,5,4),(2,6,1)],⟨11,70,21,56,176,352,196,387,267⟩,⟨11,70,21,56,176,352,196,384,264⟩,[⟨4,1214876156888119010954241,⟨491,230,487,40,160,354,230,384,264⟩⟩]⟩
theorem node1130 : UpperPrefix a [3,6,4,5,7,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,7,8,2] 30 cert1130 (by decide +kernel)

theorem node1131 : UpperPrefix a [3,6,4,5,7,8] 30 :=
  branch_upper a [3,6,4,5,7,8] 30 (by decide) (fin9_cases _
  node1126
  node1129
  node1130
  (invalid_upper a [3,6,4,5,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,8,8] 30 (by decide +kernel)))

theorem node1132 : UpperPrefix a [3,6,4,5,7] 30 :=
  branch_upper a [3,6,4,5,7] 30 (by decide) (fin9_cases _
  node1121
  node1122
  node1123
  (invalid_upper a [3,6,4,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,7,7] 30 (by decide +kernel))
  node1131)

def cert1133 : Leaf := ⟨⟨464,408,456,0,200,410,284,88,208⟩,[(3,4)],[(5,3,3),(1,6,5),(2,7,6)],⟨11,70,21,56,304,97,194,388,392⟩,⟨11,70,21,56,304,97,194,388,264⟩,[⟨0,1233777169876425286683648,⟨458,454,478,56,312,376,194,454,264⟩⟩]⟩
theorem node1133 : UpperPrefix a [3,6,4,5,8,0,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,8,0,1,2] 30 cert1133 (by decide +kernel)

theorem node1134 : UpperPrefix a [3,6,4,5,8,0,1] 30 :=
  branch_upper a [3,6,4,5,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,5,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,1,1] 30 (by decide +kernel))
  node1133
  (invalid_upper a [3,6,4,5,8,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,1,8] 30 (by decide +kernel)))

def cert1135 : Leaf := ⟨⟨464,0,458,0,202,410,282,90,210⟩,[(1,6),(3,4)],[(5,3,3),(2,6,1)],⟨11,70,21,56,304,97,196,386,394⟩,⟨11,70,21,56,304,97,196,384,264⟩,[⟨0,1385785240558970879380480,⟨474,454,478,440,440,506,454,384,280⟩⟩]⟩
theorem node1135 : UpperPrefix a [3,6,4,5,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,8,0,2] 30 cert1135 (by decide +kernel)

theorem node1136 : UpperPrefix a [3,6,4,5,8,0] 30 :=
  branch_upper a [3,6,4,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,5,8,0,0] 30 (by decide +kernel))
  node1134
  node1135
  (invalid_upper a [3,6,4,5,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,0,8] 30 (by decide +kernel)))

def cert1137 : Local := ⟨⟨404,409,394,0,142,0,286,30,150⟩,[(3,4),(5,1)],[(6,1,5),(5,3,3),(0,6,1)]⟩
theorem node1137 : UpperPrefix a [3,6,4,5,8,1,0] 30 :=
  local_sound a [3,6,4,5,8,1,0] 30 cert1137 (by decide +kernel)

def cert1138 : Local := ⟨⟨400,0,394,0,139,0,283,27,147⟩,[(1,6),(3,4),(5,1)],[(6,1,5),(5,3,3),(2,6,1),(2,6,5)]⟩
theorem node1138 : UpperPrefix a [3,6,4,5,8,1,2] 30 :=
  local_sound a [3,6,4,5,8,1,2] 30 cert1138 (by decide +kernel)

theorem node1139 : UpperPrefix a [3,6,4,5,8,1] 30 :=
  branch_upper a [3,6,4,5,8,1] 30 (by decide) (fin9_cases _
  node1137
  (invalid_upper a [3,6,4,5,8,1,1] 30 (by decide +kernel))
  node1138
  (invalid_upper a [3,6,4,5,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,1,8] 30 (by decide +kernel)))

def cert1140 : Leaf := ⟨⟨452,0,458,0,207,0,271,79,199⟩,[(1,5),(3,4),(5,1)],[(5,3,3)],⟨11,70,21,56,304,100,195,387,395⟩,⟨11,70,21,56,304,100,192,384,264⟩,[⟨4,1252729001863344949316617,⟨491,230,487,491,290,230,192,384,457⟩⟩]⟩
theorem node1140 : UpperPrefix a [3,6,4,5,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,5,8,2] 30 cert1140 (by decide +kernel)

def cert1141 : Local := ⟨⟨340,281,330,0,78,0,286,94,86⟩,[(3,4),(5,6)],[(5,3,3),(7,5,5),(0,6,1)]⟩
theorem node1141 : UpperPrefix a [3,6,4,5,8,7,0] 30 :=
  local_sound a [3,6,4,5,8,7,0] 30 cert1141 (by decide +kernel)

def cert1142 : Leaf := ⟨⟨340,281,328,0,77,0,285,93,85⟩,[(3,4),(5,6)],[(5,3,3),(7,5,5)],⟨11,70,21,56,304,224,194,389,269⟩,⟨11,70,21,56,304,224,194,384,264⟩,[⟨1,1233765516880770042691585,⟨445,508,413,56,312,232,248,384,264⟩⟩]⟩
theorem node1142 : UpperPrefix a [3,6,4,5,8,7,1] 30 :=
  Boolean.leaf_sound a [3,6,4,5,8,7,1] 30 cert1142 (by decide +kernel)

def cert1143 : Local := ⟨⟨336,0,330,0,75,0,283,91,83⟩,[(1,6),(3,4),(5,6)],[(5,3,3),(7,5,5),(2,6,1)]⟩
theorem node1143 : UpperPrefix a [3,6,4,5,8,7,2] 30 :=
  local_sound a [3,6,4,5,8,7,2] 30 cert1143 (by decide +kernel)

theorem node1144 : UpperPrefix a [3,6,4,5,8,7] 30 :=
  branch_upper a [3,6,4,5,8,7] 30 (by decide) (fin9_cases _
  node1141
  node1142
  node1143
  (invalid_upper a [3,6,4,5,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,7,8] 30 (by decide +kernel)))

theorem node1145 : UpperPrefix a [3,6,4,5,8] 30 :=
  branch_upper a [3,6,4,5,8] 30 (by decide) (fin9_cases _
  node1136
  node1139
  node1140
  (invalid_upper a [3,6,4,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,8,6] 30 (by decide +kernel))
  node1144
  (invalid_upper a [3,6,4,5,8,8] 30 (by decide +kernel)))

theorem node1146 : UpperPrefix a [3,6,4,5] 30 :=
  branch_upper a [3,6,4,5] 30 (by decide) (fin9_cases _
  node1113
  node1114
  node1115
  (invalid_upper a [3,6,4,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,5,6] 30 (by decide +kernel))
  node1132
  node1145)

def cert1147 : Leaf := ⟨⟨180,184,0,36,142,0,316,60,180⟩,[(2,4),(5,1)],[(6,1,5),(0,4,2),(1,5,4)],⟨11,70,21,152,49,98,484,420,300⟩,⟨11,70,21,152,49,98,192,384,264⟩,[⟨8,1181747998202917602403,⟨63,127,21,156,55,127,255,128,8⟩⟩]⟩
theorem node1147 : UpperPrefix a [3,6,4,7,0,1] 30 :=
  Boolean.leaf_sound a [3,6,4,7,0,1] 30 cert1147 (by decide +kernel)

def cert1148 : Leaf := ⟨⟨244,0,0,102,206,0,302,110,230⟩,[(1,5),(2,4),(5,1)],[(0,4,2)],⟨11,70,21,152,49,100,482,418,298⟩,⟨11,70,21,152,49,100,192,384,264⟩,[⟨4,1215024001091870701669377,⟨491,230,487,200,483,230,192,384,264⟩⟩,⟨8,1181747998202917602403,⟨63,127,21,156,55,127,255,128,8⟩⟩]⟩
theorem node1148 : UpperPrefix a [3,6,4,7,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,0,2] 30 cert1148 (by decide +kernel)

def cert1149 : Leaf := ⟨⟨180,176,0,292,204,148,52,60,180⟩,[(2,4)],[(0,4,2)],⟨11,70,21,152,49,352,194,420,300⟩,⟨11,70,21,152,49,352,194,384,264⟩,[⟨1,1300007774849315286286337,⟨445,492,413,412,445,352,480,384,264⟩⟩,⟨6,1285811850040853767652355,⟨11,15,413,412,445,288,131,384,264⟩⟩,⟨8,1184195629618839049993,⟨79,70,23,223,55,119,194,195,79⟩⟩,⟨3,1210107718406237947171841,⟨67,70,21,214,53,352,194,416,354⟩⟩]⟩
theorem node1149 : UpperPrefix a [3,6,4,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,6,4,7,0,8,1] 30 cert1149 (by decide +kernel)

def cert1150 : Leaf := ⟨⟨496,0,0,354,458,138,298,106,226⟩,[(1,6),(2,4)],[(0,4,2),(2,6,1)],⟨11,70,21,152,49,352,196,418,298⟩,⟨11,70,21,152,49,352,196,384,264⟩,[⟨4,1215171304793298363780097,⟨491,230,487,136,417,482,230,384,264⟩⟩]⟩
theorem node1150 : UpperPrefix a [3,6,4,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,7,0,8,2] 30 cert1150 (by decide +kernel)

def cert1151 : Leaf := ⟨⟨176,184,0,34,138,154,282,60,182⟩,[(2,4)],[(0,4,2),(8,5,6)],⟨11,70,21,152,49,352,224,386,268⟩,⟨11,70,21,152,49,352,224,386,264⟩,[⟨2,1210110028766617521882243,⟨91,91,17,249,49,376,249,507,376⟩⟩,⟨6,2414337535614626785920131,⟨399,415,413,413,445,316,445,399,268⟩⟩]⟩
theorem node1151 : UpperPrefix a [3,6,4,7,0,8,5,1] 30 :=
  Boolean.leaf_sound a [3,6,4,7,0,8,5,1] 30 cert1151 (by decide +kernel)

#print axioms node1151
end Delivery.FiniteExclusion.Sharp3x6
