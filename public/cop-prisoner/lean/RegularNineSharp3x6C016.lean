import RegularNineSharp3x6Base
import RegularNineSharp3x6C002
import RegularNineSharp3x6C009
import RegularNineSharp3x6C011
import RegularNineSharp3x6C013
import RegularNineSharp3x6C014
import RegularNineSharp3x6C015
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert1024 : Leaf := ⟨⟨368,0,370,98,66,147,50,114,114⟩,[(1,5)],[(7,2,5),(2,5,1)],⟨11,38,133,280,49,100,210,466,346⟩,⟨11,38,133,280,49,100,192,384,264⟩,[⟨3,1210181587256910229564929,⟨247,118,247,498,119,118,192,384,448⟩⟩,⟨0,1285813291192733985162240,⟨10,38,132,472,506,102,192,384,264⟩⟩,⟨8,1181817938266379275265,⟨59,118,247,24,51,118,192,128,8⟩⟩]⟩
theorem node1024 : UpperPrefix a [3,5,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,0,2] 30 cert1024 (by decide +kernel)

def cert1025 : Leaf := ⟨⟨320,457,330,66,330,266,268,74,66⟩,[],[(2,7,6)],⟨11,38,133,280,49,112,194,388,328⟩,⟨11,38,133,280,49,112,194,388,264⟩,[⟨4,1255238587508594725643273,⟨463,230,453,463,487,230,194,388,461⟩⟩,⟨5,1452119677076186234356739,⟨463,463,453,412,477,476,455,388,392⟩⟩,⟨0,1451003650748576644989952,⟨458,494,452,312,376,376,450,388,264⟩⟩,⟨7,1662274158277169838556227,⟨27,319,5,280,313,377,379,260,264⟩⟩]⟩
theorem node1025 : UpperPrefix a [3,5,7,8,0,4,1,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,0,4,1,2] 30 cert1025 (by decide +kernel)

def cert1026 : Leaf := ⟨⟨260,257,258,7,262,263,261,7,7⟩,[],[],⟨11,38,133,280,49,112,194,448,268⟩,⟨11,38,133,280,49,112,194,448,264⟩,[⟨3,1212542770779820028866049,⟨247,118,247,498,119,114,226,448,480⟩⟩,⟨4,1255238587508594725643273,⟨463,230,453,463,487,230,194,452,461⟩⟩,⟨5,1489824821962848557859843,⟨463,463,453,412,477,476,455,452,264⟩⟩,⟨6,2296250703424717426017395,⟨283,319,397,281,315,319,415,397,264⟩⟩,⟨7,1237261179331583776132167,⟨283,319,319,280,57,121,379,377,264⟩⟩]⟩
theorem node1026 : UpperPrefix a [3,5,7,8,0,4,1,6] 30 :=
  Boolean.leaf_sound a [3,5,7,8,0,4,1,6] 30 cert1026 (by decide +kernel)

theorem node1027 : UpperPrefix a [3,5,7,8,0,4,1] 30 :=
  branch_upper a [3,5,7,8,0,4,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,0,4,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,1,1] 30 (by decide +kernel))
  node1025
  (invalid_upper a [3,5,7,8,0,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,1,5] 30 (by decide +kernel))
  node1026
  (invalid_upper a [3,5,7,8,0,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,1,8] 30 (by decide +kernel)))

def cert1028 : Leaf := ⟨⟨356,65,330,71,70,7,0,79,71⟩,[(6,2)],[(7,2,6)],⟨11,38,133,280,49,112,196,450,330⟩,⟨11,38,133,280,49,112,196,384,264⟩,[⟨4,1252847464336837143979017,⟨463,102,453,463,487,230,196,452,461⟩⟩,⟨5,1214839532315229130327041,⟨463,70,453,348,477,92,196,384,264⟩⟩,⟨3,1210107639804694293941249,⟨51,118,247,272,49,114,246,384,256⟩⟩,⟨8,1181820190066192976897,⟨59,118,247,24,49,114,246,128,8⟩⟩]⟩
theorem node1028 : UpperPrefix a [3,5,7,8,0,4,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,0,4,2] 30 cert1028 (by decide +kernel)

theorem node1029 : UpperPrefix a [3,5,7,8,0,4] 30 :=
  branch_upper a [3,5,7,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,0,4,0] 30 (by decide +kernel))
  node1027
  node1028
  (invalid_upper a [3,5,7,8,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,4,8] 30 (by decide +kernel)))

theorem node1030 : UpperPrefix a [3,5,7,8,0] 30 :=
  branch_upper a [3,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,0,0] 30 (by decide +kernel))
  node1023
  node1024
  (invalid_upper a [3,5,7,8,0,3] 30 (by decide +kernel))
  node1029
  (invalid_upper a [3,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,8] 30 (by decide +kernel)))

def cert1031 : Leaf := ⟨⟨340,337,346,70,0,278,0,94,86⟩,[(4,1),(6,2)],[(5,1,4),(7,2,6),(0,5,1)],⟨11,38,133,280,50,97,196,464,344⟩,⟨11,38,133,280,50,97,196,384,264⟩,[⟨3,1210107637489191525321729,⟨19,118,247,272,50,115,246,384,256⟩⟩]⟩
theorem node1031 : UpperPrefix a [3,5,7,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,1,0,2] 30 cert1031 (by decide +kernel)

def cert1032 : Leaf := ⟨⟨468,209,344,196,0,148,4,92,212⟩,[(4,1)],[(5,1,4),(0,5,1)],⟨11,38,133,280,50,97,208,452,332⟩,⟨11,38,133,280,50,97,208,384,264⟩,[⟨1,1441955900555029531328513,⟨493,420,421,472,508,493,472,384,328⟩⟩,⟨3,1210107637482594455522305,⟨19,118,247,272,50,97,208,384,256⟩⟩,⟨8,1181817867966354557953,⟨27,118,247,24,50,97,208,128,8⟩⟩]⟩
theorem node1032 : UpperPrefix a [3,5,7,8,1,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,8,1,0,4] 30 cert1032 (by decide +kernel)

theorem node1033 : UpperPrefix a [3,5,7,8,1,0] 30 :=
  branch_upper a [3,5,7,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,0,1] 30 (by decide +kernel))
  node1031
  (invalid_upper a [3,5,7,8,1,0,3] 30 (by decide +kernel))
  node1032
  (invalid_upper a [3,5,7,8,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,0,8] 30 (by decide +kernel)))

def cert1034 : Leaf := ⟨⟨336,0,346,67,0,403,275,91,83⟩,[(1,5),(4,1)],[(5,1,4),(7,2,5),(2,5,1),(2,5,4)],⟨11,38,133,280,50,100,209,465,345⟩,⟨11,38,133,280,50,100,192,384,264⟩,[⟨3,1210107637555230942448641,⟨51,118,247,272,50,118,192,384,256⟩⟩]⟩
theorem node1034 : UpperPrefix a [3,5,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,1,2] 30 cert1034 (by decide +kernel)

def cert1035 : Leaf := ⟨⟨468,457,0,197,0,399,0,77,197⟩,[(2,6),(4,1),(6,2)],[(5,1,4)],⟨11,38,133,280,50,112,193,452,332⟩,⟨11,38,133,280,50,112,193,384,264⟩,[⟨1,1376340489576084317405185,⟨461,492,453,280,440,508,453,384,264⟩⟩,⟨4,1215466434508157363700737,⟨463,230,453,264,34,230,453,384,264⟩⟩]⟩
theorem node1035 : UpperPrefix a [3,5,7,8,1,4,0] 30 :=
  Boolean.leaf_sound a [3,5,7,8,1,4,0] 30 cert1035 (by decide +kernel)

def cert1036 : Leaf := ⟨⟨340,345,344,71,0,269,0,93,85⟩,[(4,1),(6,2)],[(5,1,4),(7,2,6)],⟨11,38,133,280,50,112,196,449,329⟩,⟨11,38,133,280,50,112,196,384,264⟩,[⟨1,1214876175290645125267457,⟨461,228,453,312,112,112,196,384,264⟩⟩]⟩
theorem node1036 : UpperPrefix a [3,5,7,8,1,4,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,1,4,2] 30 cert1036 (by decide +kernel)

theorem node1037 : UpperPrefix a [3,5,7,8,1,4] 30 :=
  branch_upper a [3,5,7,8,1,4] 30 (by decide) (fin9_cases _
  node1035
  (invalid_upper a [3,5,7,8,1,4,1] 30 (by decide +kernel))
  node1036
  (invalid_upper a [3,5,7,8,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,4,8] 30 (by decide +kernel)))

theorem node1038 : UpperPrefix a [3,5,7,8,1] 30 :=
  branch_upper a [3,5,7,8,1] 30 (by decide) (fin9_cases _
  node1033
  (invalid_upper a [3,5,7,8,1,1] 30 (by decide +kernel))
  node1034
  (invalid_upper a [3,5,7,8,1,3] 30 (by decide +kernel))
  node1037
  (invalid_upper a [3,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,1,8] 30 (by decide +kernel)))

def cert1039 : Leaf := ⟨⟨372,0,368,100,0,278,308,116,116⟩,[(1,4),(4,1)],[(0,5,1),(0,5,4),(1,6,5)],⟨11,38,133,280,52,97,194,464,344⟩,⟨11,38,133,280,52,97,194,384,264⟩,[⟨3,1210181586625927994174977,⟨247,118,247,466,118,119,210,384,448⟩⟩,⟨7,1511158430818737411073097,⟨27,54,5,283,54,361,379,256,265⟩⟩]⟩
theorem node1039 : UpperPrefix a [3,5,7,8,2,0,1] 30 :=
  Boolean.leaf_sound a [3,5,7,8,2,0,1] 30 cert1039 (by decide +kernel)

def cert1040 : Leaf := ⟨⟨116,0,370,102,0,22,38,118,118⟩,[(1,4),(4,1)],[(0,5,1),(0,5,4)],⟨11,38,133,280,52,97,208,450,330⟩,⟨11,38,133,280,52,97,208,384,264⟩,[⟨3,1210181586625927994174977,⟨247,118,247,466,118,119,210,384,448⟩⟩,⟨7,1511158430818737411073097,⟨27,54,5,283,54,361,379,256,265⟩⟩,⟨8,1181817867966354566153,⟨27,118,247,27,118,97,210,128,9⟩⟩]⟩
theorem node1040 : UpperPrefix a [3,5,7,8,2,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,8,2,0,4] 30 cert1040 (by decide +kernel)

theorem node1041 : UpperPrefix a [3,5,7,8,2,0] 30 :=
  branch_upper a [3,5,7,8,2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,2,0,0] 30 (by decide +kernel))
  node1039
  (invalid_upper a [3,5,7,8,2,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,0,3] 30 (by decide +kernel))
  node1040
  (invalid_upper a [3,5,7,8,2,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,0,8] 30 (by decide +kernel)))

def cert1042 : Leaf := ⟨⟨36,0,376,101,0,149,53,125,117⟩,[(1,4),(4,1)],[],⟨11,38,133,280,52,98,209,465,345⟩,⟨11,38,133,280,52,98,192,384,264⟩,[⟨1,1214839173153294269022209,⟨477,52,461,280,52,112,192,384,264⟩⟩,⟨7,1360042701115107071501371,⟨27,319,5,283,319,379,64,256,265⟩⟩,⟨8,1181818501285052165129,⟨59,118,247,59,118,114,192,128,9⟩⟩,⟨3,1210107638115913153129473,⟨51,118,247,306,118,114,192,384,256⟩⟩,⟨4,1210107565282752174498825,⟨11,38,133,267,38,98,192,384,265⟩⟩,⟨6,1210106412362484518233097,⟨27,54,133,283,54,50,128,384,265⟩⟩]⟩
theorem node1042 : UpperPrefix a [3,5,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,5,7,8,2,1] 30 cert1042 (by decide +kernel)

def cert1043 : Leaf := ⟨⟨356,0,330,103,0,399,267,75,67⟩,[(1,4),(4,1)],[],⟨11,38,133,280,52,112,195,451,331⟩,⟨11,38,133,280,52,112,192,384,264⟩,[⟨4,1252692036106497329210377,⟨463,38,453,463,38,98,192,388,461⟩⟩,⟨5,1214839172027256789009409,⟨463,6,453,280,20,80,192,384,264⟩⟩,⟨2,1214839173153156694541313,⟨459,34,449,280,48,112,192,384,264⟩⟩,⟨7,1360042701115107071501371,⟨27,319,5,283,319,379,64,256,265⟩⟩]⟩
theorem node1043 : UpperPrefix a [3,5,7,8,2,4] 30 :=
  Boolean.leaf_sound a [3,5,7,8,2,4] 30 cert1043 (by decide +kernel)

theorem node1044 : UpperPrefix a [3,5,7,8,2] 30 :=
  branch_upper a [3,5,7,8,2] 30 (by decide) (fin9_cases _
  node1041
  node1042
  (invalid_upper a [3,5,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,3] 30 (by decide +kernel))
  node1043
  (invalid_upper a [3,5,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,2,8] 30 (by decide +kernel)))

def cert1045 : Leaf := ⟨⟨308,401,312,36,0,278,308,60,52⟩,[(4,5)],[(6,4,4),(0,5,1),(1,6,5)],⟨11,38,133,280,112,97,194,404,284⟩,⟨11,38,133,280,112,97,194,384,264⟩,[⟨7,1218371709450229260485699,⟨267,319,5,312,121,121,379,256,264⟩⟩,⟨3,1210107637484793478777857,⟨19,118,247,272,112,113,210,384,256⟩⟩]⟩
theorem node1045 : UpperPrefix a [3,5,7,8,6,0,1] 30 :=
  Boolean.leaf_sound a [3,5,7,8,6,0,1] 30 cert1045 (by decide +kernel)

def cert1046 : Local := ⟨⟨308,281,314,38,0,286,0,62,54⟩,[(4,5),(6,2)],[(7,2,6),(6,4,4),(0,5,1)]⟩
theorem node1046 : UpperPrefix a [3,5,7,8,6,0,2] 30 :=
  local_sound a [3,5,7,8,6,0,2] 30 cert1046 (by decide +kernel)

def cert1047 : Leaf := ⟨⟨420,385,266,166,0,406,294,14,134⟩,[(4,5)],[(6,4,4),(0,5,1)],⟨11,38,133,280,112,97,208,390,270⟩,⟨11,38,133,280,112,97,208,384,264⟩,[⟨4,1252987021882090105103369,⟨399,166,389,399,230,487,194,388,397⟩⟩,⟨3,1210107637484793478777857,⟨19,118,247,272,112,113,208,384,256⟩⟩,⟨5,1214839154012858287916033,⟨399,6,389,280,84,453,208,384,264⟩⟩]⟩
theorem node1047 : UpperPrefix a [3,5,7,8,6,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,8,6,0,4] 30 cert1047 (by decide +kernel)

theorem node1048 : UpperPrefix a [3,5,7,8,6,0] 30 :=
  branch_upper a [3,5,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,6,0,0] 30 (by decide +kernel))
  node1045
  node1046
  (invalid_upper a [3,5,7,8,6,0,3] 30 (by decide +kernel))
  node1047
  (invalid_upper a [3,5,7,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,0,8] 30 (by decide +kernel)))

def cert1049 : Leaf := ⟨⟨436,409,0,166,0,413,0,62,182⟩,[(2,6),(4,5),(6,2)],[(6,4,4)],⟨11,38,133,280,112,98,193,404,284⟩,⟨11,38,133,280,112,98,193,384,264⟩,[⟨0,1219570744995868272755712,⟨394,446,132,280,120,506,192,384,264⟩⟩]⟩
theorem node1049 : UpperPrefix a [3,5,7,8,6,1,0] 30 :=
  Boolean.leaf_sound a [3,5,7,8,6,1,0] 30 cert1049 (by decide +kernel)

def cert1050 : Local := ⟨⟨304,281,314,35,0,285,0,59,51⟩,[(4,5),(6,2)],[(7,2,6),(6,4,4),(2,6,5)]⟩
theorem node1050 : UpperPrefix a [3,5,7,8,6,1,2] 30 :=
  local_sound a [3,5,7,8,6,1,2] 30 cert1050 (by decide +kernel)

def cert1051 : Leaf := ⟨⟨388,393,264,133,0,397,269,13,133⟩,[(4,5)],[(6,4,4)],⟨11,38,133,280,112,98,208,389,269⟩,⟨11,38,133,280,112,98,208,384,264⟩,[⟨4,1255089953521242786272521,⟨399,166,389,431,98,98,230,389,399⟩⟩,⟨5,1442011239626166385771553,⟨463,391,389,476,477,463,476,384,328⟩⟩,⟨1,1233765568603916579635201,⟨477,508,461,280,112,120,208,384,264⟩⟩]⟩
theorem node1051 : UpperPrefix a [3,5,7,8,6,1,4] 30 :=
  Boolean.leaf_sound a [3,5,7,8,6,1,4] 30 cert1051 (by decide +kernel)

theorem node1052 : UpperPrefix a [3,5,7,8,6,1] 30 :=
  branch_upper a [3,5,7,8,6,1] 30 (by decide) (fin9_cases _
  node1049
  (invalid_upper a [3,5,7,8,6,1,1] 30 (by decide +kernel))
  node1050
  (invalid_upper a [3,5,7,8,6,1,3] 30 (by decide +kernel))
  node1051
  (invalid_upper a [3,5,7,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,1,8] 30 (by decide +kernel)))

def cert1053 : Leaf := ⟨⟨304,0,314,35,0,403,307,59,51⟩,[(1,5),(4,5)],[(7,2,5),(6,4,4),(2,5,1)],⟨11,38,133,280,112,100,211,403,283⟩,⟨11,38,133,280,112,100,192,384,264⟩,[⟨3,1210107637555162222971905,⟨51,118,247,272,114,118,192,384,256⟩⟩]⟩
theorem node1053 : UpperPrefix a [3,5,7,8,6,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,6,2] 30 cert1053 (by decide +kernel)

def cert1054 : Leaf := ⟨⟨308,409,266,39,0,0,271,15,7⟩,[(4,5),(5,4)],[(6,4,4),(6,4,5)],⟨11,38,133,280,112,112,199,391,271⟩,⟨11,38,133,280,112,112,192,384,264⟩,[⟨4,1214839173152057184224257,⟨463,38,453,264,96,96,192,384,264⟩⟩,⟨5,1214839172027256789009409,⟨463,6,453,280,80,80,192,384,264⟩⟩,⟨7,1218371709450220670551043,⟨267,319,5,312,112,112,112,256,264⟩⟩]⟩
theorem node1054 : UpperPrefix a [3,5,7,8,6,4] 30 :=
  Boolean.leaf_sound a [3,5,7,8,6,4] 30 cert1054 (by decide +kernel)

theorem node1055 : UpperPrefix a [3,5,7,8,6] 30 :=
  branch_upper a [3,5,7,8,6] 30 (by decide) (fin9_cases _
  node1048
  node1052
  node1053
  (invalid_upper a [3,5,7,8,6,3] 30 (by decide +kernel))
  node1054
  (invalid_upper a [3,5,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,6,8] 30 (by decide +kernel)))

theorem node1056 : UpperPrefix a [3,5,7,8] 30 :=
  branch_upper a [3,5,7,8] 30 (by decide) (fin9_cases _
  node1030
  node1038
  node1044
  (invalid_upper a [3,5,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,5] 30 (by decide +kernel))
  node1055
  (invalid_upper a [3,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,8] 30 (by decide +kernel)))

theorem node1057 : UpperPrefix a [3,5,7] 30 :=
  branch_upper a [3,5,7] 30 (by decide) (fin9_cases _
  node921
  node938
  node975
  (invalid_upper a [3,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,5] 30 (by decide +kernel))
  node1018
  (invalid_upper a [3,5,7,7] 30 (by decide +kernel))
  node1056)

theorem node1058 : UpperPrefix a [3,5] 30 :=
  branch_upper a [3,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [3,5,1] [2,3,5] 30 (by decide +kernel) node128)
  (invalid_upper a [3,5,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,3] 30 (by decide +kernel))
  node888
  (invalid_upper a [3,5,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut16 [3,5,6] [3,4,7] 30 (by decide +kernel) node738)
  node1057
  (PrefixConjugacy.upper aut7 [3,5,8] [3,4,6] 30 (by decide +kernel) node606))

def cert1059 : Leaf := ⟨⟨52,49,0,0,69,405,309,53,181⟩,[(2,3),(3,2)],[(6,1,4),(1,4,2),(1,4,3)],⟨11,70,21,25,50,484,484,420,428⟩,⟨11,70,21,25,50,96,192,384,264⟩,[⟨3,1212473369244891398407169,⟨7,70,21,21,50,96,208,498,502⟩⟩,⟨7,1208926973665340292088883,⟨15,79,29,29,63,127,64,256,268⟩⟩,⟨8,1181745671428528686131,⟨15,79,29,29,63,127,192,128,12⟩⟩]⟩
theorem node1059 : UpperPrefix a [3,6,4,0,1] 30 :=
  Boolean.leaf_sound a [3,6,4,0,1] 30 cert1059 (by decide +kernel)

def cert1060 : Leaf := ⟨⟨480,424,0,0,458,394,298,106,226⟩,[(2,3),(3,2)],[],⟨11,70,21,25,52,482,482,418,426⟩,⟨11,70,21,25,52,96,192,384,264⟩,[⟨0,1252729002111147382418432,⟨506,246,502,506,246,96,192,384,488⟩⟩,⟨4,1252729002109635553930249,⟨491,230,487,491,230,96,192,384,489⟩⟩,⟨2,1224302388997320366621699,⟨491,491,505,505,56,96,192,384,264⟩⟩]⟩
theorem node1060 : UpperPrefix a [3,6,4,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,0,2] 30 cert1060 (by decide +kernel)

def cert1061 : Leaf := ⟨⟨180,177,0,0,7,0,311,55,183⟩,[(2,3),(3,2),(5,1)],[(6,1,5)],⟨11,70,21,25,176,98,484,420,300⟩,⟨11,70,21,25,176,98,192,384,264⟩,[⟨3,1212473373823257816466433,⟨39,118,21,21,176,114,240,498,502⟩⟩,⟨8,1181747995804985508979,⟨47,127,29,29,191,127,255,128,12⟩⟩]⟩
theorem node1061 : UpperPrefix a [3,6,4,0,7,1] 30 :=
  Boolean.leaf_sound a [3,6,4,0,7,1] 30 cert1061 (by decide +kernel)

def cert1062 : Leaf := ⟨⟨500,0,0,0,334,0,318,126,246⟩,[(1,5),(2,3),(3,2),(5,1)],[],⟨11,70,21,25,176,100,482,418,298⟩,⟨11,70,21,25,176,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,178,246,192,384,264⟩⟩]⟩
theorem node1062 : UpperPrefix a [3,6,4,0,7,2] 30 :=
  Boolean.leaf_sound a [3,6,4,0,7,2] 30 cert1062 (by decide +kernel)

def cert1063 : Leaf := ⟨⟨212,145,0,0,325,149,21,117,245⟩,[(2,3),(3,2)],[(8,5,4)],⟨11,70,21,25,176,352,194,420,300⟩,⟨11,70,21,25,176,352,194,384,264⟩,[⟨3,1212476256058849612661761,⟨7,86,21,21,240,498,242,498,502⟩⟩,⟨1,1224302337175344622338049,⟨445,508,413,413,176,368,496,384,268⟩⟩,⟨5,1210107852388330621648159,⟨15,79,95,95,223,321,195,385,271⟩⟩]⟩
theorem node1063 : UpperPrefix a [3,6,4,0,7,8,1] 30 :=
  Boolean.leaf_sound a [3,6,4,0,7,8,1] 30 cert1063 (by decide +kernel)

def cert1064 : Leaf := ⟨⟨240,0,0,0,330,154,58,122,242⟩,[(1,6),(2,3),(3,2)],[(8,5,4),(2,6,1)],⟨11,70,21,25,176,352,196,418,298⟩,⟨11,70,21,25,176,352,196,384,264⟩,[⟨0,1215171304802025737325568,⟨506,246,502,440,176,498,246,384,280⟩⟩]⟩
theorem node1064 : UpperPrefix a [3,6,4,0,7,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,0,7,8,2] 30 cert1064 (by decide +kernel)

def cert1065 : Local := ⟨⟨244,185,0,0,0,159,0,127,247⟩,[(2,3),(3,2),(4,6),(6,4)],[(8,5,4),(8,5,6)]⟩
theorem node1065 : UpperPrefix a [3,6,4,0,7,8,5] 30 :=
  local_sound a [3,6,4,0,7,8,5] 30 cert1065 (by decide +kernel)

theorem node1066 : UpperPrefix a [3,6,4,0,7,8] 30 :=
  branch_upper a [3,6,4,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,0,7,8,0] 30 (by decide +kernel))
  node1063
  node1064
  (invalid_upper a [3,6,4,0,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,7,8,4] 30 (by decide +kernel))
  node1065
  (invalid_upper a [3,6,4,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,7,8,8] 30 (by decide +kernel)))

theorem node1067 : UpperPrefix a [3,6,4,0,7] 30 :=
  branch_upper a [3,6,4,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,0,7,0] 30 (by decide +kernel))
  node1061
  node1062
  (invalid_upper a [3,6,4,0,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,7,7] 30 (by decide +kernel))
  node1066)

def cert1068 : Leaf := ⟨⟨432,433,0,0,135,0,311,55,183⟩,[(2,3),(3,2),(5,1)],[(6,1,5)],⟨11,70,21,25,304,98,228,420,428⟩,⟨11,70,21,25,304,98,192,384,264⟩,[⟨3,1212473374381809723376641,⟨39,102,53,53,498,98,240,498,502⟩⟩,⟨2,1210107565354220966118403,⟨43,107,25,25,304,99,192,384,264⟩⟩]⟩
theorem node1068 : UpperPrefix a [3,6,4,0,8,1] 30 :=
  Boolean.leaf_sound a [3,6,4,0,8,1] 30 cert1068 (by decide +kernel)

def cert1069 : Leaf := ⟨⟨500,0,0,0,206,0,318,126,246⟩,[(1,5),(2,3),(3,2),(5,1)],[],⟨11,70,21,25,304,100,226,418,426⟩,⟨11,70,21,25,304,100,192,384,264⟩,[⟨0,1215024613582863133068288,⟨506,246,502,472,498,246,192,384,264⟩⟩]⟩
theorem node1069 : UpperPrefix a [3,6,4,0,8,2] 30 :=
  Boolean.leaf_sound a [3,6,4,0,8,2] 30 cert1069 (by decide +kernel)

def cert1070 : Leaf := ⟨⟨368,305,0,0,71,0,311,119,119⟩,[(2,3),(3,2),(5,6)],[(7,5,5)],⟨11,70,21,25,304,224,230,422,302⟩,⟨11,70,21,25,304,224,192,384,264⟩,[⟨3,1212473376563240792884225,⟨7,102,53,53,498,240,240,498,502⟩⟩,⟨2,1210107567535652035625987,⟨11,107,25,25,304,224,224,384,264⟩⟩]⟩
theorem node1070 : UpperPrefix a [3,6,4,0,8,7] 30 :=
  Boolean.leaf_sound a [3,6,4,0,8,7] 30 cert1070 (by decide +kernel)

theorem node1071 : UpperPrefix a [3,6,4,0,8] 30 :=
  branch_upper a [3,6,4,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,0,8,0] 30 (by decide +kernel))
  node1068
  node1069
  (invalid_upper a [3,6,4,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,8,6] 30 (by decide +kernel))
  node1070
  (invalid_upper a [3,6,4,0,8,8] 30 (by decide +kernel)))

theorem node1072 : UpperPrefix a [3,6,4,0] 30 :=
  branch_upper a [3,6,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,0,0] 30 (by decide +kernel))
  node1059
  node1060
  (invalid_upper a [3,6,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,0,6] 30 (by decide +kernel))
  node1067
  node1071)

def cert1073 : Leaf := ⟨⟨0,56,0,100,76,412,316,124,244⟩,[(0,3),(2,4)],[(1,3,0),(0,4,2)],⟨11,70,21,26,49,484,484,420,428⟩,⟨11,70,21,26,49,96,192,384,264⟩,[⟨7,1208926973665339755217977,⟨15,70,29,31,63,127,64,256,269⟩⟩,⟨8,1181745671427991815225,⟨15,70,29,31,63,127,192,128,13⟩⟩]⟩
theorem node1073 : UpperPrefix a [3,6,4,1,0] 30 :=
  Boolean.leaf_sound a [3,6,4,1,0] 30 cert1073 (by decide +kernel)

def cert1074 : Leaf := ⟨⟨0,41,104,101,73,393,297,105,225⟩,[(0,3)],[(1,3,0),(2,4,3)],⟨11,70,21,26,52,481,481,417,425⟩,⟨11,70,21,26,52,96,192,384,264⟩,[⟨4,1255094806044288058665993,⟨491,230,487,491,230,96,192,480,489⟩⟩,⟨7,1208926973665339755217977,⟨15,70,29,31,63,127,64,256,269⟩⟩,⟨8,1181745671427991815225,⟨15,70,29,31,63,127,192,128,13⟩⟩]⟩
theorem node1074 : UpperPrefix a [3,6,4,1,2] 30 :=
  Boolean.leaf_sound a [3,6,4,1,2] 30 cert1074 (by decide +kernel)

def cert1075 : Leaf := ⟨⟨0,0,488,480,328,408,312,120,240⟩,[(0,3),(1,6)],[(1,3,0),(2,6,1)],⟨11,70,21,26,176,97,196,416,296⟩,⟨11,70,21,26,176,97,196,384,264⟩,[⟨0,1437223950379161578671104,⟨10,78,478,410,440,506,206,384,264⟩⟩]⟩
theorem node1075 : UpperPrefix a [3,6,4,1,7,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,1,7,0,2] 30 cert1075 (by decide +kernel)

def cert1076 : Leaf := ⟨⟨0,440,488,484,0,412,0,124,244⟩,[(0,3),(4,6),(6,4)],[(1,3,0)],⟨11,70,21,26,176,97,224,388,268⟩,⟨11,70,21,26,176,97,224,384,264⟩,[⟨0,1238497392648065689586688,⟨394,478,478,474,240,112,240,384,264⟩⟩]⟩
theorem node1076 : UpperPrefix a [3,6,4,1,7,0,5] 30 :=
  Boolean.leaf_sound a [3,6,4,1,7,0,5] 30 cert1076 (by decide +kernel)

def cert1077 : Leaf := ⟨⟨0,153,136,197,77,156,0,125,245⟩,[(0,3),(6,7)],[(1,3,0),(8,6,6)],⟨11,70,21,26,176,97,448,420,300⟩,⟨11,70,21,26,176,97,448,384,264⟩,[⟨5,1210109870000963683623967,⟨15,79,31,31,223,65,448,448,269⟩⟩,⟨6,1210106412362347081368585,⟨15,6,21,31,176,33,384,384,269⟩⟩]⟩
theorem node1077 : UpperPrefix a [3,6,4,1,7,0,8] 30 :=
  Boolean.leaf_sound a [3,6,4,1,7,0,8] 30 cert1077 (by decide +kernel)

theorem node1078 : UpperPrefix a [3,6,4,1,7,0] 30 :=
  branch_upper a [3,6,4,1,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,1,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,0,1] 30 (by decide +kernel))
  node1075
  (invalid_upper a [3,6,4,1,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,0,4] 30 (by decide +kernel))
  node1076
  (invalid_upper a [3,6,4,1,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,0,7] 30 (by decide +kernel))
  node1077)

def cert1079 : Leaf := ⟨⟨0,0,360,357,333,0,301,109,101⟩,[(0,3),(1,5),(5,1)],[(1,3,0)],⟨11,70,21,26,176,100,481,417,297⟩,⟨11,70,21,26,176,100,192,384,264⟩,[⟨4,1252729001863344949316617,⟨491,230,487,491,162,230,192,384,457⟩⟩,⟨7,1326986135805246303126553,⟨303,102,285,319,319,102,64,256,269⟩⟩]⟩
theorem node1079 : UpperPrefix a [3,6,4,1,7,2] 30 :=
  Boolean.leaf_sound a [3,6,4,1,7,2] 30 cert1079 (by decide +kernel)

def cert1080 : Leaf := ⟨⟨0,153,136,196,332,156,28,124,244⟩,[(0,3)],[(1,3,0),(8,5,4),(0,6,1)],⟨11,70,21,26,176,352,193,420,300⟩,⟨11,70,21,26,176,352,193,384,264⟩,[⟨5,1210110158231339835342111,⟨15,79,95,95,223,321,193,449,271⟩⟩,⟨6,1210106412362347081368585,⟨15,6,21,31,176,288,129,384,269⟩⟩]⟩
theorem node1080 : UpperPrefix a [3,6,4,1,7,8,0] 30 :=
  Boolean.leaf_sound a [3,6,4,1,7,8,0] 30 cert1080 (by decide +kernel)

def cert1081 : Local := ⟨⟨0,0,232,225,329,153,57,121,241⟩,[(0,3),(1,6)],[(1,3,0),(8,5,4),(2,6,1)]⟩
theorem node1081 : UpperPrefix a [3,6,4,1,7,8,2] 30 :=
  local_sound a [3,6,4,1,7,8,2] 30 cert1081 (by decide +kernel)

def cert1082 : Leaf := ⟨⟨0,185,168,165,0,157,0,61,181⟩,[(0,3),(4,6),(6,4)],[(1,3,0),(8,5,4),(8,5,6)],⟨11,70,21,26,176,352,224,389,269⟩,⟨11,70,21,26,176,352,224,384,264⟩,[⟨6,1264551977502498161689611,⟨399,415,405,415,176,432,176,384,397⟩⟩]⟩
theorem node1082 : UpperPrefix a [3,6,4,1,7,8,5] 30 :=
  Boolean.leaf_sound a [3,6,4,1,7,8,5] 30 cert1082 (by decide +kernel)

theorem node1083 : UpperPrefix a [3,6,4,1,7,8] 30 :=
  branch_upper a [3,6,4,1,7,8] 30 (by decide) (fin9_cases _
  node1080
  (invalid_upper a [3,6,4,1,7,8,1] 30 (by decide +kernel))
  node1081
  (invalid_upper a [3,6,4,1,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,8,4] 30 (by decide +kernel))
  node1082
  (invalid_upper a [3,6,4,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,8,8] 30 (by decide +kernel)))

theorem node1084 : UpperPrefix a [3,6,4,1,7] 30 :=
  branch_upper a [3,6,4,1,7] 30 (by decide) (fin9_cases _
  node1078
  (invalid_upper a [3,6,4,1,7,1] 30 (by decide +kernel))
  node1079
  (invalid_upper a [3,6,4,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,7,7] 30 (by decide +kernel))
  node1083)

def cert1085 : Leaf := ⟨⟨0,0,488,480,200,408,312,120,240⟩,[(0,3),(1,6)],[(1,3,0),(2,6,1)],⟨11,70,21,26,304,97,196,416,424⟩,⟨11,70,21,26,304,97,196,384,264⟩,[⟨0,1437223950379161578671104,⟨10,78,478,410,440,506,206,384,264⟩⟩]⟩
theorem node1085 : UpperPrefix a [3,6,4,1,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,4,1,8,0,2] 30 cert1085 (by decide +kernel)

def cert1086 : Leaf := ⟨⟨0,185,168,229,137,152,25,57,53⟩,[(0,3)],[(1,3,0)],⟨11,70,21,26,304,97,224,388,392⟩,⟨11,70,21,26,304,97,224,388,392⟩,[⟨8,1188679594170236741023,⟨47,111,63,63,127,97,227,239,239⟩⟩,⟨6,1255531519646055883867145,⟨399,134,405,415,436,437,180,388,397⟩⟩,⟨2,1210114491846466859959305,⟨11,66,17,27,368,97,240,496,505⟩⟩]⟩
theorem node1086 : UpperPrefix a [3,6,4,1,8,0,5,2,7] 30 :=
  Boolean.leaf_sound a [3,6,4,1,8,0,5,2,7] 30 cert1086 (by decide +kernel)

theorem node1087 : UpperPrefix a [3,6,4,1,8,0,5,2] 30 :=
  branch_upper a [3,6,4,1,8,0,5,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,4,1,8,0,5,2,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,4,1,8,0,5,2,6] 30 (by decide +kernel))
  node1086
  (invalid_upper a [3,6,4,1,8,0,5,2,8] 30 (by decide +kernel)))

#print axioms node1087
end Delivery.FiniteExclusion.Sharp3x6
