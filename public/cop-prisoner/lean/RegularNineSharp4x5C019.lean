import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C001
import RegularNineSharp4x5C002
import RegularNineSharp4x5C003
import RegularNineSharp4x5C004
import RegularNineSharp4x5C006
import RegularNineSharp4x5C007
import RegularNineSharp4x5C009
import RegularNineSharp4x5C010
import RegularNineSharp4x5C011
import RegularNineSharp4x5C012
import RegularNineSharp4x5C014
import RegularNineSharp4x5C016
import RegularNineSharp4x5C017
import RegularNineSharp4x5C018
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
theorem node1216 : UpperPrefix a [4,6,5] 30 :=
  branch_upper a [4,6,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,6,5,1] [2,4,6,5] 30 (by decide +kernel) node212)
  (PrefixConjugacy.upper aut5 [4,6,5,2] [3,4,6,5] 30 (by decide +kernel) node671)
  (invalid_upper a [4,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,6] 30 (by decide +kernel))
  node1215
  (PrefixConjugacy.upper aut6 [4,6,5,8] [4,5,7,6] 30 (by decide +kernel) node1083))

theorem node1217 : UpperPrefix a [4,6,7] 30 :=
  branch_upper a [4,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,6,7,1] [2,4,6,7] 30 (by decide +kernel) node244)
  (PrefixConjugacy.upper aut5 [4,6,7,2] [3,4,6,7] 30 (by decide +kernel) node713)
  (invalid_upper a [4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [4,6,7,5] [4,5,8,7] 30 (by decide +kernel) node1162)
  (invalid_upper a [4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [4,6,7,8] [4,5,6,7] 30 (by decide +kernel) node1041))

theorem node1218 : UpperPrefix a [4,6,8] 30 :=
  branch_upper a [4,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,6,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,6,8,1] [2,4,6,8] 30 (by decide +kernel) node270)
  (PrefixConjugacy.upper aut5 [4,6,8,2] [3,4,6,8] 30 (by decide +kernel) node747)
  (invalid_upper a [4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,8,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut11 [4,6,8,5] [4,6,5,7] 30 (by decide +kernel) node1215)
  (invalid_upper a [4,6,8,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [4,6,8,7] [4,6,5,7] 30 (by decide +kernel) node1215)
  (invalid_upper a [4,6,8,8] 30 (by decide +kernel)))

theorem node1219 : UpperPrefix a [4,6] 30 :=
  branch_upper a [4,6] 30 (by decide) (fin9_cases _
  node1165
  node1166
  (invalid_upper a [4,6,2] 30 (by decide +kernel))
  (invalid_upper a [4,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,4] 30 (by decide +kernel))
  node1216
  (invalid_upper a [4,6,6] 30 (by decide +kernel))
  node1217
  node1218)

theorem node1220 : UpperPrefix a [4,7,0] 30 :=
  branch_upper a [4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,7,0,1] [2,3,4,7] 30 (by decide +kernel) node80)
  (PrefixConjugacy.upper aut10 [4,7,0,2] [2,0,4,7] 30 (by decide +kernel) node39)
  (invalid_upper a [4,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,0,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,7,0,5] [2,4,8,6] 30 (by decide +kernel) node420)
  (PrefixConjugacy.upper aut13 [4,7,0,6] [2,4,7,5] 30 (by decide +kernel) node301)
  (invalid_upper a [4,7,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut11 [4,7,0,8] [2,4,5,8] 30 (by decide +kernel) node185))

theorem node1221 : UpperPrefix a [4,7,1] 30 :=
  branch_upper a [4,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,7,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,7,1,2] [3,0,4,7] 30 (by decide +kernel) node487)
  (invalid_upper a [4,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,1,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,7,1,5] [3,4,8,6] 30 (by decide +kernel) node946)
  (PrefixConjugacy.upper aut13 [4,7,1,6] [3,4,7,5] 30 (by decide +kernel) node797)
  (invalid_upper a [4,7,1,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut11 [4,7,1,8] [3,4,5,8] 30 (by decide +kernel) node625))

theorem node1222 : UpperPrefix a [4,7,5] 30 :=
  branch_upper a [4,7,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,7,5,1] [2,4,7,5] 30 (by decide +kernel) node301)
  (PrefixConjugacy.upper aut5 [4,7,5,2] [3,4,7,5] 30 (by decide +kernel) node797)
  (invalid_upper a [4,7,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,5,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [4,7,5,6] [4,5,8,6] 30 (by decide +kernel) node1129)
  (invalid_upper a [4,7,5,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [4,7,5,8] [4,5,8,6] 30 (by decide +kernel) node1129))

def cert1223 : Leaf := ⟨⟨300,297,289,0,0,397,301,45,45⟩,[(3,4),(4,3)],[(7,1,5),(1,5,3),(1,5,4)],⟨19,134,76,41,49,98,460,396,284⟩,⟨19,134,76,41,49,98,192,384,272⟩,[⟨4,1212473375972806335071233,⟨11,166,108,41,41,98,226,486,494⟩⟩,⟨6,1229032771784728300751909,⟨27,391,415,57,57,59,128,384,280⟩⟩]⟩
theorem node1223 : UpperPrefix a [4,7,6,5,0,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,0,1] 30 cert1223 (by decide +kernel)

def cert1224 : Leaf := ⟨⟨428,297,419,0,0,0,299,43,171⟩,[(3,4),(4,3),(5,2)],[(6,2,5)],⟨19,134,76,41,49,100,458,394,282⟩,⟨19,134,76,41,49,100,192,384,272⟩,[⟨4,1212473373861744009741313,⟨11,166,108,41,41,100,226,486,494⟩⟩,⟨2,1214839173153708597838849,⟨475,130,88,505,505,96,192,384,280⟩⟩]⟩
theorem node1224 : UpperPrefix a [4,7,6,5,0,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,0,2] 30 cert1224 (by decide +kernel)

def cert1225 : Leaf := ⟨⟨484,369,0,0,0,0,311,119,231⟩,[(2,5),(3,4),(4,3),(5,2)],[],⟨19,134,76,41,49,104,454,390,278⟩,⟨19,134,76,41,49,104,192,384,272⟩,[⟨3,1229052479534491134594053,⟨211,455,471,49,49,112,192,384,272⟩⟩]⟩
theorem node1225 : UpperPrefix a [4,7,6,5,0,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,0,3] 30 cert1225 (by decide +kernel)

def cert1226 : Leaf := ⟨⟨364,361,291,0,0,15,0,111,111⟩,[(3,4),(4,3),(6,1)],[(7,1,6)],⟨19,134,76,41,49,352,194,396,284⟩,⟨19,134,76,41,49,352,194,384,272⟩,[⟨4,1212476292053565064037377,⟨79,230,76,111,111,486,226,486,494⟩⟩]⟩
theorem node1226 : UpperPrefix a [4,7,6,5,0,8,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,0,8,1] 30 cert1226 (by decide +kernel)

def cert1227 : Leaf := ⟨⟨492,0,419,0,0,143,0,111,239⟩,[(1,6),(3,4),(4,3),(6,1)],[],⟨19,134,76,41,49,352,196,394,282⟩,⟨19,134,76,41,49,352,196,384,272⟩,[⟨4,1212476292053565064070145,⟨79,230,78,111,111,486,230,486,494⟩⟩]⟩
theorem node1227 : UpperPrefix a [4,7,6,5,0,8,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,0,8,2] 30 cert1227 (by decide +kernel)

def cert1228 : Leaf := ⟨⟨484,353,0,0,0,135,295,103,231⟩,[(2,6),(3,4),(4,3)],[(3,6,2)],⟨19,134,76,41,49,352,200,390,278⟩,⟨19,134,76,41,49,352,200,384,272⟩,[⟨4,1212768953971750125171713,⟨79,166,78,239,239,486,238,486,494⟩⟩]⟩
theorem node1228 : UpperPrefix a [4,7,6,5,0,8,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,0,8,3] 30 cert1228 (by decide +kernel)

theorem node1229 : UpperPrefix a [4,7,6,5,0,8] 30 :=
  branch_upper a [4,7,6,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,5,0,8,0] 30 (by decide +kernel))
  node1226
  node1227
  node1228
  (invalid_upper a [4,7,6,5,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,0,8,8] 30 (by decide +kernel)))

theorem node1230 : UpperPrefix a [4,7,6,5,0] 30 :=
  branch_upper a [4,7,6,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,5,0,0] 30 (by decide +kernel))
  node1223
  node1224
  node1225
  (invalid_upper a [4,7,6,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,0,7] 30 (by decide +kernel))
  node1229)

def cert1231 : Leaf := ⟨⟨0,120,176,0,204,156,316,124,236⟩,[(0,4),(3,5)],[(1,4,0),(0,5,3)],⟨19,134,76,41,50,97,460,396,284⟩,⟨19,134,76,41,50,97,192,384,272⟩,[⟨8,1181748068785062970487,⟨27,191,127,61,63,127,255,128,25⟩⟩]⟩
theorem node1231 : UpperPrefix a [4,7,6,5,1,0] 30 :=
  Boolean.leaf_sound a [4,7,6,5,1,0] 30 cert1231 (by decide +kernel)

def cert1232 : Leaf := ⟨⟨0,57,177,144,141,0,313,57,169⟩,[(0,4),(5,2)],[(6,2,5),(1,4,0),(2,5,4)],⟨19,134,76,41,50,100,457,393,281⟩,⟨19,134,76,41,50,100,192,384,272⟩,[⟨8,1181748068785062970487,⟨27,191,127,61,63,127,255,128,25⟩⟩]⟩
theorem node1232 : UpperPrefix a [4,7,6,5,1,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,1,2] 30 cert1232 (by decide +kernel)

def cert1233 : Leaf := ⟨⟨0,345,0,340,333,0,285,93,77⟩,[(0,4),(2,5),(5,2)],[(1,4,0)],⟨19,134,76,41,50,104,453,389,277⟩,⟨19,134,76,41,50,104,192,384,272⟩,[⟨5,1285813290066831939216657,⟨467,134,76,13,471,76,192,385,467⟩⟩,⟨7,1293929570495665240278035,⟨283,319,108,45,319,108,64,256,281⟩⟩]⟩
theorem node1233 : UpperPrefix a [4,7,6,5,1,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,1,3] 30 cert1233 (by decide +kernel)

def cert1234 : Local := ⟨⟨0,0,433,464,456,152,312,120,232⟩,[(0,4),(1,7)],[(1,4,0),(0,6,2),(2,7,1)]⟩
theorem node1234 : UpperPrefix a [4,7,6,5,1,8,0,2] 30 :=
  local_sound a [4,7,6,5,1,8,0,2] 30 cert1234 (by decide +kernel)

def cert1235 : Leaf := ⟨⟨0,360,417,452,452,132,292,100,228⟩,[(0,4)],[(1,4,0),(0,6,2),(3,7,1)],⟨19,134,76,41,50,352,193,392,276⟩,⟨19,134,76,41,50,352,193,392,272⟩,[⟨4,1210402861806727881421825,⟨3,166,78,239,166,494,239,494,258⟩⟩]⟩
theorem node1235 : UpperPrefix a [4,7,6,5,1,8,0,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,1,8,0,3] 30 cert1235 (by decide +kernel)

theorem node1236 : UpperPrefix a [4,7,6,5,1,8,0] 30 :=
  branch_upper a [4,7,6,5,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,5,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,0,1] 30 (by decide +kernel))
  node1234
  node1235
  (invalid_upper a [4,7,6,5,1,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,0,8] 30 (by decide +kernel)))

def cert1237 : Leaf := ⟨⟨0,0,433,404,397,157,0,61,173⟩,[(0,4),(1,6),(6,1)],[(1,4,0)],⟨19,134,76,41,50,352,196,393,281⟩,⟨19,134,76,41,50,352,196,384,272⟩,[⟨6,1482168217335657867021361,⟨411,134,398,441,443,443,134,384,409⟩⟩]⟩
theorem node1237 : UpperPrefix a [4,7,6,5,1,8,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,1,8,2] 30 cert1237 (by decide +kernel)

def cert1238 : Leaf := ⟨⟨0,112,0,212,196,149,309,117,229⟩,[(0,4),(2,6)],[(1,4,0),(3,6,2)],⟨19,134,76,41,50,352,200,389,277⟩,⟨19,134,76,41,50,352,200,384,272⟩,[⟨8,1181745671428002317361,⟨27,134,78,61,63,127,206,128,25⟩⟩,⟨0,1210107565286050726183936,⟨18,134,78,56,50,374,206,384,272⟩⟩]⟩
theorem node1238 : UpperPrefix a [4,7,6,5,1,8,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,1,8,3] 30 cert1238 (by decide +kernel)

theorem node1239 : UpperPrefix a [4,7,6,5,1,8] 30 :=
  branch_upper a [4,7,6,5,1,8] 30 (by decide) (fin9_cases _
  node1236
  (invalid_upper a [4,7,6,5,1,8,1] 30 (by decide +kernel))
  node1237
  node1238
  (invalid_upper a [4,7,6,5,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,8,8] 30 (by decide +kernel)))

theorem node1240 : UpperPrefix a [4,7,6,5,1] 30 :=
  branch_upper a [4,7,6,5,1] 30 (by decide) (fin9_cases _
  node1231
  (invalid_upper a [4,7,6,5,1,1] 30 (by decide +kernel))
  node1232
  node1233
  (invalid_upper a [4,7,6,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,1,7] 30 (by decide +kernel))
  node1239)

def cert1241 : Leaf := ⟨⟨172,56,176,0,200,154,314,58,170⟩,[(3,5)],[(6,2,4),(2,4,0),(0,5,3)],⟨19,134,76,41,52,97,458,394,282⟩,⟨19,134,76,41,52,97,192,384,272⟩,[⟨8,1181748069334818784359,⟨27,191,127,61,61,127,255,128,24⟩⟩,⟨1,1210107565286604768542721,⟨17,132,92,61,60,125,192,384,272⟩⟩]⟩
theorem node1241 : UpperPrefix a [4,7,6,5,2,0] 30 :=
  Boolean.leaf_sound a [4,7,6,5,2,0] 30 cert1241 (by decide +kernel)

def cert1242 : Leaf := ⟨⟨44,56,49,18,72,152,56,56,40⟩,[],[(7,1,5),(6,2,4),(2,4,0),(1,5,3),(0,6,2)],⟨19,134,76,41,52,98,193,392,280⟩,⟨19,134,76,41,52,98,193,384,272⟩,[⟨8,1184094559175956071655,⟨127,255,127,61,61,127,255,255,24⟩⟩]⟩
theorem node1242 : UpperPrefix a [4,7,6,5,2,1,0] 30 :=
  Boolean.leaf_sound a [4,7,6,5,2,1,0] 30 cert1242 (by decide +kernel)

def cert1243 : Local := ⟨⟨292,305,0,274,321,401,305,49,33⟩,[(2,6)],[(7,1,5),(6,2,4),(2,4,0),(1,5,3),(3,6,2)]⟩
theorem node1243 : UpperPrefix a [4,7,6,5,2,1,3] 30 :=
  local_sound a [4,7,6,5,2,1,3] 30 cert1243 (by decide +kernel)

def cert1244 : Local := ⟨⟨44,57,49,18,73,153,0,57,41⟩,[(6,7)],[(7,1,5),(6,2,4),(2,4,0),(1,5,3),(8,6,6)]⟩
theorem node1244 : UpperPrefix a [4,7,6,5,2,1,8] 30 :=
  local_sound a [4,7,6,5,2,1,8] 30 cert1244 (by decide +kernel)

theorem node1245 : UpperPrefix a [4,7,6,5,2,1] 30 :=
  branch_upper a [4,7,6,5,2,1] 30 (by decide) (fin9_cases _
  node1242
  (invalid_upper a [4,7,6,5,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,1,2] 30 (by decide +kernel))
  node1243
  (invalid_upper a [4,7,6,5,2,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,1,7] 30 (by decide +kernel))
  node1244)

def cert1246 : Leaf := ⟨⟨388,273,0,402,459,0,275,19,131⟩,[(2,5),(5,2)],[(6,2,4),(2,4,0),(3,5,4)],⟨19,134,76,41,52,104,451,387,275⟩,⟨19,134,76,41,52,104,192,384,272⟩,[⟨5,1292984623955073114864913,⟨467,134,206,463,471,206,192,449,467⟩⟩]⟩
theorem node1246 : UpperPrefix a [4,7,6,5,2,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,2,3] 30 cert1246 (by decide +kernel)

def cert1247 : Leaf := ⟨⟨300,312,305,272,328,24,314,56,40⟩,[],[(6,2,4),(2,4,0),(0,6,2),(1,7,6)],⟨19,134,76,41,52,352,193,386,280⟩,⟨19,134,76,41,52,352,193,386,272⟩,[⟨7,2337572565469084808905859,⟨283,319,380,317,308,380,381,283,272⟩⟩]⟩
theorem node1247 : UpperPrefix a [4,7,6,5,2,8,0,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,2,8,0,1] 30 cert1247 (by decide +kernel)

def cert1248 : Leaf := ⟨⟨420,312,433,400,448,144,304,48,162⟩,[],[(6,2,4),(2,4,0),(0,6,2),(3,7,1)],⟨19,134,76,41,52,352,193,392,274⟩,⟨19,134,76,41,52,352,193,392,272⟩,[⟨1,1210402861823907750477825,⟨17,180,92,253,180,508,253,508,272⟩⟩]⟩
theorem node1248 : UpperPrefix a [4,7,6,5,2,8,0,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,2,8,0,3] 30 cert1248 (by decide +kernel)

theorem node1249 : UpperPrefix a [4,7,6,5,2,8,0] 30 :=
  branch_upper a [4,7,6,5,2,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,5,2,8,0,0] 30 (by decide +kernel))
  node1247
  (invalid_upper a [4,7,6,5,2,8,0,2] 30 (by decide +kernel))
  node1248
  (invalid_upper a [4,7,6,5,2,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,0,8] 30 (by decide +kernel)))

def cert1250 : Local := ⟨⟨300,297,291,258,331,11,0,58,43⟩,[(6,1)],[(4,0,7),(7,1,6),(6,2,4),(2,4,0)]⟩
theorem node1250 : UpperPrefix a [4,7,6,5,2,8,1,0] 30 :=
  local_sound a [4,7,6,5,2,8,1,0] 30 cert1250 (by decide +kernel)

def cert1251 : Local := ⟨⟨292,313,307,274,323,19,0,51,35⟩,[(6,1)],[(7,1,6),(6,2,4),(2,4,0),(3,7,1)]⟩
theorem node1251 : UpperPrefix a [4,7,6,5,2,8,1,3] 30 :=
  local_sound a [4,7,6,5,2,8,1,3] 30 cert1251 (by decide +kernel)

theorem node1252 : UpperPrefix a [4,7,6,5,2,8,1] 30 :=
  branch_upper a [4,7,6,5,2,8,1] 30 (by decide) (fin9_cases _
  node1250
  (invalid_upper a [4,7,6,5,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,1,2] 30 (by decide +kernel))
  node1251
  (invalid_upper a [4,7,6,5,2,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,1,8] 30 (by decide +kernel)))

def cert1253 : Leaf := ⟨⟨388,273,0,402,451,147,275,19,131⟩,[(2,6)],[(6,2,4),(2,4,0),(3,6,2)],⟨19,134,76,41,52,352,200,387,275⟩,⟨19,134,76,41,52,352,200,384,272⟩,[⟨5,1293274925987053425458449,⟨403,198,206,463,471,455,206,385,403⟩⟩]⟩
theorem node1253 : UpperPrefix a [4,7,6,5,2,8,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,2,8,3] 30 cert1253 (by decide +kernel)

theorem node1254 : UpperPrefix a [4,7,6,5,2,8] 30 :=
  branch_upper a [4,7,6,5,2,8] 30 (by decide) (fin9_cases _
  node1249
  node1252
  (invalid_upper a [4,7,6,5,2,8,2] 30 (by decide +kernel))
  node1253
  (invalid_upper a [4,7,6,5,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,8,8] 30 (by decide +kernel)))

theorem node1255 : UpperPrefix a [4,7,6,5,2] 30 :=
  branch_upper a [4,7,6,5,2] 30 (by decide) (fin9_cases _
  node1241
  node1245
  (invalid_upper a [4,7,6,5,2,2] 30 (by decide +kernel))
  node1246
  (invalid_upper a [4,7,6,5,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,2,7] 30 (by decide +kernel))
  node1254)

def cert1256 : Leaf := ⟨⟨396,280,402,0,0,414,286,30,142⟩,[(3,5),(4,3)],[(5,3,4),(0,5,3),(0,5,4)],⟨19,134,76,41,56,97,454,390,278⟩,⟨19,134,76,41,56,97,192,384,272⟩,[⟨6,1229051218528799862819845,⟨147,391,415,57,56,57,128,384,272⟩⟩]⟩
theorem node1256 : UpperPrefix a [4,7,6,5,3,0] 30 :=
  Boolean.leaf_sound a [4,7,6,5,3,0] 30 cert1256 (by decide +kernel)

def cert1257 : Leaf := ⟨⟨12,25,17,22,0,157,285,29,13⟩,[(4,3)],[(7,1,5),(5,3,4),(1,5,3)],⟨19,134,76,41,56,98,453,389,277⟩,⟨19,134,76,41,56,98,192,384,272⟩,[⟨6,1229051218528802010303525,⟨155,391,415,57,57,187,128,384,280⟩⟩,⟨8,1181748069334818784359,⟨27,191,127,61,61,127,255,128,24⟩⟩]⟩
theorem node1257 : UpperPrefix a [4,7,6,5,3,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,3,1] 30 cert1257 (by decide +kernel)

def cert1258 : Leaf := ⟨⟨140,25,147,150,0,0,287,31,143⟩,[(4,3),(5,2)],[(6,2,5),(5,3,4)],⟨19,134,76,41,56,100,451,387,275⟩,⟨19,134,76,41,56,100,192,384,272⟩,[⟨8,1181748069334818784359,⟨27,191,127,61,61,127,255,128,24⟩⟩]⟩
theorem node1258 : UpperPrefix a [4,7,6,5,3,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,3,2] 30 cert1258 (by decide +kernel)

def cert1259 : Leaf := ⟨⟨332,344,273,340,0,28,286,92,76⟩,[(4,3)],[(5,3,4),(0,6,2),(1,7,6)],⟨19,134,76,41,56,352,193,386,276⟩,⟨19,134,76,41,56,352,193,386,272⟩,[⟨7,1803945152904814899758211,⟨283,319,380,317,316,380,381,283,272⟩⟩]⟩
theorem node1259 : UpperPrefix a [4,7,6,5,3,8,0,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,3,8,0,1] 30 cert1259 (by decide +kernel)

def cert1260 : Local := ⟨⟨456,0,403,466,0,154,282,90,202⟩,[(1,7),(4,3)],[(5,3,4),(0,6,2),(2,7,1)]⟩
theorem node1260 : UpperPrefix a [4,7,6,5,3,8,0,2] 30 :=
  local_sound a [4,7,6,5,3,8,0,2] 30 cert1260 (by decide +kernel)

theorem node1261 : UpperPrefix a [4,7,6,5,3,8,0] 30 :=
  branch_upper a [4,7,6,5,3,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,5,3,8,0,0] 30 (by decide +kernel))
  node1259
  node1260
  (invalid_upper a [4,7,6,5,3,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,0,8] 30 (by decide +kernel)))

def cert1262 : Leaf := ⟨⟨268,281,275,342,0,31,0,31,15⟩,[(4,3),(6,1)],[(7,1,6),(5,3,4)],⟨19,134,76,41,56,352,194,389,277⟩,⟨19,134,76,41,56,352,194,384,272⟩,[⟨6,1229051218526596544596997,⟨147,391,415,57,56,288,130,384,272⟩⟩]⟩
theorem node1262 : UpperPrefix a [4,7,6,5,3,8,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,3,8,1] 30 cert1262 (by decide +kernel)

def cert1263 : Leaf := ⟨⟨396,0,403,406,0,159,0,31,143⟩,[(1,6),(4,3),(6,1)],[(5,3,4)],⟨19,134,76,41,56,352,196,387,275⟩,⟨19,134,76,41,56,352,196,384,272⟩,[⟨6,1385783979551075215641637,⟨411,391,415,441,441,443,391,384,280⟩⟩]⟩
theorem node1263 : UpperPrefix a [4,7,6,5,3,8,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,3,8,2] 30 cert1263 (by decide +kernel)

theorem node1264 : UpperPrefix a [4,7,6,5,3,8] 30 :=
  branch_upper a [4,7,6,5,3,8] 30 (by decide) (fin9_cases _
  node1261
  node1262
  node1263
  (invalid_upper a [4,7,6,5,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,8,8] 30 (by decide +kernel)))

theorem node1265 : UpperPrefix a [4,7,6,5,3] 30 :=
  branch_upper a [4,7,6,5,3] 30 (by decide) (fin9_cases _
  node1256
  node1257
  node1258
  (invalid_upper a [4,7,6,5,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,3,7] 30 (by decide +kernel))
  node1264)

def cert1266 : Local := ⟨⟨364,376,304,0,76,286,0,124,108⟩,[(3,5),(6,1)],[(7,1,6),(0,5,3),(1,6,5)]⟩
theorem node1266 : UpperPrefix a [4,7,6,5,8,0,1] 30 :=
  local_sound a [4,7,6,5,8,0,1] 30 cert1266 (by decide +kernel)

def cert1267 : Leaf := ⟨⟨428,0,434,0,142,414,0,62,174⟩,[(1,6),(3,5),(6,1)],[(0,5,3)],⟨19,134,76,41,304,97,196,394,282⟩,⟨19,134,76,41,304,97,196,384,272⟩,[⟨6,1385175236996642800438309,⟨411,391,415,441,441,443,391,384,280⟩⟩]⟩
theorem node1267 : UpperPrefix a [4,7,6,5,8,0,2] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,0,2] 30 cert1267 (by decide +kernel)

def cert1268 : Leaf := ⟨⟨484,352,0,0,198,390,294,102,230⟩,[(2,6),(3,5)],[(0,5,3),(3,6,2)],⟨19,134,76,41,304,97,200,390,278⟩,⟨19,134,76,41,304,97,200,384,272⟩,[⟨4,1212616629038215144580609,⟨239,134,110,111,494,111,238,386,454⟩⟩]⟩
theorem node1268 : UpperPrefix a [4,7,6,5,8,0,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,0,3] 30 cert1268 (by decide +kernel)

theorem node1269 : UpperPrefix a [4,7,6,5,8,0] 30 :=
  branch_upper a [4,7,6,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,5,8,0,0] 30 (by decide +kernel))
  node1266
  node1267
  node1268
  (invalid_upper a [4,7,6,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,0,8] 30 (by decide +kernel)))

def cert1270 : Local := ⟨⟨360,0,305,338,72,408,312,120,104⟩,[(1,7)],[(7,1,5),(1,5,3),(0,6,2),(2,7,1)]⟩
theorem node1270 : UpperPrefix a [4,7,6,5,8,1,0,2] 30 :=
  local_sound a [4,7,6,5,8,1,0,2] 30 cert1270 (by decide +kernel)

def cert1271 : Leaf := ⟨⟨356,104,33,70,68,132,308,116,100⟩,[],[(7,1,5),(1,5,3),(0,6,2),(3,7,1)],⟨19,134,76,41,304,98,193,392,276⟩,⟨19,134,76,41,304,98,193,392,272⟩,[⟨4,1210107567675298091664385,⟨3,166,110,45,292,110,239,392,256⟩⟩,⟨8,1181748061768428585985,⟨19,166,110,45,52,110,239,136,16⟩⟩]⟩
theorem node1271 : UpperPrefix a [4,7,6,5,8,1,0,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,1,0,3] 30 cert1271 (by decide +kernel)

theorem node1272 : UpperPrefix a [4,7,6,5,8,1,0] 30 :=
  branch_upper a [4,7,6,5,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,7,6,5,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,0,1] 30 (by decide +kernel))
  node1270
  node1271
  (invalid_upper a [4,7,6,5,8,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,0,8] 30 (by decide +kernel)))

def cert1273 : Local := ⟨⟨360,0,305,338,73,413,0,121,105⟩,[(1,6),(6,1)],[(7,1,5),(1,5,3),(2,6,5)]⟩
theorem node1273 : UpperPrefix a [4,7,6,5,8,1,2] 30 :=
  local_sound a [4,7,6,5,8,1,2] 30 cert1273 (by decide +kernel)

def cert1274 : Leaf := ⟨⟨356,96,0,342,69,132,309,117,101⟩,[(2,6)],[(7,1,5),(1,5,3),(3,6,2)],⟨19,134,76,41,304,98,200,389,277⟩,⟨19,134,76,41,304,98,200,384,272⟩,[⟨0,1210107567676389004968960,⟨18,166,110,40,304,102,238,384,272⟩⟩,⟨4,1210107567675289493341185,⟨3,166,110,41,288,102,238,384,256⟩⟩,⟨8,1181748061759830262785,⟨19,166,110,41,48,102,238,128,16⟩⟩]⟩
theorem node1274 : UpperPrefix a [4,7,6,5,8,1,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,1,3] 30 cert1274 (by decide +kernel)

theorem node1275 : UpperPrefix a [4,7,6,5,8,1] 30 :=
  branch_upper a [4,7,6,5,8,1] 30 (by decide) (fin9_cases _
  node1272
  (invalid_upper a [4,7,6,5,8,1,1] 30 (by decide +kernel))
  node1273
  node1274
  (invalid_upper a [4,7,6,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,1,8] 30 (by decide +kernel)))

def cert1276 : Leaf := ⟨⟨300,40,35,6,14,0,318,62,46⟩,[(5,2)],[(6,2,5),(0,6,2)],⟨19,134,76,41,304,100,193,394,282⟩,⟨19,134,76,41,304,100,193,384,272⟩,[⟨7,1223094075509374637310979,⟨283,319,124,317,308,124,381,256,272⟩⟩,⟨4,1210107567675298091664385,⟨3,166,110,45,292,110,239,384,256⟩⟩,⟨8,1181748061768428585985,⟨19,166,110,45,52,110,239,128,16⟩⟩]⟩
theorem node1276 : UpperPrefix a [4,7,6,5,8,2,0] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,2,0] 30 cert1276 (by decide +kernel)

def cert1277 : Leaf := ⟨⟨300,313,307,278,13,0,0,61,45⟩,[(5,2),(6,1)],[(7,1,6),(6,2,5)],⟨19,134,76,41,304,100,194,393,281⟩,⟨19,134,76,41,304,100,194,384,272⟩,[⟨1,1247960284264665808109569,⟨17,180,508,441,304,116,192,384,272⟩⟩]⟩
theorem node1277 : UpperPrefix a [4,7,6,5,8,2,1] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,2,1] 30 cert1277 (by decide +kernel)

def cert1278 : Leaf := ⟨⟨420,305,0,406,131,0,307,51,163⟩,[(2,6),(5,2)],[(6,2,5),(3,6,2),(3,6,5)],⟨19,134,76,41,304,100,200,387,275⟩,⟨19,134,76,41,304,100,200,384,272⟩,[⟨2,1214839299254496016729089,⟨403,130,88,505,304,96,216,384,272⟩⟩]⟩
theorem node1278 : UpperPrefix a [4,7,6,5,8,2,3] 30 :=
  Boolean.leaf_sound a [4,7,6,5,8,2,3] 30 cert1278 (by decide +kernel)

theorem node1279 : UpperPrefix a [4,7,6,5,8,2] 30 :=
  branch_upper a [4,7,6,5,8,2] 30 (by decide) (fin9_cases _
  node1276
  node1277
  (invalid_upper a [4,7,6,5,8,2,2] 30 (by decide +kernel))
  node1278
  (invalid_upper a [4,7,6,5,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,7,6,5,8,2,8] 30 (by decide +kernel)))

#print axioms node1279
end Delivery.FiniteExclusion.Sharp4x5
