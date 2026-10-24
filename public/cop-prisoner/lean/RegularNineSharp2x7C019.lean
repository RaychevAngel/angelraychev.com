import RegularNineSharp2x7Base
import RegularNineSharp2x7C018
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert1216 : Leaf := ⟨⟨0,92,113,356,76,12,0,125,121⟩,[(0,2),(6,3)],[(1,2,0),(7,3,6),(8,4,3)],⟨7,35,14,152,304,112,200,449,325⟩,⟨7,35,14,152,304,112,200,384,260⟩,[⟨0,1210110022287745256260608,⟨6,34,110,248,304,120,248,504,260⟩⟩]⟩
theorem node1216 : UpperPrefix a [2,5,1,7,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,1,7,8,4,3] 30 cert1216 (by decide +kernel)

theorem node1217 : UpperPrefix a [2,5,1,7,8,4] 30 :=
  branch_upper a [2,5,1,7,8,4] 30 (by decide) (fin9_cases _
  node1215
  (invalid_upper a [2,5,1,7,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,2] 30 (by decide +kernel))
  node1216
  (invalid_upper a [2,5,1,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,4,8] 30 (by decide +kernel)))

theorem node1218 : UpperPrefix a [2,5,1,7,8] 30 :=
  branch_upper a [2,5,1,7,8] 30 (by decide) (fin9_cases _
  node1213
  (invalid_upper a [2,5,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,2] 30 (by decide +kernel))
  node1214
  node1217
  (invalid_upper a [2,5,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,8,8] 30 (by decide +kernel)))

theorem node1219 : UpperPrefix a [2,5,1,7] 30 :=
  branch_upper a [2,5,1,7] 30 (by decide) (fin9_cases _
  node1198
  (invalid_upper a [2,5,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,2] 30 (by decide +kernel))
  node1204
  (invalid_upper a [2,5,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,7,5] 30 (by decide +kernel))
  node1212
  (invalid_upper a [2,5,1,7,7] 30 (by decide +kernel))
  node1218)

def cert1220 : Leaf := ⟨⟨0,0,497,229,0,408,312,120,249⟩,[(0,2),(1,4),(4,1)],[(1,2,0)],⟨7,35,14,280,49,248,216,472,476⟩,⟨7,35,14,280,49,96,192,384,260⟩,[⟨0,1210181496656809576891392,⟨6,34,238,504,48,96,192,384,260⟩⟩,⟨2,1210181568855347260564993,⟨115,51,250,506,51,96,192,384,352⟩⟩]⟩
theorem node1220 : UpperPrefix a [2,5,1,8,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,0] 30 cert1220 (by decide +kernel)

def cert1221 : Leaf := ⟨⟨0,0,496,228,452,404,308,116,248⟩,[(0,2),(1,5)],[(1,2,0),(0,5,1)],⟨7,35,14,280,56,97,208,464,468⟩,⟨7,35,14,280,56,97,192,384,260⟩,[⟨3,1210181785027922143371013,⟨39,35,231,499,242,99,192,387,295⟩⟩]⟩
theorem node1221 : UpperPrefix a [2,5,1,8,3,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,3,0] 30 cert1221 (by decide +kernel)

def cert1222 : Leaf := ⟨⟨0,388,417,229,453,389,261,69,193⟩,[(0,2)],[(1,2,0),(4,5,4)],⟨7,35,14,280,56,112,193,449,453⟩,⟨7,35,14,280,56,112,192,384,260⟩,[⟨3,1236226120109616696139013,⟨455,483,487,499,242,112,192,449,455⟩⟩,⟨5,1236149881204800805143557,⟨455,451,463,472,24,80,192,448,453⟩⟩,⟨6,1210106412362347085587517,⟨7,35,15,287,63,55,128,384,261⟩⟩]⟩
theorem node1222 : UpperPrefix a [2,5,1,8,3,4] 30 :=
  Boolean.leaf_sound a [2,5,1,8,3,4] 30 cert1222 (by decide +kernel)

def cert1223 : Leaf := ⟨⟨0,324,353,101,325,0,309,117,121⟩,[(0,2),(5,6)],[(1,2,0),(7,5,5)],⟨7,35,14,280,56,224,209,465,341⟩,⟨7,35,14,280,56,224,192,384,260⟩,[⟨3,1210181499612295758749445,⟨39,35,231,499,242,224,224,387,295⟩⟩,⟨4,1210107567534551994475549,⟨7,35,15,271,47,224,224,384,261⟩⟩]⟩
theorem node1223 : UpperPrefix a [2,5,1,8,3,7] 30 :=
  Boolean.leaf_sound a [2,5,1,8,3,7] 30 cert1223 (by decide +kernel)

theorem node1224 : UpperPrefix a [2,5,1,8,3] 30 :=
  branch_upper a [2,5,1,8,3] 30 (by decide) (fin9_cases _
  node1221
  (invalid_upper a [2,5,1,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,3,3] 30 (by decide +kernel))
  node1222
  (invalid_upper a [2,5,1,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,3,6] 30 (by decide +kernel))
  node1223
  (invalid_upper a [2,5,1,8,3,8] 30 (by decide +kernel)))

def cert1225 : Local := ⟨⟨0,0,432,164,0,412,316,60,184⟩,[(0,2),(1,5),(4,5)],[(1,2,0),(6,4,4),(0,5,1)]⟩
theorem node1225 : UpperPrefix a [2,5,1,8,6,0] 30 :=
  local_sound a [2,5,1,8,6,0] 30 cert1225 (by decide +kernel)

def cert1226 : Leaf := ⟨⟨0,396,417,165,0,405,309,53,177⟩,[(0,2),(4,5)],[(1,2,0),(6,4,4)],⟨7,35,14,280,112,104,209,401,405⟩,⟨7,35,14,280,112,104,192,384,260⟩,[⟨3,1233784087405582850458629,⟨471,499,471,272,112,112,192,384,453⟩⟩,⟨4,1210107565282752185001023,⟨7,39,15,271,103,111,192,384,261⟩⟩]⟩
theorem node1226 : UpperPrefix a [2,5,1,8,6,3] 30 :=
  Boolean.leaf_sound a [2,5,1,8,6,3] 30 cert1226 (by decide +kernel)

def cert1227 : Local := ⟨⟨0,412,433,165,0,0,317,61,185⟩,[(0,2),(4,5),(5,4)],[(1,2,0),(6,4,4),(6,4,5)]⟩
theorem node1227 : UpperPrefix a [2,5,1,8,6,4] 30 :=
  local_sound a [2,5,1,8,6,4] 30 cert1227 (by decide +kernel)

def cert1228 : Local := ⟨⟨0,284,305,37,0,0,317,61,57⟩,[(0,2),(4,5),(5,6)],[(1,2,0),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node1228 : UpperPrefix a [2,5,1,8,6,7] 30 :=
  local_sound a [2,5,1,8,6,7] 30 cert1228 (by decide +kernel)

theorem node1229 : UpperPrefix a [2,5,1,8,6] 30 :=
  branch_upper a [2,5,1,8,6] 30 (by decide) (fin9_cases _
  node1225
  (invalid_upper a [2,5,1,8,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,6,2] 30 (by decide +kernel))
  node1226
  node1227
  (invalid_upper a [2,5,1,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,6,6] 30 (by decide +kernel))
  node1228
  (invalid_upper a [2,5,1,8,6,8] 30 (by decide +kernel)))

def cert1230 : Leaf := ⟨⟨0,0,496,228,332,412,280,88,248⟩,[(0,2),(1,5)],[(1,2,0),(0,5,1)],⟨7,35,14,280,176,97,216,472,348⟩,⟨7,35,14,280,176,97,192,384,260⟩,[⟨2,1210181496375334599148545,⟨3,35,202,472,178,99,192,384,256⟩⟩,⟨5,1210181495249434693338117,⟨7,3,207,472,144,65,192,384,261⟩⟩]⟩
theorem node1230 : UpperPrefix a [2,5,1,8,7,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,0] 30 cert1230 (by decide +kernel)

def cert1231 : Leaf := ⟨⟨0,140,161,229,325,133,36,117,241⟩,[(0,2)],[(1,2,0)],⟨7,35,14,280,176,104,193,464,340⟩,⟨7,35,14,280,176,104,193,384,260⟩,[⟨3,1233862486067896116052997,⟨471,499,471,464,176,240,449,448,453⟩⟩,⟨4,1210110159637612527123775,⟨7,39,47,367,231,111,193,449,263⟩⟩,⟨8,1184340024082864045375,⟨7,39,47,127,247,111,193,193,7⟩⟩,⟨6,1210106412362347089781823,⟨7,39,15,287,183,47,129,384,261⟩⟩]⟩
theorem node1231 : UpperPrefix a [2,5,1,8,7,3,0] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,3,0] 30 cert1231 (by decide +kernel)

def cert1232 : Local := ⟨⟨0,332,353,101,333,277,0,109,105⟩,[(0,2),(6,4)],[(1,2,0),(7,4,6),(4,6,5)]⟩
theorem node1232 : UpperPrefix a [2,5,1,8,7,3,4] 30 :=
  local_sound a [2,5,1,8,7,3,4] 30 cert1232 (by decide +kernel)

theorem node1233 : UpperPrefix a [2,5,1,8,7,3] 30 :=
  branch_upper a [2,5,1,8,7,3] 30 (by decide) (fin9_cases _
  node1231
  (invalid_upper a [2,5,1,8,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,3,3] 30 (by decide +kernel))
  node1232
  (invalid_upper a [2,5,1,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,3,8] 30 (by decide +kernel)))

def cert1234 : Leaf := ⟨⟨0,348,369,101,320,384,269,77,73⟩,[(0,2)],[(1,2,0),(7,4,5)],⟨7,35,14,280,176,112,201,457,333⟩,⟨7,35,14,280,176,112,192,384,260⟩,[⟨4,1229033996759972212376581,⟨455,35,463,264,160,96,192,384,453⟩⟩,⟨5,1229033995635171817161733,⟨455,3,463,280,144,80,192,384,453⟩⟩,⟨0,1210107567540049546314752,⟨6,34,14,280,176,112,240,384,260⟩⟩,⟨2,1210107567540049545266177,⟨3,35,10,280,176,112,240,384,256⟩⟩,⟨3,1210107567540048472572933,⟨7,35,7,272,176,112,240,384,261⟩⟩]⟩
theorem node1234 : UpperPrefix a [2,5,1,8,7,4] 30 :=
  Boolean.leaf_sound a [2,5,1,8,7,4] 30 cert1234 (by decide +kernel)

theorem node1235 : UpperPrefix a [2,5,1,8,7] 30 :=
  branch_upper a [2,5,1,8,7] 30 (by decide) (fin9_cases _
  node1230
  (invalid_upper a [2,5,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,2] 30 (by decide +kernel))
  node1233
  node1234
  (invalid_upper a [2,5,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,7,8] 30 (by decide +kernel)))

theorem node1236 : UpperPrefix a [2,5,1,8] 30 :=
  branch_upper a [2,5,1,8] 30 (by decide) (fin9_cases _
  node1220
  (invalid_upper a [2,5,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,2] 30 (by decide +kernel))
  node1224
  (invalid_upper a [2,5,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,8,5] 30 (by decide +kernel))
  node1229
  node1235
  (invalid_upper a [2,5,1,8,8] 30 (by decide +kernel)))

theorem node1237 : UpperPrefix a [2,5,1] 30 :=
  branch_upper a [2,5,1] 30 (by decide) (fin9_cases _
  node1175
  (invalid_upper a [2,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,1,5] 30 (by decide +kernel))
  node1194
  node1219
  node1236)

def cert1238 : Leaf := ⟨⟨456,460,0,454,0,396,268,76,200⟩,[(2,3),(4,1)],[(5,1,4),(4,2,2),(1,4,3)],⟨7,35,28,25,50,488,456,456,460⟩,⟨7,35,28,25,50,96,192,384,260⟩,[⟨0,1266886860137930425369600,⟨502,50,508,508,50,96,192,384,484⟩⟩]⟩
theorem node1238 : UpperPrefix a [2,5,4,0,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,1] 30 cert1238 (by decide +kernel)

def cert1239 : Leaf := ⟨⟨288,260,0,294,262,390,294,102,226⟩,[(2,3)],[(4,2,2),(3,4,2)],⟨7,35,28,25,56,482,450,450,454⟩,⟨7,35,28,25,56,96,192,384,260⟩,[⟨0,1214857656032130302477312,⟨486,482,28,508,60,96,192,384,260⟩⟩,⟨6,1210106412364690938946623,⟨31,63,31,31,63,63,128,384,269⟩⟩,⟨7,1208926973665478134490175,⟨31,63,31,31,63,127,64,256,269⟩⟩]⟩
theorem node1239 : UpperPrefix a [2,5,4,0,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,3] 30 cert1239 (by decide +kernel)

def cert1240 : Leaf := ⟨⟨40,12,0,38,0,399,303,47,171⟩,[(2,3),(4,5)],[(4,2,2),(6,4,4)],⟨7,35,28,25,112,490,458,394,398⟩,⟨7,35,28,25,112,96,192,384,260⟩,[⟨7,1208926973665340561056831,⟨15,63,31,31,127,127,64,256,269⟩⟩,⟨8,1181745671428797654079,⟨15,63,31,31,127,127,192,128,13⟩⟩]⟩
theorem node1240 : UpperPrefix a [2,5,4,0,6] 30 :=
  Boolean.leaf_sound a [2,5,4,0,6] 30 cert1240 (by decide +kernel)

def cert1241 : Leaf := ⟨⟨232,204,0,228,76,140,300,108,232⟩,[(2,3)],[(4,2,2),(1,5,1)],⟨7,35,28,25,176,98,456,456,332⟩,⟨7,35,28,25,176,98,192,384,260⟩,[⟨0,1266886859751314649252864,⟨502,50,476,508,176,98,192,384,452⟩⟩,⟨8,1181747925435972379775,⟨15,47,31,31,191,127,255,128,13⟩⟩]⟩
theorem node1241 : UpperPrefix a [2,5,4,0,7,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,1] 30 cert1241 (by decide +kernel)

def cert1242 : Leaf := ⟨⟨104,76,0,102,70,134,294,102,98⟩,[(2,3)],[(4,2,2)],⟨7,35,28,25,176,104,450,450,326⟩,⟨7,35,28,25,176,104,192,384,260⟩,[⟨0,1224302389173928896496640,⟨470,502,60,508,180,124,192,384,260⟩⟩,⟨8,1181747925435972379775,⟨15,47,31,31,191,127,255,128,13⟩⟩,⟨3,1214857655926163789317121,⟨471,499,20,465,176,96,192,384,260⟩⟩,⟨7,1360042701114965612323901,⟨15,291,31,31,319,367,64,256,269⟩⟩]⟩
theorem node1242 : UpperPrefix a [2,5,4,0,7,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,3] 30 cert1242 (by decide +kernel)

def cert1243 : Leaf := ⟨⟨40,12,0,36,333,141,45,109,233⟩,[(2,3)],[(4,2,2),(8,5,4)],⟨7,35,28,25,176,352,194,456,332⟩,⟨7,35,28,25,176,352,194,384,260⟩,[⟨1,1512929318256264856731649,⟨13,61,28,29,176,500,508,384,260⟩⟩,⟨6,1210106412362349769925661,⟨15,35,31,31,191,288,130,384,269⟩⟩,⟨7,1208926973663136965469213,⟨15,35,31,31,63,352,66,256,269⟩⟩]⟩
theorem node1243 : UpperPrefix a [2,5,4,0,7,8,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,8,1] 30 cert1243 (by decide +kernel)

def cert1244 : Leaf := ⟨⟨168,140,0,166,270,142,38,44,234⟩,[(2,3)],[(4,2,2),(8,5,4)],⟨7,35,28,25,176,352,200,386,324⟩,⟨7,35,28,25,176,352,200,386,260⟩,[⟨0,1720150962344238267761664,⟨438,434,380,508,432,372,508,402,292⟩⟩,⟨6,1210401560269887505196223,⟨31,191,31,31,191,447,141,415,269⟩⟩]⟩
theorem node1244 : UpperPrefix a [2,5,4,0,7,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,7,8,3,1] 30 cert1244 (by decide +kernel)

def cert1245 : Local := ⟨⟨168,140,0,166,335,0,39,0,171⟩,[(2,3),(5,7),(7,5)],[(4,2,2),(8,5,4),(6,7,4)]⟩
theorem node1245 : UpperPrefix a [2,5,4,0,7,8,3,6] 30 :=
  local_sound a [2,5,4,0,7,8,3,6] 30 cert1245 (by decide +kernel)

theorem node1246 : UpperPrefix a [2,5,4,0,7,8,3] 30 :=
  branch_upper a [2,5,4,0,7,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,7,8,3,0] 30 (by decide +kernel))
  node1244
  (invalid_upper a [2,5,4,0,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,3,5] 30 (by decide +kernel))
  node1245
  (invalid_upper a [2,5,4,0,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,3,8] 30 (by decide +kernel)))

theorem node1247 : UpperPrefix a [2,5,4,0,7,8] 30 :=
  branch_upper a [2,5,4,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,7,8,0] 30 (by decide +kernel))
  node1243
  (invalid_upper a [2,5,4,0,7,8,2] 30 (by decide +kernel))
  node1246
  (invalid_upper a [2,5,4,0,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,8,8] 30 (by decide +kernel)))

theorem node1248 : UpperPrefix a [2,5,4,0,7] 30 :=
  branch_upper a [2,5,4,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,7,0] 30 (by decide +kernel))
  node1241
  (invalid_upper a [2,5,4,0,7,2] 30 (by decide +kernel))
  node1242
  (invalid_upper a [2,5,4,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,7,7] 30 (by decide +kernel))
  node1247)

def cert1249 : Leaf := ⟨⟨424,396,0,420,204,396,268,76,200⟩,[(2,3)],[(4,2,2),(1,5,1)],⟨7,35,28,25,304,98,200,456,460⟩,⟨7,35,28,25,304,98,192,384,260⟩,[⟨0,1266886859751314649252864,⟨502,50,476,508,304,98,192,384,452⟩⟩,⟨5,1266886858589611895030785,⟨455,3,476,477,272,66,192,384,452⟩⟩,⟨6,1210106412362349769925661,⟨15,35,31,31,319,34,128,384,269⟩⟩]⟩
theorem node1249 : UpperPrefix a [2,5,4,0,8,1] 30 :=
  Boolean.leaf_sound a [2,5,4,0,8,1] 30 cert1249 (by decide +kernel)

def cert1250 : Leaf := ⟨⟨424,396,0,422,198,390,262,70,194⟩,[(2,3)],[(4,2,2)],⟨7,35,28,25,304,104,194,450,454⟩,⟨7,35,28,25,304,104,192,384,260⟩,[⟨0,1224302389173928896496640,⟨470,502,60,508,308,124,192,384,260⟩⟩,⟨3,1214857655926163789317121,⟨471,499,20,465,304,96,192,384,260⟩⟩,⟨5,1214857654800127519360001,⟨455,451,28,477,272,76,192,384,260⟩⟩,⟨6,1210106412362349769942077,⟨15,35,31,31,319,47,128,384,269⟩⟩]⟩
theorem node1250 : UpperPrefix a [2,5,4,0,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,0,8,3] 30 cert1250 (by decide +kernel)

def cert1251 : Leaf := ⟨⟨40,12,0,38,79,0,303,111,107⟩,[(2,3),(5,6)],[(4,2,2),(7,5,5)],⟨7,35,28,25,304,224,202,458,334⟩,⟨7,35,28,25,304,224,192,384,260⟩,[⟨6,1210106412362349769925661,⟨15,35,31,31,319,160,128,384,269⟩⟩,⟨8,1181747921025015751709,⟨15,35,31,31,63,224,224,128,13⟩⟩]⟩
theorem node1251 : UpperPrefix a [2,5,4,0,8,7] 30 :=
  Boolean.leaf_sound a [2,5,4,0,8,7] 30 cert1251 (by decide +kernel)

theorem node1252 : UpperPrefix a [2,5,4,0,8] 30 :=
  branch_upper a [2,5,4,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,8,0] 30 (by decide +kernel))
  node1249
  (invalid_upper a [2,5,4,0,8,2] 30 (by decide +kernel))
  node1250
  (invalid_upper a [2,5,4,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,8,6] 30 (by decide +kernel))
  node1251
  (invalid_upper a [2,5,4,0,8,8] 30 (by decide +kernel)))

theorem node1253 : UpperPrefix a [2,5,4,0] 30 :=
  branch_upper a [2,5,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,0,0] 30 (by decide +kernel))
  node1238
  (invalid_upper a [2,5,4,0,2] 30 (by decide +kernel))
  node1239
  (invalid_upper a [2,5,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,0,5] 30 (by decide +kernel))
  node1240
  node1248
  node1252)

def cert1254 : Local := ⟨⟨456,0,0,485,0,398,270,78,202⟩,[(1,4),(2,3),(4,1)],[(5,1,3),(4,2,2),(0,4,3)]⟩
theorem node1254 : UpperPrefix a [2,5,4,1,0] 30 :=
  local_sound a [2,5,4,1,0] 30 cert1254 (by decide +kernel)

def cert1255 : Leaf := ⟨⟨384,388,0,421,389,389,261,69,193⟩,[(2,3)],[(5,1,3),(4,2,2),(3,4,2)],⟨7,35,28,26,56,481,449,449,453⟩,⟨7,35,28,26,56,96,192,384,260⟩,[⟨1,1214857656032130302476289,⟨485,481,28,252,60,96,192,384,260⟩⟩,⟨6,1210106412364690938946623,⟨31,63,31,31,63,63,128,384,269⟩⟩]⟩
theorem node1255 : UpperPrefix a [2,5,4,1,3] 30 :=
  Boolean.leaf_sound a [2,5,4,1,3] 30 cert1255 (by decide +kernel)

def cert1256 : Leaf := ⟨⟨264,268,0,293,0,399,271,15,139⟩,[(2,3),(4,5)],[(5,1,3),(4,2,2),(6,4,4)],⟨7,35,28,26,112,489,457,393,397⟩,⟨7,35,28,26,112,96,192,384,260⟩,[⟨7,1208926973665340561056831,⟨15,63,31,31,127,127,64,256,269⟩⟩]⟩
theorem node1256 : UpperPrefix a [2,5,4,1,6] 30 :=
  Boolean.leaf_sound a [2,5,4,1,6] 30 cert1256 (by decide +kernel)

def cert1257 : Leaf := ⟨⟨456,0,0,484,332,396,268,76,200⟩,[(1,5),(2,3)],[(5,1,3),(4,2,2),(0,5,1)],⟨7,35,28,26,176,97,456,456,332⟩,⟨7,35,28,26,176,97,192,384,260⟩,[⟨1,1266886859750764893437953,⟨501,49,476,476,176,113,192,384,452⟩⟩]⟩
theorem node1257 : UpperPrefix a [2,5,4,1,7,0] 30 :=
  Boolean.leaf_sound a [2,5,4,1,7,0] 30 cert1257 (by decide +kernel)

def cert1258 : Leaf := ⟨⟨200,204,0,229,69,133,261,69,193⟩,[(2,3)],[(5,1,3),(4,2,2)],⟨7,35,28,26,176,104,449,449,325⟩,⟨7,35,28,26,176,104,192,384,260⟩,[⟨1,1224302389173928896495617,⟨469,501,60,508,180,124,192,384,260⟩⟩,⟨8,1181747925435972379775,⟨15,47,31,31,191,127,255,128,13⟩⟩,⟨3,1214857655926163789317121,⟨471,499,20,210,176,96,192,384,260⟩⟩]⟩
theorem node1258 : UpperPrefix a [2,5,4,1,7,3] 30 :=
  Boolean.leaf_sound a [2,5,4,1,7,3] 30 cert1258 (by decide +kernel)

def cert1259 : Leaf := ⟨⟨8,12,0,37,335,143,14,79,203⟩,[(2,3)],[(5,1,3),(4,2,2),(8,5,4)],⟨7,35,28,26,176,352,193,456,332⟩,⟨7,35,28,26,176,352,193,384,260⟩,[⟨6,1210106412362349769925661,⟨15,35,31,31,191,288,129,384,269⟩⟩,⟨7,1208926973663136965469213,⟨15,35,31,31,63,352,65,256,269⟩⟩]⟩
theorem node1259 : UpperPrefix a [2,5,4,1,7,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,1,7,8,0] 30 cert1259 (by decide +kernel)

def cert1260 : Leaf := ⟨⟨8,12,0,37,335,15,7,79,75⟩,[(2,3)],[(5,1,3),(4,2,2),(8,5,4)],⟨7,35,28,26,176,352,200,449,325⟩,⟨7,35,28,26,176,352,200,384,260⟩,[⟨7,1511158430818594072880221,⟨15,35,31,31,63,355,367,256,269⟩⟩,⟨6,1210106412362349769925661,⟨15,35,31,31,191,288,141,384,269⟩⟩]⟩
theorem node1260 : UpperPrefix a [2,5,4,1,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,1,7,8,3] 30 cert1260 (by decide +kernel)

theorem node1261 : UpperPrefix a [2,5,4,1,7,8] 30 :=
  branch_upper a [2,5,4,1,7,8] 30 (by decide) (fin9_cases _
  node1259
  (invalid_upper a [2,5,4,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,8,2] 30 (by decide +kernel))
  node1260
  (invalid_upper a [2,5,4,1,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,8,8] 30 (by decide +kernel)))

theorem node1262 : UpperPrefix a [2,5,4,1,7] 30 :=
  branch_upper a [2,5,4,1,7] 30 (by decide) (fin9_cases _
  node1257
  (invalid_upper a [2,5,4,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,2] 30 (by decide +kernel))
  node1258
  (invalid_upper a [2,5,4,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,7,7] 30 (by decide +kernel))
  node1261)

def cert1263 : Leaf := ⟨⟨456,0,0,484,204,396,268,76,200⟩,[(1,5),(2,3)],[(5,1,3),(4,2,2),(0,5,1)],⟨7,35,28,26,304,97,200,456,460⟩,⟨7,35,28,26,304,97,192,384,260⟩,[⟨1,1266886859750764893437953,⟨501,49,476,476,304,113,192,384,452⟩⟩]⟩
theorem node1263 : UpperPrefix a [2,5,4,1,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,1,8,0] 30 cert1263 (by decide +kernel)

def cert1264 : Leaf := ⟨⟨392,396,0,421,197,389,261,69,193⟩,[(2,3)],[(5,1,3),(4,2,2)],⟨7,35,28,26,304,104,193,449,453⟩,⟨7,35,28,26,304,104,192,384,260⟩,[⟨1,1224302389173928896495617,⟨469,501,60,508,308,124,192,384,260⟩⟩,⟨3,1214857655926163789317121,⟨471,499,20,210,304,96,192,384,260⟩⟩,⟨6,1210106412362349769942077,⟨15,35,31,31,319,47,128,384,269⟩⟩]⟩
theorem node1264 : UpperPrefix a [2,5,4,1,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,1,8,3] 30 cert1264 (by decide +kernel)

def cert1265 : Leaf := ⟨⟨264,268,0,293,79,0,271,79,75⟩,[(2,3),(5,6)],[(5,1,3),(4,2,2),(7,5,5)],⟨7,35,28,26,304,224,201,457,333⟩,⟨7,35,28,26,304,224,192,384,260⟩,[⟨6,1210106412362349769925661,⟨15,35,31,31,319,160,128,384,269⟩⟩]⟩
theorem node1265 : UpperPrefix a [2,5,4,1,8,7] 30 :=
  Boolean.leaf_sound a [2,5,4,1,8,7] 30 cert1265 (by decide +kernel)

theorem node1266 : UpperPrefix a [2,5,4,1,8] 30 :=
  branch_upper a [2,5,4,1,8] 30 (by decide) (fin9_cases _
  node1263
  (invalid_upper a [2,5,4,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,8,2] 30 (by decide +kernel))
  node1264
  (invalid_upper a [2,5,4,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,8,6] 30 (by decide +kernel))
  node1265
  (invalid_upper a [2,5,4,1,8,8] 30 (by decide +kernel)))

theorem node1267 : UpperPrefix a [2,5,4,1] 30 :=
  branch_upper a [2,5,4,1] 30 (by decide) (fin9_cases _
  node1254
  (invalid_upper a [2,5,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,2] 30 (by decide +kernel))
  node1255
  (invalid_upper a [2,5,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,1,5] 30 (by decide +kernel))
  node1256
  node1262
  node1266)

def cert1268 : Leaf := ⟨⟨296,0,0,295,0,399,303,47,171⟩,[(1,4),(2,3),(4,1)],[(4,2,2)],⟨7,35,28,88,49,490,458,394,398⟩,⟨7,35,28,88,49,96,192,384,260⟩,[⟨6,1266885490621362520204301,⟨407,51,415,415,51,32,128,384,389⟩⟩,⟨7,1208926973665475047220287,⟨23,63,31,95,63,127,64,256,261⟩⟩]⟩
theorem node1268 : UpperPrefix a [2,5,4,6,0] 30 :=
  Boolean.leaf_sound a [2,5,4,6,0] 30 cert1268 (by decide +kernel)

def cert1269 : Leaf := ⟨⟨72,76,0,7,0,399,271,79,203⟩,[(2,3),(4,1)],[(5,1,4),(4,2,2)],⟨7,35,28,88,50,489,457,393,397⟩,⟨7,35,28,88,50,96,192,384,260⟩,[⟨7,1208926973665475047220287,⟨23,63,31,95,63,127,64,256,261⟩⟩,⟨8,1181745671563283817535,⟨23,63,31,95,63,127,192,128,5⟩⟩]⟩
theorem node1269 : UpperPrefix a [2,5,4,6,1] 30 :=
  Boolean.leaf_sound a [2,5,4,6,1] 30 cert1269 (by decide +kernel)

def cert1270 : Leaf := ⟨⟨32,4,0,39,71,391,295,39,163⟩,[(2,3)],[(4,2,2),(6,3,4),(3,4,2)],⟨7,35,28,88,56,483,451,387,391⟩,⟨7,35,28,88,56,96,192,384,260⟩,[⟨7,1208926973665475047220287,⟨23,63,31,95,63,127,64,256,261⟩⟩,⟨8,1181745671563283817535,⟨23,63,31,95,63,127,192,128,5⟩⟩]⟩
theorem node1270 : UpperPrefix a [2,5,4,6,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,3] 30 cert1270 (by decide +kernel)

def cert1271 : Leaf := ⟨⟨104,0,0,166,78,14,302,110,106⟩,[(1,5),(2,3)],[(4,2,2),(7,4,3),(0,5,1)],⟨7,35,28,88,176,97,458,394,270⟩,⟨7,35,28,88,176,97,192,384,260⟩,[⟨8,1181748206908264742271,⟨7,47,63,127,191,127,255,129,7⟩⟩]⟩
theorem node1271 : UpperPrefix a [2,5,4,6,7,0] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,0] 30 cert1271 (by decide +kernel)

def cert1272 : Leaf := ⟨⟨104,76,0,164,76,13,44,108,104⟩,[(2,3)],[(4,2,2),(7,4,3),(1,5,1),(0,6,5)],⟨7,35,28,88,176,98,193,392,268⟩,⟨7,35,28,88,176,98,193,384,260⟩,[⟨8,1184347496396690292735,⟨47,47,127,127,255,127,255,255,47⟩⟩]⟩
theorem node1272 : UpperPrefix a [2,5,4,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,1,0] 30 cert1272 (by decide +kernel)

def cert1273 : Leaf := ⟨⟨104,76,0,165,77,13,37,109,105⟩,[(2,3)],[(4,2,2),(7,4,3),(1,5,1)],⟨7,35,28,88,176,98,200,385,261⟩,⟨7,35,28,88,176,98,200,384,260⟩,[⟨8,1184347496396690292735,⟨47,47,127,127,255,127,255,255,47⟩⟩]⟩
theorem node1273 : UpperPrefix a [2,5,4,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,1,3] 30 cert1273 (by decide +kernel)

def cert1274 : Local := ⟨⟨104,76,0,165,77,13,0,109,105⟩,[(2,3),(6,7)],[(4,2,2),(7,4,3),(1,5,1),(8,6,6)]⟩
theorem node1274 : UpperPrefix a [2,5,4,6,7,1,8] 30 :=
  local_sound a [2,5,4,6,7,1,8] 30 cert1274 (by decide +kernel)

theorem node1275 : UpperPrefix a [2,5,4,6,7,1] 30 :=
  branch_upper a [2,5,4,6,7,1] 30 (by decide) (fin9_cases _
  node1272
  (invalid_upper a [2,5,4,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,1,2] 30 (by decide +kernel))
  node1273
  (invalid_upper a [2,5,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,1,7] 30 (by decide +kernel))
  node1274)

def cert1276 : Leaf := ⟨⟨296,268,0,423,263,0,295,39,35⟩,[(2,3),(5,3)],[(4,2,2),(6,3,5),(7,4,3)],⟨7,35,28,88,176,104,451,387,263⟩,⟨7,35,28,88,176,104,192,384,260⟩,[⟨3,1214857655926163789317121,⟨471,499,20,80,176,96,192,384,260⟩⟩]⟩
theorem node1276 : UpperPrefix a [2,5,4,6,7,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,3] 30 cert1276 (by decide +kernel)

def cert1277 : Leaf := ⟨⟨104,72,0,161,329,9,42,105,105⟩,[(2,3)],[(4,2,2),(7,4,3),(8,5,4),(1,7,6)],⟨7,35,28,88,176,352,193,386,268⟩,⟨7,35,28,88,176,352,193,386,260⟩,[⟨2,1210402753736988753429505,⟨91,251,24,90,184,506,251,506,256⟩⟩]⟩
theorem node1277 : UpperPrefix a [2,5,4,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,8,0,1] 30 cert1277 (by decide +kernel)

def cert1278 : Leaf := ⟨⟨104,76,0,166,334,14,46,102,106⟩,[(2,3)],[(4,2,2),(7,4,3),(8,5,4)],⟨7,35,28,88,176,352,193,392,262⟩,⟨7,35,28,88,176,352,193,392,260⟩,[⟨0,1225178557451169418445824,⟨406,446,28,252,188,508,508,412,260⟩⟩]⟩
theorem node1278 : UpperPrefix a [2,5,4,6,7,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,8,0,3] 30 cert1278 (by decide +kernel)

theorem node1279 : UpperPrefix a [2,5,4,6,7,8,0] 30 :=
  branch_upper a [2,5,4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,6,7,8,0,0] 30 (by decide +kernel))
  node1277
  (invalid_upper a [2,5,4,6,7,8,0,2] 30 (by decide +kernel))
  node1278
  (invalid_upper a [2,5,4,6,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,0,8] 30 (by decide +kernel)))

#print axioms node1279
end Delivery.FiniteExclusion.Sharp2x7
