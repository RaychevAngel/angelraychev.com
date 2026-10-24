import RegularNineSharp2x7Base
import RegularNineSharp2x7C019
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert1280 : Local := ⟨⟨104,72,0,162,330,10,41,110,106⟩,[(2,3)],[(2,0,7),(4,2,2),(7,4,3),(8,5,4),(0,7,6)]⟩
theorem node1280 : UpperPrefix a [2,5,4,6,7,8,1,0] 30 :=
  local_sound a [2,5,4,6,7,8,1,0] 30 cert1280 (by decide +kernel)

def cert1281 : Leaf := ⟨⟨96,68,0,167,327,7,37,103,99⟩,[(2,3)],[(4,2,2),(7,4,3),(8,5,4)],⟨7,35,28,88,176,352,194,392,261⟩,⟨7,35,28,88,176,352,194,392,260⟩,[⟨3,1233721996429115459325701,⟨295,291,375,80,242,371,242,499,295⟩⟩]⟩
theorem node1281 : UpperPrefix a [2,5,4,6,7,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,8,1,3] 30 cert1281 (by decide +kernel)

theorem node1282 : UpperPrefix a [2,5,4,6,7,8,1] 30 :=
  branch_upper a [2,5,4,6,7,8,1] 30 (by decide) (fin9_cases _
  node1280
  (invalid_upper a [2,5,4,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,1,2] 30 (by decide +kernel))
  node1281
  (invalid_upper a [2,5,4,6,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,1,8] 30 (by decide +kernel)))

def cert1283 : Leaf := ⟨⟨104,76,0,164,332,12,36,111,107⟩,[(2,3)],[(4,2,2),(7,4,3),(8,5,4)],⟨7,35,28,88,176,352,200,387,263⟩,⟨7,35,28,88,176,352,200,384,260⟩,[⟨0,1210110163874063632565248,⟨14,46,92,92,252,380,252,508,268⟩⟩,⟨1,1210110163874063632564225,⟨13,45,92,92,252,380,252,508,268⟩⟩]⟩
theorem node1283 : UpperPrefix a [2,5,4,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,7,8,3] 30 cert1283 (by decide +kernel)

theorem node1284 : UpperPrefix a [2,5,4,6,7,8] 30 :=
  branch_upper a [2,5,4,6,7,8] 30 (by decide) (fin9_cases _
  node1279
  node1282
  (invalid_upper a [2,5,4,6,7,8,2] 30 (by decide +kernel))
  node1283
  (invalid_upper a [2,5,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,8,8] 30 (by decide +kernel)))

theorem node1285 : UpperPrefix a [2,5,4,6,7] 30 :=
  branch_upper a [2,5,4,6,7] 30 (by decide) (fin9_cases _
  node1271
  node1275
  (invalid_upper a [2,5,4,6,7,2] 30 (by decide +kernel))
  node1276
  (invalid_upper a [2,5,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,7,7] 30 (by decide +kernel))
  node1284)

def cert1286 : Leaf := ⟨⟨360,0,0,418,206,270,298,106,234⟩,[(1,5),(2,3)],[(4,2,2),(0,5,1)],⟨7,35,28,88,304,97,202,394,398⟩,⟨7,35,28,88,304,97,192,384,260⟩,[⟨2,1210255427466820197565441,⟨11,35,216,216,506,99,192,384,264⟩⟩,⟨7,1208926973944609253653773,⟨7,35,63,127,307,99,64,257,263⟩⟩]⟩
theorem node1286 : UpperPrefix a [2,5,4,6,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,6,8,0] 30 cert1286 (by decide +kernel)

def cert1287 : Leaf := ⟨⟨480,452,0,420,196,389,292,108,232⟩,[(2,3)],[(4,2,2),(1,5,1),(0,6,5)],⟨7,35,28,88,304,98,193,392,396⟩,⟨7,35,28,88,304,98,193,384,260⟩,[⟨3,1210109878172530336967941,⟨7,35,55,114,307,98,243,499,263⟩⟩]⟩
theorem node1287 : UpperPrefix a [2,5,4,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,4,6,8,1,0] 30 cert1287 (by decide +kernel)

def cert1288 : Leaf := ⟨⟨480,452,0,421,133,389,293,37,161⟩,[(2,3)],[(4,2,2),(1,5,1)],⟨7,35,28,88,304,98,200,385,389⟩,⟨7,35,28,88,304,98,200,384,260⟩,[⟨3,1236292718778368614477061,⟨407,435,439,242,435,242,224,385,407⟩⟩,⟨6,1214856448961464729863169,⟨407,435,28,28,304,178,140,384,260⟩⟩]⟩
theorem node1288 : UpperPrefix a [2,5,4,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,8,1,3] 30 cert1288 (by decide +kernel)

theorem node1289 : UpperPrefix a [2,5,4,6,8,1] 30 :=
  branch_upper a [2,5,4,6,8,1] 30 (by decide) (fin9_cases _
  node1287
  (invalid_upper a [2,5,4,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,1,2] 30 (by decide +kernel))
  node1288
  (invalid_upper a [2,5,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,1,8] 30 (by decide +kernel)))

def cert1290 : Leaf := ⟨⟨424,396,0,423,135,0,263,7,131⟩,[(2,3),(5,3)],[(4,2,2),(6,3,5)],⟨7,35,28,88,304,104,195,387,391⟩,⟨7,35,28,88,304,104,192,384,260⟩,[⟨3,1214857655926163789317121,⟨471,499,20,80,304,96,192,384,260⟩⟩,⟨5,1214857654800127519360001,⟨455,451,28,92,272,76,192,384,260⟩⟩]⟩
theorem node1290 : UpperPrefix a [2,5,4,6,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,8,3] 30 cert1290 (by decide +kernel)

def cert1291 : Leaf := ⟨⟨104,64,0,295,79,0,302,111,107⟩,[(2,3),(5,6)],[(4,2,2),(7,5,5)],⟨7,35,28,88,304,224,193,394,270⟩,⟨7,35,28,88,304,224,193,384,260⟩,[⟨8,1181747921022327231501,⟨7,35,31,127,48,226,227,128,5⟩⟩,⟨2,1210107567535651498787841,⟨3,35,24,122,304,226,227,384,256⟩⟩,⟨3,1210107567535650426094593,⟨7,35,20,114,304,226,227,384,260⟩⟩]⟩
theorem node1291 : UpperPrefix a [2,5,4,6,8,7,0] 30 :=
  Boolean.leaf_sound a [2,5,4,6,8,7,0] 30 cert1291 (by decide +kernel)

def cert1292 : Leaf := ⟨⟨360,332,0,293,77,0,301,109,105⟩,[(2,3),(5,6)],[(4,2,2),(7,5,5)],⟨7,35,28,88,304,224,194,393,269⟩,⟨7,35,28,88,304,224,194,384,260⟩,[⟨1,1219570747250012902129665,⟨405,445,28,124,316,252,508,384,260⟩⟩]⟩
theorem node1292 : UpperPrefix a [2,5,4,6,8,7,1] 30 :=
  Boolean.leaf_sound a [2,5,4,6,8,7,1] 30 cert1292 (by decide +kernel)

def cert1293 : Leaf := ⟨⟨352,324,0,295,71,0,295,103,99⟩,[(2,3),(5,6)],[(4,2,2),(7,5,5)],⟨7,35,28,88,304,224,200,387,263⟩,⟨7,35,28,88,304,224,200,384,260⟩,[⟨3,1236292721030168428162309,⟨407,435,439,242,435,224,224,385,407⟩⟩]⟩
theorem node1293 : UpperPrefix a [2,5,4,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,5,4,6,8,7,3] 30 cert1293 (by decide +kernel)

theorem node1294 : UpperPrefix a [2,5,4,6,8,7] 30 :=
  branch_upper a [2,5,4,6,8,7] 30 (by decide) (fin9_cases _
  node1291
  node1292
  (invalid_upper a [2,5,4,6,8,7,2] 30 (by decide +kernel))
  node1293
  (invalid_upper a [2,5,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,7,8] 30 (by decide +kernel)))

theorem node1295 : UpperPrefix a [2,5,4,6,8] 30 :=
  branch_upper a [2,5,4,6,8] 30 (by decide) (fin9_cases _
  node1286
  node1289
  (invalid_upper a [2,5,4,6,8,2] 30 (by decide +kernel))
  node1290
  (invalid_upper a [2,5,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,8,6] 30 (by decide +kernel))
  node1294
  (invalid_upper a [2,5,4,6,8,8] 30 (by decide +kernel)))

theorem node1296 : UpperPrefix a [2,5,4,6] 30 :=
  branch_upper a [2,5,4,6] 30 (by decide) (fin9_cases _
  node1268
  node1269
  (invalid_upper a [2,5,4,6,2] 30 (by decide +kernel))
  node1270
  (invalid_upper a [2,5,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,6,6] 30 (by decide +kernel))
  node1285
  node1295)

def cert1297 : Local := ⟨⟨488,0,0,357,0,397,301,109,233⟩,[(1,4),(2,3),(4,1)],[(4,2,2),(1,5,1),(1,5,4)]⟩
theorem node1297 : UpperPrefix a [2,5,4,7,0,1] 30 :=
  local_sound a [2,5,4,7,0,1] 30 cert1297 (by decide +kernel)

def cert1298 : Leaf := ⟨⟨360,0,0,358,0,390,302,110,106⟩,[(1,4),(2,3),(4,1)],[(4,2,2),(7,3,5)],⟨7,35,28,152,49,104,450,450,326⟩,⟨7,35,28,152,49,104,192,384,260⟩,[⟨0,1214857656488979531301888,⟨454,482,60,188,508,108,192,384,260⟩⟩]⟩
theorem node1298 : UpperPrefix a [2,5,4,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,4,7,0,3] 30 cert1298 (by decide +kernel)

def cert1299 : Leaf := ⟨⟨224,0,0,359,0,143,43,111,235⟩,[(1,4),(2,3),(4,1)],[(4,2,2)],⟨7,35,28,152,49,352,202,458,334⟩,⟨7,35,28,152,49,352,192,384,260⟩,[⟨8,1181889784548028326925,⟨23,51,95,223,51,96,192,128,5⟩⟩,⟨2,1210107709399177199887361,⟨19,51,90,218,51,352,192,384,256⟩⟩,⟨3,1210107565283988051338245,⟨23,51,23,146,51,352,192,384,261⟩⟩]⟩
theorem node1299 : UpperPrefix a [2,5,4,7,0,8] 30 :=
  Boolean.leaf_sound a [2,5,4,7,0,8] 30 cert1299 (by decide +kernel)

theorem node1300 : UpperPrefix a [2,5,4,7,0] 30 :=
  branch_upper a [2,5,4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,7,0,0] 30 (by decide +kernel))
  node1297
  (invalid_upper a [2,5,4,7,0,2] 30 (by decide +kernel))
  node1298
  (invalid_upper a [2,5,4,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,0,7] 30 (by decide +kernel))
  node1299)

def cert1301 : Local := ⟨⟨456,0,0,326,0,398,270,78,202⟩,[(1,5),(2,3),(4,1)],[(5,1,4),(4,2,2),(0,5,1),(0,5,4)]⟩
theorem node1301 : UpperPrefix a [2,5,4,7,1,0] 30 :=
  local_sound a [2,5,4,7,1,0] 30 cert1301 (by decide +kernel)

def cert1302 : Leaf := ⟨⟨328,332,0,325,0,389,269,77,73⟩,[(2,3),(4,1)],[(5,1,4),(4,2,2),(7,3,5)],⟨7,35,28,152,50,104,449,449,325⟩,⟨7,35,28,152,50,104,192,384,260⟩,[⟨1,1214857656488979531300865,⟨453,481,60,188,252,108,192,384,260⟩⟩]⟩
theorem node1302 : UpperPrefix a [2,5,4,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,4,7,1,3] 30 cert1302 (by decide +kernel)

def cert1303 : Leaf := ⟨⟨456,460,0,325,0,141,268,77,201⟩,[(2,3),(4,1)],[(5,1,4),(4,2,2)],⟨7,35,28,152,50,352,193,456,332⟩,⟨7,35,28,152,50,352,193,384,260⟩,[⟨1,1290544649780763288403969,⟨493,481,444,444,508,352,481,384,268⟩⟩]⟩
theorem node1303 : UpperPrefix a [2,5,4,7,1,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,7,1,8,0] 30 cert1303 (by decide +kernel)

def cert1304 : Local := ⟨⟨328,332,0,327,0,15,0,79,75⟩,[(2,3),(4,1),(6,3)],[(5,1,4),(4,2,2),(7,3,6)]⟩
theorem node1304 : UpperPrefix a [2,5,4,7,1,8,3] 30 :=
  local_sound a [2,5,4,7,1,8,3] 30 cert1304 (by decide +kernel)

theorem node1305 : UpperPrefix a [2,5,4,7,1,8] 30 :=
  branch_upper a [2,5,4,7,1,8] 30 (by decide) (fin9_cases _
  node1303
  (invalid_upper a [2,5,4,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,8,2] 30 (by decide +kernel))
  node1304
  (invalid_upper a [2,5,4,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,8,8] 30 (by decide +kernel)))

theorem node1306 : UpperPrefix a [2,5,4,7,1] 30 :=
  branch_upper a [2,5,4,7,1] 30 (by decide) (fin9_cases _
  node1301
  (invalid_upper a [2,5,4,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,2] 30 (by decide +kernel))
  node1302
  (invalid_upper a [2,5,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,1,7] 30 (by decide +kernel))
  node1305)

def cert1307 : Local := ⟨⟨480,0,0,358,454,390,294,102,226⟩,[(1,5),(2,3)],[(4,2,2),(3,4,2),(0,5,1)]⟩
theorem node1307 : UpperPrefix a [2,5,4,7,3,0] 30 :=
  local_sound a [2,5,4,7,3,0] 30 cert1307 (by decide +kernel)

def cert1308 : Leaf := ⟨⟨224,196,0,101,197,133,293,101,225⟩,[(2,3)],[(4,2,2),(3,4,2),(1,5,1)],⟨7,35,28,152,56,98,449,449,325⟩,⟨7,35,28,152,56,98,192,384,260⟩,[⟨8,1181747927628016313471,⟨7,55,31,159,63,127,255,128,5⟩⟩]⟩
theorem node1308 : UpperPrefix a [2,5,4,7,3,1] 30 :=
  Boolean.leaf_sound a [2,5,4,7,3,1] 30 cert1308 (by decide +kernel)

def cert1309 : Leaf := ⟨⟨32,4,0,359,455,135,7,71,195⟩,[(2,3)],[(4,2,2),(3,4,2)],⟨7,35,28,152,56,352,195,451,327⟩,⟨7,35,28,152,56,352,192,384,260⟩,[⟨5,1214857654800127523554305,⟨455,451,28,156,28,320,192,384,260⟩⟩,⟨8,1181889784410593567773,⟨7,35,95,223,127,96,192,128,5⟩⟩,⟨6,1210106412362347085571101,⟨7,35,31,159,63,288,128,384,261⟩⟩,⟨7,1208926973663134281114653,⟨7,35,31,31,63,352,64,256,261⟩⟩]⟩
theorem node1309 : UpperPrefix a [2,5,4,7,3,8] 30 :=
  Boolean.leaf_sound a [2,5,4,7,3,8] 30 cert1309 (by decide +kernel)

theorem node1310 : UpperPrefix a [2,5,4,7,3] 30 :=
  branch_upper a [2,5,4,7,3] 30 (by decide) (fin9_cases _
  node1307
  node1308
  (invalid_upper a [2,5,4,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,3,7] 30 (by decide +kernel))
  node1309)

def cert1311 : Local := ⟨⟨424,0,0,294,0,398,302,46,170⟩,[(1,5),(2,3),(4,5)],[(4,2,2),(6,4,4),(0,5,1)]⟩
theorem node1311 : UpperPrefix a [2,5,4,7,6,0] 30 :=
  local_sound a [2,5,4,7,6,0] 30 cert1311 (by decide +kernel)

def cert1312 : Local := ⟨⟨424,396,0,293,0,397,301,45,169⟩,[(2,3),(4,5)],[(4,2,2),(6,4,4),(1,5,1)]⟩
theorem node1312 : UpperPrefix a [2,5,4,7,6,1] 30 :=
  local_sound a [2,5,4,7,6,1] 30 cert1312 (by decide +kernel)

def cert1313 : Leaf := ⟨⟨40,12,0,39,0,135,303,47,43⟩,[(2,3),(4,5)],[(4,2,2),(7,3,5),(6,4,4)],⟨7,35,28,152,112,104,451,387,263⟩,⟨7,35,28,152,112,104,192,384,260⟩,[⟨8,1181748490577969741183,⟨7,55,63,191,127,127,255,129,7⟩⟩]⟩
theorem node1313 : UpperPrefix a [2,5,4,7,6,3] 30 :=
  Boolean.leaf_sound a [2,5,4,7,6,3] 30 cert1313 (by decide +kernel)

def cert1314 : Leaf := ⟨⟨424,396,0,294,0,142,302,46,170⟩,[(2,3),(4,5)],[(4,2,2),(6,4,4)],⟨7,35,28,152,112,352,193,394,270⟩,⟨7,35,28,152,112,352,193,384,260⟩,[⟨0,1224302337106976959890432,⟨398,446,28,156,124,380,508,384,260⟩⟩]⟩
theorem node1314 : UpperPrefix a [2,5,4,7,6,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,7,6,8,0] 30 cert1314 (by decide +kernel)

def cert1315 : Leaf := ⟨⟨424,396,0,293,0,141,301,45,169⟩,[(2,3),(4,5)],[(4,2,2),(6,4,4)],⟨7,35,28,152,112,352,194,393,269⟩,⟨7,35,28,152,112,352,194,384,260⟩,[⟨1,1224302337106976959889409,⟨397,445,28,156,124,380,508,384,260⟩⟩]⟩
theorem node1315 : UpperPrefix a [2,5,4,7,6,8,1] 30 :=
  Boolean.leaf_sound a [2,5,4,7,6,8,1] 30 cert1315 (by decide +kernel)

def cert1316 : Local := ⟨⟨296,268,0,295,0,15,0,47,43⟩,[(2,3),(4,5),(6,3)],[(4,2,2),(7,3,6),(6,4,4)]⟩
theorem node1316 : UpperPrefix a [2,5,4,7,6,8,3] 30 :=
  local_sound a [2,5,4,7,6,8,3] 30 cert1316 (by decide +kernel)

theorem node1317 : UpperPrefix a [2,5,4,7,6,8] 30 :=
  branch_upper a [2,5,4,7,6,8] 30 (by decide) (fin9_cases _
  node1314
  node1315
  (invalid_upper a [2,5,4,7,6,8,2] 30 (by decide +kernel))
  node1316
  (invalid_upper a [2,5,4,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,6,8,8] 30 (by decide +kernel)))

theorem node1318 : UpperPrefix a [2,5,4,7,6] 30 :=
  branch_upper a [2,5,4,7,6] 30 (by decide) (fin9_cases _
  node1311
  node1312
  (invalid_upper a [2,5,4,7,6,2] 30 (by decide +kernel))
  node1313
  (invalid_upper a [2,5,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,6,7] 30 (by decide +kernel))
  node1317)

def cert1319 : Leaf := ⟨⟨232,0,0,354,206,142,42,106,234⟩,[(1,5),(2,3)],[(4,2,2),(8,4,3),(0,5,1)],⟨7,35,28,152,304,97,202,458,334⟩,⟨7,35,28,152,304,97,192,384,260⟩,[⟨2,1210255427466820197565441,⟨11,35,216,216,506,99,192,384,264⟩⟩]⟩
theorem node1319 : UpperPrefix a [2,5,4,7,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,7,8,0] 30 cert1319 (by decide +kernel)

def cert1320 : Leaf := ⟨⟨224,196,0,356,196,133,36,108,232⟩,[(2,3)],[(4,2,2),(8,4,3),(1,5,1),(0,6,5)],⟨7,35,28,152,304,98,193,456,332⟩,⟨7,35,28,152,304,98,193,384,260⟩,[⟨3,1210109878172530336967941,⟨7,35,55,242,307,98,243,499,263⟩⟩]⟩
theorem node1320 : UpperPrefix a [2,5,4,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,4,7,8,1,0] 30 cert1320 (by decide +kernel)

def cert1321 : Local := ⟨⟨104,76,0,357,77,13,0,109,105⟩,[(2,3),(6,3)],[(4,2,2),(7,3,6),(8,4,3),(1,5,1)]⟩
theorem node1321 : UpperPrefix a [2,5,4,7,8,1,3] 30 :=
  local_sound a [2,5,4,7,8,1,3] 30 cert1321 (by decide +kernel)

theorem node1322 : UpperPrefix a [2,5,4,7,8,1] 30 :=
  branch_upper a [2,5,4,7,8,1] 30 (by decide) (fin9_cases _
  node1320
  (invalid_upper a [2,5,4,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,1,2] 30 (by decide +kernel))
  node1321
  (invalid_upper a [2,5,4,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,1,8] 30 (by decide +kernel)))

def cert1323 : Leaf := ⟨⟨104,76,0,359,71,135,7,71,67⟩,[(2,3)],[(4,2,2),(7,3,5),(8,4,3)],⟨7,35,28,152,304,104,195,451,327⟩,⟨7,35,28,152,304,104,192,384,260⟩,[⟨3,1214857655926163789317121,⟨471,499,20,144,304,96,192,384,260⟩⟩,⟨5,1214857654800127519360001,⟨455,451,28,156,272,76,192,384,260⟩⟩]⟩
theorem node1323 : UpperPrefix a [2,5,4,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,4,7,8,3] 30 cert1323 (by decide +kernel)

theorem node1324 : UpperPrefix a [2,5,4,7,8] 30 :=
  branch_upper a [2,5,4,7,8] 30 (by decide) (fin9_cases _
  node1319
  node1322
  (invalid_upper a [2,5,4,7,8,2] 30 (by decide +kernel))
  node1323
  (invalid_upper a [2,5,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,8,8] 30 (by decide +kernel)))

theorem node1325 : UpperPrefix a [2,5,4,7] 30 :=
  branch_upper a [2,5,4,7] 30 (by decide) (fin9_cases _
  node1300
  node1306
  (invalid_upper a [2,5,4,7,2] 30 (by decide +kernel))
  node1310
  (invalid_upper a [2,5,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,7,5] 30 (by decide +kernel))
  node1318
  (invalid_upper a [2,5,4,7,7] 30 (by decide +kernel))
  node1324)

def cert1326 : Leaf := ⟨⟨416,0,0,231,0,395,299,107,235⟩,[(1,4),(2,3),(4,1)],[(4,2,2)],⟨7,35,28,280,49,234,202,458,462⟩,⟨7,35,28,280,49,96,192,384,260⟩,[⟨2,1210181568855347260564993,⟨115,51,250,506,51,96,192,384,352⟩⟩,⟨3,1210107565283988051338245,⟨23,51,23,274,51,96,192,384,261⟩⟩,⟨6,1210106412362484520330253,⟨23,51,31,287,51,32,128,384,261⟩⟩]⟩
theorem node1326 : UpperPrefix a [2,5,4,8,0] 30 :=
  Boolean.leaf_sound a [2,5,4,8,0] 30 cert1326 (by decide +kernel)

def cert1327 : Local := ⟨⟨456,0,0,198,0,398,270,78,202⟩,[(1,5),(2,3),(4,1)],[(5,1,4),(4,2,2),(0,5,1),(0,5,4)]⟩
theorem node1327 : UpperPrefix a [2,5,4,8,1,0] 30 :=
  local_sound a [2,5,4,8,1,0] 30 cert1327 (by decide +kernel)

def cert1328 : Leaf := ⟨⟨456,460,0,199,0,391,261,69,193⟩,[(2,3),(4,1)],[(5,1,4),(4,2,2)],⟨7,35,28,280,50,104,193,449,453⟩,⟨7,35,28,280,50,104,192,384,260⟩,[⟨1,1214857655926027426201601,⟨453,481,28,284,240,108,192,384,260⟩⟩,⟨3,1214857655926163789317121,⟨471,499,20,272,242,96,192,384,260⟩⟩]⟩
theorem node1328 : UpperPrefix a [2,5,4,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,4,8,1,3] 30 cert1328 (by decide +kernel)

def cert1329 : Local := ⟨⟨328,332,0,71,0,0,271,79,75⟩,[(2,3),(4,1),(5,6)],[(5,1,4),(4,2,2),(7,5,5)]⟩
theorem node1329 : UpperPrefix a [2,5,4,8,1,7] 30 :=
  local_sound a [2,5,4,8,1,7] 30 cert1329 (by decide +kernel)

theorem node1330 : UpperPrefix a [2,5,4,8,1] 30 :=
  branch_upper a [2,5,4,8,1] 30 (by decide) (fin9_cases _
  node1327
  (invalid_upper a [2,5,4,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,1,2] 30 (by decide +kernel))
  node1328
  (invalid_upper a [2,5,4,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,1,6] 30 (by decide +kernel))
  node1329
  (invalid_upper a [2,5,4,8,1,8] 30 (by decide +kernel)))

def cert1331 : Local := ⟨⟨480,0,0,230,454,390,294,102,226⟩,[(1,5),(2,3)],[(4,2,2),(3,4,2),(0,5,1)]⟩
theorem node1331 : UpperPrefix a [2,5,4,8,3,0] 30 :=
  local_sound a [2,5,4,8,3,0] 30 cert1331 (by decide +kernel)

def cert1332 : Leaf := ⟨⟨416,388,0,229,453,389,261,69,193⟩,[(2,3)],[(4,2,2),(3,4,2),(1,5,1)],⟨7,35,28,280,56,98,193,449,453⟩,⟨7,35,28,280,56,98,192,384,260⟩,[⟨5,1214857654800127523554305,⟨455,451,28,284,28,194,192,384,260⟩⟩,⟨6,1210106412362347085571101,⟨7,35,31,287,63,34,128,384,261⟩⟩]⟩
theorem node1332 : UpperPrefix a [2,5,4,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,4,8,3,1] 30 cert1332 (by decide +kernel)

def cert1333 : Local := ⟨⟨352,324,0,103,327,0,295,103,99⟩,[(2,3),(5,6)],[(4,2,2),(3,4,2),(7,5,5)]⟩
theorem node1333 : UpperPrefix a [2,5,4,8,3,7] 30 :=
  local_sound a [2,5,4,8,3,7] 30 cert1333 (by decide +kernel)

theorem node1334 : UpperPrefix a [2,5,4,8,3] 30 :=
  branch_upper a [2,5,4,8,3] 30 (by decide) (fin9_cases _
  node1331
  node1332
  (invalid_upper a [2,5,4,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,3,6] 30 (by decide +kernel))
  node1333
  (invalid_upper a [2,5,4,8,3,8] 30 (by decide +kernel)))

def cert1335 : Local := ⟨⟨424,0,0,166,0,398,302,46,170⟩,[(1,5),(2,3),(4,5)],[(4,2,2),(6,4,4),(0,5,1)]⟩
theorem node1335 : UpperPrefix a [2,5,4,8,6,0] 30 :=
  local_sound a [2,5,4,8,6,0] 30 cert1335 (by decide +kernel)

def cert1336 : Local := ⟨⟨424,396,0,165,0,397,301,45,169⟩,[(2,3),(4,5)],[(4,2,2),(6,4,4),(1,5,1)]⟩
theorem node1336 : UpperPrefix a [2,5,4,8,6,1] 30 :=
  local_sound a [2,5,4,8,6,1] 30 cert1336 (by decide +kernel)

def cert1337 : Leaf := ⟨⟨424,396,0,167,0,391,263,7,131⟩,[(2,3),(4,5)],[(4,2,2),(6,4,4)],⟨7,35,28,280,112,104,195,387,391⟩,⟨7,35,28,280,112,104,192,384,260⟩,[⟨3,1214857655928362812572673,⟨471,499,20,272,112,112,192,384,260⟩⟩,⟨5,1214857654800127519360001,⟨455,451,28,284,80,76,192,384,260⟩⟩]⟩
theorem node1337 : UpperPrefix a [2,5,4,8,6,3] 30 :=
  Boolean.leaf_sound a [2,5,4,8,6,3] 30 cert1337 (by decide +kernel)

def cert1338 : Local := ⟨⟨296,268,0,39,0,0,303,47,43⟩,[(2,3),(4,5),(5,6)],[(4,2,2),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node1338 : UpperPrefix a [2,5,4,8,6,7] 30 :=
  local_sound a [2,5,4,8,6,7] 30 cert1338 (by decide +kernel)

theorem node1339 : UpperPrefix a [2,5,4,8,6] 30 :=
  branch_upper a [2,5,4,8,6] 30 (by decide) (fin9_cases _
  node1335
  node1336
  (invalid_upper a [2,5,4,8,6,2] 30 (by decide +kernel))
  node1337
  (invalid_upper a [2,5,4,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,6,6] 30 (by decide +kernel))
  node1338
  (invalid_upper a [2,5,4,8,6,8] 30 (by decide +kernel)))

def cert1340 : Local := ⟨⟨488,0,0,228,332,398,300,108,232⟩,[(1,5),(2,3)],[(4,2,2),(0,5,1),(1,6,5)]⟩
theorem node1340 : UpperPrefix a [2,5,4,8,7,0,1] 30 :=
  local_sound a [2,5,4,8,7,0,1] 30 cert1340 (by decide +kernel)

def cert1341 : Leaf := ⟨⟨104,0,0,230,78,14,294,110,106⟩,[(1,5),(2,3)],[(4,2,2),(8,3,6),(0,5,1)],⟨7,35,28,280,176,97,200,450,326⟩,⟨7,35,28,280,176,97,200,384,260⟩,[⟨7,1511158430818591384323137,⟨7,35,28,284,50,355,367,256,260⟩⟩]⟩
theorem node1341 : UpperPrefix a [2,5,4,8,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,4,8,7,0,3] 30 cert1341 (by decide +kernel)

theorem node1342 : UpperPrefix a [2,5,4,8,7,0] 30 :=
  branch_upper a [2,5,4,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,4,8,7,0,0] 30 (by decide +kernel))
  node1340
  (invalid_upper a [2,5,4,8,7,0,2] 30 (by decide +kernel))
  node1341
  (invalid_upper a [2,5,4,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,4,8,7,0,8] 30 (by decide +kernel)))

def cert1343 : Leaf := ⟨⟨480,452,0,228,324,389,292,108,232⟩,[(2,3)],[(4,2,2),(1,5,1),(0,6,5)],⟨7,35,28,280,176,98,193,456,332⟩,⟨7,35,28,280,176,98,193,384,260⟩,[⟨3,1210109878458403360185605,⟨7,35,55,307,242,114,243,499,263⟩⟩]⟩
theorem node1343 : UpperPrefix a [2,5,4,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,4,8,7,1,0] 30 cert1343 (by decide +kernel)

#print axioms node1343
end Delivery.FiniteExclusion.Sharp2x7
