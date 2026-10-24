import RegularNineSharp3x6Base
import RegularNineSharp3x6C019
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node1280 : UpperPrefix a [3,6,5,1,7,8] 30 :=
  branch_upper a [3,6,5,1,7,8] 30 (by decide) (fin9_cases _
  node1277
  (invalid_upper a [3,6,5,1,7,8,1] 30 (by decide +kernel))
  node1278
  (invalid_upper a [3,6,5,1,7,8,3] 30 (by decide +kernel))
  node1279
  (invalid_upper a [3,6,5,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,8,8] 30 (by decide +kernel)))

theorem node1281 : UpperPrefix a [3,6,5,1,7] 30 :=
  branch_upper a [3,6,5,1,7] 30 (by decide) (fin9_cases _
  node1272
  (invalid_upper a [3,6,5,1,7,1] 30 (by decide +kernel))
  node1273
  (invalid_upper a [3,6,5,1,7,3] 30 (by decide +kernel))
  node1274
  (invalid_upper a [3,6,5,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,7,7] 30 (by decide +kernel))
  node1280)

def cert1282 : Leaf := ⟨⟨0,304,0,356,204,412,308,116,244⟩,[(0,3),(2,5)],[(1,3,0),(0,5,2)],⟨11,70,37,26,304,97,212,404,412⟩,⟨11,70,37,26,304,97,192,384,264⟩,[⟨3,1210255427466816448914433,⟨3,70,39,210,502,103,192,384,256⟩⟩,⟨7,1208926973663136434897945,⟨11,70,39,31,319,103,64,256,265⟩⟩]⟩
theorem node1282 : UpperPrefix a [3,6,5,1,8,0] 30 :=
  Boolean.leaf_sound a [3,6,5,1,8,0] 30 cert1282 (by decide +kernel)

def cert1283 : Leaf := ⟨⟨0,0,472,453,205,0,285,93,213⟩,[(0,3),(1,5),(5,1)],[(1,3,0)],⟨11,70,37,26,304,100,209,401,409⟩,⟨11,70,37,26,304,100,192,384,264⟩,[⟨5,1323666153021274154091545,⟨459,70,7,475,475,70,192,384,457⟩⟩]⟩
theorem node1283 : UpperPrefix a [3,6,5,1,8,2] 30 :=
  Boolean.leaf_sound a [3,6,5,1,8,2] 30 cert1283 (by decide +kernel)

def cert1284 : Leaf := ⟨⟨0,41,72,100,204,396,300,108,228⟩,[(0,3)],[(1,3,0),(0,6,1)],⟨11,70,37,26,304,112,193,388,396⟩,⟨11,70,37,26,304,112,193,384,264⟩,[⟨4,1248115225963584233176329,⟨459,70,103,463,487,230,193,449,459⟩⟩,⟨7,1208926973663140729865277,⟨11,71,47,31,319,127,65,256,265⟩⟩,⟨8,1181745669228966462525,⟨11,71,47,31,63,127,193,128,9⟩⟩]⟩
theorem node1284 : UpperPrefix a [3,6,5,1,8,4,0] 30 :=
  Boolean.leaf_sound a [3,6,5,1,8,4,0] 30 cert1284 (by decide +kernel)

def cert1285 : Leaf := ⟨⟨0,0,456,481,201,393,297,105,225⟩,[(0,3),(1,6)],[(1,3,0),(2,6,1)],⟨11,70,37,26,304,112,196,385,393⟩,⟨11,70,37,26,304,112,196,384,264⟩,[⟨4,1255238641551790184660233,⟨459,198,487,463,487,230,198,385,459⟩⟩]⟩
theorem node1285 : UpperPrefix a [3,6,5,1,8,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,1,8,4,2] 30 cert1285 (by decide +kernel)

theorem node1286 : UpperPrefix a [3,6,5,1,8,4] 30 :=
  branch_upper a [3,6,5,1,8,4] 30 (by decide) (fin9_cases _
  node1284
  (invalid_upper a [3,6,5,1,8,4,1] 30 (by decide +kernel))
  node1285
  (invalid_upper a [3,6,5,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,4,8] 30 (by decide +kernel)))

def cert1287 : Local := ⟨⟨0,313,344,356,76,0,316,124,116⟩,[(0,3),(5,6)],[(1,3,0),(7,5,5),(0,6,1)]⟩
theorem node1287 : UpperPrefix a [3,6,5,1,8,7,0] 30 :=
  local_sound a [3,6,5,1,8,7,0] 30 cert1287 (by decide +kernel)

def cert1288 : Local := ⟨⟨0,0,344,353,73,0,313,121,113⟩,[(0,3),(1,6),(5,6)],[(1,3,0),(7,5,5),(2,6,1)]⟩
theorem node1288 : UpperPrefix a [3,6,5,1,8,7,2] 30 :=
  local_sound a [3,6,5,1,8,7,2] 30 cert1288 (by decide +kernel)

def cert1289 : Leaf := ⟨⟨0,56,88,101,76,0,300,125,117⟩,[(0,3),(5,6)],[(1,3,0),(8,4,6),(7,5,5)],⟨11,70,37,26,304,224,208,389,269⟩,⟨11,70,37,26,304,224,208,384,264⟩,[⟨0,1210110454351808737315840,⟨10,102,102,26,368,240,240,496,264⟩⟩]⟩
theorem node1289 : UpperPrefix a [3,6,5,1,8,7,4] 30 :=
  Boolean.leaf_sound a [3,6,5,1,8,7,4] 30 cert1289 (by decide +kernel)

theorem node1290 : UpperPrefix a [3,6,5,1,8,7] 30 :=
  branch_upper a [3,6,5,1,8,7] 30 (by decide) (fin9_cases _
  node1287
  (invalid_upper a [3,6,5,1,8,7,1] 30 (by decide +kernel))
  node1288
  (invalid_upper a [3,6,5,1,8,7,3] 30 (by decide +kernel))
  node1289
  (invalid_upper a [3,6,5,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,7,8] 30 (by decide +kernel)))

theorem node1291 : UpperPrefix a [3,6,5,1,8] 30 :=
  branch_upper a [3,6,5,1,8] 30 (by decide) (fin9_cases _
  node1282
  (invalid_upper a [3,6,5,1,8,1] 30 (by decide +kernel))
  node1283
  (invalid_upper a [3,6,5,1,8,3] 30 (by decide +kernel))
  node1286
  (invalid_upper a [3,6,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,8,6] 30 (by decide +kernel))
  node1290
  (invalid_upper a [3,6,5,1,8,8] 30 (by decide +kernel)))

theorem node1292 : UpperPrefix a [3,6,5,1] 30 :=
  branch_upper a [3,6,5,1] 30 (by decide) (fin9_cases _
  node1270
  (invalid_upper a [3,6,5,1,1] 30 (by decide +kernel))
  node1271
  (invalid_upper a [3,6,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,1,6] 30 (by decide +kernel))
  node1281
  node1291)

def cert1293 : Leaf := ⟨⟨404,408,0,419,0,410,282,26,146⟩,[(2,4),(4,2)],[(5,2,3),(2,3,0),(0,4,3)],⟨11,70,37,28,49,498,466,402,410⟩,⟨11,70,37,28,49,96,192,384,264⟩,[⟨6,1219569592072437914141699,⟨395,415,61,28,61,32,128,384,264⟩⟩]⟩
theorem node1293 : UpperPrefix a [3,6,5,2,0] 30 :=
  Boolean.leaf_sound a [3,6,5,2,0] 30 cert1293 (by decide +kernel)

def cert1294 : Leaf := ⟨⟨404,408,0,416,456,408,280,24,144⟩,[(2,5)],[(6,1,4),(5,2,3),(2,3,0),(0,5,2)],⟨11,70,37,28,50,97,464,400,408⟩,⟨11,70,37,28,50,97,192,384,264⟩,[⟨1,1323666154182358441656321,⟨493,68,37,476,508,101,192,384,456⟩⟩]⟩
theorem node1294 : UpperPrefix a [3,6,5,2,1,0] 30 :=
  Boolean.leaf_sound a [3,6,5,2,1,0] 30 cert1294 (by decide +kernel)

def cert1295 : Leaf := ⟨⟨20,25,26,35,73,11,283,27,147⟩,[],[(6,1,4),(5,2,3),(2,3,0)],⟨11,70,37,28,50,112,449,385,393⟩,⟨11,70,37,28,50,112,192,384,264⟩,[⟨7,1208926975992396940887159,⟨63,127,63,29,63,127,127,256,264⟩⟩,⟨8,1181747998485177484407,⟨63,127,63,29,63,127,255,128,8⟩⟩]⟩
theorem node1295 : UpperPrefix a [3,6,5,2,1,4] 30 :=
  Boolean.leaf_sound a [3,6,5,2,1,4] 30 cert1295 (by decide +kernel)

def cert1296 : Leaf := ⟨⟨20,25,26,35,73,0,283,27,19⟩,[(5,6)],[(6,1,4),(5,2,3),(2,3,0),(7,5,5)],⟨11,70,37,28,50,224,465,401,281⟩,⟨11,70,37,28,50,224,192,384,264⟩,[⟨8,1181747928047713567863,⟨31,127,63,29,63,255,255,128,8⟩⟩]⟩
theorem node1296 : UpperPrefix a [3,6,5,2,1,7] 30 :=
  Boolean.leaf_sound a [3,6,5,2,1,7] 30 cert1296 (by decide +kernel)

def cert1297 : Leaf := ⟨⟨276,281,280,290,328,152,280,24,144⟩,[],[(6,1,4),(5,2,3),(2,3,0),(0,6,1)],⟨11,70,37,28,50,352,193,400,408⟩,⟨11,70,37,28,50,352,193,384,264⟩,[⟨1,1247960302172686584643585,⟨493,68,101,412,48,356,229,384,392⟩⟩,⟨7,1208926973665615436334135,⟨11,95,63,29,63,383,65,256,264⟩⟩]⟩
theorem node1297 : UpperPrefix a [3,6,5,2,1,8,0] 30 :=
  Boolean.leaf_sound a [3,6,5,2,1,8,0] 30 cert1297 (by decide +kernel)

def cert1298 : Leaf := ⟨⟨20,25,24,35,73,153,265,25,145⟩,[],[(6,1,4),(5,2,3),(2,3,0)],⟨11,70,37,28,50,352,208,385,393⟩,⟨11,70,37,28,50,352,208,384,264⟩,[⟨1,1214876201784477308157953,⟨493,196,421,220,48,352,208,416,360⟩⟩,⟨7,1208926973665624026301559,⟨11,95,63,29,63,383,95,256,264⟩⟩,⟨8,1181745671712262898807,⟨11,95,63,29,63,127,223,128,8⟩⟩]⟩
theorem node1298 : UpperPrefix a [3,6,5,2,1,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,2,1,8,4] 30 cert1298 (by decide +kernel)

theorem node1299 : UpperPrefix a [3,6,5,2,1,8] 30 :=
  branch_upper a [3,6,5,2,1,8] 30 (by decide) (fin9_cases _
  node1297
  (invalid_upper a [3,6,5,2,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,8,3] 30 (by decide +kernel))
  node1298
  (invalid_upper a [3,6,5,2,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,8,8] 30 (by decide +kernel)))

theorem node1300 : UpperPrefix a [3,6,5,2,1] 30 :=
  branch_upper a [3,6,5,2,1] 30 (by decide) (fin9_cases _
  node1294
  (invalid_upper a [3,6,5,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,3] 30 (by decide +kernel))
  node1295
  (invalid_upper a [3,6,5,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,1,6] 30 (by decide +kernel))
  node1296
  node1299)

def cert1301 : Leaf := ⟨⟨212,152,0,226,74,154,282,90,210⟩,[(2,5)],[(5,2,3),(2,3,0),(0,5,2)],⟨11,70,37,28,176,97,466,402,282⟩,⟨11,70,37,28,176,97,192,384,264⟩,[⟨8,1181747995804446803063,⟨47,127,47,29,191,127,255,128,8⟩⟩]⟩
theorem node1301 : UpperPrefix a [3,6,5,2,7,0] 30 :=
  Boolean.leaf_sound a [3,6,5,2,7,0] 30 cert1301 (by decide +kernel)

def cert1302 : Leaf := ⟨⟨148,153,154,161,9,0,281,25,145⟩,[(5,1)],[(6,1,5),(5,2,3),(2,3,0),(1,5,2)],⟨11,70,37,28,176,98,465,401,281⟩,⟨11,70,37,28,176,98,192,384,264⟩,[⟨8,1181747995804446803063,⟨47,127,47,29,191,127,255,128,8⟩⟩]⟩
theorem node1302 : UpperPrefix a [3,6,5,2,7,1] 30 :=
  Boolean.leaf_sound a [3,6,5,2,7,1] 30 cert1302 (by decide +kernel)

def cert1303 : Leaf := ⟨⟨4,9,90,35,11,139,267,11,3⟩,[],[(5,2,3),(2,3,0),(7,4,5)],⟨11,70,37,28,176,112,451,387,267⟩,⟨11,70,37,28,176,112,192,384,264⟩,[⟨8,1181747995804446803063,⟨47,127,47,29,191,127,255,128,8⟩⟩,⟨4,1255094796579691966766345,⟨459,198,487,463,160,96,192,449,459⟩⟩,⟨6,1224301181927342262453251,⟨395,415,445,28,176,48,128,384,264⟩⟩]⟩
theorem node1303 : UpperPrefix a [3,6,5,2,7,4] 30 :=
  Boolean.leaf_sound a [3,6,5,2,7,4] 30 cert1303 (by decide +kernel)

def cert1304 : Local := ⟨⟨212,153,216,224,328,152,26,88,208⟩,[],[(5,2,3),(2,3,0),(8,5,4),(0,6,1),(1,7,6)]⟩
theorem node1304 : UpperPrefix a [3,6,5,2,7,8,0,1] 30 :=
  local_sound a [3,6,5,2,7,8,0,1] 30 cert1304 (by decide +kernel)

def cert1305 : Leaf := ⟨⟨84,25,90,98,330,26,26,74,82⟩,[],[(5,2,3),(2,3,0),(8,5,4),(0,6,1)],⟨11,70,37,28,176,352,193,400,266⟩,⟨11,70,37,28,176,352,193,400,264⟩,[⟨7,1591438661097763452535889,⟨303,359,295,285,319,359,367,285,264⟩⟩]⟩
theorem node1305 : UpperPrefix a [3,6,5,2,7,8,0,4] 30 :=
  Boolean.leaf_sound a [3,6,5,2,7,8,0,4] 30 cert1305 (by decide +kernel)

theorem node1306 : UpperPrefix a [3,6,5,2,7,8,0] 30 :=
  branch_upper a [3,6,5,2,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,2,7,8,0,0] 30 (by decide +kernel))
  node1304
  (invalid_upper a [3,6,5,2,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,0,3] 30 (by decide +kernel))
  node1305
  (invalid_upper a [3,6,5,2,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,0,8] 30 (by decide +kernel)))

def cert1307 : Leaf := ⟨⟨148,153,152,161,265,153,25,25,145⟩,[],[(5,2,3),(2,3,0),(8,5,4)],⟨11,70,37,28,176,352,194,401,281⟩,⟨11,70,37,28,176,352,194,384,264⟩,[⟨1,1233765514633632952877057,⟨445,508,445,412,176,368,248,384,264⟩⟩,⟨6,1389906826851275236181059,⟨395,415,445,412,444,445,395,384,264⟩⟩]⟩
theorem node1307 : UpperPrefix a [3,6,5,2,7,8,1] 30 :=
  Boolean.leaf_sound a [3,6,5,2,7,8,1] 30 cert1307 (by decide +kernel)

def cert1308 : Leaf := ⟨⟨20,25,90,35,267,27,0,27,19⟩,[(6,4)],[(5,2,3),(2,3,0),(7,4,6),(8,5,4)],⟨11,70,37,28,176,352,208,387,267⟩,⟨11,70,37,28,176,352,208,384,264⟩,[⟨6,1224301181927342262453251,⟨395,415,445,28,176,288,144,384,264⟩⟩]⟩
theorem node1308 : UpperPrefix a [3,6,5,2,7,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,2,7,8,4] 30 cert1308 (by decide +kernel)

theorem node1309 : UpperPrefix a [3,6,5,2,7,8] 30 :=
  branch_upper a [3,6,5,2,7,8] 30 (by decide) (fin9_cases _
  node1306
  node1307
  (invalid_upper a [3,6,5,2,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,3] 30 (by decide +kernel))
  node1308
  (invalid_upper a [3,6,5,2,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,8,8] 30 (by decide +kernel)))

theorem node1310 : UpperPrefix a [3,6,5,2,7] 30 :=
  branch_upper a [3,6,5,2,7] 30 (by decide) (fin9_cases _
  node1301
  node1302
  (invalid_upper a [3,6,5,2,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,3] 30 (by decide +kernel))
  node1303
  (invalid_upper a [3,6,5,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,7,7] 30 (by decide +kernel))
  node1309)

def cert1311 : Leaf := ⟨⟨340,272,0,354,202,402,274,82,210⟩,[(2,5)],[(5,2,3),(2,3,0),(0,5,2)],⟨11,70,37,28,304,97,210,402,410⟩,⟨11,70,37,28,304,97,192,384,264⟩,[⟨3,1210255571617188897125889,⟨103,70,39,214,502,103,192,384,322⟩⟩,⟨7,1208926973663136434897937,⟨11,70,39,29,319,103,64,256,264⟩⟩]⟩
theorem node1311 : UpperPrefix a [3,6,5,2,8,0] 30 :=
  Boolean.leaf_sound a [3,6,5,2,8,0] 30 cert1311 (by decide +kernel)

def cert1312 : Leaf := ⟨⟨404,409,402,417,137,0,281,25,145⟩,[(5,1)],[(6,1,5),(5,2,3),(2,3,0),(1,5,2)],⟨11,70,37,28,304,98,209,401,409⟩,⟨11,70,37,28,304,98,192,384,264⟩,[⟨3,1210107565354219356816385,⟨39,102,37,20,304,98,192,384,256⟩⟩]⟩
theorem node1312 : UpperPrefix a [3,6,5,2,8,1] 30 :=
  Boolean.leaf_sound a [3,6,5,2,8,1] 30 cert1312 (by decide +kernel)

def cert1313 : Leaf := ⟨⟨4,9,74,35,139,395,267,11,131⟩,[],[(5,2,3),(2,3,0)],⟨11,70,37,28,304,112,195,387,395⟩,⟨11,70,37,28,304,112,192,384,264⟩,[⟨4,1255242658762657799109897,⟨459,198,487,463,487,230,192,449,459⟩⟩,⟨6,1224301181927342262453251,⟨395,415,445,28,304,48,128,384,264⟩⟩,⟨7,1208926973663140729865269,⟨11,71,47,29,319,127,64,256,264⟩⟩,⟨8,1181745669228966462517,⟨11,71,47,29,63,127,192,128,8⟩⟩]⟩
theorem node1313 : UpperPrefix a [3,6,5,2,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,2,8,4] 30 cert1313 (by decide +kernel)

def cert1314 : Leaf := ⟨⟨84,25,90,98,74,0,282,90,82⟩,[(5,6)],[(5,2,3),(2,3,0),(7,5,5),(0,6,1)],⟨11,70,37,28,304,224,193,402,282⟩,⟨11,70,37,28,304,224,193,384,264⟩,[⟨8,1181747921024493601809,⟨11,102,39,29,63,230,231,128,8⟩⟩]⟩
theorem node1314 : UpperPrefix a [3,6,5,2,8,7,0] 30 :=
  Boolean.leaf_sound a [3,6,5,2,8,7,0] 30 cert1314 (by decide +kernel)

def cert1315 : Leaf := ⟨⟨276,281,282,291,11,0,281,27,19⟩,[(5,6)],[(5,2,3),(2,3,0),(7,5,5)],⟨11,70,37,28,304,224,194,401,281⟩,⟨11,70,37,28,304,224,194,384,264⟩,[⟨6,1389906826851275236181059,⟨395,415,445,412,444,445,395,384,264⟩⟩]⟩
theorem node1315 : UpperPrefix a [3,6,5,2,8,7,1] 30 :=
  Boolean.leaf_sound a [3,6,5,2,8,7,1] 30 cert1315 (by decide +kernel)

def cert1316 : Leaf := ⟨⟨20,25,90,35,11,0,267,27,19⟩,[(5,6)],[(5,2,3),(2,3,0),(8,4,6),(7,5,5)],⟨11,70,37,28,304,224,208,387,267⟩,⟨11,70,37,28,304,224,208,384,264⟩,[⟨6,1224301181927342262453251,⟨395,415,445,28,304,160,144,384,264⟩⟩]⟩
theorem node1316 : UpperPrefix a [3,6,5,2,8,7,4] 30 :=
  Boolean.leaf_sound a [3,6,5,2,8,7,4] 30 cert1316 (by decide +kernel)

theorem node1317 : UpperPrefix a [3,6,5,2,8,7] 30 :=
  branch_upper a [3,6,5,2,8,7] 30 (by decide) (fin9_cases _
  node1314
  node1315
  (invalid_upper a [3,6,5,2,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,8,7,3] 30 (by decide +kernel))
  node1316
  (invalid_upper a [3,6,5,2,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,8,7,8] 30 (by decide +kernel)))

theorem node1318 : UpperPrefix a [3,6,5,2,8] 30 :=
  branch_upper a [3,6,5,2,8] 30 (by decide) (fin9_cases _
  node1311
  node1312
  (invalid_upper a [3,6,5,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,8,3] 30 (by decide +kernel))
  node1313
  (invalid_upper a [3,6,5,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,8,6] 30 (by decide +kernel))
  node1317
  (invalid_upper a [3,6,5,2,8,8] 30 (by decide +kernel)))

theorem node1319 : UpperPrefix a [3,6,5,2] 30 :=
  branch_upper a [3,6,5,2] 30 (by decide) (fin9_cases _
  node1293
  node1300
  (invalid_upper a [3,6,5,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,2,6] 30 (by decide +kernel))
  node1310
  node1318)

def cert1320 : Leaf := ⟨⟨180,185,0,37,0,0,317,61,181⟩,[(2,4),(4,2),(5,1)],[(6,1,5),(1,5,2),(1,5,4)],⟨11,70,37,152,49,98,468,404,284⟩,⟨11,70,37,152,49,98,192,384,264⟩,[⟨8,1181747998477795509347,⟨63,127,55,156,55,127,255,128,8⟩⟩]⟩
theorem node1320 : UpperPrefix a [3,6,5,7,0,1] 30 :=
  Boolean.leaf_sound a [3,6,5,7,0,1] 30 cert1320 (by decide +kernel)

def cert1321 : Leaf := ⟨⟨496,0,0,355,0,0,315,123,243⟩,[(1,5),(2,4),(4,2),(5,1)],[],⟨11,70,37,152,49,100,466,402,282⟩,⟨11,70,37,152,49,100,192,384,264⟩,[⟨2,1219570781022736850355203,⟨459,475,49,152,49,112,192,384,264⟩⟩]⟩
theorem node1321 : UpperPrefix a [3,6,5,7,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,0,2] 30 cert1321 (by decide +kernel)

def cert1322 : Leaf := ⟨⟨164,41,0,39,0,15,303,47,39⟩,[(2,4),(4,2)],[],⟨11,70,37,152,49,112,454,390,270⟩,⟨11,70,37,152,49,112,192,384,264⟩,[⟨4,1247960428237192254477577,⟨459,70,39,463,39,102,192,385,459⟩⟩,⟨6,1219569592072435229787139,⟨395,415,53,156,53,52,128,384,264⟩⟩,⟨8,1181747998477795509347,⟨63,127,55,156,55,127,255,128,8⟩⟩,⟨7,1213649340216716266062849,⟨319,118,311,28,311,118,64,256,264⟩⟩]⟩
theorem node1322 : UpperPrefix a [3,6,5,7,0,4] 30 :=
  Boolean.leaf_sound a [3,6,5,7,0,4] 30 cert1322 (by decide +kernel)

def cert1323 : Leaf := ⟨⟨420,417,0,293,0,133,293,61,181⟩,[(2,4),(4,2)],[],⟨11,70,37,152,49,352,194,404,284⟩,⟨11,70,37,152,49,352,194,384,264⟩,[⟨1,1356786853108468432502785,⟨445,508,445,412,445,352,488,384,392⟩⟩,⟨4,1210110028751748461745929,⟨79,70,39,239,39,359,230,487,367⟩⟩,⟨6,1503464983369031240123459,⟨395,415,445,412,445,445,395,384,392⟩⟩,⟨3,1210107718406512825078785,⟨67,86,53,214,53,352,194,416,354⟩⟩]⟩
theorem node1323 : UpperPrefix a [3,6,5,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,6,5,7,0,8,1] 30 cert1323 (by decide +kernel)

def cert1324 : Leaf := ⟨⟨432,0,0,291,0,155,315,59,179⟩,[(1,6),(2,4),(4,2)],[(2,6,1)],⟨11,70,37,152,49,352,196,402,282⟩,⟨11,70,37,152,49,352,196,384,264⟩,[⟨6,1219569592072443819721731,⟨395,415,53,156,53,296,156,384,264⟩⟩]⟩
theorem node1324 : UpperPrefix a [3,6,5,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,0,8,2] 30 cert1324 (by decide +kernel)

def cert1325 : Leaf := ⟨⟨500,441,0,0,0,158,0,126,246⟩,[(2,4),(3,6),(4,2),(6,3)],[],⟨11,70,37,152,49,352,208,390,270⟩,⟨11,70,37,152,49,352,208,384,264⟩,[⟨0,1219570898221613722895360,⟨490,494,36,216,48,360,216,416,360⟩⟩]⟩
theorem node1325 : UpperPrefix a [3,6,5,7,0,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,7,0,8,4] 30 cert1325 (by decide +kernel)

theorem node1326 : UpperPrefix a [3,6,5,7,0,8] 30 :=
  branch_upper a [3,6,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,7,0,8,0] 30 (by decide +kernel))
  node1323
  node1324
  (invalid_upper a [3,6,5,7,0,8,3] 30 (by decide +kernel))
  node1325
  (invalid_upper a [3,6,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,0,8,8] 30 (by decide +kernel)))

theorem node1327 : UpperPrefix a [3,6,5,7,0] 30 :=
  branch_upper a [3,6,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,7,0,0] 30 (by decide +kernel))
  node1320
  node1321
  (invalid_upper a [3,6,5,7,0,3] 30 (by decide +kernel))
  node1322
  (invalid_upper a [3,6,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,0,7] 30 (by decide +kernel))
  node1326)

def cert1328 : Leaf := ⟨⟨180,176,0,36,196,158,316,60,180⟩,[(2,5)],[(6,1,4),(0,5,2)],⟨11,70,37,152,50,97,468,404,284⟩,⟨11,70,37,152,50,97,192,384,264⟩,[⟨8,1181747998477795509347,⟨63,127,55,156,55,127,255,128,8⟩⟩,⟨1,1285813291192733993533441,⟨9,68,37,472,508,101,192,384,264⟩⟩,⟨3,1210107565286324521944065,⟨3,86,55,144,54,119,192,384,256⟩⟩]⟩
theorem node1328 : UpperPrefix a [3,6,5,7,1,0] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,0] 30 cert1328 (by decide +kernel)

def cert1329 : Leaf := ⟨⟨400,0,410,259,461,0,283,27,147⟩,[(1,5),(5,1)],[(6,1,4),(2,5,4)],⟨11,70,37,152,50,100,465,401,281⟩,⟨11,70,37,152,50,100,192,384,264⟩,[⟨5,1323666153021274154091537,⟨459,70,7,473,475,70,192,384,456⟩⟩]⟩
theorem node1329 : UpperPrefix a [3,6,5,7,1,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,2] 30 cert1329 (by decide +kernel)

def cert1330 : Leaf := ⟨⟨176,57,26,34,72,10,62,62,54⟩,[],[(6,1,4),(0,6,1)],⟨11,70,37,152,50,112,193,388,268⟩,⟨11,70,37,152,50,112,193,384,264⟩,[⟨8,1184211811088633681899,⟨127,127,55,255,55,127,255,255,127⟩⟩,⟨7,1213649342475250601083905,⟨319,118,311,24,50,118,375,256,264⟩⟩,⟨2,1210107567606234991297539,⟨59,123,49,152,51,120,249,384,264⟩⟩]⟩
theorem node1330 : UpperPrefix a [3,6,5,7,1,4,0] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,4,0] 30 cert1330 (by decide +kernel)

def cert1331 : Leaf := ⟨⟨144,0,154,3,201,139,27,27,147⟩,[(1,6)],[(6,1,4),(2,6,1)],⟨11,70,37,152,50,112,196,385,265⟩,⟨11,70,37,152,50,112,196,384,264⟩,[⟨8,1184211811088633681899,⟨127,127,55,255,55,127,255,255,127⟩⟩,⟨5,1499343395948078193216565,⟨459,455,463,409,475,475,455,384,392⟩⟩]⟩
theorem node1331 : UpperPrefix a [3,6,5,7,1,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,4,2] 30 cert1331 (by decide +kernel)

def cert1332 : Leaf := ⟨⟨180,185,16,39,69,5,0,61,53⟩,[(6,7)],[(6,1,4),(8,6,6)],⟨11,70,37,152,50,112,448,389,269⟩,⟨11,70,37,152,50,112,448,384,264⟩,[⟨1,1214878444823382343286785,⟨493,196,485,248,48,112,448,448,296⟩⟩,⟨7,1213649340216578822898689,⟨319,118,309,24,50,112,320,256,264⟩⟩,⟨3,1210109871478909705651201,⟨55,118,53,240,50,112,448,448,288⟩⟩]⟩
theorem node1332 : UpperPrefix a [3,6,5,7,1,4,8] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,4,8] 30 cert1332 (by decide +kernel)

theorem node1333 : UpperPrefix a [3,6,5,7,1,4] 30 :=
  branch_upper a [3,6,5,7,1,4] 30 (by decide) (fin9_cases _
  node1330
  (invalid_upper a [3,6,5,7,1,4,1] 30 (by decide +kernel))
  node1331
  (invalid_upper a [3,6,5,7,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,4,7] 30 (by decide +kernel))
  node1332)

def cert1334 : Leaf := ⟨⟨420,417,384,292,452,132,292,32,180⟩,[],[(6,1,4),(0,6,1)],⟨11,70,37,152,50,352,193,388,280⟩,⟨11,70,37,152,50,352,193,388,264⟩,[⟨1,1323748826760718090240001,⟨493,68,229,440,440,484,229,484,264⟩⟩,⟨3,1210402789766441443904513,⟨19,86,247,178,178,502,247,502,272⟩⟩,⟨4,1212771620102727418511113,⟨79,70,231,239,230,487,231,487,495⟩⟩]⟩
theorem node1334 : UpperPrefix a [3,6,5,7,1,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,8,0,2] 30 cert1334 (by decide +kernel)

def cert1335 : Leaf := ⟨⟨420,417,394,0,452,134,294,38,162⟩,[(3,7)],[(6,1,4),(0,6,1),(4,7,3)],⟨11,70,37,152,50,352,193,400,268⟩,⟨11,70,37,152,50,352,193,400,268⟩,[⟨3,1212763977524120260840449,⟨3,86,247,144,178,498,209,434,502⟩⟩]⟩
theorem node1335 : UpperPrefix a [3,6,5,7,1,8,0,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,8,0,4,2] 30 cert1335 (by decide +kernel)

theorem node1336 : UpperPrefix a [3,6,5,7,1,8,0,4] 30 :=
  branch_upper a [3,6,5,7,1,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,7,1,8,0,4,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,4,1] 30 (by decide +kernel))
  node1335
  (invalid_upper a [3,6,5,7,1,8,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,4,8] 30 (by decide +kernel)))

theorem node1337 : UpperPrefix a [3,6,5,7,1,8,0] 30 :=
  branch_upper a [3,6,5,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,1] 30 (by decide +kernel))
  node1334
  (invalid_upper a [3,6,5,7,1,8,0,3] 30 (by decide +kernel))
  node1336
  (invalid_upper a [3,6,5,7,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,0,8] 30 (by decide +kernel)))

def cert1338 : Leaf := ⟨⟨160,0,138,35,201,139,43,59,179⟩,[(1,6)],[(6,1,4),(2,6,1)],⟨11,70,37,152,50,352,196,401,281⟩,⟨11,70,37,152,50,352,196,384,264⟩,[⟨8,1181889786893091001707,⟨75,95,55,223,55,127,223,129,75⟩⟩,⟨4,1210110028751748457551625,⟨79,70,39,239,38,359,230,487,367⟩⟩]⟩
theorem node1338 : UpperPrefix a [3,6,5,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,8,2] 30 cert1338 (by decide +kernel)

def cert1339 : Leaf := ⟨⟨148,185,152,0,205,157,0,29,149⟩,[(3,6),(6,3)],[(6,1,4)],⟨11,70,37,152,50,352,208,389,269⟩,⟨11,70,37,152,50,352,208,384,264⟩,[⟨1,1214876201784485898092545,⟨493,204,421,216,48,360,216,416,360⟩⟩,⟨8,1181889786893091001707,⟨75,95,55,223,55,127,223,129,75⟩⟩,⟨5,1219571176213339744240659,⟨459,463,5,217,475,328,217,384,328⟩⟩]⟩
theorem node1339 : UpperPrefix a [3,6,5,7,1,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,7,1,8,4] 30 cert1339 (by decide +kernel)

theorem node1340 : UpperPrefix a [3,6,5,7,1,8] 30 :=
  branch_upper a [3,6,5,7,1,8] 30 (by decide) (fin9_cases _
  node1337
  (invalid_upper a [3,6,5,7,1,8,1] 30 (by decide +kernel))
  node1338
  (invalid_upper a [3,6,5,7,1,8,3] 30 (by decide +kernel))
  node1339
  (invalid_upper a [3,6,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,8,8] 30 (by decide +kernel)))

theorem node1341 : UpperPrefix a [3,6,5,7,1] 30 :=
  branch_upper a [3,6,5,7,1] 30 (by decide) (fin9_cases _
  node1328
  (invalid_upper a [3,6,5,7,1,1] 30 (by decide +kernel))
  node1329
  (invalid_upper a [3,6,5,7,1,3] 30 (by decide +kernel))
  node1333
  (invalid_upper a [3,6,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,1,7] 30 (by decide +kernel))
  node1340)

def cert1342 : Leaf := ⟨⟨404,408,0,262,0,414,286,30,150⟩,[(2,5),(4,2)],[(5,2,4),(0,5,2),(0,5,4)],⟨11,70,37,152,52,97,466,402,282⟩,⟨11,70,37,152,52,97,192,384,264⟩,[⟨6,1219569592074634257236995,⟨395,415,53,152,52,53,128,384,264⟩⟩]⟩
theorem node1342 : UpperPrefix a [3,6,5,7,2,0] 30 :=
  Boolean.leaf_sound a [3,6,5,7,2,0] 30 cert1342 (by decide +kernel)

def cert1343 : Local := ⟨⟨404,409,410,261,0,0,285,29,149⟩,[(4,2),(5,1)],[(6,1,5),(5,2,4),(1,5,2)]⟩
theorem node1343 : UpperPrefix a [3,6,5,7,2,1] 30 :=
  local_sound a [3,6,5,7,2,1] 30 cert1343 (by decide +kernel)

#print axioms node1343
end Delivery.FiniteExclusion.Sharp3x6
