import RegularNineSharp3x6Base
import RegularNineSharp3x6C020
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert1344 : Leaf := ⟨⟨132,137,218,7,0,143,267,11,131⟩,[(4,2)],[(5,2,4)],⟨11,70,37,152,52,112,451,387,267⟩,⟨11,70,37,152,52,112,192,384,264⟩,[⟨4,1252729001652238716775433,⟨459,198,487,459,230,98,192,384,457⟩⟩,⟨8,1181747998477795509347,⟨63,127,55,156,55,127,255,128,8⟩⟩,⟨6,1224301181927342262453251,⟨395,415,445,152,60,48,128,384,264⟩⟩,⟨2,1214839173153156694541313,⟨459,66,481,152,48,112,192,384,264⟩⟩]⟩
theorem node1344 : UpperPrefix a [3,6,5,7,2,4] 30 :=
  Boolean.leaf_sound a [3,6,5,7,2,4] 30 cert1344 (by decide +kernel)

def cert1345 : Leaf := ⟨⟨388,265,330,262,0,14,270,30,22⟩,[(4,2)],[(5,2,4),(0,6,1)],⟨11,70,37,152,52,352,193,402,282⟩,⟨11,70,37,152,52,352,193,384,264⟩,[⟨4,1210110028751748474328841,⟨79,70,39,239,38,359,231,487,367⟩⟩,⟨6,1219569592072435225592835,⟨395,415,53,152,52,288,129,384,264⟩⟩,⟨7,1213649342404813137167361,⟨283,118,311,24,54,374,375,256,264⟩⟩]⟩
theorem node1345 : UpperPrefix a [3,6,5,7,2,8,0] 30 :=
  Boolean.leaf_sound a [3,6,5,7,2,8,0] 30 cert1345 (by decide +kernel)

def cert1346 : Leaf := ⟨⟨388,393,392,261,0,141,269,29,149⟩,[(4,2)],[(5,2,4)],⟨11,70,37,152,52,352,194,401,281⟩,⟨11,70,37,152,52,352,194,384,264⟩,[⟨1,1233765514629245643784193,⟨445,508,445,152,444,360,248,384,264⟩⟩,⟨4,1210110028751748457551625,⟨79,70,39,239,38,359,230,487,367⟩⟩,⟨6,1389906826851275236181059,⟨395,415,445,152,444,445,395,384,264⟩⟩]⟩
theorem node1346 : UpperPrefix a [3,6,5,7,2,8,1] 30 :=
  Boolean.leaf_sound a [3,6,5,7,2,8,1] 30 cert1346 (by decide +kernel)

def cert1347 : Leaf := ⟨⟨464,409,474,0,0,155,0,91,211⟩,[(3,6),(4,2),(6,3)],[(5,2,4)],⟨11,70,37,152,52,352,208,387,267⟩,⟨11,70,37,152,52,352,208,384,264⟩,[⟨2,1224302488076520221836291,⟨491,491,417,216,48,360,216,416,360⟩⟩]⟩
theorem node1347 : UpperPrefix a [3,6,5,7,2,8,4] 30 :=
  Boolean.leaf_sound a [3,6,5,7,2,8,4] 30 cert1347 (by decide +kernel)

theorem node1348 : UpperPrefix a [3,6,5,7,2,8] 30 :=
  branch_upper a [3,6,5,7,2,8] 30 (by decide) (fin9_cases _
  node1345
  node1346
  (invalid_upper a [3,6,5,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,2,8,3] 30 (by decide +kernel))
  node1347
  (invalid_upper a [3,6,5,7,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,2,8,8] 30 (by decide +kernel)))

theorem node1349 : UpperPrefix a [3,6,5,7,2] 30 :=
  branch_upper a [3,6,5,7,2] 30 (by decide) (fin9_cases _
  node1342
  node1343
  (invalid_upper a [3,6,5,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,2,3] 30 (by decide +kernel))
  node1344
  (invalid_upper a [3,6,5,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,2,7] 30 (by decide +kernel))
  node1348)

def cert1350 : Leaf := ⟨⟨180,176,0,292,140,150,52,52,180⟩,[(2,5)],[(8,4,3),(0,5,2),(1,6,5)],⟨11,70,37,152,304,97,194,404,284⟩,⟨11,70,37,152,304,97,194,384,264⟩,[⟨6,1465612264529779236013123,⟨395,415,445,408,444,445,395,384,264⟩⟩,⟨3,1210255571617188897121793,⟨103,70,39,210,502,103,194,384,320⟩⟩]⟩
theorem node1350 : UpperPrefix a [3,6,5,7,8,0,1] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,0,1] 30 cert1350 (by decide +kernel)

def cert1351 : Local := ⟨⟨240,0,0,354,202,154,58,122,242⟩,[(1,6),(2,5)],[(8,4,3),(0,5,2),(2,6,1)]⟩
theorem node1351 : UpperPrefix a [3,6,5,7,8,0,2] 30 :=
  local_sound a [3,6,5,7,8,0,2] 30 cert1351 (by decide +kernel)

def cert1352 : Leaf := ⟨⟨244,176,0,0,206,150,0,118,246⟩,[(2,5),(3,6),(6,3)],[(8,4,3),(8,4,6),(0,5,2)],⟨11,70,37,152,304,97,208,390,270⟩,⟨11,70,37,152,304,97,208,384,264⟩,[⟨3,1210255571617188897121793,⟨103,70,39,210,502,103,210,384,320⟩⟩]⟩
theorem node1352 : UpperPrefix a [3,6,5,7,8,0,4] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,0,4] 30 cert1352 (by decide +kernel)

theorem node1353 : UpperPrefix a [3,6,5,7,8,0] 30 :=
  branch_upper a [3,6,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,7,8,0,0] 30 (by decide +kernel))
  node1350
  node1351
  (invalid_upper a [3,6,5,7,8,0,3] 30 (by decide +kernel))
  node1352
  (invalid_upper a [3,6,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,0,8] 30 (by decide +kernel)))

def cert1354 : Leaf := ⟨⟨164,169,138,292,140,0,44,60,180⟩,[(5,1)],[(6,1,5),(8,4,3),(1,5,2),(0,6,1)],⟨11,70,37,152,304,98,193,404,284⟩,⟨11,70,37,152,304,98,193,384,264⟩,[⟨4,1210110031390576377059081,⟨111,102,39,239,295,102,231,487,367⟩⟩]⟩
theorem node1354 : UpperPrefix a [3,6,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,1,0] 30 cert1354 (by decide +kernel)

def cert1355 : Local := ⟨⟨176,0,154,289,137,0,57,57,177⟩,[(1,6),(5,1)],[(6,1,5),(8,4,3),(1,5,2),(2,6,1),(2,6,5)]⟩
theorem node1355 : UpperPrefix a [3,6,5,7,8,1,2] 30 :=
  local_sound a [3,6,5,7,8,1,2] 30 cert1355 (by decide +kernel)

def cert1356 : Local := ⟨⟨180,185,154,0,141,0,0,61,181⟩,[(3,6),(5,1),(6,3)],[(6,1,5),(8,4,3),(8,4,6),(1,5,2)]⟩
theorem node1356 : UpperPrefix a [3,6,5,7,8,1,4] 30 :=
  local_sound a [3,6,5,7,8,1,4] 30 cert1356 (by decide +kernel)

theorem node1357 : UpperPrefix a [3,6,5,7,8,1] 30 :=
  branch_upper a [3,6,5,7,8,1] 30 (by decide) (fin9_cases _
  node1354
  (invalid_upper a [3,6,5,7,8,1,1] 30 (by decide +kernel))
  node1355
  (invalid_upper a [3,6,5,7,8,1,3] 30 (by decide +kernel))
  node1356
  (invalid_upper a [3,6,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,1,8] 30 (by decide +kernel)))

def cert1358 : Leaf := ⟨⟨196,0,202,326,206,0,14,94,214⟩,[(1,5),(5,1)],[(8,4,3),(0,6,1),(0,6,5)],⟨11,70,37,152,304,100,193,402,282⟩,⟨11,70,37,152,304,100,193,384,264⟩,[⟨5,1285813434182022154175505,⟨75,70,7,473,475,70,193,384,328⟩⟩,⟨4,1210110031390576377059081,⟨111,102,39,239,295,102,231,487,367⟩⟩]⟩
theorem node1358 : UpperPrefix a [3,6,5,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,2,0] 30 cert1358 (by decide +kernel)

def cert1359 : Leaf := ⟨⟨176,0,154,291,139,0,57,59,179⟩,[(1,5),(5,1)],[(8,4,3)],⟨11,70,37,152,304,100,194,401,281⟩,⟨11,70,37,152,304,100,194,384,264⟩,[⟨2,1389908033815975362036803,⟨459,475,505,152,440,505,459,384,264⟩⟩,⟨6,1389906826851275236181059,⟨395,415,445,152,444,445,395,384,264⟩⟩]⟩
theorem node1359 : UpperPrefix a [3,6,5,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,2,1] 30 cert1359 (by decide +kernel)

def cert1360 : Local := ⟨⟨244,0,218,0,207,0,0,127,247⟩,[(1,5),(3,6),(5,1),(6,3)],[(8,4,3),(8,4,6)]⟩
theorem node1360 : UpperPrefix a [3,6,5,7,8,2,4] 30 :=
  local_sound a [3,6,5,7,8,2,4] 30 cert1360 (by decide +kernel)

theorem node1361 : UpperPrefix a [3,6,5,7,8,2] 30 :=
  branch_upper a [3,6,5,7,8,2] 30 (by decide) (fin9_cases _
  node1358
  node1359
  (invalid_upper a [3,6,5,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,2,3] 30 (by decide +kernel))
  node1360
  (invalid_upper a [3,6,5,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,2,8] 30 (by decide +kernel)))

def cert1362 : Leaf := ⟨⟨224,169,200,352,200,136,42,108,228⟩,[],[(8,4,3),(0,6,1),(1,7,6)],⟨11,70,37,152,304,112,193,386,268⟩,⟨11,70,37,152,304,112,193,386,264⟩,[⟨4,1250485704634649948486921,⟨459,70,231,463,487,230,193,451,459⟩⟩,⟨2,1210110031312536695997571,⟨107,107,33,249,304,120,249,507,376⟩⟩]⟩
theorem node1362 : UpperPrefix a [3,6,5,7,8,4,0,1] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,4,0,1] 30 cert1362 (by decide +kernel)

def cert1363 : Leaf := ⟨⟨192,137,202,354,202,138,14,74,194⟩,[],[(8,4,3),(0,6,1)],⟨11,70,37,152,304,112,193,388,266⟩,⟨11,70,37,152,304,112,193,388,264⟩,[⟨4,1252874557992195335486729,⟨459,198,487,463,487,230,451,455,459⟩⟩,⟨2,1224274667059534031225859,⟨315,379,305,152,304,120,505,408,264⟩⟩,⟨5,1252645972164708119153673,⟨331,198,455,475,272,80,451,454,329⟩⟩]⟩
theorem node1363 : UpperPrefix a [3,6,5,7,8,4,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,4,0,2] 30 cert1363 (by decide +kernel)

theorem node1364 : UpperPrefix a [3,6,5,7,8,4,0] 30 :=
  branch_upper a [3,6,5,7,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,7,8,4,0,0] 30 (by decide +kernel))
  node1362
  node1363
  (invalid_upper a [3,6,5,7,8,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,0,8] 30 (by decide +kernel)))

def cert1365 : Leaf := ⟨⟨164,169,8,293,13,13,45,45,37⟩,[],[(8,4,3)],⟨11,70,37,152,304,112,194,389,269⟩,⟨11,70,37,152,304,112,194,384,264⟩,[⟨1,1233765516881043309985793,⟨445,508,445,152,304,120,248,384,264⟩⟩,⟨4,1248113496581327322905865,⟨459,70,103,463,487,230,194,449,459⟩⟩,⟨6,1389906826851275236181059,⟨395,415,445,152,444,445,395,384,264⟩⟩,⟨7,1213649340216716261852161,⟨319,118,309,24,304,112,98,256,264⟩⟩]⟩
theorem node1365 : UpperPrefix a [3,6,5,7,8,4,1] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,4,1] 30 cert1365 (by decide +kernel)

def cert1366 : Leaf := ⟨⟨192,0,202,323,203,139,11,75,195⟩,[(1,6)],[(8,4,3),(2,6,1)],⟨11,70,37,152,304,112,196,387,267⟩,⟨11,70,37,152,304,112,196,384,264⟩,[⟨4,1255238641551790184660233,⟨459,198,487,463,487,230,198,385,459⟩⟩,⟨5,1385785239430322193468453,⟨459,455,463,152,409,475,455,384,264⟩⟩]⟩
theorem node1366 : UpperPrefix a [3,6,5,7,8,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,7,8,4,2] 30 cert1366 (by decide +kernel)

theorem node1367 : UpperPrefix a [3,6,5,7,8,4] 30 :=
  branch_upper a [3,6,5,7,8,4] 30 (by decide) (fin9_cases _
  node1364
  node1365
  node1366
  (invalid_upper a [3,6,5,7,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,4,8] 30 (by decide +kernel)))

theorem node1368 : UpperPrefix a [3,6,5,7,8] 30 :=
  branch_upper a [3,6,5,7,8] 30 (by decide) (fin9_cases _
  node1353
  node1357
  node1361
  (invalid_upper a [3,6,5,7,8,3] 30 (by decide +kernel))
  node1367
  (invalid_upper a [3,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,8,8] 30 (by decide +kernel)))

theorem node1369 : UpperPrefix a [3,6,5,7] 30 :=
  branch_upper a [3,6,5,7] 30 (by decide) (fin9_cases _
  node1327
  node1341
  node1349
  (invalid_upper a [3,6,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,7,7] 30 (by decide +kernel))
  node1368)

def cert1370 : Leaf := ⟨⟨436,433,0,165,0,0,309,53,181⟩,[(2,4),(4,2),(5,1)],[(6,1,5),(1,5,2),(1,5,4)],⟨11,70,37,280,49,98,212,404,412⟩,⟨11,70,37,280,49,98,192,384,264⟩,[⟨3,1210181524487990427270657,⟨247,118,119,502,119,98,192,416,482⟩⟩]⟩
theorem node1370 : UpperPrefix a [3,6,5,8,0,1] 30 :=
  Boolean.leaf_sound a [3,6,5,8,0,1] 30 cert1370 (by decide +kernel)

def cert1371 : Leaf := ⟨⟨496,0,0,227,0,0,315,123,243⟩,[(1,5),(2,4),(4,2),(5,1)],[],⟨11,70,37,280,49,100,210,402,410⟩,⟨11,70,37,280,49,100,192,384,264⟩,[⟨2,1219570781022736850355203,⟨459,475,49,280,49,112,192,384,264⟩⟩]⟩
theorem node1371 : UpperPrefix a [3,6,5,8,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,8,0,2] 30 cert1371 (by decide +kernel)

def cert1372 : Leaf := ⟨⟨420,289,0,167,0,263,295,39,167⟩,[(2,4),(4,2)],[],⟨11,70,37,280,49,112,198,390,398⟩,⟨11,70,37,280,49,112,192,384,264⟩,[⟨4,1247960428237192254477577,⟨459,70,39,463,39,102,192,385,459⟩⟩,⟨3,1210181515480791172546049,⟨247,118,119,502,119,118,192,384,482⟩⟩,⟨6,1219569592072435229787139,⟨395,415,53,284,53,52,128,384,264⟩⟩,⟨7,1208926973733846620849153,⟨63,118,55,284,55,118,64,256,264⟩⟩]⟩
theorem node1372 : UpperPrefix a [3,6,5,8,0,4] 30 :=
  Boolean.leaf_sound a [3,6,5,8,0,4] 30 cert1372 (by decide +kernel)

def cert1373 : Leaf := ⟨⟨308,305,0,39,0,0,311,55,55⟩,[(2,4),(4,2),(5,6)],[(7,5,5)],⟨11,70,37,280,49,224,214,406,286⟩,⟨11,70,37,280,49,224,192,384,264⟩,[⟨6,1219569592072435229787139,⟨395,415,53,284,53,160,128,384,264⟩⟩,⟨3,1210181525965734055001601,⟨247,118,119,502,119,224,224,416,482⟩⟩]⟩
theorem node1373 : UpperPrefix a [3,6,5,8,0,7] 30 :=
  Boolean.leaf_sound a [3,6,5,8,0,7] 30 cert1373 (by decide +kernel)

theorem node1374 : UpperPrefix a [3,6,5,8,0] 30 :=
  branch_upper a [3,6,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,8,0,0] 30 (by decide +kernel))
  node1370
  node1371
  (invalid_upper a [3,6,5,8,0,3] 30 (by decide +kernel))
  node1372
  (invalid_upper a [3,6,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,0,6] 30 (by decide +kernel))
  node1373
  (invalid_upper a [3,6,5,8,0,8] 30 (by decide +kernel)))

def cert1375 : Leaf := ⟨⟨436,32,0,164,68,414,316,60,180⟩,[(2,5)],[(6,1,4),(0,5,2)],⟨11,70,37,280,50,97,212,404,412⟩,⟨11,70,37,280,50,97,192,384,264⟩,[⟨1,1285813291192733993533441,⟨9,68,37,472,508,101,192,384,264⟩⟩,⟨3,1210107565286324521944065,⟨3,86,55,272,54,119,192,384,256⟩⟩,⟨7,1208926973665608184382465,⟨11,86,55,280,54,119,64,256,264⟩⟩,⟨8,1181745671696420979713,⟨11,86,55,24,54,119,192,128,8⟩⟩,⟨4,1210107565282752182895617,⟨11,70,39,264,38,103,192,384,264⟩⟩]⟩
theorem node1375 : UpperPrefix a [3,6,5,8,1,0] 30 :=
  Boolean.leaf_sound a [3,6,5,8,1,0] 30 cert1375 (by decide +kernel)

def cert1376 : Leaf := ⟨⟨400,0,410,131,461,0,283,27,147⟩,[(1,5),(5,1)],[(6,1,4),(2,5,4)],⟨11,70,37,280,50,100,209,401,409⟩,⟨11,70,37,280,50,100,192,384,264⟩,[⟨5,1323666153021274154091537,⟨459,70,7,473,475,70,192,384,456⟩⟩]⟩
theorem node1376 : UpperPrefix a [3,6,5,8,1,2] 30 :=
  Boolean.leaf_sound a [3,6,5,8,1,2] 30 cert1376 (by decide +kernel)

def cert1377 : Leaf := ⟨⟨272,281,282,2,328,266,286,26,146⟩,[],[(6,1,4),(0,6,1)],⟨11,70,37,280,50,112,193,388,392⟩,⟨11,70,37,280,50,112,193,388,264⟩,[⟨5,1309335320704616831716373,⟨459,455,463,345,475,345,451,455,264⟩⟩,⟨7,1208926975992398144652353,⟨63,119,55,280,54,119,127,284,264⟩⟩,⟨2,1512339022509896848376851,⟨59,379,57,281,59,377,505,384,264⟩⟩]⟩
theorem node1377 : UpperPrefix a [3,6,5,8,1,4,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,8,1,4,0,2] 30 cert1377 (by decide +kernel)

theorem node1378 : UpperPrefix a [3,6,5,8,1,4,0] 30 :=
  branch_upper a [3,6,5,8,1,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,8,1,4,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,0,1] 30 (by decide +kernel))
  node1377
  (invalid_upper a [3,6,5,8,1,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,0,8] 30 (by decide +kernel)))

def cert1379 : Leaf := ⟨⟨400,0,410,131,457,393,281,25,145⟩,[(1,6)],[(6,1,4),(2,6,1)],⟨11,70,37,280,50,112,196,385,393⟩,⟨11,70,37,280,50,112,196,384,264⟩,[⟨5,1499343395948078193216565,⟨459,455,463,409,475,475,455,384,392⟩⟩,⟨1,1214876157276246615523329,⟨457,196,485,312,112,112,196,384,264⟩⟩]⟩
theorem node1379 : UpperPrefix a [3,6,5,8,1,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,8,1,4,2] 30 cert1379 (by decide +kernel)

theorem node1380 : UpperPrefix a [3,6,5,8,1,4] 30 :=
  branch_upper a [3,6,5,8,1,4] 30 (by decide) (fin9_cases _
  node1378
  (invalid_upper a [3,6,5,8,1,4,1] 30 (by decide +kernel))
  node1379
  (invalid_upper a [3,6,5,8,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,4,8] 30 (by decide +kernel)))

def cert1381 : Leaf := ⟨⟨308,49,18,38,68,0,318,62,54⟩,[(5,6)],[(6,1,4),(7,5,5),(0,6,1)],⟨11,70,37,280,50,224,193,404,284⟩,⟨11,70,37,280,50,224,193,384,264⟩,[⟨3,1210107567542659829515265,⟨19,118,55,272,50,246,247,384,256⟩⟩,⟨8,1181747928031728550913,⟨27,118,55,24,50,246,247,128,8⟩⟩]⟩
theorem node1381 : UpperPrefix a [3,6,5,8,1,7,0] 30 :=
  Boolean.leaf_sound a [3,6,5,8,1,7,0] 30 cert1381 (by decide +kernel)

def cert1382 : Local := ⟨⟨304,0,282,35,329,0,315,59,51⟩,[(1,6),(5,6)],[(6,1,4),(7,5,5),(2,6,1)]⟩
theorem node1382 : UpperPrefix a [3,6,5,8,1,7,2] 30 :=
  local_sound a [3,6,5,8,1,7,2] 30 cert1382 (by decide +kernel)

def cert1383 : Leaf := ⟨⟨308,313,264,39,320,0,303,45,37⟩,[(5,6)],[(6,1,4),(7,5,5)],⟨11,70,37,280,50,224,208,389,269⟩,⟨11,70,37,280,50,224,208,384,264⟩,[⟨1,1214876050949074163335169,⟨429,228,421,280,48,224,240,384,264⟩⟩,⟨4,1214876050947974651708417,⟨431,230,421,264,34,224,224,384,264⟩⟩,⟨0,1210107567535788938757120,⟨26,118,36,280,50,224,240,384,264⟩⟩,⟨2,1210107567535788937708545,⟨27,114,33,280,50,224,240,384,264⟩⟩,⟨3,1210107567535787865015297,⟨19,118,37,272,50,224,240,384,256⟩⟩]⟩
theorem node1383 : UpperPrefix a [3,6,5,8,1,7,4] 30 :=
  Boolean.leaf_sound a [3,6,5,8,1,7,4] 30 cert1383 (by decide +kernel)

theorem node1384 : UpperPrefix a [3,6,5,8,1,7] 30 :=
  branch_upper a [3,6,5,8,1,7] 30 (by decide) (fin9_cases _
  node1381
  (invalid_upper a [3,6,5,8,1,7,1] 30 (by decide +kernel))
  node1382
  (invalid_upper a [3,6,5,8,1,7,3] 30 (by decide +kernel))
  node1383
  (invalid_upper a [3,6,5,8,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,7,8] 30 (by decide +kernel)))

theorem node1385 : UpperPrefix a [3,6,5,8,1] 30 :=
  branch_upper a [3,6,5,8,1] 30 (by decide) (fin9_cases _
  node1375
  (invalid_upper a [3,6,5,8,1,1] 30 (by decide +kernel))
  node1376
  (invalid_upper a [3,6,5,8,1,3] 30 (by decide +kernel))
  node1380
  (invalid_upper a [3,6,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,1,6] 30 (by decide +kernel))
  node1384
  (invalid_upper a [3,6,5,8,1,8] 30 (by decide +kernel)))

def cert1386 : Leaf := ⟨⟨404,408,0,134,0,414,286,30,150⟩,[(2,5),(4,2)],[(5,2,4),(0,5,2),(0,5,4)],⟨11,70,37,280,52,97,210,402,410⟩,⟨11,70,37,280,52,97,192,384,264⟩,[⟨6,1219569592074634257236995,⟨395,415,53,280,52,53,128,384,264⟩⟩]⟩
theorem node1386 : UpperPrefix a [3,6,5,8,2,0] 30 :=
  Boolean.leaf_sound a [3,6,5,8,2,0] 30 cert1386 (by decide +kernel)

def cert1387 : Local := ⟨⟨404,409,410,133,0,0,285,29,149⟩,[(4,2),(5,1)],[(6,1,5),(5,2,4),(1,5,2)]⟩
theorem node1387 : UpperPrefix a [3,6,5,8,2,1] 30 :=
  local_sound a [3,6,5,8,2,1] 30 cert1387 (by decide +kernel)

def cert1388 : Leaf := ⟨⟨388,393,464,135,0,389,267,11,131⟩,[(4,2)],[(5,2,4)],⟨11,70,37,280,52,112,195,387,395⟩,⟨11,70,37,280,52,112,192,384,264⟩,[⟨4,1252729001652238716775433,⟨459,198,487,459,230,98,192,384,457⟩⟩,⟨6,1224301181927342262453251,⟨395,415,445,280,60,48,128,384,264⟩⟩,⟨2,1214839173153156694541313,⟨459,66,481,280,48,112,192,384,264⟩⟩,⟨1,1210107565354701466894337,⟨61,116,53,280,52,112,192,384,264⟩⟩,⟨3,1210107565354700393153537,⟨55,118,53,272,52,112,192,384,256⟩⟩]⟩
theorem node1388 : UpperPrefix a [3,6,5,8,2,4] 30 :=
  Boolean.leaf_sound a [3,6,5,8,2,4] 30 cert1388 (by decide +kernel)

def cert1389 : Leaf := ⟨⟨276,281,346,7,0,0,287,31,23⟩,[(4,2),(5,6)],[(5,2,4),(7,5,5)],⟨11,70,37,280,52,224,211,403,283⟩,⟨11,70,37,280,52,224,192,384,264⟩,[⟨6,1219569592072435225592835,⟨395,415,53,280,52,160,128,384,264⟩⟩]⟩
theorem node1389 : UpperPrefix a [3,6,5,8,2,7] 30 :=
  Boolean.leaf_sound a [3,6,5,8,2,7] 30 cert1389 (by decide +kernel)

theorem node1390 : UpperPrefix a [3,6,5,8,2] 30 :=
  branch_upper a [3,6,5,8,2] 30 (by decide) (fin9_cases _
  node1386
  node1387
  (invalid_upper a [3,6,5,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,2,3] 30 (by decide +kernel))
  node1388
  (invalid_upper a [3,6,5,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,2,6] 30 (by decide +kernel))
  node1389
  (invalid_upper a [3,6,5,8,2,8] 30 (by decide +kernel)))

def cert1391 : Leaf := ⟨⟨180,184,0,164,12,158,60,60,180⟩,[(2,5)],[(0,5,2),(1,6,5)],⟨11,70,37,280,176,97,194,404,284⟩,⟨11,70,37,280,176,97,194,384,264⟩,[⟨6,1465612264529779236013123,⟨395,415,445,408,444,445,395,384,264⟩⟩,⟨8,1184344540876731970825,⟨47,86,39,127,246,119,246,247,47⟩⟩]⟩
theorem node1391 : UpperPrefix a [3,6,5,8,7,0,1] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,0,1] 30 cert1391 (by decide +kernel)

def cert1392 : Leaf := ⟨⟨496,0,0,226,322,402,306,114,242⟩,[(1,6),(2,5)],[(0,5,2),(2,6,1)],⟨11,70,37,280,176,97,196,402,282⟩,⟨11,70,37,280,176,97,196,384,264⟩,[⟨3,1210181658685308746919425,⟨247,118,119,466,246,119,246,384,384⟩⟩]⟩
theorem node1392 : UpperPrefix a [3,6,5,8,7,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,0,2] 30 cert1392 (by decide +kernel)

def cert1393 : Leaf := ⟨⟨116,56,0,102,78,30,0,126,118⟩,[(2,5),(6,4)],[(7,4,6),(0,5,2)],⟨11,70,37,280,176,97,208,390,270⟩,⟨11,70,37,280,176,97,208,384,264⟩,[⟨8,1184344540876731970825,⟨47,86,39,127,246,119,246,247,47⟩⟩]⟩
theorem node1393 : UpperPrefix a [3,6,5,8,7,0,4] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,0,4] 30 cert1393 (by decide +kernel)

theorem node1394 : UpperPrefix a [3,6,5,8,7,0] 30 :=
  branch_upper a [3,6,5,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,8,7,0,0] 30 (by decide +kernel))
  node1391
  node1392
  (invalid_upper a [3,6,5,8,7,0,3] 30 (by decide +kernel))
  node1393
  (invalid_upper a [3,6,5,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,0,8] 30 (by decide +kernel)))

def cert1395 : Leaf := ⟨⟨308,313,282,36,268,0,316,60,52⟩,[(5,1)],[(6,1,5),(1,5,2),(0,6,1)],⟨11,70,37,280,176,98,193,404,284⟩,⟨11,70,37,280,176,98,193,384,264⟩,[⟨7,1322263771574176486573073,⟨303,102,39,285,319,102,103,256,264⟩⟩]⟩
theorem node1395 : UpperPrefix a [3,6,5,8,7,1,0] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,1,0] 30 cert1395 (by decide +kernel)

def cert1396 : Local := ⟨⟨432,0,410,161,265,0,313,57,177⟩,[(1,6),(5,1)],[(6,1,5),(1,5,2),(2,6,1),(2,6,5)]⟩
theorem node1396 : UpperPrefix a [3,6,5,8,7,1,2] 30 :=
  local_sound a [3,6,5,8,7,1,2] 30 cert1396 (by decide +kernel)

def cert1397 : Local := ⟨⟨308,313,282,37,269,0,0,61,53⟩,[(5,1),(6,4)],[(6,1,5),(7,4,6),(1,5,2)]⟩
theorem node1397 : UpperPrefix a [3,6,5,8,7,1,4] 30 :=
  local_sound a [3,6,5,8,7,1,4] 30 cert1397 (by decide +kernel)

theorem node1398 : UpperPrefix a [3,6,5,8,7,1] 30 :=
  branch_upper a [3,6,5,8,7,1] 30 (by decide) (fin9_cases _
  node1395
  (invalid_upper a [3,6,5,8,7,1,1] 30 (by decide +kernel))
  node1396
  (invalid_upper a [3,6,5,8,7,1,3] 30 (by decide +kernel))
  node1397
  (invalid_upper a [3,6,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,1,8] 30 (by decide +kernel)))

def cert1399 : Leaf := ⟨⟨340,0,344,70,332,0,286,94,86⟩,[(1,5),(5,1)],[(0,6,1),(0,6,5)],⟨11,70,37,280,176,100,193,402,282⟩,⟨11,70,37,280,176,100,193,384,264⟩,[⟨5,1285813434182022154175505,⟨75,70,7,473,475,70,193,384,328⟩⟩,⟨7,1284484839711219324863505,⟨47,102,39,285,319,102,103,256,264⟩⟩,⟨1,1210107567610418307530753,⟨45,116,37,280,176,116,245,384,264⟩⟩]⟩
theorem node1399 : UpperPrefix a [3,6,5,8,7,2,0] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,2,0] 30 cert1399 (by decide +kernel)

def cert1400 : Leaf := ⟨⟨432,0,408,161,265,0,313,57,177⟩,[(1,5),(5,1)],[],⟨11,70,37,280,176,100,194,401,281⟩,⟨11,70,37,280,176,100,194,384,264⟩,[⟨2,1389908033815975362036803,⟨459,475,505,280,440,505,459,384,264⟩⟩,⟨6,1389906826851275236181059,⟨395,415,445,280,444,445,395,384,264⟩⟩,⟨1,1233765514635836271099905,⟨445,508,445,280,184,508,248,384,264⟩⟩]⟩
theorem node1400 : UpperPrefix a [3,6,5,8,7,2,1] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,2,1] 30 cert1400 (by decide +kernel)

def cert1401 : Leaf := ⟨⟨368,0,346,99,331,0,0,123,115⟩,[(1,5),(5,1),(6,4)],[(7,4,6)],⟨11,70,37,280,176,100,208,387,267⟩,⟨11,70,37,280,176,100,208,384,264⟩,[⟨2,1224302731165614076855299,⟨459,475,505,344,240,120,208,384,264⟩⟩]⟩
theorem node1401 : UpperPrefix a [3,6,5,8,7,2,4] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,2,4] 30 cert1401 (by decide +kernel)

theorem node1402 : UpperPrefix a [3,6,5,8,7,2] 30 :=
  branch_upper a [3,6,5,8,7,2] 30 (by decide) (fin9_cases _
  node1399
  node1400
  (invalid_upper a [3,6,5,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,2,3] 30 (by decide +kernel))
  node1401
  (invalid_upper a [3,6,5,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,2,8] 30 (by decide +kernel)))

def cert1403 : Leaf := ⟨⟨304,313,280,32,264,392,314,60,52⟩,[],[(7,4,5),(0,6,1),(1,7,6)],⟨11,70,37,280,176,112,193,386,268⟩,⟨11,70,37,280,176,112,193,386,264⟩,[⟨6,1502920804416657776706691,⟨395,415,445,284,445,316,129,395,264⟩⟩,⟨2,1210110167040641485243521,⟨43,114,33,376,249,112,249,507,296⟩⟩]⟩
theorem node1403 : UpperPrefix a [3,6,5,8,7,4,0,1] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,4,0,1] 30 cert1403 (by decide +kernel)

def cert1404 : Leaf := ⟨⟨272,281,346,2,266,394,286,26,18⟩,[],[(7,4,5),(0,6,1)],⟨11,70,37,280,176,112,193,388,266⟩,⟨11,70,37,280,176,112,193,388,264⟩,[⟨5,1309335320704616831716373,⟨459,455,463,345,475,345,451,455,264⟩⟩,⟨2,1224274667059036083454979,⟨299,379,289,280,176,120,505,384,264⟩⟩,⟨6,1224328852043470006649859,⟨395,415,445,280,184,48,393,412,264⟩⟩]⟩
theorem node1404 : UpperPrefix a [3,6,5,8,7,4,0,2] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,4,0,2] 30 cert1404 (by decide +kernel)

theorem node1405 : UpperPrefix a [3,6,5,8,7,4,0] 30 :=
  branch_upper a [3,6,5,8,7,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,6,5,8,7,4,0,0] 30 (by decide +kernel))
  node1403
  node1404
  (invalid_upper a [3,6,5,8,7,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,6,5,8,7,4,0,8] 30 (by decide +kernel)))

def cert1406 : Leaf := ⟨⟨52,57,16,37,5,133,61,61,53⟩,[],[(7,4,5)],⟨11,70,37,280,176,112,194,389,269⟩,⟨11,70,37,280,176,112,194,384,264⟩,[⟨1,1233765516885432766562305,⟨445,508,445,280,176,112,248,384,264⟩⟩,⟨6,1389906826851275236181059,⟨395,415,445,280,444,445,395,384,264⟩⟩,⟨8,1184347425995234850057,⟨47,118,37,127,246,114,246,247,47⟩⟩,⟨3,1210107567610417217012737,⟨39,118,37,272,176,112,242,384,256⟩⟩]⟩
theorem node1406 : UpperPrefix a [3,6,5,8,7,4,1] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,4,1] 30 cert1406 (by decide +kernel)

def cert1407 : Leaf := ⟨⟨272,0,346,3,267,395,283,27,19⟩,[(1,6)],[(7,4,5),(2,6,1)],⟨11,70,37,280,176,112,196,387,267⟩,⟨11,70,37,280,176,112,196,384,264⟩,[⟨5,1385785239430322193468453,⟨459,455,463,280,409,475,455,384,264⟩⟩,⟨6,1224301181927342262453251,⟨395,415,445,280,176,48,156,384,264⟩⟩]⟩
theorem node1407 : UpperPrefix a [3,6,5,8,7,4,2] 30 :=
  Boolean.leaf_sound a [3,6,5,8,7,4,2] 30 cert1407 (by decide +kernel)

#print axioms node1407
end Delivery.FiniteExclusion.Sharp3x6
