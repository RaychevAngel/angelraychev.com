import RegularNineSharp2x7Base
import RegularNineSharp2x7C021
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
theorem node1408 : UpperPrefix a [2,5,6,1,8] 30 :=
  branch_upper a [2,5,6,1,8] 30 (by decide) (fin9_cases _
  node1402
  (invalid_upper a [2,5,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,1,8,2] 30 (by decide +kernel))
  node1403
  node1406
  (invalid_upper a [2,5,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,1,8,6] 30 (by decide +kernel))
  node1407
  (invalid_upper a [2,5,6,1,8,8] 30 (by decide +kernel)))

theorem node1409 : UpperPrefix a [2,5,6,1] 30 :=
  branch_upper a [2,5,6,1] 30 (by decide) (fin9_cases _
  node1384
  (invalid_upper a [2,5,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,1,2] 30 (by decide +kernel))
  node1391
  (invalid_upper a [2,5,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,1,6] 30 (by decide +kernel))
  node1401
  node1408)

def cert1410 : Leaf := ⟨⟨376,0,400,324,0,285,284,92,88⟩,[(1,4),(4,1)],[(7,3,2),(1,5,1),(1,5,4)],⟨7,35,76,152,49,98,472,408,284⟩,⟨7,35,76,152,49,98,192,384,260⟩,[⟨0,1323666154147174067209216,⟨6,34,460,476,508,98,192,384,260⟩⟩,⟨5,1323666153021274160366593,⟨7,3,460,476,477,66,192,384,260⟩⟩]⟩
theorem node1410 : UpperPrefix a [2,5,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,0,1] 30 cert1410 (by decide +kernel)

def cert1411 : Leaf := ⟨⟨376,0,0,359,0,0,311,119,115⟩,[(1,4),(2,5),(4,1),(5,2)],[(7,3,2),(7,3,5)],⟨7,35,76,152,49,104,466,402,278⟩,⟨7,35,76,152,49,104,192,384,260⟩,[⟨3,1215005518109129617449985,⟨471,499,68,210,499,96,192,384,260⟩⟩]⟩
theorem node1411 : UpperPrefix a [2,5,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,0,3] 30 cert1411 (by decide +kernel)

def cert1412 : Leaf := ⟨⟨104,0,163,39,0,15,303,47,43⟩,[(1,4),(4,1)],[(7,3,2)],⟨7,35,76,152,49,112,458,394,270⟩,⟨7,35,76,152,49,112,192,384,260⟩,[⟨4,1247960428237192252367881,⟨7,35,461,463,35,98,192,384,260⟩⟩,⟨8,1181748086455900761975,⟨55,55,127,155,55,127,255,155,55⟩⟩,⟨6,1215004022914061249291265,⟨415,443,12,154,443,186,128,384,260⟩⟩]⟩
theorem node1412 : UpperPrefix a [2,5,6,7,0,4] 30 :=
  Boolean.leaf_sound a [2,5,6,7,0,4] 30 cert1412 (by decide +kernel)

def cert1413 : Leaf := ⟨⟨104,0,161,101,0,29,45,125,121⟩,[(1,4),(4,1)],[(7,3,2)],⟨7,35,76,152,49,352,194,408,284⟩,⟨7,35,76,152,49,352,194,384,260⟩,[⟨1,1602903312610140649160705,⟨445,445,492,408,445,492,508,384,292⟩⟩,⟨8,1181889786755666699387,⟨23,55,77,223,55,127,223,128,4⟩⟩,⟨4,1210107709397940252451849,⟨7,35,77,207,35,352,194,384,260⟩⟩]⟩
theorem node1413 : UpperPrefix a [2,5,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,0,8,1] 30 cert1413 (by decide +kernel)

def cert1414 : Local := ⟨⟨368,0,0,359,0,23,0,119,115⟩,[(1,4),(2,6),(4,1),(6,3)],[(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node1414 : UpperPrefix a [2,5,6,7,0,8,3] 30 :=
  local_sound a [2,5,6,7,0,8,3] 30 cert1414 (by decide +kernel)

def cert1415 : Local := ⟨⟨360,0,435,0,0,15,0,111,107⟩,[(1,4),(3,6),(4,1),(6,3)],[(7,3,2),(4,6,2)]⟩
theorem node1415 : UpperPrefix a [2,5,6,7,0,8,4] 30 :=
  local_sound a [2,5,6,7,0,8,4] 30 cert1415 (by decide +kernel)

theorem node1416 : UpperPrefix a [2,5,6,7,0,8] 30 :=
  branch_upper a [2,5,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,7,0,8,0] 30 (by decide +kernel))
  node1413
  (invalid_upper a [2,5,6,7,0,8,2] 30 (by decide +kernel))
  node1414
  node1415
  (invalid_upper a [2,5,6,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,0,8,8] 30 (by decide +kernel)))

theorem node1417 : UpperPrefix a [2,5,6,7,0] 30 :=
  branch_upper a [2,5,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,7,0,0] 30 (by decide +kernel))
  node1410
  (invalid_upper a [2,5,6,7,0,2] 30 (by decide +kernel))
  node1411
  node1412
  (invalid_upper a [2,5,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,0,7] 30 (by decide +kernel))
  node1416)

def cert1418 : Leaf := ⟨⟨344,0,400,324,0,286,284,92,88⟩,[(1,5),(4,1)],[(5,1,4),(7,3,2),(0,5,1),(0,5,4)],⟨7,35,76,152,50,97,472,408,284⟩,⟨7,35,76,152,50,97,192,384,260⟩,[⟨1,1323666154147174067208193,⟨5,33,460,476,508,97,192,384,260⟩⟩]⟩
theorem node1418 : UpperPrefix a [2,5,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,6,7,1,0] 30 cert1418 (by decide +kernel)

def cert1419 : Leaf := ⟨⟨344,348,0,327,0,0,279,87,83⟩,[(2,5),(4,1),(5,2)],[(5,1,4),(7,3,2),(7,3,5)],⟨7,35,76,152,50,104,465,401,277⟩,⟨7,35,76,152,50,104,192,384,260⟩,[⟨3,1214857655926163789317121,⟨471,499,68,144,242,96,192,384,260⟩⟩]⟩
theorem node1419 : UpperPrefix a [2,5,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,1,3] 30 cert1419 (by decide +kernel)

def cert1420 : Leaf := ⟨⟨80,84,147,7,0,7,287,31,27⟩,[(4,1)],[(5,1,4),(7,3,2)],⟨7,35,76,152,50,112,457,393,269⟩,⟨7,35,76,152,50,112,192,384,260⟩,[⟨8,1181748086455900761975,⟨55,55,127,155,55,127,255,155,55⟩⟩,⟨3,1210107565442661323247365,⟨55,51,119,144,50,112,192,403,311⟩⟩,⟨6,1214856448961467277902849,⟨415,443,12,152,186,56,128,384,260⟩⟩]⟩
theorem node1420 : UpperPrefix a [2,5,6,7,1,4] 30 :=
  Boolean.leaf_sound a [2,5,6,7,1,4] 30 cert1420 (by decide +kernel)

def cert1421 : Leaf := ⟨⟨336,340,402,326,0,22,278,86,82⟩,[(4,1)],[(5,1,4),(7,3,2)],⟨7,35,76,152,50,352,193,392,276⟩,⟨7,35,76,152,50,352,193,392,260⟩,[⟨0,1603235354003467421090816,⟨446,446,492,408,446,492,508,392,420⟩⟩,⟨3,1233721710471361122782981,⟨311,307,375,242,50,371,499,499,311⟩⟩]⟩
theorem node1421 : UpperPrefix a [2,5,6,7,1,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,1,8,0,3] 30 cert1421 (by decide +kernel)

def cert1422 : Local := ⟨⟨328,332,387,0,0,15,270,79,75⟩,[(3,7),(4,1)],[(5,1,4),(7,3,2),(4,7,3)]⟩
theorem node1422 : UpperPrefix a [2,5,6,7,1,8,0,4] 30 :=
  local_sound a [2,5,6,7,1,8,0,4] 30 cert1422 (by decide +kernel)

theorem node1423 : UpperPrefix a [2,5,6,7,1,8,0] 30 :=
  branch_upper a [2,5,6,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,0,2] 30 (by decide +kernel))
  node1421
  node1422
  (invalid_upper a [2,5,6,7,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,0,8] 30 (by decide +kernel)))

def cert1424 : Local := ⟨⟨336,340,0,327,0,23,0,87,83⟩,[(2,6),(4,1),(6,3)],[(5,1,4),(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node1424 : UpperPrefix a [2,5,6,7,1,8,3] 30 :=
  local_sound a [2,5,6,7,1,8,3] 30 cert1424 (by decide +kernel)

def cert1425 : Local := ⟨⟨328,332,403,0,0,15,0,79,75⟩,[(3,6),(4,1),(6,3)],[(5,1,4),(7,3,2),(4,6,2)]⟩
theorem node1425 : UpperPrefix a [2,5,6,7,1,8,4] 30 :=
  local_sound a [2,5,6,7,1,8,4] 30 cert1425 (by decide +kernel)

theorem node1426 : UpperPrefix a [2,5,6,7,1,8] 30 :=
  branch_upper a [2,5,6,7,1,8] 30 (by decide) (fin9_cases _
  node1423
  (invalid_upper a [2,5,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,2] 30 (by decide +kernel))
  node1424
  node1425
  (invalid_upper a [2,5,6,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,8,8] 30 (by decide +kernel)))

theorem node1427 : UpperPrefix a [2,5,6,7,1] 30 :=
  branch_upper a [2,5,6,7,1] 30 (by decide) (fin9_cases _
  node1418
  (invalid_upper a [2,5,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,2] 30 (by decide +kernel))
  node1419
  node1420
  (invalid_upper a [2,5,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,1,7] 30 (by decide +kernel))
  node1426)

def cert1428 : Leaf := ⟨⟨112,0,178,38,6,22,318,62,58⟩,[(1,5)],[(7,3,2),(0,5,1)],⟨7,35,76,152,56,97,466,402,278⟩,⟨7,35,76,152,56,97,192,384,260⟩,[⟨8,1181748068640376418167,⟨55,55,127,155,63,127,255,131,55⟩⟩,⟨6,1215151596868849948967937,⟨415,443,12,152,186,443,128,384,260⟩⟩,⟨3,1210107565424588100882181,⟨39,35,103,144,50,99,192,387,295⟩⟩]⟩
theorem node1428 : UpperPrefix a [2,5,6,7,3,0] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,0] 30 cert1428 (by decide +kernel)

def cert1429 : Leaf := ⟨⟨96,68,177,37,5,5,317,61,57⟩,[],[(7,3,2),(1,5,1)],⟨7,35,76,152,56,98,465,401,277⟩,⟨7,35,76,152,56,98,192,384,260⟩,[⟨8,1181748068640376418167,⟨55,55,127,155,63,127,255,131,55⟩⟩,⟨6,1214856448963668448642049,⟨415,443,12,152,56,186,128,384,260⟩⟩,⟨3,1210107565424588100865797,⟨39,35,103,144,48,98,192,387,295⟩⟩,⟨4,1210107565423489662979845,⟨39,35,111,136,40,98,192,387,295⟩⟩]⟩
theorem node1429 : UpperPrefix a [2,5,6,7,3,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,1] 30 cert1429 (by decide +kernel)

def cert1430 : Leaf := ⟨⟨104,72,160,96,64,8,303,111,107⟩,[],[(7,3,2),(4,5,4)],⟨7,35,76,152,56,112,451,387,263⟩,⟨7,35,76,152,56,112,192,384,260⟩,[⟨8,1181748068640376418167,⟨55,55,127,155,63,127,255,131,55⟩⟩,⟨0,1210107567683269550932992,⟨54,54,124,152,60,124,252,384,308⟩⟩,⟨1,1210107567683269550931969,⟨53,53,124,152,60,124,252,384,308⟩⟩,⟨2,1210107567683269524719105,⟨51,51,120,152,56,120,248,384,304⟩⟩]⟩
theorem node1430 : UpperPrefix a [2,5,6,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,4] 30 cert1430 (by decide +kernel)

def cert1431 : Leaf := ⟨⟨360,328,416,352,320,8,298,104,120⟩,[],[(7,3,2),(1,7,6)],⟨7,35,76,152,56,352,193,386,276⟩,⟨7,35,76,152,56,352,193,386,260⟩,[⟨0,1772096849261091636642816,⟨446,446,380,408,316,380,508,410,308⟩⟩,⟨2,1210402753737540522509313,⟨91,251,90,184,184,506,251,506,256⟩⟩,⟨4,1212771872304306429621533,⟨71,227,79,239,239,483,227,483,487⟩⟩]⟩
theorem node1431 : UpperPrefix a [2,5,6,7,3,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,8,0,1] 30 cert1431 (by decide +kernel)

def cert1432 : Leaf := ⟨⟨352,324,418,0,326,6,294,110,98⟩,[(3,7)],[(7,3,2),(4,7,3)],⟨7,35,76,152,56,352,193,400,262⟩,⟨7,35,76,152,56,352,193,400,260⟩,[⟨0,1227548964064420804166656,⟨414,446,252,152,188,508,508,408,412⟩⟩,⟨3,1233721710437344981798661,⟨295,291,359,242,50,355,483,499,295⟩⟩]⟩
theorem node1432 : UpperPrefix a [2,5,6,7,3,8,0,4] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,8,0,4] 30 cert1432 (by decide +kernel)

theorem node1433 : UpperPrefix a [2,5,6,7,3,8,0] 30 :=
  branch_upper a [2,5,6,7,3,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,7,3,8,0,0] 30 (by decide +kernel))
  node1431
  (invalid_upper a [2,5,6,7,3,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,0,3] 30 (by decide +kernel))
  node1432
  (invalid_upper a [2,5,6,7,3,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,0,8] 30 (by decide +kernel)))

def cert1434 : Leaf := ⟨⟨360,328,416,352,320,8,297,108,120⟩,[],[(2,0,7),(7,3,2),(0,7,6)],⟨7,35,76,152,56,352,194,385,276⟩,⟨7,35,76,152,56,352,194,385,260⟩,[⟨1,1772096849261091636641793,⟨445,445,380,408,316,380,508,409,308⟩⟩,⟨4,1212771872304306429588765,⟨71,227,79,239,239,483,226,483,487⟩⟩]⟩
theorem node1434 : UpperPrefix a [2,5,6,7,3,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,8,1,0] 30 cert1434 (by decide +kernel)

def cert1435 : Leaf := ⟨⟨352,324,417,0,325,5,293,109,97⟩,[(3,7)],[(7,3,2),(4,7,3)],⟨7,35,76,152,56,352,194,400,261⟩,⟨7,35,76,152,56,352,194,400,260⟩,[⟨1,1227548964064420804165633,⟨413,445,252,152,188,508,508,408,412⟩⟩,⟨3,1233721852300733243936517,⟨295,291,359,242,114,355,226,499,295⟩⟩]⟩
theorem node1435 : UpperPrefix a [2,5,6,7,3,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,8,1,4] 30 cert1435 (by decide +kernel)

theorem node1436 : UpperPrefix a [2,5,6,7,3,8,1] 30 :=
  branch_upper a [2,5,6,7,3,8,1] 30 (by decide) (fin9_cases _
  node1434
  (invalid_upper a [2,5,6,7,3,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,1,3] 30 (by decide +kernel))
  node1435
  (invalid_upper a [2,5,6,7,3,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,1,8] 30 (by decide +kernel)))

def cert1437 : Leaf := ⟨⟨352,324,435,0,327,7,0,103,99⟩,[(3,6),(6,3)],[(7,3,2),(4,6,2)],⟨7,35,76,152,56,352,208,387,263⟩,⟨7,35,76,152,56,352,208,384,260⟩,[⟨3,1236440724935372713381637,⟨423,419,487,208,242,483,208,387,423⟩⟩]⟩
theorem node1437 : UpperPrefix a [2,5,6,7,3,8,4] 30 :=
  Boolean.leaf_sound a [2,5,6,7,3,8,4] 30 cert1437 (by decide +kernel)

theorem node1438 : UpperPrefix a [2,5,6,7,3,8] 30 :=
  branch_upper a [2,5,6,7,3,8] 30 (by decide) (fin9_cases _
  node1433
  node1436
  (invalid_upper a [2,5,6,7,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,3] 30 (by decide +kernel))
  node1437
  (invalid_upper a [2,5,6,7,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,8,8] 30 (by decide +kernel)))

theorem node1439 : UpperPrefix a [2,5,6,7,3] 30 :=
  branch_upper a [2,5,6,7,3] 30 (by decide) (fin9_cases _
  node1428
  node1429
  (invalid_upper a [2,5,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,3] 30 (by decide +kernel))
  node1430
  (invalid_upper a [2,5,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,3,7] 30 (by decide +kernel))
  node1438)

def cert1440 : Leaf := ⟨⟨120,0,178,290,14,30,58,58,58⟩,[(1,5)],[(7,3,2),(8,4,3),(0,5,1)],⟨7,35,76,152,304,97,218,410,286⟩,⟨7,35,76,152,304,97,192,384,260⟩,[⟨6,1215299170821439625380865,⟨415,443,12,152,442,443,128,384,260⟩⟩,⟨2,1210255427466819660694529,⟨3,35,72,216,506,99,192,384,256⟩⟩]⟩
theorem node1440 : UpperPrefix a [2,5,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,0] 30 cert1440 (by decide +kernel)

def cert1441 : Leaf := ⟨⟨96,68,177,293,5,5,61,61,57⟩,[],[(7,3,2),(8,4,3),(1,5,1)],⟨7,35,76,152,304,98,217,409,285⟩,⟨7,35,76,152,304,98,192,384,260⟩,[⟨3,1210107565442180286918405,⟨39,35,103,146,307,98,192,403,311⟩⟩,⟨6,1214856448961469425386497,⟨415,443,12,152,312,186,128,384,260⟩⟩,⟨4,1210107565423489662988037,⟨39,35,111,138,291,98,192,387,295⟩⟩]⟩
theorem node1441 : UpperPrefix a [2,5,6,7,8,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,1] 30 cert1441 (by decide +kernel)

def cert1442 : Leaf := ⟨⟨120,92,0,295,7,0,55,55,51⟩,[(2,5),(5,2)],[(7,3,2),(7,3,5),(8,4,3)],⟨7,35,76,152,304,104,211,403,279⟩,⟨7,35,76,152,304,104,192,384,260⟩,[⟨3,1214857655926163789317121,⟨471,499,68,144,304,96,192,384,260⟩⟩,⟨6,1214856448961465130419201,⟨415,443,12,152,304,40,128,384,260⟩⟩]⟩
theorem node1442 : UpperPrefix a [2,5,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,3] 30 cert1442 (by decide +kernel)

def cert1443 : Leaf := ⟨⟨112,84,176,356,68,4,54,116,120⟩,[],[(7,3,2),(8,4,3),(1,7,6)],⟨7,35,76,152,304,112,193,386,268⟩,⟨7,35,76,152,304,112,193,386,260⟩,[⟨0,1696538985552769499268096,⟨446,446,380,152,308,380,508,410,308⟩⟩,⟨3,1212623544870690809425157,⟨7,35,103,242,499,242,243,499,503⟩⟩]⟩
theorem node1443 : UpperPrefix a [2,5,6,7,8,4,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,4,0,1] 30 cert1443 (by decide +kernel)

def cert1444 : Leaf := ⟨⟨80,84,146,326,70,6,22,86,82⟩,[],[(7,3,2),(8,4,3)],⟨7,35,76,152,304,112,193,392,262⟩,⟨7,35,76,152,304,112,193,392,260⟩,[⟨0,1227401390267755620467712,⟨446,446,252,152,444,252,508,408,444⟩⟩,⟨3,1233721710750087320416005,⟨311,307,375,242,307,114,499,499,311⟩⟩,⟨5,1224440738346426080691203,⟨455,463,76,152,412,220,449,392,260⟩⟩]⟩
theorem node1444 : UpperPrefix a [2,5,6,7,8,4,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,4,0,3] 30 cert1444 (by decide +kernel)

theorem node1445 : UpperPrefix a [2,5,6,7,8,4,0] 30 :=
  branch_upper a [2,5,6,7,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,7,8,4,0,0] 30 (by decide +kernel))
  node1443
  (invalid_upper a [2,5,6,7,8,4,0,2] 30 (by decide +kernel))
  node1444
  (invalid_upper a [2,5,6,7,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,0,8] 30 (by decide +kernel)))

def cert1446 : Leaf := ⟨⟨80,84,145,325,69,5,21,93,89⟩,[],[(7,3,2),(8,4,3)],⟨7,35,76,152,304,112,194,393,269⟩,⟨7,35,76,152,304,112,194,384,260⟩,[⟨1,1224302337263331076734977,⟨445,445,124,152,308,124,508,408,308⟩⟩,⟨5,1389908032687600758686787,⟨455,463,461,152,412,477,455,384,388⟩⟩,⟨3,1210110022287718412791045,⟨7,35,103,242,307,114,242,499,263⟩⟩]⟩
theorem node1446 : UpperPrefix a [2,5,6,7,8,4,1] 30 :=
  Boolean.leaf_sound a [2,5,6,7,8,4,1] 30 cert1446 (by decide +kernel)

def cert1447 : Local := ⟨⟨112,84,0,359,71,7,0,119,115⟩,[(2,6),(6,3)],[(7,3,2),(7,3,6),(8,4,3),(3,6,2)]⟩
theorem node1447 : UpperPrefix a [2,5,6,7,8,4,3] 30 :=
  local_sound a [2,5,6,7,8,4,3] 30 cert1447 (by decide +kernel)

theorem node1448 : UpperPrefix a [2,5,6,7,8,4] 30 :=
  branch_upper a [2,5,6,7,8,4] 30 (by decide) (fin9_cases _
  node1445
  node1446
  (invalid_upper a [2,5,6,7,8,4,2] 30 (by decide +kernel))
  node1447
  (invalid_upper a [2,5,6,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,4,8] 30 (by decide +kernel)))

theorem node1449 : UpperPrefix a [2,5,6,7,8] 30 :=
  branch_upper a [2,5,6,7,8] 30 (by decide) (fin9_cases _
  node1440
  node1441
  (invalid_upper a [2,5,6,7,8,2] 30 (by decide +kernel))
  node1442
  node1448
  (invalid_upper a [2,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,8,8] 30 (by decide +kernel)))

theorem node1450 : UpperPrefix a [2,5,6,7] 30 :=
  branch_upper a [2,5,6,7] 30 (by decide) (fin9_cases _
  node1417
  node1427
  (invalid_upper a [2,5,6,7,2] 30 (by decide +kernel))
  node1439
  (invalid_upper a [2,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,7,7] 30 (by decide +kernel))
  node1449)

def cert1451 : Leaf := ⟨⟨504,0,400,196,0,413,284,92,216⟩,[(1,4),(4,1)],[(1,5,1),(1,5,4)],⟨7,35,76,280,49,98,216,408,412⟩,⟨7,35,76,280,49,98,192,384,260⟩,[⟨0,1323666154147174067209216,⟨6,34,460,476,508,98,192,384,260⟩⟩,⟨5,1323666153021274160366593,⟨7,3,460,476,477,66,192,384,260⟩⟩]⟩
theorem node1451 : UpperPrefix a [2,5,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,1] 30 cert1451 (by decide +kernel)

def cert1452 : Leaf := ⟨⟨504,0,0,231,0,0,311,119,243⟩,[(1,4),(2,5),(4,1),(5,2)],[],⟨7,35,76,280,49,104,210,402,406⟩,⟨7,35,76,280,49,104,192,384,260⟩,[⟨3,1215079449200612531512321,⟨471,499,196,466,499,224,192,384,260⟩⟩]⟩
theorem node1452 : UpperPrefix a [2,5,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,3] 30 cert1452 (by decide +kernel)

def cert1453 : Leaf := ⟨⟨360,0,291,39,0,267,299,43,171⟩,[(1,4),(4,1)],[],⟨7,35,76,280,49,112,202,394,398⟩,⟨7,35,76,280,49,112,192,384,260⟩,[⟨4,1247960428237192252367881,⟨7,35,461,463,35,98,192,384,260⟩⟩,⟨7,1208926976080393425579877,⟨55,51,127,283,51,119,127,283,319⟩⟩,⟨2,1210181496656947014804481,⟨19,51,232,506,51,114,192,384,256⟩⟩,⟨6,1215077809890351792530433,⟨415,443,140,410,443,186,128,384,260⟩⟩]⟩
theorem node1453 : UpperPrefix a [2,5,6,8,0,4] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,4] 30 cert1453 (by decide +kernel)

def cert1454 : Leaf := ⟨⟨376,0,307,39,0,0,315,59,59⟩,[(1,4),(4,1),(5,6)],[(7,5,5)],⟨7,35,76,280,49,224,218,410,286⟩,⟨7,35,76,280,49,224,192,384,260⟩,[⟨6,1215077809890351792530433,⟨415,443,140,410,443,160,128,384,260⟩⟩,⟨2,1210181499049553036322305,⟨51,51,232,506,51,224,224,384,288⟩⟩]⟩
theorem node1454 : UpperPrefix a [2,5,6,8,0,7] 30 :=
  Boolean.leaf_sound a [2,5,6,8,0,7] 30 cert1454 (by decide +kernel)

theorem node1455 : UpperPrefix a [2,5,6,8,0] 30 :=
  branch_upper a [2,5,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,8,0,0] 30 (by decide +kernel))
  node1451
  (invalid_upper a [2,5,6,8,0,2] 30 (by decide +kernel))
  node1452
  node1453
  (invalid_upper a [2,5,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,0,6] 30 (by decide +kernel))
  node1454
  (invalid_upper a [2,5,6,8,0,8] 30 (by decide +kernel)))

def cert1456 : Leaf := ⟨⟨472,0,400,196,0,414,284,92,216⟩,[(1,5),(4,1)],[(5,1,4),(0,5,1),(0,5,4)],⟨7,35,76,280,50,97,216,408,412⟩,⟨7,35,76,280,50,97,192,384,260⟩,[⟨1,1323666154147174067208193,⟨5,33,460,476,508,97,192,384,260⟩⟩]⟩
theorem node1456 : UpperPrefix a [2,5,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,0] 30 cert1456 (by decide +kernel)

def cert1457 : Leaf := ⟨⟨472,476,0,135,0,0,279,23,147⟩,[(2,5),(4,1),(5,2)],[(5,1,4)],⟨7,35,76,280,50,104,209,401,405⟩,⟨7,35,76,280,50,104,192,384,260⟩,[⟨3,1214857655926163789317121,⟨471,499,68,272,242,96,192,384,260⟩⟩,⟨6,1214856448961465130419201,⟨415,443,12,280,186,40,128,384,260⟩⟩]⟩
theorem node1457 : UpperPrefix a [2,5,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,3] 30 cert1457 (by decide +kernel)

def cert1458 : Leaf := ⟨⟨344,348,272,68,0,269,284,92,216⟩,[(4,1)],[(5,1,4)],⟨7,35,76,280,50,112,193,392,396⟩,⟨7,35,76,280,50,112,193,384,260⟩,[⟨1,1503466190894206622892033,⟨453,493,460,444,508,508,193,384,388⟩⟩,⟨7,1208926976080393425579877,⟨55,51,127,283,51,119,127,283,319⟩⟩,⟨0,1773240544994164332299264,⟨414,446,460,408,446,508,460,384,388⟩⟩]⟩
theorem node1458 : UpperPrefix a [2,5,6,8,1,4,0] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,4,0] 30 cert1458 (by decide +kernel)

def cert1459 : Leaf := ⟨⟨208,212,0,197,0,133,277,85,209⟩,[(2,6),(4,1)],[(5,1,4),(8,3,6),(3,6,2)],⟨7,35,76,280,50,112,200,385,389⟩,⟨7,35,76,280,50,112,200,384,260⟩,[⟨1,1224302623923374446870529,⟨389,421,108,380,508,124,236,384,260⟩⟩]⟩
theorem node1459 : UpperPrefix a [2,5,6,8,1,4,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,4,3] 30 cert1459 (by decide +kernel)

theorem node1460 : UpperPrefix a [2,5,6,8,1,4] 30 :=
  branch_upper a [2,5,6,8,1,4] 30 (by decide) (fin9_cases _
  node1458
  (invalid_upper a [2,5,6,8,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,4,2] 30 (by decide +kernel))
  node1459
  (invalid_upper a [2,5,6,8,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,4,8] 30 (by decide +kernel)))

def cert1461 : Leaf := ⟨⟨336,340,275,7,0,0,287,31,27⟩,[(4,1),(5,6)],[(5,1,4),(7,5,5)],⟨7,35,76,280,50,224,217,409,285⟩,⟨7,35,76,280,50,224,192,384,260⟩,[⟨6,1214856448961465130419201,⟨415,443,12,280,186,160,128,384,260⟩⟩,⟨3,1210107567536062742924549,⟨23,51,119,273,50,224,224,385,279⟩⟩]⟩
theorem node1461 : UpperPrefix a [2,5,6,8,1,7] 30 :=
  Boolean.leaf_sound a [2,5,6,8,1,7] 30 cert1461 (by decide +kernel)

theorem node1462 : UpperPrefix a [2,5,6,8,1] 30 :=
  branch_upper a [2,5,6,8,1] 30 (by decide) (fin9_cases _
  node1456
  (invalid_upper a [2,5,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,2] 30 (by decide +kernel))
  node1457
  node1460
  (invalid_upper a [2,5,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,1,6] 30 (by decide +kernel))
  node1461
  (invalid_upper a [2,5,6,8,1,8] 30 (by decide +kernel)))

def cert1463 : Leaf := ⟨⟨112,0,306,38,6,22,310,54,186⟩,[(1,5)],[(0,5,1)],⟨7,35,76,280,56,97,210,402,406⟩,⟨7,35,76,280,56,97,192,384,260⟩,[⟨7,1208926976077988243894117,⟨55,35,127,283,59,119,127,283,319⟩⟩,⟨3,1210181785027922143371013,⟨39,35,231,499,242,99,192,387,295⟩⟩,⟨6,1215151596868847801484289,⟨415,443,12,280,186,443,128,384,260⟩⟩,⟨8,1181745810234877824773,⟨55,35,127,27,58,99,192,131,55⟩⟩]⟩
theorem node1463 : UpperPrefix a [2,5,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,0] 30 cert1463 (by decide +kernel)

def cert1464 : Leaf := ⟨⟨96,68,305,37,5,5,309,53,185⟩,[],[(1,5,1)],⟨7,35,76,280,56,98,209,401,405⟩,⟨7,35,76,280,56,98,192,384,260⟩,[⟨7,1208926976077988243894117,⟨55,35,127,283,59,119,127,283,319⟩⟩,⟨3,1210181497360495945064197,⟨39,35,231,499,242,98,192,387,295⟩⟩,⟨6,1214856448963664153674753,⟨415,443,12,280,56,186,128,384,260⟩⟩,⟨8,1181745810234877808389,⟨55,35,127,27,56,98,192,131,55⟩⟩,⟨4,1210107565423489662979845,⟨39,35,111,267,40,98,192,387,295⟩⟩]⟩
theorem node1464 : UpperPrefix a [2,5,6,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,1] 30 cert1464 (by decide +kernel)

def cert1465 : Leaf := ⟨⟨96,68,290,102,70,6,39,103,227⟩,[],[(4,5,4)],⟨7,35,76,280,56,112,195,387,391⟩,⟨7,35,76,280,56,112,192,384,260⟩,[⟨3,1236223814266607482445061,⟨455,483,487,499,242,112,192,449,455⟩⟩,⟨7,1208926976077988243894117,⟨55,35,127,283,59,119,127,283,319⟩⟩,⟨8,1184051653244091502341,⟨55,35,127,27,56,112,192,195,55⟩⟩,⟨0,1210107567698705655006208,⟨54,34,124,280,56,116,252,408,316⟩⟩]⟩
theorem node1465 : UpperPrefix a [2,5,6,8,3,4] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,4] 30 cert1465 (by decide +kernel)

def cert1466 : Leaf := ⟨⟨112,84,307,36,4,0,311,55,59⟩,[(5,6)],[(7,5,5)],⟨7,35,76,280,56,224,211,403,279⟩,⟨7,35,76,280,56,224,192,384,260⟩,[⟨3,1210181499612295758749445,⟨39,35,231,499,242,224,224,387,295⟩⟩,⟨6,1214856448961465130419201,⟨415,443,12,280,56,160,128,384,260⟩⟩,⟨8,1181747921297203006725,⟨23,35,127,25,56,224,224,129,23⟩⟩,⟨0,1210107567535960737448960,⟨22,34,124,280,56,224,224,392,284⟩⟩,⟨1,1210107567535960737447937,⟨21,33,124,280,56,224,224,392,284⟩⟩]⟩
theorem node1466 : UpperPrefix a [2,5,6,8,3,7] 30 :=
  Boolean.leaf_sound a [2,5,6,8,3,7] 30 cert1466 (by decide +kernel)

theorem node1467 : UpperPrefix a [2,5,6,8,3] 30 :=
  branch_upper a [2,5,6,8,3] 30 (by decide) (fin9_cases _
  node1463
  node1464
  (invalid_upper a [2,5,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,3,3] 30 (by decide +kernel))
  node1465
  (invalid_upper a [2,5,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,3,6] 30 (by decide +kernel))
  node1466
  (invalid_upper a [2,5,6,8,3,8] 30 (by decide +kernel)))

def cert1468 : Leaf := ⟨⟨240,0,176,228,68,150,52,124,248⟩,[(1,5)],[(0,5,1),(1,6,5)],⟨7,35,76,280,176,97,194,408,284⟩,⟨7,35,76,280,176,97,194,384,260⟩,[⟨8,1184344681614111104781,⟨39,35,127,127,242,115,242,243,39⟩⟩,⟨3,1210110164296242209971973,⟨39,35,119,371,242,115,242,499,295⟩⟩]⟩
theorem node1468 : UpperPrefix a [2,5,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,0,1] 30 cert1468 (by decide +kernel)

def cert1469 : Leaf := ⟨⟨240,0,0,166,6,150,310,54,178⟩,[(1,5),(2,6)],[(8,3,6),(0,5,1),(3,6,2)],⟨7,35,76,280,176,97,200,402,278⟩,⟨7,35,76,280,176,97,200,384,260⟩,[⟨6,1215151596868847801484289,⟨415,443,12,280,186,443,136,384,260⟩⟩]⟩
theorem node1469 : UpperPrefix a [2,5,6,8,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,6,8,7,0,3] 30 cert1469 (by decide +kernel)

def cert1470 : Local := ⟨⟨360,0,306,102,334,270,0,110,106⟩,[(1,5),(6,4)],[(7,4,6),(0,5,1),(4,6,2)]⟩
theorem node1470 : UpperPrefix a [2,5,6,8,7,0,4] 30 :=
  local_sound a [2,5,6,8,7,0,4] 30 cert1470 (by decide +kernel)

theorem node1471 : UpperPrefix a [2,5,6,8,7,0] 30 :=
  branch_upper a [2,5,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,6,8,7,0,0] 30 (by decide +kernel))
  node1468
  (invalid_upper a [2,5,6,8,7,0,2] 30 (by decide +kernel))
  node1469
  node1470
  (invalid_upper a [2,5,6,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,6,8,7,0,8] 30 (by decide +kernel)))

#print axioms node1471
end Delivery.FiniteExclusion.Sharp2x7
