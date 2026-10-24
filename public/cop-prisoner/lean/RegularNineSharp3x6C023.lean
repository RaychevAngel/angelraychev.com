import RegularNineSharp3x6Base
import RegularNineSharp3x6C022
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert1472 : Leaf := ⟨⟨0,361,328,353,73,265,296,41,101⟩,[(0,3)],[(1,3,0)],⟨11,134,37,26,304,112,193,448,268⟩,⟨11,134,37,26,304,112,193,448,264⟩,[⟨2,1212621131011660623905803,⟨107,251,33,251,496,240,241,496,505⟩⟩,⟨4,1250485704634649948486921,⟨459,198,231,463,487,230,193,449,459⟩⟩,⟨7,1581993932581041587356683,⟨287,319,317,287,304,372,381,372,265⟩⟩]⟩
theorem node1472 : UpperPrefix a [3,7,5,1,8,4,0,6] 30 :=
  Boolean.leaf_sound a [3,7,5,1,8,4,0,6] 30 cert1472 (by decide +kernel)

theorem node1473 : UpperPrefix a [3,7,5,1,8,4,0] 30 :=
  branch_upper a [3,7,5,1,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,1,8,4,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,0,1] 30 (by decide +kernel))
  node1471
  (invalid_upper a [3,7,5,1,8,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,0,5] 30 (by decide +kernel))
  node1472
  (invalid_upper a [3,7,5,1,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,0,8] 30 (by decide +kernel)))

def cert1474 : Leaf := ⟨⟨0,0,472,484,204,396,0,125,245⟩,[(0,3),(1,6),(6,1)],[(1,3,0)],⟨11,134,37,26,304,112,196,449,329⟩,⟨11,134,37,26,304,112,196,384,264⟩,[⟨0,1210107601611720162837504,⟨106,198,44,122,312,122,198,400,312⟩⟩]⟩
theorem node1474 : UpperPrefix a [3,7,5,1,8,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,1,8,4,2] 30 cert1474 (by decide +kernel)

theorem node1475 : UpperPrefix a [3,7,5,1,8,4] 30 :=
  branch_upper a [3,7,5,1,8,4] 30 (by decide) (fin9_cases _
  node1473
  (invalid_upper a [3,7,5,1,8,4,1] 30 (by decide +kernel))
  node1474
  (invalid_upper a [3,7,5,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,4,8] 30 (by decide +kernel)))

theorem node1476 : UpperPrefix a [3,7,5,1,8] 30 :=
  branch_upper a [3,7,5,1,8] 30 (by decide) (fin9_cases _
  node1467
  (invalid_upper a [3,7,5,1,8,1] 30 (by decide +kernel))
  node1470
  (invalid_upper a [3,7,5,1,8,3] 30 (by decide +kernel))
  node1475
  (invalid_upper a [3,7,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,8,8] 30 (by decide +kernel)))

theorem node1477 : UpperPrefix a [3,7,5,1] 30 :=
  branch_upper a [3,7,5,1] 30 (by decide) (fin9_cases _
  node1455
  (invalid_upper a [3,7,5,1,1] 30 (by decide +kernel))
  node1456
  (invalid_upper a [3,7,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,1,5] 30 (by decide +kernel))
  node1464
  (invalid_upper a [3,7,5,1,7] 30 (by decide +kernel))
  node1476)

def cert1478 : Leaf := ⟨⟨404,344,0,419,0,410,282,90,210⟩,[(2,4),(4,2)],[(5,2,3),(2,3,0),(0,4,3)],⟨11,134,37,28,49,370,466,466,346⟩,⟨11,134,37,28,49,96,192,384,264⟩,[⟨6,1210106412362624914162691,⟨11,159,61,28,61,32,128,384,264⟩⟩]⟩
theorem node1478 : UpperPrefix a [3,7,5,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,2,0] 30 cert1478 (by decide +kernel)

def cert1479 : Leaf := ⟨⟨468,344,0,480,456,408,280,88,208⟩,[(2,5)],[(5,2,3),(2,3,0),(0,5,2)],⟨11,134,37,28,50,97,464,464,344⟩,⟨11,134,37,28,50,97,192,384,264⟩,[⟨1,1323666154182358441656321,⟨493,132,37,476,508,101,192,384,456⟩⟩]⟩
theorem node1479 : UpperPrefix a [3,7,5,2,1,0] 30 :=
  Boolean.leaf_sound a [3,7,5,2,1,0] 30 cert1479 (by decide +kernel)

def cert1480 : Leaf := ⟨⟨68,73,88,99,201,137,265,73,65⟩,[],[(5,2,3),(2,3,0)],⟨11,134,37,28,50,112,449,449,329⟩,⟨11,134,37,28,50,112,192,384,264⟩,[⟨8,1181747927634993513587,⟨11,143,61,29,63,127,255,128,8⟩⟩,⟨1,1214876138980373129592833,⟨493,196,485,252,48,112,192,384,296⟩⟩,⟨4,1255097102422701180460297,⟨459,198,487,463,34,96,192,449,459⟩⟩,⟨7,1360042701114969376687121,⟨11,6,301,29,319,381,64,256,264⟩⟩]⟩
theorem node1480 : UpperPrefix a [3,7,5,2,1,4] 30 :=
  Boolean.leaf_sound a [3,7,5,2,1,4] 30 cert1480 (by decide +kernel)

def cert1481 : Leaf := ⟨⟨20,25,26,35,393,27,26,11,83⟩,[],[(5,2,3),(2,3,0)],⟨11,134,37,28,50,352,193,400,328⟩,⟨11,134,37,28,50,352,193,400,264⟩,[⟨6,1210401560270024773561599,⟨11,159,191,31,191,447,139,415,265⟩⟩,⟨7,1511158430818610730501139,⟨11,15,37,29,63,356,365,285,264⟩⟩,⟨8,1184087541048084071635,⟨75,207,37,29,127,101,203,223,8⟩⟩]⟩
theorem node1481 : UpperPrefix a [3,7,5,2,1,8,0,4] 30 :=
  Boolean.leaf_sound a [3,7,5,2,1,8,0,4] 30 cert1481 (by decide +kernel)

def cert1482 : Leaf := ⟨⟨340,344,346,354,328,0,282,0,82⟩,[(5,7),(7,5)],[(5,2,3),(2,3,0)],⟨11,134,37,28,50,352,193,448,280⟩,⟨11,134,37,28,50,352,193,448,264⟩,[⟨7,1336430875456154147226643,⟨287,319,301,285,319,356,365,356,264⟩⟩,⟨0,1357386376724161309445120,⟨282,446,446,286,442,480,480,480,264⟩⟩]⟩
theorem node1482 : UpperPrefix a [3,7,5,2,1,8,0,6] 30 :=
  Boolean.leaf_sound a [3,7,5,2,1,8,0,6] 30 cert1482 (by decide +kernel)

theorem node1483 : UpperPrefix a [3,7,5,2,1,8,0] 30 :=
  branch_upper a [3,7,5,2,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,2,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,0,3] 30 (by decide +kernel))
  node1481
  (invalid_upper a [3,7,5,2,1,8,0,5] 30 (by decide +kernel))
  node1482
  (invalid_upper a [3,7,5,2,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,0,8] 30 (by decide +kernel)))

def cert1484 : Leaf := ⟨⟨468,337,464,480,448,144,256,88,208⟩,[],[(3,0,7),(5,2,3),(2,3,0),(0,7,1)],⟨11,134,37,28,50,352,208,385,328⟩,⟨11,134,37,28,50,352,208,385,264⟩,[⟨1,1706002318536203824267265,⟨493,132,421,508,304,360,508,421,360⟩⟩]⟩
theorem node1484 : UpperPrefix a [3,7,5,2,1,8,4,0] 30 :=
  Boolean.leaf_sound a [3,7,5,2,1,8,4,0] 30 cert1484 (by decide +kernel)

def cert1485 : Leaf := ⟨⟨404,281,410,419,393,0,267,0,147⟩,[(5,7),(7,5)],[(5,2,3),(2,3,0)],⟨11,134,37,28,50,352,208,448,265⟩,⟨11,134,37,28,50,352,208,448,264⟩,[⟨6,2414309865496321213891827,⟨267,399,317,285,319,319,415,395,264⟩⟩]⟩
theorem node1485 : UpperPrefix a [3,7,5,2,1,8,4,6] 30 :=
  Boolean.leaf_sound a [3,7,5,2,1,8,4,6] 30 cert1485 (by decide +kernel)

theorem node1486 : UpperPrefix a [3,7,5,2,1,8,4] 30 :=
  branch_upper a [3,7,5,2,1,8,4] 30 (by decide) (fin9_cases _
  node1484
  (invalid_upper a [3,7,5,2,1,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,4,5] 30 (by decide +kernel))
  node1485
  (invalid_upper a [3,7,5,2,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,4,8] 30 (by decide +kernel)))

theorem node1487 : UpperPrefix a [3,7,5,2,1,8] 30 :=
  branch_upper a [3,7,5,2,1,8] 30 (by decide) (fin9_cases _
  node1483
  (invalid_upper a [3,7,5,2,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,3] 30 (by decide +kernel))
  node1486
  (invalid_upper a [3,7,5,2,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,8,8] 30 (by decide +kernel)))

theorem node1488 : UpperPrefix a [3,7,5,2,1] 30 :=
  branch_upper a [3,7,5,2,1] 30 (by decide) (fin9_cases _
  node1479
  (invalid_upper a [3,7,5,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,3] 30 (by decide +kernel))
  node1480
  (invalid_upper a [3,7,5,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,1,7] 30 (by decide +kernel))
  node1487)

def cert1489 : Local := ⟨⟨404,280,0,418,0,410,282,26,146⟩,[(2,5),(4,5)],[(5,2,3),(2,3,0),(6,4,4),(0,5,2)]⟩
theorem node1489 : UpperPrefix a [3,7,5,2,6,0] 30 :=
  local_sound a [3,7,5,2,6,0] 30 cert1489 (by decide +kernel)

def cert1490 : Local := ⟨⟨276,281,282,289,0,409,281,25,17⟩,[(4,5)],[(7,1,5),(5,2,3),(2,3,0),(6,4,4),(1,5,2)]⟩
theorem node1490 : UpperPrefix a [3,7,5,2,6,1] 30 :=
  local_sound a [3,7,5,2,6,1] 30 cert1490 (by decide +kernel)

def cert1491 : Leaf := ⟨⟨388,265,410,419,0,0,267,11,131⟩,[(4,5),(5,4)],[(5,2,3),(2,3,0),(6,4,4),(6,4,5)],⟨11,134,37,28,112,112,451,387,267⟩,⟨11,134,37,28,112,112,192,384,264⟩,[⟨4,1255094796579691966766345,⟨459,198,487,463,96,96,192,449,459⟩⟩]⟩
theorem node1491 : UpperPrefix a [3,7,5,2,6,4] 30 :=
  Boolean.leaf_sound a [3,7,5,2,6,4] 30 cert1491 (by decide +kernel)

def cert1492 : Leaf := ⟨⟨20,281,410,32,0,155,283,27,147⟩,[(4,5)],[(5,2,3),(2,3,0),(6,4,4)],⟨11,134,37,28,112,352,211,403,283⟩,⟨11,134,37,28,112,352,192,384,264⟩,[⟨7,1208926973665333834941443,⟨11,15,61,28,112,368,64,256,264⟩⟩,⟨8,1181745671422071538691,⟨11,143,61,28,112,112,192,128,8⟩⟩,⟨0,1210107565286051246244864,⟨10,142,60,28,112,368,192,384,264⟩⟩,⟨1,1210107565286051246243841,⟨9,140,61,28,112,368,192,384,264⟩⟩]⟩
theorem node1492 : UpperPrefix a [3,7,5,2,6,8] 30 :=
  Boolean.leaf_sound a [3,7,5,2,6,8] 30 cert1492 (by decide +kernel)

theorem node1493 : UpperPrefix a [3,7,5,2,6] 30 :=
  branch_upper a [3,7,5,2,6] 30 (by decide) (fin9_cases _
  node1489
  node1490
  (invalid_upper a [3,7,5,2,6,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,6,3] 30 (by decide +kernel))
  node1491
  (invalid_upper a [3,7,5,2,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,6,7] 30 (by decide +kernel))
  node1492)

def cert1494 : Leaf := ⟨⟨468,336,0,480,202,402,274,82,210⟩,[(2,5)],[(5,2,3),(2,3,0),(0,5,2)],⟨11,134,37,28,304,97,210,466,346⟩,⟨11,134,37,28,304,97,192,384,264⟩,[⟨3,1210255571617188897108993,⟨103,134,37,214,502,101,192,384,322⟩⟩,⟨1,1210107565283853841989633,⟨9,132,37,28,316,101,192,384,264⟩⟩]⟩
theorem node1494 : UpperPrefix a [3,7,5,2,8,0] 30 :=
  Boolean.leaf_sound a [3,7,5,2,8,0] 30 cert1494 (by decide +kernel)

def cert1495 : Leaf := ⟨⟨340,336,338,352,72,401,280,88,80⟩,[],[(7,1,5),(5,2,3),(2,3,0),(1,5,2)],⟨11,134,37,28,304,98,193,464,344⟩,⟨11,134,37,28,304,98,193,384,264⟩,[⟨0,1361518440643334392253440,⟨10,158,446,30,432,506,192,384,264⟩⟩,⟨3,1210107567535650442871809,⟨3,134,37,20,304,102,231,384,256⟩⟩]⟩
theorem node1495 : UpperPrefix a [3,7,5,2,8,1,0] 30 :=
  Boolean.leaf_sound a [3,7,5,2,8,1,0] 30 cert1495 (by decide +kernel)

def cert1496 : Leaf := ⟨⟨20,25,26,33,73,153,265,89,81⟩,[],[(7,1,5),(5,2,3),(2,3,0),(8,4,6),(1,5,2)],⟨11,134,37,28,304,98,208,449,329⟩,⟨11,134,37,28,304,98,208,384,264⟩,[⟨6,1210106412362357829305441,⟨11,134,37,28,317,47,159,384,264⟩⟩]⟩
theorem node1496 : UpperPrefix a [3,7,5,2,8,1,4] 30 :=
  Boolean.leaf_sound a [3,7,5,2,8,1,4] 30 cert1496 (by decide +kernel)

theorem node1497 : UpperPrefix a [3,7,5,2,8,1] 30 :=
  branch_upper a [3,7,5,2,8,1] 30 (by decide) (fin9_cases _
  node1495
  (invalid_upper a [3,7,5,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,1,3] 30 (by decide +kernel))
  node1496
  (invalid_upper a [3,7,5,2,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,1,8] 30 (by decide +kernel)))

def cert1498 : Leaf := ⟨⟨324,329,328,353,73,265,266,73,65⟩,[],[(5,2,3),(2,3,0),(1,7,6)],⟨11,134,37,28,304,112,193,386,328⟩,⟨11,134,37,28,304,112,193,386,264⟩,[⟨4,1255244964605667012803849,⟨459,198,487,463,487,230,449,451,459⟩⟩,⟨7,1662274158277305683674243,⟨11,31,317,28,312,380,381,267,264⟩⟩]⟩
theorem node1498 : UpperPrefix a [3,7,5,2,8,4,0,1] 30 :=
  Boolean.leaf_sound a [3,7,5,2,8,4,0,1] 30 cert1498 (by decide +kernel)

def cert1499 : Leaf := ⟨⟨324,329,330,354,74,266,266,10,66⟩,[],[(5,2,3),(2,3,0)],⟨11,134,37,28,304,112,193,448,266⟩,⟨11,134,37,28,304,112,193,448,264⟩,[⟨4,1255835260416025718455561,⟨459,198,487,463,487,230,449,449,459⟩⟩,⟨7,1223094079880780129502211,⟨287,319,317,28,312,124,381,380,264⟩⟩,⟨0,1224864967311826030167040,⟨282,446,316,28,304,240,496,496,264⟩⟩]⟩
theorem node1499 : UpperPrefix a [3,7,5,2,8,4,0,6] 30 :=
  Boolean.leaf_sound a [3,7,5,2,8,4,0,6] 30 cert1499 (by decide +kernel)

theorem node1500 : UpperPrefix a [3,7,5,2,8,4,0] 30 :=
  branch_upper a [3,7,5,2,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,2,8,4,0,0] 30 (by decide +kernel))
  node1498
  (invalid_upper a [3,7,5,2,8,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,0,5] 30 (by decide +kernel))
  node1499
  (invalid_upper a [3,7,5,2,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,0,8] 30 (by decide +kernel)))

def cert1501 : Local := ⟨⟨340,337,338,354,66,258,0,90,82⟩,[(6,1)],[(3,0,7),(7,1,6),(5,2,3),(2,3,0),(0,7,1)]⟩
theorem node1501 : UpperPrefix a [3,7,5,2,8,4,1,0] 30 :=
  local_sound a [3,7,5,2,8,4,1,0] 30 cert1501 (by decide +kernel)

def cert1502 : Leaf := ⟨⟨340,344,346,354,74,266,0,26,83⟩,[(6,1)],[(7,1,6),(5,2,3),(2,3,0)],⟨11,134,37,28,304,112,194,448,265⟩,⟨11,134,37,28,304,112,194,448,264⟩,[⟨0,1212621131011660624958464,⟨106,254,36,254,496,240,250,496,506⟩⟩]⟩
theorem node1502 : UpperPrefix a [3,7,5,2,8,4,1,6] 30 :=
  Boolean.leaf_sound a [3,7,5,2,8,4,1,6] 30 cert1502 (by decide +kernel)

theorem node1503 : UpperPrefix a [3,7,5,2,8,4,1] 30 :=
  branch_upper a [3,7,5,2,8,4,1] 30 (by decide) (fin9_cases _
  node1501
  (invalid_upper a [3,7,5,2,8,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,1,5] 30 (by decide +kernel))
  node1502
  (invalid_upper a [3,7,5,2,8,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,1,8] 30 (by decide +kernel)))

theorem node1504 : UpperPrefix a [3,7,5,2,8,4] 30 :=
  branch_upper a [3,7,5,2,8,4] 30 (by decide) (fin9_cases _
  node1500
  node1503
  (invalid_upper a [3,7,5,2,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,4,8] 30 (by decide +kernel)))

theorem node1505 : UpperPrefix a [3,7,5,2,8] 30 :=
  branch_upper a [3,7,5,2,8] 30 (by decide) (fin9_cases _
  node1494
  node1497
  (invalid_upper a [3,7,5,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,3] 30 (by decide +kernel))
  node1504
  (invalid_upper a [3,7,5,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,8,8] 30 (by decide +kernel)))

theorem node1506 : UpperPrefix a [3,7,5,2] 30 :=
  branch_upper a [3,7,5,2] 30 (by decide) (fin9_cases _
  node1478
  node1488
  (invalid_upper a [3,7,5,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,2,5] 30 (by decide +kernel))
  node1493
  (invalid_upper a [3,7,5,2,7] 30 (by decide +kernel))
  node1505)

def cert1507 : Leaf := ⟨⟨52,57,0,37,0,157,317,61,53⟩,[(2,4),(4,2)],[(7,1,5),(1,5,2),(1,5,4)],⟨11,134,37,88,49,98,468,404,284⟩,⟨11,134,37,88,49,98,192,384,264⟩,[⟨6,1247959131201873961293065,⟨395,150,53,415,53,34,128,385,395⟩⟩,⟨8,1181748227592894645353,⟨63,150,61,127,61,127,255,150,61⟩⟩]⟩
theorem node1507 : UpperPrefix a [3,7,5,6,0,1] 30 :=
  Boolean.leaf_sound a [3,7,5,6,0,1] 30 cert1507 (by decide +kernel)

def cert1508 : Leaf := ⟨⟨176,57,0,35,0,27,315,59,51⟩,[(2,4),(4,2)],[],⟨11,134,37,88,49,100,466,402,282⟩,⟨11,134,37,88,49,100,192,384,264⟩,[⟨2,1219570781022741145322499,⟨459,475,57,88,57,120,192,384,264⟩⟩,⟨6,1247959131201873961293065,⟨395,150,53,415,53,52,128,385,395⟩⟩,⟨8,1181748227592894645353,⟨63,150,61,127,61,127,255,150,61⟩⟩,⟨7,1213649340427826793546753,⟨319,22,317,124,317,124,64,256,296⟩⟩]⟩
theorem node1508 : UpperPrefix a [3,7,5,6,0,2] 30 :=
  Boolean.leaf_sound a [3,7,5,6,0,2] 30 cert1508 (by decide +kernel)

def cert1509 : Leaf := ⟨⟨484,361,0,0,0,0,303,111,231⟩,[(2,4),(3,5),(4,2),(5,3)],[],⟨11,134,37,88,49,112,454,390,270⟩,⟨11,134,37,88,49,112,192,384,264⟩,[⟨4,1247960428237192254461193,⟨459,134,37,463,37,100,192,385,459⟩⟩]⟩
theorem node1509 : UpperPrefix a [3,7,5,6,0,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,0,4] 30 cert1509 (by decide +kernel)

def cert1510 : Leaf := ⟨⟨308,313,0,295,0,31,0,63,55⟩,[(2,4),(4,2),(6,1)],[(7,1,6)],⟨11,134,37,88,49,352,194,404,284⟩,⟨11,134,37,88,49,352,194,384,264⟩,[⟨6,1248254279109252345789705,⟨395,150,183,415,183,439,130,385,395⟩⟩]⟩
theorem node1510 : UpperPrefix a [3,7,5,6,0,8,1] 30 :=
  Boolean.leaf_sound a [3,7,5,6,0,8,1] 30 cert1510 (by decide +kernel)

def cert1511 : Leaf := ⟨⟨500,0,0,423,0,158,0,126,246⟩,[(1,6),(2,4),(4,2),(6,1)],[],⟨11,134,37,88,49,352,196,402,282⟩,⟨11,134,37,88,49,352,196,384,264⟩,[⟨0,1247960320468560053830656,⟨490,198,36,506,48,354,198,384,424⟩⟩]⟩
theorem node1511 : UpperPrefix a [3,7,5,6,0,8,2] 30 :=
  Boolean.leaf_sound a [3,7,5,6,0,8,2] 30 cert1511 (by decide +kernel)

def cert1512 : Leaf := ⟨⟨420,297,0,0,0,143,303,47,167⟩,[(2,4),(3,6),(4,2)],[(4,6,3)],⟨11,134,37,88,49,352,208,390,270⟩,⟨11,134,37,88,49,352,208,384,264⟩,[⟨6,1248254279109252345822473,⟨395,150,183,415,183,439,150,385,395⟩⟩]⟩
theorem node1512 : UpperPrefix a [3,7,5,6,0,8,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,0,8,4] 30 cert1512 (by decide +kernel)

theorem node1513 : UpperPrefix a [3,7,5,6,0,8] 30 :=
  branch_upper a [3,7,5,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,6,0,8,0] 30 (by decide +kernel))
  node1510
  node1511
  (invalid_upper a [3,7,5,6,0,8,3] 30 (by decide +kernel))
  node1512
  (invalid_upper a [3,7,5,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,0,8,8] 30 (by decide +kernel)))

theorem node1514 : UpperPrefix a [3,7,5,6,0] 30 :=
  branch_upper a [3,7,5,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,6,0,0] 30 (by decide +kernel))
  node1507
  node1508
  (invalid_upper a [3,7,5,6,0,3] 30 (by decide +kernel))
  node1509
  (invalid_upper a [3,7,5,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,0,7] 30 (by decide +kernel))
  node1513)

def cert1515 : Leaf := ⟨⟨112,120,0,32,72,26,316,124,116⟩,[(2,5)],[(0,5,2)],⟨11,134,37,88,50,97,468,404,284⟩,⟨11,134,37,88,50,97,192,384,264⟩,[⟨7,1496991329399730638947345,⟨319,262,317,381,319,381,64,256,300⟩⟩,⟨8,1181748209725830694009,⟨63,134,61,127,63,127,255,134,61⟩⟩,⟨1,1285813291192733993533441,⟨9,132,37,472,508,101,192,384,264⟩⟩,⟨2,1210107565565399676224529,⟨59,130,57,121,59,121,192,384,296⟩⟩]⟩
theorem node1515 : UpperPrefix a [3,7,5,6,1,0] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,0] 30 cert1515 (by decide +kernel)

def cert1516 : Leaf := ⟨⟨240,112,208,162,196,145,56,112,240⟩,[],[(2,5,4),(0,6,5)],⟨11,134,37,88,50,100,193,400,280⟩,⟨11,134,37,88,50,100,193,384,264⟩,[⟨8,1184095262588056470779,⟨127,255,61,127,127,127,255,255,61⟩⟩,⟨1,1247960304846698863394817,⟨493,164,101,508,48,100,229,384,424⟩⟩,⟨3,1212468751065775787508737,⟨55,134,53,118,50,118,247,384,432⟩⟩]⟩
theorem node1516 : UpperPrefix a [3,7,5,6,1,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,2,0] 30 cert1516 (by decide +kernel)

def cert1517 : Leaf := ⟨⟨192,73,202,0,205,139,11,75,195⟩,[(3,6)],[(2,5,4),(4,6,3)],⟨11,134,37,88,50,100,208,385,265⟩,⟨11,134,37,88,50,100,208,384,264⟩,[⟨8,1184095262588056470779,⟨127,255,61,127,127,127,255,255,61⟩⟩,⟨5,1782667262435360662113329,⟨459,134,391,473,475,463,473,384,456⟩⟩]⟩
theorem node1517 : UpperPrefix a [3,7,5,6,1,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,2,4] 30 cert1517 (by decide +kernel)

def cert1518 : Leaf := ⟨⟨192,105,202,130,204,138,0,91,211⟩,[(6,7)],[(2,5,4),(8,6,6)],⟨11,134,37,88,50,100,448,401,281⟩,⟨11,134,37,88,50,100,448,384,264⟩,[⟨4,1210109878233004619695113,⟨47,230,37,111,34,102,486,486,301⟩⟩,⟨5,1323673088564700304638993,⟨459,198,69,473,475,68,448,448,456⟩⟩,⟨0,1210109871197436070855680,⟨58,254,52,88,58,100,448,448,264⟩⟩]⟩
theorem node1518 : UpperPrefix a [3,7,5,6,1,2,8] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,2,8] 30 cert1518 (by decide +kernel)

theorem node1519 : UpperPrefix a [3,7,5,6,1,2] 30 :=
  branch_upper a [3,7,5,6,1,2] 30 (by decide) (fin9_cases _
  node1516
  (invalid_upper a [3,7,5,6,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,2,3] 30 (by decide +kernel))
  node1517
  (invalid_upper a [3,7,5,6,1,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,2,7] 30 (by decide +kernel))
  node1518)

def cert1520 : Leaf := ⟨⟨84,89,88,0,77,0,285,93,85⟩,[(3,5),(5,3)],[],⟨11,134,37,88,50,112,453,389,269⟩,⟨11,134,37,88,50,112,192,384,264⟩,[⟨5,1229052478408048988130325,⟨203,455,463,89,219,89,192,384,264⟩⟩,⟨1,1233765604911856005414913,⟨493,452,493,120,56,120,192,384,296⟩⟩,⟨7,1496991329399730638947345,⟨319,262,317,381,319,381,64,256,300⟩⟩,⟨8,1181748209725830694009,⟨63,134,61,127,63,127,255,134,61⟩⟩]⟩
theorem node1520 : UpperPrefix a [3,7,5,6,1,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,4] 30 cert1520 (by decide +kernel)

def cert1521 : Leaf := ⟨⟨496,0,464,418,448,144,304,112,240⟩,[(1,7)],[(2,7,1)],⟨11,134,37,88,50,352,193,388,280⟩,⟨11,134,37,88,50,352,193,388,264⟩,[⟨0,1800458718412807785745408,⟨442,406,446,376,442,376,506,406,296⟩⟩,⟨1,1248264750292571434254337,⟨493,228,229,508,176,484,229,484,424⟩⟩,⟨3,1210402789766029127044097,⟨19,246,247,86,178,502,247,502,256⟩⟩]⟩
theorem node1521 : UpperPrefix a [3,7,5,6,1,8,0,2] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,8,0,2] 30 cert1521 (by decide +kernel)

def cert1522 : Leaf := ⟨⟨448,361,328,259,329,9,280,77,69⟩,[],[],⟨11,134,37,88,50,352,193,400,268⟩,⟨11,134,37,88,50,352,193,400,264⟩,[⟨1,1252682671329568508608513,⟨493,164,357,508,48,356,485,400,424⟩⟩,⟨2,1210109911659414714057747,⟨91,251,41,89,123,352,233,505,264⟩⟩,⟨4,1252608866161853858153481,⟨303,134,293,367,34,358,487,390,301⟩⟩,⟨5,1219702645293670533694483,⟨331,463,5,217,475,320,201,473,328⟩⟩,⟨7,1704775456897799139099649,⟨319,6,309,380,306,364,381,272,296⟩⟩]⟩
theorem node1522 : UpperPrefix a [3,7,5,6,1,8,0,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,8,0,4] 30 cert1522 (by decide +kernel)

theorem node1523 : UpperPrefix a [3,7,5,6,1,8,0] 30 :=
  branch_upper a [3,7,5,6,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,6,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,0,1] 30 (by decide +kernel))
  node1521
  (invalid_upper a [3,7,5,6,1,8,0,3] 30 (by decide +kernel))
  node1522
  (invalid_upper a [3,7,5,6,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,0,8] 30 (by decide +kernel)))

def cert1524 : Leaf := ⟨⟨148,0,218,134,140,159,0,31,151⟩,[(1,6),(6,1)],[],⟨11,134,37,88,50,352,196,401,281⟩,⟨11,134,37,88,50,352,196,384,264⟩,[⟨5,1323665756704506945504281,⟨459,198,5,475,475,322,198,384,393⟩⟩,⟨6,1247959131203798102475785,⟨395,134,53,411,50,306,134,384,393⟩⟩,⟨8,1181781700225008698425,⟨75,198,61,95,127,127,198,128,9⟩⟩,⟨0,1210107601314854170821632,⟨74,198,60,90,122,378,198,384,264⟩⟩]⟩
theorem node1524 : UpperPrefix a [3,7,5,6,1,8,2] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,8,2] 30 cert1524 (by decide +kernel)

def cert1525 : Leaf := ⟨⟨228,97,194,0,196,134,294,110,230⟩,[(3,6)],[(3,0,7),(4,6,3),(0,7,1)],⟨11,134,37,88,50,352,208,385,268⟩,⟨11,134,37,88,50,352,208,385,264⟩,[⟨8,1181745671434432185465,⟨11,134,61,95,63,127,223,129,9⟩⟩]⟩
theorem node1525 : UpperPrefix a [3,7,5,6,1,8,4,0] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,8,4,0] 30 cert1525 (by decide +kernel)

def cert1526 : Leaf := ⟨⟨480,0,458,0,456,138,298,107,227⟩,[(1,7),(3,6)],[(4,6,3),(2,7,1)],⟨11,134,37,88,50,352,208,388,265⟩,⟨11,134,37,88,50,352,208,388,264⟩,[⟨0,1210109911672621739607040,⟨90,254,44,88,122,376,250,510,264⟩⟩]⟩
theorem node1526 : UpperPrefix a [3,7,5,6,1,8,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,6,1,8,4,2] 30 cert1526 (by decide +kernel)

theorem node1527 : UpperPrefix a [3,7,5,6,1,8,4] 30 :=
  branch_upper a [3,7,5,6,1,8,4] 30 (by decide) (fin9_cases _
  node1525
  (invalid_upper a [3,7,5,6,1,8,4,1] 30 (by decide +kernel))
  node1526
  (invalid_upper a [3,7,5,6,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,4,8] 30 (by decide +kernel)))

theorem node1528 : UpperPrefix a [3,7,5,6,1,8] 30 :=
  branch_upper a [3,7,5,6,1,8] 30 (by decide) (fin9_cases _
  node1523
  (invalid_upper a [3,7,5,6,1,8,1] 30 (by decide +kernel))
  node1524
  (invalid_upper a [3,7,5,6,1,8,3] 30 (by decide +kernel))
  node1527
  (invalid_upper a [3,7,5,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,8,8] 30 (by decide +kernel)))

theorem node1529 : UpperPrefix a [3,7,5,6,1] 30 :=
  branch_upper a [3,7,5,6,1] 30 (by decide) (fin9_cases _
  node1515
  (invalid_upper a [3,7,5,6,1,1] 30 (by decide +kernel))
  node1519
  (invalid_upper a [3,7,5,6,1,3] 30 (by decide +kernel))
  node1520
  (invalid_upper a [3,7,5,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,1,7] 30 (by decide +kernel))
  node1528)

def cert1530 : Leaf := ⟨⟨212,88,0,134,0,158,286,94,214⟩,[(2,5),(4,2)],[(5,2,4),(0,5,2),(0,5,4)],⟨11,134,37,88,52,97,466,402,282⟩,⟨11,134,37,88,52,97,192,384,264⟩,[⟨8,1181748227592894645353,⟨63,150,61,127,61,127,255,150,61⟩⟩]⟩
theorem node1530 : UpperPrefix a [3,7,5,6,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,6,2,0] 30 cert1530 (by decide +kernel)

def cert1531 : Leaf := ⟨⟨84,89,90,5,0,157,28,93,85⟩,[(4,2)],[(7,1,5),(5,2,4),(1,5,2)],⟨11,134,37,88,52,98,193,400,280⟩,⟨11,134,37,88,52,98,193,384,264⟩,[⟨8,1184094717503019517163,⟨127,255,61,127,61,127,255,255,61⟩⟩]⟩
theorem node1531 : UpperPrefix a [3,7,5,6,2,1,0] 30 :=
  Boolean.leaf_sound a [3,7,5,6,2,1,0] 30 cert1531 (by decide +kernel)

def cert1532 : Local := ⟨⟨324,329,330,0,0,397,269,77,69⟩,[(3,6),(4,2)],[(7,1,5),(5,2,4),(1,5,2),(4,6,3)]⟩
theorem node1532 : UpperPrefix a [3,7,5,6,2,1,4] 30 :=
  local_sound a [3,7,5,6,2,1,4] 30 cert1532 (by decide +kernel)

def cert1533 : Local := ⟨⟨84,89,90,5,0,157,0,93,85⟩,[(4,2),(6,7)],[(7,1,5),(5,2,4),(1,5,2),(8,6,6)]⟩
theorem node1533 : UpperPrefix a [3,7,5,6,2,1,8] 30 :=
  local_sound a [3,7,5,6,2,1,8] 30 cert1533 (by decide +kernel)

theorem node1534 : UpperPrefix a [3,7,5,6,2,1] 30 :=
  branch_upper a [3,7,5,6,2,1] 30 (by decide) (fin9_cases _
  node1531
  (invalid_upper a [3,7,5,6,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,1,3] 30 (by decide +kernel))
  node1532
  (invalid_upper a [3,7,5,6,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,1,7] 30 (by decide +kernel))
  node1533)

def cert1535 : Leaf := ⟨⟨452,329,474,0,0,0,271,79,199⟩,[(3,5),(4,2),(5,3)],[(5,2,4)],⟨11,134,37,88,52,112,451,387,267⟩,⟨11,134,37,88,52,112,192,384,264⟩,[⟨4,1252729001652238716775433,⟨459,198,487,459,230,98,192,384,457⟩⟩]⟩
theorem node1535 : UpperPrefix a [3,7,5,6,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,2,4] 30 cert1535 (by decide +kernel)

#print axioms node1535
end Delivery.FiniteExclusion.Sharp3x6
