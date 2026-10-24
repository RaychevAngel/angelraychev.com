import RegularNineSharp3x6Base
import RegularNineSharp3x6C023
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert1536 : Leaf := ⟨⟨452,329,456,385,0,137,266,73,209⟩,[(4,2)],[(5,2,4),(1,7,6)],⟨11,134,37,88,52,352,193,386,280⟩,⟨11,134,37,88,52,352,193,386,264⟩,[⟨4,1212771475987539340553481,⟨11,230,231,79,230,487,231,487,495⟩⟩,⟨2,1323453675196364022088705,⟨491,194,225,376,376,352,225,386,296⟩⟩]⟩
theorem node1536 : UpperPrefix a [3,7,5,6,2,8,0,1] 30 :=
  Boolean.leaf_sound a [3,7,5,6,2,8,0,1] 30 cert1536 (by decide +kernel)

def cert1537 : Leaf := ⟨⟨388,264,458,391,0,142,286,14,134⟩,[(4,2)],[(5,2,4)],⟨11,134,37,88,52,352,193,400,266⟩,⟨11,134,37,88,52,352,193,400,264⟩,[⟨4,1252608866161853858153481,⟨303,134,293,367,36,358,487,390,301⟩⟩,⟨0,1252719546627670418664448,⟨426,150,438,506,182,352,480,402,424⟩⟩,⟨6,1252718391172891021421577,⟨395,150,439,411,182,288,385,402,393⟩⟩]⟩
theorem node1537 : UpperPrefix a [3,7,5,6,2,8,0,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,2,8,0,4] 30 cert1537 (by decide +kernel)

theorem node1538 : UpperPrefix a [3,7,5,6,2,8,0] 30 :=
  branch_upper a [3,7,5,6,2,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,6,2,8,0,0] 30 (by decide +kernel))
  node1536
  (invalid_upper a [3,7,5,6,2,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,0,3] 30 (by decide +kernel))
  node1537
  (invalid_upper a [3,7,5,6,2,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,0,8] 30 (by decide +kernel)))

def cert1539 : Leaf := ⟨⟨84,345,90,6,0,31,0,95,87⟩,[(4,2),(6,1)],[(7,1,6),(5,2,4)],⟨11,134,37,88,52,352,194,401,281⟩,⟨11,134,37,88,52,352,194,384,264⟩,[⟨8,1181781700498003330115,⟨75,223,61,89,60,125,203,128,8⟩⟩,⟨0,1210107601312923851424768,⟨74,222,52,88,52,352,202,384,264⟩⟩]⟩
theorem node1539 : UpperPrefix a [3,7,5,6,2,8,1] 30 :=
  Boolean.leaf_sound a [3,7,5,6,2,8,1] 30 cert1539 (by decide +kernel)

def cert1540 : Leaf := ⟨⟨388,265,458,0,0,143,271,15,135⟩,[(3,6),(4,2)],[(5,2,4),(4,6,3)],⟨11,134,37,88,52,352,208,387,267⟩,⟨11,134,37,88,52,352,208,384,264⟩,[⟨6,1252727614544927876197385,⟨395,150,439,411,182,288,146,384,393⟩⟩]⟩
theorem node1540 : UpperPrefix a [3,7,5,6,2,8,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,2,8,4] 30 cert1540 (by decide +kernel)

theorem node1541 : UpperPrefix a [3,7,5,6,2,8] 30 :=
  branch_upper a [3,7,5,6,2,8] 30 (by decide) (fin9_cases _
  node1538
  node1539
  (invalid_upper a [3,7,5,6,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,3] 30 (by decide +kernel))
  node1540
  (invalid_upper a [3,7,5,6,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,8,8] 30 (by decide +kernel)))

theorem node1542 : UpperPrefix a [3,7,5,6,2] 30 :=
  branch_upper a [3,7,5,6,2] 30 (by decide) (fin9_cases _
  node1530
  node1534
  (invalid_upper a [3,7,5,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,3] 30 (by decide +kernel))
  node1535
  (invalid_upper a [3,7,5,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,2,7] 30 (by decide +kernel))
  node1541)

def cert1543 : Local := ⟨⟨372,376,0,292,76,286,0,124,116⟩,[(2,5),(6,1)],[(7,1,6),(0,5,2),(1,6,5)]⟩
theorem node1543 : UpperPrefix a [3,7,5,6,8,0,1] 30 :=
  local_sound a [3,7,5,6,8,0,1] 30 cert1543 (by decide +kernel)

def cert1544 : Leaf := ⟨⟨404,0,0,422,206,414,0,30,150⟩,[(1,6),(2,5),(6,1)],[(0,5,2)],⟨11,134,37,88,304,97,196,402,282⟩,⟨11,134,37,88,304,97,196,384,264⟩,[⟨5,1247960319026000798188553,⟨459,198,5,475,272,67,198,384,393⟩⟩,⟨6,1248106705154188768228617,⟨395,134,37,415,439,39,134,385,395⟩⟩]⟩
theorem node1544 : UpperPrefix a [3,7,5,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,0,2] 30 cert1544 (by decide +kernel)

def cert1545 : Leaf := ⟨⟨228,96,0,0,206,134,294,102,230⟩,[(2,5),(3,6)],[(8,4,6),(0,5,2),(4,6,3)],⟨11,134,37,88,304,97,208,390,270⟩,⟨11,134,37,88,304,97,208,384,264⟩,[⟨3,1210255571617188897104897,⟨103,134,37,210,502,101,210,384,320⟩⟩]⟩
theorem node1545 : UpperPrefix a [3,7,5,6,8,0,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,0,4] 30 cert1545 (by decide +kernel)

theorem node1546 : UpperPrefix a [3,7,5,6,8,0] 30 :=
  branch_upper a [3,7,5,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,6,8,0,0] 30 (by decide +kernel))
  node1543
  node1544
  (invalid_upper a [3,7,5,6,8,0,3] 30 (by decide +kernel))
  node1545
  (invalid_upper a [3,7,5,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,0,8] 30 (by decide +kernel)))

def cert1547 : Leaf := ⟨⟨36,33,2,293,69,133,316,61,53⟩,[],[(7,1,5),(1,5,2)],⟨11,134,37,88,304,98,193,404,284⟩,⟨11,134,37,88,304,98,193,384,264⟩,[⟨6,1248106705154188759807241,⟨395,134,37,415,439,34,129,385,395⟩⟩,⟨3,1210107567834717605889025,⟨39,134,37,118,304,102,231,400,304⟩⟩,⟨4,1210107567816027051230217,⟨47,134,37,111,292,102,231,390,301⟩⟩,⟨8,1181748202497388151817,⟨47,134,37,127,52,102,231,134,45⟩⟩]⟩
theorem node1547 : UpperPrefix a [3,7,5,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,1,0] 30 cert1547 (by decide +kernel)

def cert1548 : Local := ⟨⟨368,0,346,289,73,413,0,121,113⟩,[(1,6),(6,1)],[(7,1,5),(1,5,2),(2,6,5)]⟩
theorem node1548 : UpperPrefix a [3,7,5,6,8,1,2] 30 :=
  local_sound a [3,7,5,6,8,1,2] 30 cert1548 (by decide +kernel)

def cert1549 : Leaf := ⟨⟨36,41,10,0,77,141,301,45,37⟩,[(3,6)],[(7,1,5),(8,4,6),(1,5,2),(4,6,3)],⟨11,134,37,88,304,98,208,389,269⟩,⟨11,134,37,88,304,98,208,384,264⟩,[⟨6,1248106705154188759840009,⟨395,134,37,415,439,34,150,385,395⟩⟩]⟩
theorem node1549 : UpperPrefix a [3,7,5,6,8,1,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,1,4] 30 cert1549 (by decide +kernel)

theorem node1550 : UpperPrefix a [3,7,5,6,8,1] 30 :=
  branch_upper a [3,7,5,6,8,1] 30 (by decide) (fin9_cases _
  node1547
  (invalid_upper a [3,7,5,6,8,1,1] 30 (by decide +kernel))
  node1548
  (invalid_upper a [3,7,5,6,8,1,3] 30 (by decide +kernel))
  node1549
  (invalid_upper a [3,7,5,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,1,8] 30 (by decide +kernel)))

def cert1551 : Leaf := ⟨⟨164,32,2,294,70,3,318,62,54⟩,[],[(0,6,5)],⟨11,134,37,88,304,100,193,402,282⟩,⟨11,134,37,88,304,100,193,384,264⟩,[⟨6,1248106705154188759807241,⟨395,134,37,415,439,36,129,385,395⟩⟩,⟨7,1213649342701625442305025,⟨319,22,317,124,312,124,381,272,312⟩⟩,⟨3,1210107567834717605889025,⟨39,134,37,118,304,102,231,400,304⟩⟩,⟨4,1210107567816027051230217,⟨47,134,37,111,292,102,231,390,301⟩⟩,⟨8,1181748202497388151817,⟨47,134,37,127,52,102,231,134,45⟩⟩]⟩
theorem node1551 : UpperPrefix a [3,7,5,6,8,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,2,0] 30 cert1551 (by decide +kernel)

def cert1552 : Leaf := ⟨⟨304,313,282,289,73,283,0,57,49⟩,[(6,1)],[(7,1,6)],⟨11,134,37,88,304,100,194,401,281⟩,⟨11,134,37,88,304,100,194,384,264⟩,[⟨2,1427760752655225214469187,⟨459,475,505,473,440,505,459,384,392⟩⟩,⟨6,1248106705154188759807241,⟨395,134,37,415,439,36,130,385,395⟩⟩,⟨1,1229033924705955882205185,⟨9,404,445,88,312,508,192,384,264⟩⟩]⟩
theorem node1552 : UpperPrefix a [3,7,5,6,8,2,1] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,2,1] 30 cert1552 (by decide +kernel)

def cert1553 : Leaf := ⟨⟨160,41,138,0,139,139,299,43,163⟩,[(3,6)],[(8,4,6),(4,6,3)],⟨11,134,37,88,304,100,208,387,267⟩,⟨11,134,37,88,304,100,208,384,264⟩,[⟨6,1255236371738952379464969,⟨395,150,439,415,439,182,150,385,395⟩⟩,⟨2,1224302442935250810045443,⟨459,475,505,88,312,120,216,384,264⟩⟩]⟩
theorem node1553 : UpperPrefix a [3,7,5,6,8,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,2,4] 30 cert1553 (by decide +kernel)

theorem node1554 : UpperPrefix a [3,7,5,6,8,2] 30 :=
  branch_upper a [3,7,5,6,8,2] 30 (by decide) (fin9_cases _
  node1551
  node1552
  (invalid_upper a [3,7,5,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,2,3] 30 (by decide +kernel))
  node1553
  (invalid_upper a [3,7,5,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,2,8] 30 (by decide +kernel)))

def cert1555 : Leaf := ⟨⟨388,265,394,0,207,0,271,15,135⟩,[(3,5),(5,3)],[],⟨11,134,37,88,304,112,199,391,271⟩,⟨11,134,37,88,304,112,192,384,264⟩,[⟨4,1248108290420158082610441,⟨459,134,39,463,487,230,192,385,459⟩⟩,⟨5,1229052478408046840646661,⟨203,455,463,88,280,88,192,384,264⟩⟩,⟨6,1248106705154188759823625,⟨395,134,39,415,439,182,128,385,395⟩⟩]⟩
theorem node1555 : UpperPrefix a [3,7,5,6,8,4] 30 :=
  Boolean.leaf_sound a [3,7,5,6,8,4] 30 cert1555 (by decide +kernel)

theorem node1556 : UpperPrefix a [3,7,5,6,8] 30 :=
  branch_upper a [3,7,5,6,8] 30 (by decide) (fin9_cases _
  node1546
  node1550
  node1554
  (invalid_upper a [3,7,5,6,8,3] 30 (by decide +kernel))
  node1555
  (invalid_upper a [3,7,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,8,8] 30 (by decide +kernel)))

theorem node1557 : UpperPrefix a [3,7,5,6] 30 :=
  branch_upper a [3,7,5,6] 30 (by decide) (fin9_cases _
  node1514
  node1529
  node1542
  (invalid_upper a [3,7,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,6,7] 30 (by decide +kernel))
  node1556)

def cert1558 : Local := ⟨⟨368,0,0,97,0,413,0,121,113⟩,[(1,6),(2,4),(4,2),(6,1)],[(7,1,5),(1,5,2),(1,5,4),(2,6,5)]⟩
theorem node1558 : UpperPrefix a [3,7,5,8,0,1,2] 30 :=
  local_sound a [3,7,5,8,0,1,2] 30 cert1558 (by decide +kernel)

def cert1559 : Leaf := ⟨⟨372,113,0,101,0,149,37,117,117⟩,[(2,4),(4,2)],[(7,1,5),(1,5,2),(1,5,4)],⟨11,134,37,280,49,98,208,452,332⟩,⟨11,134,37,280,49,98,208,384,264⟩,[⟨3,1210181562768587259942401,⟨247,246,119,502,119,98,246,416,482⟩⟩,⟨8,1181784055716062200833,⟨127,246,53,28,53,98,246,128,8⟩⟩]⟩
theorem node1559 : UpperPrefix a [3,7,5,8,0,1,4] 30 :=
  Boolean.leaf_sound a [3,7,5,8,0,1,4] 30 cert1559 (by decide +kernel)

theorem node1560 : UpperPrefix a [3,7,5,8,0,1] 30 :=
  branch_upper a [3,7,5,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,1,1] 30 (by decide +kernel))
  node1558
  (invalid_upper a [3,7,5,8,0,1,3] 30 (by decide +kernel))
  node1559
  (invalid_upper a [3,7,5,8,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,1,8] 30 (by decide +kernel)))

def cert1561 : Leaf := ⟨⟨368,377,0,99,0,283,0,123,115⟩,[(2,4),(4,2),(6,1)],[(7,1,6)],⟨11,134,37,280,49,100,194,464,344⟩,⟨11,134,37,280,49,100,194,384,264⟩,[⟨2,1465613471494479361868867,⟨459,475,505,408,505,505,459,384,264⟩⟩]⟩
theorem node1561 : UpperPrefix a [3,7,5,8,0,2,1] 30 :=
  Boolean.leaf_sound a [3,7,5,8,0,2,1] 30 cert1561 (by decide +kernel)

def cert1562 : Leaf := ⟨⟨464,344,0,194,0,411,266,90,210⟩,[(2,4),(4,2)],[],⟨11,134,37,280,49,100,208,450,330⟩,⟨11,134,37,280,49,100,208,384,264⟩,[⟨5,1441955899393945243765809,⟨459,134,391,473,475,463,473,384,328⟩⟩,⟨0,1441955900519845150608384,⟨458,134,422,472,506,494,472,384,328⟩⟩,⟨2,1224302731165616224338947,⟨459,475,505,344,505,120,216,384,264⟩⟩]⟩
theorem node1562 : UpperPrefix a [3,7,5,8,0,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,8,0,2,4] 30 cert1562 (by decide +kernel)

theorem node1563 : UpperPrefix a [3,7,5,8,0,2] 30 :=
  branch_upper a [3,7,5,8,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,0,2,0] 30 (by decide +kernel))
  node1561
  (invalid_upper a [3,7,5,8,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,2,3] 30 (by decide +kernel))
  node1562
  (invalid_upper a [3,7,5,8,0,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,2,8] 30 (by decide +kernel)))

def cert1564 : Leaf := ⟨⟨356,361,0,103,0,271,0,111,103⟩,[(2,4),(4,2),(6,1)],[(7,1,6)],⟨11,134,37,280,49,112,194,452,332⟩,⟨11,134,37,280,49,112,194,384,264⟩,[⟨4,1247965093966406210295049,⟨459,198,101,463,101,100,194,449,459⟩⟩]⟩
theorem node1564 : UpperPrefix a [3,7,5,8,0,4,1] 30 :=
  Boolean.leaf_sound a [3,7,5,8,0,4,1] 30 cert1564 (by decide +kernel)

def cert1565 : Leaf := ⟨⟨468,0,0,199,0,399,0,95,215⟩,[(1,6),(2,4),(4,2),(6,1)],[],⟨11,134,37,280,49,112,196,450,330⟩,⟨11,134,37,280,49,112,196,384,264⟩,[⟨5,1385785239430322193468453,⟨459,455,463,280,409,475,455,384,264⟩⟩]⟩
theorem node1565 : UpperPrefix a [3,7,5,8,0,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,8,0,4,2] 30 cert1565 (by decide +kernel)

theorem node1566 : UpperPrefix a [3,7,5,8,0,4] 30 :=
  branch_upper a [3,7,5,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,0,4,0] 30 (by decide +kernel))
  node1564
  node1565
  (invalid_upper a [3,7,5,8,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,4,8] 30 (by decide +kernel)))

theorem node1567 : UpperPrefix a [3,7,5,8,0] 30 :=
  branch_upper a [3,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,0,0] 30 (by decide +kernel))
  node1560
  node1563
  (invalid_upper a [3,7,5,8,0,3] 30 (by decide +kernel))
  node1566
  (invalid_upper a [3,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,0,8] 30 (by decide +kernel)))

def cert1568 : Leaf := ⟨⟨500,0,0,228,460,412,0,124,244⟩,[(1,6),(2,5),(6,1)],[(0,5,2)],⟨11,134,37,280,50,97,196,464,344⟩,⟨11,134,37,280,50,97,196,384,264⟩,[⟨1,1323666064251103382601729,⟨493,228,101,472,508,101,228,384,392⟩⟩]⟩
theorem node1568 : UpperPrefix a [3,7,5,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,0,2] 30 cert1568 (by decide +kernel)

def cert1569 : Leaf := ⟨⟨496,0,0,224,456,408,296,120,240⟩,[(1,7),(2,5)],[(0,5,2),(2,7,1)],⟨11,134,37,280,50,97,208,388,328⟩,⟨11,134,37,280,50,97,208,388,264⟩,[⟨1,1782003180809791405817857,⟨493,132,421,472,508,493,472,388,328⟩⟩]⟩
theorem node1569 : UpperPrefix a [3,7,5,8,1,0,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,0,4,2] 30 cert1569 (by decide +kernel)

def cert1570 : Leaf := ⟨⟨436,304,0,164,388,404,292,52,180⟩,[(2,5)],[(0,5,2)],⟨11,134,37,280,50,97,208,448,268⟩,⟨11,134,37,280,50,97,208,448,264⟩,[⟨1,1444981166583117897793537,⟨493,132,421,472,508,493,472,456,456⟩⟩,⟨3,1212542733838565806179841,⟨247,246,119,464,118,119,208,448,448⟩⟩,⟨6,1805124589206136981325043,⟨267,399,317,285,319,319,415,395,264⟩⟩]⟩
theorem node1570 : UpperPrefix a [3,7,5,8,1,0,4,6] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,0,4,6] 30 cert1570 (by decide +kernel)

theorem node1571 : UpperPrefix a [3,7,5,8,1,0,4] 30 :=
  branch_upper a [3,7,5,8,1,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,1,0,4,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,4,1] 30 (by decide +kernel))
  node1569
  (invalid_upper a [3,7,5,8,1,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,4,5] 30 (by decide +kernel))
  node1570
  (invalid_upper a [3,7,5,8,1,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,4,8] 30 (by decide +kernel)))

theorem node1572 : UpperPrefix a [3,7,5,8,1,0] 30 :=
  branch_upper a [3,7,5,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,1] 30 (by decide +kernel))
  node1568
  (invalid_upper a [3,7,5,8,1,0,3] 30 (by decide +kernel))
  node1571
  (invalid_upper a [3,7,5,8,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,0,8] 30 (by decide +kernel)))

def cert1573 : Leaf := ⟨⟨464,96,194,194,196,131,282,90,210⟩,[],[(2,5,4),(0,6,5)],⟨11,134,37,280,50,100,193,464,344⟩,⟨11,134,37,280,50,100,193,384,264⟩,[⟨5,1323666171035672663557137,⟨459,134,69,473,475,68,193,384,456⟩⟩,⟨3,1210107567542247512638465,⟨3,134,53,272,50,118,247,384,256⟩⟩,⟨8,1181747927619411674113,⟨11,134,53,24,50,118,247,128,8⟩⟩,⟨4,1210107567534552004985857,⟨11,134,37,264,34,102,231,384,264⟩⟩]⟩
theorem node1573 : UpperPrefix a [3,7,5,8,1,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,2,0] 30 cert1573 (by decide +kernel)

def cert1574 : Leaf := ⟨⟨336,337,338,66,452,274,258,90,82⟩,[],[(3,0,7),(2,5,4),(0,7,1)],⟨11,134,37,280,50,100,208,385,328⟩,⟨11,134,37,280,50,100,208,385,264⟩,[⟨5,1782667262435360662113329,⟨459,134,391,473,475,463,473,385,456⟩⟩,⟨7,1662274158270430787404817,⟨11,6,293,285,319,364,381,257,264⟩⟩]⟩
theorem node1574 : UpperPrefix a [3,7,5,8,1,2,4,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,2,4,0] 30 cert1574 (by decide +kernel)

def cert1575 : Leaf := ⟨⟨272,273,274,3,261,275,259,19,19⟩,[],[(2,5,4)],⟨11,134,37,280,50,100,208,448,265⟩,⟨11,134,37,280,50,100,208,448,264⟩,[⟨3,1212542733906735518713345,⟨247,246,119,464,114,116,208,448,448⟩⟩,⟨5,1784991552188648065616945,⟨459,134,391,473,475,463,473,456,456⟩⟩,⟨6,2414309865496321213891827,⟨267,399,317,285,319,319,415,395,264⟩⟩,⟨7,1657551796291298611692563,⟨287,319,301,285,319,364,381,364,264⟩⟩]⟩
theorem node1575 : UpperPrefix a [3,7,5,8,1,2,4,6] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,2,4,6] 30 cert1575 (by decide +kernel)

theorem node1576 : UpperPrefix a [3,7,5,8,1,2,4] 30 :=
  branch_upper a [3,7,5,8,1,2,4] 30 (by decide) (fin9_cases _
  node1574
  (invalid_upper a [3,7,5,8,1,2,4,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,4,5] 30 (by decide +kernel))
  node1575
  (invalid_upper a [3,7,5,8,1,2,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,4,8] 30 (by decide +kernel)))

theorem node1577 : UpperPrefix a [3,7,5,8,1,2] 30 :=
  branch_upper a [3,7,5,8,1,2] 30 (by decide) (fin9_cases _
  node1573
  (invalid_upper a [3,7,5,8,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,3] 30 (by decide +kernel))
  node1576
  (invalid_upper a [3,7,5,8,1,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,2,8] 30 (by decide +kernel)))

def cert1578 : Leaf := ⟨⟨464,0,474,192,456,394,280,88,208⟩,[(1,7)],[(2,7,1)],⟨11,134,37,280,50,112,193,388,328⟩,⟨11,134,37,280,50,112,193,388,264⟩,[⟨0,1663491643383990533032960,⟨10,158,446,280,314,376,506,414,264⟩⟩,⟨5,1498229980019402640264213,⟨459,455,463,345,475,345,451,455,264⟩⟩,⟨1,1384890555454248677539841,⟨457,452,493,280,440,376,449,452,264⟩⟩]⟩
theorem node1578 : UpperPrefix a [3,7,5,8,1,4,0,2] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,4,0,2] 30 cert1578 (by decide +kernel)

def cert1579 : Leaf := ⟨⟨260,65,18,39,197,135,270,15,51⟩,[],[],⟨11,134,37,280,50,112,193,448,268⟩,⟨11,134,37,280,50,112,193,448,268⟩,[⟨3,1210107572054780672050177,⟨19,182,53,272,50,118,247,502,260⟩⟩,⟨4,1212549615159096061854985,⟨203,198,101,459,34,96,193,451,463⟩⟩,⟨5,1212549614034295666640137,⟨203,198,69,475,18,80,193,451,463⟩⟩,⟨6,1493448401334532247127057,⟨267,390,301,285,319,317,129,384,268⟩⟩,⟨7,1492268962635319442670609,⟨267,262,301,285,319,381,65,320,268⟩⟩,⟨8,1181752440152571085825,⟨27,182,53,24,50,118,247,246,12⟩⟩]⟩
theorem node1579 : UpperPrefix a [3,7,5,8,1,4,0,6,2] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,4,0,6,2] 30 cert1579 (by decide +kernel)

theorem node1580 : UpperPrefix a [3,7,5,8,1,4,0,6] 30 :=
  branch_upper a [3,7,5,8,1,4,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,1,4,0,6,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,6,1] 30 (by decide +kernel))
  node1579
  (invalid_upper a [3,7,5,8,1,4,0,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,6,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,6,8] 30 (by decide +kernel)))

theorem node1581 : UpperPrefix a [3,7,5,8,1,4,0] 30 :=
  branch_upper a [3,7,5,8,1,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,1,4,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,1] 30 (by decide +kernel))
  node1578
  (invalid_upper a [3,7,5,8,1,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,5] 30 (by decide +kernel))
  node1580
  (invalid_upper a [3,7,5,8,1,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,0,8] 30 (by decide +kernel)))

def cert1582 : Leaf := ⟨⟨336,0,346,67,461,397,0,89,81⟩,[(1,6),(6,1)],[],⟨11,134,37,280,50,112,196,449,329⟩,⟨11,134,37,280,50,112,196,384,264⟩,[⟨2,1361518440640866127184913,⟨11,130,425,281,443,505,192,384,264⟩⟩,⟨5,1461490677108826193300533,⟨459,455,463,409,475,475,455,384,264⟩⟩,⟨7,1360042701114969376687121,⟨11,6,301,285,319,381,68,256,264⟩⟩,⟨1,1214876157276246615523329,⟨457,196,485,312,112,112,196,384,264⟩⟩]⟩
theorem node1582 : UpperPrefix a [3,7,5,8,1,4,2] 30 :=
  Boolean.leaf_sound a [3,7,5,8,1,4,2] 30 cert1582 (by decide +kernel)

theorem node1583 : UpperPrefix a [3,7,5,8,1,4] 30 :=
  branch_upper a [3,7,5,8,1,4] 30 (by decide) (fin9_cases _
  node1581
  (invalid_upper a [3,7,5,8,1,4,1] 30 (by decide +kernel))
  node1582
  (invalid_upper a [3,7,5,8,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,4,8] 30 (by decide +kernel)))

theorem node1584 : UpperPrefix a [3,7,5,8,1] 30 :=
  branch_upper a [3,7,5,8,1] 30 (by decide) (fin9_cases _
  node1572
  (invalid_upper a [3,7,5,8,1,1] 30 (by decide +kernel))
  node1577
  (invalid_upper a [3,7,5,8,1,3] 30 (by decide +kernel))
  node1583
  (invalid_upper a [3,7,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,1,8] 30 (by decide +kernel)))

def cert1585 : Leaf := ⟨⟨468,344,0,198,0,150,22,94,214⟩,[(2,5),(4,2)],[(5,2,4),(0,5,2),(0,5,4)],⟨11,134,37,280,52,97,210,466,346⟩,⟨11,134,37,280,52,97,192,384,264⟩,[⟨3,1210107601350374632719361,⟨119,214,53,272,52,117,192,384,256⟩⟩,⟨8,1181781735746531755009,⟨127,214,53,24,52,117,192,128,8⟩⟩]⟩
theorem node1585 : UpperPrefix a [3,7,5,8,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,2,0] 30 cert1585 (by decide +kernel)

def cert1586 : Leaf := ⟨⟨340,321,322,69,0,389,284,93,85⟩,[(4,2)],[(7,1,5),(5,2,4),(1,5,2)],⟨11,134,37,280,52,98,193,464,344⟩,⟨11,134,37,280,52,98,193,384,264⟩,[⟨3,1210107567542522390545409,⟨3,150,53,272,52,118,247,384,256⟩⟩,⟨4,1210107567534552004985857,⟨11,134,37,264,36,102,231,384,264⟩⟩]⟩
theorem node1586 : UpperPrefix a [3,7,5,8,2,1,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,2,1,0] 30 cert1586 (by decide +kernel)

def cert1587 : Leaf := ⟨⟨336,345,346,65,0,409,265,89,81⟩,[(4,2)],[(7,1,5),(5,2,4),(1,5,2)],⟨11,134,37,280,52,98,208,449,329⟩,⟨11,134,37,280,52,98,208,384,264⟩,[⟨2,1441955900555029521630241,⟨491,130,417,472,505,491,472,384,328⟩⟩]⟩
theorem node1587 : UpperPrefix a [3,7,5,8,2,1,4] 30 :=
  Boolean.leaf_sound a [3,7,5,8,2,1,4] 30 cert1587 (by decide +kernel)

theorem node1588 : UpperPrefix a [3,7,5,8,2,1] 30 :=
  branch_upper a [3,7,5,8,2,1] 30 (by decide) (fin9_cases _
  node1586
  (invalid_upper a [3,7,5,8,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,1,3] 30 (by decide +kernel))
  node1587
  (invalid_upper a [3,7,5,8,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,1,8] 30 (by decide +kernel)))

def cert1589 : Leaf := ⟨⟨452,320,466,198,0,387,266,74,194⟩,[(4,2)],[(5,2,4)],⟨11,134,37,280,52,112,193,450,330⟩,⟨11,134,37,280,52,112,193,384,264⟩,[⟨4,1252733613338257144163337,⟨459,198,487,459,230,98,449,448,457⟩⟩,⟨0,1361518440641141543021568,⟨10,158,446,282,446,506,192,384,264⟩⟩,⟨2,1214839245773700685890561,⟨459,194,481,312,112,112,449,384,264⟩⟩,⟨3,1210107567542522390545409,⟨3,150,53,272,52,118,247,384,256⟩⟩]⟩
theorem node1589 : UpperPrefix a [3,7,5,8,2,4,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,2,4,0] 30 cert1589 (by decide +kernel)

def cert1590 : Leaf := ⟨⟨324,329,346,71,0,271,0,79,71⟩,[(4,2),(6,1)],[(7,1,6),(5,2,4)],⟨11,134,37,280,52,112,194,449,329⟩,⟨11,134,37,280,52,112,194,384,264⟩,[⟨4,1255090509152846710057993,⟨459,198,487,459,230,98,194,384,457⟩⟩]⟩
theorem node1590 : UpperPrefix a [3,7,5,8,2,4,1] 30 :=
  Boolean.leaf_sound a [3,7,5,8,2,4,1] 30 cert1590 (by decide +kernel)

theorem node1591 : UpperPrefix a [3,7,5,8,2,4] 30 :=
  branch_upper a [3,7,5,8,2,4] 30 (by decide) (fin9_cases _
  node1589
  node1590
  (invalid_upper a [3,7,5,8,2,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,4,8] 30 (by decide +kernel)))

theorem node1592 : UpperPrefix a [3,7,5,8,2] 30 :=
  branch_upper a [3,7,5,8,2] 30 (by decide) (fin9_cases _
  node1585
  node1588
  (invalid_upper a [3,7,5,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,3] 30 (by decide +kernel))
  node1591
  (invalid_upper a [3,7,5,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,2,8] 30 (by decide +kernel)))

def cert1593 : Local := ⟨⟨308,312,0,36,0,286,0,60,52⟩,[(2,5),(4,5),(6,1)],[(7,1,6),(6,4,4),(0,5,2),(1,6,5)]⟩
theorem node1593 : UpperPrefix a [3,7,5,8,6,0,1] 30 :=
  local_sound a [3,7,5,8,6,0,1] 30 cert1593 (by decide +kernel)

def cert1594 : Local := ⟨⟨436,0,0,166,0,414,0,62,182⟩,[(1,6),(2,5),(4,5),(6,1)],[(6,4,4),(0,5,2)]⟩
theorem node1594 : UpperPrefix a [3,7,5,8,6,0,2] 30 :=
  local_sound a [3,7,5,8,6,0,2] 30 cert1594 (by decide +kernel)

def cert1595 : Leaf := ⟨⟨432,312,0,162,0,410,298,60,182⟩,[(2,5),(4,5)],[(6,4,4),(0,5,2)],⟨11,134,37,280,112,97,208,386,268⟩,⟨11,134,37,280,112,97,208,386,264⟩,[⟨2,1210109914032226976138371,⟨123,251,49,280,112,113,249,507,264⟩⟩]⟩
theorem node1595 : UpperPrefix a [3,7,5,8,6,0,4,1] 30 :=
  Boolean.leaf_sound a [3,7,5,8,6,0,4,1] 30 cert1595 (by decide +kernel)

def cert1596 : Local := ⟨⟨432,0,0,162,0,410,298,58,178⟩,[(1,7),(2,5),(4,5)],[(6,4,4),(0,5,2),(2,7,1)]⟩
theorem node1596 : UpperPrefix a [3,7,5,8,6,0,4,2] 30 :=
  local_sound a [3,7,5,8,6,0,4,2] 30 cert1596 (by decide +kernel)

theorem node1597 : UpperPrefix a [3,7,5,8,6,0,4] 30 :=
  branch_upper a [3,7,5,8,6,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,6,0,4,0] 30 (by decide +kernel))
  node1595
  node1596
  (invalid_upper a [3,7,5,8,6,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,4,8] 30 (by decide +kernel)))

theorem node1598 : UpperPrefix a [3,7,5,8,6,0] 30 :=
  branch_upper a [3,7,5,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,5,8,6,0,0] 30 (by decide +kernel))
  node1593
  node1594
  (invalid_upper a [3,7,5,8,6,0,3] 30 (by decide +kernel))
  node1597
  (invalid_upper a [3,7,5,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,0,8] 30 (by decide +kernel)))

def cert1599 : Leaf := ⟨⟨308,304,274,36,0,405,316,60,52⟩,[(4,5)],[(7,1,5),(6,4,4),(1,5,2)],⟨11,134,37,280,112,98,193,404,284⟩,⟨11,134,37,280,112,98,193,384,264⟩,[⟨0,1229033924705677246204928,⟨10,398,446,280,112,114,192,384,264⟩⟩,⟨3,1210107568105197466059777,⟨3,134,53,304,118,118,247,384,256⟩⟩]⟩
theorem node1599 : UpperPrefix a [3,7,5,8,6,1,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,6,1,0] 30 cert1599 (by decide +kernel)

#print axioms node1599
end Delivery.FiniteExclusion.Sharp3x6
