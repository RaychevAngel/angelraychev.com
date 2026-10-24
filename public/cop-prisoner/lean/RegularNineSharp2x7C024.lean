import RegularNineSharp2x7Base
import RegularNineSharp2x7C023
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert1536 : Leaf := ⟨⟨200,200,65,229,193,145,257,69,193⟩,[],[(5,1,3),(8,4,6),(4,6,5)],⟨7,35,140,26,304,104,208,449,325⟩,⟨7,35,140,26,304,104,208,384,260⟩,[⟨1,1214860106324235525292033,⟨501,497,236,252,304,108,208,464,308⟩⟩,⟨2,1210109871285190573164033,⟨35,35,232,26,304,104,208,464,304⟩⟩,⟨3,1214857800041351865172993,⟨471,499,196,210,304,96,208,384,260⟩⟩]⟩
theorem node1536 : UpperPrefix a [2,5,7,1,8,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,3,4] 30 cert1536 (by decide +kernel)

theorem node1537 : UpperPrefix a [2,5,7,1,8,3] 30 :=
  branch_upper a [2,5,7,1,8,3] 30 (by decide) (fin9_cases _
  node1535
  (invalid_upper a [2,5,7,1,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,3] 30 (by decide +kernel))
  node1536
  (invalid_upper a [2,5,7,1,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,8] 30 (by decide +kernel)))

def cert1538 : Leaf := ⟨⟨448,468,0,484,198,390,262,70,194⟩,[(2,7)],[(5,1,3),(3,7,2)],⟨7,35,140,26,304,112,193,392,324⟩,⟨7,35,140,26,304,112,193,392,260⟩,[⟨0,1664063492452304820110336,⟨158,446,140,158,304,500,508,396,260⟩⟩,⟨4,2178305914765661573219337,⟨455,355,461,463,288,352,453,461,452⟩⟩]⟩
theorem node1538 : UpperPrefix a [2,5,7,1,8,4,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,4,0,3] 30 cert1538 (by decide +kernel)

def cert1539 : Leaf := ⟨⟨400,404,272,420,132,388,276,20,152⟩,[],[(5,1,3)],⟨7,35,140,26,304,112,193,448,268⟩,⟨7,35,140,26,304,112,193,448,260⟩,[⟨0,1584059967917297057137664,⟨286,446,444,286,432,500,508,500,276⟩⟩,⟨1,1266859034621931632459777,⟨501,241,444,508,304,112,241,496,276⟩⟩,⟨3,1212623617069022335708933,⟨103,35,247,242,499,242,243,499,503⟩⟩,⟨6,1687065427134524569969697,⟨287,315,396,26,315,319,397,388,260⟩⟩]⟩
theorem node1539 : UpperPrefix a [2,5,7,1,8,4,0,6] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,4,0,6] 30 cert1539 (by decide +kernel)

theorem node1540 : UpperPrefix a [2,5,7,1,8,4,0] 30 :=
  branch_upper a [2,5,7,1,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,1,8,4,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,2] 30 (by decide +kernel))
  node1538
  (invalid_upper a [2,5,7,1,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,5] 30 (by decide +kernel))
  node1539
  (invalid_upper a [2,5,7,1,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,8] 30 (by decide +kernel)))

def cert1541 : Leaf := ⟨⟨456,456,0,485,201,393,0,77,201⟩,[(2,6),(6,2)],[(5,1,3)],⟨7,35,140,26,304,112,200,449,325⟩,⟨7,35,140,26,304,112,200,384,260⟩,[⟨1,1214839238657867607179265,⟨501,433,252,24,304,116,252,432,372⟩⟩,⟨4,1725851075640342806029353,⟨455,419,461,463,419,487,461,384,452⟩⟩,⟨2,1210107648767570558846465,⟨99,35,248,26,304,112,248,432,368⟩⟩]⟩
theorem node1541 : UpperPrefix a [2,5,7,1,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,4,3] 30 cert1541 (by decide +kernel)

theorem node1542 : UpperPrefix a [2,5,7,1,8,4] 30 :=
  branch_upper a [2,5,7,1,8,4] 30 (by decide) (fin9_cases _
  node1540
  (invalid_upper a [2,5,7,1,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,2] 30 (by decide +kernel))
  node1541
  (invalid_upper a [2,5,7,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,8] 30 (by decide +kernel)))

theorem node1543 : UpperPrefix a [2,5,7,1,8] 30 :=
  branch_upper a [2,5,7,1,8] 30 (by decide) (fin9_cases _
  node1534
  (invalid_upper a [2,5,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,2] 30 (by decide +kernel))
  node1537
  node1542
  (invalid_upper a [2,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,8] 30 (by decide +kernel)))

theorem node1544 : UpperPrefix a [2,5,7,1] 30 :=
  branch_upper a [2,5,7,1] 30 (by decide) (fin9_cases _
  node1519
  (invalid_upper a [2,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,2] 30 (by decide +kernel))
  node1525
  (invalid_upper a [2,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,5] 30 (by decide +kernel))
  node1533
  (invalid_upper a [2,5,7,1,7] 30 (by decide +kernel))
  node1543)

def cert1545 : Leaf := ⟨⟨504,0,336,388,0,413,284,92,216⟩,[(1,4),(4,1)],[(1,5,1),(1,5,4)],⟨7,35,140,88,49,98,472,408,284⟩,⟨7,35,140,88,49,98,192,384,260⟩,[⟨0,1323666154147174067209216,⟨6,34,460,476,508,98,192,384,260⟩⟩,⟨5,1323666153021274160366593,⟨7,3,460,476,477,66,192,384,260⟩⟩]⟩
theorem node1545 : UpperPrefix a [2,5,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,1] 30 cert1545 (by decide +kernel)

def cert1546 : Leaf := ⟨⟨184,0,51,167,0,0,311,55,179⟩,[(1,4),(4,1),(5,3)],[(6,3,5)],⟨7,35,140,88,49,104,466,402,278⟩,⟨7,35,140,88,49,104,192,384,260⟩,[⟨3,1215005518109129617449985,⟨471,499,132,210,499,96,192,384,260⟩⟩,⟨8,1181748210069345992045,⟨23,59,191,127,59,127,255,129,23⟩⟩]⟩
theorem node1546 : UpperPrefix a [2,5,7,6,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,3] 30 cert1546 (by decide +kernel)

def cert1547 : Leaf := ⟨⟨488,0,355,0,0,0,303,111,235⟩,[(1,4),(3,5),(4,1),(5,3)],[],⟨7,35,140,88,49,112,458,394,270⟩,⟨7,35,140,88,49,112,192,384,260⟩,[⟨4,1247960428237192252367881,⟨7,35,461,463,35,98,192,384,260⟩⟩]⟩
theorem node1547 : UpperPrefix a [2,5,7,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,4] 30 cert1547 (by decide +kernel)

def cert1548 : Leaf := ⟨⟨432,0,304,421,0,148,309,60,184⟩,[(1,4),(4,1)],[],⟨7,35,140,88,49,352,194,408,284⟩,⟨7,35,140,88,49,352,194,384,260⟩,[⟨1,1550782037370540531908609,⟨21,53,428,508,53,492,508,384,260⟩⟩,⟨0,1247960284404578664842240,⟨6,34,428,508,48,352,194,384,260⟩⟩,⟨6,1247959131201736520246281,⟨23,51,397,415,51,288,146,384,260⟩⟩,⟨3,1210109956724252365516037,⟨87,51,247,82,51,371,242,499,375⟩⟩]⟩
theorem node1548 : UpperPrefix a [2,5,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,8,1] 30 cert1548 (by decide +kernel)

def cert1549 : Leaf := ⟨⟨440,0,0,423,0,159,0,63,187⟩,[(1,4),(2,6),(4,1),(6,2)],[],⟨7,35,140,88,49,352,200,402,278⟩,⟨7,35,140,88,49,352,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩]⟩
theorem node1549 : UpperPrefix a [2,5,7,6,0,8,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,8,3] 30 cert1549 (by decide +kernel)

def cert1550 : Leaf := ⟨⟨424,0,291,0,0,143,303,47,171⟩,[(1,4),(3,6),(4,1)],[(4,6,3)],⟨7,35,140,88,49,352,208,394,270⟩,⟨7,35,140,88,49,352,208,384,260⟩,[⟨6,1247959131201736520246281,⟨23,51,397,415,51,288,146,384,260⟩⟩]⟩
theorem node1550 : UpperPrefix a [2,5,7,6,0,8,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,8,4] 30 cert1550 (by decide +kernel)

theorem node1551 : UpperPrefix a [2,5,7,6,0,8] 30 :=
  branch_upper a [2,5,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,6,0,8,0] 30 (by decide +kernel))
  node1548
  (invalid_upper a [2,5,7,6,0,8,2] 30 (by decide +kernel))
  node1549
  node1550
  (invalid_upper a [2,5,7,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,8,8] 30 (by decide +kernel)))

theorem node1552 : UpperPrefix a [2,5,7,6,0] 30 :=
  branch_upper a [2,5,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,6,0,0] 30 (by decide +kernel))
  node1545
  (invalid_upper a [2,5,7,6,0,2] 30 (by decide +kernel))
  node1546
  node1547
  (invalid_upper a [2,5,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,7] 30 (by decide +kernel))
  node1551)

def cert1553 : Leaf := ⟨⟨472,0,336,388,0,414,284,92,216⟩,[(1,5),(4,1)],[(5,1,4),(0,5,1),(0,5,4)],⟨7,35,140,88,50,97,472,408,284⟩,⟨7,35,140,88,50,97,192,384,260⟩,[⟨1,1323666154147174067208193,⟨5,33,460,476,508,97,192,384,260⟩⟩]⟩
theorem node1553 : UpperPrefix a [2,5,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,0] 30 cert1553 (by decide +kernel)

def cert1554 : Leaf := ⟨⟨152,156,19,135,0,0,287,31,155⟩,[(4,1),(5,3)],[(5,1,4),(6,3,5)],⟨7,35,140,88,50,104,465,401,277⟩,⟨7,35,140,88,50,104,192,384,260⟩,[⟨8,1181748210069345992045,⟨23,59,191,127,59,127,255,129,23⟩⟩]⟩
theorem node1554 : UpperPrefix a [2,5,7,6,1,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,3] 30 cert1554 (by decide +kernel)

def cert1555 : Leaf := ⟨⟨472,476,337,0,0,0,285,93,217⟩,[(3,5),(4,1),(5,3)],[(5,1,4)],⟨7,35,140,88,50,112,457,393,269⟩,⟨7,35,140,88,50,112,192,384,260⟩,[⟨1,1219570781866893082361857,⟨453,493,172,124,508,124,192,384,260⟩⟩]⟩
theorem node1555 : UpperPrefix a [2,5,7,6,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,4] 30 cert1555 (by decide +kernel)

def cert1556 : Leaf := ⟨⟨208,212,80,135,0,148,22,92,216⟩,[(4,1)],[(5,1,4)],⟨7,35,140,88,50,352,193,408,284⟩,⟨7,35,140,88,50,352,193,384,260⟩,[⟨8,1181817729157457536041,⟨95,59,205,95,59,127,205,128,68⟩⟩,⟨0,1247960284404716103795712,⟨22,50,428,508,50,352,192,384,260⟩⟩,⟨1,1247960284404578664841217,⟨5,33,428,508,48,352,193,384,260⟩⟩,⟨3,1210109956728650412051717,⟨87,51,247,82,50,371,243,499,375⟩⟩]⟩
theorem node1556 : UpperPrefix a [2,5,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,8,0] 30 cert1556 (by decide +kernel)

def cert1557 : Leaf := ⟨⟨408,412,0,391,0,159,0,31,155⟩,[(2,6),(4,1),(6,2)],[(5,1,4)],⟨7,35,140,88,50,352,200,401,277⟩,⟨7,35,140,88,50,352,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩]⟩
theorem node1557 : UpperPrefix a [2,5,7,6,1,8,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,8,3] 30 cert1557 (by decide +kernel)

def cert1558 : Leaf := ⟨⟨448,452,323,0,0,135,263,79,203⟩,[(3,6),(4,1)],[(5,1,4),(4,6,3)],⟨7,35,140,88,50,352,208,393,269⟩,⟨7,35,140,88,50,352,208,384,260⟩,[⟨3,1210109956728650412018949,⟨87,51,247,80,50,371,242,499,375⟩⟩]⟩
theorem node1558 : UpperPrefix a [2,5,7,6,1,8,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,8,4] 30 cert1558 (by decide +kernel)

theorem node1559 : UpperPrefix a [2,5,7,6,1,8] 30 :=
  branch_upper a [2,5,7,6,1,8] 30 (by decide) (fin9_cases _
  node1556
  (invalid_upper a [2,5,7,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,2] 30 (by decide +kernel))
  node1557
  node1558
  (invalid_upper a [2,5,7,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,8] 30 (by decide +kernel)))

theorem node1560 : UpperPrefix a [2,5,7,6,1] 30 :=
  branch_upper a [2,5,7,6,1] 30 (by decide) (fin9_cases _
  node1553
  (invalid_upper a [2,5,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,2] 30 (by decide +kernel))
  node1554
  node1555
  (invalid_upper a [2,5,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,7] 30 (by decide +kernel))
  node1559)

def cert1561 : Leaf := ⟨⟨184,0,50,32,64,158,318,62,58⟩,[(1,5)],[(6,3,4),(0,5,1)],⟨7,35,140,88,56,97,466,402,278⟩,⟨7,35,140,88,56,97,192,384,260⟩,[⟨8,1181748210069345992045,⟨23,59,191,127,59,127,255,129,23⟩⟩,⟨7,1213649340148344677221377,⟨279,315,12,88,58,379,64,256,260⟩⟩,⟨1,1210107565286192443293697,⟨21,57,140,88,56,121,192,384,260⟩⟩,⟨2,1210107565286192442262529,⟨19,59,136,88,58,123,192,384,256⟩⟩]⟩
theorem node1561 : UpperPrefix a [2,5,7,6,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,0] 30 cert1561 (by decide +kernel)

def cert1562 : Leaf := ⟨⟨56,28,48,36,68,29,60,60,56⟩,[],[(6,3,4),(1,5,1),(0,6,5)],⟨7,35,140,88,56,98,193,400,276⟩,⟨7,35,140,88,56,98,193,384,260⟩,[⟨8,1184139823902583160813,⟨127,59,255,127,59,127,255,255,127⟩⟩,⟨7,1232538808618329318657285,⟨279,315,319,122,56,122,379,257,279⟩⟩]⟩
theorem node1562 : UpperPrefix a [2,5,7,6,3,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,1,0] 30 cert1562 (by decide +kernel)

def cert1563 : Leaf := ⟨⟨168,140,33,0,197,141,45,45,169⟩,[(3,6)],[(6,3,4),(1,5,1),(4,6,3)],⟨7,35,140,88,56,98,208,385,261⟩,⟨7,35,140,88,56,98,208,384,260⟩,[⟨8,1184139823902583160813,⟨127,59,255,127,59,127,255,255,127⟩⟩]⟩
theorem node1563 : UpperPrefix a [2,5,7,6,3,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,1,4] 30 cert1563 (by decide +kernel)

def cert1564 : Leaf := ⟨⟨56,28,49,37,69,29,0,61,57⟩,[(6,7)],[(6,3,4),(1,5,1),(8,6,6)],⟨7,35,140,88,56,98,448,401,277⟩,⟨7,35,140,88,56,98,448,384,260⟩,[⟨7,1232538808618329318657285,⟨279,315,319,122,56,122,379,257,279⟩⟩]⟩
theorem node1564 : UpperPrefix a [2,5,7,6,3,1,8] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,1,8] 30 cert1564 (by decide +kernel)

theorem node1565 : UpperPrefix a [2,5,7,6,3,1] 30 :=
  branch_upper a [2,5,7,6,3,1] 30 (by decide) (fin9_cases _
  node1562
  (invalid_upper a [2,5,7,6,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,1,3] 30 (by decide +kernel))
  node1563
  (invalid_upper a [2,5,7,6,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,1,7] 30 (by decide +kernel))
  node1564)

def cert1566 : Leaf := ⟨⟨416,388,291,0,455,0,295,39,163⟩,[(3,5),(5,3)],[(6,3,4),(4,5,4)],⟨7,35,140,88,56,112,451,387,263⟩,⟨7,35,140,88,56,112,192,384,260⟩,[⟨3,1236149882612174614957317,⟨455,483,487,112,48,112,192,449,455⟩⟩]⟩
theorem node1566 : UpperPrefix a [2,5,7,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,4] 30 cert1566 (by decide +kernel)

def cert1567 : Leaf := ⟨⟨176,20,50,38,70,22,54,62,58⟩,[],[(6,3,4)],⟨7,35,140,88,56,352,193,402,278⟩,⟨7,35,140,88,56,352,193,384,260⟩,[⟨0,1224302337107668166509568,⟨406,446,156,124,56,380,508,384,260⟩⟩,⟨8,1181817729157457536041,⟨95,59,205,95,59,127,205,128,68⟩⟩,⟨7,1213649342405100883182593,⟨279,315,28,122,56,378,379,256,260⟩⟩,⟨3,1210109956695252746358021,⟨71,35,231,82,50,355,227,483,359⟩⟩]⟩
theorem node1567 : UpperPrefix a [2,5,7,6,3,8,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,8,0] 30 cert1567 (by decide +kernel)

def cert1568 : Leaf := ⟨⟨160,132,48,164,196,133,293,61,185⟩,[],[(6,3,4)],⟨7,35,140,88,56,352,194,401,277⟩,⟨7,35,140,88,56,352,194,384,260⟩,[⟨1,1224302337107668166508545,⟨405,445,156,124,56,380,508,384,260⟩⟩,⟨8,1181745671571875325033,⟨23,59,141,95,59,127,223,128,4⟩⟩,⟨3,1210109956695252746325253,⟨71,35,231,80,50,355,226,483,359⟩⟩,⟨4,1210109956694154308439301,⟨71,35,239,72,42,355,226,483,359⟩⟩,⟨0,1210107565286201050006528,⟨22,58,140,92,56,380,222,384,260⟩⟩]⟩
theorem node1568 : UpperPrefix a [2,5,7,6,3,8,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,8,1] 30 cert1568 (by decide +kernel)

def cert1569 : Leaf := ⟨⟨168,140,32,0,196,140,300,47,171⟩,[(3,6)],[(6,3,4),(4,6,3)],⟨7,35,140,88,56,352,208,387,263⟩,⟨7,35,140,88,56,352,208,384,260⟩,[⟨0,1210109956728716631475200,⟨94,58,252,92,56,380,252,508,380⟩⟩,⟨1,1210109956728716631474177,⟨93,57,252,92,56,380,252,508,380⟩⟩,⟨8,1181745671571875325033,⟨23,59,141,95,59,127,223,128,4⟩⟩]⟩
theorem node1569 : UpperPrefix a [2,5,7,6,3,8,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,8,4] 30 cert1569 (by decide +kernel)

theorem node1570 : UpperPrefix a [2,5,7,6,3,8] 30 :=
  branch_upper a [2,5,7,6,3,8] 30 (by decide) (fin9_cases _
  node1567
  node1568
  (invalid_upper a [2,5,7,6,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,8,3] 30 (by decide +kernel))
  node1569
  (invalid_upper a [2,5,7,6,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,8,8] 30 (by decide +kernel)))

theorem node1571 : UpperPrefix a [2,5,7,6,3] 30 :=
  branch_upper a [2,5,7,6,3] 30 (by decide) (fin9_cases _
  node1561
  node1565
  (invalid_upper a [2,5,7,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,3] 30 (by decide +kernel))
  node1566
  (invalid_upper a [2,5,7,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,7] 30 (by decide +kernel))
  node1570)

def cert1572 : Leaf := ⟨⟨480,0,368,416,196,390,288,120,248⟩,[(1,5)],[(0,5,1),(1,6,5)],⟨7,35,140,88,304,97,194,408,284⟩,⟨7,35,140,88,304,97,194,384,260⟩,[⟨3,1210109956897562885844741,⟨103,35,247,82,307,99,242,499,375⟩⟩,⟨2,1210255427466819660694529,⟨3,35,136,216,506,99,194,384,256⟩⟩,⟨4,1210109956870076168892165,⟨103,35,239,74,291,99,226,483,359⟩⟩]⟩
theorem node1572 : UpperPrefix a [2,5,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,0,1] 30 cert1572 (by decide +kernel)

def cert1573 : Leaf := ⟨⟨440,0,0,422,142,414,0,62,186⟩,[(1,5),(2,6),(6,2)],[(0,5,1)],⟨7,35,140,88,304,97,200,402,278⟩,⟨7,35,140,88,304,97,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩]⟩
theorem node1573 : UpperPrefix a [2,5,7,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,0,3] 30 cert1573 (by decide +kernel)

def cert1574 : Leaf := ⟨⟨224,0,98,0,198,134,294,110,234⟩,[(1,5),(3,6)],[(8,4,6),(0,5,1),(4,6,3)],⟨7,35,140,88,304,97,208,394,270⟩,⟨7,35,140,88,304,97,208,384,260⟩,[⟨3,1210109956897562885844741,⟨103,35,247,82,307,99,242,499,375⟩⟩]⟩
theorem node1574 : UpperPrefix a [2,5,7,6,8,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,0,4] 30 cert1574 (by decide +kernel)

theorem node1575 : UpperPrefix a [2,5,7,6,8,0] 30 :=
  branch_upper a [2,5,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,6,8,0,0] 30 (by decide +kernel))
  node1572
  (invalid_upper a [2,5,7,6,8,0,2] 30 (by decide +kernel))
  node1573
  node1574
  (invalid_upper a [2,5,7,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,0,8] 30 (by decide +kernel)))

def cert1576 : Leaf := ⟨⟨96,68,368,420,68,5,36,124,120⟩,[],[(1,5,1),(0,6,5)],⟨7,35,140,88,304,98,193,408,284⟩,⟨7,35,140,88,304,98,193,384,260⟩,[⟨3,1210109959430837676257029,⟨103,35,247,114,307,98,243,499,375⟩⟩,⟨7,1227816442128162524015877,⟨279,35,319,122,307,98,99,257,279⟩⟩,⟨4,1210109959403350959304453,⟨103,35,239,106,291,98,227,483,359⟩⟩,⟨8,1184139789821296226053,⟨103,35,239,122,51,98,227,227,103⟩⟩]⟩
theorem node1576 : UpperPrefix a [2,5,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,1,0] 30 cert1576 (by decide +kernel)

def cert1577 : Leaf := ⟨⟨368,340,0,293,69,277,0,117,113⟩,[(2,6),(6,2)],[(1,5,1)],⟨7,35,140,88,304,98,200,401,277⟩,⟨7,35,140,88,304,98,200,384,260⟩,[⟨3,1236292718778368614477061,⟨407,435,439,242,435,242,224,385,407⟩⟩,⟨7,1232538806359374089432325,⟨279,315,319,122,315,122,104,257,279⟩⟩]⟩
theorem node1577 : UpperPrefix a [2,5,7,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,1,3] 30 cert1577 (by decide +kernel)

def cert1578 : Leaf := ⟨⟨224,196,97,0,197,133,293,109,233⟩,[(3,6)],[(8,4,6),(1,5,1),(4,6,3)],⟨7,35,140,88,304,98,208,393,269⟩,⟨7,35,140,88,304,98,208,384,260⟩,[⟨3,1210109959430837676224261,⟨103,35,247,114,307,98,242,499,375⟩⟩]⟩
theorem node1578 : UpperPrefix a [2,5,7,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,1,4] 30 cert1578 (by decide +kernel)

theorem node1579 : UpperPrefix a [2,5,7,6,8,1] 30 :=
  branch_upper a [2,5,7,6,8,1] 30 (by decide) (fin9_cases _
  node1576
  (invalid_upper a [2,5,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,2] 30 (by decide +kernel))
  node1577
  node1578
  (invalid_upper a [2,5,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,8] 30 (by decide +kernel)))

def cert1580 : Leaf := ⟨⟨312,284,306,294,6,0,310,54,50⟩,[(5,3)],[(6,3,5)],⟨7,35,140,88,304,104,193,402,278⟩,⟨7,35,140,88,304,104,193,384,260⟩,[⟨0,1224302337386394364150784,⟨406,446,172,124,312,124,508,384,260⟩⟩,⟨7,1232538808615580539596037,⟨279,315,319,122,315,122,379,257,279⟩⟩,⟨3,1214857655926163789317121,⟨471,499,132,80,304,96,449,384,260⟩⟩]⟩
theorem node1580 : UpperPrefix a [2,5,7,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,3,0] 30 cert1580 (by decide +kernel)

def cert1581 : Leaf := ⟨⟨312,284,305,293,5,0,309,53,49⟩,[(5,3)],[(6,3,5)],⟨7,35,140,88,304,104,194,401,277⟩,⟨7,35,140,88,304,104,194,384,260⟩,[⟨1,1224302337386394364149761,⟨405,445,172,124,312,124,508,384,260⟩⟩,⟨7,1232538808611178198084869,⟨279,307,319,122,307,104,122,257,279⟩⟩,⟨3,1214857655926163789317121,⟨471,499,132,80,304,96,210,384,260⟩⟩]⟩
theorem node1581 : UpperPrefix a [2,5,7,6,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,3,1] 30 cert1581 (by decide +kernel)

def cert1582 : Local := ⟨⟨168,140,35,0,143,0,303,47,171⟩,[(3,6),(5,3)],[(6,3,5),(8,4,6),(4,6,3),(4,6,5)]⟩
theorem node1582 : UpperPrefix a [2,5,7,6,8,3,4] 30 :=
  local_sound a [2,5,7,6,8,3,4] 30 cert1582 (by decide +kernel)

theorem node1583 : UpperPrefix a [2,5,7,6,8,3] 30 :=
  branch_upper a [2,5,7,6,8,3] 30 (by decide) (fin9_cases _
  node1580
  node1581
  (invalid_upper a [2,5,7,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,3] 30 (by decide +kernel))
  node1582
  (invalid_upper a [2,5,7,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,8] 30 (by decide +kernel)))

def cert1584 : Leaf := ⟨⟨336,340,338,0,70,0,278,94,90⟩,[(3,5),(5,3)],[],⟨7,35,140,88,304,112,193,394,270⟩,⟨7,35,140,88,304,112,193,384,260⟩,[⟨5,1219570797910964603192323,⟨455,463,140,88,280,88,193,384,260⟩⟩,⟨0,1219570745275281397253120,⟨406,446,172,120,312,120,192,384,260⟩⟩,⟨3,1210109959395653304168197,⟨103,35,247,114,307,114,243,499,375⟩⟩,⟨7,1227816439876367005265157,⟨279,43,319,122,315,122,65,257,279⟩⟩]⟩
theorem node1584 : UpperPrefix a [2,5,7,6,8,4,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,4,0] 30 cert1584 (by decide +kernel)

def cert1585 : Leaf := ⟨⟨336,340,337,0,69,0,277,93,89⟩,[(3,5),(5,3)],[],⟨7,35,140,88,304,112,194,393,269⟩,⟨7,35,140,88,304,112,194,384,260⟩,[⟨5,1408834392107224617452611,⟨455,463,396,477,412,477,455,384,260⟩⟩,⟨1,1219570747531487864160257,⟨405,445,172,124,312,124,508,384,260⟩⟩,⟨3,1210109959395653304135429,⟨103,35,247,114,307,114,242,499,375⟩⟩,⟨7,1227816439876367005265157,⟨279,43,319,122,315,122,66,257,279⟩⟩]⟩
theorem node1585 : UpperPrefix a [2,5,7,6,8,4,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,4,1] 30 cert1585 (by decide +kernel)

def cert1586 : Leaf := ⟨⟨496,468,0,0,199,0,0,119,243⟩,[(2,6),(3,5),(5,3),(6,2)],[],⟨7,35,140,88,304,112,200,387,263⟩,⟨7,35,140,88,304,112,200,384,260⟩,[⟨3,1236292718778368614477061,⟨407,435,439,242,435,242,224,385,407⟩⟩]⟩
theorem node1586 : UpperPrefix a [2,5,7,6,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,4,3] 30 cert1586 (by decide +kernel)

theorem node1587 : UpperPrefix a [2,5,7,6,8,4] 30 :=
  branch_upper a [2,5,7,6,8,4] 30 (by decide) (fin9_cases _
  node1584
  node1585
  (invalid_upper a [2,5,7,6,8,4,2] 30 (by decide +kernel))
  node1586
  (invalid_upper a [2,5,7,6,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,8] 30 (by decide +kernel)))

theorem node1588 : UpperPrefix a [2,5,7,6,8] 30 :=
  branch_upper a [2,5,7,6,8] 30 (by decide) (fin9_cases _
  node1575
  node1579
  (invalid_upper a [2,5,7,6,8,2] 30 (by decide +kernel))
  node1583
  node1587
  (invalid_upper a [2,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,8] 30 (by decide +kernel)))

theorem node1589 : UpperPrefix a [2,5,7,6] 30 :=
  branch_upper a [2,5,7,6] 30 (by decide) (fin9_cases _
  node1552
  node1560
  (invalid_upper a [2,5,7,6,2] 30 (by decide +kernel))
  node1571
  (invalid_upper a [2,5,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,7] 30 (by decide +kernel))
  node1588)

def cert1590 : Leaf := ⟨⟨248,0,336,196,0,157,28,92,216⟩,[(1,4),(4,1)],[(8,3,2),(1,5,1),(1,5,4)],⟨7,35,140,280,49,98,216,472,348⟩,⟨7,35,140,280,49,98,192,384,260⟩,[⟨0,1323666154147174067209216,⟨6,34,460,476,508,98,192,384,260⟩⟩,⟨5,1323666153021274160366593,⟨7,3,460,476,477,66,192,384,260⟩⟩]⟩
theorem node1590 : UpperPrefix a [2,5,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,1] 30 cert1590 (by decide +kernel)

def cert1591 : Leaf := ⟨⟨248,0,369,229,0,145,49,113,241⟩,[(1,4),(4,1)],[(8,3,2)],⟨7,35,140,280,49,104,194,464,340⟩,⟨7,35,140,280,49,104,194,384,260⟩,[⟨1,1512929318249813553184769,⟨21,53,140,280,53,492,508,384,260⟩⟩,⟨2,1210181496797753222637057,⟨51,51,232,506,51,232,210,384,288⟩⟩,⟨3,1215079449200612531512321,⟨471,499,196,466,499,224,210,384,260⟩⟩]⟩
theorem node1591 : UpperPrefix a [2,5,7,8,0,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,3,1] 30 cert1591 (by decide +kernel)

def cert1592 : Leaf := ⟨⟨232,0,352,228,0,148,45,108,232⟩,[(1,4),(4,1)],[(8,3,2),(4,6,5)],⟨7,35,140,280,49,104,208,386,324⟩,⟨7,35,140,280,49,104,208,386,260⟩,[⟨0,1663473196635221904065536,⟨134,418,140,280,312,364,508,386,260⟩⟩,⟨1,2286809436117511466647553,⟨317,313,492,280,313,364,508,508,292⟩⟩]⟩
theorem node1592 : UpperPrefix a [2,5,7,8,0,3,4,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,3,4,1] 30 cert1592 (by decide +kernel)

def cert1593 : Leaf := ⟨⟨232,0,354,230,0,150,46,46,234⟩,[(1,4),(4,1)],[(8,3,2),(4,6,5)],⟨7,35,140,280,49,104,208,448,262⟩,⟨7,35,140,280,49,104,208,448,260⟩,[⟨0,1224496461243873775059968,⟨294,294,236,508,508,236,252,484,292⟩⟩]⟩
theorem node1593 : UpperPrefix a [2,5,7,8,0,3,4,6] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,3,4,6] 30 cert1593 (by decide +kernel)

theorem node1594 : UpperPrefix a [2,5,7,8,0,3,4] 30 :=
  branch_upper a [2,5,7,8,0,3,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,0,3,4,0] 30 (by decide +kernel))
  node1592
  (invalid_upper a [2,5,7,8,0,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,4,5] 30 (by decide +kernel))
  node1593
  (invalid_upper a [2,5,7,8,0,3,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,4,8] 30 (by decide +kernel)))

theorem node1595 : UpperPrefix a [2,5,7,8,0,3] 30 :=
  branch_upper a [2,5,7,8,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,0,3,0] 30 (by decide +kernel))
  node1591
  (invalid_upper a [2,5,7,8,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,3] 30 (by decide +kernel))
  node1594
  (invalid_upper a [2,5,7,8,0,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,8] 30 (by decide +kernel)))

def cert1596 : Leaf := ⟨⟨216,0,338,198,0,142,28,94,218⟩,[(1,4),(4,1)],[(8,3,2)],⟨7,35,140,280,49,112,194,456,332⟩,⟨7,35,140,280,49,112,194,384,260⟩,[⟨0,1446687112635328625116160,⟨454,494,140,444,508,508,454,384,260⟩⟩,⟨5,1446687110946478764852291,⟨455,463,140,412,477,477,455,384,260⟩⟩]⟩
theorem node1596 : UpperPrefix a [2,5,7,8,0,4,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,4,1] 30 cert1596 (by decide +kernel)

def cert1597 : Local := ⟨⟨248,0,0,231,0,143,0,127,251⟩,[(1,4),(2,6),(4,1),(6,2)],[(8,3,2),(8,3,6)]⟩
theorem node1597 : UpperPrefix a [2,5,7,8,0,4,3] 30 :=
  local_sound a [2,5,7,8,0,4,3] 30 cert1597 (by decide +kernel)

theorem node1598 : UpperPrefix a [2,5,7,8,0,4] 30 :=
  branch_upper a [2,5,7,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,0,4,0] 30 (by decide +kernel))
  node1596
  (invalid_upper a [2,5,7,8,0,4,2] 30 (by decide +kernel))
  node1597
  (invalid_upper a [2,5,7,8,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,8] 30 (by decide +kernel)))

theorem node1599 : UpperPrefix a [2,5,7,8,0] 30 :=
  branch_upper a [2,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,0,0] 30 (by decide +kernel))
  node1590
  (invalid_upper a [2,5,7,8,0,2] 30 (by decide +kernel))
  node1595
  node1598
  (invalid_upper a [2,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,8] 30 (by decide +kernel)))

#print axioms node1599
end Delivery.FiniteExclusion.Sharp2x7
