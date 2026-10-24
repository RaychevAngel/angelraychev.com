import RegularNineSharp2x7Base
import RegularNineSharp2x7C023
import RegularNineSharp2x7C024
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert1600 : Leaf := ⟨⟨216,0,336,196,0,158,28,92,216⟩,[(1,5),(4,1)],[(5,1,4),(8,3,2),(0,5,1),(0,5,4)],⟨7,35,140,280,50,97,216,472,348⟩,⟨7,35,140,280,50,97,192,384,260⟩,[⟨1,1323666154147174067208193,⟨5,33,460,476,508,97,192,384,260⟩⟩]⟩
theorem node1600 : UpperPrefix a [2,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,0] 30 cert1600 (by decide +kernel)

def cert1601 : Local := ⟨⟨200,204,339,0,0,135,14,0,203⟩,[(3,7),(4,1),(7,3)],[(5,1,4),(8,3,2),(4,7,2)]⟩
theorem node1601 : UpperPrefix a [2,5,7,8,1,3,0,4] 30 :=
  local_sound a [2,5,7,8,1,3,0,4] 30 cert1601 (by decide +kernel)

def cert1602 : Leaf := ⟨⟨200,204,321,197,0,133,12,13,217⟩,[(4,1)],[(5,1,4),(8,3,2)],⟨7,35,140,280,50,104,193,448,276⟩,⟨7,35,140,280,50,104,193,448,260⟩,[⟨1,1323887119322241335033857,⟨69,229,396,444,508,492,193,448,260⟩⟩,⟨4,1212550246085256369307455,⟨103,103,239,495,103,239,195,451,487⟩⟩]⟩
theorem node1602 : UpperPrefix a [2,5,7,8,1,3,0,6] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,3,0,6] 30 cert1602 (by decide +kernel)

theorem node1603 : UpperPrefix a [2,5,7,8,1,3,0] 30 :=
  branch_upper a [2,5,7,8,1,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,1,3,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,0,3] 30 (by decide +kernel))
  node1601
  (invalid_upper a [2,5,7,8,1,3,0,5] 30 (by decide +kernel))
  node1602
  (invalid_upper a [2,5,7,8,1,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,0,8] 30 (by decide +kernel)))

def cert1604 : Local := ⟨⟨200,200,323,195,0,147,11,78,203⟩,[(4,1)],[(2,0,7),(5,1,4),(8,3,2),(4,6,5)]⟩
theorem node1604 : UpperPrefix a [2,5,7,8,1,3,4,0] 30 :=
  local_sound a [2,5,7,8,1,3,4,0] 30 cert1604 (by decide +kernel)

def cert1605 : Leaf := ⟨⟨200,204,321,197,0,149,13,13,201⟩,[(4,1)],[(5,1,4),(8,3,2),(4,6,5)],⟨7,35,140,280,50,104,208,448,261⟩,⟨7,35,140,280,50,104,208,448,260⟩,[⟨1,1224496461243873775058945,⟨293,293,236,508,508,236,252,484,292⟩⟩]⟩
theorem node1605 : UpperPrefix a [2,5,7,8,1,3,4,6] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,3,4,6] 30 cert1605 (by decide +kernel)

theorem node1606 : UpperPrefix a [2,5,7,8,1,3,4] 30 :=
  branch_upper a [2,5,7,8,1,3,4] 30 (by decide) (fin9_cases _
  node1604
  (invalid_upper a [2,5,7,8,1,3,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,4,5] 30 (by decide +kernel))
  node1605
  (invalid_upper a [2,5,7,8,1,3,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,4,8] 30 (by decide +kernel)))

theorem node1607 : UpperPrefix a [2,5,7,8,1,3] 30 :=
  branch_upper a [2,5,7,8,1,3] 30 (by decide) (fin9_cases _
  node1603
  (invalid_upper a [2,5,7,8,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,3] 30 (by decide +kernel))
  node1606
  (invalid_upper a [2,5,7,8,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,8] 30 (by decide +kernel)))

def cert1608 : Leaf := ⟨⟨216,220,336,196,0,141,28,92,216⟩,[(4,1)],[(5,1,4),(8,3,2)],⟨7,35,140,280,50,112,193,456,332⟩,⟨7,35,140,280,50,112,193,384,260⟩,[⟨1,1446687112635328625115137,⟨453,493,140,444,508,508,193,384,260⟩⟩,⟨0,1361518440641003848729600,⟨30,446,140,284,446,508,192,384,260⟩⟩]⟩
theorem node1608 : UpperPrefix a [2,5,7,8,1,4,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,4,0] 30 cert1608 (by decide +kernel)

def cert1609 : Leaf := ⟨⟨200,204,0,199,0,143,0,79,203⟩,[(2,6),(4,1),(6,2)],[(5,1,4),(8,3,2),(8,3,6)],⟨7,35,140,280,50,112,200,449,325⟩,⟨7,35,140,280,50,112,200,384,260⟩,[⟨4,1725851075640342806029353,⟨455,419,461,463,419,487,461,384,452⟩⟩]⟩
theorem node1609 : UpperPrefix a [2,5,7,8,1,4,3] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,4,3] 30 cert1609 (by decide +kernel)

theorem node1610 : UpperPrefix a [2,5,7,8,1,4] 30 :=
  branch_upper a [2,5,7,8,1,4] 30 (by decide) (fin9_cases _
  node1608
  (invalid_upper a [2,5,7,8,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,4,2] 30 (by decide +kernel))
  node1609
  (invalid_upper a [2,5,7,8,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,4,8] 30 (by decide +kernel)))

theorem node1611 : UpperPrefix a [2,5,7,8,1] 30 :=
  branch_upper a [2,5,7,8,1] 30 (by decide) (fin9_cases _
  node1600
  (invalid_upper a [2,5,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,2] 30 (by decide +kernel))
  node1607
  node1610
  (invalid_upper a [2,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,8] 30 (by decide +kernel)))

def cert1612 : Leaf := ⟨⟨224,0,368,228,196,134,36,116,248⟩,[(1,5)],[(8,3,2),(0,5,1),(1,6,5)],⟨7,35,140,280,56,97,194,464,340⟩,⟨7,35,140,280,56,97,194,384,260⟩,[⟨3,1210184176474508649258757,⟨103,35,231,499,242,99,226,483,359⟩⟩,⟨4,1210109956870076168888069,⟨103,35,239,299,42,99,226,483,359⟩⟩]⟩
theorem node1612 : UpperPrefix a [2,5,7,8,3,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,0,1] 30 cert1612 (by decide +kernel)

def cert1613 : Leaf := ⟨⟨224,0,354,230,198,134,38,102,226⟩,[(1,5)],[(8,3,2),(0,5,1)],⟨7,35,140,280,56,97,208,450,326⟩,⟨7,35,140,280,56,97,208,384,260⟩,[⟨3,1229108144447548143329029,⟨423,35,487,499,242,99,208,387,423⟩⟩,⟨4,1513224466153747344581721,⟨7,163,141,271,175,483,487,384,260⟩⟩]⟩
theorem node1613 : UpperPrefix a [2,5,7,8,3,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,0,4] 30 cert1613 (by decide +kernel)

theorem node1614 : UpperPrefix a [2,5,7,8,3,0] 30 :=
  branch_upper a [2,5,7,8,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,3,0,0] 30 (by decide +kernel))
  node1612
  (invalid_upper a [2,5,7,8,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,0,3] 30 (by decide +kernel))
  node1613
  (invalid_upper a [2,5,7,8,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,0,8] 30 (by decide +kernel)))

def cert1615 : Leaf := ⟨⟨224,192,368,228,196,129,36,116,248⟩,[],[(8,3,2),(1,5,1),(0,6,5)],⟨7,35,140,280,56,98,193,464,340⟩,⟨7,35,140,280,56,98,193,384,260⟩,[⟨3,1210183891058882264669957,⟨103,35,231,499,242,98,227,483,359⟩⟩,⟨4,1210109959121875982589701,⟨103,35,239,299,42,98,227,483,359⟩⟩,⟨2,1210107567535651498787841,⟨3,35,136,280,56,98,227,384,256⟩⟩]⟩
theorem node1615 : UpperPrefix a [2,5,7,8,3,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,1,0] 30 cert1615 (by decide +kernel)

def cert1616 : Leaf := ⟨⟨192,196,321,197,197,133,5,69,193⟩,[],[(8,3,2),(1,5,1)],⟨7,35,140,280,56,98,208,449,325⟩,⟨7,35,140,280,56,98,208,384,260⟩,[⟨3,1229108145010498096733957,⟨423,35,487,499,242,98,240,387,423⟩⟩,⟨4,1513224466153747344581721,⟨7,163,141,271,175,483,487,384,260⟩⟩,⟨5,1437224309539038775215139,⟨7,391,204,476,477,463,476,384,260⟩⟩]⟩
theorem node1616 : UpperPrefix a [2,5,7,8,3,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,1,4] 30 cert1616 (by decide +kernel)

theorem node1617 : UpperPrefix a [2,5,7,8,3,1] 30 :=
  branch_upper a [2,5,7,8,3,1] 30 (by decide) (fin9_cases _
  node1615
  (invalid_upper a [2,5,7,8,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,1,3] 30 (by decide +kernel))
  node1616
  (invalid_upper a [2,5,7,8,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,1,8] 30 (by decide +kernel)))

def cert1618 : Leaf := ⟨⟨224,196,352,228,196,132,38,100,224⟩,[],[(8,3,2),(4,5,4),(1,7,6)],⟨7,35,140,280,56,112,193,386,324⟩,⟨7,35,140,280,56,112,193,386,260⟩,[⟨0,1663473196641978190398464,⟨158,446,140,280,312,380,508,414,260⟩⟩,⟨3,1236226120109616696139013,⟨455,483,487,499,242,112,449,451,455⟩⟩]⟩
theorem node1618 : UpperPrefix a [2,5,7,8,3,4,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,4,0,1] 30 cert1618 (by decide +kernel)

def cert1619 : Leaf := ⟨⟨160,132,290,166,134,134,38,38,162⟩,[],[(8,3,2),(4,5,4)],⟨7,35,140,280,56,112,193,448,262⟩,⟨7,35,140,280,56,112,193,448,260⟩,[⟨0,1224864967314084839031808,⟨286,318,188,280,60,252,508,508,284⟩⟩,⟨3,1236816415919975401790725,⟨455,483,487,499,242,240,449,449,455⟩⟩,⟨6,1365944506299388695438369,⟨287,315,140,282,315,319,397,388,260⟩⟩]⟩
theorem node1619 : UpperPrefix a [2,5,7,8,3,4,0,6] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,4,0,6] 30 cert1619 (by decide +kernel)

theorem node1620 : UpperPrefix a [2,5,7,8,3,4,0] 30 :=
  branch_upper a [2,5,7,8,3,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,3,4,0,0] 30 (by decide +kernel))
  node1618
  (invalid_upper a [2,5,7,8,3,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,0,5] 30 (by decide +kernel))
  node1619
  (invalid_upper a [2,5,7,8,3,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,0,8] 30 (by decide +kernel)))

def cert1621 : Leaf := ⟨⟨232,200,352,224,192,136,41,108,232⟩,[],[(2,0,7),(8,3,2),(4,5,4),(0,7,6)],⟨7,35,140,280,56,112,194,385,324⟩,⟨7,35,140,280,56,112,194,385,260⟩,[⟨1,1663473196641960976973825,⟨157,445,140,280,312,380,508,389,260⟩⟩]⟩
theorem node1621 : UpperPrefix a [2,5,7,8,3,4,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,4,1,0] 30 cert1621 (by decide +kernel)

def cert1622 : Leaf := ⟨⟨192,196,321,197,197,133,5,5,193⟩,[],[(8,3,2),(4,5,4)],⟨7,35,140,280,56,112,194,448,261⟩,⟨7,35,140,280,56,112,194,448,260⟩,[⟨1,1224864967314084839030785,⟨285,317,188,280,60,252,508,508,284⟩⟩,⟨3,1236224102496983634156805,⟨455,483,487,499,242,112,194,449,455⟩⟩,⟨5,1678535013836897262240835,⟨455,463,140,284,412,477,455,449,260⟩⟩]⟩
theorem node1622 : UpperPrefix a [2,5,7,8,3,4,1,6] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,4,1,6] 30 cert1622 (by decide +kernel)

theorem node1623 : UpperPrefix a [2,5,7,8,3,4,1] 30 :=
  branch_upper a [2,5,7,8,3,4,1] 30 (by decide) (fin9_cases _
  node1621
  (invalid_upper a [2,5,7,8,3,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,1,5] 30 (by decide +kernel))
  node1622
  (invalid_upper a [2,5,7,8,3,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,1,8] 30 (by decide +kernel)))

theorem node1624 : UpperPrefix a [2,5,7,8,3,4] 30 :=
  branch_upper a [2,5,7,8,3,4] 30 (by decide) (fin9_cases _
  node1620
  node1623
  (invalid_upper a [2,5,7,8,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,4,8] 30 (by decide +kernel)))

theorem node1625 : UpperPrefix a [2,5,7,8,3] 30 :=
  branch_upper a [2,5,7,8,3] 30 (by decide) (fin9_cases _
  node1614
  node1617
  (invalid_upper a [2,5,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,3] 30 (by decide +kernel))
  node1624
  (invalid_upper a [2,5,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,8] 30 (by decide +kernel)))

def cert1626 : Local := ⟨⟨184,0,304,164,0,158,60,60,184⟩,[(1,5),(4,5)],[(8,3,2),(6,4,4),(0,5,1),(1,6,5)]⟩
theorem node1626 : UpperPrefix a [2,5,7,8,6,0,1] 30 :=
  local_sound a [2,5,7,8,6,0,1] 30 cert1626 (by decide +kernel)

def cert1627 : Local := ⟨⟨184,0,0,166,0,158,0,62,186⟩,[(1,5),(2,6),(4,5),(6,2)],[(8,3,2),(8,3,6),(6,4,4),(0,5,1)]⟩
theorem node1627 : UpperPrefix a [2,5,7,8,6,0,3] 30 :=
  local_sound a [2,5,7,8,6,0,3] 30 cert1627 (by decide +kernel)

def cert1628 : Leaf := ⟨⟨176,0,306,166,0,150,38,62,186⟩,[(1,5),(4,5)],[(8,3,2),(6,4,4),(0,5,1)],⟨7,35,140,280,112,97,208,394,270⟩,⟨7,35,140,280,112,97,208,384,260⟩,[⟨3,1210109956904503552990981,⟨119,51,247,307,114,115,242,499,375⟩⟩]⟩
theorem node1628 : UpperPrefix a [2,5,7,8,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,0,4] 30 cert1628 (by decide +kernel)

theorem node1629 : UpperPrefix a [2,5,7,8,6,0] 30 :=
  branch_upper a [2,5,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,6,0,0] 30 (by decide +kernel))
  node1626
  (invalid_upper a [2,5,7,8,6,0,2] 30 (by decide +kernel))
  node1627
  node1628
  (invalid_upper a [2,5,7,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,0,8] 30 (by decide +kernel)))

def cert1630 : Leaf := ⟨⟨176,148,304,164,0,149,52,60,184⟩,[(4,5)],[(8,3,2),(6,4,4),(1,5,1),(0,6,5)],⟨7,35,140,280,112,98,193,408,284⟩,⟨7,35,140,280,112,98,193,384,260⟩,[⟨3,1210109959719253320113925,⟨119,51,247,307,114,114,243,499,375⟩⟩]⟩
theorem node1630 : UpperPrefix a [2,5,7,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,1,0] 30 cert1630 (by decide +kernel)

def cert1631 : Local := ⟨⟨184,156,0,165,0,157,0,61,185⟩,[(2,6),(4,5),(6,2)],[(8,3,2),(8,3,6),(6,4,4),(1,5,1)]⟩
theorem node1631 : UpperPrefix a [2,5,7,8,6,1,3] 30 :=
  local_sound a [2,5,7,8,6,1,3] 30 cert1631 (by decide +kernel)

def cert1632 : Leaf := ⟨⟨152,156,273,133,0,157,13,29,153⟩,[(4,5)],[(8,3,2),(6,4,4),(1,5,1)],⟨7,35,140,280,112,98,208,393,269⟩,⟨7,35,140,280,112,98,208,384,260⟩,[⟨5,1437224309539038775215139,⟨7,391,204,476,477,463,476,384,260⟩⟩]⟩
theorem node1632 : UpperPrefix a [2,5,7,8,6,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,1,4] 30 cert1632 (by decide +kernel)

theorem node1633 : UpperPrefix a [2,5,7,8,6,1] 30 :=
  branch_upper a [2,5,7,8,6,1] 30 (by decide) (fin9_cases _
  node1630
  (invalid_upper a [2,5,7,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,1,2] 30 (by decide +kernel))
  node1631
  node1632
  (invalid_upper a [2,5,7,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,1,8] 30 (by decide +kernel)))

def cert1634 : Leaf := ⟨⟨168,140,306,166,0,135,38,54,178⟩,[(4,5)],[(8,3,2),(6,4,4)],⟨7,35,140,280,112,104,193,402,278⟩,⟨7,35,140,280,112,104,193,384,260⟩,[⟨0,1219570744995863978574848,⟨398,446,140,280,112,120,196,384,260⟩⟩,⟨4,1210109943324092914601733,⟨103,35,239,267,96,104,195,451,359⟩⟩,⟨3,1214857655928362812572673,⟨471,499,132,272,112,112,449,384,260⟩⟩]⟩
theorem node1634 : UpperPrefix a [2,5,7,8,6,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,3,0] 30 cert1634 (by decide +kernel)

def cert1635 : Leaf := ⟨⟨168,140,305,165,0,133,37,53,177⟩,[(4,5)],[(8,3,2),(6,4,4)],⟨7,35,140,280,112,104,194,401,277⟩,⟨7,35,140,280,112,104,194,384,260⟩,[⟨1,1219570747815020398903297,⟨397,445,140,312,124,124,508,384,260⟩⟩,⟨4,1210109943324092914601733,⟨103,35,239,267,96,104,194,451,359⟩⟩,⟨3,1214857655928362812572673,⟨471,499,132,272,112,112,210,384,260⟩⟩]⟩
theorem node1635 : UpperPrefix a [2,5,7,8,6,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,3,1] 30 cert1635 (by decide +kernel)

def cert1636 : Leaf := ⟨⟨168,140,288,164,0,148,44,47,171⟩,[(4,5)],[(8,3,2),(6,4,4),(4,6,5)],⟨7,35,140,280,112,104,208,387,263⟩,⟨7,35,140,280,112,104,208,384,260⟩,[⟨0,1210109959121171658048512,⟨118,50,252,312,116,124,252,508,380⟩⟩,⟨1,1210109959121171658047489,⟨117,49,252,312,116,124,252,508,380⟩⟩]⟩
theorem node1636 : UpperPrefix a [2,5,7,8,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,3,4] 30 cert1636 (by decide +kernel)

theorem node1637 : UpperPrefix a [2,5,7,8,6,3] 30 :=
  branch_upper a [2,5,7,8,6,3] 30 (by decide) (fin9_cases _
  node1634
  node1635
  (invalid_upper a [2,5,7,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,3] 30 (by decide +kernel))
  node1636
  (invalid_upper a [2,5,7,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,8] 30 (by decide +kernel)))

def cert1638 : Leaf := ⟨⟨176,148,306,166,0,0,54,62,186⟩,[(4,5),(5,4)],[(8,3,2),(6,4,4),(6,4,5)],⟨7,35,140,280,112,112,193,394,270⟩,⟨7,35,140,280,112,112,193,384,260⟩,[⟨0,1224302337669926898893824,⟨398,446,140,312,124,124,508,384,260⟩⟩,⟨3,1210109959719253320113925,⟨119,51,247,307,114,114,243,499,375⟩⟩]⟩
theorem node1638 : UpperPrefix a [2,5,7,8,6,4,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,4,0] 30 cert1638 (by decide +kernel)

def cert1639 : Leaf := ⟨⟨152,156,275,135,0,0,29,31,155⟩,[(4,5),(5,4)],[(8,3,2),(6,4,4),(6,4,5)],⟨7,35,140,280,112,112,194,393,269⟩,⟨7,35,140,280,112,112,194,384,260⟩,[⟨5,1446687110946478764852291,⟨455,463,140,412,477,477,455,384,260⟩⟩]⟩
theorem node1639 : UpperPrefix a [2,5,7,8,6,4,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,4,1] 30 cert1639 (by decide +kernel)

def cert1640 : Local := ⟨⟨184,156,0,167,0,0,0,63,187⟩,[(2,6),(4,5),(5,4),(6,2)],[(8,3,2),(8,3,6),(6,4,4),(6,4,5)]⟩
theorem node1640 : UpperPrefix a [2,5,7,8,6,4,3] 30 :=
  local_sound a [2,5,7,8,6,4,3] 30 cert1640 (by decide +kernel)

theorem node1641 : UpperPrefix a [2,5,7,8,6,4] 30 :=
  branch_upper a [2,5,7,8,6,4] 30 (by decide) (fin9_cases _
  node1638
  node1639
  (invalid_upper a [2,5,7,8,6,4,2] 30 (by decide +kernel))
  node1640
  (invalid_upper a [2,5,7,8,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,8] 30 (by decide +kernel)))

theorem node1642 : UpperPrefix a [2,5,7,8,6] 30 :=
  branch_upper a [2,5,7,8,6] 30 (by decide) (fin9_cases _
  node1629
  node1633
  (invalid_upper a [2,5,7,8,6,2] 30 (by decide +kernel))
  node1637
  node1641
  (invalid_upper a [2,5,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,8] 30 (by decide +kernel)))

theorem node1643 : UpperPrefix a [2,5,7,8] 30 :=
  branch_upper a [2,5,7,8] 30 (by decide) (fin9_cases _
  node1599
  node1611
  (invalid_upper a [2,5,7,8,2] 30 (by decide +kernel))
  node1625
  (invalid_upper a [2,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,5] 30 (by decide +kernel))
  node1642
  (invalid_upper a [2,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,8] 30 (by decide +kernel)))

theorem node1644 : UpperPrefix a [2,5,7] 30 :=
  branch_upper a [2,5,7] 30 (by decide) (fin9_cases _
  node1518
  node1544
  (invalid_upper a [2,5,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,5] 30 (by decide +kernel))
  node1589
  (invalid_upper a [2,5,7,7] 30 (by decide +kernel))
  node1643)

def cert1645 : Leaf := ⟨⟨472,472,208,386,0,408,280,88,216⟩,[(4,1)],[(5,1,4),(1,4,3)],⟨7,35,268,25,50,248,216,472,476⟩,⟨7,35,268,25,50,96,192,384,260⟩,[⟨0,1247960428519904179651584,⟨22,50,492,508,50,96,192,384,260⟩⟩,⟨2,1210144549020944706835969,⟨251,123,506,123,58,96,192,384,496⟩⟩,⟨6,1210106412362484920878081,⟨31,59,268,25,58,32,128,384,260⟩⟩]⟩
theorem node1645 : UpperPrefix a [2,5,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,1] 30 cert1645 (by decide +kernel)

def cert1646 : Leaf := ⟨⟨504,472,208,32,0,408,280,88,216⟩,[],[(1,5,1)],⟨7,35,268,25,56,98,208,464,468⟩,⟨7,35,268,25,56,98,192,384,260⟩,[⟨0,1342592585660126085514240,⟨486,34,476,508,508,98,192,384,452⟩⟩,⟨2,1212510344302440700974593,⟨251,123,506,123,58,122,192,448,496⟩⟩,⟨5,1323666153021272012882945,⟨7,3,460,477,476,66,192,384,260⟩⟩,⟨6,1210106412364683944133633,⟨31,59,268,25,56,58,128,384,260⟩⟩,⟨7,1208926973665471139677185,⟨31,59,268,25,56,122,64,256,260⟩⟩,⟨8,1181745671559376274433,⟨31,59,12,25,56,122,192,128,4⟩⟩]⟩
theorem node1646 : UpperPrefix a [2,5,8,0,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,3,1] 30 cert1646 (by decide +kernel)

def cert1647 : Leaf := ⟨⟨480,448,194,482,450,386,258,66,194⟩,[],[(4,5,4)],⟨7,35,268,25,56,112,194,450,454⟩,⟨7,35,268,25,56,112,192,384,260⟩,[⟨0,1214857656243511408722944,⟨502,482,316,508,60,112,192,384,276⟩⟩,⟨2,1210144558379987682465281,⟨251,123,506,123,58,112,192,416,496⟩⟩,⟨3,1236224102496983634156805,⟨455,483,487,499,242,112,192,449,455⟩⟩,⟨5,1214857654800127519360001,⟨455,451,268,477,28,80,192,384,260⟩⟩]⟩
theorem node1647 : UpperPrefix a [2,5,8,0,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,3,4] 30 cert1647 (by decide +kernel)

def cert1648 : Leaf := ⟨⟨376,344,114,32,0,0,314,122,122⟩,[(5,6)],[(7,5,5)],⟨7,35,268,25,56,224,210,466,342⟩,⟨7,35,268,25,56,224,192,384,260⟩,[⟨0,1214839175792809238070272,⟨502,482,316,508,60,224,224,384,276⟩⟩,⟨2,1210144560279943775262209,⟨251,123,506,123,58,224,224,416,496⟩⟩,⟨1,1210107567535789341409281,⟨29,57,268,25,56,224,224,384,260⟩⟩,⟨6,1210106412362484920878081,⟨31,59,268,25,56,160,128,384,260⟩⟩,⟨8,1181747921160166704129,⟨31,59,12,25,56,224,224,128,4⟩⟩]⟩
theorem node1648 : UpperPrefix a [2,5,8,0,3,7] 30 :=
  Boolean.leaf_sound a [2,5,8,0,3,7] 30 cert1648 (by decide +kernel)

theorem node1649 : UpperPrefix a [2,5,8,0,3] 30 :=
  branch_upper a [2,5,8,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,3,0] 30 (by decide +kernel))
  node1646
  (invalid_upper a [2,5,8,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,3,3] 30 (by decide +kernel))
  node1647
  (invalid_upper a [2,5,8,0,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,3,6] 30 (by decide +kernel))
  node1648
  (invalid_upper a [2,5,8,0,3,8] 30 (by decide +kernel)))

def cert1650 : Leaf := ⟨⟨440,408,176,416,0,408,312,56,184⟩,[(4,5)],[(6,4,4),(1,5,1)],⟨7,35,268,25,112,98,216,408,412⟩,⟨7,35,268,25,112,98,192,384,260⟩,[⟨0,1266886859753513672508416,⟨502,50,476,508,112,114,192,384,452⟩⟩,⟨2,1210144549392579637024257,⟨251,123,506,123,112,122,192,400,496⟩⟩]⟩
theorem node1650 : UpperPrefix a [2,5,8,0,6,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,1] 30 cert1650 (by decide +kernel)

def cert1651 : Leaf := ⟨⟨440,408,178,288,0,402,306,50,178⟩,[(4,5)],[(6,4,4)],⟨7,35,268,25,112,104,210,402,406⟩,⟨7,35,268,25,112,104,192,384,260⟩,[⟨0,1214857656210388620936192,⟨470,498,316,508,112,124,192,384,260⟩⟩,⟨2,1210144549392579637024257,⟨251,123,506,123,112,122,192,400,496⟩⟩,⟨3,1214857655928362812572673,⟨471,499,260,465,112,112,192,384,260⟩⟩,⟨1,1210107565286050977808385,⟨13,57,268,25,112,120,192,384,260⟩⟩,⟨7,1208926973665333566505985,⟨15,59,268,25,112,120,64,256,260⟩⟩]⟩
theorem node1651 : UpperPrefix a [2,5,8,0,6,3] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,3] 30 cert1651 (by decide +kernel)

def cert1652 : Leaf := ⟨⟨56,24,179,34,0,0,315,59,187⟩,[(4,5),(5,4)],[(6,4,4),(6,4,5)],⟨7,35,268,25,112,112,202,394,398⟩,⟨7,35,268,25,112,112,192,384,260⟩,[⟨2,1210144561218926705382913,⟨251,123,506,123,112,112,240,432,496⟩⟩,⟨7,1208926976484481380127749,⟨15,59,271,59,112,112,112,256,261⟩⟩,⟨8,1181748490569616724997,⟨15,59,15,59,112,112,240,128,5⟩⟩]⟩
theorem node1652 : UpperPrefix a [2,5,8,0,6,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,4] 30 cert1652 (by decide +kernel)

def cert1653 : Leaf := ⟨⟨312,280,51,290,0,0,315,59,59⟩,[(4,5),(5,6)],[(6,4,4),(7,5,4),(7,5,5)],⟨7,35,268,25,112,224,218,410,286⟩,⟨7,35,268,25,112,224,192,384,260⟩,[⟨2,1210144560304133031073281,⟨251,123,506,123,112,240,240,432,496⟩⟩]⟩
theorem node1653 : UpperPrefix a [2,5,8,0,6,7] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,7] 30 cert1653 (by decide +kernel)

theorem node1654 : UpperPrefix a [2,5,8,0,6] 30 :=
  branch_upper a [2,5,8,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,6,0] 30 (by decide +kernel))
  node1650
  (invalid_upper a [2,5,8,0,6,2] 30 (by decide +kernel))
  node1651
  node1652
  (invalid_upper a [2,5,8,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,6] 30 (by decide +kernel))
  node1653
  (invalid_upper a [2,5,8,0,6,8] 30 (by decide +kernel)))

def cert1655 : Leaf := ⟨⟨248,216,208,224,72,152,24,88,216⟩,[],[(1,5,1)],⟨7,35,268,25,176,98,216,472,348⟩,⟨7,35,268,25,176,98,192,384,260⟩,[⟨0,1266886859751314649252864,⟨502,50,476,508,176,98,192,384,452⟩⟩,⟨2,1210144549389693419001345,⟨251,123,506,123,176,106,192,400,496⟩⟩,⟨8,1184347355643567480069,⟨7,35,47,123,250,114,250,251,7⟩⟩,⟨5,1247960427112391857144833,⟨7,3,460,477,144,66,192,384,260⟩⟩]⟩
theorem node1655 : UpperPrefix a [2,5,8,0,7,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,1] 30 cert1655 (by decide +kernel)

def cert1656 : Leaf := ⟨⟨248,216,240,224,64,144,48,112,240⟩,[],[],⟨7,35,268,25,176,104,194,464,340⟩,⟨7,35,268,25,176,104,194,384,260⟩,[⟨0,1414156279183021502891008,⟨470,502,444,508,436,508,466,384,276⟩⟩,⟨1,1664340193613410435858433,⟨29,445,268,25,436,508,508,384,260⟩⟩,⟨2,1212505734887326101804545,⟨251,123,506,123,176,122,250,400,496⟩⟩,⟨8,1184347355643567480069,⟨7,35,47,123,250,122,250,251,7⟩⟩,⟨3,1214931442904657650779137,⟨471,499,388,465,176,240,210,384,260⟩⟩]⟩
theorem node1656 : UpperPrefix a [2,5,8,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,3,1] 30 cert1656 (by decide +kernel)

def cert1657 : Leaf := ⟨⟨360,328,98,354,330,274,0,106,106⟩,[(6,4)],[(7,4,6),(4,6,5)],⟨7,35,268,25,176,104,208,450,326⟩,⟨7,35,268,25,176,104,208,384,260⟩,[⟨0,1214858088694560033080320,⟨502,498,380,508,240,124,208,384,292⟩⟩,⟨2,1210151755149097211794945,⟨251,123,506,123,240,106,208,464,496⟩⟩]⟩
theorem node1657 : UpperPrefix a [2,5,8,0,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,3,4] 30 cert1657 (by decide +kernel)

theorem node1658 : UpperPrefix a [2,5,8,0,7,3] 30 :=
  branch_upper a [2,5,8,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,3,0] 30 (by decide +kernel))
  node1656
  (invalid_upper a [2,5,8,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,3] 30 (by decide +kernel))
  node1657
  (invalid_upper a [2,5,8,0,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,8] 30 (by decide +kernel)))

def cert1659 : Leaf := ⟨⟨88,88,81,64,73,137,25,89,89⟩,[],[(7,4,5)],⟨7,35,268,25,176,112,194,456,332⟩,⟨7,35,268,25,176,112,194,384,260⟩,[⟨1,1512929318256264854110209,⟨13,57,268,25,176,500,508,384,260⟩⟩,⟨2,1210144560661886626960897,⟨251,123,506,123,176,112,250,432,496⟩⟩,⟨5,1408834392107224617452611,⟨455,463,396,477,412,477,455,384,260⟩⟩,⟨8,1184347355643567480069,⟨7,35,47,123,250,112,250,251,7⟩⟩]⟩
theorem node1659 : UpperPrefix a [2,5,8,0,7,4,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,4,1] 30 cert1659 (by decide +kernel)

def cert1660 : Leaf := ⟨⟨104,72,99,98,72,136,35,107,107⟩,[],[(7,4,5)],⟨7,35,268,25,176,112,200,450,326⟩,⟨7,35,268,25,176,112,200,384,260⟩,[⟨2,1210144560661886626960897,⟨251,123,506,123,176,112,250,432,496⟩⟩,⟨4,1404102965506700806743081,⟨455,419,461,463,419,487,461,384,324⟩⟩,⟨8,1184347355643567480069,⟨7,35,47,123,250,112,250,251,7⟩⟩,⟨0,1210107567540049546314752,⟨6,34,268,24,176,112,248,384,260⟩⟩,⟨1,1210107567540049546313729,⟨5,33,268,25,176,112,248,384,260⟩⟩]⟩
theorem node1660 : UpperPrefix a [2,5,8,0,7,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,4,3] 30 cert1660 (by decide +kernel)

theorem node1661 : UpperPrefix a [2,5,8,0,7,4] 30 :=
  branch_upper a [2,5,8,0,7,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,4,0] 30 (by decide +kernel))
  node1659
  (invalid_upper a [2,5,8,0,7,4,2] 30 (by decide +kernel))
  node1660
  (invalid_upper a [2,5,8,0,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,8] 30 (by decide +kernel)))

theorem node1662 : UpperPrefix a [2,5,8,0,7] 30 :=
  branch_upper a [2,5,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,0] 30 (by decide +kernel))
  node1655
  (invalid_upper a [2,5,8,0,7,2] 30 (by decide +kernel))
  node1658
  node1661
  (invalid_upper a [2,5,8,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,8] 30 (by decide +kernel)))

theorem node1663 : UpperPrefix a [2,5,8,0] 30 :=
  branch_upper a [2,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,0] 30 (by decide +kernel))
  node1645
  (invalid_upper a [2,5,8,0,2] 30 (by decide +kernel))
  node1649
  (invalid_upper a [2,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,5] 30 (by decide +kernel))
  node1654
  node1662
  (invalid_upper a [2,5,8,0,8] 30 (by decide +kernel)))

#print axioms node1663
end Delivery.FiniteExclusion.Sharp2x7
