import RegularNineSharp3x6Base
import RegularNineSharp3x6C005
import RegularNineSharp3x6C006
import RegularNineSharp3x6C007
import RegularNineSharp3x6C011
import RegularNineSharp3x6C013
import RegularNineSharp3x6C016
import RegularNineSharp3x6C019
import RegularNineSharp3x6C022
import RegularNineSharp3x6C023
import RegularNineSharp3x6C024
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert1600 : Local := ⟨⟨304,0,282,33,0,413,0,57,49⟩,[(1,6),(4,5),(6,1)],[(7,1,5),(6,4,4),(1,5,2),(2,6,5)]⟩
theorem node1600 : UpperPrefix a [3,7,5,8,6,1,2] 30 :=
  local_sound a [3,7,5,8,6,1,2] 30 cert1600 (by decide +kernel)

def cert1601 : Leaf := ⟨⟨308,313,18,37,0,149,37,61,53⟩,[(4,5)],[(7,1,5),(6,4,4),(1,5,2)],⟨11,134,37,280,112,98,208,389,269⟩,⟨11,134,37,280,112,98,208,384,264⟩,[⟨3,1210107601420605929554945,⟨119,246,53,272,112,114,208,384,256⟩⟩,⟨8,1181781805977828590593,⟨127,246,53,24,112,114,208,128,8⟩⟩]⟩
theorem node1601 : UpperPrefix a [3,7,5,8,6,1,4] 30 :=
  Boolean.leaf_sound a [3,7,5,8,6,1,4] 30 cert1601 (by decide +kernel)

theorem node1602 : UpperPrefix a [3,7,5,8,6,1] 30 :=
  branch_upper a [3,7,5,8,6,1] 30 (by decide) (fin9_cases _
  node1599
  (invalid_upper a [3,7,5,8,6,1,1] 30 (by decide +kernel))
  node1600
  (invalid_upper a [3,7,5,8,6,1,3] 30 (by decide +kernel))
  node1601
  (invalid_upper a [3,7,5,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,1,8] 30 (by decide +kernel)))

def cert1603 : Leaf := ⟨⟨432,288,386,162,0,387,314,58,178⟩,[(4,5)],[(6,4,4),(0,6,5)],⟨11,134,37,280,112,100,193,402,282⟩,⟨11,134,37,280,112,100,193,384,264⟩,[⟨2,1219570799039334383092739,⟨459,475,113,280,112,112,193,384,264⟩⟩,⟨3,1210107568105197466059777,⟨3,134,53,304,118,118,247,384,256⟩⟩,⟨4,1210107568097501958407169,⟨11,134,37,296,102,102,231,384,264⟩⟩]⟩
theorem node1603 : UpperPrefix a [3,7,5,8,6,2,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,6,2,0] 30 cert1603 (by decide +kernel)

def cert1604 : Leaf := ⟨⟨304,313,282,35,0,283,0,59,51⟩,[(4,5),(6,1)],[(7,1,6),(6,4,4)],⟨11,134,37,280,112,100,194,401,281⟩,⟨11,134,37,280,112,100,194,384,264⟩,[⟨2,1465613471494479361868867,⟨459,475,505,408,505,505,459,384,264⟩⟩]⟩
theorem node1604 : UpperPrefix a [3,7,5,8,6,2,1] 30 :=
  Boolean.leaf_sound a [3,7,5,8,6,2,1] 30 cert1604 (by decide +kernel)

def cert1605 : Leaf := ⟨⟨400,281,408,131,0,409,265,27,147⟩,[(4,5)],[(6,4,4)],⟨11,134,37,280,112,100,208,387,267⟩,⟨11,134,37,280,112,100,208,384,264⟩,[⟨5,1441992792882092662869041,⟨459,134,391,473,475,463,473,384,328⟩⟩,⟨2,1224302442937436948399107,⟨459,475,505,280,112,120,208,384,264⟩⟩,⟨1,1210107601420607003295745,⟨125,244,53,280,112,116,208,384,264⟩⟩]⟩
theorem node1605 : UpperPrefix a [3,7,5,8,6,2,4] 30 :=
  Boolean.leaf_sound a [3,7,5,8,6,2,4] 30 cert1605 (by decide +kernel)

theorem node1606 : UpperPrefix a [3,7,5,8,6,2] 30 :=
  branch_upper a [3,7,5,8,6,2] 30 (by decide) (fin9_cases _
  node1603
  node1604
  (invalid_upper a [3,7,5,8,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,2,3] 30 (by decide +kernel))
  node1605
  (invalid_upper a [3,7,5,8,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,2,8] 30 (by decide +kernel)))

def cert1607 : Leaf := ⟨⟨436,48,146,166,0,0,318,62,182⟩,[(4,5),(5,4)],[(6,4,4),(6,4,5)],⟨11,134,37,280,112,112,193,390,270⟩,⟨11,134,37,280,112,112,193,384,264⟩,[⟨0,1238497107234638059801600,⟨394,398,446,312,112,112,240,384,264⟩⟩,⟨3,1210107568105197466059777,⟨3,134,53,304,118,118,247,384,256⟩⟩,⟨8,1181748490569365095425,⟨11,134,53,56,118,118,247,128,8⟩⟩]⟩
theorem node1607 : UpperPrefix a [3,7,5,8,6,4,0] 30 :=
  Boolean.leaf_sound a [3,7,5,8,6,4,0] 30 cert1607 (by decide +kernel)

def cert1608 : Local := ⟨⟨308,313,282,39,0,0,0,63,55⟩,[(4,5),(5,4),(6,1)],[(7,1,6),(6,4,4),(6,4,5)]⟩
theorem node1608 : UpperPrefix a [3,7,5,8,6,4,1] 30 :=
  local_sound a [3,7,5,8,6,4,1] 30 cert1608 (by decide +kernel)

def cert1609 : Local := ⟨⟨436,0,410,167,0,0,0,63,183⟩,[(1,6),(4,5),(5,4),(6,1)],[(6,4,4),(6,4,5)]⟩
theorem node1609 : UpperPrefix a [3,7,5,8,6,4,2] 30 :=
  local_sound a [3,7,5,8,6,4,2] 30 cert1609 (by decide +kernel)

theorem node1610 : UpperPrefix a [3,7,5,8,6,4] 30 :=
  branch_upper a [3,7,5,8,6,4] 30 (by decide) (fin9_cases _
  node1607
  node1608
  node1609
  (invalid_upper a [3,7,5,8,6,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,4,8] 30 (by decide +kernel)))

theorem node1611 : UpperPrefix a [3,7,5,8,6] 30 :=
  branch_upper a [3,7,5,8,6] 30 (by decide) (fin9_cases _
  node1598
  node1602
  node1606
  (invalid_upper a [3,7,5,8,6,3] 30 (by decide +kernel))
  node1610
  (invalid_upper a [3,7,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,6,8] 30 (by decide +kernel)))

theorem node1612 : UpperPrefix a [3,7,5,8] 30 :=
  branch_upper a [3,7,5,8] 30 (by decide) (fin9_cases _
  node1567
  node1584
  node1592
  (invalid_upper a [3,7,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,5] 30 (by decide +kernel))
  node1611
  (invalid_upper a [3,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,8,8] 30 (by decide +kernel)))

theorem node1613 : UpperPrefix a [3,7,5] 30 :=
  branch_upper a [3,7,5] 30 (by decide) (fin9_cases _
  node1451
  node1477
  node1506
  (invalid_upper a [3,7,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,7,5,5] 30 (by decide +kernel))
  node1557
  (invalid_upper a [3,7,5,7] 30 (by decide +kernel))
  node1612)

theorem node1614 : UpperPrefix a [3,7] 30 :=
  branch_upper a [3,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [3,7,1] [2,3,7] 30 (by decide +kernel) node338)
  (invalid_upper a [3,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,7,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [3,7,4] [3,6,5] 30 (by decide +kernel) node1411)
  node1613
  (PrefixConjugacy.upper aut9 [3,7,6] [3,6,4] 30 (by decide +kernel) node1230)
  (invalid_upper a [3,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [3,7,8] [3,4,5] 30 (by decide +kernel) node472))

theorem node1615 : UpperPrefix a [3,8] 30 :=
  branch_upper a [3,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [3,8,1] [2,3,8] 30 (by decide +kernel) node383)
  (invalid_upper a [3,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut13 [3,8,4] [3,5,4] 30 (by decide +kernel) node888)
  (PrefixConjugacy.upper aut13 [3,8,5] [3,6,4] 30 (by decide +kernel) node1230)
  (PrefixConjugacy.upper aut9 [3,8,6] [3,6,5] 30 (by decide +kernel) node1411)
  (PrefixConjugacy.upper aut8 [3,8,7] [3,5,4] 30 (by decide +kernel) node888)
  (invalid_upper a [3,8,8] 30 (by decide +kernel)))

theorem node1616 : UpperPrefix a [3] 30 :=
  branch_upper a [3] 30 (by decide) (fin9_cases _
  node386
  (invalid_upper a [3,1] 30 (by decide +kernel))
  (invalid_upper a [3,2] 30 (by decide +kernel))
  (invalid_upper a [3,3] 30 (by decide +kernel))
  node739
  node1058
  node1412
  node1614
  node1615)

theorem node1617 : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
  (invalid_upper a [0] 30 (by decide +kernel))
  (invalid_upper a [1] 30 (by decide +kernel))
  node385
  node1616
  (PrefixConjugacy.upper aut5 [4] [3] 30 (by decide +kernel) node1616)
  (PrefixConjugacy.upper aut4 [5] [3] 30 (by decide +kernel) node1616)
  (PrefixConjugacy.upper aut3 [6] [3] 30 (by decide +kernel) node1616)
  (PrefixConjugacy.upper aut2 [7] [3] 30 (by decide +kernel) node1616)
  (PrefixConjugacy.upper aut1 [8] [3] 30 (by decide +kernel) node1616))

#print axioms node1617
end Delivery.FiniteExclusion.Sharp3x6
