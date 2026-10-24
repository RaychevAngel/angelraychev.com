import RegularNineSharp2x7Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert1664 : Leaf := ⟨⟨472,0,208,481,0,412,284,92,216⟩,[(1,4),(4,1)],[(5,1,3),(0,4,3)],⟨7,35,268,26,49,248,216,472,476⟩,⟨7,35,268,26,49,96,192,384,260⟩,[⟨1,1247960428519904179650561,⟨21,49,492,508,49,96,192,384,260⟩⟩,⟨2,1210107565283991674168321,⟨27,59,264,26,59,96,192,384,256⟩⟩]⟩
theorem node1664 : UpperPrefix a [2,5,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,0] 30 cert1664 (by decide +kernel)

def cert1665 : Leaf := ⟨⟨472,0,208,416,386,410,280,88,216⟩,[(1,5)],[(5,1,3),(0,5,1)],⟨7,35,268,26,56,97,208,464,468⟩,⟨7,35,268,26,56,97,192,384,260⟩,[⟨2,1210144548952506550470145,⟨251,123,472,58,58,123,192,384,448⟩⟩,⟨1,1323666154147171919724545,⟨5,33,460,476,508,97,192,384,260⟩⟩,⟨6,1210106412364690386600961,⟨31,59,268,26,58,59,128,384,260⟩⟩]⟩
theorem node1665 : UpperPrefix a [2,5,8,1,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,3,0] 30 cert1665 (by decide +kernel)

def cert1666 : Leaf := ⟨⟨448,452,195,416,384,389,261,69,193⟩,[],[(5,1,3),(4,5,4)],⟨7,35,268,26,56,112,193,449,453⟩,⟨7,35,268,26,56,112,192,384,260⟩,[⟨3,1236152188455183828651269,⟨455,483,487,242,48,112,192,449,455⟩⟩,⟨1,1214857656243511406624769,⟨501,481,316,248,56,112,192,384,276⟩⟩,⟨0,1210107565283989527725056,⟨30,58,268,26,56,112,192,384,260⟩⟩,⟨2,1210107565283989526676481,⟨27,59,264,26,56,112,192,384,256⟩⟩,⟨6,1210106412362484920878081,⟨31,59,268,26,56,48,128,384,260⟩⟩]⟩
theorem node1666 : UpperPrefix a [2,5,8,1,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,3,4] 30 cert1666 (by decide +kernel)

def cert1667 : Leaf := ⟨⟨344,348,80,356,324,0,284,92,88⟩,[(5,6)],[(5,1,3),(7,5,5)],⟨7,35,268,26,56,224,193,464,340⟩,⟨7,35,268,26,56,224,193,384,260⟩,[⟨0,1664340193611211408409600,⟨30,446,268,30,444,500,508,384,260⟩⟩,⟨1,1252691930660858261143553,⟨501,481,444,508,444,224,481,384,276⟩⟩]⟩
theorem node1667 : UpperPrefix a [2,5,8,1,3,7,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,3,7,0] 30 cert1667 (by decide +kernel)

def cert1668 : Leaf := ⟨⟨344,348,83,288,256,0,269,93,89⟩,[(5,6)],[(5,1,3),(7,5,5)],⟨7,35,268,26,56,224,208,449,325⟩,⟨7,35,268,26,56,224,208,384,260⟩,[⟨1,1214857766652071021379585,⟨501,481,380,248,120,224,240,384,276⟩⟩,⟨0,1210107567535789341410304,⟨30,58,268,26,56,224,240,384,260⟩⟩,⟨2,1210107567535789340361729,⟨27,59,264,26,56,224,240,384,256⟩⟩,⟨6,1210106412362484920878081,⟨31,59,268,26,56,160,144,384,260⟩⟩]⟩
theorem node1668 : UpperPrefix a [2,5,8,1,3,7,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,3,7,4] 30 cert1668 (by decide +kernel)

theorem node1669 : UpperPrefix a [2,5,8,1,3,7] 30 :=
  branch_upper a [2,5,8,1,3,7] 30 (by decide) (fin9_cases _
  node1667
  (invalid_upper a [2,5,8,1,3,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,7,3] 30 (by decide +kernel))
  node1668
  (invalid_upper a [2,5,8,1,3,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,7,8] 30 (by decide +kernel)))

theorem node1670 : UpperPrefix a [2,5,8,1,3] 30 :=
  branch_upper a [2,5,8,1,3] 30 (by decide) (fin9_cases _
  node1665
  (invalid_upper a [2,5,8,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,3] 30 (by decide +kernel))
  node1666
  (invalid_upper a [2,5,8,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,6] 30 (by decide +kernel))
  node1669
  (invalid_upper a [2,5,8,1,3,8] 30 (by decide +kernel)))

def cert1671 : Local := ⟨⟨408,0,146,420,0,414,286,30,154⟩,[(1,5),(4,5)],[(5,1,3),(6,4,4),(0,5,1)]⟩
theorem node1671 : UpperPrefix a [2,5,8,1,6,0] 30 :=
  local_sound a [2,5,8,1,6,0] 30 cert1671 (by decide +kernel)

def cert1672 : Leaf := ⟨⟨408,412,147,288,0,405,277,21,145⟩,[(4,5)],[(5,1,3),(6,4,4)],⟨7,35,268,26,112,104,209,401,405⟩,⟨7,35,268,26,112,104,192,384,260⟩,[⟨1,1214857656210388618838017,⟨469,497,316,248,112,120,192,384,260⟩⟩,⟨3,1214857655928362812572673,⟨471,499,260,210,112,112,192,384,260⟩⟩,⟨0,1210107565286050977809408,⟨14,58,268,26,112,120,192,384,260⟩⟩,⟨2,1210107565286050976760833,⟨11,59,264,26,112,120,192,384,256⟩⟩,⟨7,1208926973665333566505985,⟨15,59,268,26,112,120,64,256,260⟩⟩]⟩
theorem node1672 : UpperPrefix a [2,5,8,1,6,3] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,3] 30 cert1672 (by decide +kernel)

def cert1673 : Leaf := ⟨⟨392,412,131,421,0,0,271,15,139⟩,[(4,5),(5,4)],[(5,1,3),(6,4,4),(6,4,5)],⟨7,35,268,26,112,112,201,393,397⟩,⟨7,35,268,26,112,112,192,384,260⟩,[⟨4,1266886859714412290245641,⟨455,35,461,463,96,96,192,384,452⟩⟩]⟩
theorem node1673 : UpperPrefix a [2,5,8,1,6,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,4] 30 cert1673 (by decide +kernel)

def cert1674 : Local := ⟨⟨280,284,19,293,0,0,287,31,27⟩,[(4,5),(5,6)],[(5,1,3),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node1674 : UpperPrefix a [2,5,8,1,6,7] 30 :=
  local_sound a [2,5,8,1,6,7] 30 cert1674 (by decide +kernel)

theorem node1675 : UpperPrefix a [2,5,8,1,6] 30 :=
  branch_upper a [2,5,8,1,6] 30 (by decide) (fin9_cases _
  node1671
  (invalid_upper a [2,5,8,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,2] 30 (by decide +kernel))
  node1672
  node1673
  (invalid_upper a [2,5,8,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,6] 30 (by decide +kernel))
  node1674
  (invalid_upper a [2,5,8,1,6,8] 30 (by decide +kernel)))

def cert1676 : Leaf := ⟨⟨472,0,208,32,334,414,24,92,216⟩,[(1,5)],[(5,1,3),(0,5,1)],⟨7,35,268,26,176,97,216,472,348⟩,⟨7,35,268,26,176,97,192,384,260⟩,[⟨1,1247960428238291763986433,⟨5,33,460,476,176,97,192,384,260⟩⟩,⟨2,1210107853514229984281601,⟨3,35,264,90,250,99,192,384,256⟩⟩,⟨8,1182033899600810624001,⟨7,35,12,90,250,99,192,128,4⟩⟩,⟨6,1210106412362349226771457,⟨7,35,268,26,186,35,128,384,260⟩⟩,⟨7,1208926973663136422315009,⟨7,35,268,26,58,99,64,256,260⟩⟩]⟩
theorem node1676 : UpperPrefix a [2,5,8,1,7,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,0] 30 cert1676 (by decide +kernel)

def cert1677 : Leaf := ⟨⟨472,216,208,224,64,144,276,84,208⟩,[],[(5,1,3)],⟨7,35,268,26,176,104,193,464,340⟩,⟨7,35,268,26,176,104,193,384,260⟩,[⟨0,1664340193613410435859456,⟨30,446,268,30,436,508,508,384,260⟩⟩,⟨1,1413565983372662797238273,⟨469,501,444,508,436,508,449,384,276⟩⟩,⟨2,1210107567540062430200833,⟨3,43,264,26,184,122,251,384,256⟩⟩,⟨3,1214857655926163789317121,⟨471,499,260,210,176,96,449,384,260⟩⟩,⟨8,1181747925433256543233,⟨7,43,12,26,184,122,251,128,4⟩⟩]⟩
theorem node1677 : UpperPrefix a [2,5,8,1,7,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,3,0] 30 cert1677 (by decide +kernel)

def cert1678 : Leaf := ⟨⟨72,76,67,101,79,23,0,79,75⟩,[(6,4)],[(5,1,3),(7,4,6),(4,6,5)],⟨7,35,268,26,176,104,208,449,325⟩,⟨7,35,268,26,176,104,208,384,260⟩,[⟨8,1184347355654304894213,⟨7,35,47,122,250,120,250,251,7⟩⟩]⟩
theorem node1678 : UpperPrefix a [2,5,8,1,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,3,4] 30 cert1678 (by decide +kernel)

theorem node1679 : UpperPrefix a [2,5,8,1,7,3] 30 :=
  branch_upper a [2,5,8,1,7,3] 30 (by decide) (fin9_cases _
  node1677
  (invalid_upper a [2,5,8,1,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,3] 30 (by decide +kernel))
  node1678
  (invalid_upper a [2,5,8,1,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,8] 30 (by decide +kernel)))

def cert1680 : Leaf := ⟨⟨328,80,67,97,67,131,270,79,75⟩,[],[(5,1,3),(7,4,5)],⟨7,35,268,26,176,112,193,456,332⟩,⟨7,35,268,26,176,112,193,384,260⟩,[⟨4,1266886877728810799727625,⟨455,99,461,463,160,96,193,384,452⟩⟩,⟨2,1210107567540062430200833,⟨3,43,264,26,184,122,251,384,256⟩⟩,⟨8,1181747925433256543233,⟨7,43,12,26,184,122,251,128,4⟩⟩,⟨3,1210107567540048472605697,⟨7,35,260,18,176,114,243,384,260⟩⟩]⟩
theorem node1680 : UpperPrefix a [2,5,8,1,7,4,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,4,0] 30 cert1680 (by decide +kernel)

def cert1681 : Leaf := ⟨⟨72,76,67,101,76,140,7,79,75⟩,[],[(5,1,3),(7,4,5)],⟨7,35,268,26,176,112,200,449,325⟩,⟨7,35,268,26,176,112,200,384,260⟩,[⟨4,1725851075640342806029353,⟨455,419,461,463,419,487,461,384,452⟩⟩,⟨8,1184347355654304894213,⟨7,35,47,122,250,120,250,251,7⟩⟩,⟨0,1210107567540049546314752,⟨6,34,268,26,176,112,248,384,260⟩⟩,⟨1,1210107567540049546313729,⟨5,33,268,24,176,112,248,384,260⟩⟩]⟩
theorem node1681 : UpperPrefix a [2,5,8,1,7,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,4,3] 30 cert1681 (by decide +kernel)

theorem node1682 : UpperPrefix a [2,5,8,1,7,4] 30 :=
  branch_upper a [2,5,8,1,7,4] 30 (by decide) (fin9_cases _
  node1680
  (invalid_upper a [2,5,8,1,7,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,2] 30 (by decide +kernel))
  node1681
  (invalid_upper a [2,5,8,1,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,8] 30 (by decide +kernel)))

theorem node1683 : UpperPrefix a [2,5,8,1,7] 30 :=
  branch_upper a [2,5,8,1,7] 30 (by decide) (fin9_cases _
  node1676
  (invalid_upper a [2,5,8,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,2] 30 (by decide +kernel))
  node1679
  node1682
  (invalid_upper a [2,5,8,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,8] 30 (by decide +kernel)))

theorem node1684 : UpperPrefix a [2,5,8,1] 30 :=
  branch_upper a [2,5,8,1] 30 (by decide) (fin9_cases _
  node1664
  (invalid_upper a [2,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,2] 30 (by decide +kernel))
  node1670
  (invalid_upper a [2,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,5] 30 (by decide +kernel))
  node1675
  node1683
  (invalid_upper a [2,5,8,1,8] 30 (by decide +kernel)))

def cert1685 : Leaf := ⟨⟨504,0,208,388,0,413,284,92,216⟩,[(1,4),(4,1)],[(1,5,1),(1,5,4)],⟨7,35,268,88,49,98,216,408,412⟩,⟨7,35,268,88,49,98,192,384,260⟩,[⟨0,1323666154147174067209216,⟨6,34,460,476,508,98,192,384,260⟩⟩,⟨5,1323666153021274160366593,⟨7,3,460,476,477,66,192,384,260⟩⟩]⟩
theorem node1685 : UpperPrefix a [2,5,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,1] 30 cert1685 (by decide +kernel)

def cert1686 : Leaf := ⟨⟨184,0,179,167,0,0,55,55,179⟩,[(1,4),(4,1),(5,3)],[(6,3,5)],⟨7,35,268,88,49,104,210,402,406⟩,⟨7,35,268,88,49,104,192,384,260⟩,[⟨3,1215005662224317693305857,⟨471,499,324,210,499,96,192,384,260⟩⟩,⟨8,1184058558340322635013,⟨23,51,63,122,51,104,250,251,23⟩⟩]⟩
theorem node1686 : UpperPrefix a [2,5,8,6,0,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,3] 30 cert1686 (by decide +kernel)

def cert1687 : Leaf := ⟨⟨488,0,227,0,0,0,303,111,235⟩,[(1,4),(3,5),(4,1),(5,3)],[],⟨7,35,268,88,49,112,202,394,398⟩,⟨7,35,268,88,49,112,192,384,260⟩,[⟨4,1247960428237192252367881,⟨7,35,461,463,35,98,192,384,260⟩⟩]⟩
theorem node1687 : UpperPrefix a [2,5,8,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,4] 30 cert1687 (by decide +kernel)

def cert1688 : Leaf := ⟨⟨376,0,113,293,0,0,317,125,121⟩,[(1,4),(4,1),(5,6)],[(7,5,5)],⟨7,35,268,88,49,224,194,408,284⟩,⟨7,35,268,88,49,224,194,384,260⟩,[⟨1,1550782037370540531908609,⟨21,53,428,508,53,492,508,384,260⟩⟩]⟩
theorem node1688 : UpperPrefix a [2,5,8,6,0,7,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,7,1] 30 cert1688 (by decide +kernel)

def cert1689 : Leaf := ⟨⟨312,0,51,295,0,0,311,63,59⟩,[(1,4),(4,1),(5,6)],[(7,5,5)],⟨7,35,268,88,49,224,200,402,278⟩,⟨7,35,268,88,49,224,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩]⟩
theorem node1689 : UpperPrefix a [2,5,8,6,0,7,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,7,3] 30 cert1689 (by decide +kernel)

def cert1690 : Local := ⟨⟨360,0,99,0,0,0,303,111,107⟩,[(1,4),(3,6),(4,1),(5,6)],[(7,5,5),(4,6,3)]⟩
theorem node1690 : UpperPrefix a [2,5,8,6,0,7,4] 30 :=
  local_sound a [2,5,8,6,0,7,4] 30 cert1690 (by decide +kernel)

theorem node1691 : UpperPrefix a [2,5,8,6,0,7] 30 :=
  branch_upper a [2,5,8,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,6,0,7,0] 30 (by decide +kernel))
  node1688
  (invalid_upper a [2,5,8,6,0,7,2] 30 (by decide +kernel))
  node1689
  node1690
  (invalid_upper a [2,5,8,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,7,8] 30 (by decide +kernel)))

theorem node1692 : UpperPrefix a [2,5,8,6,0] 30 :=
  branch_upper a [2,5,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,6,0,0] 30 (by decide +kernel))
  node1685
  (invalid_upper a [2,5,8,6,0,2] 30 (by decide +kernel))
  node1686
  node1687
  (invalid_upper a [2,5,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,6] 30 (by decide +kernel))
  node1691
  (invalid_upper a [2,5,8,6,0,8] 30 (by decide +kernel)))

def cert1693 : Leaf := ⟨⟨472,0,208,388,0,414,284,92,216⟩,[(1,5),(4,1)],[(5,1,4),(0,5,1),(0,5,4)],⟨7,35,268,88,50,97,216,408,412⟩,⟨7,35,268,88,50,97,192,384,260⟩,[⟨1,1323666154147174067208193,⟨5,33,460,476,508,97,192,384,260⟩⟩]⟩
theorem node1693 : UpperPrefix a [2,5,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,0] 30 cert1693 (by decide +kernel)

def cert1694 : Leaf := ⟨⟨152,156,147,135,0,0,31,31,155⟩,[(4,1),(5,3)],[(5,1,4),(6,3,5)],⟨7,35,268,88,50,104,209,401,405⟩,⟨7,35,268,88,50,104,192,384,260⟩,[⟨8,1184058562742664105221,⟨23,59,63,120,58,120,250,251,23⟩⟩]⟩
theorem node1694 : UpperPrefix a [2,5,8,6,1,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,3] 30 cert1694 (by decide +kernel)

def cert1695 : Leaf := ⟨⟨472,476,209,0,0,0,285,93,217⟩,[(3,5),(4,1),(5,3)],[(5,1,4)],⟨7,35,268,88,50,112,201,393,397⟩,⟨7,35,268,88,50,112,192,384,260⟩,[⟨1,1219570781866893082361857,⟨453,493,300,124,508,124,192,384,260⟩⟩]⟩
theorem node1695 : UpperPrefix a [2,5,8,6,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,4] 30 cert1695 (by decide +kernel)

def cert1696 : Leaf := ⟨⟨344,344,83,259,0,0,282,91,91⟩,[(4,1),(5,6)],[(5,1,4),(7,5,5)],⟨7,35,268,88,50,224,193,408,284⟩,⟨7,35,268,88,50,224,193,384,260⟩,[⟨2,1210144479080748071028225,⟨251,123,408,122,58,250,251,384,384⟩⟩]⟩
theorem node1696 : UpperPrefix a [2,5,8,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,7,0] 30 cert1696 (by decide +kernel)

def cert1697 : Leaf := ⟨⟨280,284,19,263,0,0,279,31,27⟩,[(4,1),(5,6)],[(5,1,4),(7,5,5)],⟨7,35,268,88,50,224,200,401,277⟩,⟨7,35,268,88,50,224,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩]⟩
theorem node1697 : UpperPrefix a [2,5,8,6,1,7,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,7,3] 30 cert1697 (by decide +kernel)

def cert1698 : Local := ⟨⟨328,332,67,0,0,0,271,79,75⟩,[(3,6),(4,1),(5,6)],[(5,1,4),(7,5,5),(4,6,3)]⟩
theorem node1698 : UpperPrefix a [2,5,8,6,1,7,4] 30 :=
  local_sound a [2,5,8,6,1,7,4] 30 cert1698 (by decide +kernel)

theorem node1699 : UpperPrefix a [2,5,8,6,1,7] 30 :=
  branch_upper a [2,5,8,6,1,7] 30 (by decide) (fin9_cases _
  node1696
  (invalid_upper a [2,5,8,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,2] 30 (by decide +kernel))
  node1697
  node1698
  (invalid_upper a [2,5,8,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,8] 30 (by decide +kernel)))

theorem node1700 : UpperPrefix a [2,5,8,6,1] 30 :=
  branch_upper a [2,5,8,6,1] 30 (by decide) (fin9_cases _
  node1693
  (invalid_upper a [2,5,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,2] 30 (by decide +kernel))
  node1694
  node1695
  (invalid_upper a [2,5,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,6] 30 (by decide +kernel))
  node1699
  (invalid_upper a [2,5,8,6,1,8] 30 (by decide +kernel)))

def cert1701 : Leaf := ⟨⟨440,0,144,416,448,414,316,28,152⟩,[(1,5)],[(6,3,4),(0,5,1),(1,6,5)],⟨7,35,268,88,56,97,194,400,404⟩,⟨7,35,268,88,56,97,194,384,260⟩,[⟨5,1323665720675707785315329,⟨7,3,396,476,412,65,194,384,260⟩⟩,⟨2,1210107565286201032197121,⟨19,59,264,88,58,123,218,384,256⟩⟩]⟩
theorem node1701 : UpperPrefix a [2,5,8,6,3,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,0,1] 30 cert1701 (by decide +kernel)

def cert1702 : Local := ⟨⟨424,0,162,0,454,398,302,46,170⟩,[(1,5),(3,6)],[(6,3,4),(0,5,1),(4,6,3)]⟩
theorem node1702 : UpperPrefix a [2,5,8,6,3,0,4] 30 :=
  local_sound a [2,5,8,6,3,0,4] 30 cert1702 (by decide +kernel)

theorem node1703 : UpperPrefix a [2,5,8,6,3,0] 30 :=
  branch_upper a [2,5,8,6,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,6,3,0,0] 30 (by decide +kernel))
  node1701
  (invalid_upper a [2,5,8,6,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,0,3] 30 (by decide +kernel))
  node1702
  (invalid_upper a [2,5,8,6,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,0,8] 30 (by decide +kernel)))

def cert1704 : Leaf := ⟨⟨184,152,176,160,192,153,56,56,184⟩,[],[(6,3,4),(1,5,1),(0,6,5)],⟨7,35,268,88,56,98,193,400,404⟩,⟨7,35,268,88,56,98,193,384,260⟩,[⟨2,1212505662674301492430337,⟨251,123,440,122,56,122,251,384,400⟩⟩,⟨8,1184058565491443207429,⟨23,59,63,122,56,122,251,251,23⟩⟩]⟩
theorem node1704 : UpperPrefix a [2,5,8,6,3,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,1,0] 30 cert1704 (by decide +kernel)

def cert1705 : Leaf := ⟨⟨392,396,129,0,453,397,269,13,137⟩,[(3,6)],[(6,3,4),(1,5,1),(4,6,3)],⟨7,35,268,88,56,98,208,385,389⟩,⟨7,35,268,88,56,98,208,384,260⟩,[⟨5,1451419079103758275183651,⟨391,391,332,476,477,463,476,384,260⟩⟩]⟩
theorem node1705 : UpperPrefix a [2,5,8,6,3,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,1,4] 30 cert1705 (by decide +kernel)

theorem node1706 : UpperPrefix a [2,5,8,6,3,1] 30 :=
  branch_upper a [2,5,8,6,3,1] 30 (by decide) (fin9_cases _
  node1704
  (invalid_upper a [2,5,8,6,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,3] 30 (by decide +kernel))
  node1705
  (invalid_upper a [2,5,8,6,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,8] 30 (by decide +kernel)))

def cert1707 : Leaf := ⟨⟨416,388,163,0,455,0,295,39,163⟩,[(3,5),(5,3)],[(6,3,4),(4,5,4)],⟨7,35,268,88,56,112,195,387,391⟩,⟨7,35,268,88,56,112,192,384,260⟩,[⟨3,1236149882612174614957317,⟨455,483,487,112,48,112,192,449,455⟩⟩]⟩
theorem node1707 : UpperPrefix a [2,5,8,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,4] 30 cert1707 (by decide +kernel)

def cert1708 : Leaf := ⟨⟨312,24,50,34,66,0,318,62,58⟩,[(5,6)],[(6,3,4),(7,5,5)],⟨7,35,268,88,56,224,193,402,278⟩,⟨7,35,268,88,56,224,193,384,260⟩,[⟨0,1224302337107668166509568,⟨406,446,284,124,56,252,508,384,260⟩⟩,⟨2,1210107567542948648223745,⟨19,59,280,122,56,250,251,384,256⟩⟩,⟨8,1181747928319474566145,⟨23,59,28,122,56,250,251,128,4⟩⟩]⟩
theorem node1708 : UpperPrefix a [2,5,8,6,3,7,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,7,0] 30 cert1708 (by decide +kernel)

def cert1709 : Leaf := ⟨⟨312,284,49,288,320,0,317,61,57⟩,[(5,6)],[(6,3,4),(7,5,5)],⟨7,35,268,88,56,224,194,401,277⟩,⟨7,35,268,88,56,224,194,384,260⟩,[⟨1,1224302337107668166508545,⟨405,445,284,124,56,252,508,384,260⟩⟩,⟨0,1210107567542948649239552,⟨22,58,284,120,56,248,250,384,260⟩⟩,⟨2,1210107567542948648190977,⟨19,59,280,120,56,248,250,384,256⟩⟩]⟩
theorem node1709 : UpperPrefix a [2,5,8,6,3,7,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,7,1] 30 cert1709 (by decide +kernel)

def cert1710 : Local := ⟨⟨296,268,35,0,327,0,303,47,43⟩,[(3,6),(5,6)],[(6,3,4),(7,5,5),(4,6,3)]⟩
theorem node1710 : UpperPrefix a [2,5,8,6,3,7,4] 30 :=
  local_sound a [2,5,8,6,3,7,4] 30 cert1710 (by decide +kernel)

theorem node1711 : UpperPrefix a [2,5,8,6,3,7] 30 :=
  branch_upper a [2,5,8,6,3,7] 30 (by decide) (fin9_cases _
  node1708
  node1709
  (invalid_upper a [2,5,8,6,3,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,3] 30 (by decide +kernel))
  node1710
  (invalid_upper a [2,5,8,6,3,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,8] 30 (by decide +kernel)))

theorem node1712 : UpperPrefix a [2,5,8,6,3] 30 :=
  branch_upper a [2,5,8,6,3] 30 (by decide) (fin9_cases _
  node1703
  node1706
  (invalid_upper a [2,5,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,3] 30 (by decide +kernel))
  node1707
  (invalid_upper a [2,5,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,6] 30 (by decide +kernel))
  node1711
  (invalid_upper a [2,5,8,6,3,8] 30 (by decide +kernel)))

def cert1713 : Leaf := ⟨⟨376,0,16,420,332,286,316,28,24⟩,[(1,5)],[(7,4,3),(0,5,1),(1,6,5)],⟨7,35,268,88,176,97,194,408,284⟩,⟨7,35,268,88,176,97,194,384,260⟩,[⟨5,1247960282997203781288961,⟨7,3,396,476,144,65,194,384,260⟩⟩,⟨6,1247959131201599081300993,⟨7,35,396,412,178,35,130,384,260⟩⟩]⟩
theorem node1713 : UpperPrefix a [2,5,8,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,0,1] 30 cert1713 (by decide +kernel)

def cert1714 : Leaf := ⟨⟨312,0,50,420,262,286,308,54,50⟩,[(1,5)],[(7,4,3),(0,5,1)],⟨7,35,268,88,176,97,200,402,278⟩,⟨7,35,268,88,176,97,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩,⟨3,1215152749790346636968961,⟨407,435,260,80,178,499,192,384,260⟩⟩,⟨1,1210107853514229985312769,⟨5,33,268,88,248,97,200,384,260⟩⟩]⟩
theorem node1714 : UpperPrefix a [2,5,8,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,0,3] 30 cert1714 (by decide +kernel)

def cert1715 : Local := ⟨⟨360,0,98,0,334,270,0,110,106⟩,[(1,5),(3,6),(6,4)],[(7,4,3),(7,4,6),(0,5,1),(4,6,3)]⟩
theorem node1715 : UpperPrefix a [2,5,8,6,7,0,4] 30 :=
  local_sound a [2,5,8,6,7,0,4] 30 cert1715 (by decide +kernel)

theorem node1716 : UpperPrefix a [2,5,8,6,7,0] 30 :=
  branch_upper a [2,5,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,6,7,0,0] 30 (by decide +kernel))
  node1713
  (invalid_upper a [2,5,8,6,7,0,2] 30 (by decide +kernel))
  node1714
  node1715
  (invalid_upper a [2,5,8,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,0,8] 30 (by decide +kernel)))

def cert1717 : Leaf := ⟨⟨120,88,112,160,72,25,56,120,120⟩,[],[(7,4,3),(1,5,1),(0,6,5)],⟨7,35,268,88,176,98,193,408,284⟩,⟨7,35,268,88,176,98,193,384,260⟩,[⟨2,1210144479429980451800577,⟨251,123,440,122,184,122,251,384,400⟩⟩,⟨8,1184059125282448182533,⟨7,43,47,122,250,122,251,251,7⟩⟩]⟩
theorem node1717 : UpperPrefix a [2,5,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,1,0] 30 cert1717 (by decide +kernel)

def cert1718 : Leaf := ⟨⟨312,284,49,384,261,285,272,53,49⟩,[],[(7,4,3),(1,5,1)],⟨7,35,268,88,176,98,200,401,277⟩,⟨7,35,268,88,176,98,200,384,260⟩,[⟨6,1404267617112513445913641,⟨407,435,397,415,435,439,397,384,260⟩⟩,⟨3,1214857601885167284126721,⟨407,435,260,80,176,242,192,384,260⟩⟩,⟨0,1210107853514229985313792,⟨6,34,268,88,248,98,200,384,260⟩⟩,⟨2,1210107853514229984265217,⟨3,35,264,88,248,98,200,384,256⟩⟩,⟨5,1210107852388330078471169,⟨7,3,268,88,216,66,200,384,260⟩⟩]⟩
theorem node1718 : UpperPrefix a [2,5,8,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,1,3] 30 cert1718 (by decide +kernel)

def cert1719 : Local := ⟨⟨360,332,97,0,333,269,0,109,105⟩,[(3,6),(6,4)],[(7,4,3),(7,4,6),(1,5,1),(4,6,3)]⟩
theorem node1719 : UpperPrefix a [2,5,8,6,7,1,4] 30 :=
  local_sound a [2,5,8,6,7,1,4] 30 cert1719 (by decide +kernel)

theorem node1720 : UpperPrefix a [2,5,8,6,7,1] 30 :=
  branch_upper a [2,5,8,6,7,1] 30 (by decide) (fin9_cases _
  node1717
  (invalid_upper a [2,5,8,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,2] 30 (by decide +kernel))
  node1718
  node1719
  (invalid_upper a [2,5,8,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,8] 30 (by decide +kernel)))

def cert1721 : Leaf := ⟨⟨56,28,51,166,6,0,55,55,51⟩,[(5,3)],[(6,3,5),(7,4,3)],⟨7,35,268,88,176,104,211,403,279⟩,⟨7,35,268,88,176,104,192,384,260⟩,[⟨8,1184059125282448149765,⟨7,43,47,120,250,120,250,251,7⟩⟩,⟨3,1214857655926163789317121,⟨471,499,260,80,176,96,192,384,260⟩⟩,⟨0,1210107567821537407927296,⟨6,42,300,120,184,120,248,384,260⟩⟩]⟩
theorem node1721 : UpperPrefix a [2,5,8,6,7,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,3] 30 cert1721 (by decide +kernel)

def cert1722 : Leaf := ⟨⟨80,84,83,0,71,0,31,95,91⟩,[(3,5),(5,3)],[(7,4,3),(7,4,5)],⟨7,35,268,88,176,112,203,395,271⟩,⟨7,35,268,88,176,112,192,384,260⟩,[⟨5,1219570779896566093710339,⟨455,463,268,88,152,88,192,384,260⟩⟩,⟨8,1184059125282448149765,⟨7,43,47,120,250,120,250,251,7⟩⟩,⟨3,1210107567821523449285893,⟨7,35,295,112,176,112,240,385,263⟩⟩]⟩
theorem node1722 : UpperPrefix a [2,5,8,6,7,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,4] 30 cert1722 (by decide +kernel)

theorem node1723 : UpperPrefix a [2,5,8,6,7] 30 :=
  branch_upper a [2,5,8,6,7] 30 (by decide) (fin9_cases _
  node1716
  node1720
  (invalid_upper a [2,5,8,6,7,2] 30 (by decide +kernel))
  node1721
  node1722
  (invalid_upper a [2,5,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,8] 30 (by decide +kernel)))

theorem node1724 : UpperPrefix a [2,5,8,6] 30 :=
  branch_upper a [2,5,8,6] 30 (by decide) (fin9_cases _
  node1692
  node1700
  (invalid_upper a [2,5,8,6,2] 30 (by decide +kernel))
  node1712
  (invalid_upper a [2,5,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,6] 30 (by decide +kernel))
  node1723
  (invalid_upper a [2,5,8,6,8] 30 (by decide +kernel)))

def cert1725 : Leaf := ⟨⟨504,0,208,324,0,413,284,92,216⟩,[(1,4),(4,1)],[(1,5,1),(1,5,4)],⟨7,35,268,152,49,98,216,472,348⟩,⟨7,35,268,152,49,98,192,384,260⟩,[⟨0,1323666154147174067209216,⟨6,34,460,476,508,98,192,384,260⟩⟩,⟨5,1323666153021274160366593,⟨7,3,460,476,477,66,192,384,260⟩⟩]⟩
theorem node1725 : UpperPrefix a [2,5,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,1] 30 cert1725 (by decide +kernel)

def cert1726 : Leaf := ⟨⟨120,0,113,97,0,145,57,125,121⟩,[(1,4),(4,1)],[(7,3,5)],⟨7,35,268,152,49,104,194,464,340⟩,⟨7,35,268,152,49,104,194,384,260⟩,[⟨1,1512929318249813553184769,⟨21,53,268,152,53,492,508,384,260⟩⟩,⟨8,1184202831926792498949,⟨55,51,127,250,51,104,250,251,55⟩⟩,⟨2,1210107712073266788050433,⟨51,51,360,250,51,104,250,384,288⟩⟩]⟩
theorem node1726 : UpperPrefix a [2,5,8,7,0,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,3,1] 30 cert1726 (by decide +kernel)

def cert1727 : Local := ⟨⟨360,0,99,0,0,407,0,111,107⟩,[(1,4),(3,6),(4,1),(6,3)],[(7,3,5),(4,6,5)]⟩
theorem node1727 : UpperPrefix a [2,5,8,7,0,3,4] 30 :=
  local_sound a [2,5,8,7,0,3,4] 30 cert1727 (by decide +kernel)

#print axioms node1727
end Delivery.FiniteExclusion.Sharp2x7
