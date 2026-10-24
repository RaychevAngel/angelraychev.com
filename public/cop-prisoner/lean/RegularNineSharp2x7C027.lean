import RegularNineSharp2x7Base
import RegularNineSharp2x7C006
import RegularNineSharp2x7C016
import RegularNineSharp2x7C018
import RegularNineSharp2x7C019
import RegularNineSharp2x7C021
import RegularNineSharp2x7C023
import RegularNineSharp2x7C025
import RegularNineSharp2x7C026
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
theorem node1728 : UpperPrefix a [2,5,8,7,0,3] 30 :=
  branch_upper a [2,5,8,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,0,3,0] 30 (by decide +kernel))
  node1726
  (invalid_upper a [2,5,8,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,3] 30 (by decide +kernel))
  node1727
  (invalid_upper a [2,5,8,7,0,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,8] 30 (by decide +kernel)))

def cert1729 : Leaf := ⟨⟨472,0,208,324,0,396,284,92,216⟩,[(1,4),(4,1)],[],⟨7,35,268,152,49,112,194,456,332⟩,⟨7,35,268,152,49,112,194,384,260⟩,[⟨0,1446687112635328625116160,⟨454,494,268,444,508,508,454,384,260⟩⟩,⟨5,1446687110946478764852291,⟨455,463,268,412,477,477,455,384,260⟩⟩,⟨1,1664340193606828268453889,⟨29,445,268,156,445,508,508,384,260⟩⟩]⟩
theorem node1729 : UpperPrefix a [2,5,8,7,0,4,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,4,1] 30 cert1729 (by decide +kernel)

def cert1730 : Leaf := ⟨⟨360,0,99,359,0,271,0,111,107⟩,[(1,4),(4,1),(6,3)],[(7,3,6)],⟨7,35,268,152,49,112,200,450,326⟩,⟨7,35,268,152,49,112,200,384,260⟩,[⟨4,1404102965506700806743081,⟨455,419,461,463,419,487,461,384,324⟩⟩]⟩
theorem node1730 : UpperPrefix a [2,5,8,7,0,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,4,3] 30 cert1730 (by decide +kernel)

theorem node1731 : UpperPrefix a [2,5,8,7,0,4] 30 :=
  branch_upper a [2,5,8,7,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,0,4,0] 30 (by decide +kernel))
  node1729
  (invalid_upper a [2,5,8,7,0,4,2] 30 (by decide +kernel))
  node1730
  (invalid_upper a [2,5,8,7,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,8] 30 (by decide +kernel)))

theorem node1732 : UpperPrefix a [2,5,8,7,0] 30 :=
  branch_upper a [2,5,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,0,0] 30 (by decide +kernel))
  node1725
  (invalid_upper a [2,5,8,7,0,2] 30 (by decide +kernel))
  node1728
  node1731
  (invalid_upper a [2,5,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,8] 30 (by decide +kernel)))

def cert1733 : Leaf := ⟨⟨472,0,208,324,0,414,284,92,216⟩,[(1,5),(4,1)],[(5,1,4),(0,5,1),(0,5,4)],⟨7,35,268,152,50,97,216,472,348⟩,⟨7,35,268,152,50,97,192,384,260⟩,[⟨1,1323666154147174067208193,⟨5,33,460,476,508,97,192,384,260⟩⟩]⟩
theorem node1733 : UpperPrefix a [2,5,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,0] 30 cert1733 (by decide +kernel)

def cert1734 : Leaf := ⟨⟨72,72,83,67,0,131,14,95,91⟩,[(4,1)],[(5,1,4),(7,3,5)],⟨7,35,268,152,50,104,193,464,340⟩,⟨7,35,268,152,50,104,193,384,260⟩,[⟨8,1184058565487148240133,⟨23,51,63,250,50,122,251,251,23⟩⟩,⟨4,1210109871407236364897541,⟨7,35,303,232,34,104,193,449,263⟩⟩,⟨2,1210107567542394597442561,⟨19,51,264,152,50,122,251,384,256⟩⟩]⟩
theorem node1734 : UpperPrefix a [2,5,8,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,3,0] 30 cert1734 (by decide +kernel)

def cert1735 : Local := ⟨⟨328,332,67,0,0,407,0,79,75⟩,[(3,6),(4,1),(6,3)],[(5,1,4),(7,3,5),(4,6,5)]⟩
theorem node1735 : UpperPrefix a [2,5,8,7,1,3,4] 30 :=
  local_sound a [2,5,8,7,1,3,4] 30 cert1735 (by decide +kernel)

theorem node1736 : UpperPrefix a [2,5,8,7,1,3] 30 :=
  branch_upper a [2,5,8,7,1,3] 30 (by decide) (fin9_cases _
  node1734
  (invalid_upper a [2,5,8,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,3] 30 (by decide +kernel))
  node1735
  (invalid_upper a [2,5,8,7,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,8] 30 (by decide +kernel)))

def cert1737 : Leaf := ⟨⟨216,220,208,68,0,141,28,92,216⟩,[(4,1)],[(5,1,4)],⟨7,35,268,152,50,112,193,456,332⟩,⟨7,35,268,152,50,112,193,384,260⟩,[⟨1,1446687112635328625115137,⟨453,493,268,444,508,508,193,384,260⟩⟩,⟨8,1184058565487148240133,⟨23,51,63,250,50,122,251,251,23⟩⟩,⟨0,1361518440641003848729600,⟨30,446,268,156,446,508,192,384,260⟩⟩]⟩
theorem node1737 : UpperPrefix a [2,5,8,7,1,4,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,4,0] 30 cert1737 (by decide +kernel)

def cert1738 : Leaf := ⟨⟨328,332,67,327,0,271,0,79,75⟩,[(4,1),(6,3)],[(5,1,4),(7,3,6)],⟨7,35,268,152,50,112,200,449,325⟩,⟨7,35,268,152,50,112,200,384,260⟩,[⟨4,1725851075640342806029353,⟨455,419,461,463,419,487,461,384,452⟩⟩]⟩
theorem node1738 : UpperPrefix a [2,5,8,7,1,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,4,3] 30 cert1738 (by decide +kernel)

theorem node1739 : UpperPrefix a [2,5,8,7,1,4] 30 :=
  branch_upper a [2,5,8,7,1,4] 30 (by decide) (fin9_cases _
  node1737
  (invalid_upper a [2,5,8,7,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,2] 30 (by decide +kernel))
  node1738
  (invalid_upper a [2,5,8,7,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,8] 30 (by decide +kernel)))

theorem node1740 : UpperPrefix a [2,5,8,7,1] 30 :=
  branch_upper a [2,5,8,7,1] 30 (by decide) (fin9_cases _
  node1733
  (invalid_upper a [2,5,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,2] 30 (by decide +kernel))
  node1736
  node1739
  (invalid_upper a [2,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,8] 30 (by decide +kernel)))

def cert1741 : Leaf := ⟨⟨224,0,240,100,196,134,36,124,248⟩,[(1,5)],[(0,5,1),(1,6,5)],⟨7,35,268,152,56,97,194,464,340⟩,⟨7,35,268,152,56,97,194,384,260⟩,[⟨8,1184200288000483217157,⟨55,51,127,250,122,123,250,251,55⟩⟩,⟨3,1210110019886385017868037,⟨39,35,359,242,114,99,226,483,295⟩⟩,⟨4,1210110019885286579982085,⟨39,35,367,234,106,99,226,483,295⟩⟩]⟩
theorem node1741 : UpperPrefix a [2,5,8,7,3,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,0,1] 30 cert1741 (by decide +kernel)

def cert1742 : Leaf := ⟨⟨496,0,242,0,454,406,0,118,242⟩,[(1,5),(3,6),(6,3)],[(0,5,1)],⟨7,35,268,152,56,97,208,450,326⟩,⟨7,35,268,152,56,97,208,384,260⟩,[⟨3,1229034068959402176696069,⟨423,35,487,208,114,99,208,387,423⟩⟩]⟩
theorem node1742 : UpperPrefix a [2,5,8,7,3,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,0,4] 30 cert1742 (by decide +kernel)

theorem node1743 : UpperPrefix a [2,5,8,7,3,0] 30 :=
  branch_upper a [2,5,8,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,3,0,0] 30 (by decide +kernel))
  node1741
  (invalid_upper a [2,5,8,7,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,0,3] 30 (by decide +kernel))
  node1742
  (invalid_upper a [2,5,8,7,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,0,8] 30 (by decide +kernel)))

def cert1744 : Leaf := ⟨⟨224,192,240,96,192,129,36,124,248⟩,[],[(1,5,1),(0,6,5)],⟨7,35,268,152,56,98,193,464,340⟩,⟨7,35,268,152,56,98,193,384,260⟩,[⟨8,1184058565349709286661,⟨23,51,63,250,56,122,251,251,23⟩⟩,⟨2,1210107567542257158489089,⟨3,51,264,152,56,122,251,384,256⟩⟩,⟨3,1210109878163734243937541,⟨7,35,295,242,48,98,227,483,263⟩⟩,⟨4,1210109878162635806051589,⟨7,35,303,234,40,98,227,483,263⟩⟩]⟩
theorem node1744 : UpperPrefix a [2,5,8,7,3,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,1,0] 30 cert1744 (by decide +kernel)

def cert1745 : Leaf := ⟨⟨208,212,209,0,197,149,0,85,209⟩,[(3,6),(6,3)],[(1,5,1)],⟨7,35,268,152,56,98,208,449,325⟩,⟨7,35,268,152,56,98,208,384,260⟩,[⟨3,1229034068959402176679685,⟨423,35,487,208,112,98,208,387,423⟩⟩,⟨5,1437224309539038775215139,⟨7,391,332,476,477,463,476,384,260⟩⟩,⟨8,1184202821275273596677,⟨55,51,127,250,120,122,250,251,55⟩⟩]⟩
theorem node1745 : UpperPrefix a [2,5,8,7,3,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,1,4] 30 cert1745 (by decide +kernel)

theorem node1746 : UpperPrefix a [2,5,8,7,3,1] 30 :=
  branch_upper a [2,5,8,7,3,1] 30 (by decide) (fin9_cases _
  node1744
  (invalid_upper a [2,5,8,7,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,1,3] 30 (by decide +kernel))
  node1745
  (invalid_upper a [2,5,8,7,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,1,8] 30 (by decide +kernel)))

def cert1747 : Leaf := ⟨⟨104,76,99,96,192,136,39,103,99⟩,[],[(4,5,4)],⟨7,35,268,152,56,112,195,451,327⟩,⟨7,35,268,152,56,112,192,384,260⟩,[⟨8,1184058565349709253893,⟨23,51,63,250,56,120,250,251,23⟩⟩,⟨7,1360042701114962925872185,⟨7,291,269,31,319,375,64,256,260⟩⟩,⟨0,1210107567542257159504896,⟨6,50,268,152,56,120,248,384,260⟩⟩,⟨1,1210107567542257159503873,⟨5,49,268,152,56,120,248,384,260⟩⟩,⟨2,1210107567542257158456321,⟨3,51,264,152,56,120,248,384,256⟩⟩,⟨3,1214857655926026350363649,⟨455,483,260,144,48,112,192,384,260⟩⟩]⟩
theorem node1747 : UpperPrefix a [2,5,8,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,4] 30 cert1747 (by decide +kernel)

theorem node1748 : UpperPrefix a [2,5,8,7,3] 30 :=
  branch_upper a [2,5,8,7,3] 30 (by decide) (fin9_cases _
  node1743
  node1746
  (invalid_upper a [2,5,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,3] 30 (by decide +kernel))
  node1747
  (invalid_upper a [2,5,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,8] 30 (by decide +kernel)))

def cert1749 : Local := ⟨⟨440,0,176,292,0,414,316,60,184⟩,[(1,5),(4,5)],[(6,4,4),(0,5,1),(1,6,5)]⟩
theorem node1749 : UpperPrefix a [2,5,8,7,6,0,1] 30 :=
  local_sound a [2,5,8,7,6,0,1] 30 cert1749 (by decide +kernel)

def cert1750 : Local := ⟨⟨312,0,50,294,0,286,0,62,58⟩,[(1,5),(4,5),(6,3)],[(7,3,6),(6,4,4),(0,5,1)]⟩
theorem node1750 : UpperPrefix a [2,5,8,7,6,0,3] 30 :=
  local_sound a [2,5,8,7,6,0,3] 30 cert1750 (by decide +kernel)

def cert1751 : Local := ⟨⟨440,0,178,0,0,414,0,62,186⟩,[(1,5),(3,6),(4,5),(6,3)],[(6,4,4),(0,5,1)]⟩
theorem node1751 : UpperPrefix a [2,5,8,7,6,0,4] 30 :=
  local_sound a [2,5,8,7,6,0,4] 30 cert1751 (by decide +kernel)

theorem node1752 : UpperPrefix a [2,5,8,7,6,0] 30 :=
  branch_upper a [2,5,8,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,6,0,0] 30 (by decide +kernel))
  node1749
  (invalid_upper a [2,5,8,7,6,0,2] 30 (by decide +kernel))
  node1750
  node1751
  (invalid_upper a [2,5,8,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,0,8] 30 (by decide +kernel)))

def cert1753 : Leaf := ⟨⟨312,284,48,292,0,285,316,60,56⟩,[(4,5)],[(6,4,4),(1,5,1),(0,6,5)],⟨7,35,268,152,112,98,193,408,284⟩,⟨7,35,268,152,112,98,193,384,260⟩,[⟨7,1246705908347438275531789,⟨7,51,271,319,114,114,115,256,261⟩⟩]⟩
theorem node1753 : UpperPrefix a [2,5,8,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,1,0] 30 cert1753 (by decide +kernel)

def cert1754 : Local := ⟨⟨312,284,49,293,0,285,0,61,57⟩,[(4,5),(6,3)],[(7,3,6),(6,4,4),(1,5,1)]⟩
theorem node1754 : UpperPrefix a [2,5,8,7,6,1,3] 30 :=
  local_sound a [2,5,8,7,6,1,3] 30 cert1754 (by decide +kernel)

def cert1755 : Local := ⟨⟨440,412,177,0,0,413,0,61,185⟩,[(3,6),(4,5),(6,3)],[(6,4,4),(1,5,1)]⟩
theorem node1755 : UpperPrefix a [2,5,8,7,6,1,4] 30 :=
  local_sound a [2,5,8,7,6,1,4] 30 cert1755 (by decide +kernel)

theorem node1756 : UpperPrefix a [2,5,8,7,6,1] 30 :=
  branch_upper a [2,5,8,7,6,1] 30 (by decide) (fin9_cases _
  node1753
  (invalid_upper a [2,5,8,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,2] 30 (by decide +kernel))
  node1754
  node1755
  (invalid_upper a [2,5,8,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,8] 30 (by decide +kernel)))

def cert1757 : Leaf := ⟨⟨56,28,51,36,0,148,55,55,51⟩,[(4,5)],[(7,3,5),(6,4,4)],⟨7,35,268,152,112,104,211,403,279⟩,⟨7,35,268,152,112,104,192,384,260⟩,[⟨8,1184059128024784768261,⟨7,51,63,250,120,120,250,251,7⟩⟩,⟨3,1214857655928362812572673,⟨471,499,260,144,112,112,192,384,260⟩⟩,⟨0,1210107568105207112926208,⟨6,50,268,184,120,120,248,384,260⟩⟩,⟨1,1210107568105207112925185,⟨5,49,268,184,120,120,248,384,260⟩⟩]⟩
theorem node1757 : UpperPrefix a [2,5,8,7,6,3] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,3] 30 cert1757 (by decide +kernel)

def cert1758 : Leaf := ⟨⟨56,28,51,38,0,0,63,63,59⟩,[(4,5),(5,4)],[(6,4,4),(6,4,5)],⟨7,35,268,152,112,112,203,395,271⟩,⟨7,35,268,152,112,112,192,384,260⟩,[⟨7,1265595374278916856353805,⟨263,51,271,319,112,112,112,256,261⟩⟩,⟨8,1184059128024784768261,⟨7,51,63,250,120,120,250,251,7⟩⟩,⟨0,1210107568105207112926208,⟨6,50,268,184,120,120,248,384,260⟩⟩]⟩
theorem node1758 : UpperPrefix a [2,5,8,7,6,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,4] 30 cert1758 (by decide +kernel)

theorem node1759 : UpperPrefix a [2,5,8,7,6] 30 :=
  branch_upper a [2,5,8,7,6] 30 (by decide) (fin9_cases _
  node1752
  node1756
  (invalid_upper a [2,5,8,7,6,2] 30 (by decide +kernel))
  node1757
  node1758
  (invalid_upper a [2,5,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,8] 30 (by decide +kernel)))

theorem node1760 : UpperPrefix a [2,5,8,7] 30 :=
  branch_upper a [2,5,8,7] 30 (by decide) (fin9_cases _
  node1732
  node1740
  (invalid_upper a [2,5,8,7,2] 30 (by decide +kernel))
  node1748
  (invalid_upper a [2,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,5] 30 (by decide +kernel))
  node1759
  (invalid_upper a [2,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,8] 30 (by decide +kernel)))

theorem node1761 : UpperPrefix a [2,5,8] 30 :=
  branch_upper a [2,5,8] 30 (by decide) (fin9_cases _
  node1663
  node1684
  (invalid_upper a [2,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,5] 30 (by decide +kernel))
  node1724
  node1760
  (invalid_upper a [2,5,8,8] 30 (by decide +kernel)))

theorem node1762 : UpperPrefix a [2,5] 30 :=
  branch_upper a [2,5] 30 (by decide) (fin9_cases _
  node1164
  node1237
  (invalid_upper a [2,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,3] 30 (by decide +kernel))
  node1351
  (invalid_upper a [2,5,5] 30 (by decide +kernel))
  node1483
  node1644
  node1761)

theorem node1763 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0] 30 (by decide +kernel))
  (invalid_upper a [2,1] 30 (by decide +kernel))
  (invalid_upper a [2,2] 30 (by decide +kernel))
  node392
  node1082
  node1762
  (PrefixConjugacy.upper aut10 [2,6] [2,5] 30 (by decide +kernel) node1762)
  (PrefixConjugacy.upper aut9 [2,7] [2,4] 30 (by decide +kernel) node1082)
  (PrefixConjugacy.upper aut8 [2,8] [2,3] 30 (by decide +kernel) node392))

theorem node1764 : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
  (invalid_upper a [0] 30 (by decide +kernel))
  (invalid_upper a [1] 30 (by decide +kernel))
  node1763
  (PrefixConjugacy.upper aut6 [3] [2] 30 (by decide +kernel) node1763)
  (PrefixConjugacy.upper aut5 [4] [2] 30 (by decide +kernel) node1763)
  (PrefixConjugacy.upper aut4 [5] [2] 30 (by decide +kernel) node1763)
  (PrefixConjugacy.upper aut3 [6] [2] 30 (by decide +kernel) node1763)
  (PrefixConjugacy.upper aut2 [7] [2] 30 (by decide +kernel) node1763)
  (PrefixConjugacy.upper aut1 [8] [2] 30 (by decide +kernel) node1763))

#print axioms node1764
end Delivery.FiniteExclusion.Sharp2x7
