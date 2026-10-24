import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C001
import RegularNineSharp2x3x4C002
import RegularNineSharp2x3x4C003
import RegularNineSharp2x3x4C005
import RegularNineSharp2x3x4C006
import RegularNineSharp2x3x4C009
import RegularNineSharp2x3x4C010
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert704 : Local := ⟨⟨0,332,99,0,0,407,0,111,79⟩,[(0,4),(3,6),(4,0),(6,3)],[(7,3,5),(4,6,5)]⟩
theorem node704 : UpperPrefix a [2,5,8,7,1,3,4] 30 :=
  local_sound a [2,5,8,7,1,3,4] 30 cert704 (by decide +kernel)

theorem node705 : UpperPrefix a [2,5,8,7,1,3] 30 :=
  branch_upper a [2,5,8,7,1,3] 30 (by decide) (fin9_cases _
  node703
  (invalid_upper a [2,5,8,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,3] 30 (by decide +kernel))
  node704
  (invalid_upper a [2,5,8,7,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,3,8] 30 (by decide +kernel)))

def cert706 : Leaf := ⟨⟨0,476,240,352,0,392,312,120,216⟩,[(0,4),(4,0)],[],⟨7,35,268,152,22,112,193,456,360⟩,⟨7,35,268,152,22,112,193,384,288⟩,[⟨1,1446687112635328692224001,⟨453,493,268,444,508,508,193,388,428⟩⟩,⟨0,1664340193606894903362560,⟨30,446,268,152,30,508,508,388,428⟩⟩,⟨2,1446687112635328608863233,⟨451,491,264,440,506,504,193,384,424⟩⟩]⟩
theorem node706 : UpperPrefix a [2,5,8,7,1,4,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,4,0] 30 cert706 (by decide +kernel)

def cert707 : Leaf := ⟨⟨0,324,115,359,0,271,0,103,71⟩,[(0,4),(4,0),(6,3)],[(7,3,6)],⟨7,35,268,152,22,112,200,449,353⟩,⟨7,35,268,152,22,112,200,384,288⟩,[⟨3,1361518440640927331533841,⟨23,435,260,145,23,499,192,384,418⟩⟩,⟨4,1361518584754948250027025,⟨7,419,332,201,7,483,200,384,418⟩⟩]⟩
theorem node707 : UpperPrefix a [2,5,8,7,1,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,4,3] 30 cert707 (by decide +kernel)

theorem node708 : UpperPrefix a [2,5,8,7,1,4] 30 :=
  branch_upper a [2,5,8,7,1,4] 30 (by decide) (fin9_cases _
  node706
  (invalid_upper a [2,5,8,7,1,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,2] 30 (by decide +kernel))
  node707
  (invalid_upper a [2,5,8,7,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,4,8] 30 (by decide +kernel)))

theorem node709 : UpperPrefix a [2,5,8,7,1] 30 :=
  branch_upper a [2,5,8,7,1] 30 (by decide) (fin9_cases _
  node702
  (invalid_upper a [2,5,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,2] 30 (by decide +kernel))
  node705
  node708
  (invalid_upper a [2,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,1,8] 30 (by decide +kernel)))

def cert710 : Leaf := ⟨⟨240,0,240,356,0,150,54,118,214⟩,[(1,5),(4,2)],[(3,4,4),(0,5,1)],⟨7,35,268,152,28,97,210,466,370⟩,⟨7,35,268,152,28,97,192,384,288⟩,[⟨8,1181890769847883693589,⟨55,35,127,251,127,99,192,128,34⟩⟩,⟨1,1210107565297896262729729,⟨21,33,284,156,28,121,220,412,288⟩⟩]⟩
theorem node710 : UpperPrefix a [2,5,8,7,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,0] 30 cert710 (by decide +kernel)

def cert711 : Leaf := ⟨⟨240,212,144,260,0,149,53,117,213⟩,[(4,2)],[(3,4,4),(1,5,1)],⟨7,35,268,152,28,98,209,465,369⟩,⟨7,35,268,152,28,98,192,384,288⟩,[⟨8,1181890769847883677205,⟨55,35,127,251,127,98,192,128,32⟩⟩,⟨0,1210107565297896262730752,⟨22,34,284,156,28,122,220,412,288⟩⟩,⟨5,1210107564171996355888129,⟨23,3,284,156,28,90,220,412,256⟩⟩,⟨6,1210106412376391655883777,⟨23,35,284,156,28,58,156,412,288⟩⟩]⟩
theorem node711 : UpperPrefix a [2,5,8,7,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,1] 30 cert711 (by decide +kernel)

def cert712 : Leaf := ⟨⟨240,212,240,356,0,132,35,99,195⟩,[(4,2)],[(3,4,4)],⟨7,35,268,152,28,112,195,451,355⟩,⟨7,35,268,152,28,112,192,384,288⟩,[⟨8,1181890769847883693589,⟨55,35,127,251,127,115,192,128,34⟩⟩,⟨0,1210107567549696076416000,⟨22,34,284,156,28,120,252,412,288⟩⟩,⟨1,1210107567549696076414977,⟨21,33,284,156,28,120,252,412,288⟩⟩,⟨2,1219580022408897068270593,⟨451,483,264,152,24,112,192,384,288⟩⟩,⟨4,1219580022407797557691393,⟨455,483,268,136,12,96,192,384,288⟩⟩]⟩
theorem node712 : UpperPrefix a [2,5,8,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,3,4] 30 cert712 (by decide +kernel)

theorem node713 : UpperPrefix a [2,5,8,7,3] 30 :=
  branch_upper a [2,5,8,7,3] 30 (by decide) (fin9_cases _
  node710
  node711
  (invalid_upper a [2,5,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,3] 30 (by decide +kernel))
  node712
  (invalid_upper a [2,5,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,3,8] 30 (by decide +kernel)))

def cert714 : Leaf := ⟨⟨112,0,112,356,160,22,52,124,92⟩,[(1,5)],[(0,5,1),(1,6,5)],⟨7,35,268,152,84,97,194,408,312⟩,⟨7,35,268,152,84,97,194,384,288⟩,[⟨3,1210107710384475984657941,⟨55,35,375,243,119,99,194,384,290⟩⟩,⟨7,1246705906089041392071709,⟨7,35,271,319,119,99,66,256,290⟩⟩,⟨8,1181890769847883693589,⟨55,35,127,251,119,99,194,128,34⟩⟩]⟩
theorem node714 : UpperPrefix a [2,5,8,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,0,1] 30 cert714 (by decide +kernel)

def cert715 : Local := ⟨⟨368,0,114,358,298,278,0,118,86⟩,[(1,5),(6,3)],[(7,3,6),(0,5,1),(3,6,4)]⟩
theorem node715 : UpperPrefix a [2,5,8,7,6,0,3] 30 :=
  local_sound a [2,5,8,7,6,0,3] 30 cert715 (by decide +kernel)

def cert716 : Leaf := ⟨⟨488,0,226,0,426,398,0,110,206⟩,[(1,5),(3,6),(6,3)],[(0,5,1)],⟨7,35,268,152,84,97,208,394,298⟩,⟨7,35,268,152,84,97,208,384,288⟩,[⟨4,1247997180424901362775069,⟨135,35,399,431,231,99,227,384,290⟩⟩]⟩
theorem node716 : UpperPrefix a [2,5,8,7,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,0,4] 30 cert716 (by decide +kernel)

theorem node717 : UpperPrefix a [2,5,8,7,6,0] 30 :=
  branch_upper a [2,5,8,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,6,0,0] 30 (by decide +kernel))
  node714
  (invalid_upper a [2,5,8,7,6,0,2] 30 (by decide +kernel))
  node715
  node716
  (invalid_upper a [2,5,8,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,0,8] 30 (by decide +kernel)))

def cert718 : Leaf := ⟨⟨368,336,112,352,416,273,308,120,88⟩,[],[(1,5,1),(0,6,5)],⟨7,35,268,152,84,98,193,408,312⟩,⟨7,35,268,152,84,98,193,384,288⟩,[⟨2,1323665724616359599440897,⟨3,35,392,440,506,98,227,384,288⟩⟩,⟨3,1210107712636275798359573,⟨55,35,375,243,119,98,227,384,288⟩⟩,⟨7,1246705908340841205773341,⟨7,35,271,319,119,98,99,256,288⟩⟩]⟩
theorem node718 : UpperPrefix a [2,5,8,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,1,0] 30 cert718 (by decide +kernel)

def cert719 : Leaf := ⟨⟨112,84,113,357,41,21,0,117,85⟩,[(6,3)],[(7,3,6),(1,5,1),(3,6,4)],⟨7,35,268,152,84,98,200,401,305⟩,⟨7,35,268,152,84,98,200,384,288⟩,[⟨8,1181893021647697362453,⟨55,35,127,251,119,98,234,128,32⟩⟩]⟩
theorem node719 : UpperPrefix a [2,5,8,7,6,1,3] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,1,3] 30 cert719 (by decide +kernel)

def cert720 : Leaf := ⟨⟨424,396,161,0,425,397,0,45,141⟩,[(3,6),(6,3)],[(1,5,1)],⟨7,35,268,152,84,98,208,393,297⟩,⟨7,35,268,152,84,98,208,384,288⟩,[⟨4,1247997180424901362758685,⟨135,35,399,431,231,98,227,384,288⟩⟩,⟨6,1361554181207513243993383,⟨135,423,399,152,157,431,152,387,423⟩⟩]⟩
theorem node720 : UpperPrefix a [2,5,8,7,6,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,1,4] 30 cert720 (by decide +kernel)

theorem node721 : UpperPrefix a [2,5,8,7,6,1] 30 :=
  branch_upper a [2,5,8,7,6,1] 30 (by decide) (fin9_cases _
  node718
  (invalid_upper a [2,5,8,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,2] 30 (by decide +kernel))
  node719
  node720
  (invalid_upper a [2,5,8,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,1,8] 30 (by decide +kernel)))

def cert722 : Leaf := ⟨⟨328,332,80,324,264,388,270,108,92⟩,[],[(5,1,7),(7,3,5),(1,7,6)],⟨7,35,268,152,84,104,193,386,304⟩,⟨7,35,268,152,84,104,193,386,288⟩,[⟨0,1786263949131414727558144,⟨398,446,268,444,380,380,508,398,308⟩⟩,⟨4,1210144981610668833652245,⟨231,99,495,235,231,106,195,386,288⟩⟩]⟩
theorem node722 : UpperPrefix a [2,5,8,7,6,3,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,3,0,1] 30 cert722 (by decide +kernel)

def cert723 : Leaf := ⟨⟨104,76,98,0,42,134,46,111,78⟩,[(3,7)],[(7,3,5),(4,7,3)],⟨7,35,268,152,84,104,193,400,290⟩,⟨7,35,268,152,84,104,193,400,288⟩,[⟨8,1184202805323764973077,⟨55,35,127,251,119,106,235,251,32⟩⟩,⟨0,1219552301068764593521664,⟨262,290,268,188,124,120,252,444,288⟩⟩]⟩
theorem node723 : UpperPrefix a [2,5,8,7,6,3,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,3,0,4] 30 cert723 (by decide +kernel)

theorem node724 : UpperPrefix a [2,5,8,7,6,3,0] 30 :=
  branch_upper a [2,5,8,7,6,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,6,3,0,0] 30 (by decide +kernel))
  node722
  (invalid_upper a [2,5,8,7,6,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,0,3] 30 (by decide +kernel))
  node723
  (invalid_upper a [2,5,8,7,6,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,0,8] 30 (by decide +kernel)))

def cert725 : Leaf := ⟨⟨104,76,112,356,40,132,45,108,92⟩,[],[(7,3,5),(0,7,6)],⟨7,35,268,152,84,104,194,385,304⟩,⟨7,35,268,152,84,104,194,385,288⟩,[⟨1,1786263949131414694002689,⟨397,445,268,444,380,380,508,389,308⟩⟩,⟨4,1210147287453678047346197,⟨231,99,495,235,231,106,194,451,288⟩⟩,⟨8,1184196049907143949845,⟨55,35,127,251,119,106,194,195,32⟩⟩]⟩
theorem node725 : UpperPrefix a [2,5,8,7,6,3,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,3,1,0] 30 cert725 (by decide +kernel)

def cert726 : Leaf := ⟨⟨104,76,97,0,41,133,45,109,77⟩,[(3,7)],[(7,3,5),(4,7,3)],⟨7,35,268,152,84,104,194,400,289⟩,⟨7,35,268,152,84,104,194,400,288⟩,[⟨1,1222522226866872009883649,⟨397,445,396,188,252,252,508,444,444⟩⟩,⟨8,1184202805323764940309,⟨55,35,127,251,119,106,234,251,32⟩⟩]⟩
theorem node726 : UpperPrefix a [2,5,8,7,6,3,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,3,1,4] 30 cert726 (by decide +kernel)

theorem node727 : UpperPrefix a [2,5,8,7,6,3,1] 30 :=
  branch_upper a [2,5,8,7,6,3,1] 30 (by decide) (fin9_cases _
  node725
  (invalid_upper a [2,5,8,7,6,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,1,3] 30 (by decide +kernel))
  node726
  (invalid_upper a [2,5,8,7,6,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,1,8] 30 (by decide +kernel)))

def cert728 : Leaf := ⟨⟨296,268,35,0,299,407,0,47,15⟩,[(3,6),(6,3)],[(7,3,5),(4,6,5)],⟨7,35,268,152,84,104,208,387,291⟩,⟨7,35,268,152,84,104,208,384,288⟩,[⟨6,1373387767530797921355047,⟨391,423,399,152,157,431,152,387,423⟩⟩]⟩
theorem node728 : UpperPrefix a [2,5,8,7,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,3,4] 30 cert728 (by decide +kernel)

theorem node729 : UpperPrefix a [2,5,8,7,6,3] 30 :=
  branch_upper a [2,5,8,7,6,3] 30 (by decide) (fin9_cases _
  node724
  node727
  (invalid_upper a [2,5,8,7,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,3] 30 (by decide +kernel))
  node728
  (invalid_upper a [2,5,8,7,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,3,8] 30 (by decide +kernel)))

def cert730 : Leaf := ⟨⟨408,412,144,260,392,0,286,60,156⟩,[(5,4)],[(5,1,7),(6,4,5),(1,7,6)],⟨7,35,268,152,84,112,193,386,296⟩,⟨7,35,268,152,84,112,193,386,288⟩,[⟨0,1786263949131414727558144,⟨398,446,268,444,380,380,508,398,308⟩⟩]⟩
theorem node730 : UpperPrefix a [2,5,8,7,6,4,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,4,0,1] 30 cert730 (by decide +kernel)

def cert731 : Leaf := ⟨⟨432,404,0,295,419,0,310,0,151⟩,[(2,7),(5,4),(7,2)],[(6,4,5)],⟨7,35,268,152,84,112,193,392,290⟩,⟨7,35,268,152,84,112,193,392,288⟩,[⟨3,2112079708612578220473877,⟨311,291,375,499,375,371,451,482,290⟩⟩]⟩
theorem node731 : UpperPrefix a [2,5,8,7,6,4,0,3] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,4,0,3] 30 cert731 (by decide +kernel)

theorem node732 : UpperPrefix a [2,5,8,7,6,4,0] 30 :=
  branch_upper a [2,5,8,7,6,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,6,4,0,0] 30 (by decide +kernel))
  node730
  (invalid_upper a [2,5,8,7,6,4,0,2] 30 (by decide +kernel))
  node731
  (invalid_upper a [2,5,8,7,6,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,0,8] 30 (by decide +kernel)))

def cert733 : Leaf := ⟨⟨48,20,49,293,161,0,53,61,29⟩,[(5,4)],[(6,4,5)],⟨7,35,268,152,84,112,194,393,297⟩,⟨7,35,268,152,84,112,194,384,288⟩,[⟨1,1219579971187057253679105,⟨397,445,268,184,124,124,508,384,304⟩⟩,⟨3,1210107710384475984657941,⟨55,35,375,243,119,115,194,384,290⟩⟩,⟨7,1246705906089041392071709,⟨7,35,271,319,119,115,66,256,290⟩⟩,⟨8,1181890769847883693589,⟨55,35,127,251,119,115,194,128,34⟩⟩]⟩
theorem node733 : UpperPrefix a [2,5,8,7,6,4,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,6,4,1] 30 cert733 (by decide +kernel)

def cert734 : Local := ⟨⟨304,276,51,295,299,0,0,55,23⟩,[(5,4),(6,3)],[(7,3,6),(6,4,5),(3,6,4)]⟩
theorem node734 : UpperPrefix a [2,5,8,7,6,4,3] 30 :=
  local_sound a [2,5,8,7,6,4,3] 30 cert734 (by decide +kernel)

theorem node735 : UpperPrefix a [2,5,8,7,6,4] 30 :=
  branch_upper a [2,5,8,7,6,4] 30 (by decide) (fin9_cases _
  node732
  node733
  (invalid_upper a [2,5,8,7,6,4,2] 30 (by decide +kernel))
  node734
  (invalid_upper a [2,5,8,7,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,4,8] 30 (by decide +kernel)))

theorem node736 : UpperPrefix a [2,5,8,7,6] 30 :=
  branch_upper a [2,5,8,7,6] 30 (by decide) (fin9_cases _
  node717
  node721
  (invalid_upper a [2,5,8,7,6,2] 30 (by decide +kernel))
  node729
  node735
  (invalid_upper a [2,5,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,6,8] 30 (by decide +kernel)))

theorem node737 : UpperPrefix a [2,5,8,7] 30 :=
  branch_upper a [2,5,8,7] 30 (by decide) (fin9_cases _
  node701
  node709
  (invalid_upper a [2,5,8,7,2] 30 (by decide +kernel))
  node713
  (invalid_upper a [2,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,5] 30 (by decide +kernel))
  node736
  (invalid_upper a [2,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,8] 30 (by decide +kernel)))

theorem node738 : UpperPrefix a [2,5,8] 30 :=
  branch_upper a [2,5,8] 30 (by decide) (fin9_cases _
  node611
  node650
  (invalid_upper a [2,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,5] 30 (by decide +kernel))
  node691
  node737
  (invalid_upper a [2,5,8,8] 30 (by decide +kernel)))

theorem node739 : UpperPrefix a [2,5] 30 :=
  branch_upper a [2,5] 30 (by decide) (fin9_cases _
  node173
  node228
  (invalid_upper a [2,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,3] 30 (by decide +kernel))
  node321
  (invalid_upper a [2,5,5] 30 (by decide +kernel))
  node438
  node582
  node738)

theorem node740 : UpperPrefix a [2] 30 :=
  branch_upper a [2] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0] 30 (by decide +kernel))
  (invalid_upper a [2,1] 30 (by decide +kernel))
  (invalid_upper a [2,2] 30 (by decide +kernel))
  node108
  (PrefixConjugacy.upper aut16 [2,4] [2,3] 30 (by decide +kernel) node108)
  node739
  (PrefixConjugacy.upper aut3 [2,6] [2,5] 30 (by decide +kernel) node739)
  (PrefixConjugacy.upper aut2 [2,7] [2,5] 30 (by decide +kernel) node739)
  (PrefixConjugacy.upper aut1 [2,8] [2,5] 30 (by decide +kernel) node739))

def cert741 : Leaf := ⟨⟨340,308,306,293,0,404,308,52,148⟩,[(4,2)],[(6,1,0),(1,3,2),(3,4,4)],⟨35,67,13,26,28,500,468,404,436⟩,⟨35,67,13,26,28,96,192,384,288⟩,[⟨0,1304739723373914195231744,⟨34,66,508,506,508,96,192,384,288⟩⟩,⟨7,1208926973692791536502049,⟨63,95,29,30,28,127,84,285,319⟩⟩]⟩
theorem node741 : UpperPrefix a [5,6,0,1,3] 30 :=
  Boolean.leaf_sound a [5,6,0,1,3] 30 cert741 (by decide +kernel)

def cert742 : Leaf := ⟨⟨192,160,178,164,40,152,316,60,156⟩,[],[(6,1,0),(1,3,2)],⟨35,67,13,26,148,100,472,408,312⟩,⟨35,67,13,26,148,100,192,384,288⟩,[⟨0,1271618468290978286404608,⟨506,458,508,506,500,500,192,384,304⟩⟩,⟨8,1181748004598457353579,⟨47,127,13,63,148,127,255,149,47⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,26,144,99,192,385,291⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,18,148,103,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,10,132,103,192,385,291⟩⟩]⟩
theorem node742 : UpperPrefix a [5,6,0,1,7,2] 30 :=
  Boolean.leaf_sound a [5,6,0,1,7,2] 30 cert742 (by decide +kernel)

def cert743 : Leaf := ⟨⟨76,44,34,165,40,148,316,60,156⟩,[],[(6,1,0),(1,3,2)],⟨35,67,13,26,148,104,468,404,308⟩,⟨35,67,13,26,148,104,192,384,288⟩,[⟨8,1181748004598457353579,⟨47,127,13,63,148,127,255,149,47⟩⟩,⟨0,1304739723092439218521088,⟨34,66,508,506,500,104,192,384,288⟩⟩,⟨4,1210107565282752182895905,⟨39,67,13,10,132,111,192,385,295⟩⟩,⟨7,1208926973663134283220257,⟨39,67,13,26,20,111,64,257,295⟩⟩]⟩
theorem node743 : UpperPrefix a [5,6,0,1,7,3] 30 :=
  Boolean.leaf_sound a [5,6,0,1,7,3] 30 cert743 (by decide +kernel)

def cert744 : Leaf := ⟨⟨88,56,50,33,40,140,316,60,28⟩,[],[(6,1,0),(1,3,2),(7,4,5)],⟨35,67,13,26,148,112,460,396,300⟩,⟨35,67,13,26,148,112,192,384,288⟩,[⟨8,1181748004598457353579,⟨47,127,13,63,148,127,255,149,47⟩⟩,⟨0,1229033997465034043687936,⟨34,66,508,58,500,112,192,384,288⟩⟩,⟨2,1210107565283855980053793,⟨43,67,9,26,144,123,192,385,299⟩⟩]⟩
theorem node744 : UpperPrefix a [5,6,0,1,7,4] 30 :=
  Boolean.leaf_sound a [5,6,0,1,7,4] 30 cert744 (by decide +kernel)

def cert745 : Leaf := ⟨⟨192,160,178,165,40,156,60,60,156⟩,[],[(6,1,0),(1,3,2)],⟨35,67,13,26,148,352,220,412,316⟩,⟨35,67,13,26,148,352,192,384,288⟩,[⟨8,1184339755834606961953,⟨47,95,13,94,222,127,222,223,47⟩⟩,⟨0,1229033997465034043687936,⟨34,66,508,58,500,352,192,384,288⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,26,144,355,192,385,291⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,18,148,355,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,10,132,355,192,385,291⟩⟩]⟩
theorem node745 : UpperPrefix a [5,6,0,1,7,8] 30 :=
  Boolean.leaf_sound a [5,6,0,1,7,8] 30 cert745 (by decide +kernel)

theorem node746 : UpperPrefix a [5,6,0,1,7] 30 :=
  branch_upper a [5,6,0,1,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,1,7,0] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,1,7,1] 30 (by decide +kernel))
  node742
  node743
  node744
  (invalid_upper a [5,6,0,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,1,7,7] 30 (by decide +kernel))
  node745)

def cert747 : Leaf := ⟨⟨64,32,306,293,40,412,316,60,156⟩,[],[(6,1,0),(1,3,2)],⟨35,67,13,26,276,252,220,412,444⟩,⟨35,67,13,26,276,96,192,384,288⟩,[⟨0,1229033996902084090266624,⟨34,66,508,26,500,96,192,384,288⟩⟩,⟨7,1208926973689557018494241,⟨35,67,13,30,285,99,84,285,319⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,26,273,99,192,385,291⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,18,277,99,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,10,261,99,192,385,291⟩⟩,⟨8,1181745669222511428897,⟨35,67,13,26,21,99,192,129,35⟩⟩]⟩
theorem node747 : UpperPrefix a [5,6,0,1,8] 30 :=
  Boolean.leaf_sound a [5,6,0,1,8] 30 cert747 (by decide +kernel)

theorem node748 : UpperPrefix a [5,6,0,1] 30 :=
  branch_upper a [5,6,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,1,2] 30 (by decide +kernel))
  node741
  (invalid_upper a [5,6,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,1,6] 30 (by decide +kernel))
  node746
  node747)

def cert749 : Leaf := ⟨⟨344,312,306,0,297,408,312,56,152⟩,[(3,4)],[(6,1,0),(0,2,4),(2,3,3)],⟨35,67,13,28,22,504,472,408,440⟩,⟨35,67,13,28,22,96,192,384,288⟩,[⟨1,1323666154991598991048705,⟨33,65,493,508,508,96,192,384,288⟩⟩,⟨7,1208926973683190673982753,⟨63,95,29,28,30,127,76,285,319⟩⟩]⟩
theorem node749 : UpperPrefix a [5,6,0,2,1] 30 :=
  Boolean.leaf_sound a [5,6,0,2,1] 30 cert749 (by decide +kernel)

def cert750 : Leaf := ⟨⟨336,304,306,0,0,403,307,51,147⟩,[(3,4),(4,2)],[(6,1,0),(2,3,3),(2,3,4),(3,4,3),(3,4,4)],⟨35,67,13,28,28,498,466,402,434⟩,⟨35,67,13,28,28,96,192,384,288⟩,[⟨7,1208926973697218037171489,⟨63,95,29,28,28,127,92,285,319⟩⟩]⟩
theorem node750 : UpperPrefix a [5,6,0,2,3] 30 :=
  Boolean.leaf_sound a [5,6,0,2,3] 30 cert750 (by decide +kernel)

def cert751 : Local := ⟨⟨0,440,432,0,297,0,313,57,153⟩,[(0,5),(3,4),(5,1)],[(6,1,0),(6,1,5),(2,3,3),(1,5,0)]⟩
theorem node751 : UpperPrefix a [5,6,0,2,7,1] 30 :=
  local_sound a [5,6,0,2,7,1] 30 cert751 (by decide +kernel)

def cert752 : Leaf := ⟨⟨72,40,34,0,43,147,315,59,155⟩,[(3,4)],[(6,1,0),(2,3,3)],⟨35,67,13,28,148,104,466,402,306⟩,⟨35,67,13,28,148,104,192,384,288⟩,[⟨8,1181748004617816163683,⟨47,127,13,28,156,127,255,157,47⟩⟩,⟨4,1210107565282752182895905,⟨39,67,13,12,132,111,192,385,295⟩⟩,⟨7,1208926973663136430703905,⟨39,67,13,28,28,111,64,257,295⟩⟩]⟩
theorem node752 : UpperPrefix a [5,6,0,2,7,3] 30 :=
  Boolean.leaf_sound a [5,6,0,2,7,3] 30 cert752 (by decide +kernel)

def cert753 : Leaf := ⟨⟨80,48,50,0,43,139,315,59,27⟩,[(3,4)],[(6,1,0),(2,3,3),(7,4,5)],⟨35,67,13,28,148,112,458,394,298⟩,⟨35,67,13,28,148,112,192,384,288⟩,[⟨8,1181748004617816163683,⟨47,127,13,28,156,127,255,157,47⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,20,148,115,192,385,291⟩⟩]⟩
theorem node753 : UpperPrefix a [5,6,0,2,7,4] 30 :=
  Boolean.leaf_sound a [5,6,0,2,7,4] 30 cert753 (by decide +kernel)

def cert754 : Leaf := ⟨⟨64,32,178,0,43,155,59,59,155⟩,[(3,4)],[(6,1,0),(2,3,3)],⟨35,67,13,28,148,352,218,410,314⟩,⟨35,67,13,28,148,352,192,384,288⟩,[⟨8,1184339755834606961953,⟨47,95,13,92,222,127,222,223,47⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,20,148,355,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,12,132,355,192,385,291⟩⟩,⟨7,1208926973663136422315297,⟨35,67,13,28,28,355,64,257,291⟩⟩]⟩
theorem node754 : UpperPrefix a [5,6,0,2,7,8] 30 :=
  Boolean.leaf_sound a [5,6,0,2,7,8] 30 cert754 (by decide +kernel)

theorem node755 : UpperPrefix a [5,6,0,2,7] 30 :=
  branch_upper a [5,6,0,2,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,2,7,0] 30 (by decide +kernel))
  node751
  (invalid_upper a [5,6,0,2,7,2] 30 (by decide +kernel))
  node752
  node753
  (invalid_upper a [5,6,0,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,2,7,7] 30 (by decide +kernel))
  node754)

def cert756 : Leaf := ⟨⟨80,16,50,0,43,411,283,27,155⟩,[(3,4)],[(6,1,0),(2,3,3)],⟨35,67,13,28,276,250,218,410,442⟩,⟨35,67,13,28,276,96,192,384,288⟩,[⟨7,1208926973689584944694561,⟨39,79,13,28,285,111,92,285,319⟩⟩,⟨5,1210255570456107830742017,⟨3,67,79,222,478,64,192,384,256⟩⟩,⟨8,1181745669224663106849,⟨35,67,13,28,29,99,192,129,35⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,20,277,99,192,385,291⟩⟩]⟩
theorem node756 : UpperPrefix a [5,6,0,2,8] 30 :=
  Boolean.leaf_sound a [5,6,0,2,8] 30 cert756 (by decide +kernel)

theorem node757 : UpperPrefix a [5,6,0,2] 30 :=
  branch_upper a [5,6,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,2,0] 30 (by decide +kernel))
  node749
  (invalid_upper a [5,6,0,2,2] 30 (by decide +kernel))
  node750
  (invalid_upper a [5,6,0,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,2,6] 30 (by decide +kernel))
  node755
  node756)

def cert758 : Leaf := ⟨⟨84,52,178,36,33,152,316,60,156⟩,[],[(6,1,0),(0,2,4)],⟨35,67,13,152,22,100,472,408,312⟩,⟨35,67,13,152,22,100,192,384,288⟩,[⟨8,1181748015812314711411,⟨55,127,29,157,55,127,255,157,55⟩⟩,⟨1,1323666154850861502693377,⟨33,65,493,504,508,100,192,384,288⟩⟩,⟨3,1210107565286049635648801,⟨51,67,5,144,22,119,192,385,307⟩⟩,⟨7,1208926973665333298087201,⟨51,67,13,24,22,119,64,257,307⟩⟩]⟩
theorem node758 : UpperPrefix a [5,6,0,7,1,2] 30 :=
  Boolean.leaf_sound a [5,6,0,7,1,2] 30 cert758 (by decide +kernel)

def cert759 : Leaf := ⟨⟨76,44,34,36,41,148,316,60,28⟩,[],[(6,1,0),(0,2,4),(7,3,5)],⟨35,67,13,152,22,104,468,404,308⟩,⟨35,67,13,152,22,104,192,384,288⟩,[⟨8,1181748015812314711411,⟨55,127,29,157,55,127,255,157,55⟩⟩,⟨1,1285813292037158915276801,⟨33,65,45,504,508,104,192,384,288⟩⟩,⟨4,1210107565282752182895905,⟨39,67,13,136,6,111,192,385,295⟩⟩]⟩
theorem node759 : UpperPrefix a [5,6,0,7,1,3] 30 :=
  Boolean.leaf_sound a [5,6,0,7,1,3] 30 cert759 (by decide +kernel)

def cert760 : Leaf := ⟨⟨192,160,176,36,169,140,316,60,156⟩,[],[(6,1,0),(0,2,4)],⟨35,67,13,152,22,112,460,396,300⟩,⟨35,67,13,152,22,112,192,384,288⟩,[⟨1,1309471331383688257863681,⟨493,453,493,504,508,504,192,384,296⟩⟩,⟨8,1181748015812314711411,⟨55,127,29,157,55,127,255,157,55⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,152,18,115,192,385,291⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,144,22,115,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,136,6,99,192,385,291⟩⟩]⟩
theorem node760 : UpperPrefix a [5,6,0,7,1,4] 30 :=
  Boolean.leaf_sound a [5,6,0,7,1,4] 30 cert760 (by decide +kernel)

def cert761 : Leaf := ⟨⟨192,160,178,36,169,156,60,60,156⟩,[],[(6,1,0),(0,2,4)],⟨35,67,13,152,22,352,220,412,316⟩,⟨35,67,13,152,22,352,192,384,288⟩,[⟨8,1184195661461754301729,⟨55,95,95,222,22,127,222,223,55⟩⟩,⟨1,1285813292037158915276801,⟨33,65,45,504,508,352,192,384,288⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,152,18,355,192,385,291⟩⟩,⟨3,1210107565283850612393249,⟨35,67,5,144,22,355,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,136,6,355,192,385,291⟩⟩]⟩
theorem node761 : UpperPrefix a [5,6,0,7,1,8] 30 :=
  Boolean.leaf_sound a [5,6,0,7,1,8] 30 cert761 (by decide +kernel)

theorem node762 : UpperPrefix a [5,6,0,7,1] 30 :=
  branch_upper a [5,6,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,1,1] 30 (by decide +kernel))
  node758
  node759
  node760
  (invalid_upper a [5,6,0,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,1,7] 30 (by decide +kernel))
  node761)

def cert763 : Local := ⟨⟨0,436,432,293,0,0,309,53,149⟩,[(0,5),(4,2),(5,1)],[(6,1,0),(6,1,5),(3,4,4),(1,5,0)]⟩
theorem node763 : UpperPrefix a [5,6,0,7,3,1] 30 :=
  local_sound a [5,6,0,7,3,1] 30 cert763 (by decide +kernel)

def cert764 : Leaf := ⟨⟨84,52,178,38,0,146,310,54,22⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,13,152,28,100,466,402,306⟩,⟨35,67,13,152,28,100,192,384,288⟩,[⟨0,1214839173296368756196352,⟨506,458,508,152,60,124,192,384,304⟩⟩,⟨8,1181748007772133836131,⟨55,127,29,156,28,127,255,157,55⟩⟩,⟨7,1360042701115237799576865,⟨291,67,29,24,28,375,64,257,291⟩⟩]⟩
theorem node764 : UpperPrefix a [5,6,0,7,3,2] 30 :=
  Boolean.leaf_sound a [5,6,0,7,3,2] 30 cert764 (by decide +kernel)

def cert765 : Leaf := ⟨⟨64,32,178,39,0,135,311,55,151⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,13,152,28,112,454,390,294⟩,⟨35,67,13,152,28,112,192,384,288⟩,[⟨8,1181748007772133836131,⟨55,127,29,156,28,127,255,157,55⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,152,24,115,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,136,12,99,192,385,291⟩⟩,⟨7,1208926973663409152738593,⟨35,67,29,24,28,115,64,257,291⟩⟩]⟩
theorem node765 : UpperPrefix a [5,6,0,7,3,4] 30 :=
  Boolean.leaf_sound a [5,6,0,7,3,4] 30 cert765 (by decide +kernel)

def cert766 : Leaf := ⟨⟨64,32,178,39,0,151,55,55,151⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,13,152,28,352,214,406,310⟩,⟨35,67,13,152,28,352,192,384,288⟩,[⟨8,1184195643800848780577,⟨55,95,95,222,94,127,222,223,55⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,152,24,355,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,13,136,12,355,192,385,291⟩⟩,⟨7,1208926973663409152738593,⟨35,67,29,24,28,355,64,257,291⟩⟩]⟩
theorem node766 : UpperPrefix a [5,6,0,7,3,8] 30 :=
  Boolean.leaf_sound a [5,6,0,7,3,8] 30 cert766 (by decide +kernel)

theorem node767 : UpperPrefix a [5,6,0,7,3] 30 :=
  branch_upper a [5,6,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,3,0] 30 (by decide +kernel))
  node763
  node764
  (invalid_upper a [5,6,0,7,3,3] 30 (by decide +kernel))
  node765
  (invalid_upper a [5,6,0,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,3,7] 30 (by decide +kernel))
  node766)

#print axioms node767
end Delivery.FiniteExclusion.Sharp2x3x4
