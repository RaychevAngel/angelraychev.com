import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C009
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert640 : Leaf := ⟨⟨104,76,97,101,361,21,0,109,77⟩,[(6,4)],[(8,2,4),(7,4,6),(4,6,5)],⟨7,35,268,26,148,104,208,449,353⟩,⟨7,35,268,26,148,104,208,384,288⟩,[⟨1,1224302821660161884553217,⟨501,497,380,508,244,124,208,384,288⟩⟩]⟩
theorem node640 : UpperPrefix a [2,5,8,1,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,3,4] 30 cert640 (by decide +kernel)

theorem node641 : UpperPrefix a [2,5,8,1,7,3] 30 :=
  branch_upper a [2,5,8,1,7,3] 30 (by decide) (fin9_cases _
  node639
  (invalid_upper a [2,5,8,1,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,3] 30 (by decide +kernel))
  node640
  (invalid_upper a [2,5,8,1,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,8] 30 (by decide +kernel)))

def cert642 : Local := ⟨⟨112,84,0,101,363,135,54,0,87⟩,[(2,7),(7,2)],[(8,2,4),(7,4,5),(3,7,4)]⟩
theorem node642 : UpperPrefix a [2,5,8,1,7,4,0,3] 30 :=
  local_sound a [2,5,8,1,7,4,0,3] 30 cert642 (by decide +kernel)

def cert643 : Leaf := ⟨⟨112,84,112,100,352,132,52,52,92⟩,[],[(8,2,4),(7,4,5)],⟨7,35,268,26,148,112,193,448,296⟩,⟨7,35,268,26,148,112,193,448,288⟩,[⟨0,1522669203639716793811968,⟨286,446,268,286,180,500,508,500,432⟩⟩,⟨1,1266859030109535912067073,⟨501,241,444,508,404,112,241,480,288⟩⟩,⟨3,1210144840417225676488213,⟨247,115,503,115,247,115,243,482,290⟩⟩]⟩
theorem node643 : UpperPrefix a [2,5,8,1,7,4,0,6] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,4,0,6] 30 cert643 (by decide +kernel)

theorem node644 : UpperPrefix a [2,5,8,1,7,4,0] 30 :=
  branch_upper a [2,5,8,1,7,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,1,7,4,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,0,2] 30 (by decide +kernel))
  node642
  (invalid_upper a [2,5,8,1,7,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,0,5] 30 (by decide +kernel))
  node643
  (invalid_upper a [2,5,8,1,7,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,0,8] 30 (by decide +kernel)))

def cert645 : Leaf := ⟨⟨56,28,48,37,296,140,53,60,92⟩,[],[(8,2,4),(7,4,5)],⟨7,35,268,26,148,112,200,385,352⟩,⟨7,35,268,26,148,112,200,385,288⟩,[⟨1,1720150962344100828807169,⟨437,433,380,508,436,372,508,401,288⟩⟩,⟨6,1212504489123111823869317,⟨159,59,415,26,157,48,157,415,447⟩⟩,⟨0,1663454749895535503606784,⟨6,290,268,26,148,372,508,384,288⟩⟩]⟩
theorem node645 : UpperPrefix a [2,5,8,1,7,4,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,4,3,0] 30 cert645 (by decide +kernel)

def cert646 : Leaf := ⟨⟨56,28,49,36,296,140,52,60,29⟩,[],[(8,2,4),(7,4,5)],⟨7,35,268,26,148,112,200,448,289⟩,⟨7,35,268,26,148,112,200,448,288⟩,[⟨1,1224394792522759481065473,⟨501,433,508,508,244,112,252,496,288⟩⟩,⟨6,1370666872793130742728111,⟨263,303,271,287,157,319,157,415,303⟩⟩,⟨0,1210144549653576210711552,⟨254,122,508,58,244,112,200,448,288⟩⟩]⟩
theorem node646 : UpperPrefix a [2,5,8,1,7,4,3,6] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,4,3,6] 30 cert646 (by decide +kernel)

theorem node647 : UpperPrefix a [2,5,8,1,7,4,3] 30 :=
  branch_upper a [2,5,8,1,7,4,3] 30 (by decide) (fin9_cases _
  node645
  (invalid_upper a [2,5,8,1,7,4,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,3,5] 30 (by decide +kernel))
  node646
  (invalid_upper a [2,5,8,1,7,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,3,8] 30 (by decide +kernel)))

theorem node648 : UpperPrefix a [2,5,8,1,7,4] 30 :=
  branch_upper a [2,5,8,1,7,4] 30 (by decide) (fin9_cases _
  node644
  (invalid_upper a [2,5,8,1,7,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,2] 30 (by decide +kernel))
  node647
  (invalid_upper a [2,5,8,1,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,4,8] 30 (by decide +kernel)))

theorem node649 : UpperPrefix a [2,5,8,1,7] 30 :=
  branch_upper a [2,5,8,1,7] 30 (by decide) (fin9_cases _
  node636
  (invalid_upper a [2,5,8,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,2] 30 (by decide +kernel))
  node641
  node648
  (invalid_upper a [2,5,8,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,8] 30 (by decide +kernel)))

theorem node650 : UpperPrefix a [2,5,8,1] 30 :=
  branch_upper a [2,5,8,1] 30 (by decide) (fin9_cases _
  node612
  (invalid_upper a [2,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,2] 30 (by decide +kernel))
  node616
  (invalid_upper a [2,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,5] 30 (by decide +kernel))
  node635
  node649
  (invalid_upper a [2,5,8,1,8] 30 (by decide +kernel)))

def cert651 : Leaf := ⟨⟨96,64,241,417,0,1,313,121,217⟩,[(4,0)],[(2,0,4),(1,5,1)],⟨7,35,268,88,21,98,216,408,440⟩,⟨7,35,268,88,21,98,192,384,288⟩,[⟨3,1210107565565669186477077,⟨23,51,311,115,23,98,192,384,288⟩⟩,⟨4,1210107565564227151207445,⟨7,35,303,107,7,98,192,384,288⟩⟩,⟨7,1208926973944952848915477,⟨23,51,319,123,23,98,64,256,288⟩⟩,⟨8,1181745951041085512725,⟨23,51,63,123,23,98,192,128,32⟩⟩]⟩
theorem node651 : UpperPrefix a [2,5,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,1] 30 cert651 (by decide +kernel)

def cert652 : Leaf := ⟨⟨424,392,179,419,0,0,307,51,147⟩,[(4,0),(5,3)],[(2,0,4),(6,3,5)],⟨7,35,268,88,21,104,210,402,434⟩,⟨7,35,268,88,21,104,192,384,288⟩,[⟨3,1219580022408964715054081,⟨471,499,260,80,213,96,192,384,288⟩⟩,⟨4,1210107565564227151207445,⟨7,35,303,107,7,106,192,384,288⟩⟩]⟩
theorem node652 : UpperPrefix a [2,5,8,6,0,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,3] 30 cert652 (by decide +kernel)

def cert653 : Leaf := ⟨⟨376,344,114,0,0,0,314,122,218⟩,[(3,5),(4,0),(5,3)],[(2,0,4)],⟨7,35,268,88,21,112,202,394,426⟩,⟨7,35,268,88,21,112,192,384,288⟩,[⟨0,1219570781303941044372480,⟨454,494,300,120,20,120,192,388,300⟩⟩,⟨7,1208926976223153893858709,⟨23,59,319,123,23,123,123,279,319⟩⟩]⟩
theorem node653 : UpperPrefix a [2,5,8,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,4] 30 cert653 (by decide +kernel)

def cert654 : Leaf := ⟨⟨376,344,113,289,0,0,313,121,89⟩,[(4,0),(5,6)],[(2,0,4),(7,5,5)],⟨7,35,268,88,21,224,194,408,312⟩,⟨7,35,268,88,21,224,194,384,288⟩,[⟨1,1550782037370609251385345,⟨21,53,428,508,21,492,508,384,292⟩⟩]⟩
theorem node654 : UpperPrefix a [2,5,8,6,0,7,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,7,1] 30 cert654 (by decide +kernel)

def cert655 : Leaf := ⟨⟨368,336,115,291,0,0,307,115,83⟩,[(4,0),(5,6)],[(2,0,4),(7,5,5)],⟨7,35,268,88,21,224,200,402,306⟩,⟨7,35,268,88,21,224,200,384,288⟩,[⟨3,1276506623110786531204117,⟨407,435,439,499,407,224,482,384,288⟩⟩]⟩
theorem node655 : UpperPrefix a [2,5,8,6,0,7,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,0,7,3] 30 cert655 (by decide +kernel)

def cert656 : Local := ⟨⟨360,328,99,0,0,0,299,107,75⟩,[(3,6),(4,0),(5,6)],[(2,0,4),(7,5,5),(4,6,3)]⟩
theorem node656 : UpperPrefix a [2,5,8,6,0,7,4] 30 :=
  local_sound a [2,5,8,6,0,7,4] 30 cert656 (by decide +kernel)

theorem node657 : UpperPrefix a [2,5,8,6,0,7] 30 :=
  branch_upper a [2,5,8,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,6,0,7,0] 30 (by decide +kernel))
  node654
  (invalid_upper a [2,5,8,6,0,7,2] 30 (by decide +kernel))
  node655
  node656
  (invalid_upper a [2,5,8,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,7,8] 30 (by decide +kernel)))

theorem node658 : UpperPrefix a [2,5,8,6,0] 30 :=
  branch_upper a [2,5,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,6,0,0] 30 (by decide +kernel))
  node651
  (invalid_upper a [2,5,8,6,0,2] 30 (by decide +kernel))
  node652
  node653
  (invalid_upper a [2,5,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,0,6] 30 (by decide +kernel))
  node657
  (invalid_upper a [2,5,8,6,0,8] 30 (by decide +kernel)))

def cert659 : Leaf := ⟨⟨0,0,82,262,0,286,318,126,222⟩,[(0,4),(1,5),(4,0)],[(0,5,1)],⟨7,35,268,88,22,97,216,408,440⟩,⟨7,35,268,88,22,97,192,384,288⟩,[⟨7,1208926976223153893858709,⟨23,59,319,123,23,123,123,279,319⟩⟩,⟨5,1210107564158024860828689,⟨23,27,268,89,23,89,192,388,268⟩⟩]⟩
theorem node659 : UpperPrefix a [2,5,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,0] 30 cert659 (by decide +kernel)

def cert660 : Leaf := ⟨⟨0,268,179,423,0,0,311,55,151⟩,[(0,4),(4,0),(5,3)],[(6,3,5)],⟨7,35,268,88,22,104,209,401,433⟩,⟨7,35,268,88,22,104,192,384,288⟩,[⟨3,1219728028707118619034641,⟨471,499,324,209,471,96,192,384,288⟩⟩,⟨4,1210107565564227151207445,⟨7,35,303,107,7,106,192,384,288⟩⟩,⟨7,1208926973944952848915477,⟨23,51,319,123,23,106,64,256,288⟩⟩]⟩
theorem node660 : UpperPrefix a [2,5,8,6,1,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,3] 30 cert660 (by decide +kernel)

def cert661 : Leaf := ⟨⟨0,476,241,0,0,0,317,125,221⟩,[(0,4),(3,5),(4,0),(5,3)],[],⟨7,35,268,88,22,112,201,393,425⟩,⟨7,35,268,88,22,112,192,384,288⟩,[⟨1,1219570781866893149470721,⟨453,493,300,124,508,124,192,388,300⟩⟩]⟩
theorem node661 : UpperPrefix a [2,5,8,6,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,4] 30 cert661 (by decide +kernel)

def cert662 : Leaf := ⟨⟨0,348,114,294,0,0,318,126,94⟩,[(0,4),(4,0),(5,6)],[(7,5,5)],⟨7,35,268,88,22,224,193,408,312⟩,⟨7,35,268,88,22,224,193,384,288⟩,[⟨0,1550782037370609251386368,⟨22,54,428,508,22,492,508,384,292⟩⟩]⟩
theorem node662 : UpperPrefix a [2,5,8,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,7,0] 30 cert662 (by decide +kernel)

def cert663 : Leaf := ⟨⟨0,340,115,295,0,0,311,55,23⟩,[(0,4),(4,0),(5,6)],[(7,5,5)],⟨7,35,268,88,22,224,200,401,305⟩,⟨7,35,268,88,22,224,200,384,288⟩,[⟨3,1276506623110786531204117,⟨407,435,439,499,407,224,482,384,288⟩⟩,⟨6,1219726389396855329915921,⟨407,435,268,153,407,160,136,384,288⟩⟩]⟩
theorem node663 : UpperPrefix a [2,5,8,6,1,7,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,1,7,3] 30 cert663 (by decide +kernel)

def cert664 : Local := ⟨⟨0,332,99,0,0,0,303,111,79⟩,[(0,4),(3,6),(4,0),(5,6)],[(7,5,5),(4,6,3)]⟩
theorem node664 : UpperPrefix a [2,5,8,6,1,7,4] 30 :=
  local_sound a [2,5,8,6,1,7,4] 30 cert664 (by decide +kernel)

theorem node665 : UpperPrefix a [2,5,8,6,1,7] 30 :=
  branch_upper a [2,5,8,6,1,7] 30 (by decide) (fin9_cases _
  node662
  (invalid_upper a [2,5,8,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,2] 30 (by decide +kernel))
  node663
  node664
  (invalid_upper a [2,5,8,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,7,8] 30 (by decide +kernel)))

theorem node666 : UpperPrefix a [2,5,8,6,1] 30 :=
  branch_upper a [2,5,8,6,1] 30 (by decide) (fin9_cases _
  node659
  (invalid_upper a [2,5,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,2] 30 (by decide +kernel))
  node660
  node661
  (invalid_upper a [2,5,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,1,6] 30 (by decide +kernel))
  node665
  (invalid_upper a [2,5,8,6,1,8] 30 (by decide +kernel)))

def cert667 : Leaf := ⟨⟨96,0,242,422,0,6,310,118,214⟩,[(1,5),(4,2)],[(3,4,4),(0,5,1)],⟨7,35,268,88,28,97,210,402,434⟩,⟨7,35,268,88,28,97,192,384,288⟩,[⟨4,1210107565564227151232021,⟨7,35,303,107,47,99,192,384,290⟩⟩,⟨7,1208926973944884129463317,⟨23,35,319,123,63,99,64,256,290⟩⟩,⟨8,1181745950972366060565,⟨23,35,63,123,63,99,192,128,34⟩⟩]⟩
theorem node667 : UpperPrefix a [2,5,8,6,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,0] 30 cert667 (by decide +kernel)

def cert668 : Leaf := ⟨⟨480,448,240,420,0,385,308,112,208⟩,[(4,2)],[(3,4,4),(1,5,1),(0,6,5)],⟨7,35,268,88,28,98,193,400,432⟩,⟨7,35,268,88,28,98,193,384,288⟩,[⟨2,1323665724334882475246593,⟨3,35,424,506,440,98,227,384,288⟩⟩,⟨4,1210107567816026964933653,⟨7,35,303,107,47,98,227,384,288⟩⟩]⟩
theorem node668 : UpperPrefix a [2,5,8,6,3,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,1,0] 30 cert668 (by decide +kernel)

def cert669 : Local := ⟨⟨480,452,225,0,0,389,293,101,197⟩,[(3,6),(4,2)],[(3,4,4),(1,5,1),(4,6,3)]⟩
theorem node669 : UpperPrefix a [2,5,8,6,3,1,4] 30 :=
  local_sound a [2,5,8,6,3,1,4] 30 cert669 (by decide +kernel)

theorem node670 : UpperPrefix a [2,5,8,6,3,1] 30 :=
  branch_upper a [2,5,8,6,3,1] 30 (by decide) (fin9_cases _
  node668
  (invalid_upper a [2,5,8,6,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,3] 30 (by decide +kernel))
  node669
  (invalid_upper a [2,5,8,6,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,1,8] 30 (by decide +kernel)))

def cert671 : Leaf := ⟨⟨496,468,243,0,0,0,291,99,195⟩,[(3,5),(4,2),(5,3)],[(3,4,4)],⟨7,35,268,88,28,112,195,387,419⟩,⟨7,35,268,88,28,112,192,384,288⟩,[⟨2,1219580022690376339948545,⟨451,491,296,120,56,120,192,384,296⟩⟩,⟨4,1219580022407797557691393,⟨455,483,268,72,12,96,192,384,288⟩⟩]⟩
theorem node671 : UpperPrefix a [2,5,8,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,4] 30 cert671 (by decide +kernel)

def cert672 : Leaf := ⟨⟨352,320,115,295,0,0,310,115,83⟩,[(4,2),(5,6)],[(3,4,4),(7,5,5)],⟨7,35,268,88,28,224,193,402,306⟩,⟨7,35,268,88,28,224,193,384,288⟩,[⟨2,1247960286656378475414529,⟨3,35,424,506,440,226,227,384,288⟩⟩,⟨4,1210107567534551988212757,⟨7,35,271,107,15,226,227,384,288⟩⟩]⟩
theorem node672 : UpperPrefix a [2,5,8,6,3,7,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,7,0] 30 cert672 (by decide +kernel)

def cert673 : Leaf := ⟨⟨368,340,113,293,0,0,309,117,85⟩,[(4,2),(5,6)],[(3,4,4),(7,5,5)],⟨7,35,268,88,28,224,194,401,305⟩,⟨7,35,268,88,28,224,194,384,288⟩,[⟨1,1219579970642665652355073,⟨405,445,284,124,28,252,508,404,316⟩⟩]⟩
theorem node673 : UpperPrefix a [2,5,8,6,3,7,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,3,7,1] 30 cert673 (by decide +kernel)

def cert674 : Local := ⟨⟨352,324,99,0,0,0,295,103,71⟩,[(3,6),(4,2),(5,6)],[(3,4,4),(7,5,5),(4,6,3)]⟩
theorem node674 : UpperPrefix a [2,5,8,6,3,7,4] 30 :=
  local_sound a [2,5,8,6,3,7,4] 30 cert674 (by decide +kernel)

theorem node675 : UpperPrefix a [2,5,8,6,3,7] 30 :=
  branch_upper a [2,5,8,6,3,7] 30 (by decide) (fin9_cases _
  node672
  node673
  (invalid_upper a [2,5,8,6,3,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,3] 30 (by decide +kernel))
  node674
  (invalid_upper a [2,5,8,6,3,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,7,8] 30 (by decide +kernel)))

theorem node676 : UpperPrefix a [2,5,8,6,3] 30 :=
  branch_upper a [2,5,8,6,3] 30 (by decide) (fin9_cases _
  node667
  node670
  (invalid_upper a [2,5,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,3] 30 (by decide +kernel))
  node671
  (invalid_upper a [2,5,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,3,6] 30 (by decide +kernel))
  node675
  (invalid_upper a [2,5,8,6,3,8] 30 (by decide +kernel)))

def cert677 : Leaf := ⟨⟨120,0,80,132,328,30,28,92,92⟩,[(1,5)],[(8,2,4),(7,4,3),(0,5,1),(1,6,5)],⟨7,35,268,88,148,97,194,408,312⟩,⟨7,35,268,88,148,97,194,384,288⟩,[⟨5,1212505658928677761582081,⟨223,91,412,88,148,89,218,404,412⟩⟩]⟩
theorem node677 : UpperPrefix a [2,5,8,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,0,1] 30 cert677 (by decide +kernel)

def cert678 : Leaf := ⟨⟨112,0,112,164,352,22,52,118,86⟩,[(1,5)],[(8,2,4),(7,4,3),(0,5,1)],⟨7,35,268,88,148,97,200,402,306⟩,⟨7,35,268,88,148,97,200,384,288⟩,[⟨3,1427917496215994717199381,⟨407,435,439,499,407,499,482,384,418⟩⟩,⟨1,1210110159370463503974401,⟨5,41,268,88,220,121,220,476,300⟩⟩]⟩
theorem node678 : UpperPrefix a [2,5,8,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,0,3] 30 cert678 (by decide +kernel)

def cert679 : Local := ⟨⟨104,0,98,0,362,14,0,110,78⟩,[(1,5),(3,6),(6,4)],[(8,2,4),(7,4,3),(7,4,6),(0,5,1),(4,6,3)]⟩
theorem node679 : UpperPrefix a [2,5,8,6,7,0,4] 30 :=
  local_sound a [2,5,8,6,7,0,4] 30 cert679 (by decide +kernel)

theorem node680 : UpperPrefix a [2,5,8,6,7,0] 30 :=
  branch_upper a [2,5,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,6,7,0,0] 30 (by decide +kernel))
  node677
  (invalid_upper a [2,5,8,6,7,0,2] 30 (by decide +kernel))
  node678
  node679
  (invalid_upper a [2,5,8,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,0,8] 30 (by decide +kernel)))

def cert681 : Leaf := ⟨⟨112,80,112,164,360,17,52,120,88⟩,[],[(8,2,4),(7,4,3),(1,5,1),(0,6,5)],⟨7,35,268,88,148,98,193,408,312⟩,⟨7,35,268,88,148,98,193,384,288⟩,[⟨2,1247960286656378475414529,⟨3,35,424,506,144,98,227,384,288⟩⟩,⟨3,1210107856610451507952661,⟨7,35,295,115,247,98,227,384,288⟩⟩]⟩
theorem node681 : UpperPrefix a [2,5,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,1,0] 30 cert681 (by decide +kernel)

def cert682 : Leaf := ⟨⟨112,84,112,164,352,21,52,117,85⟩,[],[(8,2,4),(7,4,3),(1,5,1)],⟨7,35,268,88,148,98,200,401,305⟩,⟨7,35,268,88,148,98,200,384,288⟩,[⟨3,1276506623110786531204117,⟨407,435,439,499,407,482,482,384,288⟩⟩,⟨0,1210110159370463503975424,⟨6,42,268,88,220,122,220,476,300⟩⟩]⟩
theorem node682 : UpperPrefix a [2,5,8,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,1,3] 30 cert682 (by decide +kernel)

def cert683 : Local := ⟨⟨104,76,97,0,361,13,0,109,77⟩,[(3,6),(6,4)],[(8,2,4),(7,4,3),(7,4,6),(1,5,1),(4,6,3)]⟩
theorem node683 : UpperPrefix a [2,5,8,6,7,1,4] 30 :=
  local_sound a [2,5,8,6,7,1,4] 30 cert683 (by decide +kernel)

theorem node684 : UpperPrefix a [2,5,8,6,7,1] 30 :=
  branch_upper a [2,5,8,6,7,1] 30 (by decide) (fin9_cases _
  node681
  (invalid_upper a [2,5,8,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,2] 30 (by decide +kernel))
  node682
  node683
  (invalid_upper a [2,5,8,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,1,8] 30 (by decide +kernel)))

def cert685 : Leaf := ⟨⟨56,28,51,166,290,0,54,54,22⟩,[(5,3)],[(8,2,4),(6,3,5),(7,4,3)],⟨7,35,268,88,148,104,193,402,306⟩,⟨7,35,268,88,148,104,193,384,288⟩,[⟨0,1219579970899053640680448,⟨406,434,300,120,148,104,248,384,288⟩⟩,⟨3,1219580022408964715054081,⟨471,499,260,80,148,96,209,384,288⟩⟩]⟩
theorem node685 : UpperPrefix a [2,5,8,6,7,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,3,0] 30 cert685 (by decide +kernel)

def cert686 : Leaf := ⟨⟨56,28,49,165,289,0,53,53,21⟩,[(5,3)],[(8,2,4),(6,3,5),(7,4,3)],⟨7,35,268,88,148,104,194,401,305⟩,⟨7,35,268,88,148,104,194,384,288⟩,[⟨1,1219579970912389598543873,⟨405,445,300,124,148,124,508,404,300⟩⟩,⟨3,1219580022408964715054081,⟨471,499,260,80,148,96,450,384,288⟩⟩]⟩
theorem node686 : UpperPrefix a [2,5,8,6,7,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,3,1] 30 cert686 (by decide +kernel)

def cert687 : Local := ⟨⟨40,12,35,0,299,0,0,47,15⟩,[(3,6),(5,3),(6,4)],[(8,2,4),(6,3,5),(7,4,3),(7,4,6),(4,6,3),(4,6,5)]⟩
theorem node687 : UpperPrefix a [2,5,8,6,7,3,4] 30 :=
  local_sound a [2,5,8,6,7,3,4] 30 cert687 (by decide +kernel)

theorem node688 : UpperPrefix a [2,5,8,6,7,3] 30 :=
  branch_upper a [2,5,8,6,7,3] 30 (by decide) (fin9_cases _
  node685
  node686
  (invalid_upper a [2,5,8,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,3,3] 30 (by decide +kernel))
  node687
  (invalid_upper a [2,5,8,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,3,8] 30 (by decide +kernel)))

def cert689 : Leaf := ⟨⟨112,84,112,0,360,0,59,123,91⟩,[(3,5),(5,3)],[(8,2,4),(7,4,3),(7,4,5)],⟨7,35,268,88,148,112,203,395,299⟩,⟨7,35,268,88,148,112,192,384,288⟩,[⟨2,1219570781303940975690753,⟨451,491,296,120,144,120,192,384,296⟩⟩,⟨0,1210107567825935521547264,⟨6,42,300,120,148,120,248,404,300⟩⟩,⟨1,1210107567825935521546241,⟨5,41,300,120,148,120,248,404,300⟩⟩,⟨3,1210107565565325589109781,⟨7,35,295,115,151,115,192,384,290⟩⟩]⟩
theorem node689 : UpperPrefix a [2,5,8,6,7,4] 30 :=
  Boolean.leaf_sound a [2,5,8,6,7,4] 30 cert689 (by decide +kernel)

theorem node690 : UpperPrefix a [2,5,8,6,7] 30 :=
  branch_upper a [2,5,8,6,7] 30 (by decide) (fin9_cases _
  node680
  node684
  (invalid_upper a [2,5,8,6,7,2] 30 (by decide +kernel))
  node688
  node689
  (invalid_upper a [2,5,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,7,8] 30 (by decide +kernel)))

theorem node691 : UpperPrefix a [2,5,8,6] 30 :=
  branch_upper a [2,5,8,6] 30 (by decide) (fin9_cases _
  node658
  node666
  (invalid_upper a [2,5,8,6,2] 30 (by decide +kernel))
  node676
  (invalid_upper a [2,5,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,6,6] 30 (by decide +kernel))
  node690
  (invalid_upper a [2,5,8,6,8] 30 (by decide +kernel)))

def cert692 : Local := ⟨⟨376,344,113,353,0,281,0,121,89⟩,[(4,0),(6,3)],[(2,0,4),(7,3,6),(1,5,1)]⟩
theorem node692 : UpperPrefix a [2,5,8,7,0,1,3] 30 :=
  local_sound a [2,5,8,7,0,1,3] 30 cert692 (by decide +kernel)

def cert693 : Leaf := ⟨⟨504,472,240,0,0,409,0,120,216⟩,[(3,6),(4,0),(6,3)],[(2,0,4),(1,5,1)],⟨7,35,268,152,21,98,208,456,360⟩,⟨7,35,268,152,21,98,208,384,288⟩,[⟨0,1361555766474582078260224,⟨134,422,460,216,220,494,216,384,420⟩⟩]⟩
theorem node693 : UpperPrefix a [2,5,8,7,0,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,1,4] 30 cert693 (by decide +kernel)

theorem node694 : UpperPrefix a [2,5,8,7,0,1] 30 :=
  branch_upper a [2,5,8,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,1,2] 30 (by decide +kernel))
  node692
  node693
  (invalid_upper a [2,5,8,7,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,1,8] 30 (by decide +kernel)))

def cert695 : Leaf := ⟨⟨104,72,113,353,0,129,41,121,89⟩,[(4,0)],[(2,0,4),(7,3,5)],⟨7,35,268,152,21,104,194,464,368⟩,⟨7,35,268,152,21,104,194,384,288⟩,[⟨1,1512929318249882272661505,⟨21,53,268,152,21,492,508,384,292⟩⟩,⟨4,1210107709820152715427349,⟨39,35,367,235,39,106,194,384,288⟩⟩,⟨8,1181890206966649732629,⟨55,51,127,251,55,106,194,128,32⟩⟩]⟩
theorem node695 : UpperPrefix a [2,5,8,7,0,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,3,1] 30 cert695 (by decide +kernel)

def cert696 : Local := ⟨⟨360,328,99,0,0,403,0,107,75⟩,[(3,6),(4,0),(6,3)],[(2,0,4),(7,3,5),(4,6,5)]⟩
theorem node696 : UpperPrefix a [2,5,8,7,0,3,4] 30 :=
  local_sound a [2,5,8,7,0,3,4] 30 cert696 (by decide +kernel)

theorem node697 : UpperPrefix a [2,5,8,7,0,3] 30 :=
  branch_upper a [2,5,8,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,0,3,0] 30 (by decide +kernel))
  node695
  (invalid_upper a [2,5,8,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,3] 30 (by decide +kernel))
  node696
  (invalid_upper a [2,5,8,7,0,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,3,8] 30 (by decide +kernel)))

def cert698 : Leaf := ⟨⟨496,464,240,352,0,384,304,120,216⟩,[(4,0)],[(2,0,4)],⟨7,35,268,152,21,112,194,456,360⟩,⟨7,35,268,152,21,112,194,384,288⟩,[⟨0,1446687112635328692225024,⟨454,494,268,444,508,508,454,388,428⟩⟩,⟨1,1664340193606894903361537,⟨29,445,268,152,21,508,508,388,428⟩⟩,⟨3,1210107709821594750713365,⟨55,51,375,243,55,115,194,384,290⟩⟩]⟩
theorem node698 : UpperPrefix a [2,5,8,7,0,4,1] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,4,1] 30 cert698 (by decide +kernel)

def cert699 : Leaf := ⟨⟨120,88,115,355,0,10,0,123,91⟩,[(4,0),(6,3)],[(2,0,4),(7,3,6)],⟨7,35,268,152,21,112,200,450,354⟩,⟨7,35,268,152,21,112,200,384,288⟩,[⟨8,1181890206966649749013,⟨55,51,127,251,55,115,234,128,34⟩⟩,⟨0,1210107709680514738684928,⟨6,34,364,248,20,112,232,384,288⟩⟩]⟩
theorem node699 : UpperPrefix a [2,5,8,7,0,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,7,0,4,3] 30 cert699 (by decide +kernel)

theorem node700 : UpperPrefix a [2,5,8,7,0,4] 30 :=
  branch_upper a [2,5,8,7,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,0,4,0] 30 (by decide +kernel))
  node698
  (invalid_upper a [2,5,8,7,0,4,2] 30 (by decide +kernel))
  node699
  (invalid_upper a [2,5,8,7,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,4,8] 30 (by decide +kernel)))

theorem node701 : UpperPrefix a [2,5,8,7,0] 30 :=
  branch_upper a [2,5,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,7,0,0] 30 (by decide +kernel))
  node694
  (invalid_upper a [2,5,8,7,0,2] 30 (by decide +kernel))
  node697
  node700
  (invalid_upper a [2,5,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,7,0,8] 30 (by decide +kernel)))

def cert702 : Leaf := ⟨⟨0,0,242,358,0,158,56,126,222⟩,[(0,4),(1,5),(4,0)],[(0,5,1)],⟨7,35,268,152,22,97,216,472,376⟩,⟨7,35,268,152,22,97,192,384,288⟩,[⟨8,1181890206966649749013,⟨55,51,127,251,55,115,192,128,34⟩⟩,⟨1,1210107709399039761973249,⟨5,33,332,216,20,97,192,384,288⟩⟩,⟨2,1210107709399039760942081,⟨3,35,328,216,18,99,192,384,290⟩⟩]⟩
theorem node702 : UpperPrefix a [2,5,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,0] 30 cert702 (by decide +kernel)

def cert703 : Leaf := ⟨⟨0,92,114,102,0,150,54,118,86⟩,[(0,4),(4,0)],[(7,3,5)],⟨7,35,268,152,22,104,193,464,368⟩,⟨7,35,268,152,22,104,193,384,288⟩,[⟨0,1512929318249882272662528,⟨22,54,268,152,22,492,508,384,292⟩⟩,⟨8,1181892458775053385237,⟨55,51,127,251,55,106,251,128,32⟩⟩,⟨3,1219728028707118619034641,⟨471,499,324,209,471,96,209,384,288⟩⟩]⟩
theorem node703 : UpperPrefix a [2,5,8,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,7,1,3,0] 30 cert703 (by decide +kernel)

#print axioms node703
end Delivery.FiniteExclusion.Sharp2x3x4
