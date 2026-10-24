import RegularNineSharp4x5Base
import RegularNineSharp4x5C002
import RegularNineSharp4x5C008
import RegularNineSharp4x5C009
import RegularNineSharp4x5C015
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert1024 : Leaf := ⟨⟨44,88,145,20,6,28,285,29,13⟩,[],[(5,1,0),(6,2,1),(7,3,2)],⟨19,38,76,137,56,98,453,389,277⟩,⟨19,38,76,137,56,98,192,384,272⟩,[⟨8,1181748068657556155767,⟨19,55,127,137,63,127,255,137,19⟩⟩,⟨1,1214913104244639750422529,⟨477,36,204,461,252,96,192,384,276⟩⟩,⟨0,1210107565424864052382720,⟨18,54,126,136,56,98,192,384,272⟩⟩]⟩
theorem node1024 : UpperPrefix a [4,5,6,7,3,1] 30 :=
  Boolean.leaf_sound a [4,5,6,7,3,1] 30 cert1024 (by decide +kernel)

def cert1025 : Local := ⟨⟨296,0,403,274,259,0,283,27,11⟩,[(1,5),(5,2)],[(5,1,0),(6,2,1),(6,2,5),(7,3,2),(2,5,1)]⟩
theorem node1025 : UpperPrefix a [4,5,6,7,3,2] 30 :=
  local_sound a [4,5,6,7,3,2] 30 cert1025 (by decide +kernel)

def cert1026 : Local := ⟨⟨300,344,403,0,262,30,0,30,14⟩,[(3,6),(6,3)],[(5,1,0),(6,2,1),(7,3,2),(0,6,2)]⟩
theorem node1026 : UpperPrefix a [4,5,6,7,3,8,0] 30 :=
  local_sound a [4,5,6,7,3,8,0] 30 cert1026 (by decide +kernel)

def cert1027 : Local := ⟨⟨300,328,386,0,262,14,268,30,14⟩,[(3,7)],[(4,0,7),(5,1,0),(6,2,1),(7,3,2),(0,7,3)]⟩
theorem node1027 : UpperPrefix a [4,5,6,7,3,8,1,0] 30 :=
  local_sound a [4,5,6,7,3,8,1,0] 30 cert1027 (by decide +kernel)

def cert1028 : Leaf := ⟨⟨296,344,402,274,258,26,284,26,11⟩,[],[(5,1,0),(6,2,1),(7,3,2),(2,7,6)],⟨19,38,76,137,56,352,194,388,273⟩,⟨19,38,76,137,56,352,194,388,272⟩,[⟨0,1212476400141603173512192,⟨22,102,94,254,126,482,226,486,502⟩⟩]⟩
theorem node1028 : UpperPrefix a [4,5,6,7,3,8,1,2] 30 :=
  Boolean.leaf_sound a [4,5,6,7,3,8,1,2] 30 cert1028 (by decide +kernel)

theorem node1029 : UpperPrefix a [4,5,6,7,3,8,1] 30 :=
  branch_upper a [4,5,6,7,3,8,1] 30 (by decide) (fin9_cases _
  node1027
  (invalid_upper a [4,5,6,7,3,8,1,1] 30 (by decide +kernel))
  node1028
  (invalid_upper a [4,5,6,7,3,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,1,8] 30 (by decide +kernel)))

def cert1030 : Leaf := ⟨⟨40,88,146,18,259,31,26,27,11⟩,[],[(5,1,0),(6,2,1),(7,3,2)],⟨19,38,76,137,56,352,196,387,275⟩,⟨19,38,76,137,56,352,196,384,272⟩,[⟨2,1224302334848709026644995,⟨411,443,72,393,56,352,192,384,272⟩⟩,⟨8,1184195627437037479185,⟨23,38,76,205,127,103,204,205,23⟩⟩,⟨0,1210107709399039768273920,⟨22,38,76,204,126,352,196,384,278⟩⟩]⟩
theorem node1030 : UpperPrefix a [4,5,6,7,3,8,2] 30 :=
  Boolean.leaf_sound a [4,5,6,7,3,8,2] 30 cert1030 (by decide +kernel)

theorem node1031 : UpperPrefix a [4,5,6,7,3,8] 30 :=
  branch_upper a [4,5,6,7,3,8] 30 (by decide) (fin9_cases _
  node1026
  node1029
  node1030
  (invalid_upper a [4,5,6,7,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,8,8] 30 (by decide +kernel)))

theorem node1032 : UpperPrefix a [4,5,6,7,3] 30 :=
  branch_upper a [4,5,6,7,3] 30 (by decide) (fin9_cases _
  node1023
  node1024
  node1025
  (invalid_upper a [4,5,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,7] 30 (by decide +kernel))
  node1031)

def cert1033 : Leaf := ⟨⟨300,73,129,276,13,14,13,29,13⟩,[],[(5,1,0),(6,2,1),(7,3,2),(1,6,5)],⟨19,38,76,137,304,97,194,396,284⟩,⟨19,38,76,137,304,97,194,384,272⟩,[⟨4,1210107709679415229160449,⟨3,38,110,239,288,97,194,384,256⟩⟩,⟨8,1181890065885566082049,⟨19,38,110,239,48,97,194,128,16⟩⟩]⟩
theorem node1033 : UpperPrefix a [4,5,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [4,5,6,7,8,0,1] 30 cert1033 (by decide +kernel)

def cert1034 : Leaf := ⟨⟨296,73,131,274,11,14,11,27,11⟩,[],[(5,1,0),(6,2,1),(7,3,2)],⟨19,38,76,137,304,97,196,394,282⟩,⟨19,38,76,137,304,97,196,384,272⟩,[⟨2,1224302334850912344867843,⟨411,443,72,393,312,505,192,384,272⟩⟩,⟨4,1210107709679415229160449,⟨3,38,110,239,288,97,198,384,256⟩⟩,⟨8,1181890065885566082049,⟨19,38,110,239,48,97,198,128,16⟩⟩]⟩
theorem node1034 : UpperPrefix a [4,5,6,7,8,0,2] 30 :=
  Boolean.leaf_sound a [4,5,6,7,8,0,2] 30 cert1034 (by decide +kernel)

def cert1035 : Local := ⟨⟨292,337,0,278,7,278,0,23,7⟩,[(2,6),(6,3)],[(5,1,0),(6,2,1),(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node1035 : UpperPrefix a [4,5,6,7,8,0,3] 30 :=
  local_sound a [4,5,6,7,8,0,3] 30 cert1035 (by decide +kernel)

theorem node1036 : UpperPrefix a [4,5,6,7,8,0] 30 :=
  branch_upper a [4,5,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,6,7,8,0,0] 30 (by decide +kernel))
  node1033
  node1034
  node1035
  (invalid_upper a [4,5,6,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,0,8] 30 (by decide +kernel)))

def cert1037 : Leaf := ⟨⟨300,73,129,276,15,13,13,29,13⟩,[],[(5,1,0),(6,2,1),(7,3,2)],⟨19,38,76,137,304,98,205,397,285⟩,⟨19,38,76,137,304,98,192,384,272⟩,[⟨1,1214913104244639746228225,⟨477,36,204,461,304,96,192,384,272⟩⟩,⟨4,1210107709820152717515777,⟨3,38,110,239,288,98,192,384,256⟩⟩,⟨8,1181890206623054437377,⟨19,38,110,239,48,98,192,128,16⟩⟩]⟩
theorem node1037 : UpperPrefix a [4,5,6,7,8,1] 30 :=
  Boolean.leaf_sound a [4,5,6,7,8,1] 30 cert1037 (by decide +kernel)

def cert1038 : Local := ⟨⟨296,0,403,274,11,0,283,27,11⟩,[(1,5),(5,2)],[(5,1,0),(6,2,1),(6,2,5),(7,3,2),(2,5,1)]⟩
theorem node1038 : UpperPrefix a [4,5,6,7,8,2] 30 :=
  local_sound a [4,5,6,7,8,2] 30 cert1038 (by decide +kernel)

def cert1039 : Local := ⟨⟨292,345,0,278,7,0,279,23,7⟩,[(2,5),(5,2)],[(5,1,0),(6,2,1),(7,3,2),(7,3,5),(3,5,1)]⟩
theorem node1039 : UpperPrefix a [4,5,6,7,8,3] 30 :=
  local_sound a [4,5,6,7,8,3] 30 cert1039 (by decide +kernel)

theorem node1040 : UpperPrefix a [4,5,6,7,8] 30 :=
  branch_upper a [4,5,6,7,8] 30 (by decide) (fin9_cases _
  node1036
  node1037
  node1038
  node1039
  (invalid_upper a [4,5,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,8,8] 30 (by decide +kernel)))

theorem node1041 : UpperPrefix a [4,5,6,7] 30 :=
  branch_upper a [4,5,6,7] 30 (by decide) (fin9_cases _
  node1017
  node1018
  node1019
  node1032
  (invalid_upper a [4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,7] 30 (by decide +kernel))
  node1040)

theorem node1042 : UpperPrefix a [4,5,6] 30 :=
  branch_upper a [4,5,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,5,6,1] [2,4,5,6] 30 (by decide +kernel) node152)
  (PrefixConjugacy.upper aut5 [4,5,6,2] [3,4,5,6] 30 (by decide +kernel) node557)
  (invalid_upper a [4,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,6] 30 (by decide +kernel))
  node1041
  (PrefixConjugacy.upper aut6 [4,5,6,8] [4,5,6,7] 30 (by decide +kernel) node1041))

def cert1043 : Leaf := ⟨⟨32,217,81,16,2,157,285,93,77⟩,[],[(5,1,0),(1,5,4)],⟨19,38,140,73,49,98,460,396,284⟩,⟨19,38,140,73,49,98,192,384,272⟩,[⟨8,1181748210069345983615,⟨19,63,191,127,59,127,255,128,17⟩⟩,⟨7,1218371706631214322418723,⟨275,319,12,73,57,379,64,256,272⟩⟩,⟨2,1210107565286192442246179,⟨19,59,136,73,57,123,192,384,272⟩⟩,⟨3,1210107565286187074585635,⟨19,55,132,65,49,115,192,384,272⟩⟩,⟨6,1210106412364683541480483,⟨19,55,140,9,49,51,128,384,272⟩⟩]⟩
theorem node1043 : UpperPrefix a [4,5,7,6,0,1] 30 :=
  Boolean.leaf_sound a [4,5,7,6,0,1] 30 cert1043 (by decide +kernel)

def cert1044 : Leaf := ⟨⟨96,0,83,18,66,155,283,91,75⟩,[(1,5)],[(5,1,0),(7,2,5),(2,5,1)],⟨19,38,140,73,49,100,458,394,282⟩,⟨19,38,140,73,49,100,192,384,272⟩,[⟨8,1181748210069345983615,⟨19,63,191,127,59,127,255,128,17⟩⟩,⟨3,1210107565286187074602035,⟨19,55,132,65,51,119,192,384,273⟩⟩]⟩
theorem node1044 : UpperPrefix a [4,5,7,6,0,2] 30 :=
  Boolean.leaf_sound a [4,5,7,6,0,2] 30 cert1044 (by decide +kernel)

def cert1045 : Leaf := ⟨⟨164,153,19,150,134,0,279,23,135⟩,[(5,3)],[(5,1,0),(6,3,5),(3,5,1)],⟨19,38,140,73,49,104,454,390,278⟩,⟨19,38,140,73,49,104,192,384,272⟩,[⟨8,1181748210069345983615,⟨19,63,191,127,59,127,255,128,17⟩⟩]⟩
theorem node1045 : UpperPrefix a [4,5,7,6,0,3] 30 :=
  Boolean.leaf_sound a [4,5,7,6,0,3] 30 cert1045 (by decide +kernel)

def cert1046 : Leaf := ⟨⟨108,201,65,6,76,13,269,77,77⟩,[],[(5,1,0),(1,6,3)],⟨19,38,140,73,49,352,194,396,284⟩,⟨19,38,140,73,49,352,194,384,272⟩,[⟨4,1212476328082362076449793,⟨11,102,238,73,107,486,226,486,494⟩⟩,⟨7,1237261174819449109218371,⟨275,319,284,121,57,377,379,256,272⟩⟩,⟨8,1181745671571875316851,⟨19,63,140,77,59,127,223,128,17⟩⟩]⟩
theorem node1046 : UpperPrefix a [4,5,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [4,5,7,6,0,8,1] 30 cert1046 (by decide +kernel)

def cert1047 : Leaf := ⟨⟨104,329,323,6,74,15,0,79,79⟩,[(6,2)],[(5,1,0),(7,2,6)],⟨19,38,140,73,49,352,196,394,282⟩,⟨19,38,140,73,49,352,196,384,272⟩,[⟨4,1212476328082362076482561,⟨11,102,238,75,107,486,230,486,494⟩⟩,⟨8,1181817726954256729091,⟨27,127,204,73,49,96,196,128,16⟩⟩,⟨2,1210107565283989124023299,⟨19,51,136,73,49,352,192,384,272⟩⟩]⟩
theorem node1047 : UpperPrefix a [4,5,7,6,0,8,2] 30 :=
  Boolean.leaf_sound a [4,5,7,6,0,8,2] 30 cert1047 (by decide +kernel)

def cert1048 : Leaf := ⟨⟨420,393,0,390,390,143,0,7,135⟩,[(2,6),(6,2)],[(5,1,0)],⟨19,38,140,73,49,352,200,390,278⟩,⟨19,38,140,73,49,352,200,384,272⟩,[⟨6,1370980467431504557917235,⟨403,439,140,13,435,439,140,384,273⟩⟩,⟨3,1219570744993801051309059,⟨403,439,132,65,49,352,192,384,272⟩⟩,⟨4,1212768881914156219100161,⟨79,230,238,79,239,486,238,486,494⟩⟩]⟩
theorem node1048 : UpperPrefix a [4,5,7,6,0,8,3] 30 :=
  Boolean.leaf_sound a [4,5,7,6,0,8,3] 30 cert1048 (by decide +kernel)

theorem node1049 : UpperPrefix a [4,5,7,6,0,8] 30 :=
  branch_upper a [4,5,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,7,6,0,8,0] 30 (by decide +kernel))
  node1046
  node1047
  node1048
  (invalid_upper a [4,5,7,6,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,0,8,8] 30 (by decide +kernel)))

theorem node1050 : UpperPrefix a [4,5,7,6,0] 30 :=
  branch_upper a [4,5,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,7,6,0,0] 30 (by decide +kernel))
  node1043
  node1044
  node1045
  (invalid_upper a [4,5,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,0,7] 30 (by decide +kernel))
  node1049)

def cert1051 : Local := ⟨⟨0,473,337,0,0,0,285,93,205⟩,[(0,4),(3,5),(4,1),(5,3)],[(5,1,0),(5,1,4),(1,4,0)]⟩
theorem node1051 : UpperPrefix a [4,5,7,6,1,0] 30 :=
  local_sound a [4,5,7,6,1,0] 30 cert1051 (by decide +kernel)

def cert1052 : Local := ⟨⟨0,0,337,272,0,409,281,89,73⟩,[(0,4),(1,5),(4,1)],[(5,1,0),(5,1,4),(7,2,5),(1,4,0),(2,5,1),(2,5,4)]⟩
theorem node1052 : UpperPrefix a [4,5,7,6,1,2] 30 :=
  local_sound a [4,5,7,6,1,2] 30 cert1052 (by decide +kernel)

def cert1053 : Local := ⟨⟨0,409,273,404,0,0,277,21,133⟩,[(0,4),(4,1),(5,3)],[(5,1,0),(5,1,4),(6,3,5),(1,4,0),(3,5,1)]⟩
theorem node1053 : UpperPrefix a [4,5,7,6,1,3] 30 :=
  local_sound a [4,5,7,6,1,3] 30 cert1053 (by decide +kernel)

def cert1054 : Local := ⟨⟨0,472,336,0,0,156,284,92,204⟩,[(0,4),(3,6),(4,1)],[(5,1,0),(5,1,4),(1,4,0),(0,6,3)]⟩
theorem node1054 : UpperPrefix a [4,5,7,6,1,8,0] 30 :=
  local_sound a [4,5,7,6,1,8,0] 30 cert1054 (by decide +kernel)

def cert1055 : Local := ⟨⟨0,345,337,276,0,29,0,93,77⟩,[(0,4),(4,1),(6,2)],[(5,1,0),(5,1,4),(7,2,6),(1,4,0)]⟩
theorem node1055 : UpperPrefix a [4,5,7,6,1,8,2] 30 :=
  local_sound a [4,5,7,6,1,8,2] 30 cert1055 (by decide +kernel)

def cert1056 : Local := ⟨⟨0,473,0,404,0,157,0,93,205⟩,[(0,4),(2,6),(4,1),(6,2)],[(5,1,0),(5,1,4),(1,4,0)]⟩
theorem node1056 : UpperPrefix a [4,5,7,6,1,8,3] 30 :=
  local_sound a [4,5,7,6,1,8,3] 30 cert1056 (by decide +kernel)

theorem node1057 : UpperPrefix a [4,5,7,6,1,8] 30 :=
  branch_upper a [4,5,7,6,1,8] 30 (by decide) (fin9_cases _
  node1054
  (invalid_upper a [4,5,7,6,1,8,1] 30 (by decide +kernel))
  node1055
  node1056
  (invalid_upper a [4,5,7,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,1,8,8] 30 (by decide +kernel)))

theorem node1058 : UpperPrefix a [4,5,7,6,1] 30 :=
  branch_upper a [4,5,7,6,1] 30 (by decide) (fin9_cases _
  node1051
  (invalid_upper a [4,5,7,6,1,1] 30 (by decide +kernel))
  node1052
  node1053
  (invalid_upper a [4,5,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,1,7] 30 (by decide +kernel))
  node1057)

def cert1059 : Local := ⟨⟨492,0,339,0,0,0,283,91,203⟩,[(1,4),(3,5),(4,1),(5,3)],[(5,1,0),(2,4,0)]⟩
theorem node1059 : UpperPrefix a [4,5,7,6,2,0] 30 :=
  local_sound a [4,5,7,6,2,0] 30 cert1059 (by decide +kernel)

def cert1060 : Leaf := ⟨⟨492,0,337,400,0,409,281,89,201⟩,[(1,4),(4,1)],[(5,1,0),(2,4,0)],⟨19,38,140,73,52,98,457,393,281⟩,⟨19,38,140,73,52,98,192,384,272⟩,[⟨1,1214913104244777185181697,⟨477,52,204,461,52,112,192,384,272⟩⟩]⟩
theorem node1060 : UpperPrefix a [4,5,7,6,2,1] 30 :=
  Boolean.leaf_sound a [4,5,7,6,2,1] 30 cert1060 (by decide +kernel)

def cert1061 : Local := ⟨⟨420,0,275,402,0,0,275,19,131⟩,[(1,4),(4,1),(5,3)],[(5,1,0),(6,3,5),(2,4,0),(3,5,1),(3,5,4)]⟩
theorem node1061 : UpperPrefix a [4,5,7,6,2,3] 30 :=
  local_sound a [4,5,7,6,2,3] 30 cert1061 (by decide +kernel)

def cert1062 : Leaf := ⟨⟨108,0,339,18,0,155,283,91,75⟩,[(1,4),(4,1)],[(5,1,0),(2,4,0)],⟨19,38,140,73,52,352,203,395,283⟩,⟨19,38,140,73,52,352,192,384,272⟩,[⟨7,1293929570354929622590739,⟨275,319,12,73,319,361,64,257,275⟩⟩,⟨8,1181745669364245341459,⟨19,63,140,73,63,105,192,129,19⟩⟩]⟩
theorem node1062 : UpperPrefix a [4,5,7,6,2,8] 30 :=
  Boolean.leaf_sound a [4,5,7,6,2,8] 30 cert1062 (by decide +kernel)

theorem node1063 : UpperPrefix a [4,5,7,6,2] 30 :=
  branch_upper a [4,5,7,6,2] 30 (by decide) (fin9_cases _
  node1059
  node1060
  (invalid_upper a [4,5,7,6,2,2] 30 (by decide +kernel))
  node1061
  (invalid_upper a [4,5,7,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,2,7] 30 (by decide +kernel))
  node1062)

def cert1064 : Leaf := ⟨⟨300,280,274,0,327,0,286,30,14⟩,[(3,5),(5,3)],[(5,1,0),(6,3,4),(0,5,4)],⟨19,38,140,73,56,97,454,390,278⟩,⟨19,38,140,73,56,97,192,384,272⟩,[⟨7,1237261172844992513707015,⟨275,319,319,121,56,121,64,256,272⟩⟩]⟩
theorem node1064 : UpperPrefix a [4,5,7,6,3,0] 30 :=
  Boolean.leaf_sound a [4,5,7,6,3,0] 30 cert1064 (by decide +kernel)

def cert1065 : Leaf := ⟨⟨40,153,17,16,67,157,285,29,13⟩,[],[(5,1,0),(6,3,4)],⟨19,38,140,73,56,98,453,389,277⟩,⟨19,38,140,73,56,98,192,384,272⟩,[⟨8,1181748210069345983615,⟨19,63,191,127,59,127,255,128,17⟩⟩,⟨1,1214913104244639750422529,⟨477,36,204,461,252,96,192,384,276⟩⟩,⟨7,1218371706631214322418723,⟨275,319,12,73,57,379,64,256,272⟩⟩,⟨2,1210107565286192442246179,⟨19,59,136,73,57,123,192,384,272⟩⟩]⟩
theorem node1065 : UpperPrefix a [4,5,7,6,3,1] 30 :=
  Boolean.leaf_sound a [4,5,7,6,3,1] 30 cert1065 (by decide +kernel)

def cert1066 : Leaf := ⟨⟨40,0,19,18,67,155,283,27,11⟩,[(1,5)],[(5,1,0),(7,2,5),(6,3,4),(2,5,1)],⟨19,38,140,73,56,100,451,387,275⟩,⟨19,38,140,73,56,100,192,384,272⟩,[⟨8,1181748210069345983615,⟨19,63,191,127,59,127,255,128,17⟩⟩]⟩
theorem node1066 : UpperPrefix a [4,5,7,6,3,2] 30 :=
  Boolean.leaf_sound a [4,5,7,6,3,2] 30 cert1066 (by decide +kernel)

def cert1067 : Leaf := ⟨⟨172,136,2,0,198,158,286,14,142⟩,[(3,6)],[(5,1,0),(6,3,4),(0,6,3)],⟨19,38,140,73,56,352,193,390,278⟩,⟨19,38,140,73,56,352,193,384,272⟩,[⟨8,1181745671571875316787,⟨19,63,140,77,59,127,205,128,17⟩⟩,⟨4,1212763896429374969242625,⟨7,166,140,77,174,494,205,384,390⟩⟩]⟩
theorem node1067 : UpperPrefix a [4,5,7,6,3,8,0] 30 :=
  Boolean.leaf_sound a [4,5,7,6,3,8,0] 30 cert1067 (by decide +kernel)

def cert1068 : Leaf := ⟨⟨40,153,17,18,65,29,285,29,13⟩,[],[(5,1,0),(6,3,4),(1,6,3)],⟨19,38,140,73,56,352,194,389,277⟩,⟨19,38,140,73,56,352,194,384,272⟩,[⟨7,1218371708887970528363587,⟨275,319,28,121,56,377,379,256,272⟩⟩,⟨8,1181745671571875316851,⟨19,63,140,77,59,127,223,128,17⟩⟩,⟨2,1210107565286201032180803,⟨19,59,136,73,56,377,219,384,272⟩⟩]⟩
theorem node1068 : UpperPrefix a [4,5,7,6,3,8,1] 30 :=
  Boolean.leaf_sound a [4,5,7,6,3,8,1] 30 cert1068 (by decide +kernel)

def cert1069 : Leaf := ⟨⟨296,281,275,278,323,27,0,27,11⟩,[(6,2)],[(5,1,0),(7,2,6),(6,3,4)],⟨19,38,140,73,56,352,196,387,275⟩,⟨19,38,140,73,56,352,196,384,272⟩,[⟨2,1224302335130870795469827,⟨403,435,184,505,56,352,208,384,272⟩⟩]⟩
theorem node1069 : UpperPrefix a [4,5,7,6,3,8,2] 30 :=
  Boolean.leaf_sound a [4,5,7,6,3,8,2] 30 cert1069 (by decide +kernel)

theorem node1070 : UpperPrefix a [4,5,7,6,3,8] 30 :=
  branch_upper a [4,5,7,6,3,8] 30 (by decide) (fin9_cases _
  node1067
  node1068
  node1069
  (invalid_upper a [4,5,7,6,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,8,8] 30 (by decide +kernel)))

theorem node1071 : UpperPrefix a [4,5,7,6,3] 30 :=
  branch_upper a [4,5,7,6,3] 30 (by decide) (fin9_cases _
  node1064
  node1065
  node1066
  (invalid_upper a [4,5,7,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,3,7] 30 (by decide +kernel))
  node1070)

def cert1072 : Leaf := ⟨⟨364,65,323,0,79,0,15,79,79⟩,[(3,5),(5,3)],[(5,1,0)],⟨19,38,140,73,304,97,206,398,286⟩,⟨19,38,140,73,304,97,192,384,272⟩,[⟨4,1210255517854374332497409,⟨239,110,238,111,494,111,192,384,454⟩⟩,⟨7,1237261172842243734637575,⟨275,319,319,105,312,105,64,256,272⟩⟩,⟨8,1181818008295821020161,⟨19,110,238,105,56,105,192,128,16⟩⟩,⟨3,1210107565565325589089281,⟨19,38,166,97,304,97,192,384,272⟩⟩]⟩
theorem node1072 : UpperPrefix a [4,5,7,6,8,0] 30 :=
  Boolean.leaf_sound a [4,5,7,6,8,0] 30 cert1072 (by decide +kernel)

def cert1073 : Leaf := ⟨⟨236,200,64,0,204,140,284,92,204⟩,[(3,6)],[(5,1,0),(0,6,3)],⟨19,38,140,73,304,98,193,396,284⟩,⟨19,38,140,73,304,98,193,384,272⟩,[⟨1,1366914275414351528853505,⟨477,436,204,461,436,508,461,384,272⟩⟩,⟨8,1181748202505908575249,⟨19,38,174,111,51,110,239,128,17⟩⟩,⟨4,1210107567816035571653633,⟨3,38,174,111,290,110,239,384,256⟩⟩]⟩
theorem node1073 : UpperPrefix a [4,5,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [4,5,7,6,8,1,0] 30 cert1073 (by decide +kernel)

def cert1074 : Leaf := ⟨⟨360,344,337,272,75,284,0,89,73⟩,[(6,2)],[(5,1,0),(7,2,6),(2,6,5)],⟨19,38,140,73,304,98,196,393,281⟩,⟨19,38,140,73,304,98,196,384,272⟩,[⟨1,1214913176302233784156161,⟨477,100,204,461,304,96,196,384,272⟩⟩,⟨0,1210107640085826747010048,⟨50,102,238,106,304,98,230,384,272⟩⟩]⟩
theorem node1074 : UpperPrefix a [4,5,7,6,8,1,2] 30 :=
  Boolean.leaf_sound a [4,5,7,6,8,1,2] 30 cert1074 (by decide +kernel)

def cert1075 : Leaf := ⟨⟨292,409,0,278,7,413,0,23,7⟩,[(2,6),(6,2)],[(5,1,0)],⟨19,38,140,73,304,98,200,389,277⟩,⟨19,38,140,73,304,98,200,384,272⟩,[⟨6,1370980467431504557917235,⟨403,439,140,13,435,439,140,384,273⟩⟩,⟨3,1219570744996000074564643,⟨403,439,132,65,305,499,192,384,272⟩⟩,⟨7,1218371706631214322418723,⟨275,319,12,73,313,379,72,256,272⟩⟩]⟩
theorem node1075 : UpperPrefix a [4,5,7,6,8,1,3] 30 :=
  Boolean.leaf_sound a [4,5,7,6,8,1,3] 30 cert1075 (by decide +kernel)

theorem node1076 : UpperPrefix a [4,5,7,6,8,1] 30 :=
  branch_upper a [4,5,7,6,8,1] 30 (by decide) (fin9_cases _
  node1073
  (invalid_upper a [4,5,7,6,8,1,1] 30 (by decide +kernel))
  node1074
  node1075
  (invalid_upper a [4,5,7,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,1,8] 30 (by decide +kernel)))

def cert1077 : Local := ⟨⟨360,0,338,0,74,410,282,90,74⟩,[(1,5),(3,6)],[(5,1,0),(7,2,5),(2,5,1),(0,6,3)]⟩
theorem node1077 : UpperPrefix a [4,5,7,6,8,2,0] 30 :=
  local_sound a [4,5,7,6,8,2,0] 30 cert1077 (by decide +kernel)

def cert1078 : Local := ⟨⟨360,0,337,274,73,409,281,89,73⟩,[(1,5)],[(5,1,0),(7,2,5),(2,5,1),(1,6,3)]⟩
theorem node1078 : UpperPrefix a [4,5,7,6,8,2,1] 30 :=
  local_sound a [4,5,7,6,8,2,1] 30 cert1078 (by decide +kernel)

def cert1079 : Local := ⟨⟨352,0,0,274,67,411,0,83,67⟩,[(1,5),(2,6),(6,2)],[(5,1,0),(7,2,5),(2,5,1),(3,6,5)]⟩
theorem node1079 : UpperPrefix a [4,5,7,6,8,2,3] 30 :=
  local_sound a [4,5,7,6,8,2,3] 30 cert1079 (by decide +kernel)

theorem node1080 : UpperPrefix a [4,5,7,6,8,2] 30 :=
  branch_upper a [4,5,7,6,8,2] 30 (by decide) (fin9_cases _
  node1077
  node1078
  (invalid_upper a [4,5,7,6,8,2,2] 30 (by decide +kernel))
  node1079
  (invalid_upper a [4,5,7,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,2,8] 30 (by decide +kernel)))

def cert1081 : Leaf := ⟨⟨292,280,275,406,7,0,279,23,7⟩,[(5,3)],[(5,1,0),(6,3,5),(3,5,1)],⟨19,38,140,73,304,104,199,391,279⟩,⟨19,38,140,73,304,104,192,384,272⟩,[⟨7,1237261172842239439670279,⟨275,311,319,105,304,104,64,256,272⟩⟩,⟨0,1210107565565326662831104,⟨18,38,174,104,304,104,192,384,272⟩⟩]⟩
theorem node1081 : UpperPrefix a [4,5,7,6,8,3] 30 :=
  Boolean.leaf_sound a [4,5,7,6,8,3] 30 cert1081 (by decide +kernel)

theorem node1082 : UpperPrefix a [4,5,7,6,8] 30 :=
  branch_upper a [4,5,7,6,8] 30 (by decide) (fin9_cases _
  node1072
  node1076
  node1080
  node1081
  (invalid_upper a [4,5,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,8,8] 30 (by decide +kernel)))

theorem node1083 : UpperPrefix a [4,5,7,6] 30 :=
  branch_upper a [4,5,7,6] 30 (by decide) (fin9_cases _
  node1050
  node1058
  node1063
  node1071
  (invalid_upper a [4,5,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,6,7] 30 (by decide +kernel))
  node1082)

theorem node1084 : UpperPrefix a [4,5,7] 30 :=
  branch_upper a [4,5,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,5,7,1] [2,4,5,7] 30 (by decide +kernel) node173)
  (PrefixConjugacy.upper aut5 [4,5,7,2] [3,4,5,7] 30 (by decide +kernel) node596)
  (invalid_upper a [4,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,7,5] 30 (by decide +kernel))
  node1083
  (invalid_upper a [4,5,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut12 [4,5,7,8] [4,5,6,7] 30 (by decide +kernel) node1041))

def cert1085 : Leaf := ⟨⟨296,456,209,272,266,396,268,12,205⟩,[],[(5,1,0),(1,5,4)],⟨19,38,268,73,49,98,204,396,412⟩,⟨19,38,268,73,49,98,192,384,272⟩,[⟨0,1210144531040699375684608,⟨50,230,494,72,48,98,192,384,272⟩⟩,⟨4,1210144531039599864056833,⟨35,230,494,73,33,98,192,384,256⟩⟩,⟨2,1210107565286192442246179,⟨19,59,264,73,57,123,192,384,272⟩⟩,⟨6,1210143305852830960583715,⟨19,183,396,9,49,51,128,384,272⟩⟩,⟨7,1208926973665475031991331,⟨19,63,268,73,57,123,64,256,272⟩⟩]⟩
theorem node1085 : UpperPrefix a [4,5,8,6,0,1] 30 :=
  Boolean.leaf_sound a [4,5,8,6,0,1] 30 cert1085 (by decide +kernel)

def cert1086 : Leaf := ⟨⟨104,0,211,18,74,394,266,74,203⟩,[(1,5)],[(5,1,0),(2,5,1)],⟨19,38,268,73,49,100,202,394,410⟩,⟨19,38,268,73,49,100,192,384,272⟩,[⟨0,1210144531040699375700992,⟨50,230,494,72,50,230,192,384,272⟩⟩,⟨4,1210144531039599864073217,⟨35,230,494,73,35,230,192,384,256⟩⟩,⟨7,1208926973665475032007731,⟨19,63,268,73,59,127,64,256,273⟩⟩,⟨8,1181745671563268604979,⟨19,63,12,73,59,127,192,128,17⟩⟩]⟩
theorem node1086 : UpperPrefix a [4,5,8,6,0,2] 30 :=
  Boolean.leaf_sound a [4,5,8,6,0,2] 30 cert1086 (by decide +kernel)

def cert1087 : Leaf := ⟨⟨420,392,147,390,390,0,262,6,135⟩,[(5,3)],[(5,1,0),(6,3,5),(3,5,1)],⟨19,38,268,73,49,104,198,390,406⟩,⟨19,38,268,73,49,104,192,384,272⟩,[⟨4,1210144567314687621860353,⟨107,230,494,105,41,104,192,384,256⟩⟩,⟨0,1210144567280602627181568,⟨82,230,494,104,48,104,192,384,272⟩⟩]⟩
theorem node1087 : UpperPrefix a [4,5,8,6,0,3] 30 :=
  Boolean.leaf_sound a [4,5,8,6,0,3] 30 cert1087 (by decide +kernel)

#print axioms node1087
end Delivery.FiniteExclusion.Sharp4x5
