import RegularNineSharp2x7Base
import RegularNineSharp2x7C014
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert960 : Local := ⟨⟨296,300,35,0,0,0,303,47,43⟩,[(3,1),(4,5),(5,6)],[(4,1,3),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node960 : UpperPrefix a [2,4,8,1,6,7] 30 :=
  local_sound a [2,4,8,1,6,7] 30 cert960 (by decide +kernel)

theorem node961 : UpperPrefix a [2,4,8,1,6] 30 :=
  branch_upper a [2,4,8,1,6] 30 (by decide) (fin9_cases _
  node956
  (invalid_upper a [2,4,8,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,2] 30 (by decide +kernel))
  node959
  (invalid_upper a [2,4,8,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,6] 30 (by decide +kernel))
  node960
  (invalid_upper a [2,4,8,1,6,8] 30 (by decide +kernel)))

def cert962 : Leaf := ⟨⟨328,332,67,0,0,270,263,79,75⟩,[(3,1),(4,7)],[(4,1,3),(5,7,4)],⟨7,19,268,26,176,97,200,416,324⟩,⟨7,19,268,26,176,97,200,416,260⟩,[⟨7,1662274158270422465918047,⟨15,31,271,31,319,357,367,288,261⟩⟩]⟩
theorem node962 : UpperPrefix a [2,4,8,1,7,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,1,7,0,3,5] 30 cert962 (by decide +kernel)

def cert963 : Leaf := ⟨⟨424,424,163,0,329,392,289,41,169⟩,[(3,1)],[(4,1,3),(6,7,4)],⟨7,19,268,26,176,97,200,448,292⟩,⟨7,19,268,26,176,97,200,448,260⟩,[⟨1,1217532451868703372345345,⟨501,433,460,24,176,497,200,448,452⟩⟩,⟨2,1212506020421431306765825,⟨251,123,456,122,250,123,200,448,448⟩⟩]⟩
theorem node963 : UpperPrefix a [2,4,8,1,7,0,3,6] 30 :=
  Boolean.leaf_sound a [2,4,8,1,7,0,3,6] 30 cert963 (by decide +kernel)

theorem node964 : UpperPrefix a [2,4,8,1,7,0,3] 30 :=
  branch_upper a [2,4,8,1,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,1,7,0,3,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,3,4] 30 (by decide +kernel))
  node962
  node963
  (invalid_upper a [2,4,8,1,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,3,8] 30 (by decide +kernel)))

def cert965 : Leaf := ⟨⟨488,492,225,0,0,396,0,109,233⟩,[(3,1),(4,6),(6,4)],[(4,1,3)],⟨7,19,268,26,176,97,224,456,332⟩,⟨7,19,268,26,176,97,224,384,260⟩,[⟨1,1266887094013262063206401,⟨501,113,476,508,240,113,240,384,388⟩⟩]⟩
theorem node965 : UpperPrefix a [2,4,8,1,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,1,7,0,5] 30 cert965 (by decide +kernel)

theorem node966 : UpperPrefix a [2,4,8,1,7,0] 30 :=
  branch_upper a [2,4,8,1,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,1,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,2] 30 (by decide +kernel))
  node964
  (invalid_upper a [2,4,8,1,7,0,4] 30 (by decide +kernel))
  node965
  (invalid_upper a [2,4,8,1,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,0,8] 30 (by decide +kernel)))

def cert967 : Leaf := ⟨⟨360,360,96,0,328,387,302,108,104⟩,[(3,1)],[(4,1,3)],⟨7,19,268,26,176,104,193,480,356⟩,⟨7,19,268,26,176,104,193,384,260⟩,[⟨0,1361518440643058985862144,⟨14,26,268,26,436,508,192,384,260⟩⟩,⟨1,1361518440643058717425665,⟨5,17,268,24,436,508,193,384,260⟩⟩,⟨7,1360042701114965350167615,⟨15,31,271,31,319,367,65,256,261⟩⟩,⟨2,1210107567540062698636289,⟨11,27,264,26,184,122,251,384,256⟩⟩]⟩
theorem node967 : UpperPrefix a [2,4,8,1,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,1,7,3,0] 30 cert967 (by decide +kernel)

def cert968 : Leaf := ⟨⟨456,460,195,0,0,391,0,79,203⟩,[(3,1),(4,6),(6,4)],[(4,1,3)],⟨7,19,268,26,176,104,224,449,325⟩,⟨7,19,268,26,176,104,224,384,260⟩,[⟨5,1664340190228978206782527,⟨15,31,271,31,415,463,453,384,261⟩⟩]⟩
theorem node968 : UpperPrefix a [2,4,8,1,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,1,7,3,5] 30 cert968 (by decide +kernel)

theorem node969 : UpperPrefix a [2,4,8,1,7,3] 30 :=
  branch_upper a [2,4,8,1,7,3] 30 (by decide) (fin9_cases _
  node967
  (invalid_upper a [2,4,8,1,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,3,4] 30 (by decide +kernel))
  node968
  (invalid_upper a [2,4,8,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,3,8] 30 (by decide +kernel)))

theorem node970 : UpperPrefix a [2,4,8,1,7] 30 :=
  branch_upper a [2,4,8,1,7] 30 (by decide) (fin9_cases _
  node966
  (invalid_upper a [2,4,8,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,2] 30 (by decide +kernel))
  node969
  (invalid_upper a [2,4,8,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,7,8] 30 (by decide +kernel)))

theorem node971 : UpperPrefix a [2,4,8,1] 30 :=
  branch_upper a [2,4,8,1] 30 (by decide) (fin9_cases _
  node952
  (invalid_upper a [2,4,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,2] 30 (by decide +kernel))
  node955
  (invalid_upper a [2,4,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,5] 30 (by decide +kernel))
  node961
  node970
  (invalid_upper a [2,4,8,1,8] 30 (by decide +kernel)))

def cert972 : Leaf := ⟨⟨472,0,192,0,462,396,268,76,200⟩,[(1,4),(3,4)],[(5,3,3),(0,4,1),(1,5,4)],⟨7,19,268,56,49,98,200,456,460⟩,⟨7,19,268,56,49,98,192,384,260⟩,[⟨4,1266886859749596662334465,⟨487,35,460,492,33,98,192,384,452⟩⟩]⟩
theorem node972 : UpperPrefix a [2,4,8,5,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,5,0,1] 30 cert972 (by decide +kernel)

def cert973 : Leaf := ⟨⟨472,0,210,0,462,406,262,70,194⟩,[(1,4),(3,4)],[(5,3,3),(0,4,1)],⟨7,19,268,56,49,104,194,450,454⟩,⟨7,19,268,56,49,104,192,384,260⟩,[⟨3,1215005662224180254352385,⟨455,467,324,242,499,96,192,384,260⟩⟩,⟨4,1214857655924927912477697,⟨455,451,268,40,481,104,192,384,260⟩⟩]⟩
theorem node973 : UpperPrefix a [2,4,8,5,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,0,3] 30 cert973 (by decide +kernel)

def cert974 : Local := ⟨⟨344,0,82,0,334,0,286,94,90⟩,[(1,4),(3,4),(5,6)],[(5,3,3),(0,4,1),(7,5,5)]⟩
theorem node974 : UpperPrefix a [2,4,8,5,0,7] 30 :=
  local_sound a [2,4,8,5,0,7] 30 cert974 (by decide +kernel)

theorem node975 : UpperPrefix a [2,4,8,5,0] 30 :=
  branch_upper a [2,4,8,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,5,0,0] 30 (by decide +kernel))
  node972
  (invalid_upper a [2,4,8,5,0,2] 30 (by decide +kernel))
  node973
  (invalid_upper a [2,4,8,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,0,6] 30 (by decide +kernel))
  node974
  (invalid_upper a [2,4,8,5,0,8] 30 (by decide +kernel)))

def cert976 : Leaf := ⟨⟨472,456,192,0,457,392,264,72,200⟩,[(3,4)],[(5,3,3),(1,4,1),(0,5,4)],⟨7,19,268,56,50,97,200,456,460⟩,⟨7,19,268,56,50,97,192,384,260⟩,[⟨2,1210144548952506550470145,⟨251,123,472,58,58,123,192,384,448⟩⟩,⟨4,1266886859749596662334465,⟨487,35,460,492,34,97,192,384,452⟩⟩]⟩
theorem node976 : UpperPrefix a [2,4,8,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,5,1,0] 30 cert976 (by decide +kernel)

def cert977 : Leaf := ⟨⟨456,460,192,0,461,389,268,76,200⟩,[(3,4)],[(5,3,3),(1,4,1)],⟨7,19,268,56,50,104,193,448,452⟩,⟨7,19,268,56,50,104,193,384,260⟩,[⟨4,1499343775797453320619025,⟨487,451,492,493,487,492,449,384,420⟩⟩,⟨0,1361518440640861847946240,⟨6,30,268,444,446,492,192,384,260⟩⟩]⟩
theorem node977 : UpperPrefix a [2,4,8,5,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,5,1,3,0] 30 cert977 (by decide +kernel)

theorem node978 : UpperPrefix a [2,4,8,5,1,3] 30 :=
  branch_upper a [2,4,8,5,1,3] 30 (by decide) (fin9_cases _
  node977
  (invalid_upper a [2,4,8,5,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,3,8] 30 (by decide +kernel)))

def cert979 : Local := ⟨⟨344,332,81,0,333,0,285,93,89⟩,[(3,4),(5,6)],[(5,3,3),(1,4,1),(7,5,5)]⟩
theorem node979 : UpperPrefix a [2,4,8,5,1,7] 30 :=
  local_sound a [2,4,8,5,1,7] 30 cert979 (by decide +kernel)

theorem node980 : UpperPrefix a [2,4,8,5,1] 30 :=
  branch_upper a [2,4,8,5,1] 30 (by decide) (fin9_cases _
  node976
  (invalid_upper a [2,4,8,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,2] 30 (by decide +kernel))
  node978
  (invalid_upper a [2,4,8,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,1,6] 30 (by decide +kernel))
  node979
  (invalid_upper a [2,4,8,5,1,8] 30 (by decide +kernel)))

def cert981 : Leaf := ⟨⟨216,204,211,0,0,135,7,71,195⟩,[(3,4),(4,3)],[(5,3,3),(5,3,4)],⟨7,19,268,56,56,227,195,451,455⟩,⟨7,19,268,56,56,96,192,384,260⟩,[⟨3,1214857656031579466630145,⟨487,499,260,48,48,96,192,384,260⟩⟩,⟨4,1214857656030481028744193,⟨487,483,268,40,40,96,192,384,260⟩⟩,⟨8,1184056031806483401989,⟨7,27,31,56,56,120,250,251,7⟩⟩]⟩
theorem node981 : UpperPrefix a [2,4,8,5,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,3] 30 cert981 (by decide +kernel)

def cert982 : Leaf := ⟨⟨408,396,146,0,0,414,286,30,154⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,268,56,112,97,202,394,398⟩,⟨7,19,268,56,112,97,192,384,260⟩,[⟨0,1219570781024667171292160,⟨454,478,268,56,120,120,192,384,260⟩⟩]⟩
theorem node982 : UpperPrefix a [2,4,8,5,6,0] 30 :=
  Boolean.leaf_sound a [2,4,8,5,6,0] 30 cert982 (by decide +kernel)

def cert983 : Leaf := ⟨⟨408,396,145,0,0,413,285,29,153⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,268,56,112,98,201,393,397⟩,⟨7,19,268,56,112,98,192,384,260⟩,[⟨1,1219570781024667179679745,⟨453,477,268,60,124,508,192,384,260⟩⟩]⟩
theorem node983 : UpperPrefix a [2,4,8,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,8,5,6,1] 30 cert983 (by decide +kernel)

def cert984 : Leaf := ⟨⟨408,396,147,0,0,407,263,7,131⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,268,56,112,104,195,387,391⟩,⟨7,19,268,56,112,104,192,384,260⟩,[⟨3,1214857655928225373619201,⟨455,467,260,48,112,112,192,384,260⟩⟩,⟨4,1214857655924927912477697,⟨455,451,268,40,96,104,192,384,260⟩⟩]⟩
theorem node984 : UpperPrefix a [2,4,8,5,6,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,6,3] 30 cert984 (by decide +kernel)

def cert985 : Local := ⟨⟨280,268,19,0,0,0,287,31,27⟩,[(3,4),(4,5),(5,6)],[(5,3,3),(6,4,3),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node985 : UpperPrefix a [2,4,8,5,6,7] 30 :=
  local_sound a [2,4,8,5,6,7] 30 cert985 (by decide +kernel)

theorem node986 : UpperPrefix a [2,4,8,5,6] 30 :=
  branch_upper a [2,4,8,5,6] 30 (by decide) (fin9_cases _
  node982
  node983
  (invalid_upper a [2,4,8,5,6,2] 30 (by decide +kernel))
  node984
  (invalid_upper a [2,4,8,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,6,6] 30 (by decide +kernel))
  node985
  (invalid_upper a [2,4,8,5,6,8] 30 (by decide +kernel)))

def cert987 : Leaf := ⟨⟨472,448,208,0,320,402,272,92,216⟩,[(3,4)],[(5,3,3),(1,6,5)],⟨7,19,268,56,176,97,194,456,332⟩,⟨7,19,268,56,176,97,194,384,260⟩,[⟨0,1370981674396623450932224,⟨454,478,284,444,444,508,454,384,260⟩⟩,⟨2,1210107853589009928307713,⟨43,123,264,122,250,123,250,384,256⟩⟩,⟨3,1210107853588993554793473,⟨39,115,260,114,242,115,242,384,260⟩⟩]⟩
theorem node987 : UpperPrefix a [2,4,8,5,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,0,1] 30 cert987 (by decide +kernel)

def cert988 : Leaf := ⟨⟨344,332,80,0,332,284,276,92,88⟩,[(3,4)],[(5,3,3)],⟨7,19,268,56,176,97,200,386,324⟩,⟨7,19,268,56,176,97,200,386,260⟩,[⟨0,2395450123322374170870784,⟨454,478,268,380,508,508,460,454,260⟩⟩,⟨1,2390701780153832845344769,⟨301,381,268,380,508,357,476,508,260⟩⟩,⟨7,1662274158270422199579743,⟨7,31,271,319,319,357,367,259,261⟩⟩]⟩
theorem node988 : UpperPrefix a [2,4,8,5,7,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,0,3,1] 30 cert988 (by decide +kernel)

def cert989 : Leaf := ⟨⟨400,388,146,0,326,406,278,22,146⟩,[(3,4)],[(5,3,3),(6,7,4)],⟨7,19,268,56,176,97,200,448,262⟩,⟨7,19,268,56,176,97,200,448,260⟩,[⟨3,1234014550122920737328389,⟨263,275,279,178,178,499,242,499,263⟩⟩,⟨0,1226996676378795598939136,⟨454,478,476,252,252,508,216,448,452⟩⟩]⟩
theorem node989 : UpperPrefix a [2,4,8,5,7,0,3,6] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,0,3,6] 30 cert989 (by decide +kernel)

theorem node990 : UpperPrefix a [2,4,8,5,7,0,3] 30 :=
  branch_upper a [2,4,8,5,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,5,7,0,3,0] 30 (by decide +kernel))
  node988
  (invalid_upper a [2,4,8,5,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,3,5] 30 (by decide +kernel))
  node989
  (invalid_upper a [2,4,8,5,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,3,8] 30 (by decide +kernel)))

theorem node991 : UpperPrefix a [2,4,8,5,7,0] 30 :=
  branch_upper a [2,4,8,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,5,7,0,0] 30 (by decide +kernel))
  node987
  (invalid_upper a [2,4,8,5,7,0,2] 30 (by decide +kernel))
  node990
  (invalid_upper a [2,4,8,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,0,8] 30 (by decide +kernel)))

def cert992 : Leaf := ⟨⟨472,448,208,0,320,401,284,92,216⟩,[(3,4)],[(5,3,3),(0,6,5)],⟨7,19,268,56,176,98,193,456,332⟩,⟨7,19,268,56,176,98,193,384,260⟩,[⟨1,1370981674396623450931201,⟨453,477,284,444,444,508,193,384,260⟩⟩,⟨2,1210107567540064577684481,⟨3,27,264,56,184,122,251,384,256⟩⟩,⟨3,1210107567540048472605697,⟨7,19,260,48,176,114,243,384,260⟩⟩]⟩
theorem node992 : UpperPrefix a [2,4,8,5,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,1,0] 30 cert992 (by decide +kernel)

def cert993 : Leaf := ⟨⟨328,332,65,0,333,269,261,77,73⟩,[(3,4)],[(5,3,3)],⟨7,19,268,56,176,98,200,449,325⟩,⟨7,19,268,56,176,98,200,384,260⟩,[⟨4,1404102965541885178807329,⟨487,419,460,493,417,487,460,384,324⟩⟩,⟨1,1224303235570702134804481,⟨453,477,268,124,252,508,200,384,260⟩⟩,⟨7,1662274158270422199579775,⟨7,31,271,319,319,359,367,256,261⟩⟩]⟩
theorem node993 : UpperPrefix a [2,4,8,5,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,1,3] 30 cert993 (by decide +kernel)

theorem node994 : UpperPrefix a [2,4,8,5,7,1] 30 :=
  branch_upper a [2,4,8,5,7,1] 30 (by decide) (fin9_cases _
  node992
  (invalid_upper a [2,4,8,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,2] 30 (by decide +kernel))
  node993
  (invalid_upper a [2,4,8,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,1,8] 30 (by decide +kernel)))

def cert995 : Leaf := ⟨⟨344,332,83,0,328,400,263,71,67⟩,[(3,4)],[(5,3,3)],⟨7,19,268,56,176,104,195,451,327⟩,⟨7,19,268,56,176,104,192,384,260⟩,[⟨7,1360042701114965083829311,⟨7,31,271,319,319,367,64,256,261⟩⟩,⟨3,1214857655926026350363649,⟨455,467,260,48,176,96,192,384,260⟩⟩,⟨4,1214857655924927912477697,⟨455,451,268,40,160,104,192,384,260⟩⟩,⟨0,1210107567540064578700288,⟨6,26,268,56,184,120,248,384,260⟩⟩,⟨1,1210107567540064578699265,⟨5,25,268,56,184,120,248,384,260⟩⟩,⟨2,1210107567540064577651713,⟨3,27,264,56,184,120,248,384,256⟩⟩]⟩
theorem node995 : UpperPrefix a [2,4,8,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,8,5,7,3] 30 cert995 (by decide +kernel)

theorem node996 : UpperPrefix a [2,4,8,5,7] 30 :=
  branch_upper a [2,4,8,5,7] 30 (by decide) (fin9_cases _
  node991
  node994
  (invalid_upper a [2,4,8,5,7,2] 30 (by decide +kernel))
  node995
  (invalid_upper a [2,4,8,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,7,8] 30 (by decide +kernel)))

theorem node997 : UpperPrefix a [2,4,8,5] 30 :=
  branch_upper a [2,4,8,5] 30 (by decide) (fin9_cases _
  node975
  node980
  (invalid_upper a [2,4,8,5,2] 30 (by decide +kernel))
  node981
  (invalid_upper a [2,4,8,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,5,5] 30 (by decide +kernel))
  node986
  node996
  (invalid_upper a [2,4,8,5,8] 30 (by decide +kernel)))

def cert998 : Leaf := ⟨⟨248,0,240,160,202,152,56,120,248⟩,[(1,4)],[(0,4,1),(1,5,4)],⟨7,19,268,88,49,98,232,424,428⟩,⟨7,19,268,88,49,98,192,384,260⟩,[⟨2,1210144549794182701524481,⟨251,123,488,122,123,122,192,384,448⟩⟩,⟨8,1184058558202883813125,⟨23,19,63,122,51,106,250,251,23⟩⟩]⟩
theorem node998 : UpperPrefix a [2,4,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,1] 30 cert998 (by decide +kernel)

def cert999 : Leaf := ⟨⟨56,0,178,166,14,0,62,62,186⟩,[(1,4),(5,3)],[(6,3,5),(0,4,1)],⟨7,19,268,88,49,104,226,418,422⟩,⟨7,19,268,88,49,104,192,384,260⟩,[⟨8,1184058558202883813125,⟨23,19,63,122,51,104,250,251,23⟩⟩,⟨7,1208926973944884129574661,⟨23,19,319,122,51,104,64,259,279⟩⟩]⟩
theorem node999 : UpperPrefix a [2,4,8,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,3] 30 cert999 (by decide +kernel)

def cert1000 : Leaf := ⟨⟨376,0,98,294,334,0,300,110,106⟩,[(1,4),(5,6)],[(0,4,1),(7,5,5)],⟨7,19,268,88,49,224,194,424,300⟩,⟨7,19,268,88,49,224,194,384,260⟩,[⟨4,1266886664124487848428545,⟨487,99,428,492,97,224,226,384,388⟩⟩]⟩
theorem node1000 : UpperPrefix a [2,4,8,6,0,7,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,7,1] 30 cert1000 (by decide +kernel)

def cert1001 : Leaf := ⟨⟨344,0,82,262,334,0,278,92,122⟩,[(1,4),(5,6)],[(0,4,1),(7,5,5)],⟨7,19,268,88,49,224,200,386,292⟩,⟨7,19,268,88,49,224,200,386,260⟩,[⟨5,1210146853561103408968901,⟨207,91,463,91,91,197,207,463,453⟩⟩]⟩
theorem node1001 : UpperPrefix a [2,4,8,6,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,7,3,1] 30 cert1001 (by decide +kernel)

def cert1002 : Leaf := ⟨⟨312,0,50,294,270,0,310,30,58⟩,[(1,4),(5,6)],[(0,4,1),(7,5,5)],⟨7,19,268,88,49,224,200,416,262⟩,⟨7,19,268,88,49,224,200,416,260⟩,[⟨6,1725287080863902572082285,⟨263,403,271,415,435,439,415,435,261⟩⟩]⟩
theorem node1002 : UpperPrefix a [2,4,8,6,0,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,7,3,5] 30 cert1002 (by decide +kernel)

theorem node1003 : UpperPrefix a [2,4,8,6,0,7,3] 30 :=
  branch_upper a [2,4,8,6,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,0,7,3,0] 30 (by decide +kernel))
  node1001
  (invalid_upper a [2,4,8,6,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,3,4] 30 (by decide +kernel))
  node1002
  (invalid_upper a [2,4,8,6,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,3,8] 30 (by decide +kernel)))

def cert1004 : Local := ⟨⟨344,0,82,294,334,0,0,94,90⟩,[(1,4),(5,6),(6,5)],[(0,4,1),(7,5,5),(7,5,6),(5,6,3)]⟩
theorem node1004 : UpperPrefix a [2,4,8,6,0,7,5] 30 :=
  local_sound a [2,4,8,6,0,7,5] 30 cert1004 (by decide +kernel)

theorem node1005 : UpperPrefix a [2,4,8,6,0,7] 30 :=
  branch_upper a [2,4,8,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,0,7,0] 30 (by decide +kernel))
  node1000
  (invalid_upper a [2,4,8,6,0,7,2] 30 (by decide +kernel))
  node1003
  (invalid_upper a [2,4,8,6,0,7,4] 30 (by decide +kernel))
  node1004
  (invalid_upper a [2,4,8,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,8] 30 (by decide +kernel)))

theorem node1006 : UpperPrefix a [2,4,8,6,0] 30 :=
  branch_upper a [2,4,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,0,0] 30 (by decide +kernel))
  node998
  (invalid_upper a [2,4,8,6,0,2] 30 (by decide +kernel))
  node999
  (invalid_upper a [2,4,8,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,6] 30 (by decide +kernel))
  node1005
  (invalid_upper a [2,4,8,6,0,8] 30 (by decide +kernel)))

def cert1007 : Leaf := ⟨⟨312,296,48,288,265,284,304,28,184⟩,[],[(1,4,1),(0,5,4)],⟨7,19,268,88,50,97,200,416,388⟩,⟨7,19,268,88,50,97,200,416,260⟩,[⟨6,1701675248449554346013805,⟨7,147,271,415,435,439,415,435,261⟩⟩,⟨7,1208926976212639780429765,⟨23,19,319,123,58,123,127,319,279⟩⟩,⟨2,1210109871137886079828993,⟨3,19,264,88,58,123,216,506,256⟩⟩]⟩
theorem node1007 : UpperPrefix a [2,4,8,6,1,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,0,3,5] 30 cert1007 (by decide +kernel)

theorem node1008 : UpperPrefix a [2,4,8,6,1,0,3] 30 :=
  branch_upper a [2,4,8,6,1,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,1,0,3,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,3,4] 30 (by decide +kernel))
  node1007
  (invalid_upper a [2,4,8,6,1,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,3,8] 30 (by decide +kernel)))

def cert1009 : Leaf := ⟨⟨408,392,144,416,393,408,280,24,152⟩,[],[(1,4,1),(0,5,4),(5,6,3)],⟨7,19,268,88,50,97,224,392,396⟩,⟨7,19,268,88,50,97,224,384,260⟩,[⟨2,1210144476898767245690369,⟨251,123,392,88,58,123,250,384,384⟩⟩,⟨6,1266885490627822151029773,⟨391,19,399,415,50,51,178,384,389⟩⟩]⟩
theorem node1009 : UpperPrefix a [2,4,8,6,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,0,5] 30 cert1009 (by decide +kernel)

theorem node1010 : UpperPrefix a [2,4,8,6,1,0] 30 :=
  branch_upper a [2,4,8,6,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,2] 30 (by decide +kernel))
  node1008
  (invalid_upper a [2,4,8,6,1,0,4] 30 (by decide +kernel))
  node1009
  (invalid_upper a [2,4,8,6,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,0,8] 30 (by decide +kernel)))

def cert1011 : Leaf := ⟨⟨168,172,161,165,141,0,45,45,169⟩,[(5,3)],[(6,3,5),(1,4,1)],⟨7,19,268,88,50,104,225,417,421⟩,⟨7,19,268,88,50,104,192,384,260⟩,[⟨4,1328397762437589886829585,⟨487,451,492,493,487,492,192,384,292⟩⟩,⟨8,1184058562605225283333,⟨23,19,63,120,58,120,250,251,23⟩⟩]⟩
theorem node1011 : UpperPrefix a [2,4,8,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,3] 30 cert1011 (by decide +kernel)

def cert1012 : Leaf := ⟨⟨112,100,113,37,69,0,52,125,121⟩,[(5,6)],[(1,4,1),(7,5,5)],⟨7,19,268,88,50,224,193,424,300⟩,⟨7,19,268,88,50,224,193,384,260⟩,[⟨8,1184058283604149636357,⟨7,19,31,122,58,250,251,251,7⟩⟩,⟨3,1210109877898202185829637,⟨7,19,279,114,50,242,243,499,263⟩⟩]⟩
theorem node1012 : UpperPrefix a [2,4,8,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,7,0] 30 cert1012 (by decide +kernel)

def cert1013 : Leaf := ⟨⟨376,104,113,33,73,0,49,124,121⟩,[(5,6)],[(2,0,7),(1,4,1),(7,5,5)],⟨7,19,268,88,50,224,200,385,292⟩,⟨7,19,268,88,50,224,200,385,260⟩,[⟨8,1184634743808844694529,⟨7,27,12,120,122,250,250,251,4⟩⟩]⟩
theorem node1013 : UpperPrefix a [2,4,8,6,1,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,7,3,0] 30 cert1013 (by decide +kernel)

def cert1014 : Leaf := ⟨⟨312,296,49,289,265,0,305,25,57⟩,[(5,6)],[(1,4,1),(7,5,5)],⟨7,19,268,88,50,224,200,416,261⟩,⟨7,19,268,88,50,224,200,416,260⟩,[⟨6,1725287080863902572082285,⟨263,403,271,415,435,439,415,435,261⟩⟩,⟨2,1212505743520553964144129,⟨251,123,488,120,58,224,232,416,480⟩⟩]⟩
theorem node1014 : UpperPrefix a [2,4,8,6,1,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,7,3,5] 30 cert1014 (by decide +kernel)

theorem node1015 : UpperPrefix a [2,4,8,6,1,7,3] 30 :=
  branch_upper a [2,4,8,6,1,7,3] 30 (by decide) (fin9_cases _
  node1013
  (invalid_upper a [2,4,8,6,1,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,3,4] 30 (by decide +kernel))
  node1014
  (invalid_upper a [2,4,8,6,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,3,8] 30 (by decide +kernel)))

def cert1016 : Local := ⟨⟨344,332,81,293,333,0,0,93,89⟩,[(5,6),(6,5)],[(1,4,1),(7,5,5),(7,5,6),(5,6,3)]⟩
theorem node1016 : UpperPrefix a [2,4,8,6,1,7,5] 30 :=
  local_sound a [2,4,8,6,1,7,5] 30 cert1016 (by decide +kernel)

theorem node1017 : UpperPrefix a [2,4,8,6,1,7] 30 :=
  branch_upper a [2,4,8,6,1,7] 30 (by decide) (fin9_cases _
  node1012
  (invalid_upper a [2,4,8,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,2] 30 (by decide +kernel))
  node1015
  (invalid_upper a [2,4,8,6,1,7,4] 30 (by decide +kernel))
  node1016
  (invalid_upper a [2,4,8,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,8] 30 (by decide +kernel)))

theorem node1018 : UpperPrefix a [2,4,8,6,1] 30 :=
  branch_upper a [2,4,8,6,1] 30 (by decide) (fin9_cases _
  node1010
  (invalid_upper a [2,4,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,2] 30 (by decide +kernel))
  node1011
  (invalid_upper a [2,4,8,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,6] 30 (by decide +kernel))
  node1017
  (invalid_upper a [2,4,8,6,1,8] 30 (by decide +kernel)))

def cert1019 : Leaf := ⟨⟨424,428,160,420,452,390,292,36,160⟩,[],[(6,3,4),(1,6,5)],⟨7,19,268,88,56,97,194,416,420⟩,⟨7,19,268,88,56,97,194,384,260⟩,[⟨0,1437223914350364306441216,⟨78,478,268,476,444,508,206,384,260⟩⟩,⟨4,1338745991481314197373955,⟨487,487,396,492,428,481,483,384,260⟩⟩,⟨3,1215152803936758819456001,⟨487,499,260,80,176,481,226,384,260⟩⟩]⟩
theorem node1019 : UpperPrefix a [2,4,8,6,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,0,1] 30 cert1019 (by decide +kernel)

def cert1020 : Leaf := ⟨⟨408,392,146,418,450,390,262,6,130⟩,[],[(6,3,4),(5,6,3)],⟨7,19,268,88,56,97,224,386,390⟩,⟨7,19,268,88,56,97,224,384,260⟩,[⟨0,1224302911315935600575488,⟨390,414,268,88,124,508,252,384,260⟩⟩,⟨3,1214858232492331770053633,⟨487,499,260,80,112,481,224,384,260⟩⟩,⟨4,1214858232491233332167681,⟨487,483,268,72,104,481,224,384,260⟩⟩,⟨2,1210107565290461639754753,⟨3,19,264,88,58,123,250,384,256⟩⟩]⟩
theorem node1020 : UpperPrefix a [2,4,8,6,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,0,5] 30 cert1020 (by decide +kernel)

theorem node1021 : UpperPrefix a [2,4,8,6,3,0] 30 :=
  branch_upper a [2,4,8,6,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,3,0,0] 30 (by decide +kernel))
  node1019
  (invalid_upper a [2,4,8,6,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,4] 30 (by decide +kernel))
  node1020
  (invalid_upper a [2,4,8,6,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,8] 30 (by decide +kernel)))

def cert1022 : Leaf := ⟨⟨184,172,179,32,64,133,39,39,163⟩,[],[(6,3,4)],⟨7,19,268,88,56,98,225,417,421⟩,⟨7,19,268,88,56,98,192,384,260⟩,[⟨8,1184058283604149603589,⟨7,19,31,120,56,122,250,251,7⟩⟩,⟨3,1214857656031579466630145,⟨487,499,260,80,48,226,192,384,260⟩⟩,⟨4,1214857656030481028744193,⟨487,483,268,72,40,226,192,384,260⟩⟩,⟨0,1210107565286055004341248,⟨6,18,268,88,56,122,192,384,260⟩⟩,⟨1,1210107565286055004340225,⟨5,17,268,88,56,120,192,384,260⟩⟩,⟨2,1210107565286055003292673,⟨3,19,264,88,56,122,192,384,256⟩⟩,⟨7,1208926973665337593037825,⟨7,19,268,88,56,122,64,256,260⟩⟩]⟩
theorem node1022 : UpperPrefix a [2,4,8,6,3,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,1] 30 cert1022 (by decide +kernel)

def cert1023 : Leaf := ⟨⟨56,44,51,39,71,0,39,39,35⟩,[(5,6)],[(6,3,4),(7,5,5)],⟨7,19,268,88,56,224,227,419,295⟩,⟨7,19,268,88,56,224,192,384,260⟩,[⟨8,1184058283604149603589,⟨7,19,31,120,56,250,250,251,7⟩⟩,⟨3,1214857658283379280315393,⟨487,499,260,112,48,224,224,384,260⟩⟩,⟨4,1214857658282280842429441,⟨487,483,268,104,40,224,224,384,260⟩⟩]⟩
theorem node1023 : UpperPrefix a [2,4,8,6,3,7] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,7] 30 cert1023 (by decide +kernel)

#print axioms node1023
end Delivery.FiniteExclusion.Sharp2x7
