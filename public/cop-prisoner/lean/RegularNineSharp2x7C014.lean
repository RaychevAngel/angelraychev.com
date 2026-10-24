import RegularNineSharp2x7Base
import RegularNineSharp2x7C012
import RegularNineSharp2x7C013
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert896 : Leaf := ⟨⟨248,0,352,228,202,146,56,104,232⟩,[(1,4)],[(8,3,2),(0,4,1)],⟨7,19,140,280,49,104,194,480,356⟩,⟨7,19,140,280,49,104,194,384,260⟩,[⟨1,1361518440640861845848065,⟨5,29,140,284,445,492,192,384,260⟩⟩,⟨2,1210181496797615783683585,⟨51,19,232,506,51,232,194,384,288⟩⟩,⟨4,1361518440639760182543361,⟨7,3,140,264,421,492,194,384,260⟩⟩]⟩
theorem node896 : UpperPrefix a [2,4,7,8,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,8,0,3,1] 30 cert896 (by decide +kernel)

def cert897 : Leaf := ⟨⟨216,0,338,198,202,130,10,74,202⟩,[(1,4)],[(8,3,2),(0,4,1)],⟨7,19,140,280,49,104,224,450,326⟩,⟨7,19,140,280,49,104,224,384,260⟩,[⟨5,1361518439514961939018815,⟨7,31,143,287,415,463,453,384,261⟩⟩,⟨2,1210182145315962125035009,⟨115,19,232,506,115,232,224,384,352⟩⟩,⟨4,1214857980606313548219393,⟨487,451,236,360,481,104,224,384,356⟩⟩]⟩
theorem node897 : UpperPrefix a [2,4,7,8,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,0,3,5] 30 cert897 (by decide +kernel)

theorem node898 : UpperPrefix a [2,4,7,8,0,3] 30 :=
  branch_upper a [2,4,7,8,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,0,3,0] 30 (by decide +kernel))
  node896
  (invalid_upper a [2,4,7,8,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,4] 30 (by decide +kernel))
  node897
  (invalid_upper a [2,4,7,8,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,3,8] 30 (by decide +kernel)))

theorem node899 : UpperPrefix a [2,4,7,8,0] 30 :=
  branch_upper a [2,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,0,0] 30 (by decide +kernel))
  node895
  (invalid_upper a [2,4,7,8,0,2] 30 (by decide +kernel))
  node898
  (invalid_upper a [2,4,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,8] 30 (by decide +kernel)))

def cert900 : Leaf := ⟨⟨248,232,0,228,201,152,0,124,248⟩,[(2,6),(6,2)],[(8,3,2),(8,3,6),(1,4,1),(0,5,4)],⟨7,19,140,280,50,97,200,480,356⟩,⟨7,19,140,280,50,97,200,384,260⟩,[⟨2,1210107637379035276789249,⟨115,51,200,280,50,115,200,384,320⟩⟩]⟩
theorem node900 : UpperPrefix a [2,4,7,8,1,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,8,1,0,3] 30 cert900 (by decide +kernel)

def cert901 : Leaf := ⟨⟨240,32,368,228,1,148,20,124,248⟩,[],[(8,3,2),(1,4,1),(0,5,4)],⟨7,19,140,280,50,97,224,456,332⟩,⟨7,19,140,280,50,97,224,384,260⟩,[⟨3,1210109956905190747758341,⟨119,51,247,307,50,115,242,499,375⟩⟩,⟨2,1210107565290448754852865,⟨3,19,136,280,50,115,242,384,256⟩⟩,⟨6,1210106412368944149054465,⟨7,19,140,280,50,51,178,384,260⟩⟩,⟨7,1208926973669731344598017,⟨7,19,12,280,50,115,114,256,260⟩⟩]⟩
theorem node901 : UpperPrefix a [2,4,7,8,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,1,0,5] 30 cert901 (by decide +kernel)

theorem node902 : UpperPrefix a [2,4,7,8,1,0] 30 :=
  branch_upper a [2,4,7,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,2] 30 (by decide +kernel))
  node900
  (invalid_upper a [2,4,7,8,1,0,4] 30 (by decide +kernel))
  node901
  (invalid_upper a [2,4,7,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,0,8] 30 (by decide +kernel)))

def cert903 : Leaf := ⟨⟨160,164,289,165,133,133,36,77,225⟩,[],[(8,3,2),(1,4,1)],⟨7,19,140,280,50,104,193,416,324⟩,⟨7,19,140,280,50,104,193,416,260⟩,[⟨4,1501096216484455728022545,⟨487,451,492,493,487,492,449,420,420⟩⟩,⟨3,1233721775609797206449413,⟨327,275,471,275,50,114,467,499,327⟩⟩,⟨6,1210106412373359425879525,⟨7,19,159,283,51,63,159,447,263⟩⟩]⟩
theorem node903 : UpperPrefix a [2,4,7,8,1,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,1,3,0,5] 30 cert903 (by decide +kernel)

def cert904 : Leaf := ⟨⟨72,76,321,101,77,5,12,13,105⟩,[],[(8,3,2),(1,4,1)],⟨7,19,140,280,50,104,193,448,292⟩,⟨7,19,140,280,50,104,193,448,260⟩,[⟨4,1499343775797453320619025,⟨487,451,492,493,487,492,449,448,420⟩⟩,⟨7,1227816446365732548353797,⟨287,27,319,283,50,122,123,379,287⟩⟩,⟨5,1212547938695234295182397,⟨71,19,207,479,87,207,193,448,453⟩⟩]⟩
theorem node904 : UpperPrefix a [2,4,7,8,1,3,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,8,1,3,0,6] 30 cert904 (by decide +kernel)

theorem node905 : UpperPrefix a [2,4,7,8,1,3,0] 30 :=
  branch_upper a [2,4,7,8,1,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,1,3,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,0,4] 30 (by decide +kernel))
  node903
  node904
  (invalid_upper a [2,4,7,8,1,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,0,8] 30 (by decide +kernel)))

def cert906 : Leaf := ⟨⟨200,200,321,197,201,129,9,77,201⟩,[],[(8,3,2),(1,4,1)],⟨7,19,140,280,50,104,224,449,325⟩,⟨7,19,140,280,50,104,224,384,260⟩,[⟨4,1328416857700009937732625,⟨487,451,492,493,487,492,228,384,356⟩⟩,⟨5,1664340190228977938347071,⟨7,31,143,287,415,463,453,384,261⟩⟩,⟨2,1210107637482251930830337,⟨115,19,232,280,50,104,224,384,352⟩⟩]⟩
theorem node906 : UpperPrefix a [2,4,7,8,1,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,1,3,5] 30 cert906 (by decide +kernel)

theorem node907 : UpperPrefix a [2,4,7,8,1,3] 30 :=
  branch_upper a [2,4,7,8,1,3] 30 (by decide) (fin9_cases _
  node905
  (invalid_upper a [2,4,7,8,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,4] 30 (by decide +kernel))
  node906
  (invalid_upper a [2,4,7,8,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,3,8] 30 (by decide +kernel)))

theorem node908 : UpperPrefix a [2,4,7,8,1] 30 :=
  branch_upper a [2,4,7,8,1] 30 (by decide) (fin9_cases _
  node902
  (invalid_upper a [2,4,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,2] 30 (by decide +kernel))
  node907
  (invalid_upper a [2,4,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,1,8] 30 (by decide +kernel)))

def cert909 : Leaf := ⟨⟨168,172,288,164,132,142,44,76,232⟩,[],[(8,3,2),(1,6,5)],⟨7,19,140,280,56,97,194,416,324⟩,⟨7,19,140,280,56,97,194,416,260⟩,[⟨0,1678064604985540272980992,⟨334,478,156,412,444,508,478,444,260⟩⟩,⟨4,1225187834963558195528707,⟨487,487,140,268,172,481,483,416,260⟩⟩,⟨6,1210106412371160402607589,⟨7,19,159,283,59,39,159,447,263⟩⟩]⟩
theorem node909 : UpperPrefix a [2,4,7,8,3,0,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,0,1,5] 30 cert909 (by decide +kernel)

def cert910 : Leaf := ⟨⟨232,232,352,224,192,138,40,40,232⟩,[],[(8,3,2),(1,6,5)],⟨7,19,140,280,56,97,194,448,292⟩,⟨7,19,140,280,56,97,194,448,260⟩,[⟨0,1437094805156249011487744,⟨206,478,140,284,444,508,206,452,260⟩⟩,⟨2,1210181640565306645562369,⟨35,115,136,472,250,115,250,472,256⟩⟩,⟨4,1300745698689472518947843,⟨487,487,140,268,428,481,483,480,260⟩⟩]⟩
theorem node910 : UpperPrefix a [2,4,7,8,3,0,1,6] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,0,1,6] 30 cert910 (by decide +kernel)

theorem node911 : UpperPrefix a [2,4,7,8,3,0,1] 30 :=
  branch_upper a [2,4,7,8,3,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,3,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,1,4] 30 (by decide +kernel))
  node909
  node910
  (invalid_upper a [2,4,7,8,3,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,1,8] 30 (by decide +kernel)))

def cert912 : Leaf := ⟨⟨216,204,336,228,196,134,7,69,224⟩,[],[(8,3,2)],⟨7,19,140,280,56,97,224,386,324⟩,⟨7,19,140,280,56,97,224,386,260⟩,[⟨0,1663454747645949745562624,⟨6,26,140,280,312,380,508,386,260⟩⟩,⟨1,1663454747645949745561601,⟨5,25,140,280,312,381,508,384,260⟩⟩,⟨3,1233750004266819564602369,⟨487,499,452,272,112,481,224,482,260⟩⟩,⟨4,1233750004265721126716417,⟨487,483,460,264,104,481,224,482,260⟩⟩,⟨5,1210181351134246623786015,⟨7,23,143,415,159,65,192,387,261⟩⟩]⟩
theorem node912 : UpperPrefix a [2,4,7,8,3,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,0,5,1] 30 cert912 (by decide +kernel)

def cert913 : Leaf := ⟨⟨184,168,304,160,128,152,24,56,186⟩,[],[(8,3,2),(6,7,6)],⟨7,19,140,280,56,97,224,448,262⟩,⟨7,19,140,280,56,97,224,448,260⟩,[⟨0,1224662911055755856315392,⟨398,478,140,476,252,508,252,476,260⟩⟩,⟨1,1210181640565306703216641,⟨37,117,140,476,252,117,252,476,260⟩⟩,⟨2,1210181640565306645562369,⟨35,115,136,472,250,115,250,472,256⟩⟩]⟩
theorem node913 : UpperPrefix a [2,4,7,8,3,0,5,6] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,0,5,6] 30 cert913 (by decide +kernel)

theorem node914 : UpperPrefix a [2,4,7,8,3,0,5] 30 :=
  branch_upper a [2,4,7,8,3,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,3,0,5,0] 30 (by decide +kernel))
  node912
  (invalid_upper a [2,4,7,8,3,0,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,5] 30 (by decide +kernel))
  node913
  (invalid_upper a [2,4,7,8,3,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,5,8] 30 (by decide +kernel)))

theorem node915 : UpperPrefix a [2,4,7,8,3,0] 30 :=
  branch_upper a [2,4,7,8,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,3,0,0] 30 (by decide +kernel))
  node911
  (invalid_upper a [2,4,7,8,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,4] 30 (by decide +kernel))
  node914
  (invalid_upper a [2,4,7,8,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,0,8] 30 (by decide +kernel)))

def cert916 : Leaf := ⟨⟨168,172,288,164,132,141,44,76,232⟩,[],[(8,3,2),(0,6,5)],⟨7,19,140,280,56,98,193,416,324⟩,⟨7,19,140,280,56,98,193,416,260⟩,[⟨1,1678064604985540272979969,⟨333,477,156,412,444,508,477,444,260⟩⟩,⟨4,1300893846851014687196163,⟨487,487,140,396,492,483,481,480,260⟩⟩,⟨6,1210106412371160402607589,⟨7,19,159,283,59,39,159,447,263⟩⟩]⟩
theorem node916 : UpperPrefix a [2,4,7,8,3,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,1,0,5] 30 cert916 (by decide +kernel)

def cert917 : Leaf := ⟨⟨104,108,352,100,68,13,44,44,104⟩,[],[(8,3,2),(0,6,5)],⟨7,19,140,280,56,98,193,448,292⟩,⟨7,19,140,280,56,98,193,448,260⟩,[⟨1,1437094805156248994709505,⟨205,477,140,284,444,508,197,448,260⟩⟩,⟨4,1300893846851014687196163,⟨487,487,140,396,492,483,481,448,260⟩⟩,⟨7,1227816446363533525098245,⟨287,27,319,283,58,114,123,379,287⟩⟩]⟩
theorem node917 : UpperPrefix a [2,4,7,8,3,1,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,1,0,6] 30 cert917 (by decide +kernel)

theorem node918 : UpperPrefix a [2,4,7,8,3,1,0] 30 :=
  branch_upper a [2,4,7,8,3,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,3,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,4] 30 (by decide +kernel))
  node916
  node917
  (invalid_upper a [2,4,7,8,3,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,0,8] 30 (by decide +kernel)))

def cert919 : Leaf := ⟨⟨200,200,321,193,193,137,9,76,201⟩,[],[(2,0,7),(8,3,2)],⟨7,19,140,280,56,98,224,385,324⟩,⟨7,19,140,280,56,98,224,385,260⟩,[⟨1,1739031634576690359566337,⟨141,413,140,280,380,508,508,389,260⟩⟩,⟨4,1356826968955887411004419,⟨487,487,460,332,492,483,224,481,260⟩⟩,⟨5,1364691279495639976129599,⟨7,159,143,415,415,455,449,385,389⟩⟩]⟩
theorem node919 : UpperPrefix a [2,4,7,8,3,1,5,0] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,1,5,0] 30 cert919 (by decide +kernel)

def cert920 : Leaf := ⟨⟨168,172,288,164,132,140,12,44,169⟩,[],[(8,3,2),(6,7,6)],⟨7,19,140,280,56,98,224,448,261⟩,⟨7,19,140,280,56,98,224,448,260⟩,[⟨0,1210181640565306703217664,⟨38,118,140,476,252,118,252,476,260⟩⟩,⟨1,1224662911055755856314369,⟨397,477,140,476,252,508,252,476,260⟩⟩,⟨4,1224672188568822971630595,⟨487,487,140,460,236,483,224,448,260⟩⟩]⟩
theorem node920 : UpperPrefix a [2,4,7,8,3,1,5,6] 30 :=
  Boolean.leaf_sound a [2,4,7,8,3,1,5,6] 30 cert920 (by decide +kernel)

theorem node921 : UpperPrefix a [2,4,7,8,3,1,5] 30 :=
  branch_upper a [2,4,7,8,3,1,5] 30 (by decide) (fin9_cases _
  node919
  (invalid_upper a [2,4,7,8,3,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,5,5] 30 (by decide +kernel))
  node920
  (invalid_upper a [2,4,7,8,3,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,5,8] 30 (by decide +kernel)))

theorem node922 : UpperPrefix a [2,4,7,8,3,1] 30 :=
  branch_upper a [2,4,7,8,3,1] 30 (by decide) (fin9_cases _
  node918
  (invalid_upper a [2,4,7,8,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,4] 30 (by decide +kernel))
  node921
  (invalid_upper a [2,4,7,8,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,1,8] 30 (by decide +kernel)))

theorem node923 : UpperPrefix a [2,4,7,8,3] 30 :=
  branch_upper a [2,4,7,8,3] 30 (by decide) (fin9_cases _
  node915
  node922
  (invalid_upper a [2,4,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,3,8] 30 (by decide +kernel)))

def cert924 : Leaf := ⟨⟨176,164,304,164,0,150,52,60,184⟩,[(4,5)],[(8,3,2),(6,4,4),(1,6,5)],⟨7,19,140,280,112,97,194,424,300⟩,⟨7,19,140,280,112,97,194,384,260⟩,[⟨0,1437223914350366470702080,⟨78,478,140,412,508,508,206,384,260⟩⟩,⟨3,1210109956904503552990981,⟨119,51,247,307,114,115,242,499,375⟩⟩]⟩
theorem node924 : UpperPrefix a [2,4,7,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,0,1] 30 cert924 (by decide +kernel)

def cert925 : Local := ⟨⟨184,172,0,167,0,158,0,63,187⟩,[(2,6),(4,5),(6,2)],[(8,3,2),(8,3,6),(6,4,4)]⟩
theorem node925 : UpperPrefix a [2,4,7,8,6,0,3] 30 :=
  local_sound a [2,4,7,8,6,0,3] 30 cert925 (by decide +kernel)

def cert926 : Leaf := ⟨⟨152,140,274,134,0,158,30,30,154⟩,[(4,5)],[(8,3,2),(6,4,4),(5,6,4)],⟨7,19,140,280,112,97,224,394,270⟩,⟨7,19,140,280,112,97,224,384,260⟩,[⟨0,1224302911315925148632064,⟨398,414,140,280,124,508,252,384,260⟩⟩]⟩
theorem node926 : UpperPrefix a [2,4,7,8,6,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,0,5] 30 cert926 (by decide +kernel)

theorem node927 : UpperPrefix a [2,4,7,8,6,0] 30 :=
  branch_upper a [2,4,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,6,0,0] 30 (by decide +kernel))
  node924
  (invalid_upper a [2,4,7,8,6,0,2] 30 (by decide +kernel))
  node925
  (invalid_upper a [2,4,7,8,6,0,4] 30 (by decide +kernel))
  node926
  (invalid_upper a [2,4,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,0,8] 30 (by decide +kernel)))

def cert928 : Leaf := ⟨⟨176,164,304,164,0,149,52,60,184⟩,[(4,5)],[(8,3,2),(6,4,4),(0,6,5)],⟨7,19,140,280,112,98,193,424,300⟩,⟨7,19,140,280,112,98,193,384,260⟩,[⟨1,1437223914350366453923841,⟨77,477,140,412,508,508,193,384,260⟩⟩,⟨3,1210109959719253320113925,⟨119,51,247,307,114,114,243,499,375⟩⟩]⟩
theorem node928 : UpperPrefix a [2,4,7,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,1,0] 30 cert928 (by decide +kernel)

def cert929 : Local := ⟨⟨184,172,0,167,0,157,0,63,187⟩,[(2,6),(4,5),(6,2)],[(8,3,2),(8,3,6),(6,4,4)]⟩
theorem node929 : UpperPrefix a [2,4,7,8,6,1,3] 30 :=
  local_sound a [2,4,7,8,6,1,3] 30 cert929 (by decide +kernel)

def cert930 : Leaf := ⟨⟨152,140,273,133,0,157,29,29,153⟩,[(4,5)],[(8,3,2),(6,4,4),(5,6,4)],⟨7,19,140,280,112,98,224,393,269⟩,⟨7,19,140,280,112,98,224,384,260⟩,[⟨1,1224302911315925148631041,⟨397,413,140,280,124,508,252,384,260⟩⟩]⟩
theorem node930 : UpperPrefix a [2,4,7,8,6,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,1,5] 30 cert930 (by decide +kernel)

theorem node931 : UpperPrefix a [2,4,7,8,6,1] 30 :=
  branch_upper a [2,4,7,8,6,1] 30 (by decide) (fin9_cases _
  node928
  (invalid_upper a [2,4,7,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,1,2] 30 (by decide +kernel))
  node929
  (invalid_upper a [2,4,7,8,6,1,4] 30 (by decide +kernel))
  node930
  (invalid_upper a [2,4,7,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,1,8] 30 (by decide +kernel)))

def cert932 : Leaf := ⟨⟨184,172,304,164,0,148,62,60,184⟩,[(4,5)],[(8,3,2),(6,4,4),(1,7,6)],⟨7,19,140,280,112,104,193,386,292⟩,⟨7,19,140,280,112,104,193,386,260⟩,[⟨0,1748485017268463993619456,⟨398,446,140,312,380,380,508,398,260⟩⟩]⟩
theorem node932 : UpperPrefix a [2,4,7,8,6,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,3,0,1] 30 cert932 (by decide +kernel)

def cert933 : Leaf := ⟨⟨176,164,306,166,0,150,54,30,178⟩,[(4,5)],[(8,3,2),(6,4,4)],⟨7,19,140,280,112,104,193,416,262⟩,⟨7,19,140,280,112,104,193,416,260⟩,[⟨0,1224957197084560816079872,⟨398,446,140,444,252,252,508,444,260⟩⟩,⟨3,1233721775609797206449413,⟨327,275,471,275,114,114,467,499,327⟩⟩]⟩
theorem node933 : UpperPrefix a [2,4,7,8,6,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,3,0,5] 30 cert933 (by decide +kernel)

theorem node934 : UpperPrefix a [2,4,7,8,6,3,0] 30 :=
  branch_upper a [2,4,7,8,6,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,6,3,0,0] 30 (by decide +kernel))
  node932
  (invalid_upper a [2,4,7,8,6,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,0,4] 30 (by decide +kernel))
  node933
  (invalid_upper a [2,4,7,8,6,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,0,8] 30 (by decide +kernel)))

def cert935 : Leaf := ⟨⟨184,168,304,160,0,144,57,60,184⟩,[(4,5)],[(2,0,7),(8,3,2),(6,4,4),(0,7,6)],⟨7,19,140,280,112,104,194,385,292⟩,⟨7,19,140,280,112,104,194,385,260⟩,[⟨1,1748485017268463960064001,⟨397,445,140,312,380,380,508,389,260⟩⟩]⟩
theorem node935 : UpperPrefix a [2,4,7,8,6,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,3,1,0] 30 cert935 (by decide +kernel)

def cert936 : Leaf := ⟨⟨152,140,273,133,0,149,29,29,153⟩,[(4,5)],[(8,3,2),(6,4,4)],⟨7,19,140,280,112,104,194,416,261⟩,⟨7,19,140,280,112,104,194,416,260⟩,[⟨5,1762624514711296739914869,⟨335,283,463,283,351,335,463,385,325⟩⟩,⟨1,1224957197084560816078849,⟨397,445,140,444,252,252,508,444,260⟩⟩]⟩
theorem node936 : UpperPrefix a [2,4,7,8,6,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,3,1,5] 30 cert936 (by decide +kernel)

theorem node937 : UpperPrefix a [2,4,7,8,6,3,1] 30 :=
  branch_upper a [2,4,7,8,6,3,1] 30 (by decide) (fin9_cases _
  node935
  (invalid_upper a [2,4,7,8,6,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,1,4] 30 (by decide +kernel))
  node936
  (invalid_upper a [2,4,7,8,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,1,8] 30 (by decide +kernel)))

def cert938 : Leaf := ⟨⟨152,140,274,134,0,150,30,31,155⟩,[(4,5)],[(8,3,2),(6,4,4),(5,6,4)],⟨7,19,140,280,112,104,224,387,263⟩,⟨7,19,140,280,112,104,224,384,260⟩,[⟨0,1210109959121171658048512,⟨118,18,252,312,116,124,252,508,380⟩⟩]⟩
theorem node938 : UpperPrefix a [2,4,7,8,6,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,6,3,5] 30 cert938 (by decide +kernel)

theorem node939 : UpperPrefix a [2,4,7,8,6,3] 30 :=
  branch_upper a [2,4,7,8,6,3] 30 (by decide) (fin9_cases _
  node934
  node937
  (invalid_upper a [2,4,7,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,4] 30 (by decide +kernel))
  node938
  (invalid_upper a [2,4,7,8,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,3,8] 30 (by decide +kernel)))

theorem node940 : UpperPrefix a [2,4,7,8,6] 30 :=
  branch_upper a [2,4,7,8,6] 30 (by decide) (fin9_cases _
  node927
  node931
  (invalid_upper a [2,4,7,8,6,2] 30 (by decide +kernel))
  node939
  (invalid_upper a [2,4,7,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,6,8] 30 (by decide +kernel)))

theorem node941 : UpperPrefix a [2,4,7,8] 30 :=
  branch_upper a [2,4,7,8] 30 (by decide) (fin9_cases _
  node899
  node908
  (invalid_upper a [2,4,7,8,2] 30 (by decide +kernel))
  node923
  (invalid_upper a [2,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,5] 30 (by decide +kernel))
  node940
  (invalid_upper a [2,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,8] 30 (by decide +kernel)))

theorem node942 : UpperPrefix a [2,4,7] 30 :=
  branch_upper a [2,4,7] 30 (by decide) (fin9_cases _
  node777
  node804
  (invalid_upper a [2,4,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,4] 30 (by decide +kernel))
  node838
  node892
  (invalid_upper a [2,4,7,7] 30 (by decide +kernel))
  node941)

def cert943 : Leaf := ⟨⟨504,0,224,0,460,396,300,108,232⟩,[(1,3),(3,1)],[(1,4,1),(1,4,3)],⟨7,19,268,25,50,232,232,488,492⟩,⟨7,19,268,25,50,96,192,384,260⟩,[⟨0,1266886860137792986416128,⟨502,18,492,508,50,96,192,384,484⟩⟩,⟨4,1266886860136624755311617,⟨487,3,492,493,34,96,192,384,484⟩⟩]⟩
theorem node943 : UpperPrefix a [2,4,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,0,1] 30 cert943 (by decide +kernel)

def cert944 : Leaf := ⟨⟨496,0,226,0,454,390,294,102,226⟩,[(1,3),(3,1)],[],⟨7,19,268,25,56,226,226,482,486⟩,⟨7,19,268,25,56,96,192,384,260⟩,[⟨0,1214857656032130298283008,⟨486,498,284,508,60,96,192,384,260⟩⟩,⟨3,1233858307815820988781573,⟨487,499,487,499,242,96,192,384,485⟩⟩,⟨4,1214857656030481030841345,⟨487,483,268,493,44,96,192,384,260⟩⟩]⟩
theorem node944 : UpperPrefix a [2,4,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,0,3] 30 cert944 (by decide +kernel)

def cert945 : Leaf := ⟨⟨272,0,179,0,0,411,315,59,187⟩,[(1,3),(3,1),(4,5)],[(6,4,4)],⟨7,19,268,25,112,234,234,426,430⟩,⟨7,19,268,25,112,96,192,384,260⟩,[⟨2,1210144549040735916135937,⟨251,123,506,123,112,112,192,400,496⟩⟩,⟨3,1210107565286049635636229,⟨7,19,263,19,112,112,192,384,261⟩⟩,⟨5,1210107564157952047715333,⟨15,27,271,27,80,64,192,384,261⟩⟩,⟨7,1208926973665333566510085,⟨15,27,271,27,112,112,64,256,261⟩⟩]⟩
theorem node945 : UpperPrefix a [2,4,8,0,6] 30 :=
  Boolean.leaf_sound a [2,4,8,0,6] 30 cert945 (by decide +kernel)

def cert946 : Leaf := ⟨⟨272,0,113,0,329,409,313,121,121⟩,[(1,3),(3,1)],[],⟨7,19,268,25,176,98,232,488,364⟩,⟨7,19,268,25,176,98,192,384,260⟩,[⟨1,1361519017103811289284609,⟨13,25,268,25,500,508,192,384,260⟩⟩,⟨2,1210144549389693419001345,⟨251,123,506,123,176,106,192,400,496⟩⟩,⟨7,1360042701114965350167615,⟨15,31,271,31,319,367,64,256,261⟩⟩,⟨3,1210107565283850612380677,⟨7,19,263,19,176,98,192,384,261⟩⟩,⟨5,1210107564157952047715333,⟨15,27,271,27,144,74,192,384,261⟩⟩,⟨6,1210106412362347347710981,⟨15,27,271,27,176,42,128,384,261⟩⟩]⟩
theorem node946 : UpperPrefix a [2,4,8,0,7,1] 30 :=
  Boolean.leaf_sound a [2,4,8,0,7,1] 30 cert946 (by decide +kernel)

def cert947 : Leaf := ⟨⟨376,0,112,0,328,273,313,120,120⟩,[(1,3),(3,1)],[],⟨7,19,268,25,176,104,194,480,356⟩,⟨7,19,268,25,176,104,194,384,260⟩,[⟨1,1664340193613272862162945,⟨13,25,268,25,436,508,508,384,260⟩⟩,⟨0,1361518440643058717426688,⟨6,18,268,24,436,508,194,384,260⟩⟩,⟨2,1212505734887326101804545,⟨251,123,506,123,176,122,250,400,496⟩⟩,⟨7,1662274158270422474306687,⟨15,31,271,31,319,367,367,256,261⟩⟩]⟩
theorem node947 : UpperPrefix a [2,4,8,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,4,8,0,7,3,1] 30 cert947 (by decide +kernel)

def cert948 : Leaf := ⟨⟨504,0,242,0,0,406,0,126,250⟩,[(1,3),(3,1),(4,6),(6,4)],[],⟨7,19,268,25,176,104,224,450,326⟩,⟨7,19,268,25,176,104,224,384,260⟩,[⟨0,1214858052670023621673984,⟨502,466,380,508,240,124,240,384,292⟩⟩]⟩
theorem node948 : UpperPrefix a [2,4,8,0,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,0,7,3,5] 30 cert948 (by decide +kernel)

theorem node949 : UpperPrefix a [2,4,8,0,7,3] 30 :=
  branch_upper a [2,4,8,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,0,7,3,0] 30 (by decide +kernel))
  node947
  (invalid_upper a [2,4,8,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,3,4] 30 (by decide +kernel))
  node948
  (invalid_upper a [2,4,8,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,3,8] 30 (by decide +kernel)))

theorem node950 : UpperPrefix a [2,4,8,0,7] 30 :=
  branch_upper a [2,4,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,0,7,0] 30 (by decide +kernel))
  node946
  (invalid_upper a [2,4,8,0,7,2] 30 (by decide +kernel))
  node949
  (invalid_upper a [2,4,8,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,7,8] 30 (by decide +kernel)))

theorem node951 : UpperPrefix a [2,4,8,0] 30 :=
  branch_upper a [2,4,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,0,0] 30 (by decide +kernel))
  node943
  (invalid_upper a [2,4,8,0,2] 30 (by decide +kernel))
  node944
  (invalid_upper a [2,4,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,0,5] 30 (by decide +kernel))
  node945
  node950
  (invalid_upper a [2,4,8,0,8] 30 (by decide +kernel)))

def cert952 : Leaf := ⟨⟨488,0,224,0,460,396,300,108,232⟩,[(1,4),(3,1)],[(4,1,3),(0,4,1),(0,4,3)],⟨7,19,268,26,49,232,232,488,492⟩,⟨7,19,268,26,49,96,192,384,260⟩,[⟨1,1266886860137792986415105,⟨501,17,492,508,49,96,192,384,484⟩⟩]⟩
theorem node952 : UpperPrefix a [2,4,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,1,0] 30 cert952 (by decide +kernel)

def cert953 : Leaf := ⟨⟨488,488,224,0,449,388,292,100,224⟩,[(3,1)],[(4,1,3)],⟨7,19,268,26,56,97,224,480,484⟩,⟨7,19,268,26,56,97,192,384,260⟩,[⟨1,1338156702227121476468737,⟨485,501,476,508,508,481,192,384,260⟩⟩,⟨0,1285813291192732112913408,⟨14,478,268,478,508,96,192,384,260⟩⟩,⟨3,1215153812743075350447105,⟨487,499,324,242,240,481,192,384,260⟩⟩,⟨2,1210107565286057419228161,⟨11,27,264,26,58,123,192,384,256⟩⟩]⟩
theorem node953 : UpperPrefix a [2,4,8,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,1,3,0] 30 cert953 (by decide +kernel)

def cert954 : Leaf := ⟨⟨360,364,99,0,325,0,293,101,97⟩,[(3,1),(5,6)],[(4,1,3),(7,5,5)],⟨7,19,268,26,56,224,225,481,357⟩,⟨7,19,268,26,56,224,192,384,260⟩,[⟨1,1214857658565679964487681,⟨501,497,316,248,56,224,224,384,276⟩⟩,⟨3,1214857658564854257026049,⟨487,499,292,242,48,224,224,384,260⟩⟩]⟩
theorem node954 : UpperPrefix a [2,4,8,1,3,7] 30 :=
  Boolean.leaf_sound a [2,4,8,1,3,7] 30 cert954 (by decide +kernel)

theorem node955 : UpperPrefix a [2,4,8,1,3] 30 :=
  branch_upper a [2,4,8,1,3] 30 (by decide) (fin9_cases _
  node953
  (invalid_upper a [2,4,8,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,3,6] 30 (by decide +kernel))
  node954
  (invalid_upper a [2,4,8,1,3,8] 30 (by decide +kernel)))

def cert956 : Leaf := ⟨⟨424,32,163,0,0,398,303,47,171⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4)],⟨7,19,268,26,112,97,232,424,428⟩,⟨7,19,268,26,112,97,192,384,260⟩,[⟨2,1210107565286057419228161,⟨11,27,264,26,122,123,192,384,256⟩⟩,⟨3,1210107565286049635648513,⟨7,19,260,18,114,115,192,384,260⟩⟩,⟨7,1208926973665340008973313,⟨15,27,268,26,122,123,64,256,260⟩⟩,⟨8,1181745671428245570561,⟨15,27,12,26,122,123,192,128,4⟩⟩]⟩
theorem node956 : UpperPrefix a [2,4,8,1,6,0] 30 :=
  Boolean.leaf_sound a [2,4,8,1,6,0] 30 cert956 (by decide +kernel)

def cert957 : Leaf := ⟨⟨424,428,161,0,0,389,300,45,169⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4)],⟨7,19,268,26,112,104,193,416,420⟩,⟨7,19,268,26,112,104,193,384,260⟩,[⟨1,1494003010905660980199425,⟨453,465,444,508,500,508,193,384,388⟩⟩]⟩
theorem node957 : UpperPrefix a [2,4,8,1,6,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,1,6,3,0] 30 cert957 (by decide +kernel)

def cert958 : Local := ⟨⟨392,396,131,0,0,391,271,15,139⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4),(5,6,4)]⟩
theorem node958 : UpperPrefix a [2,4,8,1,6,3,5] 30 :=
  local_sound a [2,4,8,1,6,3,5] 30 cert958 (by decide +kernel)

theorem node959 : UpperPrefix a [2,4,8,1,6,3] 30 :=
  branch_upper a [2,4,8,1,6,3] 30 (by decide) (fin9_cases _
  node957
  (invalid_upper a [2,4,8,1,6,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,3,4] 30 (by decide +kernel))
  node958
  (invalid_upper a [2,4,8,1,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,1,6,3,8] 30 (by decide +kernel)))

#print axioms node959
end Delivery.FiniteExclusion.Sharp2x7
