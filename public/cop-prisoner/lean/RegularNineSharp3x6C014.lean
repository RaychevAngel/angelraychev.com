import RegularNineSharp3x6Base
import RegularNineSharp3x6C013
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert896 : Leaf := ⟨⟨484,0,330,486,0,394,266,74,194⟩,[(1,4),(4,1)],[],⟨11,38,133,25,52,112,450,450,330⟩,⟨11,38,133,25,52,112,192,384,264⟩,[⟨4,1252692036106497329210377,⟨463,38,453,463,38,98,192,388,461⟩⟩,⟨0,1252729002744466080017408,⟨506,246,502,506,246,114,192,384,488⟩⟩,⟨2,1214839173434631671251969,⟨491,34,449,505,48,112,192,384,296⟩⟩,⟨5,1214839172027256791106561,⟨463,6,453,477,20,80,192,384,268⟩⟩]⟩
theorem node896 : UpperPrefix a [3,5,7,0,2,4] 30 :=
  Boolean.leaf_sound a [3,5,7,0,2,4] 30 cert896 (by decide +kernel)

def cert897 : Leaf := ⟨⟨372,0,346,358,0,26,280,90,82⟩,[(1,4),(4,1)],[],⟨11,38,133,25,52,352,194,464,344⟩,⟨11,38,133,25,52,352,194,384,264⟩,[⟨0,1252729335377519807835136,⟨506,246,502,506,246,352,210,416,488⟩⟩,⟨2,1247960302454161543267329,⟨491,34,225,505,48,352,194,384,424⟩⟩,⟨5,1247960301011602291033089,⟨463,6,197,477,20,320,194,384,396⟩⟩,⟨7,1511158430818739961209947,⟨27,63,13,27,63,361,379,256,265⟩⟩]⟩
theorem node897 : UpperPrefix a [3,5,7,0,2,8,1] 30 :=
  Boolean.leaf_sound a [3,5,7,0,2,8,1] 30 cert897 (by decide +kernel)

def cert898 : Leaf := ⟨⟨372,0,346,358,0,26,266,90,82⟩,[(1,4),(4,1)],[],⟨11,38,133,25,52,352,208,450,330⟩,⟨11,38,133,25,52,352,208,384,264⟩,[⟨0,1252729335377519807835136,⟨506,246,502,506,246,352,210,416,488⟩⟩,⟨2,1214839308577804864455681,⟨491,34,417,505,48,352,208,416,360⟩⟩,⟨5,1214839298128046357480449,⟨463,6,389,477,20,320,208,384,332⟩⟩,⟨7,1511158430818739961209947,⟨27,63,13,27,63,361,379,256,265⟩⟩]⟩
theorem node898 : UpperPrefix a [3,5,7,0,2,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,0,2,8,4] 30 cert898 (by decide +kernel)

theorem node899 : UpperPrefix a [3,5,7,0,2,8] 30 :=
  branch_upper a [3,5,7,0,2,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,2,8,0] 30 (by decide +kernel))
  node897
  (invalid_upper a [3,5,7,0,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,2,8,3] 30 (by decide +kernel))
  node898
  (invalid_upper a [3,5,7,0,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,2,8,8] 30 (by decide +kernel)))

theorem node900 : UpperPrefix a [3,5,7,0,2] 30 :=
  branch_upper a [3,5,7,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,2,0] 30 (by decide +kernel))
  node895
  (invalid_upper a [3,5,7,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,2,3] 30 (by decide +kernel))
  node896
  (invalid_upper a [3,5,7,0,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,2,7] 30 (by decide +kernel))
  node899)

def cert901 : Leaf := ⟨⟨52,153,24,38,0,157,285,29,21⟩,[(4,5)],[(6,4,4)],⟨11,38,133,25,112,98,468,404,284⟩,⟨11,38,133,25,112,98,192,384,264⟩,[⟨8,1181748490584665941115,⟨11,63,133,59,127,127,255,128,9⟩⟩,⟨1,1247960428240490787504129,⟨461,52,133,477,112,112,192,384,460⟩⟩,⟨5,1247960427112391857406977,⟨463,6,133,477,80,66,192,384,460⟩⟩,⟨7,1218371706631079299384355,⟨267,319,5,25,121,379,64,256,264⟩⟩]⟩
theorem node901 : UpperPrefix a [3,5,7,0,6,1] 30 :=
  Boolean.leaf_sound a [3,5,7,0,6,1] 30 cert901 (by decide +kernel)

def cert902 : Leaf := ⟨⟨304,0,314,290,0,410,314,58,50⟩,[(1,5),(4,5)],[(7,2,5),(6,4,4),(2,5,1)],⟨11,38,133,25,112,100,466,402,282⟩,⟨11,38,133,25,112,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,114,246,192,384,264⟩⟩]⟩
theorem node902 : UpperPrefix a [3,5,7,0,6,2] 30 :=
  Boolean.leaf_sound a [3,5,7,0,6,2] 30 cert902 (by decide +kernel)

def cert903 : Leaf := ⟨⟨180,153,10,166,0,0,271,15,135⟩,[(4,5),(5,4)],[(6,4,4),(6,4,5)],⟨11,38,133,25,112,112,454,390,270⟩,⟨11,38,133,25,112,112,192,384,264⟩,[⟨4,1214839173152057186321409,⟨463,38,453,461,96,96,192,384,268⟩⟩,⟨5,1214839172027256791106561,⟨463,6,453,477,80,80,192,384,268⟩⟩,⟨8,1181748490584665941115,⟨11,63,133,59,127,127,255,128,9⟩⟩]⟩
theorem node903 : UpperPrefix a [3,5,7,0,6,4] 30 :=
  Boolean.leaf_sound a [3,5,7,0,6,4] 30 cert903 (by decide +kernel)

def cert904 : Leaf := ⟨⟨52,153,24,38,0,31,285,29,21⟩,[(4,5)],[(6,4,4)],⟨11,38,133,25,112,352,194,404,284⟩,⟨11,38,133,25,112,352,194,384,264⟩,[⟨5,1247960301011602291033089,⟨463,6,197,477,80,320,194,384,396⟩⟩,⟨7,1218371708887285749515331,⟨267,319,5,25,121,377,379,256,264⟩⟩,⟨8,1181745671428262356091,⟨11,63,133,27,127,127,207,128,9⟩⟩,⟨1,1247960284125302711648257,⟨397,52,133,413,112,368,192,384,396⟩⟩]⟩
theorem node904 : UpperPrefix a [3,5,7,0,6,8,1] 30 :=
  Boolean.leaf_sound a [3,5,7,0,6,8,1] 30 cert904 (by decide +kernel)

def cert905 : Leaf := ⟨⟨308,280,314,294,0,30,0,62,54⟩,[(4,5),(6,2)],[(7,2,6),(6,4,4)],⟨11,38,133,25,112,352,196,402,282⟩,⟨11,38,133,25,112,352,196,384,264⟩,[⟨0,1215171304801475981511680,⟨506,246,502,440,242,498,246,384,264⟩⟩]⟩
theorem node905 : UpperPrefix a [3,5,7,0,6,8,2] 30 :=
  Boolean.leaf_sound a [3,5,7,0,6,8,2] 30 cert905 (by decide +kernel)

def cert906 : Leaf := ⟨⟨176,152,26,162,0,154,266,31,151⟩,[(4,5)],[(6,4,4)],⟨11,38,133,25,112,352,208,390,270⟩,⟨11,38,133,25,112,352,208,384,264⟩,[⟨2,1210109947703860983235587,⟨27,123,249,25,112,368,240,496,264⟩⟩,⟨5,1214839298128046357480449,⟨463,6,389,477,80,320,208,384,332⟩⟩,⟨8,1181745671436852290683,⟨11,63,133,27,127,127,223,128,9⟩⟩,⟨0,1210109947703860044762112,⟨26,118,246,24,112,368,240,496,264⟩⟩]⟩
theorem node906 : UpperPrefix a [3,5,7,0,6,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,0,6,8,4] 30 cert906 (by decide +kernel)

theorem node907 : UpperPrefix a [3,5,7,0,6,8] 30 :=
  branch_upper a [3,5,7,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,6,8,0] 30 (by decide +kernel))
  node904
  node905
  (invalid_upper a [3,5,7,0,6,8,3] 30 (by decide +kernel))
  node906
  (invalid_upper a [3,5,7,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,6,8,8] 30 (by decide +kernel)))

theorem node908 : UpperPrefix a [3,5,7,0,6] 30 :=
  branch_upper a [3,5,7,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,6,0] 30 (by decide +kernel))
  node901
  node902
  (invalid_upper a [3,5,7,0,6,3] 30 (by decide +kernel))
  node903
  (invalid_upper a [3,5,7,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,6,7] 30 (by decide +kernel))
  node907)

def cert909 : Leaf := ⟨⟨368,336,370,354,66,276,0,114,114⟩,[(6,2)],[(7,2,6),(2,6,5)],⟨11,38,133,25,304,98,196,464,344⟩,⟨11,38,133,25,304,98,196,384,264⟩,[⟨0,1214876159212280433642496,⟨506,246,502,440,304,98,246,384,280⟩⟩,⟨3,1212621167216378164452865,⟨103,102,247,247,498,98,246,498,502⟩⟩]⟩
theorem node909 : UpperPrefix a [3,5,7,0,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,7,0,8,1,2] 30 cert909 (by decide +kernel)

def cert910 : Leaf := ⟨⟨224,200,104,224,200,136,296,104,240⟩,[],[(8,4,6)],⟨11,38,133,25,304,98,208,388,328⟩,⟨11,38,133,25,304,98,208,388,264⟩,[⟨0,1214869246195648512986112,⟨378,246,502,312,304,98,242,502,280⟩⟩,⟨1,1273998926232794353106945,⟨477,500,461,477,496,240,208,388,460⟩⟩,⟨2,2296251928474245429986339,⟨315,379,473,25,313,379,472,456,264⟩⟩,⟨4,1212616324728576556409865,⟨15,38,133,143,422,98,226,388,397⟩⟩]⟩
theorem node910 : UpperPrefix a [3,5,7,0,8,1,4,2] 30 :=
  Boolean.leaf_sound a [3,5,7,0,8,1,4,2] 30 cert910 (by decide +kernel)

def cert911 : Leaf := ⟨⟨180,144,48,164,133,148,292,52,181⟩,[],[(8,4,6)],⟨11,38,133,25,304,98,208,448,268⟩,⟨11,38,133,25,304,98,208,448,264⟩,[⟨1,1274146500185384029519873,⟨477,500,461,477,496,240,208,448,460⟩⟩,⟨3,1212623759037963716140545,⟨103,102,247,247,498,98,240,498,502⟩⟩,⟨6,2296250703424717392462899,⟨283,319,397,25,315,319,413,396,264⟩⟩,⟨0,1212616754858624784796672,⟨106,38,166,248,496,98,208,448,456⟩⟩]⟩
theorem node911 : UpperPrefix a [3,5,7,0,8,1,4,6] 30 :=
  Boolean.leaf_sound a [3,5,7,0,8,1,4,6] 30 cert911 (by decide +kernel)

theorem node912 : UpperPrefix a [3,5,7,0,8,1,4] 30 :=
  branch_upper a [3,5,7,0,8,1,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,8,1,4,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,4,1] 30 (by decide +kernel))
  node910
  (invalid_upper a [3,5,7,0,8,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,4,5] 30 (by decide +kernel))
  node911
  (invalid_upper a [3,5,7,0,8,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,4,8] 30 (by decide +kernel)))

theorem node913 : UpperPrefix a [3,5,7,0,8,1] 30 :=
  branch_upper a [3,5,7,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,1] 30 (by decide +kernel))
  node909
  (invalid_upper a [3,5,7,0,8,1,3] 30 (by decide +kernel))
  node912
  (invalid_upper a [3,5,7,0,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,1,8] 30 (by decide +kernel)))

def cert914 : Leaf := ⟨⟨304,0,370,290,66,402,306,114,114⟩,[(1,5)],[(7,2,5),(2,5,1)],⟨11,38,133,25,304,100,210,466,346⟩,⟨11,38,133,25,304,100,192,384,264⟩,[⟨0,1215024613582863133068288,⟨506,246,502,472,498,246,192,384,264⟩⟩,⟨3,1212623753971414135365121,⟨103,102,247,247,498,102,208,498,502⟩⟩,⟨6,1210106412362349226771473,⟨11,38,133,25,315,38,128,384,264⟩⟩]⟩
theorem node914 : UpperPrefix a [3,5,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,5,7,0,8,2] 30 cert914 (by decide +kernel)

def cert915 : Leaf := ⟨⟨288,392,298,290,74,266,300,42,98⟩,[],[(2,7,6)],⟨11,38,133,25,304,112,194,388,328⟩,⟨11,38,133,25,304,112,194,388,264⟩,[⟨0,1214869246195648512986112,⟨378,246,502,312,304,112,242,502,280⟩⟩,⟨4,1255238587508594721432585,⟨463,230,453,463,486,226,194,388,461⟩⟩,⟨6,1212615169556378119332923,⟨15,47,133,159,447,191,135,388,397⟩⟩,⟨7,1662274158277167825290307,⟨27,319,13,25,312,377,379,260,264⟩⟩]⟩
theorem node915 : UpperPrefix a [3,5,7,0,8,4,1,2] 30 :=
  Boolean.leaf_sound a [3,5,7,0,8,4,1,2] 30 cert915 (by decide +kernel)

def cert916 : Leaf := ⟨⟨292,257,290,292,5,261,293,37,37⟩,[],[],⟨11,38,133,25,304,112,194,448,268⟩,⟨11,38,133,25,304,112,194,448,264⟩,[⟨3,1212623761184210413559297,⟨103,102,247,247,498,240,242,498,502⟩⟩,⟨4,1255238587508594721432585,⟨463,230,453,463,486,226,194,452,461⟩⟩,⟨6,2296250703424717426017395,⟨283,319,397,25,315,319,415,397,264⟩⟩,⟨7,1237261179329389047843911,⟨283,319,319,25,312,121,379,377,264⟩⟩,⟨1,1239032066760434831589377,⟨281,316,445,25,304,240,496,496,264⟩⟩]⟩
theorem node916 : UpperPrefix a [3,5,7,0,8,4,1,6] 30 :=
  Boolean.leaf_sound a [3,5,7,0,8,4,1,6] 30 cert916 (by decide +kernel)

theorem node917 : UpperPrefix a [3,5,7,0,8,4,1] 30 :=
  branch_upper a [3,5,7,0,8,4,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,8,4,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,1,1] 30 (by decide +kernel))
  node915
  (invalid_upper a [3,5,7,0,8,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,1,5] 30 (by decide +kernel))
  node916
  (invalid_upper a [3,5,7,0,8,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,1,8] 30 (by decide +kernel)))

def cert918 : Leaf := ⟨⟨356,320,354,358,70,262,0,102,102⟩,[(6,2)],[(7,2,6)],⟨11,38,133,25,304,112,196,450,330⟩,⟨11,38,133,25,304,112,196,384,264⟩,[⟨0,1214876159212280433642496,⟨506,246,502,440,304,114,246,384,280⟩⟩,⟨3,1212621167110825048186369,⟨103,102,247,247,498,242,246,498,502⟩⟩,⟨4,1252846887876084836344841,⟨463,102,453,463,486,226,196,452,461⟩⟩]⟩
theorem node918 : UpperPrefix a [3,5,7,0,8,4,2] 30 :=
  Boolean.leaf_sound a [3,5,7,0,8,4,2] 30 cert918 (by decide +kernel)

theorem node919 : UpperPrefix a [3,5,7,0,8,4] 30 :=
  branch_upper a [3,5,7,0,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,8,4,0] 30 (by decide +kernel))
  node917
  node918
  (invalid_upper a [3,5,7,0,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,4,8] 30 (by decide +kernel)))

theorem node920 : UpperPrefix a [3,5,7,0,8] 30 :=
  branch_upper a [3,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,8,0] 30 (by decide +kernel))
  node913
  node914
  (invalid_upper a [3,5,7,0,8,3] 30 (by decide +kernel))
  node919
  (invalid_upper a [3,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,8,8] 30 (by decide +kernel)))

theorem node921 : UpperPrefix a [3,5,7,0] 30 :=
  branch_upper a [3,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,0,0] 30 (by decide +kernel))
  node894
  node900
  (invalid_upper a [3,5,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,0,5] 30 (by decide +kernel))
  node908
  (invalid_upper a [3,5,7,0,7] 30 (by decide +kernel))
  node920)

def cert922 : Local := ⟨⟨0,0,344,353,328,409,281,89,81⟩,[(0,3),(1,5)],[(5,1,3),(7,2,5),(1,3,0),(2,5,1)]⟩
theorem node922 : UpperPrefix a [3,5,7,1,0,2] 30 :=
  local_sound a [3,5,7,1,0,2] 30 cert922 (by decide +kernel)

def cert923 : Leaf := ⟨⟨0,201,72,225,200,141,269,77,197⟩,[(0,3)],[(5,1,3),(1,3,0)],⟨11,38,133,26,49,112,452,452,332⟩,⟨11,38,133,26,49,112,192,384,264⟩,[⟨4,1255244964605667082265609,⟨463,230,453,463,487,230,192,452,461⟩⟩,⟨8,1181747927772285682811,⟨27,63,141,27,59,127,255,128,9⟩⟩,⟨2,1210107565283989526676491,⟨27,59,137,27,57,112,192,384,265⟩⟩]⟩
theorem node923 : UpperPrefix a [3,5,7,1,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,1,0,4] 30 cert923 (by decide +kernel)

def cert924 : Leaf := ⟨⟨0,345,344,353,328,29,0,93,85⟩,[(0,3),(6,2)],[(5,1,3),(7,2,6),(1,3,0)],⟨11,38,133,26,49,352,196,464,344⟩,⟨11,38,133,26,49,352,196,384,264⟩,[⟨2,1210107565283989526676491,⟨27,59,137,27,57,352,192,384,265⟩⟩]⟩
theorem node924 : UpperPrefix a [3,5,7,1,0,8,2] 30 :=
  Boolean.leaf_sound a [3,5,7,1,0,8,2] 30 cert924 (by decide +kernel)

def cert925 : Leaf := ⟨⟨0,153,24,161,136,157,269,93,213⟩,[(0,3)],[(5,1,3),(1,3,0)],⟨11,38,133,26,49,352,208,452,332⟩,⟨11,38,133,26,49,352,208,384,264⟩,[⟨6,1210106412364690403378235,⟨27,63,141,27,59,319,157,384,265⟩⟩,⟨8,1181745671565835519035,⟨27,63,141,27,59,127,221,128,9⟩⟩,⟨2,1210107565283989526676491,⟨27,59,137,27,57,352,208,384,265⟩⟩]⟩
theorem node925 : UpperPrefix a [3,5,7,1,0,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,1,0,8,4] 30 cert925 (by decide +kernel)

theorem node926 : UpperPrefix a [3,5,7,1,0,8] 30 :=
  branch_upper a [3,5,7,1,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,1,0,8,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,0,8,1] 30 (by decide +kernel))
  node924
  (invalid_upper a [3,5,7,1,0,8,3] 30 (by decide +kernel))
  node925
  (invalid_upper a [3,5,7,1,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,0,8,8] 30 (by decide +kernel)))

theorem node927 : UpperPrefix a [3,5,7,1,0] 30 :=
  branch_upper a [3,5,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,0,1] 30 (by decide +kernel))
  node922
  (invalid_upper a [3,5,7,1,0,3] 30 (by decide +kernel))
  node923
  (invalid_upper a [3,5,7,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,0,7] 30 (by decide +kernel))
  node926)

def cert928 : Local := ⟨⟨0,0,344,485,0,409,281,89,209⟩,[(0,3),(1,4),(4,1)],[(5,1,3),(1,3,0),(2,4,3)]⟩
theorem node928 : UpperPrefix a [3,5,7,1,2] 30 :=
  local_sound a [3,5,7,1,2] 30 cert928 (by decide +kernel)

def cert929 : Leaf := ⟨⟨0,409,280,293,0,413,285,29,21⟩,[(0,3),(4,5)],[(5,1,3),(1,3,0),(6,4,4)],⟨11,38,133,26,112,373,469,405,285⟩,⟨11,38,133,26,112,96,192,384,264⟩,[⟨7,1218371706631072856933387,⟨267,319,5,283,112,112,64,256,265⟩⟩]⟩
theorem node929 : UpperPrefix a [3,5,7,1,6] 30 :=
  Boolean.leaf_sound a [3,5,7,1,6] 30 cert929 (by decide +kernel)

def cert930 : Local := ⟨⟨0,345,344,356,76,284,0,92,84⟩,[(0,3),(6,2)],[(5,1,3),(7,2,6),(1,3,0),(0,5,1)]⟩
theorem node930 : UpperPrefix a [3,5,7,1,8,0,2] 30 :=
  local_sound a [3,5,7,1,8,0,2] 30 cert930 (by decide +kernel)

def cert931 : Leaf := ⟨⟨0,153,24,164,204,156,268,92,212⟩,[(0,3)],[(5,1,3),(1,3,0),(8,4,6),(0,5,1)],⟨11,38,133,26,304,97,208,452,332⟩,⟨11,38,133,26,304,97,208,384,264⟩,[⟨6,1210106412362349243548697,⟨11,38,133,27,315,39,157,384,265⟩⟩]⟩
theorem node931 : UpperPrefix a [3,5,7,1,8,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,1,8,0,4] 30 cert931 (by decide +kernel)

theorem node932 : UpperPrefix a [3,5,7,1,8,0] 30 :=
  branch_upper a [3,5,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,0,1] 30 (by decide +kernel))
  node930
  (invalid_upper a [3,5,7,1,8,0,3] 30 (by decide +kernel))
  node931
  (invalid_upper a [3,5,7,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,0,8] 30 (by decide +kernel)))

def cert933 : Local := ⟨⟨0,0,344,353,73,409,281,89,81⟩,[(0,3),(1,5)],[(5,1,3),(7,2,5),(1,3,0),(2,5,1)]⟩
theorem node933 : UpperPrefix a [3,5,7,1,8,2] 30 :=
  local_sound a [3,5,7,1,8,2] 30 cert933 (by decide +kernel)

def cert934 : Leaf := ⟨⟨0,457,0,485,205,397,0,77,197⟩,[(0,3),(2,6),(6,2)],[(5,1,3),(1,3,0)],⟨11,38,133,26,304,112,193,452,332⟩,⟨11,38,133,26,304,112,193,384,264⟩,[⟨4,1255832666342640435094537,⟨463,230,453,463,486,230,453,452,461⟩⟩]⟩
theorem node934 : UpperPrefix a [3,5,7,1,8,4,0] 30 :=
  Boolean.leaf_sound a [3,5,7,1,8,4,0] 30 cert934 (by decide +kernel)

def cert935 : Leaf := ⟨⟨0,329,328,357,77,269,0,77,69⟩,[(0,3),(6,2)],[(5,1,3),(7,2,6),(1,3,0)],⟨11,38,133,26,304,112,196,449,329⟩,⟨11,38,133,26,304,112,196,384,264⟩,[⟨4,1255097426681874420605961,⟨463,230,453,463,486,98,196,452,461⟩⟩]⟩
theorem node935 : UpperPrefix a [3,5,7,1,8,4,2] 30 :=
  Boolean.leaf_sound a [3,5,7,1,8,4,2] 30 cert935 (by decide +kernel)

theorem node936 : UpperPrefix a [3,5,7,1,8,4] 30 :=
  branch_upper a [3,5,7,1,8,4] 30 (by decide) (fin9_cases _
  node934
  (invalid_upper a [3,5,7,1,8,4,1] 30 (by decide +kernel))
  node935
  (invalid_upper a [3,5,7,1,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,4,8] 30 (by decide +kernel)))

theorem node937 : UpperPrefix a [3,5,7,1,8] 30 :=
  branch_upper a [3,5,7,1,8] 30 (by decide) (fin9_cases _
  node932
  (invalid_upper a [3,5,7,1,8,1] 30 (by decide +kernel))
  node933
  (invalid_upper a [3,5,7,1,8,3] 30 (by decide +kernel))
  node936
  (invalid_upper a [3,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,8,8] 30 (by decide +kernel)))

theorem node938 : UpperPrefix a [3,5,7,1] 30 :=
  branch_upper a [3,5,7,1] 30 (by decide) (fin9_cases _
  node927
  (invalid_upper a [3,5,7,1,1] 30 (by decide +kernel))
  node928
  (invalid_upper a [3,5,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,1,5] 30 (by decide +kernel))
  node929
  (invalid_upper a [3,5,7,1,7] 30 (by decide +kernel))
  node937)

def cert939 : Leaf := ⟨⟨116,216,88,65,74,152,280,88,80⟩,[],[(2,3,0),(0,4,3),(1,5,4)],⟨11,38,133,28,49,98,464,464,344⟩,⟨11,38,133,28,49,98,192,384,264⟩,[⟨8,1181747927770003981427,⟨27,63,133,29,59,127,255,128,8⟩⟩,⟨5,1323666153021274158531585,⟨463,6,133,476,477,66,192,384,456⟩⟩,⟨7,1360042701117299652297763,⟨27,319,5,28,305,379,64,256,264⟩⟩]⟩
theorem node939 : UpperPrefix a [3,5,7,2,0,1] 30 :=
  Boolean.leaf_sound a [3,5,7,2,0,1] 30 cert939 (by decide +kernel)

def cert940 : Leaf := ⟨⟨196,200,74,195,202,138,266,74,194⟩,[],[(2,3,0),(0,4,3)],⟨11,38,133,28,49,112,450,450,330⟩,⟨11,38,133,28,49,112,192,384,264⟩,[⟨4,1252839898289463161545737,⟨463,38,453,463,487,230,192,388,461⟩⟩,⟨5,1224302387765873255121923,⟨463,463,453,28,477,92,192,384,264⟩⟩,⟨8,1181747927770003981427,⟨27,63,133,29,59,127,255,128,8⟩⟩]⟩
theorem node940 : UpperPrefix a [3,5,7,2,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,2,0,4] 30 cert940 (by decide +kernel)

def cert941 : Leaf := ⟨⟨388,392,266,387,394,138,264,10,194⟩,[],[(2,3,0),(0,4,3)],⟨11,38,133,28,49,352,194,400,328⟩,⟨11,38,133,28,49,352,194,400,264⟩,[⟨4,1247888879831387225562377,⟨299,102,231,367,33,355,230,487,299⟩⟩,⟨5,1611730094145173995127873,⟨463,262,461,412,477,325,463,412,392⟩⟩,⟨6,1210401560269895572677883,⟨31,191,141,31,191,447,159,415,265⟩⟩]⟩
theorem node941 : UpperPrefix a [3,5,7,2,0,8,1,4] 30 :=
  Boolean.leaf_sound a [3,5,7,2,0,8,1,4] 30 cert941 (by decide +kernel)

def cert942 : Leaf := ⟨⟨308,280,314,291,266,0,312,0,50⟩,[(5,7),(7,5)],[(2,3,0),(0,4,3)],⟨11,38,133,28,49,352,194,448,280⟩,⟨11,38,133,28,49,352,194,448,264⟩,[⟨6,1790957489757663106450547,⟨283,319,389,285,315,319,415,397,264⟩⟩,⟨7,1581993932581041972710479,⟨283,319,319,287,305,369,379,369,265⟩⟩]⟩
theorem node942 : UpperPrefix a [3,5,7,2,0,8,1,6] 30 :=
  Boolean.leaf_sound a [3,5,7,2,0,8,1,6] 30 cert942 (by decide +kernel)

theorem node943 : UpperPrefix a [3,5,7,2,0,8,1] 30 :=
  branch_upper a [3,5,7,2,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,2,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,1,3] 30 (by decide +kernel))
  node941
  (invalid_upper a [3,5,7,2,0,8,1,5] 30 (by decide +kernel))
  node942
  (invalid_upper a [3,5,7,2,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,1,8] 30 (by decide +kernel)))

def cert944 : Leaf := ⟨⟨436,400,306,417,384,144,288,48,240⟩,[],[(2,3,0),(0,4,3),(1,7,2)],⟨11,38,133,28,49,352,208,386,328⟩,⟨11,38,133,28,49,352,208,386,264⟩,[⟨3,1210403114009671683320833,⟨67,246,247,86,247,482,246,482,256⟩⟩,⟨6,1210401560269895572677883,⟨31,191,141,31,191,447,159,415,265⟩⟩]⟩
theorem node944 : UpperPrefix a [3,5,7,2,0,8,4,1] 30 :=
  Boolean.leaf_sound a [3,5,7,2,0,8,4,1] 30 cert944 (by decide +kernel)

def cert945 : Leaf := ⟨⟨308,280,314,291,266,0,298,0,50⟩,[(5,7),(7,5)],[(2,3,0),(0,4,3)],⟨11,38,133,28,49,352,208,448,266⟩,⟨11,38,133,28,49,352,208,448,264⟩,[⟨6,1450947102991048617509939,⟨283,319,389,285,315,319,413,396,264⟩⟩,⟨7,1279762475410191702559759,⟨283,319,319,287,305,352,112,352,265⟩⟩]⟩
theorem node945 : UpperPrefix a [3,5,7,2,0,8,4,6] 30 :=
  Boolean.leaf_sound a [3,5,7,2,0,8,4,6] 30 cert945 (by decide +kernel)

theorem node946 : UpperPrefix a [3,5,7,2,0,8,4] 30 :=
  branch_upper a [3,5,7,2,0,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,2,0,8,4,0] 30 (by decide +kernel))
  node944
  (invalid_upper a [3,5,7,2,0,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,4,5] 30 (by decide +kernel))
  node945
  (invalid_upper a [3,5,7,2,0,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,4,8] 30 (by decide +kernel)))

theorem node947 : UpperPrefix a [3,5,7,2,0,8] 30 :=
  branch_upper a [3,5,7,2,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,2,0,8,0] 30 (by decide +kernel))
  node943
  (invalid_upper a [3,5,7,2,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,3] 30 (by decide +kernel))
  node946
  (invalid_upper a [3,5,7,2,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,8,8] 30 (by decide +kernel)))

theorem node948 : UpperPrefix a [3,5,7,2,0] 30 :=
  branch_upper a [3,5,7,2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,2,0,0] 30 (by decide +kernel))
  node939
  (invalid_upper a [3,5,7,2,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,3] 30 (by decide +kernel))
  node940
  (invalid_upper a [3,5,7,2,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,0,7] 30 (by decide +kernel))
  node947)

def cert949 : Leaf := ⟨⟨212,217,88,194,0,152,280,88,208⟩,[(4,1)],[(5,1,4),(2,3,0),(0,5,1)],⟨11,38,133,28,50,97,464,464,344⟩,⟨11,38,133,28,50,97,192,384,264⟩,[⟨1,1247960428273476134240257,⟨493,36,165,476,48,101,192,384,456⟩⟩,⟨8,1181747927770003981427,⟨27,63,133,29,59,127,255,128,8⟩⟩]⟩
theorem node949 : UpperPrefix a [3,5,7,2,1,0] 30 :=
  Boolean.leaf_sound a [3,5,7,2,1,0] 30 cert949 (by decide +kernel)

def cert950 : Leaf := ⟨⟨212,217,72,195,0,137,265,73,193⟩,[(4,1)],[(5,1,4),(2,3,0)],⟨11,38,133,28,50,112,449,449,329⟩,⟨11,38,133,28,50,112,192,384,264⟩,[⟨1,1214876138980373129592833,⟨493,228,453,252,48,112,192,384,296⟩⟩,⟨8,1181747927770003981427,⟨27,63,133,29,59,127,255,128,8⟩⟩,⟨4,1214876138697798641255425,⟨463,230,453,204,34,96,192,384,264⟩⟩]⟩
theorem node950 : UpperPrefix a [3,5,7,2,1,4] 30 :=
  Boolean.leaf_sound a [3,5,7,2,1,4] 30 cert950 (by decide +kernel)

def cert951 : Leaf := ⟨⟨468,473,0,451,0,153,0,89,209⟩,[(2,6),(4,1),(6,2)],[(5,1,4),(2,3,0)],⟨11,38,133,28,50,352,193,464,344⟩,⟨11,38,133,28,50,352,193,384,264⟩,[⟨1,1247960374511755599282177,⟨493,100,229,508,48,356,229,384,424⟩⟩]⟩
theorem node951 : UpperPrefix a [3,5,7,2,1,8,0] 30 :=
  Boolean.leaf_sound a [3,5,7,2,1,8,0] 30 cert951 (by decide +kernel)

def cert952 : Leaf := ⟨⟨20,153,26,3,0,155,267,91,211⟩,[(4,1)],[(5,1,4),(2,3,0)],⟨11,38,133,28,50,352,208,449,329⟩,⟨11,38,133,28,50,352,208,384,264⟩,[⟨6,1210106412364696711611443,⟨27,63,133,29,59,319,157,384,264⟩⟩,⟨8,1181745671572143752243,⟨27,63,133,29,59,127,221,128,8⟩⟩,⟨7,1208926973663271982203923,⟨27,63,5,29,59,352,81,256,264⟩⟩]⟩
theorem node952 : UpperPrefix a [3,5,7,2,1,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,2,1,8,4] 30 cert952 (by decide +kernel)

theorem node953 : UpperPrefix a [3,5,7,2,1,8] 30 :=
  branch_upper a [3,5,7,2,1,8] 30 (by decide) (fin9_cases _
  node951
  (invalid_upper a [3,5,7,2,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,8,3] 30 (by decide +kernel))
  node952
  (invalid_upper a [3,5,7,2,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,8,8] 30 (by decide +kernel)))

theorem node954 : UpperPrefix a [3,5,7,2,1] 30 :=
  branch_upper a [3,5,7,2,1] 30 (by decide) (fin9_cases _
  node949
  (invalid_upper a [3,5,7,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,3] 30 (by decide +kernel))
  node950
  (invalid_upper a [3,5,7,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,1,7] 30 (by decide +kernel))
  node953)

def cert955 : Leaf := ⟨⟨52,153,58,34,0,154,314,58,50⟩,[(4,5)],[(2,3,0),(6,4,4),(0,5,1)],⟨11,38,133,28,112,97,466,402,282⟩,⟨11,38,133,28,112,97,192,384,264⟩,[⟨8,1181748490584699499899,⟨11,63,133,63,127,127,255,133,11⟩⟩,⟨7,1218371706631072856933379,⟨267,319,5,28,112,113,64,256,264⟩⟩]⟩
theorem node955 : UpperPrefix a [3,5,7,2,6,0] 30 :=
  Boolean.leaf_sound a [3,5,7,2,6,0] 30 cert955 (by decide +kernel)

def cert956 : Leaf := ⟨⟨36,137,42,35,0,137,315,59,51⟩,[(4,5)],[(2,3,0),(6,4,4)],⟨11,38,133,28,112,98,465,401,281⟩,⟨11,38,133,28,112,98,192,384,264⟩,[⟨8,1181748490584699499899,⟨11,63,133,63,127,127,255,133,11⟩⟩,⟨4,1210107568097501975188745,⟨11,38,133,47,98,98,230,389,267⟩⟩,⟨7,1369487434082901503771683,⟨267,319,5,28,369,379,64,256,264⟩⟩]⟩
theorem node956 : UpperPrefix a [3,5,7,2,6,1] 30 :=
  Boolean.leaf_sound a [3,5,7,2,6,1] 30 cert956 (by decide +kernel)

def cert957 : Leaf := ⟨⟨436,409,266,419,0,0,267,11,131⟩,[(4,5),(5,4)],[(2,3,0),(6,4,4),(6,4,5)],⟨11,38,133,28,112,112,451,387,267⟩,⟨11,38,133,28,112,112,192,384,264⟩,[⟨4,1214839173152057184224257,⟨463,38,453,12,96,96,192,384,264⟩⟩,⟨5,1214839172027256789009409,⟨463,6,453,28,80,80,192,384,264⟩⟩]⟩
theorem node957 : UpperPrefix a [3,5,7,2,6,4] 30 :=
  Boolean.leaf_sound a [3,5,7,2,6,4] 30 cert957 (by decide +kernel)

def cert958 : Local := ⟨⟨436,409,0,419,0,155,0,59,179⟩,[(2,6),(4,5),(6,2)],[(2,3,0),(6,4,4)]⟩
theorem node958 : UpperPrefix a [3,5,7,2,6,8,0] 30 :=
  local_sound a [3,5,7,2,6,8,0] 30 cert958 (by decide +kernel)

def cert959 : Leaf := ⟨⟨52,25,58,34,0,27,313,59,51⟩,[(4,5)],[(2,3,0),(6,4,4)],⟨11,38,133,28,112,352,194,401,281⟩,⟨11,38,133,28,112,352,194,384,264⟩,[⟨7,1558382096216835125941579,⟨267,319,5,319,369,369,379,257,267⟩⟩,⟨8,1181745671428262356091,⟨11,63,133,31,127,127,207,128,9⟩⟩,⟨0,1210107565286050977809408,⟨10,62,132,28,112,368,202,384,264⟩⟩]⟩
theorem node959 : UpperPrefix a [3,5,7,2,6,8,1] 30 :=
  Boolean.leaf_sound a [3,5,7,2,6,8,1] 30 cert959 (by decide +kernel)

#print axioms node959
end Delivery.FiniteExclusion.Sharp3x6
