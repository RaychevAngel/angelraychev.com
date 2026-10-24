import RegularNineSharp3x6Base
import RegularNineSharp3x6C014
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert960 : Leaf := ⟨⟨180,152,58,160,0,152,296,59,179⟩,[(4,5)],[(2,3,0),(6,4,4)],⟨11,38,133,28,112,352,208,387,267⟩,⟨11,38,133,28,112,352,208,384,264⟩,[⟨0,1210109947703860850068480,⟨26,126,254,94,112,368,240,496,264⟩⟩,⟨8,1181745671436852290683,⟨11,63,133,31,127,127,223,128,9⟩⟩,⟨1,1210109947703860850065409,⟨25,124,253,92,112,368,240,496,264⟩⟩]⟩
theorem node960 : UpperPrefix a [3,5,7,2,6,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,2,6,8,4] 30 cert960 (by decide +kernel)

theorem node961 : UpperPrefix a [3,5,7,2,6,8] 30 :=
  branch_upper a [3,5,7,2,6,8] 30 (by decide) (fin9_cases _
  node958
  node959
  (invalid_upper a [3,5,7,2,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,6,8,3] 30 (by decide +kernel))
  node960
  (invalid_upper a [3,5,7,2,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,6,8,8] 30 (by decide +kernel)))

theorem node962 : UpperPrefix a [3,5,7,2,6] 30 :=
  branch_upper a [3,5,7,2,6] 30 (by decide) (fin9_cases _
  node955
  node956
  (invalid_upper a [3,5,7,2,6,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,6,3] 30 (by decide +kernel))
  node957
  (invalid_upper a [3,5,7,2,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,6,7] 30 (by decide +kernel))
  node961)

def cert963 : Leaf := ⟨⟨100,201,104,352,72,10,40,120,112⟩,[],[(2,3,0),(0,5,1),(1,6,5)],⟨11,38,133,28,304,97,194,464,344⟩,⟨11,38,133,28,304,97,194,384,264⟩,[⟨4,1210109948109167552208137,⟨43,102,231,111,289,99,230,487,299⟩⟩,⟨7,1511158430825188720378947,⟨11,63,5,28,304,369,379,256,264⟩⟩,⟨8,1184128495637889129737,⟨43,102,231,127,49,99,230,231,43⟩⟩]⟩
theorem node963 : UpperPrefix a [3,5,7,2,8,0,1] 30 :=
  Boolean.leaf_sound a [3,5,7,2,8,0,1] 30 cert963 (by decide +kernel)

def cert964 : Leaf := ⟨⟨180,153,58,160,200,152,296,56,240⟩,[],[(2,3,0),(8,4,6),(0,5,1),(1,7,2)],⟨11,38,133,28,304,97,208,386,328⟩,⟨11,38,133,28,304,97,208,386,264⟩,[⟨6,1210253986314947516195961,⟨15,39,133,159,447,47,159,386,269⟩⟩]⟩
theorem node964 : UpperPrefix a [3,5,7,2,8,0,4,1] 30 :=
  Boolean.leaf_sound a [3,5,7,2,8,0,4,1] 30 cert964 (by decide +kernel)

def cert965 : Leaf := ⟨⟨164,137,42,162,138,154,298,42,162⟩,[],[(2,3,0),(8,4,6),(0,5,1)],⟨11,38,133,28,304,97,208,448,266⟩,⟨11,38,133,28,304,97,208,448,264⟩,[⟨6,1450947102991048617509939,⟨283,319,389,285,315,319,413,396,264⟩⟩,⟨4,1252904011533758342652937,⟨267,166,389,271,422,487,194,448,265⟩⟩]⟩
theorem node965 : UpperPrefix a [3,5,7,2,8,0,4,6] 30 :=
  Boolean.leaf_sound a [3,5,7,2,8,0,4,6] 30 cert965 (by decide +kernel)

theorem node966 : UpperPrefix a [3,5,7,2,8,0,4] 30 :=
  branch_upper a [3,5,7,2,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,2,8,0,4,0] 30 (by decide +kernel))
  node964
  (invalid_upper a [3,5,7,2,8,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,4,5] 30 (by decide +kernel))
  node965
  (invalid_upper a [3,5,7,2,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,4,8] 30 (by decide +kernel)))

theorem node967 : UpperPrefix a [3,5,7,2,8,0] 30 :=
  branch_upper a [3,5,7,2,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,2,8,0,0] 30 (by decide +kernel))
  node963
  (invalid_upper a [3,5,7,2,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,3] 30 (by decide +kernel))
  node966
  (invalid_upper a [3,5,7,2,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,0,8] 30 (by decide +kernel)))

def cert968 : Leaf := ⟨⟨372,473,0,352,72,409,0,120,112⟩,[(2,6),(6,2)],[(2,3,0)],⟨11,38,133,28,304,98,193,464,344⟩,⟨11,38,133,28,304,98,193,384,264⟩,[⟨0,1361518440643196416427008,⟨26,446,132,28,432,506,192,384,264⟩⟩,⟨1,1413566019119164909944833,⟨477,508,461,476,440,508,461,384,392⟩⟩,⟨7,1360042701117299652297763,⟨27,319,5,28,305,379,65,256,264⟩⟩]⟩
theorem node968 : UpperPrefix a [3,5,7,2,8,1,0] 30 :=
  Boolean.leaf_sound a [3,5,7,2,8,1,0] 30 cert968 (by decide +kernel)

def cert969 : Leaf := ⟨⟨84,217,88,65,73,153,265,89,81⟩,[],[(2,3,0),(8,4,6)],⟨11,38,133,28,304,98,208,449,329⟩,⟨11,38,133,28,304,98,208,384,264⟩,[⟨1,1233765712716905632235521,⟨477,508,461,476,304,120,208,384,328⟩⟩,⟨5,1441955899393945257116705,⟨463,391,389,476,477,463,476,384,328⟩⟩,⟨7,1360042701117299652297763,⟨27,319,5,28,305,379,80,256,264⟩⟩]⟩
theorem node969 : UpperPrefix a [3,5,7,2,8,1,4] 30 :=
  Boolean.leaf_sound a [3,5,7,2,8,1,4] 30 cert969 (by decide +kernel)

theorem node970 : UpperPrefix a [3,5,7,2,8,1] 30 :=
  branch_upper a [3,5,7,2,8,1] 30 (by decide) (fin9_cases _
  node968
  (invalid_upper a [3,5,7,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,1,3] 30 (by decide +kernel))
  node969
  (invalid_upper a [3,5,7,2,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,1,8] 30 (by decide +kernel)))

def cert971 : Leaf := ⟨⟨196,201,0,195,203,139,0,75,195⟩,[(2,6),(6,2)],[(2,3,0)],⟨11,38,133,28,304,112,193,450,330⟩,⟨11,38,133,28,304,112,193,384,264⟩,[⟨4,1252844293802699487732745,⟨463,102,453,463,486,230,453,452,461⟩⟩,⟨5,1224302459823465158149123,⟨463,463,453,92,280,92,453,384,264⟩⟩,⟨8,1184123851305085064507,⟨43,111,197,127,59,127,197,197,43⟩⟩]⟩
theorem node971 : UpperPrefix a [3,5,7,2,8,4,0] 30 :=
  Boolean.leaf_sound a [3,5,7,2,8,4,0] 30 cert971 (by decide +kernel)

def cert972 : Leaf := ⟨⟨260,393,266,259,75,267,265,75,67⟩,[],[(2,3,0)],⟨11,38,133,28,304,112,194,449,329⟩,⟨11,38,133,28,304,112,194,384,264⟩,[⟨4,1255090437095252741596169,⟨463,230,453,463,486,98,194,388,461⟩⟩,⟨5,1224929577064377244976131,⟨463,463,453,156,280,220,455,384,264⟩⟩,⟨7,1511158430825188720378947,⟨11,63,5,28,304,369,379,256,264⟩⟩,⟨6,1210106412362351391032371,⟨11,47,133,29,315,63,135,384,264⟩⟩]⟩
theorem node972 : UpperPrefix a [3,5,7,2,8,4,1] 30 :=
  Boolean.leaf_sound a [3,5,7,2,8,4,1] 30 cert972 (by decide +kernel)

theorem node973 : UpperPrefix a [3,5,7,2,8,4] 30 :=
  branch_upper a [3,5,7,2,8,4] 30 (by decide) (fin9_cases _
  node971
  node972
  (invalid_upper a [3,5,7,2,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,4,8] 30 (by decide +kernel)))

theorem node974 : UpperPrefix a [3,5,7,2,8] 30 :=
  branch_upper a [3,5,7,2,8] 30 (by decide) (fin9_cases _
  node967
  node970
  (invalid_upper a [3,5,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,3] 30 (by decide +kernel))
  node973
  (invalid_upper a [3,5,7,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,8,8] 30 (by decide +kernel)))

theorem node975 : UpperPrefix a [3,5,7,2] 30 :=
  branch_upper a [3,5,7,2] 30 (by decide) (fin9_cases _
  node948
  node954
  (invalid_upper a [3,5,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,2,5] 30 (by decide +kernel))
  node962
  (invalid_upper a [3,5,7,2,7] 30 (by decide +kernel))
  node974)

def cert976 : Leaf := ⟨⟨48,153,24,1,74,157,285,29,21⟩,[],[(1,5,4)],⟨11,38,133,88,49,98,468,404,284⟩,⟨11,38,133,88,49,98,192,384,264⟩,[⟨8,1181748227455407150459,⟨59,63,149,127,59,127,255,149,59⟩⟩,⟨5,1323666153021274158531585,⟨463,6,133,476,477,66,192,384,456⟩⟩,⟨6,1247959131201599148663817,⟨399,38,133,415,55,34,128,388,397⟩⟩,⟨7,1218371706631214322418723,⟨283,319,5,88,57,379,64,256,264⟩⟩,⟨2,1210107565286192442246179,⟨27,59,129,88,57,123,192,384,264⟩⟩]⟩
theorem node976 : UpperPrefix a [3,5,7,6,0,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,1] 30 cert976 (by decide +kernel)

def cert977 : Leaf := ⟨⟨48,0,58,34,74,155,314,58,50⟩,[(1,5)],[(7,2,5),(2,5,1)],⟨11,38,133,88,49,100,466,402,282⟩,⟨11,38,133,88,49,100,192,384,264⟩,[⟨8,1181748227455407150459,⟨59,63,149,127,59,127,255,149,59⟩⟩,⟨0,1285813291192733985162240,⟨10,38,132,472,506,102,192,384,264⟩⟩,⟨6,1247959131201599148680201,⟨399,38,133,415,55,38,128,388,397⟩⟩]⟩
theorem node977 : UpperPrefix a [3,5,7,6,0,2] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,2] 30 cert977 (by decide +kernel)

def cert978 : Leaf := ⟨⟨388,393,266,0,462,0,271,15,135⟩,[(3,5),(5,3)],[],⟨11,38,133,88,49,112,454,390,270⟩,⟨11,38,133,88,49,112,192,384,264⟩,[⟨4,1252839898289463161545737,⟨463,38,453,463,487,230,192,388,461⟩⟩,⟨5,1224302387765873255121923,⟨463,463,453,92,477,92,192,384,264⟩⟩,⟨6,1252838295009095329276937,⟨399,38,389,415,439,182,128,388,397⟩⟩]⟩
theorem node978 : UpperPrefix a [3,5,7,6,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,4] 30 cert978 (by decide +kernel)

def cert979 : Leaf := ⟨⟨48,153,24,3,72,29,285,29,21⟩,[],[],⟨11,38,133,88,49,352,194,404,284⟩,⟨11,38,133,88,49,352,194,384,264⟩,[⟨1,1252876341700290982182913,⟨445,164,405,508,437,352,192,384,424⟩⟩,⟨5,1323665738690108440445953,⟨463,6,197,476,477,320,194,384,392⟩⟩,⟨6,1247959131201599148680201,⟨399,38,133,415,55,294,130,388,397⟩⟩,⟨7,1218371708887970528363587,⟨283,319,5,121,57,377,379,256,280⟩⟩,⟨8,1181745671571875316851,⟨27,63,133,93,59,127,223,128,8⟩⟩,⟨2,1210107565286201032180803,⟨27,59,129,89,57,377,219,384,264⟩⟩]⟩
theorem node979 : UpperPrefix a [3,5,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,8,1] 30 cert979 (by decide +kernel)

def cert980 : Leaf := ⟨⟨356,321,354,293,324,5,0,101,117⟩,[(6,2)],[(7,2,6),(1,7,2)],⟨11,38,133,88,49,352,196,386,280⟩,⟨11,38,133,88,49,352,196,386,264⟩,[⟨3,1210403114009671683320833,⟨67,246,247,86,247,482,246,482,256⟩⟩,⟨4,1212771800246712498646281,⟨75,230,231,79,231,487,230,487,495⟩⟩]⟩
theorem node980 : UpperPrefix a [3,5,7,6,0,8,2,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,8,2,1] 30 cert980 (by decide +kernel)

def cert981 : Leaf := ⟨⟨292,264,314,295,334,14,0,46,38⟩,[(6,2)],[(7,2,6)],⟨11,38,133,88,49,352,196,400,266⟩,⟨11,38,133,88,49,352,196,400,264⟩,[⟨6,1252829071637058474501129,⟨399,38,389,415,439,294,132,406,397⟩⟩,⟨0,1252830297038369510689792,⟨426,102,486,506,432,354,230,400,424⟩⟩,⟨4,1252608936108385484442633,⟨299,102,487,363,289,354,230,384,297⟩⟩]⟩
theorem node981 : UpperPrefix a [3,5,7,6,0,8,2,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,8,2,4] 30 cert981 (by decide +kernel)

theorem node982 : UpperPrefix a [3,5,7,6,0,8,2] 30 :=
  branch_upper a [3,5,7,6,0,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,6,0,8,2,0] 30 (by decide +kernel))
  node980
  (invalid_upper a [3,5,7,6,0,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,2,3] 30 (by decide +kernel))
  node981
  (invalid_upper a [3,5,7,6,0,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,2,8] 30 (by decide +kernel)))

def cert983 : Leaf := ⟨⟨420,385,290,0,452,133,293,37,165⟩,[(3,6)],[(4,6,3),(1,7,2)],⟨11,38,133,88,49,352,208,386,268⟩,⟨11,38,133,88,49,352,208,386,264⟩,[⟨3,1210403114009671683320833,⟨67,246,247,86,247,482,246,482,256⟩⟩,⟨6,1253133442914274682102793,⟨399,166,389,415,439,422,150,390,397⟩⟩]⟩
theorem node983 : UpperPrefix a [3,5,7,6,0,8,4,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,8,4,1] 30 cert983 (by decide +kernel)

def cert984 : Leaf := ⟨⟨416,385,298,0,450,131,291,43,163⟩,[(3,6)],[(4,6,3)],⟨11,38,133,88,49,352,208,388,266⟩,⟨11,38,133,88,49,352,208,388,264⟩,[⟨2,1224277047348277343683587,⟨315,379,505,88,305,360,248,504,264⟩⟩,⟨6,1255531519643856923812873,⟨399,166,389,415,439,422,150,388,397⟩⟩,⟨3,1210109947688328369343489,⟨3,118,247,80,49,352,242,502,256⟩⟩]⟩
theorem node984 : UpperPrefix a [3,5,7,6,0,8,4,2] 30 :=
  Boolean.leaf_sound a [3,5,7,6,0,8,4,2] 30 cert984 (by decide +kernel)

theorem node985 : UpperPrefix a [3,5,7,6,0,8,4] 30 :=
  branch_upper a [3,5,7,6,0,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,6,0,8,4,0] 30 (by decide +kernel))
  node983
  node984
  (invalid_upper a [3,5,7,6,0,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,4,8] 30 (by decide +kernel)))

theorem node986 : UpperPrefix a [3,5,7,6,0,8] 30 :=
  branch_upper a [3,5,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,6,0,8,0] 30 (by decide +kernel))
  node979
  node982
  (invalid_upper a [3,5,7,6,0,8,3] 30 (by decide +kernel))
  node985
  (invalid_upper a [3,5,7,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,8,8] 30 (by decide +kernel)))

theorem node987 : UpperPrefix a [3,5,7,6,0] 30 :=
  branch_upper a [3,5,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,6,0,0] 30 (by decide +kernel))
  node976
  node977
  (invalid_upper a [3,5,7,6,0,3] 30 (by decide +kernel))
  node978
  (invalid_upper a [3,5,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,0,7] 30 (by decide +kernel))
  node986)

def cert988 : Leaf := ⟨⟨20,153,26,6,0,30,286,30,22⟩,[(4,1)],[(5,1,4),(0,5,1)],⟨11,38,133,88,50,97,468,404,284⟩,⟨11,38,133,88,50,97,192,384,264⟩,[⟨6,1252985868964021472093193,⟨415,182,389,415,182,439,128,388,397⟩⟩,⟨8,1181748227455407150459,⟨59,63,149,127,59,127,255,149,59⟩⟩,⟨7,1218371706910558995350547,⟨315,319,21,121,315,121,64,256,296⟩⟩]⟩
theorem node988 : UpperPrefix a [3,5,7,6,1,0] 30 :=
  Boolean.leaf_sound a [3,5,7,6,1,0] 30 cert988 (by decide +kernel)

def cert989 : Leaf := ⟨⟨80,0,90,3,0,155,283,91,83⟩,[(1,5),(4,1)],[(5,1,4),(7,2,5),(2,5,1),(2,5,4)],⟨11,38,133,88,50,100,465,401,281⟩,⟨11,38,133,88,50,100,192,384,264⟩,[⟨8,1181748227455407150459,⟨59,63,149,127,59,127,255,149,59⟩⟩]⟩
theorem node989 : UpperPrefix a [3,5,7,6,1,2] 30 :=
  Boolean.leaf_sound a [3,5,7,6,1,2] 30 cert989 (by decide +kernel)

def cert990 : Leaf := ⟨⟨468,473,344,0,0,0,285,93,213⟩,[(3,5),(4,1),(5,3)],[(5,1,4)],⟨11,38,133,88,50,112,453,389,269⟩,⟨11,38,133,88,50,112,192,384,264⟩,[⟨1,1214876138980377424560129,⟨493,236,453,120,56,120,192,384,296⟩⟩]⟩
theorem node990 : UpperPrefix a [3,5,7,6,1,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,1,4] 30 cert990 (by decide +kernel)

def cert991 : Leaf := ⟨⟨468,409,0,391,0,157,0,29,149⟩,[(2,6),(4,1),(6,2)],[(5,1,4)],⟨11,38,133,88,50,352,193,404,284⟩,⟨11,38,133,88,50,352,193,384,264⟩,[⟨1,1247960374511755599282177,⟨493,100,229,508,48,356,229,384,424⟩⟩,⟨6,1252985868964021411267585,⟨415,182,389,412,178,438,389,384,392⟩⟩]⟩
theorem node991 : UpperPrefix a [3,5,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [3,5,7,6,1,8,0] 30 cert991 (by decide +kernel)

def cert992 : Leaf := ⟨⟨340,345,282,263,0,31,0,27,19⟩,[(4,1),(6,2)],[(5,1,4),(7,2,6)],⟨11,38,133,88,50,352,196,401,281⟩,⟨11,38,133,88,50,352,196,384,264⟩,[⟨6,1214838002217391018476545,⟨415,54,389,24,50,288,132,384,264⟩⟩,⟨2,1214839155138895624012801,⟨411,50,385,88,50,352,192,384,264⟩⟩]⟩
theorem node992 : UpperPrefix a [3,5,7,6,1,8,2] 30 :=
  Boolean.leaf_sound a [3,5,7,6,1,8,2] 30 cert992 (by decide +kernel)

def cert993 : Leaf := ⟨⟨452,457,328,0,0,143,271,77,197⟩,[(3,6),(4,1)],[(5,1,4),(4,6,3)],⟨11,38,133,88,50,352,208,389,269⟩,⟨11,38,133,88,50,352,208,384,264⟩,[⟨1,1214876048626914195406849,⟨397,164,389,88,48,360,216,384,264⟩⟩]⟩
theorem node993 : UpperPrefix a [3,5,7,6,1,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,1,8,4] 30 cert993 (by decide +kernel)

theorem node994 : UpperPrefix a [3,5,7,6,1,8] 30 :=
  branch_upper a [3,5,7,6,1,8] 30 (by decide) (fin9_cases _
  node991
  (invalid_upper a [3,5,7,6,1,8,1] 30 (by decide +kernel))
  node992
  (invalid_upper a [3,5,7,6,1,8,3] 30 (by decide +kernel))
  node993
  (invalid_upper a [3,5,7,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,1,8,8] 30 (by decide +kernel)))

theorem node995 : UpperPrefix a [3,5,7,6,1] 30 :=
  branch_upper a [3,5,7,6,1] 30 (by decide) (fin9_cases _
  node988
  (invalid_upper a [3,5,7,6,1,1] 30 (by decide +kernel))
  node989
  (invalid_upper a [3,5,7,6,1,3] 30 (by decide +kernel))
  node990
  (invalid_upper a [3,5,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,1,7] 30 (by decide +kernel))
  node994)

def cert996 : Leaf := ⟨⟨52,0,58,166,0,30,318,62,54⟩,[(1,4),(4,1)],[(0,5,1),(0,5,4)],⟨11,38,133,88,52,97,466,402,282⟩,⟨11,38,133,88,52,97,192,384,264⟩,[⟨6,1252985868964021472093193,⟨415,182,389,415,182,439,128,388,397⟩⟩,⟨8,1181748209794501637499,⟨59,63,133,127,63,127,255,133,59⟩⟩,⟨7,1251428272290573497410569,⟨315,54,261,379,54,353,64,256,297⟩⟩]⟩
theorem node996 : UpperPrefix a [3,5,7,6,2,0] 30 :=
  Boolean.leaf_sound a [3,5,7,6,2,0] 30 cert996 (by decide +kernel)

def cert997 : Leaf := ⟨⟨52,0,56,37,0,29,317,61,53⟩,[(1,4),(4,1)],[],⟨11,38,133,88,52,98,465,401,281⟩,⟨11,38,133,88,52,98,192,384,264⟩,[⟨1,1214839173153298563989505,⟨477,60,461,88,60,120,192,384,264⟩⟩,⟨6,1252690721056643087606793,⟨415,54,389,415,54,50,128,388,397⟩⟩,⟨7,1487546596434060053062715,⟨315,319,261,379,319,379,64,256,297⟩⟩,⟨8,1181748209794501637499,⟨59,63,133,127,63,127,255,133,59⟩⟩]⟩
theorem node997 : UpperPrefix a [3,5,7,6,2,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,2,1] 30 cert997 (by decide +kernel)

def cert998 : Leaf := ⟨⟨484,0,362,0,0,0,303,111,231⟩,[(1,4),(3,5),(4,1),(5,3)],[],⟨11,38,133,88,52,112,451,387,267⟩,⟨11,38,133,88,52,112,192,384,264⟩,[⟨4,1252692036106497329210377,⟨463,38,453,463,38,98,192,388,461⟩⟩]⟩
theorem node998 : UpperPrefix a [3,5,7,6,2,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,2,4] 30 cert998 (by decide +kernel)

def cert999 : Leaf := ⟨⟨500,0,0,423,0,158,0,126,246⟩,[(1,4),(2,6),(4,1),(6,2)],[],⟨11,38,133,88,52,352,193,402,282⟩,⟨11,38,133,88,52,352,193,384,264⟩,[⟨0,1252691876511422415381504,⟨442,54,388,506,54,352,480,384,424⟩⟩]⟩
theorem node999 : UpperPrefix a [3,5,7,6,2,8,0] 30 :=
  Boolean.leaf_sound a [3,5,7,6,2,8,0] 30 cert999 (by decide +kernel)

def cert1000 : Leaf := ⟨⟨52,0,56,37,0,31,317,61,53⟩,[(1,4),(4,1)],[],⟨11,38,133,88,52,352,194,401,281⟩,⟨11,38,133,88,52,352,194,384,264⟩,[⟨1,1214839155138904215257089,⟨413,52,389,88,52,360,216,384,264⟩⟩,⟨6,1252690721058842110878729,⟨415,54,389,415,54,310,146,388,397⟩⟩,⟨7,1553659729446039194707017,⟨315,54,261,379,54,361,379,256,297⟩⟩,⟨8,1181745671571875325051,⟨27,63,133,95,63,127,223,128,9⟩⟩]⟩
theorem node1000 : UpperPrefix a [3,5,7,6,2,8,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,2,8,1] 30 cert1000 (by decide +kernel)

def cert1001 : Leaf := ⟨⟨420,0,298,0,0,143,303,47,167⟩,[(1,4),(3,6),(4,1)],[(4,6,3)],⟨11,38,133,88,52,352,208,387,267⟩,⟨11,38,133,88,52,352,208,384,264⟩,[⟨6,1252690721058842110878729,⟨415,54,389,415,54,310,146,388,397⟩⟩]⟩
theorem node1001 : UpperPrefix a [3,5,7,6,2,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,2,8,4] 30 cert1001 (by decide +kernel)

theorem node1002 : UpperPrefix a [3,5,7,6,2,8] 30 :=
  branch_upper a [3,5,7,6,2,8] 30 (by decide) (fin9_cases _
  node999
  node1000
  (invalid_upper a [3,5,7,6,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,2,8,3] 30 (by decide +kernel))
  node1001
  (invalid_upper a [3,5,7,6,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,2,8,8] 30 (by decide +kernel)))

theorem node1003 : UpperPrefix a [3,5,7,6,2] 30 :=
  branch_upper a [3,5,7,6,2] 30 (by decide) (fin9_cases _
  node996
  node997
  (invalid_upper a [3,5,7,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,2,3] 30 (by decide +kernel))
  node998
  (invalid_upper a [3,5,7,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,2,7] 30 (by decide +kernel))
  node1002)

def cert1004 : Leaf := ⟨⟨308,385,312,292,76,262,292,60,52⟩,[],[(0,5,1),(1,6,5)],⟨11,38,133,88,304,97,194,404,284⟩,⟨11,38,133,88,304,97,194,384,264⟩,[⟨6,1248106705154188825093129,⟨399,38,133,415,438,39,130,388,397⟩⟩,⟨7,1218371709184357631525955,⟨315,319,21,121,312,121,379,272,312⟩⟩,⟨3,1210107637482182138661889,⟨3,102,231,80,304,97,194,384,256⟩⟩,⟨4,1210107637481083700775937,⟨11,102,231,72,288,97,194,384,264⟩⟩]⟩
theorem node1004 : UpperPrefix a [3,5,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,0,1] 30 cert1004 (by decide +kernel)

def cert1005 : Leaf := ⟨⟨304,281,314,290,74,286,0,58,50⟩,[(6,2)],[(7,2,6),(0,5,1)],⟨11,38,133,88,304,97,196,402,282⟩,⟨11,38,133,88,304,97,196,384,264⟩,[⟨2,1224302334850911942214659,⟨411,443,385,88,312,505,192,384,264⟩⟩,⟨6,1248106705154188825093129,⟨399,38,133,415,438,39,132,388,397⟩⟩]⟩
theorem node1005 : UpperPrefix a [3,5,7,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,0,2] 30 cert1005 (by decide +kernel)

def cert1006 : Leaf := ⟨⟨164,137,42,0,142,142,302,46,166⟩,[(3,6)],[(8,4,6),(0,5,1),(4,6,3)],⟨11,38,133,88,304,97,208,390,270⟩,⟨11,38,133,88,304,97,208,384,264⟩,[⟨6,1253133442916473709552649,⟨399,182,389,415,438,439,146,388,397⟩⟩]⟩
theorem node1006 : UpperPrefix a [3,5,7,6,8,0,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,0,4] 30 cert1006 (by decide +kernel)

theorem node1007 : UpperPrefix a [3,5,7,6,8,0] 30 :=
  branch_upper a [3,5,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,6,8,0,0] 30 (by decide +kernel))
  node1004
  node1005
  (invalid_upper a [3,5,7,6,8,0,3] 30 (by decide +kernel))
  node1006
  (invalid_upper a [3,5,7,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,0,8] 30 (by decide +kernel)))

def cert1008 : Leaf := ⟨⟨308,409,0,292,76,413,0,60,52⟩,[(2,6),(6,2)],[],⟨11,38,133,88,304,98,193,404,284⟩,⟨11,38,133,88,304,98,193,384,264⟩,[⟨0,1219570744996005443273728,⟨410,446,132,88,312,506,192,384,264⟩⟩,⟨1,1413566019119164909944833,⟨477,508,461,476,440,508,461,384,392⟩⟩,⟨6,1248106705154188841870345,⟨399,38,133,415,438,38,133,388,397⟩⟩,⟨7,1218371706631214322418723,⟨283,319,5,88,313,379,65,256,264⟩⟩]⟩
theorem node1008 : UpperPrefix a [3,5,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,1,0] 30 cert1008 (by decide +kernel)

def cert1009 : Leaf := ⟨⟨304,272,314,291,66,276,0,59,51⟩,[(6,2)],[(7,2,6),(2,6,5)],⟨11,38,133,88,304,98,196,401,281⟩,⟨11,38,133,88,304,98,196,384,264⟩,[⟨6,1247959131201599148663817,⟨399,38,133,415,310,34,132,388,397⟩⟩,⟨0,1210107640103418933054464,⟨42,102,230,122,304,98,230,400,312⟩⟩,⟨3,1210107640103417859312641,⟨35,102,231,114,304,98,230,400,304⟩⟩]⟩
theorem node1009 : UpperPrefix a [3,5,7,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,1,2] 30 cert1009 (by decide +kernel)

def cert1010 : Leaf := ⟨⟨196,201,72,0,205,141,269,77,197⟩,[(3,6)],[(8,4,6),(4,6,3)],⟨11,38,133,88,304,98,208,389,269⟩,⟨11,38,133,88,304,98,208,384,264⟩,[⟨1,1233765568601730441281537,⟨477,508,461,88,312,120,216,384,264⟩⟩,⟨5,1442011239626166385771553,⟨463,391,389,476,477,463,476,384,328⟩⟩]⟩
theorem node1010 : UpperPrefix a [3,5,7,6,8,1,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,1,4] 30 cert1010 (by decide +kernel)

theorem node1011 : UpperPrefix a [3,5,7,6,8,1] 30 :=
  branch_upper a [3,5,7,6,8,1] 30 (by decide) (fin9_cases _
  node1008
  (invalid_upper a [3,5,7,6,8,1,1] 30 (by decide +kernel))
  node1009
  (invalid_upper a [3,5,7,6,8,1,3] 30 (by decide +kernel))
  node1010
  (invalid_upper a [3,5,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,1,8] 30 (by decide +kernel)))

def cert1012 : Local := ⟨⟨368,0,0,290,74,411,0,122,114⟩,[(1,5),(2,6),(6,2)],[(7,2,5),(2,5,1),(0,6,5)]⟩
theorem node1012 : UpperPrefix a [3,5,7,6,8,2,0] 30 :=
  local_sound a [3,5,7,6,8,2,0] 30 cert1012 (by decide +kernel)

def cert1013 : Leaf := ⟨⟨304,0,314,291,75,386,288,59,51⟩,[(1,5)],[(7,2,5),(2,5,1)],⟨11,38,133,88,304,100,194,401,281⟩,⟨11,38,133,88,304,100,194,384,264⟩,[⟨6,1247959131201599148680201,⟨399,38,133,415,310,38,130,388,397⟩⟩,⟨0,1210107637552551956597760,⟨42,102,230,88,306,102,226,384,264⟩⟩,⟨3,1210107637552550882855937,⟨35,102,231,80,306,102,226,384,256⟩⟩,⟨4,1210107637551452444969985,⟨43,102,231,72,290,102,226,384,264⟩⟩]⟩
theorem node1013 : UpperPrefix a [3,5,7,6,8,2,1] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,2,1] 30 cert1013 (by decide +kernel)

def cert1014 : Local := ⟨⟨96,0,106,0,75,139,299,107,99⟩,[(1,5),(3,6)],[(7,2,5),(8,4,6),(2,5,1),(4,6,3)]⟩
theorem node1014 : UpperPrefix a [3,5,7,6,8,2,4] 30 :=
  local_sound a [3,5,7,6,8,2,4] 30 cert1014 (by decide +kernel)

theorem node1015 : UpperPrefix a [3,5,7,6,8,2] 30 :=
  branch_upper a [3,5,7,6,8,2] 30 (by decide) (fin9_cases _
  node1012
  node1013
  (invalid_upper a [3,5,7,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,2,3] 30 (by decide +kernel))
  node1014
  (invalid_upper a [3,5,7,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,2,8] 30 (by decide +kernel)))

def cert1016 : Leaf := ⟨⟨388,393,266,0,207,0,271,15,135⟩,[(3,5),(5,3)],[],⟨11,38,133,88,304,112,199,391,271⟩,⟨11,38,133,88,304,112,192,384,264⟩,[⟨4,1252692036106497329210377,⟨463,38,453,463,294,98,192,388,461⟩⟩,⟨5,1224302387765871103443971,⟨463,463,453,88,280,88,192,384,264⟩⟩,⟨6,1252690721056505648653321,⟨399,38,389,415,310,50,128,388,397⟩⟩]⟩
theorem node1016 : UpperPrefix a [3,5,7,6,8,4] 30 :=
  Boolean.leaf_sound a [3,5,7,6,8,4] 30 cert1016 (by decide +kernel)

theorem node1017 : UpperPrefix a [3,5,7,6,8] 30 :=
  branch_upper a [3,5,7,6,8] 30 (by decide) (fin9_cases _
  node1007
  node1011
  node1015
  (invalid_upper a [3,5,7,6,8,3] 30 (by decide +kernel))
  node1016
  (invalid_upper a [3,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,8,8] 30 (by decide +kernel)))

theorem node1018 : UpperPrefix a [3,5,7,6] 30 :=
  branch_upper a [3,5,7,6] 30 (by decide) (fin9_cases _
  node987
  node995
  node1003
  (invalid_upper a [3,5,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,6,7] 30 (by decide +kernel))
  node1017)

def cert1019 : Leaf := ⟨⟨368,337,344,65,322,277,0,89,81⟩,[(6,2)],[(7,2,6),(1,5,4),(2,6,5)],⟨11,38,133,280,49,98,196,464,344⟩,⟨11,38,133,280,49,98,196,384,264⟩,[⟨5,1323666243093266705941505,⟨463,70,197,476,477,66,196,384,456⟩⟩,⟨3,1210107639804694293941249,⟨51,118,247,272,49,98,246,384,256⟩⟩]⟩
theorem node1019 : UpperPrefix a [3,5,7,8,0,1,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,0,1,2] 30 cert1019 (by decide +kernel)

def cert1020 : Leaf := ⟨⟨448,449,328,193,450,385,257,73,209⟩,[],[(1,5,4)],⟨11,38,133,280,49,98,208,388,328⟩,⟨11,38,133,280,49,98,208,388,264⟩,[⟨2,2296251928474254019920931,⟨315,379,473,280,313,379,472,456,264⟩⟩,⟨5,1782685709179434385015841,⟨463,391,389,476,477,463,476,388,456⟩⟩,⟨4,1212542537752281718465545,⟨143,38,133,399,39,98,226,388,397⟩⟩,⟨3,1210109950151303135038465,⟨51,118,247,272,49,98,242,502,256⟩⟩]⟩
theorem node1020 : UpperPrefix a [3,5,7,8,0,1,4,2] 30 :=
  Boolean.leaf_sound a [3,5,7,8,0,1,4,2] 30 cert1020 (by decide +kernel)

def cert1021 : Leaf := ⟨⟨404,400,272,133,390,404,260,20,149⟩,[],[(1,5,4)],⟨11,38,133,280,49,98,208,448,268⟩,⟨11,38,133,280,49,98,208,448,264⟩,[⟨3,1212542773031619842551297,⟨247,118,247,498,119,98,242,480,480⟩⟩,⟨5,1784991552188648078967841,⟨463,391,389,476,477,463,476,456,456⟩⟩,⟨6,2296250703424717392462899,⟨283,319,397,281,315,319,413,396,264⟩⟩,⟨0,1212542679651953794878464,⟨234,38,166,472,48,98,208,448,456⟩⟩]⟩
theorem node1021 : UpperPrefix a [3,5,7,8,0,1,4,6] 30 :=
  Boolean.leaf_sound a [3,5,7,8,0,1,4,6] 30 cert1021 (by decide +kernel)

theorem node1022 : UpperPrefix a [3,5,7,8,0,1,4] 30 :=
  branch_upper a [3,5,7,8,0,1,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,0,1,4,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,4,1] 30 (by decide +kernel))
  node1020
  (invalid_upper a [3,5,7,8,0,1,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,4,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,4,5] 30 (by decide +kernel))
  node1021
  (invalid_upper a [3,5,7,8,0,1,4,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,4,8] 30 (by decide +kernel)))

theorem node1023 : UpperPrefix a [3,5,7,8,0,1] 30 :=
  branch_upper a [3,5,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,1] 30 (by decide +kernel))
  node1019
  (invalid_upper a [3,5,7,8,0,1,3] 30 (by decide +kernel))
  node1022
  (invalid_upper a [3,5,7,8,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,7,8,0,1,8] 30 (by decide +kernel)))

#print axioms node1023
end Delivery.FiniteExclusion.Sharp3x6
