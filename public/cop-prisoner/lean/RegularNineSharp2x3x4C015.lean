import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C013
import RegularNineSharp2x3x4C014
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert960 : Leaf := ⟨⟨200,104,226,0,234,138,298,106,202⟩,[(3,6)],[(8,4,6),(4,6,3)],⟨35,131,13,88,276,100,208,394,298⟩,⟨35,131,13,88,276,100,208,384,288⟩,[⟨0,1214839227900330112975872,⟨426,386,508,120,380,124,248,384,296⟩⟩,⟨2,1361666446939024326354721,⟨419,131,75,218,475,491,218,387,419⟩⟩]⟩
theorem node960 : UpperPrefix a [5,7,0,6,8,2,4] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,2,4] 30 cert960 (by decide +kernel)

theorem node961 : UpperPrefix a [5,7,0,6,8,2] 30 :=
  branch_upper a [5,7,0,6,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,8,2,0] 30 (by decide +kernel))
  node956
  (invalid_upper a [5,7,0,6,8,2,2] 30 (by decide +kernel))
  node959
  node960
  (invalid_upper a [5,7,0,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,8] 30 (by decide +kernel)))

def cert962 : Leaf := ⟨⟨284,316,306,295,42,0,0,62,30⟩,[(5,3),(6,1)],[(7,1,6),(6,3,5)],⟨35,131,13,88,276,104,194,404,308⟩,⟨35,131,13,88,276,104,194,384,288⟩,[⟨0,1229181534966614236070912,⟨98,194,444,248,404,104,194,384,288⟩⟩]⟩
theorem node962 : UpperPrefix a [5,7,0,6,8,3,1] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,3,1] 30 cert962 (by decide +kernel)

def cert963 : Leaf := ⟨⟨408,312,432,420,168,0,312,56,152⟩,[(5,3)],[(6,3,5),(2,6,3),(1,7,1)],⟨35,131,13,88,276,104,196,386,304⟩,⟨35,131,13,88,276,104,196,386,288⟩,[⟨0,1795690307830969311167488,⟨426,130,508,376,380,376,508,386,296⟩⟩]⟩
theorem node963 : UpperPrefix a [5,7,0,6,8,3,2,1] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,3,2,1] 30 cert963 (by decide +kernel)

def cert964 : Local := ⟨⟨152,56,178,167,171,0,59,0,155⟩,[(5,3),(7,4)],[(6,3,5),(8,4,7),(2,6,3)]⟩
theorem node964 : UpperPrefix a [5,7,0,6,8,3,2,4] 30 :=
  local_sound a [5,7,0,6,8,3,2,4] 30 cert964 (by decide +kernel)

theorem node965 : UpperPrefix a [5,7,0,6,8,3,2] 30 :=
  branch_upper a [5,7,0,6,8,3,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,8,3,2,0] 30 (by decide +kernel))
  node963
  (invalid_upper a [5,7,0,6,8,3,2,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,3,2,3] 30 (by decide +kernel))
  node964
  (invalid_upper a [5,7,0,6,8,3,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,3,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,3,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,3,2,8] 30 (by decide +kernel)))

def cert966 : Local := ⟨⟨140,44,162,0,171,0,303,47,143⟩,[(3,6),(5,3)],[(6,3,5),(8,4,6),(4,6,3),(4,6,5)]⟩
theorem node966 : UpperPrefix a [5,7,0,6,8,3,4] 30 :=
  local_sound a [5,7,0,6,8,3,4] 30 cert966 (by decide +kernel)

theorem node967 : UpperPrefix a [5,7,0,6,8,3] 30 :=
  branch_upper a [5,7,0,6,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,8,3,0] 30 (by decide +kernel))
  node962
  node965
  (invalid_upper a [5,7,0,6,8,3,3] 30 (by decide +kernel))
  node966
  (invalid_upper a [5,7,0,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,3,8] 30 (by decide +kernel)))

def cert968 : Leaf := ⟨⟨348,380,368,0,105,0,0,125,93⟩,[(3,5),(5,3),(6,1)],[(7,1,6)],⟨35,131,13,88,276,112,194,396,300⟩,⟨35,131,13,88,276,112,194,384,288⟩,[⟨1,1233765517092152897961985,⟨445,405,445,120,404,120,248,384,296⟩⟩]⟩
theorem node968 : UpperPrefix a [5,7,0,6,8,4,1] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,4,1] 30 cert968 (by decide +kernel)

def cert969 : Leaf := ⟨⟨472,376,336,0,106,0,280,122,90⟩,[(3,5),(5,3)],[(2,6,3),(2,6,5)],⟨35,131,13,88,276,112,196,394,298⟩,⟨35,131,13,88,276,112,196,384,288⟩,[⟨0,1214839230433604903371776,⟨426,386,508,120,380,120,252,384,296⟩⟩,⟨7,1213649342679772631925761,⟨319,279,317,120,276,120,124,256,296⟩⟩,⟨1,1210107601594127977021441,⟨109,197,45,120,276,120,196,384,296⟩⟩,⟨5,1210107600186753093469185,⟨79,199,13,88,276,88,196,384,264⟩⟩]⟩
theorem node969 : UpperPrefix a [5,7,0,6,8,4,2] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,4,2] 30 cert969 (by decide +kernel)

def cert970 : Leaf := ⟨⟨388,292,370,0,99,0,295,39,87⟩,[(3,5),(5,3)],[],⟨35,131,13,88,276,112,200,390,294⟩,⟨35,131,13,88,276,112,200,384,288⟩,[⟨3,1229181498937816143494509,⟨35,131,439,243,407,243,227,387,291⟩⟩,⟨4,1210255283350529926849825,⟨35,131,77,202,391,227,202,387,291⟩⟩,⟨6,1210253986314936755774753,⟨35,131,13,154,407,179,138,387,291⟩⟩,⟨7,1213649340427964228305921,⟨319,279,317,120,276,120,104,256,296⟩⟩]⟩
theorem node970 : UpperPrefix a [5,7,0,6,8,4,3] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,4,3] 30 cert970 (by decide +kernel)

theorem node971 : UpperPrefix a [5,7,0,6,8,4] 30 :=
  branch_upper a [5,7,0,6,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,8,4,0] 30 (by decide +kernel))
  node968
  node969
  node970
  (invalid_upper a [5,7,0,6,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,4,8] 30 (by decide +kernel)))

theorem node972 : UpperPrefix a [5,7,0,6,8] 30 :=
  branch_upper a [5,7,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,8,0] 30 (by decide +kernel))
  node953
  node961
  node967
  node971
  (invalid_upper a [5,7,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,8] 30 (by decide +kernel)))

theorem node973 : UpperPrefix a [5,7,0,6] 30 :=
  branch_upper a [5,7,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [5,7,0,6,1] [5,7,0,1,8] 30 (by decide +kernel) node915)
  (invalid_upper a [5,7,0,6,2] 30 (by decide +kernel))
  node952
  (invalid_upper a [5,7,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,7] 30 (by decide +kernel))
  node972)

def cert974 : Leaf := ⟨⟨0,368,368,101,0,401,309,117,85⟩,[(0,5),(4,2)],[(7,1,5),(3,4,4),(1,5,0)],⟨35,131,13,280,28,98,212,468,372⟩,⟨35,131,13,280,28,98,192,384,288⟩,[⟨2,1210107567535651498787937,⟨35,131,9,280,24,99,227,384,289⟩⟩]⟩
theorem node974 : UpperPrefix a [5,7,0,8,3,1] 30 :=
  Boolean.leaf_sound a [5,7,0,8,3,1] 30 cert974 (by decide +kernel)

def cert975 : Leaf := ⟨⟨340,372,368,101,0,273,0,117,85⟩,[(4,2),(6,1)],[(7,1,6),(3,4,4)],⟨35,131,13,280,28,100,194,464,368⟩,⟨35,131,13,280,28,100,194,384,288⟩,[⟨1,1664340193613800984543233,⟨445,157,29,280,28,508,508,392,440⟩⟩]⟩
theorem node975 : UpperPrefix a [5,7,0,8,3,2,1] 30 :=
  Boolean.leaf_sound a [5,7,0,8,3,2,1] 30 cert975 (by decide +kernel)

def cert976 : Leaf := ⟨⟨448,352,482,230,0,402,290,98,194⟩,[(4,2)],[(3,4,4)],⟨35,131,13,280,28,100,208,450,354⟩,⟨35,131,13,280,28,100,208,384,288⟩,[⟨0,1214857692661020816835584,⟨506,458,508,312,124,124,240,392,312⟩⟩,⟨2,1361592659962718750727969,⟨419,131,203,475,218,483,210,387,419⟩⟩,⟨4,1361518440639760176465697,⟨419,131,15,271,12,487,194,387,419⟩⟩]⟩
theorem node976 : UpperPrefix a [5,7,0,8,3,2,4] 30 :=
  Boolean.leaf_sound a [5,7,0,8,3,2,4] 30 cert976 (by decide +kernel)

theorem node977 : UpperPrefix a [5,7,0,8,3,2] 30 :=
  branch_upper a [5,7,0,8,3,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,3,2,0] 30 (by decide +kernel))
  node975
  (invalid_upper a [5,7,0,8,3,2,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,2,3] 30 (by decide +kernel))
  node976
  (invalid_upper a [5,7,0,8,3,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,2,8] 30 (by decide +kernel)))

def cert978 : Leaf := ⟨⟨340,372,368,101,0,261,0,113,85⟩,[(4,2),(6,1)],[(7,1,6),(3,4,4)],⟨35,131,13,280,28,112,194,388,352⟩,⟨35,131,13,280,28,112,194,388,288⟩,[⟨1,1664054269087238376390657,⟨445,157,157,280,28,504,508,412,296⟩⟩]⟩
theorem node978 : UpperPrefix a [5,7,0,8,3,4,1,2] 30 :=
  Boolean.leaf_sound a [5,7,0,8,3,4,1,2] 30 cert978 (by decide +kernel)

def cert979 : Leaf := ⟨⟨340,372,368,101,0,261,0,53,85⟩,[(4,2),(6,1)],[(7,1,6),(3,4,4)],⟨35,131,13,280,28,112,194,448,292⟩,⟨35,131,13,280,28,112,194,448,288⟩,[⟨1,1527391570111965502898177,⟨445,445,285,280,28,504,508,504,424⟩⟩]⟩
theorem node979 : UpperPrefix a [5,7,0,8,3,4,1,6] 30 :=
  Boolean.leaf_sound a [5,7,0,8,3,4,1,6] 30 cert979 (by decide +kernel)

theorem node980 : UpperPrefix a [5,7,0,8,3,4,1] 30 :=
  branch_upper a [5,7,0,8,3,4,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,3,4,1,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,1,1] 30 (by decide +kernel))
  node978
  (invalid_upper a [5,7,0,8,3,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,1,5] 30 (by decide +kernel))
  node979
  (invalid_upper a [5,7,0,8,3,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,1,8] 30 (by decide +kernel)))

def cert981 : Leaf := ⟨⟨192,96,482,227,0,135,291,99,195⟩,[(4,2)],[(3,4,4),(2,6,5)],⟨35,131,13,280,28,112,196,450,354⟩,⟨35,131,13,280,28,112,196,384,288⟩,[⟨4,1361592732019213280173857,⟨419,131,207,463,206,483,198,387,419⟩⟩,⟨8,1181747921297203037281,⟨35,131,29,24,28,115,247,128,33⟩⟩]⟩
theorem node981 : UpperPrefix a [5,7,0,8,3,4,2] 30 :=
  Boolean.leaf_sound a [5,7,0,8,3,4,2] 30 cert981 (by decide +kernel)

theorem node982 : UpperPrefix a [5,7,0,8,3,4] 30 :=
  branch_upper a [5,7,0,8,3,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,3,4,0] 30 (by decide +kernel))
  node980
  node981
  (invalid_upper a [5,7,0,8,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,4,8] 30 (by decide +kernel)))

theorem node983 : UpperPrefix a [5,7,0,8,3] 30 :=
  branch_upper a [5,7,0,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,3,0] 30 (by decide +kernel))
  node974
  node977
  (invalid_upper a [5,7,0,8,3,3] 30 (by decide +kernel))
  node982
  (invalid_upper a [5,7,0,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,3,8] 30 (by decide +kernel)))

def cert984 : Leaf := ⟨⟨0,376,368,96,0,409,312,120,88⟩,[(0,5),(4,6)],[(7,1,5),(1,5,0),(2,6,4)],⟨35,131,13,280,84,98,196,408,312⟩,⟨35,131,13,280,84,98,196,384,288⟩,[⟨0,1361592299679425781302272,⟨426,130,220,408,84,506,212,384,424⟩⟩]⟩
theorem node984 : UpperPrefix a [5,7,0,8,6,1,2] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,1,2] 30 cert984 (by decide +kernel)

def cert985 : Leaf := ⟨⟨0,100,96,101,41,133,309,117,85⟩,[(0,5)],[(7,1,5),(8,3,6),(1,5,0),(3,6,4)],⟨35,131,13,280,84,98,200,404,308⟩,⟨35,131,13,280,84,98,200,384,288⟩,[⟨4,1210107568097501960504433,⟨35,131,13,301,103,103,239,384,289⟩⟩]⟩
theorem node985 : UpperPrefix a [5,7,0,8,6,1,3] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,1,3] 30 cert985 (by decide +kernel)

def cert986 : Leaf := ⟨⟨0,104,96,101,297,137,301,109,77⟩,[(0,5)],[(7,1,5),(1,5,0)],⟨35,131,13,280,84,98,208,396,300⟩,⟨35,131,13,280,84,98,208,384,288⟩,[⟨4,1247997180424901362760825,⟨35,131,399,431,231,99,227,384,289⟩⟩,⟨8,1181748483972280648817,⟨35,131,13,61,119,99,243,128,33⟩⟩,⟨2,1210107568098601452209265,⟨35,131,9,313,115,99,243,384,289⟩⟩]⟩
theorem node986 : UpperPrefix a [5,7,0,8,6,1,4] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,1,4] 30 cert986 (by decide +kernel)

theorem node987 : UpperPrefix a [5,7,0,8,6,1] 30 :=
  branch_upper a [5,7,0,8,6,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,1,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,1,1] 30 (by decide +kernel))
  node984
  node985
  node986
  (invalid_upper a [5,7,0,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,1,8] 30 (by decide +kernel)))

def cert988 : Leaf := ⟨⟨348,380,368,101,0,0,0,125,93⟩,[(4,5),(5,4),(6,1)],[(7,1,6)],⟨35,131,13,280,84,100,194,408,312⟩,⟨35,131,13,280,84,100,194,384,288⟩,[⟨1,1784991123790369371455489,⟨445,397,397,440,508,508,508,392,440⟩⟩]⟩
theorem node988 : UpperPrefix a [5,7,0,8,6,2,1] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,2,1] 30 cert988 (by decide +kernel)

def cert989 : Leaf := ⟨⟨196,100,226,230,0,0,310,118,214⟩,[(4,5),(5,4)],[(8,3,6),(3,6,4),(3,6,5)],⟨35,131,13,280,84,100,200,402,306⟩,⟨35,131,13,280,84,100,200,384,288⟩,[⟨0,1214841587788753339941888,⟨506,458,508,312,124,124,200,456,312⟩⟩,⟨4,1210107568097501960504433,⟨35,131,13,301,103,103,239,384,289⟩⟩]⟩
theorem node989 : UpperPrefix a [5,7,0,8,6,2,3] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,2,3] 30 cert989 (by decide +kernel)

def cert990 : Leaf := ⟨⟨204,108,98,102,0,0,302,110,78⟩,[(4,5),(5,4)],[],⟨35,131,13,280,84,100,208,394,298⟩,⟨35,131,13,280,84,100,208,384,288⟩,[⟨4,1247997178173101549157753,⟨35,131,399,431,231,231,227,387,291⟩⟩,⟨0,1214857692661020816835584,⟨506,458,508,312,124,124,240,392,312⟩⟩,⟨7,1213649340711187391448065,⟨319,271,269,312,116,116,112,264,312⟩⟩,⟨8,1181746234371490219121,⟨51,131,13,61,119,119,243,128,49⟩⟩]⟩
theorem node990 : UpperPrefix a [5,7,0,8,6,2,4] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,2,4] 30 cert990 (by decide +kernel)

theorem node991 : UpperPrefix a [5,7,0,8,6,2] 30 :=
  branch_upper a [5,7,0,8,6,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,2,0] 30 (by decide +kernel))
  node988
  (invalid_upper a [5,7,0,8,6,2,2] 30 (by decide +kernel))
  node989
  node990
  (invalid_upper a [5,7,0,8,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,2,8] 30 (by decide +kernel)))

def cert992 : Leaf := ⟨⟨332,364,354,100,299,260,0,104,92⟩,[(6,1)],[(7,1,6)],⟨35,131,13,280,84,104,194,388,304⟩,⟨35,131,13,280,84,104,194,388,288⟩,[⟨4,1212550282114053388361149,⟨103,195,239,495,103,239,195,487,487⟩⟩,⟨0,1323628864905209386632192,⟨98,194,396,440,508,360,194,388,288⟩⟩,⟨1,1323628828876412367667201,⟨33,129,397,440,508,360,192,388,288⟩⟩]⟩
theorem node992 : UpperPrefix a [5,7,0,8,6,3,1,2] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,3,1,2] 30 cert992 (by decide +kernel)

def cert993 : Leaf := ⟨⟨348,380,368,0,297,277,0,0,93⟩,[(3,7),(6,1),(7,3)],[(7,1,6)],⟨35,131,13,280,84,104,194,400,292⟩,⟨35,131,13,280,84,104,194,400,288⟩,[⟨1,1593726057859895548182529,⟨429,397,397,440,508,504,508,440,424⟩⟩]⟩
theorem node993 : UpperPrefix a [5,7,0,8,6,3,1,4] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,3,1,4] 30 cert993 (by decide +kernel)

theorem node994 : UpperPrefix a [5,7,0,8,6,3,1] 30 :=
  branch_upper a [5,7,0,8,6,3,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,3,1,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,1,1] 30 (by decide +kernel))
  node992
  (invalid_upper a [5,7,0,8,6,3,1,3] 30 (by decide +kernel))
  node993
  (invalid_upper a [5,7,0,8,6,3,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,1,8] 30 (by decide +kernel)))

def cert995 : Leaf := ⟨⟨456,360,480,224,0,384,296,104,216⟩,[(4,6)],[(2,6,4),(1,7,1)],⟨35,131,13,280,84,104,196,386,304⟩,⟨35,131,13,280,84,104,196,386,288⟩,[⟨4,1212547940242247155703165,⟨103,131,239,495,103,239,231,451,487⟩⟩,⟨0,1795690307549494334456832,⟨426,130,508,312,380,376,508,386,296⟩⟩]⟩
theorem node995 : UpperPrefix a [5,7,0,8,6,3,2,1] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,3,2,1] 30 cert995 (by decide +kernel)

def cert996 : Leaf := ⟨⟨464,368,498,0,0,403,307,0,211⟩,[(3,7),(4,6),(7,3)],[(2,6,4)],⟨35,131,13,280,84,104,196,400,290⟩,⟨35,131,13,280,84,104,196,400,288⟩,[⟨3,1366351847880813628841761,⟨419,387,471,467,214,499,214,467,419⟩⟩]⟩
theorem node996 : UpperPrefix a [5,7,0,8,6,3,2,4] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,3,2,4] 30 cert996 (by decide +kernel)

theorem node997 : UpperPrefix a [5,7,0,8,6,3,2] 30 :=
  branch_upper a [5,7,0,8,6,3,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,3,2,0] 30 (by decide +kernel))
  node995
  (invalid_upper a [5,7,0,8,6,3,2,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,2,3] 30 (by decide +kernel))
  node996
  (invalid_upper a [5,7,0,8,6,3,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,2,8] 30 (by decide +kernel)))

def cert998 : Leaf := ⟨⟨384,288,416,229,417,401,289,33,141⟩,[],[(4,6,5),(1,7,1)],⟨35,131,13,280,84,104,208,386,292⟩,⟨35,131,13,280,84,104,208,386,288⟩,[⟨2,1212542680038981887057213,⟨35,131,235,507,115,235,211,387,419⟩⟩,⟨3,1212542751674637265100065,⟨35,131,215,467,86,227,210,387,419⟩⟩,⟨6,1368739188024212379098913,⟨423,387,399,415,150,431,146,387,423⟩⟩]⟩
theorem node998 : UpperPrefix a [5,7,0,8,6,3,4,1] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,3,4,1] 30 cert998 (by decide +kernel)

def cert999 : Leaf := ⟨⟨456,352,480,224,416,400,292,98,194⟩,[],[(4,6,5),(2,7,6)],⟨35,131,13,280,84,104,208,388,290⟩,⟨35,131,13,280,84,104,208,388,288⟩,[⟨0,1224314268235588395074560,⟨362,506,508,376,252,104,248,508,288⟩⟩,⟨1,1210109913990445535854593,⟨117,253,29,280,116,104,248,508,288⟩⟩,⟨3,1214869527423715069922305,⟨355,467,471,336,214,96,208,470,288⟩⟩]⟩
theorem node999 : UpperPrefix a [5,7,0,8,6,3,4,2] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,3,4,2] 30 cert999 (by decide +kernel)

theorem node1000 : UpperPrefix a [5,7,0,8,6,3,4] 30 :=
  branch_upper a [5,7,0,8,6,3,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,3,4,0] 30 (by decide +kernel))
  node998
  node999
  (invalid_upper a [5,7,0,8,6,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,4,8] 30 (by decide +kernel)))

theorem node1001 : UpperPrefix a [5,7,0,8,6,3] 30 :=
  branch_upper a [5,7,0,8,6,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,3,0] 30 (by decide +kernel))
  node994
  node997
  (invalid_upper a [5,7,0,8,6,3,3] 30 (by decide +kernel))
  node1000
  (invalid_upper a [5,7,0,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,3,8] 30 (by decide +kernel)))

def cert1002 : Leaf := ⟨⟨284,316,304,37,299,0,0,61,29⟩,[(5,4),(6,1)],[(7,1,6),(6,4,5)],⟨35,131,13,280,84,112,194,396,300⟩,⟨35,131,13,280,84,112,194,384,288⟩,[⟨1,1290581486868366001176577,⟨429,389,397,440,508,504,192,384,296⟩⟩]⟩
theorem node1002 : UpperPrefix a [5,7,0,8,6,4,1] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,4,1] 30 cert1002 (by decide +kernel)

def cert1003 : Leaf := ⟨⟨152,56,178,163,0,0,315,59,155⟩,[(4,6),(5,4)],[(6,4,5),(2,6,4),(2,6,5)],⟨35,131,13,280,84,112,196,394,298⟩,⟨35,131,13,280,84,112,196,384,288⟩,[⟨8,1181748488370327159921,⟨35,131,13,61,119,115,247,128,33⟩⟩]⟩
theorem node1003 : UpperPrefix a [5,7,0,8,6,4,2] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,4,2] 30 cert1003 (by decide +kernel)

def cert1004 : Local := ⟨⟨148,52,176,165,169,0,309,53,149⟩,[(5,4)],[(8,3,6),(6,4,5),(3,6,4),(1,7,1)]⟩
theorem node1004 : UpperPrefix a [5,7,0,8,6,4,3,1] 30 :=
  local_sound a [5,7,0,8,6,4,3,1] 30 cert1004 (by decide +kernel)

def cert1005 : Leaf := ⟨⟨148,52,178,166,170,0,310,50,150⟩,[(5,4)],[(8,3,6),(6,4,5),(3,6,4)],⟨35,131,13,280,84,112,200,388,290⟩,⟨35,131,13,280,84,112,200,388,288⟩,[⟨0,1224314268200404022985728,⟨362,506,508,376,252,112,248,508,288⟩⟩]⟩
theorem node1005 : UpperPrefix a [5,7,0,8,6,4,3,2] 30 :=
  Boolean.leaf_sound a [5,7,0,8,6,4,3,2] 30 cert1005 (by decide +kernel)

theorem node1006 : UpperPrefix a [5,7,0,8,6,4,3] 30 :=
  branch_upper a [5,7,0,8,6,4,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,4,3,0] 30 (by decide +kernel))
  node1004
  node1005
  (invalid_upper a [5,7,0,8,6,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,3,8] 30 (by decide +kernel)))

theorem node1007 : UpperPrefix a [5,7,0,8,6,4] 30 :=
  branch_upper a [5,7,0,8,6,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,4,0] 30 (by decide +kernel))
  node1002
  node1003
  node1006
  (invalid_upper a [5,7,0,8,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,4,8] 30 (by decide +kernel)))

theorem node1008 : UpperPrefix a [5,7,0,8,6] 30 :=
  branch_upper a [5,7,0,8,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,6,0] 30 (by decide +kernel))
  node987
  node991
  node1001
  node1007
  (invalid_upper a [5,7,0,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,6,8] 30 (by decide +kernel)))

theorem node1009 : UpperPrefix a [5,7,0,8] 30 :=
  branch_upper a [5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [5,7,0,8,1] [5,7,0,1,6] 30 (by decide +kernel) node897)
  (invalid_upper a [5,7,0,8,2] 30 (by decide +kernel))
  node983
  (invalid_upper a [5,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,5] 30 (by decide +kernel))
  node1008
  (invalid_upper a [5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,8,8] 30 (by decide +kernel)))

theorem node1010 : UpperPrefix a [5,7,0] 30 :=
  branch_upper a [5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,0] 30 (by decide +kernel))
  node916
  node944
  (invalid_upper a [5,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,5] 30 (by decide +kernel))
  node973
  (invalid_upper a [5,7,0,7] 30 (by decide +kernel))
  node1009)

theorem node1011 : UpperPrefix a [5,7,4,0] 30 :=
  branch_upper a [5,7,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,4,0,1] [5,7,0,1,3] 30 (by decide +kernel) node882)
  (invalid_upper a [5,7,4,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,4,0,3] [5,7,0,2,3] 30 (by decide +kernel) node917)
  (invalid_upper a [5,7,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,0,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,4,0,6] [5,7,0,6,3] 30 (by decide +kernel) node952)
  (invalid_upper a [5,7,4,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,7,4,0,8] [5,7,0,8,3] 30 (by decide +kernel) node983))

def cert1012 : Local := ⟨⟨448,352,0,0,0,387,291,99,195⟩,[(2,3),(3,2),(4,2)],[(4,2,2),(4,2,3),(2,3,2),(2,3,3),(3,4,2),(3,4,3)]⟩
theorem node1012 : UpperPrefix a [5,7,4,2,3] 30 :=
  local_sound a [5,7,4,2,3] 30 cert1012 (by decide +kernel)

def cert1013 : Leaf := ⟨⟨456,360,0,0,296,395,299,107,75⟩,[(2,3),(3,2)],[(4,2,2),(4,2,3),(2,3,2),(2,3,3)],⟨35,131,28,28,84,363,459,395,299⟩,⟨35,131,28,28,84,96,192,384,288⟩,[⟨7,1213649340152651151836161,⟨319,271,28,28,92,124,92,268,316⟩⟩,⟨0,1210107565290498917925888,⟨62,142,28,28,92,124,220,396,316⟩⟩,⟨1,1210107565290498917924865,⟨61,141,28,28,92,124,220,396,316⟩⟩]⟩
theorem node1013 : UpperPrefix a [5,7,4,2,6] 30 :=
  Boolean.leaf_sound a [5,7,4,2,6] 30 cert1013 (by decide +kernel)

theorem node1014 : UpperPrefix a [5,7,4,2] 30 :=
  branch_upper a [5,7,4,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,7,4,2,0] [5,7,0,2,3] 30 (by decide +kernel) node917)
  (PrefixConjugacy.upper aut18 [5,7,4,2,1] [5,7,0,2,3] 30 (by decide +kernel) node917)
  (invalid_upper a [5,7,4,2,2] 30 (by decide +kernel))
  node1012
  (invalid_upper a [5,7,4,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,2,5] 30 (by decide +kernel))
  node1013
  (invalid_upper a [5,7,4,2,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut14 [5,7,4,2,8] [5,7,4,2,6] 30 (by decide +kernel) node1013))

def cert1015 : Leaf := ⟨⟨192,96,0,294,106,130,302,110,78⟩,[(2,3)],[(4,2,2),(0,5,0)],⟨35,131,28,88,276,97,206,398,302⟩,⟨35,131,28,88,276,97,192,384,288⟩,[⟨2,1210107567817126475498601,⟨35,131,57,123,272,99,227,384,289⟩⟩,⟨3,1210107567817125402805353,⟨35,131,53,115,276,99,227,384,289⟩⟩,⟨7,1213649340174810360316929,⟨319,279,28,92,276,381,92,276,316⟩⟩,⟨8,1181748202497303938153,⟨35,131,61,127,20,99,227,128,33⟩⟩]⟩
theorem node1015 : UpperPrefix a [5,7,4,6,8,0] 30 :=
  Boolean.leaf_sound a [5,7,4,6,8,0] 30 cert1015 (by decide +kernel)

def cert1016 : Leaf := ⟨⟨0,360,0,293,105,393,301,109,77⟩,[(0,5),(2,3)],[(7,1,5),(4,2,2),(1,5,0)],⟨35,131,28,88,276,98,205,397,301⟩,⟨35,131,28,88,276,98,192,384,288⟩,[⟨2,1210107567817126475498601,⟨35,131,57,123,272,99,227,384,289⟩⟩]⟩
theorem node1016 : UpperPrefix a [5,7,4,6,8,1] 30 :=
  Boolean.leaf_sound a [5,7,4,6,8,1] 30 cert1016 (by decide +kernel)

def cert1017 : Leaf := ⟨⟨460,0,0,422,234,394,0,110,206⟩,[(1,6),(2,3),(6,1)],[(4,2,2)],⟨35,131,28,88,276,100,193,394,298⟩,⟨35,131,28,88,276,100,193,384,288⟩,[⟨0,1214839157703038440047616,⟨446,406,60,124,276,124,508,404,316⟩⟩]⟩
theorem node1017 : UpperPrefix a [5,7,4,6,8,2,0] 30 :=
  Boolean.leaf_sound a [5,7,4,6,8,2,0] 30 cert1017 (by decide +kernel)

def cert1018 : Leaf := ⟨⟨328,360,0,291,107,267,0,107,75⟩,[(2,3),(6,1)],[(7,1,6),(4,2,2)],⟨35,131,28,88,276,100,194,393,297⟩,⟨35,131,28,88,276,100,194,384,288⟩,[⟨2,1361674067029585784170273,⟨483,195,218,218,475,491,194,451,483⟩⟩]⟩
theorem node1018 : UpperPrefix a [5,7,4,6,8,2,1] 30 :=
  Boolean.leaf_sound a [5,7,4,6,8,2,1] 30 cert1018 (by decide +kernel)

def cert1019 : Leaf := ⟨⟨384,288,0,419,163,395,291,35,131⟩,[(2,3)],[(4,2,2),(3,6,5)],⟨35,131,28,88,276,100,200,387,291⟩,⟨35,131,28,88,276,100,200,384,288⟩,[⟨2,1368778315297777646790433,⟨483,387,218,218,475,491,202,387,483⟩⟩,⟨6,1368776081514558813071137,⟨435,387,158,158,407,439,142,387,435⟩⟩]⟩
theorem node1019 : UpperPrefix a [5,7,4,6,8,2,3] 30 :=
  Boolean.leaf_sound a [5,7,4,6,8,2,3] 30 cert1019 (by decide +kernel)

theorem node1020 : UpperPrefix a [5,7,4,6,8,2] 30 :=
  branch_upper a [5,7,4,6,8,2] 30 (by decide) (fin9_cases _
  node1017
  node1018
  (invalid_upper a [5,7,4,6,8,2,2] 30 (by decide +kernel))
  node1019
  (invalid_upper a [5,7,4,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,4,6,8,2,8] 30 (by decide +kernel)))

def cert1021 : Local := ⟨⟨396,0,0,423,171,0,0,47,143⟩,[(1,6),(2,3),(5,3),(6,1)],[(4,2,2),(6,3,5)]⟩
theorem node1021 : UpperPrefix a [5,7,4,6,8,3,0] 30 :=
  local_sound a [5,7,4,6,8,3,0] 30 cert1021 (by decide +kernel)

def cert1022 : Local := ⟨⟨268,300,0,295,43,0,0,47,15⟩,[(2,3),(5,3),(6,1)],[(7,1,6),(4,2,2),(6,3,5)]⟩
theorem node1022 : UpperPrefix a [5,7,4,6,8,3,1] 30 :=
  local_sound a [5,7,4,6,8,3,1] 30 cert1022 (by decide +kernel)

def cert1023 : Local := ⟨⟨392,296,0,423,171,0,299,43,139⟩,[(2,3),(5,3)],[(4,2,2),(6,3,5),(2,6,3)]⟩
theorem node1023 : UpperPrefix a [5,7,4,6,8,3,2] 30 :=
  local_sound a [5,7,4,6,8,3,2] 30 cert1023 (by decide +kernel)

#print axioms node1023
end Delivery.FiniteExclusion.Sharp2x3x4
