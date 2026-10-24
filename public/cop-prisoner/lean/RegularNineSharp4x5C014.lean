import RegularNineSharp4x5Base
import RegularNineSharp4x5C013
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
theorem node896 : UpperPrefix a [3,4,8,5,7,0] 30 :=
  branch_upper a [3,4,8,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,5,7,0,0] 30 (by decide +kernel))
  node894
  node895
  (invalid_upper a [3,4,8,5,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,0,8] 30 (by decide +kernel)))

def cert897 : Leaf := ⟨⟨32,297,33,2,333,137,40,109,237⟩,[],[(1,5,3)],⟨11,22,268,41,176,98,193,452,340⟩,⟨11,22,268,41,176,98,193,384,272⟩,[⟨4,1212469036824938805199907,⟨43,111,396,41,233,107,201,388,460⟩⟩,⟨2,1210107853584603426063395,⟨43,123,264,41,249,107,201,384,344⟩⟩,⟨6,1210106412362353588962599,⟨11,31,271,41,185,43,129,391,287⟩⟩,⟨7,1208926973663140784506151,⟨11,31,271,41,57,107,65,263,287⟩⟩,⟨8,1182033969974252405795,⟨43,127,12,41,249,107,201,128,88⟩⟩]⟩
theorem node897 : UpperPrefix a [3,4,8,5,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,1,0] 30 cert897 (by decide +kernel)

def cert898 : Leaf := ⟨⟨32,41,33,2,73,157,297,121,233⟩,[],[(8,2,6),(1,5,3),(2,6,5)],⟨11,22,268,41,176,98,196,449,337⟩,⟨11,22,268,41,176,98,196,384,272⟩,[⟨4,1210109871125767897744419,⟨11,15,268,41,233,107,196,452,268⟩⟩,⟨6,1210106412362353588962599,⟨11,31,271,41,185,43,133,391,287⟩⟩,⟨7,1208926973663140784506151,⟨11,31,271,41,57,107,69,263,287⟩⟩]⟩
theorem node898 : UpperPrefix a [3,4,8,5,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,1,2] 30 cert898 (by decide +kernel)

theorem node899 : UpperPrefix a [3,4,8,5,7,1] 30 :=
  branch_upper a [3,4,8,5,7,1] 30 (by decide) (fin9_cases _
  node897
  (invalid_upper a [3,4,8,5,7,1,1] 30 (by decide +kernel))
  node898
  (invalid_upper a [3,4,8,5,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,1,8] 30 (by decide +kernel)))

def cert900 : Leaf := ⟨⟨420,416,160,388,260,385,294,52,228⟩,[],[(4,1,7),(1,7,6)],⟨11,22,268,41,176,100,193,386,336⟩,⟨11,22,268,41,176,100,193,386,272⟩,[⟨3,1423195291724791667510273,⟨467,438,502,499,434,502,449,402,400⟩⟩,⟨6,1212504489094134853944639,⟨11,159,399,59,187,191,129,391,415⟩⟩,⟨0,1361776695060640400694784,⟨158,150,414,446,434,502,194,386,400⟩⟩]⟩
theorem node900 : UpperPrefix a [3,4,8,5,7,2,0,1] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,2,0,1] 30 cert900 (by decide +kernel)

def cert901 : Leaf := ⟨⟨308,288,48,276,324,272,310,54,38⟩,[],[(6,7,4)],⟨11,22,268,41,176,100,193,448,274⟩,⟨11,22,268,41,176,100,193,448,272⟩,[⟨0,2415196464398892008791552,⟨286,278,286,446,434,502,502,498,272⟩⟩,⟨3,1508622163530140601043969,⟨467,438,502,499,434,502,449,448,272⟩⟩,⟨7,1293929577110219647755671,⟨271,287,271,45,319,109,109,367,287⟩⟩,⟨1,1210107572052453890195457,⟨9,20,268,41,180,124,253,508,272⟩⟩]⟩
theorem node901 : UpperPrefix a [3,4,8,5,7,2,0,6] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,2,0,6] 30 cert901 (by decide +kernel)

theorem node902 : UpperPrefix a [3,4,8,5,7,2,0] 30 :=
  branch_upper a [3,4,8,5,7,2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,5,7,2,0,0] 30 (by decide +kernel))
  node900
  (invalid_upper a [3,4,8,5,7,2,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,0,5] 30 (by decide +kernel))
  node901
  (invalid_upper a [3,4,8,5,7,2,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,0,8] 30 (by decide +kernel)))

def cert903 : Leaf := ⟨⟨180,160,178,150,2,146,48,50,226⟩,[],[],⟨11,22,268,41,176,100,194,385,336⟩,⟨11,22,268,41,176,100,194,385,272⟩,[⟨0,2352922852798853706761216,⟨302,374,268,302,498,374,498,502,336⟩⟩,⟨3,2414394551397896242088961,⟨499,374,502,499,498,374,498,465,336⟩⟩,⟨6,1212504489094134853944639,⟨11,159,399,59,187,191,131,391,415⟩⟩,⟨8,1182033974380888867963,⟨43,127,13,43,251,127,251,137,89⟩⟩,⟨2,1252691891992958450271233,⟨475,18,408,505,176,96,194,449,272⟩⟩]⟩
theorem node903 : UpperPrefix a [3,4,8,5,7,2,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,2,1,0] 30 cert903 (by decide +kernel)

def cert904 : Leaf := ⟨⟨52,32,51,22,70,18,52,54,39⟩,[],[(6,7,4)],⟨11,22,268,41,176,100,194,448,273⟩,⟨11,22,268,41,176,100,194,448,272⟩,[⟨3,1255091085833431545826305,⟨499,246,502,499,242,246,242,464,464⟩⟩,⟨7,1293929577110219664532951,⟨271,287,271,45,319,109,367,367,287⟩⟩,⟨8,1182033974380888867963,⟨43,127,13,43,251,127,251,217,89⟩⟩,⟨0,1212506615009069059034112,⟨122,246,510,122,242,246,242,464,464⟩⟩]⟩
theorem node904 : UpperPrefix a [3,4,8,5,7,2,1,6] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,2,1,6] 30 cert904 (by decide +kernel)

theorem node905 : UpperPrefix a [3,4,8,5,7,2,1] 30 :=
  branch_upper a [3,4,8,5,7,2,1] 30 (by decide) (fin9_cases _
  node903
  (invalid_upper a [3,4,8,5,7,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,1,5] 30 (by decide +kernel))
  node904
  (invalid_upper a [3,4,8,5,7,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,1,8] 30 (by decide +kernel)))

theorem node906 : UpperPrefix a [3,4,8,5,7,2] 30 :=
  branch_upper a [3,4,8,5,7,2] 30 (by decide) (fin9_cases _
  node902
  node905
  (invalid_upper a [3,4,8,5,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,2,8] 30 (by decide +kernel)))

theorem node907 : UpperPrefix a [3,4,8,5,7] 30 :=
  branch_upper a [3,4,8,5,7] 30 (by decide) (fin9_cases _
  node896
  node899
  node906
  (invalid_upper a [3,4,8,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,7,8] 30 (by decide +kernel)))

theorem node908 : UpperPrefix a [3,4,8,5] 30 :=
  branch_upper a [3,4,8,5] 30 (by decide) (fin9_cases _
  node875
  node881
  node885
  (invalid_upper a [3,4,8,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,5] 30 (by decide +kernel))
  node893
  node907
  (invalid_upper a [3,4,8,5,8] 30 (by decide +kernel)))

def cert909 : Leaf := ⟨⟨96,480,240,32,66,404,308,116,228⟩,[],[(1,5,4)],⟨11,22,268,73,49,98,228,420,436⟩,⟨11,22,268,73,49,98,192,384,272⟩,[⟨0,1295322867654409078449152,⟨494,502,492,236,502,482,192,416,498⟩⟩,⟨3,1238497212746589749120001,⟨499,502,502,113,49,482,192,384,272⟩⟩,⟨2,1210107565286055003292705,⟨11,18,264,73,57,123,192,384,272⟩⟩,⟨7,1208926973665337593037857,⟨11,22,268,73,57,123,64,256,272⟩⟩,⟨8,1181745671425829635105,⟨11,22,12,73,57,123,192,128,16⟩⟩,⟨4,1210107565282756469457953,⟨11,6,268,73,41,107,192,384,256⟩⟩]⟩
theorem node909 : UpperPrefix a [3,4,8,6,0,1] 30 :=
  Boolean.leaf_sound a [3,4,8,6,0,1] 30 cert909 (by decide +kernel)

def cert910 : Leaf := ⟨⟨368,360,240,306,320,400,304,112,224⟩,[],[(1,6,3)],⟨11,22,268,73,49,100,194,416,432⟩,⟨11,22,268,73,49,100,194,384,272⟩,[⟨0,1298278733634452130636800,⟨494,502,492,236,502,228,482,448,498⟩⟩,⟨2,1437223914350373014340675,⟨75,475,264,73,441,505,203,384,400⟩⟩,⟨3,1300598122451065809929217,⟨499,502,260,465,497,228,482,384,400⟩⟩,⟨7,1208926973665346182988913,⟨11,23,268,73,59,127,75,256,273⟩⟩]⟩
theorem node910 : UpperPrefix a [3,4,8,6,0,2,1] 30 :=
  Boolean.leaf_sound a [3,4,8,6,0,2,1] 30 cert910 (by decide +kernel)

def cert911 : Leaf := ⟨⟨464,392,146,402,454,402,274,18,130⟩,[],[],⟨11,22,268,73,49,100,224,386,402⟩,⟨11,22,268,73,49,100,224,384,272⟩,[⟨0,1297651760508728119665664,⟨494,502,492,236,502,100,224,448,498⟩⟩,⟨5,1297683481647892175135765,⟨399,407,399,205,415,205,200,386,407⟩⟩,⟨2,1219580256596080107455491,⟨395,475,264,201,249,96,224,384,344⟩⟩,⟨3,1224302677192579256157185,⟨499,502,260,465,497,100,224,384,336⟩⟩,⟨6,1297645436364135756735489,⟨399,406,396,141,439,36,160,384,402⟩⟩]⟩
theorem node911 : UpperPrefix a [3,4,8,6,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,8,6,0,2,5] 30 cert911 (by decide +kernel)

theorem node912 : UpperPrefix a [3,4,8,6,0,2] 30 :=
  branch_upper a [3,4,8,6,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,6,0,2,0] 30 (by decide +kernel))
  node910
  (invalid_upper a [3,4,8,6,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,0,2,4] 30 (by decide +kernel))
  node911
  (invalid_upper a [3,4,8,6,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,0,2,8] 30 (by decide +kernel)))

def cert913 : Leaf := ⟨⟨116,96,114,310,64,0,310,118,102⟩,[(5,6)],[(7,5,5)],⟨11,22,268,73,49,224,230,422,310⟩,⟨11,22,268,73,49,224,192,384,272⟩,[⟨0,1295285760526754335958016,⟨494,502,300,236,502,224,224,416,498⟩⟩,⟨3,1238497214998389562805249,⟨499,502,502,113,49,224,224,384,272⟩⟩,⟨8,1181747921572080913413,⟨27,23,31,121,49,224,224,128,16⟩⟩,⟨1,1210107567536201255616513,⟨25,20,284,121,49,224,224,384,272⟩⟩,⟨2,1210107567536201254568961,⟨27,18,280,121,49,224,224,384,272⟩⟩]⟩
theorem node913 : UpperPrefix a [3,4,8,6,0,7] 30 :=
  Boolean.leaf_sound a [3,4,8,6,0,7] 30 cert913 (by decide +kernel)

theorem node914 : UpperPrefix a [3,4,8,6,0] 30 :=
  branch_upper a [3,4,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,6,0,0] 30 (by decide +kernel))
  node909
  node912
  (invalid_upper a [3,4,8,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,0,6] 30 (by decide +kernel))
  node913
  (invalid_upper a [3,4,8,6,0,8] 30 (by decide +kernel)))

def cert915 : Leaf := ⟨⟨356,353,225,0,325,0,293,101,229⟩,[(3,5),(5,3)],[],⟨11,22,268,73,50,97,228,420,436⟩,⟨11,22,268,73,50,97,192,384,272⟩,[⟨3,1229033997042889224358913,⟨51,470,502,113,50,113,192,384,272⟩⟩,⟨1,1285850257019952570564609,⟨41,468,492,105,508,105,192,384,468⟩⟩,⟨4,1212512677584971720819731,⟨107,239,492,105,107,105,196,492,493⟩⟩,⟨7,1208926973944957143878677,⟨59,23,319,121,59,121,64,256,273⟩⟩]⟩
theorem node915 : UpperPrefix a [3,4,8,6,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,6,1,0] 30 cert915 (by decide +kernel)

def cert916 : Leaf := ⟨⟨480,488,224,0,460,392,296,104,232⟩,[(3,6)],[(2,5,4),(0,6,3)],⟨11,22,268,73,50,100,193,416,432⟩,⟨11,22,268,73,50,100,193,384,272⟩,[⟨1,1295322464371144920399873,⟨493,436,492,237,432,236,237,384,400⟩⟩,⟨4,1212510305700900391355411,⟨107,239,492,105,107,236,237,492,493⟩⟩]⟩
theorem node916 : UpperPrefix a [3,4,8,6,1,2,0] 30 :=
  Boolean.leaf_sound a [3,4,8,6,1,2,0] 30 cert916 (by decide +kernel)

def cert917 : Leaf := ⟨⟨384,385,131,386,389,387,259,3,131⟩,[],[(2,5,4)],⟨11,22,268,73,50,100,224,385,401⟩,⟨11,22,268,73,50,100,224,384,272⟩,[⟨3,1252691964268185998347265,⟨499,118,502,465,50,118,242,384,272⟩⟩,⟨4,1212475754084548333274131,⟨43,111,492,105,43,100,228,492,493⟩⟩,⟨5,1297683481647892175135765,⟨399,407,399,205,415,205,200,386,407⟩⟩,⟨6,1408879303135201424856077,⟨399,407,399,415,434,439,434,384,272⟩⟩]⟩
theorem node917 : UpperPrefix a [3,4,8,6,1,2,5] 30 :=
  Boolean.leaf_sound a [3,4,8,6,1,2,5] 30 cert917 (by decide +kernel)

theorem node918 : UpperPrefix a [3,4,8,6,1,2] 30 :=
  branch_upper a [3,4,8,6,1,2] 30 (by decide) (fin9_cases _
  node916
  (invalid_upper a [3,4,8,6,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,2,4] 30 (by decide +kernel))
  node917
  (invalid_upper a [3,4,8,6,1,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,2,8] 30 (by decide +kernel)))

def cert919 : Leaf := ⟨⟨372,360,112,0,332,0,316,124,108⟩,[(3,6),(5,6)],[(7,5,5),(0,6,3)],⟨11,22,268,73,50,224,193,420,308⟩,⟨11,22,268,73,50,224,193,384,272⟩,[⟨1,1219617026692640920567809,⟨493,436,492,237,432,232,237,384,272⟩⟩]⟩
theorem node919 : UpperPrefix a [3,4,8,6,1,7,0] 30 :=
  Boolean.leaf_sound a [3,4,8,6,1,7,0] 30 cert919 (by decide +kernel)

def cert920 : Leaf := ⟨⟨100,97,99,38,69,0,291,103,103⟩,[(5,6)],[(8,2,6),(7,5,5)],⟨11,22,268,73,50,224,196,417,305⟩,⟨11,22,268,73,50,224,196,384,272⟩,[⟨3,1252691948717243290913793,⟨435,118,502,499,50,242,246,384,272⟩⟩,⟨4,1212476330474934040003603,⟨11,111,492,105,107,228,228,492,493⟩⟩]⟩
theorem node920 : UpperPrefix a [3,4,8,6,1,7,2] 30 :=
  Boolean.leaf_sound a [3,4,8,6,1,7,2] 30 cert920 (by decide +kernel)

def cert921 : Leaf := ⟨⟨96,361,99,34,333,0,0,111,111⟩,[(5,6),(6,5)],[(7,5,5),(7,5,6)],⟨11,22,268,73,50,224,224,389,277⟩,⟨11,22,268,73,50,224,224,384,272⟩,[⟨4,1212476330474934040003603,⟨11,111,492,105,107,228,228,492,493⟩⟩,⟨2,1210110454343014790726675,⟨11,27,264,105,123,224,224,480,281⟩⟩,⟨8,1184634728385617069075,⟨11,31,12,105,123,224,224,224,25⟩⟩]⟩
theorem node921 : UpperPrefix a [3,4,8,6,1,7,5] 30 :=
  Boolean.leaf_sound a [3,4,8,6,1,7,5] 30 cert921 (by decide +kernel)

theorem node922 : UpperPrefix a [3,4,8,6,1,7] 30 :=
  branch_upper a [3,4,8,6,1,7] 30 (by decide) (fin9_cases _
  node919
  (invalid_upper a [3,4,8,6,1,7,1] 30 (by decide +kernel))
  node920
  (invalid_upper a [3,4,8,6,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,7,4] 30 (by decide +kernel))
  node921
  (invalid_upper a [3,4,8,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,7,8] 30 (by decide +kernel)))

theorem node923 : UpperPrefix a [3,4,8,6,1] 30 :=
  branch_upper a [3,4,8,6,1] 30 (by decide) (fin9_cases _
  node915
  (invalid_upper a [3,4,8,6,1,1] 30 (by decide +kernel))
  node918
  (invalid_upper a [3,4,8,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,1,6] 30 (by decide +kernel))
  node922
  (invalid_upper a [3,4,8,6,1,8] 30 (by decide +kernel)))

def cert924 : Leaf := ⟨⟨496,0,243,0,451,0,306,114,226⟩,[(1,4),(3,5),(5,3)],[(2,4,1)],⟨11,22,268,73,52,97,226,418,434⟩,⟨11,22,268,73,52,97,192,384,272⟩,[⟨3,1304739722951700656434177,⟨35,470,502,97,502,97,192,384,466⟩⟩,⟨0,1285813291192731837670400,⟨10,470,268,72,502,96,192,384,466⟩⟩]⟩
theorem node924 : UpperPrefix a [3,4,8,6,2,0] 30 :=
  Boolean.leaf_sound a [3,4,8,6,2,0] 30 cert924 (by decide +kernel)

def cert925 : Leaf := ⟨⟨496,0,242,0,450,400,306,114,226⟩,[(1,4),(3,6)],[(2,4,1),(0,6,3)],⟨11,22,268,73,52,98,193,416,432⟩,⟨11,22,268,73,52,98,193,384,272⟩,[⟨3,1471009252396282418310145,⟨499,438,502,481,438,498,481,384,402⟩⟩]⟩
theorem node925 : UpperPrefix a [3,4,8,6,2,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,6,2,1,0] 30 cert925 (by decide +kernel)

def cert926 : Leaf := ⟨⟨320,0,211,258,451,401,275,83,195⟩,[(1,4)],[(2,4,1)],⟨11,22,268,73,52,98,224,385,401⟩,⟨11,22,268,73,52,98,224,384,272⟩,[⟨3,1214913177111885448752129,⟨499,118,502,481,118,114,224,384,306⟩⟩,⟨5,1297978629553080126284853,⟨399,407,399,205,415,463,205,386,407⟩⟩,⟨4,1210107565282765059392545,⟨11,6,268,73,45,107,233,384,256⟩⟩,⟨7,1208926973663147159725105,⟨11,23,268,73,63,107,105,256,275⟩⟩]⟩
theorem node926 : UpperPrefix a [3,4,8,6,2,1,5] 30 :=
  Boolean.leaf_sound a [3,4,8,6,2,1,5] 30 cert926 (by decide +kernel)

theorem node927 : UpperPrefix a [3,4,8,6,2,1] 30 :=
  branch_upper a [3,4,8,6,2,1] 30 (by decide) (fin9_cases _
  node925
  (invalid_upper a [3,4,8,6,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,1,4] 30 (by decide +kernel))
  node926
  (invalid_upper a [3,4,8,6,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,1,8] 30 (by decide +kernel)))

def cert928 : Local := ⟨⟨368,0,114,0,330,0,314,122,106⟩,[(1,4),(3,6),(5,6)],[(2,4,1),(7,5,5),(0,6,3)]⟩
theorem node928 : UpperPrefix a [3,4,8,6,2,7,0] 30 :=
  local_sound a [3,4,8,6,2,7,0] 30 cert928 (by decide +kernel)

def cert929 : Local := ⟨⟨368,0,113,306,329,0,313,121,105⟩,[(1,4),(5,6)],[(2,4,1),(7,5,5),(1,6,3)]⟩
theorem node929 : UpperPrefix a [3,4,8,6,2,7,1] 30 :=
  local_sound a [3,4,8,6,2,7,1] 30 cert929 (by decide +kernel)

def cert930 : Local := ⟨⟨368,0,115,306,331,0,0,123,107⟩,[(1,4),(5,6),(6,5)],[(2,4,1),(7,5,5),(7,5,6)]⟩
theorem node930 : UpperPrefix a [3,4,8,6,2,7,5] 30 :=
  local_sound a [3,4,8,6,2,7,5] 30 cert930 (by decide +kernel)

theorem node931 : UpperPrefix a [3,4,8,6,2,7] 30 :=
  branch_upper a [3,4,8,6,2,7] 30 (by decide) (fin9_cases _
  node928
  node929
  (invalid_upper a [3,4,8,6,2,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,7,4] 30 (by decide +kernel))
  node930
  (invalid_upper a [3,4,8,6,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,7,8] 30 (by decide +kernel)))

theorem node932 : UpperPrefix a [3,4,8,6,2] 30 :=
  branch_upper a [3,4,8,6,2] 30 (by decide) (fin9_cases _
  node924
  node927
  (invalid_upper a [3,4,8,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,2,6] 30 (by decide +kernel))
  node931
  (invalid_upper a [3,4,8,6,2,8] 30 (by decide +kernel)))

def cert933 : Leaf := ⟨⟨340,321,81,0,325,0,277,117,101⟩,[(3,5),(5,3)],[(1,6,3),(1,6,5)],⟨11,22,268,73,176,97,194,420,308⟩,⟨11,22,268,73,176,97,194,384,272⟩,[⟨3,1229034033106801895934977,⟨99,470,502,97,176,97,194,384,272⟩⟩,⟨5,1210110158231404085913047,⟨11,95,271,73,223,73,207,463,351⟩⟩,⟨7,1284484839922336277865557,⟨43,279,303,105,319,105,107,258,279⟩⟩]⟩
theorem node933 : UpperPrefix a [3,4,8,6,7,0,1] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,0,1] 30 cert933 (by decide +kernel)

def cert934 : Leaf := ⟨⟨84,65,83,0,71,0,275,119,103⟩,[(3,5),(5,3)],[(8,2,6)],⟨11,22,268,73,176,97,196,418,306⟩,⟨11,22,268,73,176,97,196,384,272⟩,[⟨3,1423029217160785894083585,⟨499,470,502,499,432,499,470,384,272⟩⟩,⟨5,1210110158231404085912983,⟨11,95,271,73,223,73,205,463,351⟩⟩,⟨7,1284484839922336277865493,⟨43,279,303,105,319,105,109,258,279⟩⟩]⟩
theorem node934 : UpperPrefix a [3,4,8,6,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,0,2] 30 cert934 (by decide +kernel)

def cert935 : Leaf := ⟨⟨468,457,211,0,0,0,0,95,207⟩,[(3,5),(4,6),(5,3),(6,4)],[],⟨11,22,268,73,176,97,224,390,278⟩,⟨11,22,268,73,176,97,224,384,272⟩,[⟨5,1297683481647892175135765,⟨399,407,399,205,415,205,200,386,407⟩⟩]⟩
theorem node935 : UpperPrefix a [3,4,8,6,7,0,5] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,0,5] 30 cert935 (by decide +kernel)

theorem node936 : UpperPrefix a [3,4,8,6,7,0] 30 :=
  branch_upper a [3,4,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,6,7,0,0] 30 (by decide +kernel))
  node933
  node934
  (invalid_upper a [3,4,8,6,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,0,4] 30 (by decide +kernel))
  node935
  (invalid_upper a [3,4,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,0,8] 30 (by decide +kernel)))

def cert937 : Leaf := ⟨⟨324,328,64,0,332,396,270,124,108⟩,[(3,6)],[(0,6,3)],⟨11,22,268,73,176,98,193,420,308⟩,⟨11,22,268,73,176,98,193,384,272⟩,[⟨1,1437223878321571307192321,⟨9,404,268,73,436,508,201,384,400⟩⟩,⟨4,1210107853583512438309923,⟨43,111,268,73,233,107,201,388,332⟩⟩,⟨5,1210110158231404085913015,⟨11,95,271,73,223,75,205,463,351⟩⟩,⟨7,1284484837389061487469621,⟨11,279,271,73,319,107,73,258,279⟩⟩]⟩
theorem node937 : UpperPrefix a [3,4,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,1,0] 30 cert937 (by decide +kernel)

def cert938 : Leaf := ⟨⟨80,65,83,18,67,149,275,115,99⟩,[],[(8,2,6),(2,6,5)],⟨11,22,268,73,176,98,196,417,305⟩,⟨11,22,268,73,176,98,196,384,272⟩,[⟨3,1252691948785275572882433,⟨435,118,502,499,176,114,246,384,272⟩⟩,⟨5,1210110158231404085913015,⟨11,95,271,73,223,75,205,463,351⟩⟩,⟨7,1284484837389061487469621,⟨11,279,271,73,319,107,77,258,279⟩⟩]⟩
theorem node938 : UpperPrefix a [3,4,8,6,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,1,2] 30 cert938 (by decide +kernel)

def cert939 : Leaf := ⟨⟨276,265,19,278,0,413,0,31,15⟩,[(4,6),(6,4)],[],⟨11,22,268,73,176,98,224,389,277⟩,⟨11,22,268,73,176,98,224,384,272⟩,[⟨5,1297978629553080126284853,⟨399,407,399,205,415,463,205,386,407⟩⟩,⟨6,1257468427778193425175565,⟨399,407,399,415,176,434,176,384,272⟩⟩,⟨7,1293929570354800786547765,⟨271,279,271,77,319,367,109,258,279⟩⟩]⟩
theorem node939 : UpperPrefix a [3,4,8,6,7,1,5] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,1,5] 30 cert939 (by decide +kernel)

theorem node940 : UpperPrefix a [3,4,8,6,7,1] 30 :=
  branch_upper a [3,4,8,6,7,1] 30 (by decide) (fin9_cases _
  node937
  (invalid_upper a [3,4,8,6,7,1,1] 30 (by decide +kernel))
  node938
  (invalid_upper a [3,4,8,6,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,1,4] 30 (by decide +kernel))
  node939
  (invalid_upper a [3,4,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,1,8] 30 (by decide +kernel)))

def cert941 : Leaf := ⟨⟨340,256,82,0,262,410,286,54,38⟩,[(3,6)],[(0,6,3)],⟨11,22,268,73,176,100,193,418,306⟩,⟨11,22,268,73,176,100,193,384,272⟩,[⟨3,1437223878321561635144705,⟨3,406,260,65,434,502,193,384,400⟩⟩,⟨5,1210110158231404085912983,⟨11,95,271,73,223,77,205,463,351⟩⟩,⟨6,1437222725400058102039553,⟨11,406,268,9,434,438,129,384,400⟩⟩,⟨7,1284484837389061487469589,⟨11,279,271,73,319,109,73,258,279⟩⟩]⟩
theorem node941 : UpperPrefix a [3,4,8,6,7,2,0] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,2,0] 30 cert941 (by decide +kernel)

def cert942 : Leaf := ⟨⟨208,193,209,146,65,145,21,113,225⟩,[],[(1,6,3)],⟨11,22,268,73,176,100,194,417,305⟩,⟨11,22,268,73,176,100,194,384,272⟩,[⟨3,1214839461458367283741697,⟨499,118,260,465,242,118,242,384,336⟩⟩,⟨8,1182033974415114388595,⟨43,127,12,89,251,127,251,136,89⟩⟩,⟨2,1361518440643071592891457,⟨11,18,264,73,440,505,203,384,272⟩⟩,⟨5,1210110158231404085913047,⟨11,95,271,73,223,77,207,463,351⟩⟩]⟩
theorem node942 : UpperPrefix a [3,4,8,6,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,2,1] 30 cert942 (by decide +kernel)

def cert943 : Leaf := ⟨⟨276,265,19,278,0,283,0,31,15⟩,[(4,6),(6,4)],[],⟨11,22,268,73,176,100,224,387,275⟩,⟨11,22,268,73,176,100,224,384,272⟩,[⟨5,1297683481647892175135765,⟨399,407,399,205,415,205,200,386,407⟩⟩,⟨7,1293929570636267164935189,⟨303,279,303,109,319,109,104,258,279⟩⟩,⟨6,1408879303135201424856077,⟨399,407,399,415,434,439,434,384,272⟩⟩]⟩
theorem node943 : UpperPrefix a [3,4,8,6,7,2,5] 30 :=
  Boolean.leaf_sound a [3,4,8,6,7,2,5] 30 cert943 (by decide +kernel)

theorem node944 : UpperPrefix a [3,4,8,6,7,2] 30 :=
  branch_upper a [3,4,8,6,7,2] 30 (by decide) (fin9_cases _
  node941
  node942
  (invalid_upper a [3,4,8,6,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,2,4] 30 (by decide +kernel))
  node943
  (invalid_upper a [3,4,8,6,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,2,8] 30 (by decide +kernel)))

theorem node945 : UpperPrefix a [3,4,8,6,7] 30 :=
  branch_upper a [3,4,8,6,7] 30 (by decide) (fin9_cases _
  node936
  node940
  node944
  (invalid_upper a [3,4,8,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,7,8] 30 (by decide +kernel)))

theorem node946 : UpperPrefix a [3,4,8,6] 30 :=
  branch_upper a [3,4,8,6] 30 (by decide) (fin9_cases _
  node914
  node923
  node932
  (invalid_upper a [3,4,8,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,6,6] 30 (by decide +kernel))
  node945
  (invalid_upper a [3,4,8,6,8] 30 (by decide +kernel)))

def cert947 : Leaf := ⟨⟨240,224,240,112,194,148,304,112,224⟩,[],[(8,2,6),(1,5,4),(2,6,5)],⟨11,22,268,137,49,98,196,480,368⟩,⟨11,22,268,137,49,98,196,384,272⟩,[⟨0,1297979198801023253881856,⟨494,502,492,236,502,482,196,416,498⟩⟩,⟨3,1244114248568834121272321,⟨499,502,502,433,433,482,486,384,272⟩⟩]⟩
theorem node947 : UpperPrefix a [3,4,8,7,0,1,2] 30 :=
  Boolean.leaf_sound a [3,4,8,7,0,1,2] 30 cert947 (by decide +kernel)

def cert948 : Leaf := ⟨⟨240,224,240,112,194,144,16,116,228⟩,[],[(1,5,4)],⟨11,22,268,137,49,98,224,452,340⟩,⟨11,22,268,137,49,98,224,384,272⟩,[⟨0,1295330361644189022954496,⟨494,502,492,236,502,482,224,480,498⟩⟩,⟨3,1238497951336928637881345,⟨499,502,502,241,113,482,224,384,272⟩⟩,⟨8,1181889967968899566629,⟨123,55,127,249,49,123,249,128,16⟩⟩,⟨2,1210107709441448268006433,⟨123,18,344,249,49,123,249,384,272⟩⟩]⟩
theorem node948 : UpperPrefix a [3,4,8,7,0,1,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,0,1,5] 30 cert948 (by decide +kernel)

theorem node949 : UpperPrefix a [3,4,8,7,0,1] 30 :=
  branch_upper a [3,4,8,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,1,1] 30 (by decide +kernel))
  node947
  (invalid_upper a [3,4,8,7,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,1,4] 30 (by decide +kernel))
  node948
  (invalid_upper a [3,4,8,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,1,8] 30 (by decide +kernel)))

def cert950 : Leaf := ⟨⟨160,168,242,34,130,402,308,114,226⟩,[],[],⟨11,22,268,137,49,100,194,480,368⟩,⟨11,22,268,137,49,100,194,384,272⟩,[⟨0,1298278733634452130636800,⟨494,502,492,236,502,228,482,448,498⟩⟩,⟨2,1361518440643073740375107,⟨11,27,264,137,441,505,203,384,280⟩⟩,⟨3,1300598122451065809929217,⟨499,502,260,465,497,228,482,384,400⟩⟩,⟨6,1210106412364554692478049,⟨11,22,268,137,51,63,139,384,272⟩⟩,⟨8,1181745671430124618849,⟨11,22,12,137,51,127,203,128,16⟩⟩,⟨4,1210107565282760764425281,⟨11,6,268,137,33,109,203,384,256⟩⟩]⟩
theorem node950 : UpperPrefix a [3,4,8,7,0,2,1] 30 :=
  Boolean.leaf_sound a [3,4,8,7,0,2,1] 30 cert950 (by decide +kernel)

def cert951 : Leaf := ⟨⟨416,424,160,290,392,392,264,56,232⟩,[],[(4,1,7),(1,7,3)],⟨11,22,268,137,49,100,224,386,336⟩,⟨11,22,268,137,49,100,224,386,272⟩,[⟨0,1297654066351737333359616,⟨494,502,492,236,502,100,224,482,498⟩⟩,⟨2,1748485302681904321922179,⟨395,475,264,137,505,376,505,395,344⟩⟩,⟨6,1212504489098591721407991,⟨11,159,399,141,59,191,191,399,415⟩⟩]⟩
theorem node951 : UpperPrefix a [3,4,8,7,0,2,5,1] 30 :=
  Boolean.leaf_sound a [3,4,8,7,0,2,5,1] 30 cert951 (by decide +kernel)

def cert952 : Leaf := ⟨⟨420,424,178,294,388,384,260,36,166⟩,[],[(6,7,6)],⟨11,22,268,137,49,100,224,448,274⟩,⟨11,22,268,137,49,100,224,448,272⟩,[⟨0,1297689230457627842192384,⟨494,502,492,236,502,228,224,448,498⟩⟩,⟨3,1226922763510129842193409,⟨499,502,484,465,497,228,224,448,464⟩⟩,⟨4,1210145143529149454877699,⟨107,239,492,137,97,228,224,448,256⟩⟩,⟨1,1210145143530317417545729,⟨121,244,492,153,113,228,224,448,272⟩⟩]⟩
theorem node952 : UpperPrefix a [3,4,8,7,0,2,5,6] 30 :=
  Boolean.leaf_sound a [3,4,8,7,0,2,5,6] 30 cert952 (by decide +kernel)

theorem node953 : UpperPrefix a [3,4,8,7,0,2,5] 30 :=
  branch_upper a [3,4,8,7,0,2,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,0,2,5,0] 30 (by decide +kernel))
  node951
  (invalid_upper a [3,4,8,7,0,2,5,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,5,5] 30 (by decide +kernel))
  node952
  (invalid_upper a [3,4,8,7,0,2,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,5,8] 30 (by decide +kernel)))

theorem node954 : UpperPrefix a [3,4,8,7,0,2] 30 :=
  branch_upper a [3,4,8,7,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,0,2,0] 30 (by decide +kernel))
  node950
  (invalid_upper a [3,4,8,7,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,4] 30 (by decide +kernel))
  node953
  (invalid_upper a [3,4,8,7,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,2,8] 30 (by decide +kernel)))

theorem node955 : UpperPrefix a [3,4,8,7,0] 30 :=
  branch_upper a [3,4,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,0,0] 30 (by decide +kernel))
  node949
  node954
  (invalid_upper a [3,4,8,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,0,8] 30 (by decide +kernel)))

def cert956 : Leaf := ⟨⟨228,232,224,100,196,132,288,68,228⟩,[],[(8,2,6)],⟨11,22,268,137,50,97,196,416,336⟩,⟨11,22,268,137,50,97,196,416,272⟩,[⟨0,2391142664474764535714816,⟨334,470,334,478,498,502,470,498,400⟩⟩,⟨1,1295311905541076804698113,⟨493,468,492,237,508,237,196,492,468⟩⟩,⟨4,1212512821700153220006931,⟨107,239,492,237,107,97,196,492,493⟩⟩,⟨3,1451474096237947388953601,⟨499,470,452,433,498,497,196,416,400⟩⟩]⟩
theorem node956 : UpperPrefix a [3,4,8,7,1,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,1,0,2,5] 30 cert956 (by decide +kernel)

def cert957 : Leaf := ⟨⟨68,73,67,68,77,12,265,13,109⟩,[],[(8,2,6)],⟨11,22,268,137,50,97,196,448,304⟩,⟨11,22,268,137,50,97,196,448,272⟩,[⟨4,1212512821700153220006931,⟨107,239,492,237,107,97,196,492,493⟩⟩,⟨5,1212512810618201830458775,⟨75,223,463,205,91,73,205,463,479⟩⟩,⟨7,2342294931819042104710157,⟨15,279,271,287,306,371,375,370,272⟩⟩,⟨1,1285868451316152377802753,⟨233,468,460,169,496,105,196,448,400⟩⟩]⟩
theorem node957 : UpperPrefix a [3,4,8,7,1,0,2,6] 30 :=
  Boolean.leaf_sound a [3,4,8,7,1,0,2,6] 30 cert957 (by decide +kernel)

theorem node958 : UpperPrefix a [3,4,8,7,1,0,2] 30 :=
  branch_upper a [3,4,8,7,1,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,1,0,2,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,2,4] 30 (by decide +kernel))
  node956
  node957
  (invalid_upper a [3,4,8,7,1,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,2,8] 30 (by decide +kernel)))

def cert959 : Leaf := ⟨⟨228,224,224,356,196,132,4,100,228⟩,[],[],⟨11,22,268,137,50,97,224,452,340⟩,⟨11,22,268,137,50,97,224,384,272⟩,[⟨0,1370982485048398210941952,⟨398,470,268,140,498,502,498,384,336⟩⟩,⟨1,1297684581968760643256321,⟨493,468,492,237,508,237,232,384,468⟩⟩,⟨3,1238497627147849333476353,⟨499,470,502,241,498,113,224,384,336⟩⟩,⟨4,1212512821700153220006931,⟨107,239,492,237,107,97,228,492,493⟩⟩,⟨8,1181890242288460762117,⟨123,55,127,249,50,113,224,128,16⟩⟩]⟩
theorem node959 : UpperPrefix a [3,4,8,7,1,0,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,1,0,5] 30 cert959 (by decide +kernel)

#print axioms node959
end Delivery.FiniteExclusion.Sharp4x5
