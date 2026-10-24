import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C001
import RegularNineSharp4x5C002
import RegularNineSharp4x5C003
import RegularNineSharp4x5C004
import RegularNineSharp4x5C005
import RegularNineSharp4x5C006
import RegularNineSharp4x5C007
import RegularNineSharp4x5C008
import RegularNineSharp4x5C009
import RegularNineSharp4x5C010
import RegularNineSharp4x5C011
import RegularNineSharp4x5C012
import RegularNineSharp4x5C013
import RegularNineSharp4x5C014
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
theorem node960 : UpperPrefix a [3,4,8,7,1,0] 30 :=
  branch_upper a [3,4,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,1] 30 (by decide +kernel))
  node958
  (invalid_upper a [3,4,8,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,4] 30 (by decide +kernel))
  node959
  (invalid_upper a [3,4,8,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,0,8] 30 (by decide +kernel)))

def cert961 : Leaf := ⟨⟨480,480,227,0,452,387,0,98,226⟩,[(3,6),(6,3)],[(2,5,4)],⟨11,22,268,137,50,100,193,480,368⟩,⟨11,22,268,137,50,100,193,384,272⟩,[⟨3,1380444944319021516344321,⟨83,438,502,193,434,502,193,384,272⟩⟩,⟨0,1361518440643058709054464,⟨10,22,268,136,434,502,192,384,272⟩⟩,⟨4,1212510450097561162220563,⟨107,239,492,237,107,236,237,492,493⟩⟩]⟩
theorem node961 : UpperPrefix a [3,4,8,7,1,2,0] 30 :=
  Boolean.leaf_sound a [3,4,8,7,1,2,0] 30 cert961 (by decide +kernel)

def cert962 : Leaf := ⟨⟨432,416,178,0,388,402,274,50,226⟩,[(3,7)],[(2,5,4),(0,7,3)],⟨11,22,268,137,50,100,224,385,336⟩,⟨11,22,268,137,50,100,224,385,272⟩,[⟨3,2338836255328204397497345,⟨499,374,502,465,306,374,498,465,272⟩⟩,⟨6,1212504489098591721407991,⟨11,159,399,141,59,191,191,399,415⟩⟩]⟩
theorem node962 : UpperPrefix a [3,4,8,7,1,2,5,0] 30 :=
  Boolean.leaf_sound a [3,4,8,7,1,2,5,0] 30 cert962 (by decide +kernel)

def cert963 : Leaf := ⟨⟨416,416,163,290,388,386,258,34,163⟩,[],[(2,5,4),(6,7,6)],⟨11,22,268,137,50,100,224,448,273⟩,⟨11,22,268,137,50,100,224,448,272⟩,[⟨3,1252729470245882739837953,⟨499,246,502,465,114,246,242,464,272⟩⟩,⟨4,1212513404458908127331347,⟨107,239,492,237,107,228,228,492,493⟩⟩,⟨0,1210145143537326804192256,⟨122,246,510,152,114,246,242,464,272⟩⟩]⟩
theorem node963 : UpperPrefix a [3,4,8,7,1,2,5,6] 30 :=
  Boolean.leaf_sound a [3,4,8,7,1,2,5,6] 30 cert963 (by decide +kernel)

theorem node964 : UpperPrefix a [3,4,8,7,1,2,5] 30 :=
  branch_upper a [3,4,8,7,1,2,5] 30 (by decide) (fin9_cases _
  node962
  (invalid_upper a [3,4,8,7,1,2,5,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,5,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,5,5] 30 (by decide +kernel))
  node963
  (invalid_upper a [3,4,8,7,1,2,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,5,8] 30 (by decide +kernel)))

theorem node965 : UpperPrefix a [3,4,8,7,1,2] 30 :=
  branch_upper a [3,4,8,7,1,2] 30 (by decide) (fin9_cases _
  node961
  (invalid_upper a [3,4,8,7,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,4] 30 (by decide +kernel))
  node964
  (invalid_upper a [3,4,8,7,1,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,2,8] 30 (by decide +kernel)))

theorem node966 : UpperPrefix a [3,4,8,7,1] 30 :=
  branch_upper a [3,4,8,7,1] 30 (by decide) (fin9_cases _
  node960
  (invalid_upper a [3,4,8,7,1,1] 30 (by decide +kernel))
  node965
  (invalid_upper a [3,4,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,1,8] 30 (by decide +kernel)))

def cert967 : Leaf := ⟨⟨480,0,241,352,457,386,304,112,224⟩,[(1,4)],[(2,4,1),(1,6,5)],⟨11,22,268,137,52,97,194,480,368⟩,⟨11,22,268,137,52,97,194,384,272⟩,[⟨3,1285817938942730582369281,⟨99,470,324,161,502,97,194,448,466⟩⟩,⟨0,1285817938907547284022272,⟨74,470,332,136,502,96,194,448,466⟩⟩,⟨4,1210107567534560578110529,⟨11,6,268,137,36,105,235,384,256⟩⟩]⟩
theorem node967 : UpperPrefix a [3,4,8,7,2,0,1] 30 :=
  Boolean.leaf_sound a [3,4,8,7,2,0,1] 30 cert967 (by decide +kernel)

def cert968 : Leaf := ⟨⟨240,0,242,370,194,146,18,114,226⟩,[(1,4)],[(2,4,1)],⟨11,22,268,137,52,97,224,450,338⟩,⟨11,22,268,137,52,97,224,384,272⟩,[⟨0,1751870856677954986206208,⟨398,470,396,140,502,502,498,384,466⟩⟩,⟨3,1316574047900508594646017,⟨483,470,502,225,502,225,224,384,466⟩⟩,⟨8,1181890242219741293573,⟨123,55,127,233,55,97,224,128,18⟩⟩]⟩
theorem node968 : UpperPrefix a [3,4,8,7,2,0,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,2,0,5] 30 cert968 (by decide +kernel)

theorem node969 : UpperPrefix a [3,4,8,7,2,0] 30 :=
  branch_upper a [3,4,8,7,2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,2,0,0] 30 (by decide +kernel))
  node967
  (invalid_upper a [3,4,8,7,2,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,0,4] 30 (by decide +kernel))
  node968
  (invalid_upper a [3,4,8,7,2,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,0,8] 30 (by decide +kernel)))

def cert970 : Leaf := ⟨⟨496,0,241,0,457,409,0,121,233⟩,[(1,4),(3,6),(6,3)],[(2,4,1)],⟨11,22,268,137,52,98,193,480,368⟩,⟨11,22,268,137,52,98,193,384,272⟩,[⟨1,1361518584758255383216129,⟨73,20,332,201,436,508,201,384,272⟩⟩]⟩
theorem node970 : UpperPrefix a [3,4,8,7,2,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,7,2,1,0] 30 cert970 (by decide +kernel)

def cert971 : Leaf := ⟨⟨224,0,243,98,195,129,3,115,227⟩,[(1,4)],[(2,4,1)],⟨11,22,268,137,52,98,224,449,337⟩,⟨11,22,268,137,52,98,224,384,272⟩,[⟨3,1214913177111885448752129,⟨499,118,502,481,118,114,224,384,306⟩⟩,⟨8,1181889960753354517541,⟨123,55,127,233,55,123,233,128,18⟩⟩,⟨4,1210107709433133212369953,⟨107,6,332,233,37,107,233,384,256⟩⟩]⟩
theorem node971 : UpperPrefix a [3,4,8,7,2,1,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,2,1,5] 30 cert971 (by decide +kernel)

theorem node972 : UpperPrefix a [3,4,8,7,2,1] 30 :=
  branch_upper a [3,4,8,7,2,1] 30 (by decide) (fin9_cases _
  node970
  (invalid_upper a [3,4,8,7,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,1,4] 30 (by decide +kernel))
  node971
  (invalid_upper a [3,4,8,7,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,1,8] 30 (by decide +kernel)))

theorem node973 : UpperPrefix a [3,4,8,7,2] 30 :=
  branch_upper a [3,4,8,7,2] 30 (by decide) (fin9_cases _
  node969
  node972
  (invalid_upper a [3,4,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,2,8] 30 (by decide +kernel)))

def cert974 : Leaf := ⟨⟨128,425,177,0,0,138,317,61,173⟩,[(4,5)],[(6,4,4),(1,6,5)],⟨11,22,268,137,112,97,194,420,308⟩,⟨11,22,268,137,112,97,194,384,272⟩,[⟨2,1210107568105207111877697,⟨11,50,264,137,121,121,251,384,304⟩⟩,⟨4,1210107568097510531531841,⟨11,38,268,137,105,105,235,384,288⟩⟩,⟨8,1181748490577938220097,⟨11,54,12,137,121,121,251,128,48⟩⟩,⟨5,1210107564157960369210433,⟨11,22,268,137,89,73,203,384,272⟩⟩]⟩
theorem node974 : UpperPrefix a [3,4,8,7,6,0,1] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,0,1] 30 cert974 (by decide +kernel)

def cert975 : Local := ⟨⟨164,169,161,38,0,140,297,61,173⟩,[(4,5)],[(4,1,7),(8,2,6),(6,4,4),(1,7,3)]⟩
theorem node975 : UpperPrefix a [3,4,8,7,6,0,2,1] 30 :=
  local_sound a [3,4,8,7,6,0,2,1] 30 cert975 (by decide +kernel)

def cert976 : Leaf := ⟨⟨148,136,146,22,0,158,282,30,142⟩,[(4,5)],[(8,2,6),(6,4,4)],⟨11,22,268,137,112,97,196,416,274⟩,⟨11,22,268,137,112,97,196,416,272⟩,[⟨5,1295112610807828490626197,⟨335,279,335,205,351,77,205,463,279⟩⟩,⟨0,2391142664474764535714816,⟨334,470,334,478,498,502,470,498,400⟩⟩]⟩
theorem node976 : UpperPrefix a [3,4,8,7,6,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,0,2,5] 30 cert976 (by decide +kernel)

theorem node977 : UpperPrefix a [3,4,8,7,6,0,2] 30 :=
  branch_upper a [3,4,8,7,6,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,6,0,2,0] 30 (by decide +kernel))
  node975
  (invalid_upper a [3,4,8,7,6,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,0,2,4] 30 (by decide +kernel))
  node976
  (invalid_upper a [3,4,8,7,6,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,0,2,8] 30 (by decide +kernel)))

def cert978 : Leaf := ⟨⟨404,384,146,278,0,406,278,22,134⟩,[(4,5)],[(6,4,4),(5,6,4)],⟨11,22,268,137,112,97,224,390,278⟩,⟨11,22,268,137,112,97,224,384,272⟩,[⟨0,1370991708420435065717760,⟨398,470,268,140,498,502,498,384,336⟩⟩,⟨3,1238497338924620007345153,⟨499,470,502,241,112,113,240,384,272⟩⟩]⟩
theorem node978 : UpperPrefix a [3,4,8,7,6,0,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,0,5] 30 cert978 (by decide +kernel)

theorem node979 : UpperPrefix a [3,4,8,7,6,0] 30 :=
  branch_upper a [3,4,8,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,7,6,0,0] 30 (by decide +kernel))
  node974
  node977
  (invalid_upper a [3,4,8,7,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,0,4] 30 (by decide +kernel))
  node978
  (invalid_upper a [3,4,8,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,0,8] 30 (by decide +kernel)))

def cert980 : Leaf := ⟨⟨436,424,178,0,0,412,0,62,174⟩,[(3,6),(4,5),(6,3)],[(6,4,4)],⟨11,22,268,137,112,98,193,420,308⟩,⟨11,22,268,137,112,98,193,384,272⟩,[⟨0,1522392498529027522593792,⟨398,438,268,140,498,498,502,384,304⟩⟩]⟩
theorem node980 : UpperPrefix a [3,4,8,7,6,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,1,0] 30 cert980 (by decide +kernel)

def cert981 : Leaf := ⟨⟨176,32,179,50,0,20,315,59,171⟩,[(4,5)],[(8,2,6),(6,4,4),(2,6,5)],⟨11,22,268,137,112,98,196,417,305⟩,⟨11,22,268,137,112,98,196,384,272⟩,[⟨0,1210107568105198523024384,⟨10,54,268,136,114,114,246,384,304⟩⟩,⟨3,1210107568105197449282561,⟨3,54,260,129,114,114,246,384,304⟩⟩,⟨7,1208926976484481111720961,⟨11,54,268,9,114,114,118,256,304⟩⟩]⟩
theorem node981 : UpperPrefix a [3,4,8,7,6,1,2] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,1,2] 30 cert981 (by decide +kernel)

def cert982 : Leaf := ⟨⟨144,137,147,18,0,153,27,31,143⟩,[(4,5)],[(6,4,4),(5,6,4)],⟨11,22,268,137,112,98,224,389,277⟩,⟨11,22,268,137,112,98,224,384,272⟩,[⟨8,1181889967831460613157,⟨123,55,127,249,121,123,249,128,16⟩⟩,⟨2,1210107709441448268006433,⟨123,18,344,249,121,123,249,384,272⟩⟩]⟩
theorem node982 : UpperPrefix a [3,4,8,7,6,1,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,1,5] 30 cert982 (by decide +kernel)

theorem node983 : UpperPrefix a [3,4,8,7,6,1] 30 :=
  branch_upper a [3,4,8,7,6,1] 30 (by decide) (fin9_cases _
  node980
  (invalid_upper a [3,4,8,7,6,1,1] 30 (by decide +kernel))
  node981
  (invalid_upper a [3,4,8,7,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,1,4] 30 (by decide +kernel))
  node982
  (invalid_upper a [3,4,8,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,1,8] 30 (by decide +kernel)))

def cert984 : Leaf := ⟨⟨436,417,179,0,0,403,0,55,167⟩,[(3,6),(4,5),(6,3)],[(6,4,4)],⟨11,22,268,137,112,100,193,418,306⟩,⟨11,22,268,137,112,100,193,384,272⟩,[⟨3,1465613579721599586683905,⟨451,438,502,193,498,502,193,384,400⟩⟩]⟩
theorem node984 : UpperPrefix a [3,4,8,7,6,2,0] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,2,0] 30 cert984 (by decide +kernel)

def cert985 : Leaf := ⟨⟨128,160,179,2,0,411,313,59,171⟩,[(4,5)],[(6,4,4)],⟨11,22,268,137,112,100,194,417,305⟩,⟨11,22,268,137,112,100,194,384,272⟩,[⟨2,1437223914350375027606595,⟨75,475,264,137,505,505,203,384,408⟩⟩,⟨8,1181745671430124618865,⟨11,23,12,137,123,127,203,128,17⟩⟩,⟨4,1210107565282760764425281,⟨11,6,268,137,105,109,203,384,256⟩⟩,⟨5,1210107564157960369210433,⟨11,22,268,137,89,77,203,384,272⟩⟩,⟨0,1210107565286050709390336,⟨10,22,268,136,114,118,194,384,272⟩⟩,⟨3,1210107565286049635648513,⟨3,22,260,129,114,118,194,384,272⟩⟩]⟩
theorem node985 : UpperPrefix a [3,4,8,7,6,2,1] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,2,1] 30 cert985 (by decide +kernel)

def cert986 : Leaf := ⟨⟨144,136,147,18,0,411,287,27,139⟩,[(4,5)],[(6,4,4),(5,6,4)],⟨11,22,268,137,112,100,224,387,275⟩,⟨11,22,268,137,112,100,224,384,272⟩,[⟨2,1219579968372299012244483,⟨395,411,264,137,112,112,240,384,272⟩⟩,⟨8,1181745675828171129969,⟨11,23,12,137,123,127,251,128,17⟩⟩,⟨0,1210107565290448755901440,⟨10,22,268,136,114,118,242,384,272⟩⟩]⟩
theorem node986 : UpperPrefix a [3,4,8,7,6,2,5] 30 :=
  Boolean.leaf_sound a [3,4,8,7,6,2,5] 30 cert986 (by decide +kernel)

theorem node987 : UpperPrefix a [3,4,8,7,6,2] 30 :=
  branch_upper a [3,4,8,7,6,2] 30 (by decide) (fin9_cases _
  node984
  node985
  (invalid_upper a [3,4,8,7,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,2,4] 30 (by decide +kernel))
  node986
  (invalid_upper a [3,4,8,7,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,2,8] 30 (by decide +kernel)))

theorem node988 : UpperPrefix a [3,4,8,7,6] 30 :=
  branch_upper a [3,4,8,7,6] 30 (by decide) (fin9_cases _
  node979
  node983
  node987
  (invalid_upper a [3,4,8,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,6,8] 30 (by decide +kernel)))

theorem node989 : UpperPrefix a [3,4,8,7] 30 :=
  branch_upper a [3,4,8,7] 30 (by decide) (fin9_cases _
  node955
  node966
  node973
  (invalid_upper a [3,4,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,5] 30 (by decide +kernel))
  node988
  (invalid_upper a [3,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,7,8] 30 (by decide +kernel)))

theorem node990 : UpperPrefix a [3,4,8] 30 :=
  branch_upper a [3,4,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [3,4,8,1] [2,0,4,8] 30 (by decide +kernel) node44)
  (PrefixConjugacy.upper aut5 [3,4,8,2] [3,0,4,8] 30 (by decide +kernel) node494)
  (invalid_upper a [3,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,4] 30 (by decide +kernel))
  node908
  node946
  node989
  (invalid_upper a [3,4,8,8] 30 (by decide +kernel)))

theorem node991 : UpperPrefix a [3,4] 30 :=
  branch_upper a [3,4] 30 (by decide) (fin9_cases _
  node497
  node529
  (invalid_upper a [3,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,4] 30 (by decide +kernel))
  node626
  node748
  node874
  node990)

theorem node992 : UpperPrefix a [3] 30 :=
  branch_upper a [3] 30 (by decide) (fin9_cases _
  node496
  (invalid_upper a [3,1] 30 (by decide +kernel))
  (invalid_upper a [3,2] 30 (by decide +kernel))
  (invalid_upper a [3,3] 30 (by decide +kernel))
  node991
  (PrefixConjugacy.upper aut4 [3,5] [3,4] 30 (by decide +kernel) node991)
  (PrefixConjugacy.upper aut3 [3,6] [3,4] 30 (by decide +kernel) node991)
  (PrefixConjugacy.upper aut2 [3,7] [3,4] 30 (by decide +kernel) node991)
  (PrefixConjugacy.upper aut1 [3,8] [3,4] 30 (by decide +kernel) node991))

theorem node993 : UpperPrefix a [4,0,1] 30 :=
  branch_upper a [4,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,0,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut15 [4,0,1,2] [3,0,1,4] 30 (by decide +kernel) node459)
  (invalid_upper a [4,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,0,1,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut19 [4,0,1,5] [3,0,4,8] 30 (by decide +kernel) node494)
  (PrefixConjugacy.upper aut18 [4,0,1,6] [3,0,4,7] 30 (by decide +kernel) node487)
  (PrefixConjugacy.upper aut17 [4,0,1,7] [3,0,4,6] 30 (by decide +kernel) node472)
  (PrefixConjugacy.upper aut16 [4,0,1,8] [3,0,4,5] 30 (by decide +kernel) node461))

theorem node994 : UpperPrefix a [4,0,5] 30 :=
  branch_upper a [4,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,0,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,0,5,1] [2,4,1,5] 30 (by decide +kernel) node105)
  (PrefixConjugacy.upper aut5 [4,0,5,2] [3,4,1,5] 30 (by decide +kernel) node511)
  (invalid_upper a [4,0,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,0,5,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut19 [4,0,5,6] [3,4,5,8] 30 (by decide +kernel) node625)
  (PrefixConjugacy.upper aut19 [4,0,5,7] [3,4,6,8] 30 (by decide +kernel) node747)
  (PrefixConjugacy.upper aut19 [4,0,5,8] [3,4,7,8] 30 (by decide +kernel) node873))

theorem node995 : UpperPrefix a [4,0,6] 30 :=
  branch_upper a [4,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,0,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,0,6,1] [2,4,1,6] 30 (by decide +kernel) node119)
  (PrefixConjugacy.upper aut5 [4,0,6,2] [3,4,1,6] 30 (by decide +kernel) node528)
  (invalid_upper a [4,0,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,0,6,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [4,0,6,5] [3,4,8,7] 30 (by decide +kernel) node989)
  (invalid_upper a [4,0,6,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [4,0,6,7] [3,4,5,7] 30 (by decide +kernel) node596)
  (PrefixConjugacy.upper aut18 [4,0,6,8] [3,4,6,7] 30 (by decide +kernel) node713))

theorem node996 : UpperPrefix a [4,0,7] 30 :=
  branch_upper a [4,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,0,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,0,7,1] [2,4,1,7] 30 (by decide +kernel) node136)
  (PrefixConjugacy.upper aut17 [4,0,7,2] [3,4,1,6] 30 (by decide +kernel) node528)
  (invalid_upper a [4,0,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,0,7,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut17 [4,0,7,5] [3,4,7,6] 30 (by decide +kernel) node842)
  (PrefixConjugacy.upper aut17 [4,0,7,6] [3,4,8,6] 30 (by decide +kernel) node946)
  (invalid_upper a [4,0,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut17 [4,0,7,8] [3,4,5,6] 30 (by decide +kernel) node557))

theorem node997 : UpperPrefix a [4,0,8] 30 :=
  branch_upper a [4,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,0,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,0,8,1] [2,4,1,8] 30 (by decide +kernel) node137)
  (PrefixConjugacy.upper aut16 [4,0,8,2] [3,4,1,5] 30 (by decide +kernel) node511)
  (invalid_upper a [4,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,0,8,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut16 [4,0,8,5] [3,4,6,5] 30 (by decide +kernel) node671)
  (PrefixConjugacy.upper aut16 [4,0,8,6] [3,4,7,5] 30 (by decide +kernel) node797)
  (PrefixConjugacy.upper aut16 [4,0,8,7] [3,4,8,5] 30 (by decide +kernel) node908)
  (invalid_upper a [4,0,8,8] 30 (by decide +kernel)))

theorem node998 : UpperPrefix a [4,0] 30 :=
  branch_upper a [4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,0,0] 30 (by decide +kernel))
  node993
  (invalid_upper a [4,0,2] 30 (by decide +kernel))
  (invalid_upper a [4,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,0,4] 30 (by decide +kernel))
  node994
  node995
  node996
  node997)

theorem node999 : UpperPrefix a [4,3,0] 30 :=
  branch_upper a [4,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,3,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut15 [4,3,0,1] [2,3,0,4] 30 (by decide +kernel) node49)
  (PrefixConjugacy.upper aut10 [4,3,0,2] [2,0,4,1] 30 (by decide +kernel) node2)
  (invalid_upper a [4,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,3,0,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut19 [4,3,0,5] [2,3,4,8] 30 (by decide +kernel) node81)
  (PrefixConjugacy.upper aut18 [4,3,0,6] [2,3,4,7] 30 (by decide +kernel) node80)
  (PrefixConjugacy.upper aut17 [4,3,0,7] [2,3,4,6] 30 (by decide +kernel) node61)
  (PrefixConjugacy.upper aut16 [4,3,0,8] [2,3,4,5] 30 (by decide +kernel) node50))

theorem node1000 : UpperPrefix a [4,3,1] 30 :=
  branch_upper a [4,3,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,3,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,3,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut15 [4,3,1,2] [2,0,1,4] 30 (by decide +kernel) node0)
  (invalid_upper a [4,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,3,1,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut19 [4,3,1,5] [2,0,4,8] 30 (by decide +kernel) node44)
  (PrefixConjugacy.upper aut18 [4,3,1,6] [2,0,4,7] 30 (by decide +kernel) node39)
  (PrefixConjugacy.upper aut17 [4,3,1,7] [2,0,4,6] 30 (by decide +kernel) node25)
  (PrefixConjugacy.upper aut16 [4,3,1,8] [2,0,4,5] 30 (by decide +kernel) node11))

theorem node1001 : UpperPrefix a [4,3,5] 30 :=
  branch_upper a [4,3,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,3,5,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,3,5,1] [2,4,0,5] 30 (by decide +kernel) node84)
  (PrefixConjugacy.upper aut19 [4,3,5,2] [2,4,1,8] 30 (by decide +kernel) node137)
  (invalid_upper a [4,3,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,3,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,3,5,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut19 [4,3,5,6] [2,4,5,8] 30 (by decide +kernel) node185)
  (PrefixConjugacy.upper aut19 [4,3,5,7] [2,4,6,8] 30 (by decide +kernel) node270)
  (PrefixConjugacy.upper aut19 [4,3,5,8] [2,4,7,8] 30 (by decide +kernel) node370))

theorem node1002 : UpperPrefix a [4,3,6] 30 :=
  branch_upper a [4,3,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,3,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,3,6,1] [2,4,0,6] 30 (by decide +kernel) node95)
  (PrefixConjugacy.upper aut18 [4,3,6,2] [2,4,1,7] 30 (by decide +kernel) node136)
  (invalid_upper a [4,3,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,3,6,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [4,3,6,5] [2,4,8,7] 30 (by decide +kernel) node454)
  (invalid_upper a [4,3,6,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [4,3,6,7] [2,4,5,7] 30 (by decide +kernel) node173)
  (PrefixConjugacy.upper aut18 [4,3,6,8] [2,4,6,7] 30 (by decide +kernel) node244))

theorem node1003 : UpperPrefix a [4,3,7] 30 :=
  branch_upper a [4,3,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,3,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut17 [4,3,7,1] [2,4,0,6] 30 (by decide +kernel) node95)
  (PrefixConjugacy.upper aut17 [4,3,7,2] [2,4,1,6] 30 (by decide +kernel) node119)
  (invalid_upper a [4,3,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,3,7,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut17 [4,3,7,5] [2,4,7,6] 30 (by decide +kernel) node336)
  (PrefixConjugacy.upper aut17 [4,3,7,6] [2,4,8,6] 30 (by decide +kernel) node420)
  (invalid_upper a [4,3,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut17 [4,3,7,8] [2,4,5,6] 30 (by decide +kernel) node152))

theorem node1004 : UpperPrefix a [4,3,8] 30 :=
  branch_upper a [4,3,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,3,8,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut16 [4,3,8,1] [2,4,0,5] 30 (by decide +kernel) node84)
  (PrefixConjugacy.upper aut16 [4,3,8,2] [2,4,1,5] 30 (by decide +kernel) node105)
  (invalid_upper a [4,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,3,8,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut16 [4,3,8,5] [2,4,6,5] 30 (by decide +kernel) node212)
  (PrefixConjugacy.upper aut16 [4,3,8,6] [2,4,7,5] 30 (by decide +kernel) node301)
  (PrefixConjugacy.upper aut16 [4,3,8,7] [2,4,8,5] 30 (by decide +kernel) node391)
  (invalid_upper a [4,3,8,8] 30 (by decide +kernel)))

theorem node1005 : UpperPrefix a [4,3] 30 :=
  branch_upper a [4,3] 30 (by decide) (fin9_cases _
  node999
  node1000
  (invalid_upper a [4,3,2] 30 (by decide +kernel))
  (invalid_upper a [4,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,3,4] 30 (by decide +kernel))
  node1001
  node1002
  node1003
  node1004)

theorem node1006 : UpperPrefix a [4,5,0] 30 :=
  branch_upper a [4,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,5,0,1] [2,3,4,5] 30 (by decide +kernel) node50)
  (PrefixConjugacy.upper aut10 [4,5,0,2] [2,0,4,5] 30 (by decide +kernel) node11)
  (invalid_upper a [4,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,0,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut13 [4,5,0,6] [2,4,7,8] 30 (by decide +kernel) node370)
  (PrefixConjugacy.upper aut12 [4,5,0,7] [2,4,6,7] 30 (by decide +kernel) node244)
  (PrefixConjugacy.upper aut11 [4,5,0,8] [2,4,5,6] 30 (by decide +kernel) node152))

theorem node1007 : UpperPrefix a [4,5,1] 30 :=
  branch_upper a [4,5,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,5,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,5,1,2] [3,0,4,5] 30 (by decide +kernel) node461)
  (invalid_upper a [4,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,1,5] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut13 [4,5,1,6] [3,4,7,8] 30 (by decide +kernel) node873)
  (PrefixConjugacy.upper aut12 [4,5,1,7] [3,4,6,7] 30 (by decide +kernel) node713)
  (PrefixConjugacy.upper aut11 [4,5,1,8] [3,4,5,6] 30 (by decide +kernel) node557))

def cert1008 : Leaf := ⟨⟨36,81,145,20,6,21,285,29,13⟩,[],[(5,1,0),(6,2,1),(7,3,2),(1,5,4)],⟨19,38,76,137,49,98,460,396,284⟩,⟨19,38,76,137,49,98,192,384,272⟩,[⟨8,1181748068794995109239,⟨19,55,127,137,55,127,255,137,19⟩⟩,⟨3,1210107565427199440849959,⟨19,55,119,129,49,115,192,384,272⟩⟩]⟩
theorem node1008 : UpperPrefix a [4,5,6,7,0,1] 30 :=
  Boolean.leaf_sound a [4,5,6,7,0,1] 30 cert1008 (by decide +kernel)

def cert1009 : Local := ⟨⟨296,0,403,274,266,0,283,27,11⟩,[(1,5),(5,2)],[(5,1,0),(6,2,1),(6,2,5),(7,3,2),(2,5,1)]⟩
theorem node1009 : UpperPrefix a [4,5,6,7,0,2] 30 :=
  local_sound a [4,5,6,7,0,2] 30 cert1009 (by decide +kernel)

def cert1010 : Local := ⟨⟨292,345,0,278,262,0,279,23,7⟩,[(2,5),(5,2)],[(5,1,0),(6,2,1),(7,3,2),(7,3,5),(3,5,1)]⟩
theorem node1010 : UpperPrefix a [4,5,6,7,0,3] 30 :=
  local_sound a [4,5,6,7,0,3] 30 cert1010 (by decide +kernel)

def cert1011 : Leaf := ⟨⟨296,329,387,258,266,11,269,11,11⟩,[],[(5,1,0),(6,2,1),(7,3,2),(2,7,6)],⟨19,38,76,137,49,352,194,388,280⟩,⟨19,38,76,137,49,352,194,388,272⟩,[⟨4,1212771872304308644443137,⟨79,230,78,239,239,486,226,486,494⟩⟩]⟩
theorem node1011 : UpperPrefix a [4,5,6,7,0,8,1,2] 30 :=
  Boolean.leaf_sound a [4,5,6,7,0,8,1,2] 30 cert1011 (by decide +kernel)

def cert1012 : Leaf := ⟨⟨288,337,403,274,258,23,281,19,7⟩,[],[(5,1,0),(6,2,1),(7,3,2)],⟨19,38,76,137,49,352,194,392,276⟩,⟨19,38,76,137,49,352,194,392,272⟩,[⟨2,1212763932461614642496579,⟨91,251,73,137,185,505,219,392,408⟩⟩,⟨3,1238441766580615172328519,⟨275,311,375,129,49,369,499,384,272⟩⟩]⟩
theorem node1012 : UpperPrefix a [4,5,6,7,0,8,1,3] 30 :=
  Boolean.leaf_sound a [4,5,6,7,0,8,1,3] 30 cert1012 (by decide +kernel)

theorem node1013 : UpperPrefix a [4,5,6,7,0,8,1] 30 :=
  branch_upper a [4,5,6,7,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,6,7,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,1,1] 30 (by decide +kernel))
  node1011
  node1012
  (invalid_upper a [4,5,6,7,0,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,1,8] 30 (by decide +kernel)))

def cert1014 : Leaf := ⟨⟨40,345,146,274,10,31,26,27,11⟩,[],[(5,1,0),(6,2,1),(7,3,2)],⟨19,38,76,137,49,352,196,394,282⟩,⟨19,38,76,137,49,352,196,384,272⟩,[⟨2,1224302334848711174128643,⟨411,443,72,393,441,352,192,384,280⟩⟩,⟨8,1181889784548028318723,⟨19,55,76,205,49,96,196,128,16⟩⟩,⟨0,1210107709399039764071424,⟨18,38,76,204,48,352,196,384,272⟩⟩]⟩
theorem node1014 : UpperPrefix a [4,5,6,7,0,8,2] 30 :=
  Boolean.leaf_sound a [4,5,6,7,0,8,2] 30 cert1014 (by decide +kernel)

def cert1015 : Local := ⟨⟨292,337,0,278,262,23,0,23,7⟩,[(2,6),(6,3)],[(5,1,0),(6,2,1),(7,3,2),(7,3,6),(3,6,2)]⟩
theorem node1015 : UpperPrefix a [4,5,6,7,0,8,3] 30 :=
  local_sound a [4,5,6,7,0,8,3] 30 cert1015 (by decide +kernel)

theorem node1016 : UpperPrefix a [4,5,6,7,0,8] 30 :=
  branch_upper a [4,5,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,6,7,0,8,0] 30 (by decide +kernel))
  node1013
  node1014
  node1015
  (invalid_upper a [4,5,6,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,8,8] 30 (by decide +kernel)))

theorem node1017 : UpperPrefix a [4,5,6,7,0] 30 :=
  branch_upper a [4,5,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,6,7,0,0] 30 (by decide +kernel))
  node1008
  node1009
  node1010
  (invalid_upper a [4,5,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,0,7] 30 (by decide +kernel))
  node1016)

def cert1018 : Local := ⟨⟨0,345,401,276,0,285,285,29,13⟩,[(0,4),(4,1)],[(5,1,0),(5,1,4),(6,2,1),(7,3,2),(1,4,0)]⟩
theorem node1018 : UpperPrefix a [4,5,6,7,1] 30 :=
  local_sound a [4,5,6,7,1] 30 cert1018 (by decide +kernel)

def cert1019 : Local := ⟨⟨300,0,403,274,0,283,283,27,11⟩,[(1,4),(4,1)],[(5,1,0),(6,2,1),(6,2,4),(7,3,2),(2,4,0)]⟩
theorem node1019 : UpperPrefix a [4,5,6,7,2] 30 :=
  local_sound a [4,5,6,7,2] 30 cert1019 (by decide +kernel)

def cert1020 : Leaf := ⟨⟨44,88,144,20,5,30,28,28,12⟩,[],[(5,1,0),(6,2,1),(7,3,2),(0,5,4),(1,6,5)],⟨19,38,76,137,56,97,194,388,276⟩,⟨19,38,76,137,56,97,194,384,272⟩,[⟨8,1184203384225292091391,⟨55,55,127,255,127,127,255,255,55⟩⟩]⟩
theorem node1020 : UpperPrefix a [4,5,6,7,3,0,1] 30 :=
  Boolean.leaf_sound a [4,5,6,7,3,0,1] 30 cert1020 (by decide +kernel)

def cert1021 : Leaf := ⟨⟨44,88,146,22,7,30,26,30,14⟩,[],[(5,1,0),(6,2,1),(7,3,2),(0,5,4)],⟨19,38,76,137,56,97,196,386,274⟩,⟨19,38,76,137,56,97,196,384,272⟩,[⟨8,1184203384225292091391,⟨55,55,127,255,127,127,255,255,55⟩⟩]⟩
theorem node1021 : UpperPrefix a [4,5,6,7,3,0,2] 30 :=
  Boolean.leaf_sound a [4,5,6,7,3,0,2] 30 cert1021 (by decide +kernel)

def cert1022 : Local := ⟨⟨44,88,146,22,7,30,0,30,14⟩,[(6,7)],[(5,1,0),(6,2,1),(7,3,2),(0,5,4),(8,6,6)]⟩
theorem node1022 : UpperPrefix a [4,5,6,7,3,0,8] 30 :=
  local_sound a [4,5,6,7,3,0,8] 30 cert1022 (by decide +kernel)

theorem node1023 : UpperPrefix a [4,5,6,7,3,0] 30 :=
  branch_upper a [4,5,6,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,5,6,7,3,0,0] 30 (by decide +kernel))
  node1020
  node1021
  (invalid_upper a [4,5,6,7,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,0,4] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [4,5,6,7,3,0,7] 30 (by decide +kernel))
  node1022)

#print axioms node1023
end Delivery.FiniteExclusion.Sharp4x5
