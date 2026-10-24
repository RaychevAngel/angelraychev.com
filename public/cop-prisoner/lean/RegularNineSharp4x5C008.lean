import RegularNineSharp4x5Base
import RegularNineSharp4x5C007
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert512 : Leaf := ⟨⟨0,488,0,436,452,404,308,116,228⟩,[(0,2),(2,0)],[],⟨11,22,14,73,49,484,484,420,436⟩,⟨11,22,14,73,49,96,192,384,272⟩,[⟨1,1219607746779378248318977,⟨505,500,492,89,57,96,192,384,272⟩⟩,⟨0,1295322714672759236207616,⟨494,502,494,236,502,96,192,384,498⟩⟩,⟨3,1219607746779377040360449,⟨499,502,486,81,49,96,192,384,272⟩⟩]⟩
theorem node512 : UpperPrefix a [3,4,1,6,0] 30 :=
  Boolean.leaf_sound a [3,4,1,6,0] 30 cert512 (by decide +kernel)

def cert513 : Leaf := ⟨⟨0,0,0,50,75,411,315,59,171⟩,[(0,2),(1,4),(2,0)],[(2,4,1)],⟨11,22,14,73,52,481,481,417,433⟩,⟨11,22,14,73,52,96,192,384,272⟩,[⟨6,1285811850040851079373829,⟨15,407,15,13,439,32,128,384,402⟩⟩,⟨7,1208926973665337606038581,⟨15,23,15,77,63,127,64,258,279⟩⟩,⟨8,1181745671425842635829,⟨15,23,15,77,63,127,192,130,23⟩⟩]⟩
theorem node513 : UpperPrefix a [3,4,1,6,2] 30 :=
  Boolean.leaf_sound a [3,4,1,6,2] 30 cert513 (by decide +kernel)

def cert514 : Leaf := ⟨⟨0,488,0,0,334,0,318,126,238⟩,[(0,2),(2,0),(3,5),(5,3)],[],⟨11,22,14,73,176,97,484,420,308⟩,⟨11,22,14,73,176,97,192,384,272⟩,[⟨0,1361519017103811012740096,⟨14,22,14,76,498,502,192,384,272⟩⟩]⟩
theorem node514 : UpperPrefix a [3,4,1,6,7,0] 30 :=
  Boolean.leaf_sound a [3,4,1,6,7,0] 30 cert514 (by decide +kernel)

def cert515 : Leaf := ⟨⟨0,41,0,50,11,27,315,59,43⟩,[(0,2),(2,0)],[],⟨11,22,14,73,176,100,481,417,305⟩,⟨11,22,14,73,176,100,192,384,272⟩,[⟨2,1361519017103815306380293,⟨11,19,11,73,504,505,192,384,272⟩⟩,⟨6,1361517287721554102469637,⟨15,23,15,13,434,439,128,384,272⟩⟩,⟨7,1284484837670527874507797,⟨47,279,47,109,319,109,64,258,279⟩⟩,⟨8,1181748206908265133181,⟨47,23,47,127,191,127,255,130,23⟩⟩]⟩
theorem node515 : UpperPrefix a [3,4,1,6,7,2] 30 :=
  Boolean.leaf_sound a [3,4,1,6,7,2] 30 cert515 (by decide +kernel)

def cert516 : Leaf := ⟨⟨0,200,0,0,334,158,30,126,238⟩,[(0,2),(2,0),(3,6)],[(8,5,4),(0,6,3)],⟨11,22,14,73,176,352,193,420,308⟩,⟨11,22,14,73,176,352,193,384,272⟩,[⟨5,1210110158231404099282359,⟨15,95,15,77,223,335,205,463,351⟩⟩]⟩
theorem node516 : UpperPrefix a [3,4,1,6,7,8,0] 30 :=
  Boolean.leaf_sound a [3,4,1,6,7,8,0] 30 cert516 (by decide +kernel)

def cert517 : Leaf := ⟨⟨0,225,0,182,325,149,49,117,229⟩,[(0,2),(2,0)],[(8,5,4)],⟨11,22,14,73,176,352,196,417,305⟩,⟨11,22,14,73,176,352,196,384,272⟩,[⟨3,1252691946463107015019521,⟨435,118,502,499,176,370,246,384,272⟩⟩,⟨1,1252691946463108088725505,⟨441,116,508,505,176,368,244,384,272⟩⟩]⟩
theorem node517 : UpperPrefix a [3,4,1,6,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,1,6,7,8,2] 30 cert517 (by decide +kernel)

def cert518 : Local := ⟨⟨0,233,0,182,0,159,0,127,239⟩,[(0,2),(2,0),(4,6),(6,4)],[(8,5,4),(8,5,6)]⟩
theorem node518 : UpperPrefix a [3,4,1,6,7,8,5] 30 :=
  local_sound a [3,4,1,6,7,8,5] 30 cert518 (by decide +kernel)

theorem node519 : UpperPrefix a [3,4,1,6,7,8] 30 :=
  branch_upper a [3,4,1,6,7,8] 30 (by decide) (fin9_cases _
  node516
  (invalid_upper a [3,4,1,6,7,8,1] 30 (by decide +kernel))
  node517
  (invalid_upper a [3,4,1,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,7,8,4] 30 (by decide +kernel))
  node518
  (invalid_upper a [3,4,1,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,7,8,8] 30 (by decide +kernel)))

theorem node520 : UpperPrefix a [3,4,1,6,7] 30 :=
  branch_upper a [3,4,1,6,7] 30 (by decide) (fin9_cases _
  node514
  (invalid_upper a [3,4,1,6,7,1] 30 (by decide +kernel))
  node515
  (invalid_upper a [3,4,1,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,7,7] 30 (by decide +kernel))
  node519)

def cert521 : Leaf := ⟨⟨0,488,0,0,206,0,318,126,238⟩,[(0,2),(2,0),(3,5),(5,3)],[],⟨11,22,14,73,304,97,228,420,436⟩,⟨11,22,14,73,304,97,192,384,272⟩,[⟨0,1361519017103811012740096,⟨14,22,14,76,498,502,192,384,272⟩⟩]⟩
theorem node521 : UpperPrefix a [3,4,1,6,8,0] 30 :=
  Boolean.leaf_sound a [3,4,1,6,8,0] 30 cert521 (by decide +kernel)

def cert522 : Leaf := ⟨⟨0,41,0,50,139,27,59,59,171⟩,[(0,2),(2,0)],[],⟨11,22,14,73,304,100,225,417,433⟩,⟨11,22,14,73,304,100,192,384,272⟩,[⟨2,1361519017103815306380293,⟨11,19,11,73,504,505,192,384,272⟩⟩,⟨6,1361517287721554102469637,⟨15,23,15,13,434,439,128,384,272⟩⟩,⟨8,1184058549136245793941,⟨47,23,47,109,63,109,237,239,23⟩⟩,⟨7,1208926973944613551088661,⟨47,23,47,109,319,109,64,258,279⟩⟩]⟩
theorem node522 : UpperPrefix a [3,4,1,6,8,2] 30 :=
  Boolean.leaf_sound a [3,4,1,6,8,2] 30 cert522 (by decide +kernel)

def cert523 : Local := ⟨⟨0,360,0,0,78,0,318,126,110⟩,[(0,2),(2,0),(3,6),(5,6)],[(7,5,5),(0,6,3)]⟩
theorem node523 : UpperPrefix a [3,4,1,6,8,7,0] 30 :=
  local_sound a [3,4,1,6,8,7,0] 30 cert523 (by decide +kernel)

def cert524 : Leaf := ⟨⟨0,353,0,310,71,0,307,119,103⟩,[(0,2),(2,0),(5,6)],[(7,5,5)],⟨11,22,14,73,304,224,196,417,305⟩,⟨11,22,14,73,304,224,196,384,272⟩,[⟨3,1252691948710508782193665,⟨435,118,502,499,304,226,246,384,272⟩⟩]⟩
theorem node524 : UpperPrefix a [3,4,1,6,8,7,2] 30 :=
  Boolean.leaf_sound a [3,4,1,6,8,7,2] 30 cert524 (by decide +kernel)

def cert525 : Local := ⟨⟨0,361,0,310,79,0,0,127,111⟩,[(0,2),(2,0),(5,6),(6,5)],[(7,5,5),(7,5,6)]⟩
theorem node525 : UpperPrefix a [3,4,1,6,8,7,5] 30 :=
  local_sound a [3,4,1,6,8,7,5] 30 cert525 (by decide +kernel)

theorem node526 : UpperPrefix a [3,4,1,6,8,7] 30 :=
  branch_upper a [3,4,1,6,8,7] 30 (by decide) (fin9_cases _
  node523
  (invalid_upper a [3,4,1,6,8,7,1] 30 (by decide +kernel))
  node524
  (invalid_upper a [3,4,1,6,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,8,7,4] 30 (by decide +kernel))
  node525
  (invalid_upper a [3,4,1,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,8,7,8] 30 (by decide +kernel)))

theorem node527 : UpperPrefix a [3,4,1,6,8] 30 :=
  branch_upper a [3,4,1,6,8] 30 (by decide) (fin9_cases _
  node521
  (invalid_upper a [3,4,1,6,8,1] 30 (by decide +kernel))
  node522
  (invalid_upper a [3,4,1,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,8,6] 30 (by decide +kernel))
  node526
  (invalid_upper a [3,4,1,6,8,8] 30 (by decide +kernel)))

theorem node528 : UpperPrefix a [3,4,1,6] 30 :=
  branch_upper a [3,4,1,6] 30 (by decide) (fin9_cases _
  node512
  (invalid_upper a [3,4,1,6,1] 30 (by decide +kernel))
  node513
  (invalid_upper a [3,4,1,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,6,6] 30 (by decide +kernel))
  node520
  node527)

theorem node529 : UpperPrefix a [3,4,1] 30 :=
  branch_upper a [3,4,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [3,4,1,2] [3,0,1,4] 30 (by decide +kernel) node459)
  (invalid_upper a [3,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,1,4] 30 (by decide +kernel))
  node511
  node528
  (PrefixConjugacy.upper aut12 [3,4,1,7] [3,4,1,6] 30 (by decide +kernel) node528)
  (PrefixConjugacy.upper aut11 [3,4,1,8] [3,4,1,5] 30 (by decide +kernel) node511))

def cert530 : Leaf := ⟨⟨20,40,82,22,6,406,278,22,134⟩,[],[(5,2,1),(6,3,2)],⟨11,22,44,73,49,486,454,390,406⟩,⟨11,22,44,73,49,96,192,384,272⟩,[⟨0,1295285748986280292918272,⟨494,502,44,236,502,96,192,384,498⟩⟩,⟨3,1219570781092898094973953,⟨499,502,36,81,49,96,192,384,272⟩⟩,⟨7,1208926973665612483685429,⟨11,23,63,73,63,127,64,258,279⟩⟩,⟨8,1181745671700720282677,⟨11,23,63,73,63,127,192,130,23⟩⟩]⟩
theorem node530 : UpperPrefix a [3,4,5,6,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,0] 30 cert530 (by decide +kernel)

def cert531 : Leaf := ⟨⟨404,416,467,0,388,0,278,22,134⟩,[(3,5),(5,3)],[(5,2,1),(6,3,2),(0,5,2)],⟨11,22,44,73,50,97,452,388,404⟩,⟨11,22,44,73,50,97,192,384,272⟩,[⟨3,1238497212816683615390721,⟨499,470,502,113,498,113,192,384,272⟩⟩]⟩
theorem node531 : UpperPrefix a [3,4,5,6,1,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,1,0] 30 cert531 (by decide +kernel)

def cert532 : Leaf := ⟨⟨272,289,339,274,261,275,275,19,131⟩,[],[(5,2,1),(6,3,2),(2,5,4)],⟨11,22,44,73,50,100,449,385,401⟩,⟨11,22,44,73,50,100,192,384,272⟩,[⟨3,1214913104387987364400129,⟨467,54,246,449,50,118,192,384,272⟩⟩,⟨7,1208926976203912404991613,⟨63,23,63,127,63,127,127,258,279⟩⟩]⟩
theorem node532 : UpperPrefix a [3,4,5,6,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,1,2] 30 cert532 (by decide +kernel)

def cert533 : Leaf := ⟨⟨20,41,83,22,13,0,287,31,15⟩,[(5,6)],[(5,2,1),(6,3,2),(7,5,5)],⟨11,22,44,73,50,224,453,389,277⟩,⟨11,22,44,73,50,224,192,384,272⟩,[⟨8,1181747928456945139325,⟨31,23,63,127,63,255,255,130,23⟩⟩]⟩
theorem node533 : UpperPrefix a [3,4,5,6,1,7] 30 :=
  Boolean.leaf_sound a [3,4,5,6,1,7] 30 cert533 (by decide +kernel)

def cert534 : Leaf := ⟨⟨404,416,466,0,388,150,278,22,134⟩,[(3,6)],[(5,2,1),(6,3,2),(0,6,3)],⟨11,22,44,73,50,352,193,388,404⟩,⟨11,22,44,73,50,352,193,384,272⟩,[⟨3,1238497122463216091270145,⟨499,406,438,113,434,352,241,384,272⟩⟩]⟩
theorem node534 : UpperPrefix a [3,4,5,6,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,1,8,0] 30 cert534 (by decide +kernel)

def cert535 : Leaf := ⟨⟨260,289,323,262,261,135,259,7,135⟩,[],[(5,2,1),(6,3,2)],⟨11,22,44,73,50,352,196,385,401⟩,⟨11,22,44,73,50,352,196,384,272⟩,[⟨3,1252691946465443477228545,⟨435,118,502,499,50,370,246,384,272⟩⟩,⟨4,1212476256024802444182547,⟨11,15,108,73,111,492,228,492,493⟩⟩,⟨7,1208926973665621073652861,⟨11,23,63,75,63,383,95,258,279⟩⟩]⟩
theorem node535 : UpperPrefix a [3,4,5,6,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,1,8,2] 30 cert535 (by decide +kernel)

theorem node536 : UpperPrefix a [3,4,5,6,1,8] 30 :=
  branch_upper a [3,4,5,6,1,8] 30 (by decide) (fin9_cases _
  node534
  (invalid_upper a [3,4,5,6,1,8,1] 30 (by decide +kernel))
  node535
  (invalid_upper a [3,4,5,6,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,8,8] 30 (by decide +kernel)))

theorem node537 : UpperPrefix a [3,4,5,6,1] 30 :=
  branch_upper a [3,4,5,6,1] 30 (by decide) (fin9_cases _
  node531
  (invalid_upper a [3,4,5,6,1,1] 30 (by decide +kernel))
  node532
  (invalid_upper a [3,4,5,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,1,6] 30 (by decide +kernel))
  node533
  node536)

def cert538 : Leaf := ⟨⟨272,0,339,274,0,411,283,27,139⟩,[(1,4),(4,2)],[(5,2,1),(5,2,4),(6,3,2),(2,4,1)],⟨11,22,44,73,52,483,451,387,403⟩,⟨11,22,44,73,52,96,192,384,272⟩,[⟨7,1208926973665612483685429,⟨11,23,63,73,63,127,64,258,279⟩⟩]⟩
theorem node538 : UpperPrefix a [3,4,5,6,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,2] 30 cert538 (by decide +kernel)

def cert539 : Leaf := ⟨⟨404,416,467,0,262,0,278,22,134⟩,[(3,5),(5,3)],[(5,2,1),(6,3,2),(0,5,2)],⟨11,22,44,73,176,97,454,390,278⟩,⟨11,22,44,73,176,97,192,384,272⟩,[⟨3,1238497212816683615390721,⟨499,470,502,113,176,113,192,384,272⟩⟩]⟩
theorem node539 : UpperPrefix a [3,4,5,6,7,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,0] 30 cert539 (by decide +kernel)

def cert540 : Leaf := ⟨⟨404,416,466,0,262,404,278,22,134⟩,[(3,6)],[(5,2,1),(6,3,2),(0,6,3)],⟨11,22,44,73,176,98,193,388,276⟩,⟨11,22,44,73,176,98,193,384,272⟩,[⟨3,1238497122469813161036801,⟨499,406,438,113,176,498,241,384,272⟩⟩]⟩
theorem node540 : UpperPrefix a [3,4,5,6,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,1,0] 30 cert540 (by decide +kernel)

def cert541 : Leaf := ⟨⟨144,161,211,146,3,149,19,19,131⟩,[],[(5,2,1),(6,3,2),(2,6,5)],⟨11,22,44,73,176,98,196,385,273⟩,⟨11,22,44,73,176,98,196,384,272⟩,[⟨8,1184356433261360051711,⟨47,127,47,127,255,127,255,255,127⟩⟩,⟨3,1252691948785275572882433,⟨435,118,502,499,176,114,246,384,272⟩⟩]⟩
theorem node541 : UpperPrefix a [3,4,5,6,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,1,2] 30 cert541 (by decide +kernel)

def cert542 : Leaf := ⟨⟨20,41,83,22,15,29,0,31,15⟩,[(6,7)],[(5,2,1),(6,3,2),(8,6,6)],⟨11,22,44,73,176,98,448,389,277⟩,⟨11,22,44,73,176,98,448,384,272⟩,[⟨7,1293929572606600618845297,⟨271,279,45,109,319,367,367,258,279⟩⟩]⟩
theorem node542 : UpperPrefix a [3,4,5,6,7,1,8] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,1,8] 30 cert542 (by decide +kernel)

theorem node543 : UpperPrefix a [3,4,5,6,7,1] 30 :=
  branch_upper a [3,4,5,6,7,1] 30 (by decide) (fin9_cases _
  node540
  (invalid_upper a [3,4,5,6,7,1,1] 30 (by decide +kernel))
  node541
  (invalid_upper a [3,4,5,6,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,1,7] 30 (by decide +kernel))
  node542)

def cert544 : Leaf := ⟨⟨144,169,192,146,15,136,283,27,139⟩,[],[(5,2,1),(6,3,2)],⟨11,22,44,73,176,100,451,387,275⟩,⟨11,22,44,73,176,100,192,384,272⟩,[⟨8,1181748206908265133181,⟨47,23,47,127,191,127,255,130,23⟩⟩,⟨2,1219580022408897470923779,⟨459,475,40,201,176,96,192,384,272⟩⟩,⟨0,1210107565565326665188352,⟨46,22,44,108,176,100,192,384,272⟩⟩,⟨1,1210107565565326665187329,⟨45,20,44,109,176,100,192,384,272⟩⟩,⟨4,1210107565564227153560577,⟨47,6,44,109,160,100,192,384,256⟩⟩]⟩
theorem node544 : UpperPrefix a [3,4,5,6,7,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,2] 30 cert544 (by decide +kernel)

def cert545 : Leaf := ⟨⟨148,160,210,0,262,150,22,22,134⟩,[(3,6)],[(5,2,1),(6,3,2),(8,5,4),(0,6,3)],⟨11,22,44,73,176,352,193,390,278⟩,⟨11,22,44,73,176,352,193,384,272⟩,[⟨3,1238497122467614137781249,⟨499,406,438,113,176,368,241,384,272⟩⟩]⟩
theorem node545 : UpperPrefix a [3,4,5,6,7,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,8,0] 30 cert545 (by decide +kernel)

def cert546 : Leaf := ⟨⟨20,41,81,22,269,29,29,29,13⟩,[],[(5,2,1),(6,3,2),(8,5,4),(1,6,3)],⟨11,22,44,73,176,352,194,389,277⟩,⟨11,22,44,73,176,352,194,384,272⟩,[⟨7,1293929572606600618845297,⟨271,279,45,109,319,367,367,258,279⟩⟩]⟩
theorem node546 : UpperPrefix a [3,4,5,6,7,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,8,1] 30 cert546 (by decide +kernel)

def cert547 : Leaf := ⟨⟨20,33,83,22,263,151,19,23,7⟩,[],[(5,2,1),(6,3,2),(8,5,4)],⟨11,22,44,73,176,352,196,387,275⟩,⟨11,22,44,73,176,352,196,384,272⟩,[⟨3,1252691946463107015019521,⟨435,118,502,499,176,370,246,384,272⟩⟩,⟨7,1293929570354792196351025,⟨267,279,45,73,319,367,68,258,279⟩⟩]⟩
theorem node547 : UpperPrefix a [3,4,5,6,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,6,7,8,2] 30 cert547 (by decide +kernel)

theorem node548 : UpperPrefix a [3,4,5,6,7,8] 30 :=
  branch_upper a [3,4,5,6,7,8] 30 (by decide) (fin9_cases _
  node545
  node546
  node547
  (invalid_upper a [3,4,5,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,8,8] 30 (by decide +kernel)))

theorem node549 : UpperPrefix a [3,4,5,6,7] 30 :=
  branch_upper a [3,4,5,6,7] 30 (by decide) (fin9_cases _
  node539
  node543
  node544
  (invalid_upper a [3,4,5,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,7,7] 30 (by decide +kernel))
  node548)

def cert550 : Leaf := ⟨⟨404,416,467,0,134,0,278,22,134⟩,[(3,5),(5,3)],[(5,2,1),(6,3,2),(0,5,2)],⟨11,22,44,73,304,97,198,390,406⟩,⟨11,22,44,73,304,97,192,384,272⟩,[⟨3,1238497212816683615390721,⟨499,470,502,113,304,113,192,384,272⟩⟩]⟩
theorem node550 : UpperPrefix a [3,4,5,6,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,0] 30 cert550 (by decide +kernel)

def cert551 : Leaf := ⟨⟨0,41,67,2,143,141,15,15,143⟩,[],[(5,2,1),(6,3,2)],⟨11,22,44,73,304,98,197,389,405⟩,⟨11,22,44,73,304,98,192,384,272⟩,[⟨4,1210255463600074998416419,⟨111,239,45,109,493,111,192,384,460⟩⟩,⟨8,1184056015861480301745,⟨11,23,45,77,63,111,237,239,23⟩⟩,⟨7,1208926973663138582504497,⟨11,23,45,73,319,111,64,258,279⟩⟩,⟨2,1210107565283855980037153,⟨11,18,41,73,313,107,192,384,272⟩⟩]⟩
theorem node551 : UpperPrefix a [3,4,5,6,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,1] 30 cert551 (by decide +kernel)

def cert552 : Leaf := ⟨⟨404,416,466,0,134,402,278,22,134⟩,[(3,6)],[(5,2,1),(6,3,2),(0,6,3)],⟨11,22,44,73,304,100,193,386,402⟩,⟨11,22,44,73,304,100,193,384,272⟩,[⟨3,1470345169576643525626881,⟨467,438,502,449,434,502,449,384,400⟩⟩]⟩
theorem node552 : UpperPrefix a [3,4,5,6,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,2,0] 30 cert552 (by decide +kernel)

def cert553 : Leaf := ⟨⟨400,417,465,402,129,401,273,17,129⟩,[],[(5,2,1),(6,3,2),(1,6,3)],⟨11,22,44,73,304,100,194,385,401⟩,⟨11,22,44,73,304,100,194,384,272⟩,[⟨2,1371581193578750962304067,⟨459,475,440,201,440,505,459,384,272⟩⟩,⟨3,1252691964261451489627137,⟨499,118,502,465,306,118,226,384,272⟩⟩]⟩
theorem node553 : UpperPrefix a [3,4,5,6,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,2,1] 30 cert553 (by decide +kernel)

theorem node554 : UpperPrefix a [3,4,5,6,8,2] 30 :=
  branch_upper a [3,4,5,6,8,2] 30 (by decide) (fin9_cases _
  node552
  node553
  (invalid_upper a [3,4,5,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,2,8] 30 (by decide +kernel)))

def cert555 : Leaf := ⟨⟨20,41,83,22,15,0,31,31,15⟩,[(5,6)],[(5,2,1),(6,3,2),(7,5,5)],⟨11,22,44,73,304,224,199,391,279⟩,⟨11,22,44,73,304,224,192,384,272⟩,[⟨8,1184058267661296084113,⟨15,23,44,109,63,237,237,239,23⟩⟩]⟩
theorem node555 : UpperPrefix a [3,4,5,6,8,7] 30 :=
  Boolean.leaf_sound a [3,4,5,6,8,7] 30 cert555 (by decide +kernel)

theorem node556 : UpperPrefix a [3,4,5,6,8] 30 :=
  branch_upper a [3,4,5,6,8] 30 (by decide) (fin9_cases _
  node550
  node551
  node554
  (invalid_upper a [3,4,5,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,8,6] 30 (by decide +kernel))
  node555
  (invalid_upper a [3,4,5,6,8,8] 30 (by decide +kernel)))

theorem node557 : UpperPrefix a [3,4,5,6] 30 :=
  branch_upper a [3,4,5,6] 30 (by decide) (fin9_cases _
  node530
  node537
  node538
  (invalid_upper a [3,4,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,6,6] 30 (by decide +kernel))
  node549
  node556)

def cert558 : Leaf := ⟨⟨212,224,208,84,198,148,276,84,196⟩,[],[(5,2,1),(1,5,4)],⟨11,22,44,137,49,98,452,452,340⟩,⟨11,22,44,137,49,98,192,384,272⟩,[⟨0,1295285757993479547659264,⟨494,502,44,236,502,482,192,416,498⟩⟩,⟨3,1238497212746589749120001,⟨499,502,502,177,49,482,192,384,272⟩⟩,⟨8,1181747927902887930981,⟨11,23,63,137,55,127,255,128,18⟩⟩]⟩
theorem node558 : UpperPrefix a [3,4,5,7,0,1] 30 :=
  Boolean.leaf_sound a [3,4,5,7,0,1] 30 cert558 (by decide +kernel)

def cert559 : Leaf := ⟨⟨208,232,210,82,198,146,274,82,194⟩,[],[(5,2,1)],⟨11,22,44,137,49,100,450,450,338⟩,⟨11,22,44,137,49,100,192,384,272⟩,[⟨0,1297651544195208519623680,⟨494,502,44,236,502,100,192,448,498⟩⟩,⟨8,1181747927902887930981,⟨11,23,63,137,55,127,255,128,18⟩⟩,⟨2,1219580022408899618407427,⟨459,475,40,201,249,96,192,384,280⟩⟩,⟨3,1224302388962203104445441,⟨499,502,36,465,497,100,192,384,272⟩⟩]⟩
theorem node559 : UpperPrefix a [3,4,5,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,0,2] 30 cert559 (by decide +kernel)

def cert560 : Leaf := ⟨⟨148,160,146,22,134,150,276,86,198⟩,[],[(5,2,1)],⟨11,22,44,137,49,352,194,452,340⟩,⟨11,22,44,137,49,352,194,384,272⟩,[⟨0,1295290376434897416102912,⟨494,502,44,236,502,352,482,480,498⟩⟩,⟨3,1238497233012788072287233,⟨499,502,502,241,113,352,482,384,272⟩⟩,⟨6,1210106412364829578783845,⟨11,23,63,137,55,319,139,384,274⟩⟩,⟨8,1181745671705010924645,⟨11,23,63,137,55,127,203,128,18⟩⟩]⟩
theorem node560 : UpperPrefix a [3,4,5,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,7,0,8,1] 30 cert560 (by decide +kernel)

def cert561 : Leaf := ⟨⟨276,288,402,278,262,22,274,86,70⟩,[],[(5,2,1)],⟨11,22,44,137,49,352,196,450,338⟩,⟨11,22,44,137,49,352,196,384,272⟩,[⟨0,1297647085350102446121984,⟨494,502,108,236,502,480,196,416,498⟩⟩,⟨3,1243819100663654768446465,⟨499,502,502,433,433,480,486,384,272⟩⟩,⟨6,1210106412364829578816613,⟨11,23,63,137,55,319,159,384,274⟩⟩,⟨7,1662274158275092953467909,⟨11,23,319,9,305,370,375,256,272⟩⟩]⟩
theorem node561 : UpperPrefix a [3,4,5,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,0,8,2] 30 cert561 (by decide +kernel)

theorem node562 : UpperPrefix a [3,4,5,7,0,8] 30 :=
  branch_upper a [3,4,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,7,0,8,0] 30 (by decide +kernel))
  node560
  node561
  (invalid_upper a [3,4,5,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,8,8] 30 (by decide +kernel)))

theorem node563 : UpperPrefix a [3,4,5,7,0] 30 :=
  branch_upper a [3,4,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,7,0,0] 30 (by decide +kernel))
  node558
  node559
  (invalid_upper a [3,4,5,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,0,7] 30 (by decide +kernel))
  node562)

def cert564 : Leaf := ⟨⟨212,224,209,84,196,148,276,84,196⟩,[],[(5,2,1),(0,5,2)],⟨11,22,44,137,50,97,452,452,340⟩,⟨11,22,44,137,50,97,192,384,272⟩,[⟨1,1297651543561894263783425,⟨493,468,44,237,508,237,192,448,468⟩⟩,⟨3,1238497212535208638680065,⟨499,470,502,177,498,113,192,384,272⟩⟩,⟨8,1181747927902887930981,⟨11,23,63,137,55,127,255,128,18⟩⟩]⟩
theorem node564 : UpperPrefix a [3,4,5,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,0] 30 cert564 (by decide +kernel)

def cert565 : Leaf := ⟨⟨16,33,211,82,5,147,275,83,67⟩,[],[(5,2,1),(2,5,4)],⟨11,22,44,137,50,100,449,449,337⟩,⟨11,22,44,137,50,100,192,384,272⟩,[⟨3,1214913104387987364400129,⟨467,54,246,449,50,118,192,384,272⟩⟩,⟨8,1181747927902887930981,⟨11,23,63,137,55,127,255,128,18⟩⟩,⟨7,1360042701117436822834181,⟨11,23,319,9,306,375,64,256,272⟩⟩,⟨6,1210106412364820980452357,⟨11,23,63,137,50,55,128,384,272⟩⟩]⟩
theorem node565 : UpperPrefix a [3,4,5,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,2] 30 cert565 (by decide +kernel)

def cert566 : Leaf := ⟨⟨388,417,387,0,389,135,0,71,199⟩,[(3,6),(6,3)],[(5,2,1)],⟨11,22,44,137,50,352,193,452,340⟩,⟨11,22,44,137,50,352,193,384,272⟩,[⟨3,1229034068959814493408257,⟨83,438,502,193,50,352,193,384,272⟩⟩,⟨4,1212768953971793116267539,⟨79,79,236,237,239,492,237,492,493⟩⟩,⟨6,1210106412364829578783781,⟨11,23,63,137,55,319,137,384,274⟩⟩]⟩
theorem node566 : UpperPrefix a [3,4,5,7,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,8,0] 30 cert566 (by decide +kernel)

def cert567 : Leaf := ⟨⟨276,296,402,0,268,30,282,30,78⟩,[(3,7)],[(5,2,1),(0,7,3)],⟨11,22,44,137,50,352,196,385,336⟩,⟨11,22,44,137,50,352,196,385,272⟩,[⟨6,1212762743511502277504503,⟨11,31,191,137,191,447,159,395,415⟩⟩,⟨7,1662274158277291976723461,⟨11,23,319,9,306,370,375,257,272⟩⟩]⟩
theorem node567 : UpperPrefix a [3,4,5,7,1,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,8,2,0] 30 cert567 (by decide +kernel)

def cert568 : Leaf := ⟨⟨276,297,275,278,269,0,283,0,15⟩,[(5,7),(7,5)],[(5,2,1)],⟨11,22,44,137,50,352,196,448,273⟩,⟨11,22,44,137,50,352,196,448,272⟩,[⟨6,1767345657343464893902053,⟨267,279,319,137,311,319,415,395,274⟩⟩,⟨7,1581993932581453486398989,⟨287,279,319,319,306,370,375,370,272⟩⟩]⟩
theorem node568 : UpperPrefix a [3,4,5,7,1,8,2,6] 30 :=
  Boolean.leaf_sound a [3,4,5,7,1,8,2,6] 30 cert568 (by decide +kernel)

theorem node569 : UpperPrefix a [3,4,5,7,1,8,2] 30 :=
  branch_upper a [3,4,5,7,1,8,2] 30 (by decide) (fin9_cases _
  node567
  (invalid_upper a [3,4,5,7,1,8,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,2,5] 30 (by decide +kernel))
  node568
  (invalid_upper a [3,4,5,7,1,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,2,8] 30 (by decide +kernel)))

theorem node570 : UpperPrefix a [3,4,5,7,1,8] 30 :=
  branch_upper a [3,4,5,7,1,8] 30 (by decide) (fin9_cases _
  node566
  (invalid_upper a [3,4,5,7,1,8,1] 30 (by decide +kernel))
  node569
  (invalid_upper a [3,4,5,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,8,8] 30 (by decide +kernel)))

theorem node571 : UpperPrefix a [3,4,5,7,1] 30 :=
  branch_upper a [3,4,5,7,1] 30 (by decide) (fin9_cases _
  node564
  (invalid_upper a [3,4,5,7,1,1] 30 (by decide +kernel))
  node565
  (invalid_upper a [3,4,5,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,1,7] 30 (by decide +kernel))
  node570)

def cert572 : Leaf := ⟨⟨464,0,467,338,0,402,274,82,194⟩,[(1,4),(4,2)],[(5,2,1),(5,2,4),(2,4,1),(0,5,2)],⟨11,22,44,137,52,97,450,450,338⟩,⟨11,22,44,137,52,97,192,384,272⟩,[⟨3,1316577975039383661718529,⟨483,470,502,225,502,225,192,448,466⟩⟩]⟩
theorem node572 : UpperPrefix a [3,4,5,7,2,0] 30 :=
  Boolean.leaf_sound a [3,4,5,7,2,0] 30 cert572 (by decide +kernel)

def cert573 : Leaf := ⟨⟨464,0,467,338,0,401,275,83,195⟩,[(1,4),(4,2)],[(5,2,1),(5,2,4),(2,4,1)],⟨11,22,44,137,52,98,449,449,337⟩,⟨11,22,44,137,52,98,192,384,272⟩,[⟨3,1214913104420972713225217,⟨499,54,246,481,54,114,192,384,274⟩⟩]⟩
theorem node573 : UpperPrefix a [3,4,5,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,5,7,2,1] 30 cert573 (by decide +kernel)

def cert574 : Local := ⟨⟨464,0,467,0,0,155,0,91,203⟩,[(1,4),(3,6),(4,2),(6,3)],[(5,2,1),(5,2,4),(2,4,1)]⟩
theorem node574 : UpperPrefix a [3,4,5,7,2,8,0] 30 :=
  local_sound a [3,4,5,7,2,8,0] 30 cert574 (by decide +kernel)

def cert575 : Leaf := ⟨⟨448,0,451,322,0,155,281,75,203⟩,[(1,4),(4,2)],[(5,2,1),(5,2,4),(2,4,1)],⟨11,22,44,137,52,352,194,449,337⟩,⟨11,22,44,137,52,352,194,384,272⟩,[⟨4,1210402713187944424801345,⟨11,6,172,137,172,493,203,384,260⟩⟩]⟩
theorem node575 : UpperPrefix a [3,4,5,7,2,8,1] 30 :=
  Boolean.leaf_sound a [3,4,5,7,2,8,1] 30 cert575 (by decide +kernel)

#print axioms node575
end Delivery.FiniteExclusion.Sharp4x5
