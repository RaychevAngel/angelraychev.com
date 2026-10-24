import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C013
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
theorem node896 : UpperPrefix a [5,7,0,1,6,8] 30 :=
  branch_upper a [5,7,0,1,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,6,8,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,1] 30 (by decide +kernel))
  node891
  node892
  node895
  (invalid_upper a [5,7,0,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,8] 30 (by decide +kernel)))

theorem node897 : UpperPrefix a [5,7,0,1,6] 30 :=
  branch_upper a [5,7,0,1,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,6,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,1] 30 (by decide +kernel))
  node883
  node889
  node890
  (invalid_upper a [5,7,0,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,7] 30 (by decide +kernel))
  node896)

def cert898 : Leaf := ⟨⟨196,100,98,356,96,136,308,116,84⟩,[],[(1,3,2),(3,6,5)],⟨35,131,13,26,276,100,200,464,368⟩,⟨35,131,13,26,276,100,200,384,288⟩,[⟨0,1498734817355287304864768,⟨506,458,508,506,500,500,456,384,432⟩⟩,⟨4,1210107567534552004985953,⟨35,131,13,10,260,103,239,384,289⟩⟩,⟨7,1360042701117231067825153,⟨319,31,29,30,276,372,72,256,304⟩⟩,⟨8,1181747921022341907553,⟨35,131,13,26,20,103,239,128,33⟩⟩]⟩
theorem node898 : UpperPrefix a [5,7,0,1,8,2,3] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,2,3] 30 cert898 (by decide +kernel)

def cert899 : Leaf := ⟨⟨152,56,178,160,168,152,296,48,216⟩,[],[(1,3,2),(8,4,6)],⟨35,131,13,26,276,100,208,392,352⟩,⟨35,131,13,26,276,100,208,392,288⟩,[⟨0,1800542825807580715025408,⟨506,458,508,506,500,500,496,456,368⟩⟩,⟨2,1361666446939024326354721,⟨419,131,75,218,475,491,218,459,419⟩⟩,⟨6,1212615169582822508668161,⟨47,159,13,158,415,44,158,415,447⟩⟩]⟩
theorem node899 : UpperPrefix a [5,7,0,1,8,2,4,3] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,2,4,3] 30 cert899 (by decide +kernel)

def cert900 : Leaf := ⟨⟨208,112,242,224,232,144,288,48,216⟩,[],[(1,3,2),(8,4,6)],⟨35,131,13,26,276,100,208,448,296⟩,⟨35,131,13,26,276,100,208,448,288⟩,[⟨0,1274446296511402730324992,⟨506,458,508,506,500,500,240,448,496⟩⟩,⟨2,1361666446939024326354721,⟨419,131,75,218,475,491,218,459,419⟩⟩,⟨3,1210255572285691958244477,⟨35,131,103,243,503,103,243,451,289⟩⟩]⟩
theorem node900 : UpperPrefix a [5,7,0,1,8,2,4,6] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,2,4,6] 30 cert900 (by decide +kernel)

theorem node901 : UpperPrefix a [5,7,0,1,8,2,4] 30 :=
  branch_upper a [5,7,0,1,8,2,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,2,4,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,4,1] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,4,2] 30 (by decide +kernel))
  node899
  (invalid_upper a [5,7,0,1,8,2,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,4,5] 30 (by decide +kernel))
  node900
  (invalid_upper a [5,7,0,1,8,2,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,4,8] 30 (by decide +kernel)))

theorem node902 : UpperPrefix a [5,7,0,1,8,2] 30 :=
  branch_upper a [5,7,0,1,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,2,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,1] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,2] 30 (by decide +kernel))
  node898
  node901
  (invalid_upper a [5,7,0,1,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,2,8] 30 (by decide +kernel)))

def cert903 : Leaf := ⟨⟨156,60,178,165,168,148,56,0,220⟩,[(7,4)],[(1,3,2),(8,4,7)],⟨35,131,13,26,276,104,196,400,352⟩,⟨35,131,13,26,276,104,196,400,288⟩,[⟨6,1212615169582822508668161,⟨47,159,13,158,415,40,158,415,447⟩⟩,⟨0,1796825068007113263940608,⟨418,130,508,506,500,504,500,464,416⟩⟩]⟩
theorem node903 : UpperPrefix a [5,7,0,1,8,3,2,4] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,3,2,4] 30 cert903 (by decide +kernel)

def cert904 : Leaf := ⟨⟨460,364,290,293,40,388,288,36,28⟩,[],[(1,3,2)],⟨35,131,13,26,276,104,196,448,304⟩,⟨35,131,13,26,276,104,196,448,288⟩,[⟨4,1212621366930571804259709,⟨39,131,111,239,487,111,231,451,487⟩⟩,⟨0,1796825068007113263940608,⟨418,130,508,506,500,504,500,464,416⟩⟩,⟨6,1214828778845698164261889,⟨319,415,285,30,276,40,148,384,288⟩⟩,⟨7,1213649340146485359805441,⟨319,287,285,30,276,104,84,320,288⟩⟩,⟨3,1210255427466816440501249,⟨35,131,5,210,468,96,196,448,288⟩⟩]⟩
theorem node904 : UpperPrefix a [5,7,0,1,8,3,2,6] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,3,2,6] 30 cert904 (by decide +kernel)

theorem node905 : UpperPrefix a [5,7,0,1,8,3,2] 30 :=
  branch_upper a [5,7,0,1,8,3,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,3,2,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,2,1] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,2,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,2,3] 30 (by decide +kernel))
  node903
  (invalid_upper a [5,7,0,1,8,3,2,5] 30 (by decide +kernel))
  node904
  (invalid_upper a [5,7,0,1,8,3,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,2,8] 30 (by decide +kernel)))

def cert906 : Leaf := ⟨⟨200,104,226,225,232,144,292,100,204⟩,[],[(1,3,2),(8,4,6),(4,6,5)],⟨35,131,13,26,276,104,208,452,356⟩,⟨35,131,13,26,276,104,208,384,288⟩,[⟨0,1304739867207627294376960,⟨34,130,508,506,500,104,464,384,288⟩⟩,⟨2,1210107567535660088722529,⟨35,131,9,26,272,107,251,384,289⟩⟩,⟨3,1210255571582004516357121,⟨35,131,69,210,468,96,208,384,288⟩⟩]⟩
theorem node906 : UpperPrefix a [5,7,0,1,8,3,4] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,3,4] 30 cert906 (by decide +kernel)

theorem node907 : UpperPrefix a [5,7,0,1,8,3] 30 :=
  branch_upper a [5,7,0,1,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,3,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,1] 30 (by decide +kernel))
  node905
  (invalid_upper a [5,7,0,1,8,3,3] 30 (by decide +kernel))
  node906
  (invalid_upper a [5,7,0,1,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,3,8] 30 (by decide +kernel)))

def cert908 : Leaf := ⟨⟨144,48,178,161,161,133,57,49,209⟩,[],[(1,3,2),(2,6,5),(3,7,6)],⟨35,131,13,26,276,112,196,392,352⟩,⟨35,131,13,26,276,112,196,392,288⟩,[⟨6,1212615169582826812040481,⟨47,159,13,158,415,191,158,415,447⟩⟩,⟨8,1184087822508127257769,⟨111,199,45,127,20,127,199,239,45⟩⟩]⟩
theorem node908 : UpperPrefix a [5,7,0,1,8,4,2,3] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,4,2,3] 30 cert908 (by decide +kernel)

def cert909 : Leaf := ⟨⟨464,368,370,353,104,260,304,48,88⟩,[],[(1,3,2),(2,6,5)],⟨35,131,13,26,276,112,196,448,296⟩,⟨35,131,13,26,276,112,196,448,288⟩,[⟨0,1267624881338883041657856,⟨34,162,508,506,500,240,500,496,288⟩⟩,⟨3,1210255428311241370760509,⟨35,131,39,243,503,243,199,451,291⟩⟩,⟨7,1213649342398285173490689,⟨319,287,285,30,276,112,116,352,288⟩⟩]⟩
theorem node909 : UpperPrefix a [5,7,0,1,8,4,2,6] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,4,2,6] 30 cert909 (by decide +kernel)

theorem node910 : UpperPrefix a [5,7,0,1,8,4,2] 30 :=
  branch_upper a [5,7,0,1,8,4,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,4,2,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,2,1] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,2,2] 30 (by decide +kernel))
  node908
  (invalid_upper a [5,7,0,1,8,4,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,2,5] 30 (by decide +kernel))
  node909
  (invalid_upper a [5,7,0,1,8,4,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,2,8] 30 (by decide +kernel)))

def cert911 : Leaf := ⟨⟨452,356,498,484,0,388,292,0,196⟩,[(4,7),(7,4)],[(1,3,2)],⟨35,131,13,26,276,112,200,388,352⟩,⟨35,131,13,26,276,112,200,388,288⟩,[⟨0,2414495745877929286960128,⟨362,506,508,506,500,496,504,500,288⟩⟩,⟨3,1663602323852522136135009,⟨291,147,5,146,407,499,499,407,291⟩⟩,⟨4,1361371010802358573688097,⟨291,131,77,202,391,483,202,391,291⟩⟩]⟩
theorem node911 : UpperPrefix a [5,7,0,1,8,4,3,2] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,4,3,2] 30 cert911 (by decide +kernel)

def cert912 : Leaf := ⟨⟨344,376,306,289,40,264,304,56,28⟩,[],[(1,3,2)],⟨35,131,13,26,276,112,200,448,292⟩,⟨35,131,13,26,276,112,200,448,288⟩,[⟨2,1212621943814642515309949,⟨107,131,107,251,507,251,235,451,491⟩⟩,⟨7,1525325534776229189387267,⟨319,319,285,287,276,368,380,368,288⟩⟩,⟨0,1305108514421675287118848,⟨162,130,508,506,500,496,232,448,416⟩⟩,⟨6,1214828778845698164261889,⟨319,415,285,30,276,48,136,384,288⟩⟩]⟩
theorem node912 : UpperPrefix a [5,7,0,1,8,4,3,6] 30 :=
  Boolean.leaf_sound a [5,7,0,1,8,4,3,6] 30 cert912 (by decide +kernel)

theorem node913 : UpperPrefix a [5,7,0,1,8,4,3] 30 :=
  branch_upper a [5,7,0,1,8,4,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,4,3,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,3,1] 30 (by decide +kernel))
  node911
  (invalid_upper a [5,7,0,1,8,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,3,5] 30 (by decide +kernel))
  node912
  (invalid_upper a [5,7,0,1,8,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,3,8] 30 (by decide +kernel)))

theorem node914 : UpperPrefix a [5,7,0,1,8,4] 30 :=
  branch_upper a [5,7,0,1,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,4,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,1] 30 (by decide +kernel))
  node910
  node913
  (invalid_upper a [5,7,0,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,4,8] 30 (by decide +kernel)))

theorem node915 : UpperPrefix a [5,7,0,1,8] 30 :=
  branch_upper a [5,7,0,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,1] 30 (by decide +kernel))
  node902
  node907
  node914
  (invalid_upper a [5,7,0,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,8,8] 30 (by decide +kernel)))

theorem node916 : UpperPrefix a [5,7,0,1] 30 :=
  branch_upper a [5,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,2] 30 (by decide +kernel))
  node882
  (invalid_upper a [5,7,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,5] 30 (by decide +kernel))
  node897
  (invalid_upper a [5,7,0,1,7] 30 (by decide +kernel))
  node915)

def cert917 : Leaf := ⟨⟨464,368,272,0,0,403,307,115,211⟩,[(3,4),(4,2)],[(2,3,3),(2,3,4),(3,4,3),(3,4,4)],⟨35,131,13,28,28,370,466,466,370⟩,⟨35,131,13,28,28,96,192,384,288⟩,[⟨1,1210107565284885566062593,⟨61,157,29,28,28,96,192,384,288⟩⟩,⟨5,1210107564158985659220993,⟨31,159,29,28,28,64,192,384,256⟩⟩,⟨6,1210106412363380959216641,⟨63,159,29,28,28,32,128,384,288⟩⟩,⟨7,1208926973664168154760193,⟨63,31,29,28,28,96,64,256,288⟩⟩]⟩
theorem node917 : UpperPrefix a [5,7,0,2,3] 30 :=
  Boolean.leaf_sound a [5,7,0,2,3] 30 cert917 (by decide +kernel)

def cert918 : Leaf := ⟨⟨0,376,336,0,265,409,281,89,89⟩,[(0,5),(3,4)],[(7,1,5),(2,3,3),(1,5,0)],⟨35,131,13,28,84,98,472,408,312⟩,⟨35,131,13,28,84,98,192,384,288⟩,[⟨5,1212473359087610629981185,⟨31,143,13,28,92,94,192,448,472⟩⟩]⟩
theorem node918 : UpperPrefix a [5,7,0,2,6,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,1] 30 cert918 (by decide +kernel)

def cert919 : Leaf := ⟨⟨88,120,114,0,43,19,0,123,91⟩,[(3,4),(6,1)],[(7,1,6),(2,3,3)],⟨35,131,13,28,84,104,194,400,304⟩,⟨35,131,13,28,84,104,194,384,288⟩,[⟨8,1184094980598220555507,⟨127,255,61,61,127,127,255,255,61⟩⟩]⟩
theorem node919 : UpperPrefix a [5,7,0,2,6,3,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,3,1] 30 cert919 (by decide +kernel)

def cert920 : Leaf := ⟨⟨192,96,226,0,163,147,35,99,195⟩,[(3,4)],[(2,3,3),(4,6,5)],⟨35,131,13,28,84,104,208,386,290⟩,⟨35,131,13,28,84,104,208,384,288⟩,[⟨3,1368667634834156266147617,⟨483,387,471,214,214,499,210,387,483⟩⟩,⟨8,1184094980598220555507,⟨127,255,61,61,127,127,255,255,61⟩⟩]⟩
theorem node920 : UpperPrefix a [5,7,0,2,6,3,4] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,3,4] 30 cert920 (by decide +kernel)

def cert921 : Leaf := ⟨⟨216,120,208,0,137,145,0,123,219⟩,[(3,4),(6,7)],[(2,3,3),(8,6,6)],⟨35,131,13,28,84,104,448,402,306⟩,⟨35,131,13,28,84,104,448,384,288⟩,[⟨1,1210109871760319587287041,⟨61,253,13,60,124,104,448,448,288⟩⟩,⟨5,1210109870001100982846465,⟨31,223,13,28,92,72,448,448,256⟩⟩]⟩
theorem node921 : UpperPrefix a [5,7,0,2,6,3,8] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,3,8] 30 cert921 (by decide +kernel)

theorem node922 : UpperPrefix a [5,7,0,2,6,3] 30 :=
  branch_upper a [5,7,0,2,6,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,6,3,0] 30 (by decide +kernel))
  node919
  (invalid_upper a [5,7,0,2,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,3,3] 30 (by decide +kernel))
  node920
  (invalid_upper a [5,7,0,2,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,3,7] 30 (by decide +kernel))
  node921)

def cert923 : Local := ⟨⟨280,312,306,0,299,0,0,59,27⟩,[(3,4),(5,4),(6,1)],[(7,1,6),(2,3,3),(6,4,5)]⟩
theorem node923 : UpperPrefix a [5,7,0,2,6,4,1] 30 :=
  local_sound a [5,7,0,2,6,4,1] 30 cert923 (by decide +kernel)

def cert924 : Local := ⟨⟨400,304,434,0,427,0,307,51,147⟩,[(3,4),(5,4)],[(2,3,3),(6,4,5),(3,6,4)]⟩
theorem node924 : UpperPrefix a [5,7,0,2,6,4,3] 30 :=
  local_sound a [5,7,0,2,6,4,3] 30 cert924 (by decide +kernel)

def cert925 : Local := ⟨⟨152,56,178,0,171,0,0,59,155⟩,[(3,4),(5,4),(6,7)],[(2,3,3),(6,4,5),(8,6,6)]⟩
theorem node925 : UpperPrefix a [5,7,0,2,6,4,8] 30 :=
  local_sound a [5,7,0,2,6,4,8] 30 cert925 (by decide +kernel)

theorem node926 : UpperPrefix a [5,7,0,2,6,4] 30 :=
  branch_upper a [5,7,0,2,6,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,6,4,0] 30 (by decide +kernel))
  node923
  (invalid_upper a [5,7,0,2,6,4,2] 30 (by decide +kernel))
  node924
  (invalid_upper a [5,7,0,2,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,4,7] 30 (by decide +kernel))
  node925)

def cert927 : Leaf := ⟨⟨344,344,338,0,267,27,0,91,91⟩,[(3,4),(6,1)],[(7,1,6),(2,3,3)],⟨35,131,13,28,84,352,194,408,312⟩,⟨35,131,13,28,84,352,194,384,288⟩,[⟨5,1210402766111217421125121,⟨223,223,95,28,92,472,222,384,384⟩⟩]⟩
theorem node927 : UpperPrefix a [5,7,0,2,6,8,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,8,1] 30 cert927 (by decide +kernel)

def cert928 : Leaf := ⟨⟨464,368,208,0,137,147,17,115,211⟩,[(3,4)],[(2,3,3),(3,6,4)],⟨35,131,13,28,84,352,200,402,306⟩,⟨35,131,13,28,84,352,200,384,288⟩,[⟨1,1210107601312857951305729,⟨125,221,29,28,92,352,200,384,288⟩⟩,⟨5,1210107600186958044464129,⟨95,223,29,28,92,320,200,384,256⟩⟩,⟨8,1181781698228776600577,⟨127,223,29,28,92,96,200,128,32⟩⟩]⟩
theorem node928 : UpperPrefix a [5,7,0,2,6,8,3] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,8,3] 30 cert928 (by decide +kernel)

def cert929 : Leaf := ⟨⟨448,352,464,0,393,153,265,97,217⟩,[(3,4)],[(2,3,3),(1,7,1)],⟨35,131,13,28,84,352,208,386,296⟩,⟨35,131,13,28,84,352,208,386,288⟩,[⟨3,1212763896430464788023073,⟨163,131,7,20,84,483,210,387,419⟩⟩,⟨4,1212763896429366350137121,⟨163,131,15,12,68,483,194,387,419⟩⟩,⟨5,1210109906038780531049473,⟨95,223,29,28,92,320,216,478,256⟩⟩]⟩
theorem node929 : UpperPrefix a [5,7,0,2,6,8,4,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,8,4,1] 30 cert929 (by decide +kernel)

def cert930 : Leaf := ⟨⟨392,296,418,0,426,138,298,34,138⟩,[(3,4)],[(2,3,3)],⟨35,131,13,28,84,352,208,392,290⟩,⟨35,131,13,28,84,352,208,392,288⟩,[⟨4,1781624592989171305528441,⟨291,391,399,431,487,355,487,399,289⟩⟩,⟨0,1224314373182308698031104,⟨290,482,508,252,252,352,248,504,288⟩⟩,⟨6,1366276547690382922829601,⟨423,391,399,158,158,431,158,399,423⟩⟩]⟩
theorem node930 : UpperPrefix a [5,7,0,2,6,8,4,3] 30 :=
  Boolean.leaf_sound a [5,7,0,2,6,8,4,3] 30 cert930 (by decide +kernel)

theorem node931 : UpperPrefix a [5,7,0,2,6,8,4] 30 :=
  branch_upper a [5,7,0,2,6,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,6,8,4,0] 30 (by decide +kernel))
  node929
  (invalid_upper a [5,7,0,2,6,8,4,2] 30 (by decide +kernel))
  node930
  (invalid_upper a [5,7,0,2,6,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,8,4,8] 30 (by decide +kernel)))

theorem node932 : UpperPrefix a [5,7,0,2,6,8] 30 :=
  branch_upper a [5,7,0,2,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,6,8,0] 30 (by decide +kernel))
  node927
  (invalid_upper a [5,7,0,2,6,8,2] 30 (by decide +kernel))
  node928
  node931
  (invalid_upper a [5,7,0,2,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,8,8] 30 (by decide +kernel)))

theorem node933 : UpperPrefix a [5,7,0,2,6] 30 :=
  branch_upper a [5,7,0,2,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,6,0] 30 (by decide +kernel))
  node918
  (invalid_upper a [5,7,0,2,6,2] 30 (by decide +kernel))
  node922
  node926
  (invalid_upper a [5,7,0,2,6,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,6,7] 30 (by decide +kernel))
  node932)

def cert934 : Leaf := ⟨⟨0,376,368,0,105,409,312,120,89⟩,[(0,5),(3,4)],[(7,1,5),(2,3,3),(1,5,0)],⟨35,131,13,28,276,98,216,472,376⟩,⟨35,131,13,28,276,98,192,384,288⟩,[⟨0,1210255571582007737582592,⟨34,130,76,220,476,98,192,384,288⟩⟩]⟩
theorem node934 : UpperPrefix a [5,7,0,2,8,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,8,1] 30 cert934 (by decide +kernel)

def cert935 : Leaf := ⟨⟨344,376,368,0,105,273,0,121,89⟩,[(3,4),(6,1)],[(7,1,6),(2,3,3)],⟨35,131,13,28,276,104,194,464,368⟩,⟨35,131,13,28,276,104,194,384,288⟩,[⟨1,1664340193611153942511617,⟨445,157,29,28,284,504,508,384,416⟩⟩]⟩
theorem node935 : UpperPrefix a [5,7,0,2,8,3,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,8,3,1] 30 cert935 (by decide +kernel)

def cert936 : Leaf := ⟨⟨192,96,226,0,235,147,291,99,195⟩,[(3,4)],[(2,3,3),(8,4,6),(4,6,5)],⟨35,131,13,28,276,104,208,450,354⟩,⟨35,131,13,28,276,104,208,384,288⟩,[⟨3,1361666446939012516243233,⟨419,131,71,214,471,483,210,387,419⟩⟩]⟩
theorem node936 : UpperPrefix a [5,7,0,2,8,3,4] 30 :=
  Boolean.leaf_sound a [5,7,0,2,8,3,4] 30 cert936 (by decide +kernel)

theorem node937 : UpperPrefix a [5,7,0,2,8,3] 30 :=
  branch_upper a [5,7,0,2,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,8,3,0] 30 (by decide +kernel))
  node935
  (invalid_upper a [5,7,0,2,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,3,3] 30 (by decide +kernel))
  node936
  (invalid_upper a [5,7,0,2,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,3,8] 30 (by decide +kernel)))

def cert938 : Leaf := ⟨⟨344,376,368,0,105,265,0,121,89⟩,[(3,4),(6,1)],[(7,1,6),(2,3,3)],⟨35,131,13,28,276,112,194,456,360⟩,⟨35,131,13,28,276,112,194,384,288⟩,[⟨1,1664340193611153942511617,⟨445,157,29,28,284,504,508,384,416⟩⟩]⟩
theorem node938 : UpperPrefix a [5,7,0,2,8,4,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,8,4,1] 30 cert938 (by decide +kernel)

def cert939 : Leaf := ⟨⟨456,360,496,0,232,392,288,104,200⟩,[(3,4)],[(2,3,3),(1,7,1)],⟨35,131,13,28,276,112,200,386,352⟩,⟨35,131,13,28,276,112,200,386,288⟩,[⟨0,1795690307827108135568384,⟨418,130,508,380,380,376,504,386,288⟩⟩,⟨4,1364036637378603641958177,⟨419,131,207,206,455,483,202,387,419⟩⟩]⟩
theorem node939 : UpperPrefix a [5,7,0,2,8,4,3,1] 30 :=
  Boolean.leaf_sound a [5,7,0,2,8,4,3,1] 30 cert939 (by decide +kernel)

def cert940 : Leaf := ⟨⟨448,352,498,0,226,394,290,34,194⟩,[(3,4)],[(2,3,3)],⟨35,131,13,28,276,112,200,448,290⟩,⟨35,131,13,28,276,112,200,448,288⟩,[⟨0,1217385887670280653898752,⟨482,386,508,252,508,248,232,448,480⟩⟩,⟨3,1366240807124003135375137,⟨419,387,279,20,279,499,194,451,419⟩⟩,⟨4,1366425490736149028892449,⟨419,387,463,206,455,483,202,451,419⟩⟩]⟩
theorem node940 : UpperPrefix a [5,7,0,2,8,4,3,6] 30 :=
  Boolean.leaf_sound a [5,7,0,2,8,4,3,6] 30 cert940 (by decide +kernel)

theorem node941 : UpperPrefix a [5,7,0,2,8,4,3] 30 :=
  branch_upper a [5,7,0,2,8,4,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,8,4,3,0] 30 (by decide +kernel))
  node939
  (invalid_upper a [5,7,0,2,8,4,3,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,3,5] 30 (by decide +kernel))
  node940
  (invalid_upper a [5,7,0,2,8,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,3,8] 30 (by decide +kernel)))

theorem node942 : UpperPrefix a [5,7,0,2,8,4] 30 :=
  branch_upper a [5,7,0,2,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,8,4,0] 30 (by decide +kernel))
  node938
  (invalid_upper a [5,7,0,2,8,4,2] 30 (by decide +kernel))
  node941
  (invalid_upper a [5,7,0,2,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,4,8] 30 (by decide +kernel)))

theorem node943 : UpperPrefix a [5,7,0,2,8] 30 :=
  branch_upper a [5,7,0,2,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,8,0] 30 (by decide +kernel))
  node934
  (invalid_upper a [5,7,0,2,8,2] 30 (by decide +kernel))
  node937
  node942
  (invalid_upper a [5,7,0,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,8,8] 30 (by decide +kernel)))

theorem node944 : UpperPrefix a [5,7,0,2] 30 :=
  branch_upper a [5,7,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,2,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut18 [5,7,0,2,1] [5,7,0,1,3] 30 (by decide +kernel) node882)
  (invalid_upper a [5,7,0,2,2] 30 (by decide +kernel))
  node917
  (invalid_upper a [5,7,0,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,2,5] 30 (by decide +kernel))
  node933
  (invalid_upper a [5,7,0,2,7] 30 (by decide +kernel))
  node943)

def cert945 : Leaf := ⟨⟨0,116,112,37,0,149,309,117,85⟩,[(0,5),(4,2)],[(7,1,5),(3,4,4),(1,5,0)],⟨35,131,13,88,28,98,468,404,308⟩,⟨35,131,13,88,28,98,192,384,288⟩,[⟨8,1181748227592894579817,⟨63,151,61,127,61,127,255,148,61⟩⟩]⟩
theorem node945 : UpperPrefix a [5,7,0,6,3,1] 30 :=
  Boolean.leaf_sound a [5,7,0,6,3,1] 30 cert945 (by decide +kernel)

def cert946 : Leaf := ⟨⟨148,52,114,38,0,146,310,54,22⟩,[(4,2)],[(3,4,4)],⟨35,131,13,88,28,100,466,402,306⟩,⟨35,131,13,88,28,100,192,384,288⟩,[⟨0,1214839173296373051163648,⟨506,458,508,88,60,124,192,384,312⟩⟩,⟨8,1181748227592894579817,⟨63,151,61,127,61,127,255,148,61⟩⟩,⟨6,1361517287719629957056289,⟨419,131,31,24,28,439,130,387,419⟩⟩,⟨7,1213649340148550835897345,⟨319,279,285,88,28,124,64,256,312⟩⟩]⟩
theorem node946 : UpperPrefix a [5,7,0,6,3,2] 30 :=
  Boolean.leaf_sound a [5,7,0,6,3,2] 30 cert946 (by decide +kernel)

def cert947 : Leaf := ⟨⟨212,116,114,0,0,0,311,119,87⟩,[(3,5),(4,2),(5,3)],[(3,4,4)],⟨35,131,13,88,28,112,454,390,294⟩,⟨35,131,13,88,28,112,192,384,288⟩,[⟨8,1181748227592894579817,⟨63,151,61,127,61,127,255,148,61⟩⟩,⟨7,1213649340427826789352449,⟨319,279,317,120,60,120,64,256,296⟩⟩]⟩
theorem node947 : UpperPrefix a [5,7,0,6,3,4] 30 :=
  Boolean.leaf_sound a [5,7,0,6,3,4] 30 cert947 (by decide +kernel)

def cert948 : Leaf := ⟨⟨324,356,354,295,0,7,0,119,87⟩,[(4,2),(6,1)],[(7,1,6),(3,4,4)],⟨35,131,13,88,28,352,194,404,308⟩,⟨35,131,13,88,28,352,194,384,288⟩,[⟨4,1210109911658158036714723,⟨99,227,13,79,12,355,227,483,289⟩⟩]⟩
theorem node948 : UpperPrefix a [5,7,0,6,3,8,1] 30 :=
  Boolean.leaf_sound a [5,7,0,6,3,8,1] 30 cert948 (by decide +kernel)

def cert949 : Leaf := ⟨⟨464,368,336,261,0,147,273,115,83⟩,[(4,2)],[(3,4,4),(2,6,3)],⟨35,131,13,88,28,352,196,402,306⟩,⟨35,131,13,88,28,352,196,384,288⟩,[⟨1,1210107601317541076271105,⟨125,221,29,88,28,376,220,384,296⟩⟩,⟨5,1210107600191641169429505,⟨95,223,29,88,28,344,220,384,264⟩⟩,⟨7,1213649340150758449087489,⟨319,279,285,88,28,376,92,256,296⟩⟩]⟩
theorem node949 : UpperPrefix a [5,7,0,6,3,8,2] 30 :=
  Boolean.leaf_sound a [5,7,0,6,3,8,2] 30 cert949 (by decide +kernel)

def cert950 : Leaf := ⟨⟨452,356,480,0,0,135,293,103,199⟩,[(3,6),(4,2)],[(3,4,4),(4,6,3)],⟨35,131,13,88,28,352,208,390,294⟩,⟨35,131,13,88,28,352,208,384,288⟩,[⟨1,1210107601313138734792705,⟨125,221,29,88,28,360,216,384,288⟩⟩]⟩
theorem node950 : UpperPrefix a [5,7,0,6,3,8,4] 30 :=
  Boolean.leaf_sound a [5,7,0,6,3,8,4] 30 cert950 (by decide +kernel)

theorem node951 : UpperPrefix a [5,7,0,6,3,8] 30 :=
  branch_upper a [5,7,0,6,3,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,3,8,0] 30 (by decide +kernel))
  node948
  node949
  (invalid_upper a [5,7,0,6,3,8,3] 30 (by decide +kernel))
  node950
  (invalid_upper a [5,7,0,6,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,3,8,8] 30 (by decide +kernel)))

theorem node952 : UpperPrefix a [5,7,0,6,3] 30 :=
  branch_upper a [5,7,0,6,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,3,0] 30 (by decide +kernel))
  node945
  node946
  (invalid_upper a [5,7,0,6,3,3] 30 (by decide +kernel))
  node947
  (invalid_upper a [5,7,0,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,3,7] 30 (by decide +kernel))
  node951)

def cert953 : Leaf := ⟨⟨0,108,96,260,105,141,284,92,93⟩,[(0,5)],[(7,1,5),(1,5,0)],⟨35,131,13,88,276,98,220,412,316⟩,⟨35,131,13,88,276,98,192,384,288⟩,[⟨0,1210255427466819661726720,⟨34,130,12,216,476,98,192,384,288⟩⟩,⟨4,1210107567816026967016553,⟨35,131,45,111,260,99,227,384,289⟩⟩,⟨5,1210255426340919754884097,⟨3,131,13,216,476,66,192,384,256⟩⟩,⟨8,1181748202497303938153,⟨35,131,45,127,20,99,227,128,33⟩⟩]⟩
theorem node953 : UpperPrefix a [5,7,0,6,8,1] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,1] 30 cert953 (by decide +kernel)

def cert954 : Leaf := ⟨⟨284,316,304,292,40,282,0,52,28⟩,[(6,1)],[(7,1,6)],⟨35,131,13,88,276,100,194,392,304⟩,⟨35,131,13,88,276,100,194,392,288⟩,[⟨6,1365981399796600257211681,⟨307,407,415,26,407,439,150,415,307⟩⟩,⟨0,1463335298742111439946752,⟨506,458,508,472,444,508,194,392,440⟩⟩,⟨1,1368648107228041372237825,⟨445,405,413,88,404,508,216,392,440⟩⟩]⟩
theorem node954 : UpperPrefix a [5,7,0,6,8,2,1,3] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,2,1,3] 30 cert954 (by decide +kernel)

def cert955 : Leaf := ⟨⟨92,124,114,38,106,26,0,0,94⟩,[(6,1),(7,4)],[(7,1,6),(8,4,7)],⟨35,131,13,88,276,100,194,400,296⟩,⟨35,131,13,88,276,100,194,400,288⟩,[⟨0,1463316851998037730395136,⟨506,458,508,472,444,508,194,400,440⟩⟩]⟩
theorem node955 : UpperPrefix a [5,7,0,6,8,2,1,4] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,2,1,4] 30 cert955 (by decide +kernel)

theorem node956 : UpperPrefix a [5,7,0,6,8,2,1] 30 :=
  branch_upper a [5,7,0,6,8,2,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,8,2,1,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,1,2] 30 (by decide +kernel))
  node954
  node955
  (invalid_upper a [5,7,0,6,8,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,1,8] 30 (by decide +kernel)))

def cert957 : Leaf := ⟨⟨448,352,480,416,224,392,288,96,212⟩,[],[(3,6,5),(1,7,1)],⟨35,131,13,88,276,100,200,386,304⟩,⟨35,131,13,88,276,100,200,386,288⟩,[⟨0,1498199717661968631333888,⟨506,458,508,376,380,380,456,450,312⟩⟩,⟨4,1212616469265977047233917,⟨35,131,111,239,423,103,239,387,419⟩⟩,⟨2,1212616754823442559345921,⟨35,131,73,218,475,96,202,387,419⟩⟩]⟩
theorem node957 : UpperPrefix a [5,7,0,6,8,2,3,1] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,2,3,1] 30 cert957 (by decide +kernel)

def cert958 : Leaf := ⟨⟨196,100,226,166,226,138,54,0,198⟩,[(7,4)],[(8,4,7),(3,6,5),(4,7,6)],⟨35,131,13,88,276,100,200,400,290⟩,⟨35,131,13,88,276,100,200,400,288⟩,[⟨0,1215017822647161707299840,⟨362,458,508,248,508,252,200,504,360⟩⟩]⟩
theorem node958 : UpperPrefix a [5,7,0,6,8,2,3,4] 30 :=
  Boolean.leaf_sound a [5,7,0,6,8,2,3,4] 30 cert958 (by decide +kernel)

theorem node959 : UpperPrefix a [5,7,0,6,8,2,3] 30 :=
  branch_upper a [5,7,0,6,8,2,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,6,8,2,3,0] 30 (by decide +kernel))
  node957
  (invalid_upper a [5,7,0,6,8,2,3,2] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,3,3] 30 (by decide +kernel))
  node958
  (invalid_upper a [5,7,0,6,8,2,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,6,8,2,3,8] 30 (by decide +kernel)))

#print axioms node959
end Delivery.FiniteExclusion.Sharp2x3x4
