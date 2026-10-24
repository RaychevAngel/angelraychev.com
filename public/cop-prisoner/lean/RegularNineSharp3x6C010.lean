import RegularNineSharp3x6Base
import RegularNineSharp3x6C009
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert640 : Leaf := ⟨⟨148,137,10,0,142,142,268,78,198⟩,[(3,4)],[(4,1,0),(5,3,3),(0,4,1)],⟨11,22,133,56,49,352,194,452,332⟩,⟨11,22,133,56,49,352,194,384,264⟩,[⟨6,1210106412365102317585467,⟨27,31,133,59,59,319,135,384,281⟩⟩,⟨8,1181745671977749726267,⟨27,31,133,59,59,127,199,128,25⟩⟩]⟩
theorem node640 : UpperPrefix a [3,4,7,5,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,0,8,1] 30 cert640 (by decide +kernel)

def cert641 : Local := ⟨⟨340,329,330,0,334,14,0,78,70⟩,[(3,4),(6,2)],[(4,1,0),(7,2,6),(5,3,3),(0,4,1)]⟩
theorem node641 : UpperPrefix a [3,4,7,5,0,8,2] 30 :=
  local_sound a [3,4,7,5,0,8,2] 30 cert641 (by decide +kernel)

theorem node642 : UpperPrefix a [3,4,7,5,0,8] 30 :=
  branch_upper a [3,4,7,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,0,8,0] 30 (by decide +kernel))
  node640
  node641
  (invalid_upper a [3,4,7,5,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,8,8] 30 (by decide +kernel)))

theorem node643 : UpperPrefix a [3,4,7,5,0] 30 :=
  branch_upper a [3,4,7,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,0,0] 30 (by decide +kernel))
  node638
  node639
  (invalid_upper a [3,4,7,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,0,7] 30 (by decide +kernel))
  node642)

def cert644 : Leaf := ⟨⟨212,201,72,0,205,140,269,77,197⟩,[(3,4)],[(4,1,0),(5,3,3)],⟨11,22,133,56,50,97,452,452,332⟩,⟨11,22,133,56,50,97,192,384,264⟩,[⟨1,1338193667842684340142081,⟨493,508,485,508,508,485,192,384,456⟩⟩,⟨8,1181747928184199890043,⟨27,31,133,59,59,127,255,128,25⟩⟩]⟩
theorem node644 : UpperPrefix a [3,4,7,5,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,0] 30 cert644 (by decide +kernel)

def cert645 : Leaf := ⟨⟨336,329,328,0,333,393,265,73,65⟩,[(3,4)],[(4,1,0),(7,2,5),(5,3,3),(2,5,4)],⟨11,22,133,56,50,100,449,449,329⟩,⟨11,22,133,56,50,100,192,384,264⟩,[⟨1,1214876138945191173423105,⟨493,252,485,56,56,228,192,384,264⟩⟩]⟩
theorem node645 : UpperPrefix a [3,4,7,5,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,2] 30 cert645 (by decide +kernel)

def cert646 : Leaf := ⟨⟨144,457,328,0,461,141,5,77,197⟩,[(3,4)],[(4,1,0),(5,3,3)],⟨11,22,133,56,50,352,197,453,333⟩,⟨11,22,133,56,50,352,192,384,264⟩,[⟨1,1214876138874822429245441,⟨493,252,485,56,56,352,192,384,264⟩⟩,⟨8,1181817726818696823827,⟨11,95,197,57,59,96,192,128,8⟩⟩,⟨2,1210107565283853832553491,⟨11,27,129,57,59,352,192,384,264⟩⟩,⟨3,1210107637341444650304513,⟨3,86,197,48,50,352,192,384,256⟩⟩,⟨6,1210106412362349226755091,⟨11,31,133,57,59,288,128,384,264⟩⟩]⟩
theorem node646 : UpperPrefix a [3,4,7,5,1,8] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,8] 30 cert646 (by decide +kernel)

theorem node647 : UpperPrefix a [3,4,7,5,1] 30 :=
  branch_upper a [3,4,7,5,1] 30 (by decide) (fin9_cases _
  node644
  (invalid_upper a [3,4,7,5,1,1] 30 (by decide +kernel))
  node645
  (invalid_upper a [3,4,7,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,7] 30 (by decide +kernel))
  node646)

def cert648 : Leaf := ⟨⟨400,0,330,0,459,395,267,75,195⟩,[(1,4),(3,4)],[(4,1,0),(5,3,3),(2,4,1)],⟨11,22,133,56,52,355,451,451,331⟩,⟨11,22,133,56,52,96,192,384,264⟩,[⟨6,1210106412362349226763291,⟨11,31,133,59,63,32,128,384,265⟩⟩]⟩
theorem node648 : UpperPrefix a [3,4,7,5,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,2] 30 cert648 (by decide +kernel)

def cert649 : Local := ⟨⟨404,393,266,0,0,399,271,15,135⟩,[(3,4),(4,5)],[(4,1,0),(5,3,3),(6,4,3),(6,4,4)]⟩
theorem node649 : UpperPrefix a [3,4,7,5,6] 30 :=
  local_sound a [3,4,7,5,6] 30 cert649 (by decide +kernel)

def cert650 : Leaf := ⟨⟨212,457,72,0,205,142,268,76,196⟩,[(3,4)],[(4,1,0),(5,3,3),(1,6,5)],⟨11,22,133,56,304,97,194,452,332⟩,⟨11,22,133,56,304,97,194,384,264⟩,[⟨0,1219570799036862362027008,⟨458,478,196,56,312,96,450,384,264⟩⟩,⟨8,1181747921024489358339,⟨11,31,133,56,56,101,231,128,8⟩⟩]⟩
theorem node650 : UpperPrefix a [3,4,7,5,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,0,1] 30 cert650 (by decide +kernel)

def cert651 : Local := ⟨⟨340,329,330,0,79,270,0,79,71⟩,[(3,4),(6,2)],[(4,1,0),(7,2,6),(5,3,3)]⟩
theorem node651 : UpperPrefix a [3,4,7,5,8,0,2] 30 :=
  local_sound a [3,4,7,5,8,0,2] 30 cert651 (by decide +kernel)

theorem node652 : UpperPrefix a [3,4,7,5,8,0] 30 :=
  branch_upper a [3,4,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,8,0,0] 30 (by decide +kernel))
  node650
  node651
  (invalid_upper a [3,4,7,5,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,8] 30 (by decide +kernel)))

def cert653 : Leaf := ⟨⟨208,457,328,0,207,133,5,77,197⟩,[(3,4)],[(4,1,0),(5,3,3)],⟨11,22,133,56,304,98,197,453,333⟩,⟨11,22,133,56,304,98,192,384,264⟩,[⟨1,1214876138698900300365825,⟨461,220,453,56,312,96,192,384,264⟩⟩,⟨8,1181817797187709436963,⟨43,127,197,57,57,107,192,128,8⟩⟩,⟨3,1210107637411813394482177,⟨35,118,197,48,304,98,192,384,256⟩⟩,⟨2,1210107565283853832553475,⟨11,27,129,56,312,99,192,384,264⟩⟩]⟩
theorem node653 : UpperPrefix a [3,4,7,5,8,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,1] 30 cert653 (by decide +kernel)

def cert654 : Leaf := ⟨⟨16,329,330,0,79,395,267,75,67⟩,[(3,4)],[(4,1,0),(7,2,5),(5,3,3)],⟨11,22,133,56,304,100,195,451,331⟩,⟨11,22,133,56,304,100,192,384,264⟩,[⟨2,1224302388891768860967939,⟨459,475,449,56,312,96,192,384,264⟩⟩,⟨6,1210106412362349226755075,⟨11,31,133,56,312,36,128,384,264⟩⟩,⟨8,1181745669224658895875,⟨11,31,133,56,56,100,192,128,8⟩⟩]⟩
theorem node654 : UpperPrefix a [3,4,7,5,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,2] 30 cert654 (by decide +kernel)

theorem node655 : UpperPrefix a [3,4,7,5,8] 30 :=
  branch_upper a [3,4,7,5,8] 30 (by decide) (fin9_cases _
  node652
  node653
  node654
  (invalid_upper a [3,4,7,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,8] 30 (by decide +kernel)))

theorem node656 : UpperPrefix a [3,4,7,5] 30 :=
  branch_upper a [3,4,7,5] 30 (by decide) (fin9_cases _
  node643
  node647
  node648
  (invalid_upper a [3,4,7,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,5] 30 (by decide +kernel))
  node649
  (invalid_upper a [3,4,7,5,7] 30 (by decide +kernel))
  node655)

def cert657 : Leaf := ⟨⟨112,233,104,32,74,140,300,108,228⟩,[],[(4,1,0),(0,4,1),(1,5,4)],⟨11,22,133,88,49,98,484,420,300⟩,⟨11,22,133,88,49,98,192,384,264⟩,[⟨8,1181748227317968264569,⟨59,23,151,127,59,127,255,151,59⟩⟩,⟨2,1210107565286055003292705,⟨11,18,129,88,57,123,192,384,264⟩⟩,⟨7,1208926973665337593037857,⟨11,22,5,88,57,123,64,256,264⟩⟩]⟩
theorem node657 : UpperPrefix a [3,4,7,6,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,1] 30 cert657 (by decide +kernel)

def cert658 : Leaf := ⟨⟨112,105,106,34,74,138,40,106,98⟩,[],[(4,1,0),(7,2,5),(0,4,1)],⟨11,22,133,88,49,100,194,416,296⟩,⟨11,22,133,88,49,100,194,384,264⟩,[⟨8,1184130851853474848255,⟨59,127,255,127,59,127,255,255,59⟩⟩,⟨2,1437223914350364290188355,⟨75,475,129,473,441,505,203,384,264⟩⟩]⟩
theorem node658 : UpperPrefix a [3,4,7,6,0,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,2,1] 30 cert658 (by decide +kernel)

def cert659 : Leaf := ⟨⟨84,73,74,38,78,138,14,78,70⟩,[],[(4,1,0),(7,2,5),(0,4,1),(5,6,3)],⟨11,22,133,88,49,100,224,386,266⟩,⟨11,22,133,88,49,100,224,384,264⟩,[⟨8,1184130851853474848255,⟨59,127,255,127,59,127,255,255,59⟩⟩]⟩
theorem node659 : UpperPrefix a [3,4,7,6,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,2,5] 30 cert659 (by decide +kernel)

def cert660 : Leaf := ⟨⟨116,105,106,36,76,136,0,110,102⟩,[(6,7)],[(4,1,0),(7,2,5),(0,4,1),(8,6,6)],⟨11,22,133,88,49,100,448,418,298⟩,⟨11,22,133,88,49,100,448,384,264⟩,[⟨1,1210109871267878097911809,⟨9,60,253,88,57,124,448,448,264⟩⟩]⟩
theorem node660 : UpperPrefix a [3,4,7,6,0,2,8] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,2,8] 30 cert660 (by decide +kernel)

theorem node661 : UpperPrefix a [3,4,7,6,0,2] 30 :=
  branch_upper a [3,4,7,6,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,0,2,0] 30 (by decide +kernel))
  node658
  (invalid_upper a [3,4,7,6,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,2,4] 30 (by decide +kernel))
  node659
  (invalid_upper a [3,4,7,6,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,2,7] 30 (by decide +kernel))
  node660)

def cert662 : Leaf := ⟨⟨336,329,330,258,330,10,268,74,98⟩,[],[(4,1,0),(0,4,1),(2,7,6)],⟨11,22,133,88,49,352,194,388,296⟩,⟨11,22,133,88,49,352,194,388,264⟩,[⟨5,1212768795220963079763291,⟨11,95,133,95,223,453,207,453,463⟩⟩,⟨7,1780333320630864566029377,⟨315,278,279,377,313,377,379,262,312⟩⟩]⟩
theorem node662 : UpperPrefix a [3,4,7,6,0,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,8,1,2] 30 cert662 (by decide +kernel)

def cert663 : Leaf := ⟨⟨244,225,98,166,198,134,36,0,230⟩,[(7,5)],[(4,1,0),(0,4,1),(8,5,7)],⟨11,22,133,88,49,352,194,416,268⟩,⟨11,22,133,88,49,352,194,416,264⟩,[⟨3,1212768881915527169063937,⟨3,86,247,86,247,480,226,480,482⟩⟩]⟩
theorem node663 : UpperPrefix a [3,4,7,6,0,8,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,8,1,5] 30 cert663 (by decide +kernel)

theorem node664 : UpperPrefix a [3,4,7,6,0,8,1] 30 :=
  branch_upper a [3,4,7,6,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,1,1] 30 (by decide +kernel))
  node662
  (invalid_upper a [3,4,7,6,0,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,1,4] 30 (by decide +kernel))
  node663
  (invalid_upper a [3,4,7,6,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,1,8] 30 (by decide +kernel)))

def cert665 : Leaf := ⟨⟨276,297,298,262,270,14,0,46,102⟩,[(6,2)],[(4,1,0),(7,2,6),(0,4,1)],⟨11,22,133,88,49,352,196,418,298⟩,⟨11,22,133,88,49,352,196,384,264⟩,[⟨6,1210401560269725501519113,⟨11,22,133,31,183,439,132,389,267⟩⟩,⟨5,1210107636215546085639171,⟨11,95,197,88,17,320,196,384,264⟩⟩]⟩
theorem node665 : UpperPrefix a [3,4,7,6,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,8,2] 30 cert665 (by decide +kernel)

def cert666 : Leaf := ⟨⟨148,137,10,166,142,142,270,14,134⟩,[],[(4,1,0),(0,4,1),(8,5,6),(5,6,3)],⟨11,22,133,88,49,352,224,390,270⟩,⟨11,22,133,88,49,352,224,384,264⟩,[⟨6,1255494626157908569945353,⟨399,150,389,415,439,439,182,389,399⟩⟩]⟩
theorem node666 : UpperPrefix a [3,4,7,6,0,8,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,8,5] 30 cert666 (by decide +kernel)

theorem node667 : UpperPrefix a [3,4,7,6,0,8] 30 :=
  branch_upper a [3,4,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,0,8,0] 30 (by decide +kernel))
  node664
  node665
  (invalid_upper a [3,4,7,6,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,4] 30 (by decide +kernel))
  node666
  (invalid_upper a [3,4,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,8] 30 (by decide +kernel)))

theorem node668 : UpperPrefix a [3,4,7,6,0] 30 :=
  branch_upper a [3,4,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,0,0] 30 (by decide +kernel))
  node657
  node661
  (invalid_upper a [3,4,7,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,7] 30 (by decide +kernel))
  node667)

def cert669 : Leaf := ⟨⟨112,105,106,35,73,10,0,107,99⟩,[(6,2)],[(4,1,0),(7,2,6)],⟨11,22,133,88,50,97,196,416,296⟩,⟨11,22,133,88,50,97,196,384,264⟩,[⟨2,1482169370536504998233105,⟨443,403,401,505,443,505,192,384,424⟩⟩,⟨8,1184130851853474848255,⟨59,127,255,127,59,127,255,255,59⟩⟩]⟩
theorem node669 : UpperPrefix a [3,4,7,6,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,0,2] 30 cert669 (by decide +kernel)

def cert670 : Leaf := ⟨⟨148,137,8,165,141,140,13,13,133⟩,[],[(4,1,0),(5,6,3)],⟨11,22,133,88,50,97,224,388,268⟩,⟨11,22,133,88,50,97,224,384,264⟩,[⟨8,1184130851853474848255,⟨59,127,255,127,59,127,255,255,59⟩⟩,⟨1,1300340804888244264370177,⟨493,508,485,472,508,485,228,384,264⟩⟩,⟨6,1255383945697864354952457,⟨399,150,389,415,182,439,182,389,399⟩⟩]⟩
theorem node670 : UpperPrefix a [3,4,7,6,1,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,0,5] 30 cert670 (by decide +kernel)

def cert671 : Leaf := ⟨⟨116,105,104,37,77,12,0,109,229⟩,[(6,7)],[(4,1,0),(8,6,6)],⟨11,22,133,88,50,97,448,420,300⟩,⟨11,22,133,88,50,97,448,384,264⟩,[⟨1,1300343254846441553920001,⟨493,508,485,472,508,485,448,448,328⟩⟩,⟨7,1208926973944682265971729,⟨59,23,23,121,59,121,320,256,296⟩⟩]⟩
theorem node671 : UpperPrefix a [3,4,7,6,1,0,8] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,0,8] 30 cert671 (by decide +kernel)

theorem node672 : UpperPrefix a [3,4,7,6,1,0] 30 :=
  branch_upper a [3,4,7,6,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,0,1] 30 (by decide +kernel))
  node669
  (invalid_upper a [3,4,7,6,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,0,4] 30 (by decide +kernel))
  node670
  (invalid_upper a [3,4,7,6,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,0,7] 30 (by decide +kernel))
  node671)

def cert673 : Leaf := ⟨⟨112,105,104,33,77,137,297,105,97⟩,[],[(4,1,0),(7,2,5),(2,5,4)],⟨11,22,133,88,50,100,481,417,297⟩,⟨11,22,133,88,50,100,192,384,264⟩,[⟨1,1214876138945189025939457,⟨493,252,485,88,56,228,192,384,264⟩⟩,⟨8,1181748227317968264569,⟨59,23,151,127,59,127,255,151,59⟩⟩]⟩
theorem node673 : UpperPrefix a [3,4,7,6,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,2] 30 cert673 (by decide +kernel)

def cert674 : Leaf := ⟨⟨180,169,0,165,141,141,0,45,229⟩,[(2,6),(6,2)],[(4,1,0)],⟨11,22,133,88,50,352,193,420,300⟩,⟨11,22,133,88,50,352,193,384,264⟩,[⟨1,1263077483743066891485185,⟨493,508,485,508,440,484,485,384,424⟩⟩,⟨6,1210401560269725514102025,⟨11,22,133,31,182,439,133,389,267⟩⟩,⟨8,1184123572029400044859,⟨11,95,197,95,59,127,197,197,11⟩⟩]⟩
theorem node674 : UpperPrefix a [3,4,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,8,0] 30 cert674 (by decide +kernel)

def cert675 : Leaf := ⟨⟨84,361,360,4,333,13,0,109,101⟩,[(6,2)],[(4,1,0),(7,2,6)],⟨11,22,133,88,50,352,196,417,297⟩,⟨11,22,133,88,50,352,196,384,264⟩,[⟨1,1214876174903619448209409,⟨493,252,485,88,120,352,228,384,264⟩⟩,⟨5,1210107636215546085639187,⟨11,95,197,89,27,320,196,384,264⟩⟩,⟨8,1181817726816817775635,⟨11,95,197,89,59,96,196,128,8⟩⟩,⟨0,1210107637341445992481792,⟨10,94,196,88,58,352,196,384,264⟩⟩]⟩
theorem node675 : UpperPrefix a [3,4,7,6,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,8,2] 30 cert675 (by decide +kernel)

def cert676 : Leaf := ⟨⟨148,137,8,165,141,141,269,13,133⟩,[],[(4,1,0),(8,5,6),(5,6,3)],⟨11,22,133,88,50,352,224,389,269⟩,⟨11,22,133,88,50,352,224,384,264⟩,[⟨1,1214878485250228289273857,⟨493,252,485,88,120,352,224,480,264⟩⟩,⟨6,1255383945697864354952457,⟨399,150,389,415,182,439,182,389,399⟩⟩]⟩
theorem node676 : UpperPrefix a [3,4,7,6,1,8,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,8,5] 30 cert676 (by decide +kernel)

theorem node677 : UpperPrefix a [3,4,7,6,1,8] 30 :=
  branch_upper a [3,4,7,6,1,8] 30 (by decide) (fin9_cases _
  node674
  (invalid_upper a [3,4,7,6,1,8,1] 30 (by decide +kernel))
  node675
  (invalid_upper a [3,4,7,6,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,4] 30 (by decide +kernel))
  node676
  (invalid_upper a [3,4,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,8] 30 (by decide +kernel)))

theorem node678 : UpperPrefix a [3,4,7,6,1] 30 :=
  branch_upper a [3,4,7,6,1] 30 (by decide) (fin9_cases _
  node672
  (invalid_upper a [3,4,7,6,1,1] 30 (by decide +kernel))
  node673
  (invalid_upper a [3,4,7,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,7] 30 (by decide +kernel))
  node677)

def cert679 : Leaf := ⟨⟨112,0,106,162,203,10,298,106,98⟩,[(1,4)],[(4,1,0),(2,4,1),(0,5,4)],⟨11,22,133,88,52,97,482,418,298⟩,⟨11,22,133,88,52,97,192,384,264⟩,[⟨8,1181748209657062684025,⟨59,23,133,127,63,127,255,133,59⟩⟩,⟨7,1251428272290436058457097,⟨299,22,261,379,54,353,64,256,297⟩⟩]⟩
theorem node679 : UpperPrefix a [3,4,7,6,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,0] 30 cert679 (by decide +kernel)

def cert680 : Leaf := ⟨⟨112,0,106,163,203,0,299,107,99⟩,[(1,4)],[(4,1,0),(2,4,1)],⟨11,22,133,88,52,98,481,417,297⟩,⟨11,22,133,88,52,98,192,384,264⟩,[⟨8,1181748209657062684025,⟨59,23,133,127,63,127,255,133,59⟩⟩,⟨7,1251428272290436058457097,⟨299,22,261,379,54,98,64,256,297⟩⟩,⟨0,1210107565565326662837248,⟨42,22,132,122,54,98,192,384,296⟩⟩,⟨3,1210107565565325589095425,⟨35,22,133,114,54,98,192,384,288⟩⟩]⟩
theorem node680 : UpperPrefix a [3,4,7,6,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,1] 30 cert680 (by decide +kernel)

def cert681 : Local := ⟨⟨496,0,0,419,459,139,0,107,227⟩,[(1,4),(2,6),(6,2)],[(4,1,0),(2,4,1)]⟩
theorem node681 : UpperPrefix a [3,4,7,6,2,8,0] 30 :=
  local_sound a [3,4,7,6,2,8,0] 30 cert681 (by decide +kernel)

def cert682 : Local := ⟨⟨496,0,0,418,450,130,288,106,226⟩,[(1,4),(2,7)],[(3,0,7),(4,1,0),(2,4,1),(0,7,2)]⟩
theorem node682 : UpperPrefix a [3,4,7,6,2,8,1,0] 30 :=
  local_sound a [3,4,7,6,2,8,1,0] 30 cert682 (by decide +kernel)

def cert683 : Local := ⟨⟨240,0,106,163,203,139,41,0,227⟩,[(1,4),(7,5)],[(4,1,0),(2,4,1),(8,5,7)]⟩
theorem node683 : UpperPrefix a [3,4,7,6,2,8,1,5] 30 :=
  local_sound a [3,4,7,6,2,8,1,5] 30 cert683 (by decide +kernel)

theorem node684 : UpperPrefix a [3,4,7,6,2,8,1] 30 :=
  branch_upper a [3,4,7,6,2,8,1] 30 (by decide) (fin9_cases _
  node682
  (invalid_upper a [3,4,7,6,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,1,4] 30 (by decide +kernel))
  node683
  (invalid_upper a [3,4,7,6,2,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,1,8] 30 (by decide +kernel)))

def cert685 : Leaf := ⟨⟨144,0,10,163,139,139,267,11,131⟩,[(1,4)],[(4,1,0),(2,4,1),(8,5,6),(5,6,3)],⟨11,22,133,88,52,352,224,387,267⟩,⟨11,22,133,88,52,352,224,384,264⟩,[⟨6,1255347052209716935849225,⟨399,22,389,415,182,439,182,389,399⟩⟩]⟩
theorem node685 : UpperPrefix a [3,4,7,6,2,8,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,8,5] 30 cert685 (by decide +kernel)

theorem node686 : UpperPrefix a [3,4,7,6,2,8] 30 :=
  branch_upper a [3,4,7,6,2,8] 30 (by decide) (fin9_cases _
  node681
  node684
  (invalid_upper a [3,4,7,6,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,4] 30 (by decide +kernel))
  node685
  (invalid_upper a [3,4,7,6,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,8] 30 (by decide +kernel)))

theorem node687 : UpperPrefix a [3,4,7,6,2] 30 :=
  branch_upper a [3,4,7,6,2] 30 (by decide) (fin9_cases _
  node679
  node680
  (invalid_upper a [3,4,7,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,7] 30 (by decide +kernel))
  node686)

def cert688 : Leaf := ⟨⟨336,329,328,257,73,266,269,73,97⟩,[],[(4,1,0),(1,6,5),(2,7,6)],⟨11,22,133,88,304,97,194,388,296⟩,⟨11,22,133,88,304,97,194,388,264⟩,[⟨5,1212621401412358492403035,⟨79,223,133,223,479,69,207,453,463⟩⟩,⟨7,1780333320648456752139329,⟨315,278,279,377,312,377,379,278,312⟩⟩]⟩
theorem node688 : UpperPrefix a [3,4,7,6,8,0,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,0,1,2] 30 cert688 (by decide +kernel)

def cert689 : Leaf := ⟨⟨496,488,360,416,0,394,296,0,228⟩,[(4,7),(7,4)],[(4,1,0),(1,6,5)],⟨11,22,133,88,304,97,194,416,268⟩,⟨11,22,133,88,304,97,194,416,264⟩,[⟨0,1238589446228855778970624,⟨330,478,478,216,432,104,474,432,264⟩⟩,⟨2,1212616361171898247152707,⟨107,251,177,249,432,105,251,432,440⟩⟩]⟩
theorem node689 : UpperPrefix a [3,4,7,6,8,0,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,0,1,5] 30 cert689 (by decide +kernel)

theorem node690 : UpperPrefix a [3,4,7,6,8,0,1] 30 :=
  branch_upper a [3,4,7,6,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,1,1] 30 (by decide +kernel))
  node688
  (invalid_upper a [3,4,7,6,8,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,1,4] 30 (by decide +kernel))
  node689
  (invalid_upper a [3,4,7,6,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,1,8] 30 (by decide +kernel)))

def cert691 : Leaf := ⟨⟨20,297,298,5,79,12,0,47,103⟩,[(6,2)],[(4,1,0),(7,2,6)],⟨11,22,133,88,304,97,196,418,298⟩,⟨11,22,133,88,304,97,196,384,264⟩,[⟨6,1210253986314936795542793,⟨15,150,133,159,439,33,132,389,271⟩⟩,⟨8,1181817937923050308611,⟨43,127,229,88,48,97,228,128,8⟩⟩,⟨1,1210107637482183480836097,⟨9,124,229,88,304,97,228,384,264⟩⟩,⟨5,1210107636215546085639171,⟨11,95,197,88,272,65,196,384,264⟩⟩]⟩
theorem node691 : UpperPrefix a [3,4,7,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,0,2] 30 cert691 (by decide +kernel)

def cert692 : Leaf := ⟨⟨144,393,266,161,143,136,9,15,135⟩,[],[(4,1,0),(5,6,3)],⟨11,22,133,88,304,97,224,390,270⟩,⟨11,22,133,88,304,97,224,384,264⟩,[⟨6,1255494626157908569945353,⟨399,150,389,415,439,439,182,389,399⟩⟩,⟨2,1210107637552552223966211,⟨43,123,225,88,304,97,224,384,264⟩⟩,⟨8,1181817937923050308611,⟨43,127,229,88,48,97,224,128,8⟩⟩,⟨1,1210107637482183480836097,⟨9,124,229,88,304,97,224,384,264⟩⟩]⟩
theorem node692 : UpperPrefix a [3,4,7,6,8,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,0,5] 30 cert692 (by decide +kernel)

theorem node693 : UpperPrefix a [3,4,7,6,8,0] 30 :=
  branch_upper a [3,4,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,8,0,0] 30 (by decide +kernel))
  node690
  node691
  (invalid_upper a [3,4,7,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,4] 30 (by decide +kernel))
  node692
  (invalid_upper a [3,4,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,8] 30 (by decide +kernel)))

def cert694 : Leaf := ⟨⟨240,233,0,161,205,137,0,109,229⟩,[(2,6),(6,2)],[(4,1,0)],⟨11,22,133,88,304,98,193,420,300⟩,⟨11,22,133,88,304,98,193,384,264⟩,[⟨1,1361518512700657327144961,⟨9,92,197,92,440,508,197,384,264⟩⟩,⟨8,1184123921669802693931,⟨43,127,197,127,49,111,197,197,43⟩⟩,⟨2,1210107637411814735610915,⟨43,123,193,88,305,107,193,384,264⟩⟩]⟩
theorem node694 : UpperPrefix a [3,4,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,0] 30 cert694 (by decide +kernel)

def cert695 : Leaf := ⟨⟨48,297,298,35,75,13,0,43,99⟩,[(6,2)],[(4,1,0),(7,2,6),(2,6,5)],⟨11,22,133,88,304,98,196,417,297⟩,⟨11,22,133,88,304,98,196,384,264⟩,[⟨6,1210253986314936795542793,⟨15,150,133,159,439,34,132,389,271⟩⟩,⟨8,1181817797185561953315,⟨43,127,197,88,49,107,196,128,8⟩⟩]⟩
theorem node695 : UpperPrefix a [3,4,7,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,2] 30 cert695 (by decide +kernel)

def cert696 : Leaf := ⟨⟨464,448,0,418,194,384,258,74,198⟩,[(2,7)],[(3,0,7),(4,1,0),(5,6,3),(0,7,2)],⟨11,22,133,88,304,98,224,385,268⟩,⟨11,22,133,88,304,98,224,385,264⟩,[⟨2,1210257841510595715662883,⟨107,251,249,216,505,107,249,505,264⟩⟩]⟩
theorem node696 : UpperPrefix a [3,4,7,6,8,1,5,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,5,0] 30 cert696 (by decide +kernel)

def cert697 : Leaf := ⟨⟨400,384,266,418,194,388,262,11,131⟩,[],[(4,1,0),(5,6,3)],⟨11,22,133,88,304,98,224,388,265⟩,⟨11,22,133,88,304,98,224,388,264⟩,[⟨0,1210109950159783279528960,⟨42,126,254,120,304,106,250,510,264⟩⟩,⟨6,1255236371738677604529417,⟨399,150,389,415,439,34,164,389,399⟩⟩,⟨2,1743734977854731548886049,⟨267,274,385,344,313,379,505,384,264⟩⟩,⟨3,1210109950159755630676993,⟨35,118,247,112,304,98,242,502,256⟩⟩]⟩
theorem node697 : UpperPrefix a [3,4,7,6,8,1,5,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,5,2] 30 cert697 (by decide +kernel)

theorem node698 : UpperPrefix a [3,4,7,6,8,1,5] 30 :=
  branch_upper a [3,4,7,6,8,1,5] 30 (by decide) (fin9_cases _
  node696
  (invalid_upper a [3,4,7,6,8,1,5,1] 30 (by decide +kernel))
  node697
  (invalid_upper a [3,4,7,6,8,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,8] 30 (by decide +kernel)))

theorem node699 : UpperPrefix a [3,4,7,6,8,1] 30 :=
  branch_upper a [3,4,7,6,8,1] 30 (by decide) (fin9_cases _
  node694
  (invalid_upper a [3,4,7,6,8,1,1] 30 (by decide +kernel))
  node695
  (invalid_upper a [3,4,7,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,4] 30 (by decide +kernel))
  node698
  (invalid_upper a [3,4,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,8] 30 (by decide +kernel)))

def cert700 : Leaf := ⟨⟨372,352,0,294,70,387,0,102,102⟩,[(2,6),(6,2)],[(4,1,0),(7,2,5),(0,6,5)],⟨11,22,133,88,304,100,193,418,298⟩,⟨11,22,133,88,304,100,193,384,264⟩,[⟨3,1212468823344852698665985,⟨35,118,229,118,432,100,229,400,434⟩⟩]⟩
theorem node700 : UpperPrefix a [3,4,7,6,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,2,0] 30 cert700 (by decide +kernel)

def cert701 : Local := ⟨⟨372,352,0,294,70,386,292,110,102⟩,[(2,7)],[(3,0,7),(4,1,0),(7,2,5),(0,7,2)]⟩
theorem node701 : UpperPrefix a [3,4,7,6,8,2,1,0] 30 :=
  local_sound a [3,4,7,6,8,2,1,0] 30 cert701 (by decide +kernel)

def cert702 : Leaf := ⟨⟨368,360,362,290,0,394,296,0,99⟩,[(4,7),(7,4)],[(4,1,0),(7,2,5)],⟨11,22,133,88,304,100,194,416,265⟩,⟨11,22,133,88,304,100,194,416,264⟩,[⟨0,1210255247542744140221440,⟨106,254,254,216,432,110,250,432,264⟩⟩,⟨2,1715843536848478040753219,⟨331,475,401,473,440,505,475,440,264⟩⟩]⟩
theorem node702 : UpperPrefix a [3,4,7,6,8,2,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,2,1,5] 30 cert702 (by decide +kernel)

theorem node703 : UpperPrefix a [3,4,7,6,8,2,1] 30 :=
  branch_upper a [3,4,7,6,8,2,1] 30 (by decide) (fin9_cases _
  node701
  (invalid_upper a [3,4,7,6,8,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,1,4] 30 (by decide +kernel))
  node702
  (invalid_upper a [3,4,7,6,8,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,1,8] 30 (by decide +kernel)))

#print axioms node703
end Delivery.FiniteExclusion.Sharp3x6
