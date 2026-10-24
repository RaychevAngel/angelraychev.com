import RegularNineSharp2x7Base
import RegularNineSharp2x7C011
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert768 : Local := ⟨⟨440,0,0,0,0,159,0,63,187⟩,[(1,3),(2,6),(3,1),(4,5),(6,2)],[(6,4,4)]⟩
theorem node768 : UpperPrefix a [2,4,7,0,6,8,3] 30 :=
  local_sound a [2,4,7,0,6,8,3] 30 cert768 (by decide +kernel)

def cert769 : Local := ⟨⟨152,0,19,0,0,159,287,31,155⟩,[(1,3),(3,1),(4,5)],[(6,4,4),(8,5,6),(5,6,4)]⟩
theorem node769 : UpperPrefix a [2,4,7,0,6,8,5] 30 :=
  local_sound a [2,4,7,0,6,8,5] 30 cert769 (by decide +kernel)

theorem node770 : UpperPrefix a [2,4,7,0,6,8] 30 :=
  branch_upper a [2,4,7,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,0,6,8,0] 30 (by decide +kernel))
  node767
  (invalid_upper a [2,4,7,0,6,8,2] 30 (by decide +kernel))
  node768
  (invalid_upper a [2,4,7,0,6,8,4] 30 (by decide +kernel))
  node769
  (invalid_upper a [2,4,7,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,6,8,8] 30 (by decide +kernel)))

theorem node771 : UpperPrefix a [2,4,7,0,6] 30 :=
  branch_upper a [2,4,7,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,0,6,0] 30 (by decide +kernel))
  node765
  (invalid_upper a [2,4,7,0,6,2] 30 (by decide +kernel))
  node766
  (invalid_upper a [2,4,7,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,6,7] 30 (by decide +kernel))
  node770)

def cert772 : Leaf := ⟨⟨16,0,369,0,201,153,57,125,249⟩,[(1,3),(3,1)],[],⟨7,19,140,25,304,98,232,488,364⟩,⟨7,19,140,25,304,98,192,384,260⟩,[⟨1,1361519017103811289284609,⟨13,25,140,25,500,508,192,384,260⟩⟩,⟨2,1210107637534960037925889,⟨107,59,234,59,304,106,192,400,368⟩⟩,⟨8,1181817902738678223877,⟨111,59,239,59,48,106,192,128,101⟩⟩,⟨3,1210107565283850612380677,⟨7,19,135,19,304,98,192,384,261⟩⟩,⟨5,1210107564157952047715333,⟨15,27,143,27,272,74,192,384,261⟩⟩,⟨6,1210106412362347347710981,⟨15,27,143,27,304,42,128,384,261⟩⟩,⟨7,1208926973663134543254533,⟨15,27,15,27,304,106,64,256,261⟩⟩]⟩
theorem node772 : UpperPrefix a [2,4,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,0,8,1] 30 cert772 (by decide +kernel)

def cert773 : Leaf := ⟨⟨248,0,112,0,200,145,57,120,248⟩,[(1,3),(3,1)],[],⟨7,19,140,25,304,104,194,480,356⟩,⟨7,19,140,25,304,104,194,384,260⟩,[⟨1,1664340193613272862162945,⟨13,25,140,25,436,508,508,384,260⟩⟩,⟨0,1361518440643058717426688,⟨6,18,140,24,436,508,194,384,260⟩⟩,⟨2,1212468823028194674217985,⟨107,59,234,59,432,106,234,400,496⟩⟩,⟨8,1181820154540656178277,⟨111,59,239,59,59,111,239,128,101⟩⟩]⟩
theorem node773 : UpperPrefix a [2,4,7,0,8,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,0,8,3,1] 30 cert773 (by decide +kernel)

def cert774 : Leaf := ⟨⟨472,0,322,0,206,390,270,78,202⟩,[(1,3),(3,1)],[],⟨7,19,140,25,304,104,224,450,326⟩,⟨7,19,140,25,304,104,224,384,260⟩,[⟨0,1214857836510435647423488,⟨502,466,252,508,304,124,224,400,372⟩⟩,⟨4,1214857836491125474460673,⟨487,451,236,493,288,108,224,384,356⟩⟩,⟨5,1361518439514962207454271,⟨15,31,143,31,415,463,453,384,261⟩⟩]⟩
theorem node774 : UpperPrefix a [2,4,7,0,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,0,8,3,5] 30 cert774 (by decide +kernel)

theorem node775 : UpperPrefix a [2,4,7,0,8,3] 30 :=
  branch_upper a [2,4,7,0,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,0,8,3,0] 30 (by decide +kernel))
  node773
  (invalid_upper a [2,4,7,0,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,3,4] 30 (by decide +kernel))
  node774
  (invalid_upper a [2,4,7,0,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,3,8] 30 (by decide +kernel)))

theorem node776 : UpperPrefix a [2,4,7,0,8] 30 :=
  branch_upper a [2,4,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,0,8,0] 30 (by decide +kernel))
  node772
  (invalid_upper a [2,4,7,0,8,2] 30 (by decide +kernel))
  node775
  (invalid_upper a [2,4,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,8,8] 30 (by decide +kernel)))

theorem node777 : UpperPrefix a [2,4,7,0] 30 :=
  branch_upper a [2,4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,0,0] 30 (by decide +kernel))
  node763
  (invalid_upper a [2,4,7,0,2] 30 (by decide +kernel))
  node764
  (invalid_upper a [2,4,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,0,5] 30 (by decide +kernel))
  node771
  (invalid_upper a [2,4,7,0,7] 30 (by decide +kernel))
  node776)

def cert778 : Leaf := ⟨⟨488,0,352,0,460,396,300,108,232⟩,[(1,4),(3,1)],[(4,1,3),(0,4,1),(0,4,3)],⟨7,19,140,26,49,360,488,488,364⟩,⟨7,19,140,26,49,96,192,384,260⟩,[⟨1,1266886860137792986415105,⟨501,17,492,508,49,96,192,384,484⟩⟩]⟩
theorem node778 : UpperPrefix a [2,4,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,1,0] 30 cert778 (by decide +kernel)

def cert779 : Leaf := ⟨⟨232,236,96,0,197,140,300,108,232⟩,[(3,1)],[(4,1,3)],⟨7,19,140,26,56,97,480,480,356⟩,⟨7,19,140,26,56,97,192,384,260⟩,[⟨1,1338156702227121476468737,⟨485,501,476,508,508,481,192,384,260⟩⟩,⟨8,1181747927634712519777,⟨15,27,140,26,59,127,255,128,4⟩⟩,⟨0,1285813291192732112913408,⟨14,478,140,478,508,96,192,384,260⟩⟩]⟩
theorem node779 : UpperPrefix a [2,4,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,7,1,3,0] 30 cert779 (by decide +kernel)

def cert780 : Leaf := ⟨⟨232,236,97,0,197,141,44,0,233⟩,[(3,1),(7,5)],[(4,1,3),(8,5,7)],⟨7,19,140,26,56,352,193,416,324⟩,⟨7,19,140,26,56,352,193,416,260⟩,[⟨1,1263225021526946415116289,⟨501,501,444,508,444,480,481,416,404⟩⟩]⟩
theorem node780 : UpperPrefix a [2,4,7,1,3,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,1,3,8,0,5] 30 cert780 (by decide +kernel)

def cert781 : Leaf := ⟨⟨488,492,353,0,453,0,300,0,233⟩,[(3,1),(5,7),(7,5)],[(4,1,3)],⟨7,19,140,26,56,352,193,448,292⟩,⟨7,19,140,26,56,352,193,448,260⟩,[⟨1,1357487888247201851244545,⟨501,501,444,508,444,480,481,480,276⟩⟩]⟩
theorem node781 : UpperPrefix a [2,4,7,1,3,8,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,1,3,8,0,6] 30 cert781 (by decide +kernel)

theorem node782 : UpperPrefix a [2,4,7,1,3,8,0] 30 :=
  branch_upper a [2,4,7,1,3,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,1,3,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,0,4] 30 (by decide +kernel))
  node780
  node781
  (invalid_upper a [2,4,7,1,3,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,0,8] 30 (by decide +kernel)))

def cert783 : Leaf := ⟨⟨232,232,97,0,193,137,265,109,233⟩,[(3,1)],[(4,1,3),(8,5,6)],⟨7,19,140,26,56,352,224,449,325⟩,⟨7,19,140,26,56,352,224,384,260⟩,[⟨1,1214860191558995385778177,⟨501,497,252,252,124,352,224,480,372⟩⟩,⟨2,1210109956695529099363841,⟨91,27,248,26,56,352,224,480,368⟩⟩]⟩
theorem node783 : UpperPrefix a [2,4,7,1,3,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,1,3,8,5] 30 cert783 (by decide +kernel)

theorem node784 : UpperPrefix a [2,4,7,1,3,8] 30 :=
  branch_upper a [2,4,7,1,3,8] 30 (by decide) (fin9_cases _
  node782
  (invalid_upper a [2,4,7,1,3,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,4] 30 (by decide +kernel))
  node783
  (invalid_upper a [2,4,7,1,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,8,8] 30 (by decide +kernel)))

theorem node785 : UpperPrefix a [2,4,7,1,3] 30 :=
  branch_upper a [2,4,7,1,3] 30 (by decide) (fin9_cases _
  node779
  (invalid_upper a [2,4,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,3,7] 30 (by decide +kernel))
  node784)

def cert786 : Leaf := ⟨⟨168,172,35,0,0,142,303,47,171⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4)],⟨7,19,140,26,112,97,488,424,300⟩,⟨7,19,140,26,112,97,192,384,260⟩,[⟨8,1181748490584665945205,⟨15,59,143,59,127,127,255,128,5⟩⟩]⟩
theorem node786 : UpperPrefix a [2,4,7,1,6,0] 30 :=
  Boolean.leaf_sound a [2,4,7,1,6,0] 30 cert786 (by decide +kernel)

def cert787 : Leaf := ⟨⟨168,172,35,0,0,135,303,47,171⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4)],⟨7,19,140,26,112,104,481,417,293⟩,⟨7,19,140,26,112,104,192,384,260⟩,[⟨8,1181748490584665945205,⟨15,59,143,59,127,127,255,128,5⟩⟩]⟩
theorem node787 : UpperPrefix a [2,4,7,1,6,3] 30 :=
  Boolean.leaf_sound a [2,4,7,1,6,3] 30 cert787 (by decide +kernel)

def cert788 : Leaf := ⟨⟨416,420,291,0,0,135,294,47,171⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4)],⟨7,19,140,26,112,352,193,424,300⟩,⟨7,19,140,26,112,352,193,384,260⟩,[⟨3,1210109956728512973098757,⟨87,19,247,18,114,371,243,499,375⟩⟩]⟩
theorem node788 : UpperPrefix a [2,4,7,1,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,7,1,6,8,0] 30 cert788 (by decide +kernel)

def cert789 : Local := ⟨⟨424,428,0,0,0,143,0,47,171⟩,[(2,6),(3,1),(4,5),(6,2)],[(4,1,3),(6,4,4)]⟩
theorem node789 : UpperPrefix a [2,4,7,1,6,8,3] 30 :=
  local_sound a [2,4,7,1,6,8,3] 30 cert789 (by decide +kernel)

def cert790 : Local := ⟨⟨136,140,3,0,0,143,271,15,139⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4),(8,5,6),(5,6,4)]⟩
theorem node790 : UpperPrefix a [2,4,7,1,6,8,5] 30 :=
  local_sound a [2,4,7,1,6,8,5] 30 cert790 (by decide +kernel)

theorem node791 : UpperPrefix a [2,4,7,1,6,8] 30 :=
  branch_upper a [2,4,7,1,6,8] 30 (by decide) (fin9_cases _
  node788
  (invalid_upper a [2,4,7,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,6,8,2] 30 (by decide +kernel))
  node789
  (invalid_upper a [2,4,7,1,6,8,4] 30 (by decide +kernel))
  node790
  (invalid_upper a [2,4,7,1,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,6,8,8] 30 (by decide +kernel)))

theorem node792 : UpperPrefix a [2,4,7,1,6] 30 :=
  branch_upper a [2,4,7,1,6] 30 (by decide) (fin9_cases _
  node786
  (invalid_upper a [2,4,7,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,6,2] 30 (by decide +kernel))
  node787
  (invalid_upper a [2,4,7,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,6,7] 30 (by decide +kernel))
  node791)

def cert793 : Leaf := ⟨⟨488,492,0,0,205,396,0,109,233⟩,[(2,6),(3,1),(6,2)],[(4,1,3)],⟨7,19,140,26,304,97,200,480,356⟩,⟨7,19,140,26,304,97,200,384,260⟩,[⟨1,1366250102590949794250753,⟨501,433,204,24,432,501,204,384,324⟩⟩]⟩
theorem node793 : UpperPrefix a [2,4,7,1,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,1,8,0,3] 30 cert793 (by decide +kernel)

def cert794 : Leaf := ⟨⟨480,484,0,0,197,388,261,101,225⟩,[(2,7),(3,1)],[(4,1,3),(3,7,2)],⟨7,19,140,26,304,97,224,392,324⟩,⟨7,19,140,26,304,97,224,392,260⟩,[⟨1,2178303536979063933501441,⟨501,369,476,508,304,369,500,476,388⟩⟩]⟩
theorem node794 : UpperPrefix a [2,4,7,1,8,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,7,1,8,0,5,3] 30 cert794 (by decide +kernel)

def cert795 : Leaf := ⟨⟨416,420,289,0,133,388,261,37,169⟩,[(3,1)],[(4,1,3),(6,7,6)],⟨7,19,140,26,304,97,224,448,268⟩,⟨7,19,140,26,304,97,224,448,260⟩,[⟨1,1267044503823039870271489,⟨501,241,476,508,496,241,224,448,388⟩⟩,⟨3,1212623794785285756366085,⟨103,243,247,242,499,97,242,499,503⟩⟩]⟩
theorem node795 : UpperPrefix a [2,4,7,1,8,0,5,6] 30 :=
  Boolean.leaf_sound a [2,4,7,1,8,0,5,6] 30 cert795 (by decide +kernel)

theorem node796 : UpperPrefix a [2,4,7,1,8,0,5] 30 :=
  branch_upper a [2,4,7,1,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,1,8,0,5,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,5,2] 30 (by decide +kernel))
  node794
  (invalid_upper a [2,4,7,1,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,5,5] 30 (by decide +kernel))
  node795
  (invalid_upper a [2,4,7,1,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,5,8] 30 (by decide +kernel)))

theorem node797 : UpperPrefix a [2,4,7,1,8,0] 30 :=
  branch_upper a [2,4,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,2] 30 (by decide +kernel))
  node793
  (invalid_upper a [2,4,7,1,8,0,4] 30 (by decide +kernel))
  node796
  (invalid_upper a [2,4,7,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,0,8] 30 (by decide +kernel)))

def cert798 : Leaf := ⟨⟨488,492,353,0,0,389,300,0,233⟩,[(3,1),(4,7),(7,4)],[(4,1,3)],⟨7,19,140,26,304,104,193,416,324⟩,⟨7,19,140,26,304,104,193,416,260⟩,[⟨1,1404278047740208692068353,⟨469,465,444,508,436,508,465,436,404⟩⟩]⟩
theorem node798 : UpperPrefix a [2,4,7,1,8,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,1,8,3,0,5] 30 cert798 (by decide +kernel)

def cert799 : Leaf := ⟨⟨328,332,321,0,77,261,268,13,105⟩,[(3,1)],[(4,1,3)],⟨7,19,140,26,304,104,193,448,292⟩,⟨7,19,140,26,304,104,193,448,260⟩,[⟨1,1493846213581309326917633,⟨469,465,444,508,436,508,193,448,276⟩⟩,⟨5,1212621473469952412890175,⟨79,223,207,223,479,79,193,448,453⟩⟩,⟨7,1227816446359146484444933,⟨287,27,319,26,315,106,123,379,287⟩⟩]⟩
theorem node799 : UpperPrefix a [2,4,7,1,8,3,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,1,8,3,0,6] 30 cert799 (by decide +kernel)

theorem node800 : UpperPrefix a [2,4,7,1,8,3,0] 30 :=
  branch_upper a [2,4,7,1,8,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,1,8,3,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,0,4] 30 (by decide +kernel))
  node798
  node799
  (invalid_upper a [2,4,7,1,8,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,0,8] 30 (by decide +kernel)))

def cert801 : Leaf := ⟨⟨456,460,321,0,204,388,268,77,201⟩,[(3,1)],[(4,1,3)],⟨7,19,140,26,304,104,224,449,325⟩,⟨7,19,140,26,304,104,224,384,260⟩,[⟨1,1214857836509885891608577,⟨501,465,236,252,304,108,224,400,372⟩⟩,⟨5,1664340190228978206782527,⟨15,31,143,31,415,463,453,384,261⟩⟩,⟨0,1210107637534960038970368,⟨110,58,236,26,304,104,224,400,372⟩⟩]⟩
theorem node801 : UpperPrefix a [2,4,7,1,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,1,8,3,5] 30 cert801 (by decide +kernel)

theorem node802 : UpperPrefix a [2,4,7,1,8,3] 30 :=
  branch_upper a [2,4,7,1,8,3] 30 (by decide) (fin9_cases _
  node800
  (invalid_upper a [2,4,7,1,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,4] 30 (by decide +kernel))
  node801
  (invalid_upper a [2,4,7,1,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,3,8] 30 (by decide +kernel)))

theorem node803 : UpperPrefix a [2,4,7,1,8] 30 :=
  branch_upper a [2,4,7,1,8] 30 (by decide) (fin9_cases _
  node797
  (invalid_upper a [2,4,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,2] 30 (by decide +kernel))
  node802
  (invalid_upper a [2,4,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,8,8] 30 (by decide +kernel)))

theorem node804 : UpperPrefix a [2,4,7,1] 30 :=
  branch_upper a [2,4,7,1] 30 (by decide) (fin9_cases _
  node778
  (invalid_upper a [2,4,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,2] 30 (by decide +kernel))
  node785
  (invalid_upper a [2,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,1,5] 30 (by decide +kernel))
  node792
  (invalid_upper a [2,4,7,1,7] 30 (by decide +kernel))
  node803)

def cert805 : Leaf := ⟨⟨472,0,320,0,462,396,268,76,200⟩,[(1,4),(3,4)],[(5,3,3),(0,4,1),(1,5,4)],⟨7,19,140,56,49,98,456,456,332⟩,⟨7,19,140,56,49,98,192,384,260⟩,[⟨4,1266886859749596662334465,⟨487,35,460,492,33,98,192,384,452⟩⟩]⟩
theorem node805 : UpperPrefix a [2,4,7,5,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,0,1] 30 cert805 (by decide +kernel)

def cert806 : Leaf := ⟨⟨216,0,82,0,206,150,278,86,210⟩,[(1,4),(3,4)],[(5,3,3),(0,4,1)],⟨7,19,140,56,49,104,450,450,326⟩,⟨7,19,140,56,49,104,192,384,260⟩,[⟨8,1181747928184199904613,⟨7,27,159,59,59,127,255,129,7⟩⟩,⟨3,1215005518108992178496513,⟨455,467,132,242,499,96,192,384,260⟩⟩]⟩
theorem node806 : UpperPrefix a [2,4,7,5,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,0,3] 30 cert806 (by decide +kernel)

def cert807 : Leaf := ⟨⟨464,0,338,0,454,150,276,94,218⟩,[(1,4),(3,4)],[(5,3,3),(0,4,1)],⟨7,19,140,56,49,352,194,456,332⟩,⟨7,19,140,56,49,352,194,384,260⟩,[⟨3,1210109956724114926563077,⟨87,19,247,50,51,371,242,499,375⟩⟩]⟩
theorem node807 : UpperPrefix a [2,4,7,5,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,0,8,1] 30 cert807 (by decide +kernel)

def cert808 : Local := ⟨⟨472,0,0,0,462,158,0,94,218⟩,[(1,4),(2,6),(3,4),(6,2)],[(5,3,3),(0,4,1)]⟩
theorem node808 : UpperPrefix a [2,4,7,5,0,8,3] 30 :=
  local_sound a [2,4,7,5,0,8,3] 30 cert808 (by decide +kernel)

theorem node809 : UpperPrefix a [2,4,7,5,0,8] 30 :=
  branch_upper a [2,4,7,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,0,8,0] 30 (by decide +kernel))
  node807
  (invalid_upper a [2,4,7,5,0,8,2] 30 (by decide +kernel))
  node808
  (invalid_upper a [2,4,7,5,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,8,8] 30 (by decide +kernel)))

theorem node810 : UpperPrefix a [2,4,7,5,0] 30 :=
  branch_upper a [2,4,7,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,0,0] 30 (by decide +kernel))
  node805
  (invalid_upper a [2,4,7,5,0,2] 30 (by decide +kernel))
  node806
  (invalid_upper a [2,4,7,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,0,7] 30 (by decide +kernel))
  node809)

def cert811 : Leaf := ⟨⟨216,204,64,0,205,140,268,76,200⟩,[(3,4)],[(5,3,3),(1,4,1),(0,5,4)],⟨7,19,140,56,50,97,456,456,332⟩,⟨7,19,140,56,50,97,192,384,260⟩,[⟨4,1266886859749596662334465,⟨487,35,460,492,34,97,192,384,452⟩⟩,⟨8,1181747928184199904613,⟨7,27,159,59,59,127,255,129,7⟩⟩]⟩
theorem node811 : UpperPrefix a [2,4,7,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,0] 30 cert811 (by decide +kernel)

def cert812 : Leaf := ⟨⟨200,204,65,0,205,133,269,77,201⟩,[(3,4)],[(5,3,3),(1,4,1)],⟨7,19,140,56,50,104,449,449,325⟩,⟨7,19,140,56,50,104,192,384,260⟩,[⟨4,1328416245210460615345169,⟨487,451,492,493,487,492,192,384,292⟩⟩,⟨8,1181747928184199904613,⟨7,27,159,59,59,127,255,129,7⟩⟩]⟩
theorem node812 : UpperPrefix a [2,4,7,5,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,3] 30 cert812 (by decide +kernel)

def cert813 : Leaf := ⟨⟨144,132,337,0,133,157,29,93,217⟩,[(3,4)],[(5,3,3),(1,4,1)],⟨7,19,140,56,50,352,201,457,333⟩,⟨7,19,140,56,50,352,192,384,260⟩,[⟨8,1181817729571770879237,⟨71,27,223,58,58,123,192,129,71⟩⟩,⟨3,1210107565286599391464709,⟨7,19,151,50,50,371,192,385,263⟩⟩,⟨6,1210106412365102300810501,⟨7,27,159,58,58,315,128,385,263⟩⟩]⟩
theorem node813 : UpperPrefix a [2,4,7,5,1,8] 30 :=
  Boolean.leaf_sound a [2,4,7,5,1,8] 30 cert813 (by decide +kernel)

theorem node814 : UpperPrefix a [2,4,7,5,1] 30 :=
  branch_upper a [2,4,7,5,1] 30 (by decide) (fin9_cases _
  node811
  (invalid_upper a [2,4,7,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,2] 30 (by decide +kernel))
  node812
  (invalid_upper a [2,4,7,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,1,7] 30 (by decide +kernel))
  node813)

def cert815 : Leaf := ⟨⟨408,396,339,0,0,391,263,71,195⟩,[(3,4),(4,3)],[(5,3,3),(5,3,4)],⟨7,19,140,56,56,355,451,451,327⟩,⟨7,19,140,56,56,96,192,384,260⟩,[⟨3,1214857656031579466630145,⟨487,499,132,48,48,96,192,384,260⟩⟩,⟨4,1214857656030481028744193,⟨487,483,140,40,40,96,192,384,260⟩⟩,⟨6,1210106412365102300794117,⟨7,27,159,56,56,56,128,385,263⟩⟩]⟩
theorem node815 : UpperPrefix a [2,4,7,5,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,3] 30 cert815 (by decide +kernel)

def cert816 : Leaf := ⟨⟨408,396,274,0,0,414,286,30,154⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,140,56,112,97,458,394,270⟩,⟨7,19,140,56,112,97,192,384,260⟩,[⟨0,1219570781024667171292160,⟨454,478,140,56,120,120,192,384,260⟩⟩]⟩
theorem node816 : UpperPrefix a [2,4,7,5,6,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,0] 30 cert816 (by decide +kernel)

def cert817 : Leaf := ⟨⟨408,396,273,0,0,413,285,29,153⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,140,56,112,98,457,393,269⟩,⟨7,19,140,56,112,98,192,384,260⟩,[⟨1,1219570781024667179679745,⟨453,477,140,60,124,508,192,384,260⟩⟩]⟩
theorem node817 : UpperPrefix a [2,4,7,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,1] 30 cert817 (by decide +kernel)

def cert818 : Leaf := ⟨⟨152,140,19,0,0,151,287,31,155⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,140,56,112,104,451,387,263⟩,⟨7,19,140,56,112,104,192,384,260⟩,[⟨8,1181748490584665945205,⟨15,59,143,59,127,127,255,128,5⟩⟩]⟩
theorem node818 : UpperPrefix a [2,4,7,5,6,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,3] 30 cert818 (by decide +kernel)

def cert819 : Leaf := ⟨⟨400,388,275,0,0,151,278,31,155⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,140,56,112,352,193,394,270⟩,⟨7,19,140,56,112,352,193,384,260⟩,[⟨3,1210109956728512973098757,⟨87,19,247,50,114,371,243,499,375⟩⟩]⟩
theorem node819 : UpperPrefix a [2,4,7,5,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,0] 30 cert819 (by decide +kernel)

def cert820 : Leaf := ⟨⟨408,396,273,0,0,157,285,29,153⟩,[(3,4),(4,5)],[(5,3,3),(6,4,3),(6,4,4)],⟨7,19,140,56,112,352,194,393,269⟩,⟨7,19,140,56,112,352,194,384,260⟩,[⟨1,1219570747252076619235329,⟨389,413,140,56,124,380,508,384,260⟩⟩]⟩
theorem node820 : UpperPrefix a [2,4,7,5,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,6,8,1] 30 cert820 (by decide +kernel)

def cert821 : Local := ⟨⟨408,396,0,0,0,159,0,31,155⟩,[(2,6),(3,4),(4,5),(6,2)],[(5,3,3),(6,4,3),(6,4,4)]⟩
theorem node821 : UpperPrefix a [2,4,7,5,6,8,3] 30 :=
  local_sound a [2,4,7,5,6,8,3] 30 cert821 (by decide +kernel)

theorem node822 : UpperPrefix a [2,4,7,5,6,8] 30 :=
  branch_upper a [2,4,7,5,6,8] 30 (by decide) (fin9_cases _
  node819
  node820
  (invalid_upper a [2,4,7,5,6,8,2] 30 (by decide +kernel))
  node821
  (invalid_upper a [2,4,7,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,8,8] 30 (by decide +kernel)))

theorem node823 : UpperPrefix a [2,4,7,5,6] 30 :=
  branch_upper a [2,4,7,5,6] 30 (by decide) (fin9_cases _
  node816
  node817
  (invalid_upper a [2,4,7,5,6,2] 30 (by decide +kernel))
  node818
  (invalid_upper a [2,4,7,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,6,7] 30 (by decide +kernel))
  node822)

def cert824 : Leaf := ⟨⟨464,452,336,0,196,406,276,92,216⟩,[(3,4)],[(5,3,3),(1,6,5)],⟨7,19,140,56,304,97,194,456,332⟩,⟨7,19,140,56,304,97,194,384,260⟩,[⟨0,1370981674396623450932224,⟨454,478,156,444,444,508,454,384,260⟩⟩,⟨3,1210109956897562885827845,⟨103,51,247,50,307,97,242,499,375⟩⟩]⟩
theorem node824 : UpperPrefix a [2,4,7,5,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,0,1] 30 cert824 (by decide +kernel)

def cert825 : Leaf := ⟨⟨472,460,0,0,206,398,0,78,202⟩,[(2,6),(3,4),(6,2)],[(5,3,3)],⟨7,19,140,56,304,97,200,450,326⟩,⟨7,19,140,56,304,97,200,384,260⟩,[⟨0,1224303019397920037798912,⟨454,478,204,124,380,508,204,384,324⟩⟩,⟨4,1214839227230437101274113,⟨487,419,204,40,288,485,204,384,324⟩⟩]⟩
theorem node825 : UpperPrefix a [2,4,7,5,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,0,3] 30 cert825 (by decide +kernel)

theorem node826 : UpperPrefix a [2,4,7,5,8,0] 30 :=
  branch_upper a [2,4,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,8,0,0] 30 (by decide +kernel))
  node824
  (invalid_upper a [2,4,7,5,8,0,2] 30 (by decide +kernel))
  node825
  (invalid_upper a [2,4,7,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,0,8] 30 (by decide +kernel)))

def cert827 : Leaf := ⟨⟨464,452,336,0,196,405,276,92,216⟩,[(3,4)],[(5,3,3),(0,6,5)],⟨7,19,140,56,304,98,193,456,332⟩,⟨7,19,140,56,304,98,193,384,260⟩,[⟨1,1370981674396623450931201,⟨453,477,156,444,444,508,193,384,260⟩⟩,⟨3,1210109959149362699545861,⟨103,51,247,50,307,98,243,499,375⟩⟩]⟩
theorem node827 : UpperPrefix a [2,4,7,5,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,1,0] 30 cert827 (by decide +kernel)

def cert828 : Leaf := ⟨⟨456,460,0,0,207,397,0,79,203⟩,[(2,6),(3,4),(6,2)],[(5,3,3)],⟨7,19,140,56,304,98,200,449,325⟩,⟨7,19,140,56,304,98,200,384,260⟩,[⟨4,1404102965541885178807329,⟨487,419,460,493,417,487,460,384,324⟩⟩]⟩
theorem node828 : UpperPrefix a [2,4,7,5,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,1,3] 30 cert828 (by decide +kernel)

theorem node829 : UpperPrefix a [2,4,7,5,8,1] 30 :=
  branch_upper a [2,4,7,5,8,1] 30 (by decide) (fin9_cases _
  node827
  (invalid_upper a [2,4,7,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,2] 30 (by decide +kernel))
  node828
  (invalid_upper a [2,4,7,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,1,8] 30 (by decide +kernel)))

def cert830 : Leaf := ⟨⟨152,396,16,0,204,148,30,29,216⟩,[(3,4)],[(5,3,3),(1,7,6)],⟨7,19,140,56,304,104,193,386,324⟩,⟨7,19,140,56,304,104,193,386,260⟩,[⟨0,1663454749898299315061760,⟨6,26,156,312,312,380,508,386,260⟩⟩,⟨6,1210253986314938909996223,⟨7,159,143,191,447,47,129,391,261⟩⟩,⟨8,1184128249349700322433,⟨111,59,237,56,56,104,229,239,100⟩⟩]⟩
theorem node830 : UpperPrefix a [2,4,7,5,8,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,3,0,1] 30 cert830 (by decide +kernel)

def cert831 : Leaf := ⟨⟨344,332,322,0,78,278,270,14,74⟩,[(3,4)],[(5,3,3)],⟨7,19,140,56,304,104,193,448,262⟩,⟨7,19,140,56,304,104,193,448,260⟩,[⟨0,1215420234345706425418752,⟨270,282,188,60,316,252,508,508,268⟩⟩,⟨7,1232538812846383708745477,⟨287,283,319,58,315,122,379,379,287⟩⟩,⟨4,1215447951735286626518017,⟨455,451,140,44,292,236,449,448,260⟩⟩]⟩
theorem node831 : UpperPrefix a [2,4,7,5,8,3,0,6] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,3,0,6] 30 cert831 (by decide +kernel)

#print axioms node831
end Delivery.FiniteExclusion.Sharp2x7
