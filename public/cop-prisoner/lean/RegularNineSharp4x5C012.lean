import RegularNineSharp4x5Base
import RegularNineSharp4x5C011
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
theorem node768 : UpperPrefix a [3,4,7,5,2,8,1] 30 :=
  branch_upper a [3,4,7,5,2,8,1] 30 (by decide) (fin9_cases _
  node766
  (invalid_upper a [3,4,7,5,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,1,5] 30 (by decide +kernel))
  node767
  (invalid_upper a [3,4,7,5,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,1,8] 30 (by decide +kernel)))

theorem node769 : UpperPrefix a [3,4,7,5,2,8] 30 :=
  branch_upper a [3,4,7,5,2,8] 30 (by decide) (fin9_cases _
  node765
  node768
  (invalid_upper a [3,4,7,5,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,8] 30 (by decide +kernel)))

theorem node770 : UpperPrefix a [3,4,7,5,2] 30 :=
  branch_upper a [3,4,7,5,2] 30 (by decide) (fin9_cases _
  node761
  node762
  (invalid_upper a [3,4,7,5,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,7] 30 (by decide +kernel))
  node769)

def cert771 : Leaf := ⟨⟨436,424,274,0,0,406,278,22,134⟩,[(3,5),(4,5)],[(6,4,4),(0,5,3)],⟨11,22,140,41,112,97,454,390,278⟩,⟨11,22,140,41,112,97,192,384,272⟩,[⟨3,1219570781059912746140673,⟨499,470,132,49,112,113,192,384,272⟩⟩,⟨5,1219580021282997164835841,⟨463,470,140,205,80,197,192,384,272⟩⟩]⟩
theorem node771 : UpperPrefix a [3,4,7,5,6,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,6,0] 30 cert771 (by decide +kernel)

def cert772 : Leaf := ⟨⟨32,169,49,2,0,157,317,61,45⟩,[(4,5)],[(6,4,4),(1,5,3)],⟨11,22,140,41,112,98,453,389,277⟩,⟨11,22,140,41,112,98,192,384,272⟩,[⟨8,1181748490619059234171,⟨11,63,141,59,127,127,255,141,59⟩⟩,⟨7,1218371706631079030948899,⟨267,287,12,57,121,379,64,256,280⟩⟩,⟨2,1210107565286057150776355,⟨11,27,136,57,121,123,192,384,280⟩⟩,⟨4,1210107565282758616941603,⟨11,15,140,41,105,107,192,384,264⟩⟩]⟩
theorem node772 : UpperPrefix a [3,4,7,5,6,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,6,1] 30 cert772 (by decide +kernel)

def cert773 : Leaf := ⟨⟨52,33,51,22,0,147,307,51,35⟩,[(4,5)],[(7,2,5),(6,4,4)],⟨11,22,140,41,112,100,451,387,275⟩,⟨11,22,140,41,112,100,192,384,272⟩,[⟨3,1252692036251356842970113,⟨467,54,502,499,114,118,192,384,272⟩⟩,⟨8,1181748490619059234171,⟨11,63,141,59,127,127,255,141,59⟩⟩,⟨2,1214839173155905473610753,⟨475,18,152,505,112,112,192,384,272⟩⟩]⟩
theorem node773 : UpperPrefix a [3,4,7,5,6,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,6,2] 30 cert773 (by decide +kernel)

def cert774 : Leaf := ⟨⟨436,416,274,406,0,150,278,22,134⟩,[(4,5)],[(6,4,4)],⟨11,22,140,41,112,352,193,390,278⟩,⟨11,22,140,41,112,352,193,384,272⟩,[⟨0,1560291334228463798490112,⟨398,438,398,446,498,498,502,384,304⟩⟩,⟨3,1238497122470088038943745,⟨499,406,406,113,112,368,241,384,272⟩⟩,⟨5,1219580129369388221727745,⟨463,406,204,205,80,320,197,384,272⟩⟩]⟩
theorem node774 : UpperPrefix a [3,4,7,5,6,8,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,6,8,0] 30 cert774 (by decide +kernel)

def cert775 : Leaf := ⟨⟨436,416,305,406,0,148,308,52,164⟩,[(4,5)],[(6,4,4),(0,7,2)],⟨11,22,140,41,112,352,194,385,276⟩,⟨11,22,140,41,112,352,194,385,272⟩,[⟨3,1238451084643211886464001,⟨499,374,502,241,112,368,498,497,272⟩⟩,⟨1,1257414242719276717047809,⟨397,276,396,445,112,368,496,389,272⟩⟩]⟩
theorem node775 : UpperPrefix a [3,4,7,5,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,6,8,1,0] 30 cert775 (by decide +kernel)

def cert776 : Leaf := ⟨⟨304,417,307,274,0,19,309,51,35⟩,[(4,5)],[(6,4,4),(2,7,6)],⟨11,22,140,41,112,352,194,388,273⟩,⟨11,22,140,41,112,352,194,388,272⟩,[⟨3,1252648175742620795997185,⟨371,246,502,305,112,368,242,502,272⟩⟩,⟨7,1785055687394593128580163,⟨267,319,268,313,377,377,379,260,312⟩⟩]⟩
theorem node776 : UpperPrefix a [3,4,7,5,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,6,8,1,2] 30 cert776 (by decide +kernel)

theorem node777 : UpperPrefix a [3,4,7,5,6,8,1] 30 :=
  branch_upper a [3,4,7,5,6,8,1] 30 (by decide) (fin9_cases _
  node775
  (invalid_upper a [3,4,7,5,6,8,1,1] 30 (by decide +kernel))
  node776
  (invalid_upper a [3,4,7,5,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,1,8] 30 (by decide +kernel)))

def cert778 : Local := ⟨⟨308,296,307,278,0,30,0,62,46⟩,[(4,5),(6,2)],[(7,2,6),(6,4,4),(0,7,2)]⟩
theorem node778 : UpperPrefix a [3,4,7,5,6,8,2,0] 30 :=
  local_sound a [3,4,7,5,6,8,2,0] 30 cert778 (by decide +kernel)

def cert779 : Local := ⟨⟨292,297,291,262,0,15,0,61,47⟩,[(4,5),(6,2)],[(4,1,7),(7,2,6),(6,4,4)]⟩
theorem node779 : UpperPrefix a [3,4,7,5,6,8,2,1] 30 :=
  local_sound a [3,4,7,5,6,8,2,1] 30 cert779 (by decide +kernel)

theorem node780 : UpperPrefix a [3,4,7,5,6,8,2] 30 :=
  branch_upper a [3,4,7,5,6,8,2] 30 (by decide) (fin9_cases _
  node778
  node779
  (invalid_upper a [3,4,7,5,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,2,8] 30 (by decide +kernel)))

theorem node781 : UpperPrefix a [3,4,7,5,6,8] 30 :=
  branch_upper a [3,4,7,5,6,8] 30 (by decide) (fin9_cases _
  node774
  node777
  node780
  (invalid_upper a [3,4,7,5,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,8,8] 30 (by decide +kernel)))

theorem node782 : UpperPrefix a [3,4,7,5,6] 30 :=
  branch_upper a [3,4,7,5,6] 30 (by decide) (fin9_cases _
  node771
  node772
  node773
  (invalid_upper a [3,4,7,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,6,7] 30 (by decide +kernel))
  node781)

def cert783 : Leaf := ⟨⟨500,480,336,0,196,406,276,84,196⟩,[(3,5)],[(0,5,3),(1,6,5)],⟨11,22,140,41,304,97,194,452,340⟩,⟨11,22,140,41,304,97,194,384,272⟩,[⟨3,1238497230831082124872705,⟨499,470,502,113,304,113,450,384,272⟩⟩,⟨5,1219580021282997164835841,⟨463,470,140,205,272,197,450,384,272⟩⟩]⟩
theorem node783 : UpperPrefix a [3,4,7,5,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,0,1] 30 cert783 (by decide +kernel)

def cert784 : Leaf := ⟨⟨372,352,370,0,70,278,0,118,102⟩,[(3,5),(6,2)],[(7,2,6),(0,5,3)],⟨11,22,140,41,304,97,196,450,338⟩,⟨11,22,140,41,304,97,196,384,272⟩,[⟨3,1243819098202947745483777,⟨499,470,470,433,304,497,454,384,272⟩⟩]⟩
theorem node784 : UpperPrefix a [3,4,7,5,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,0,2] 30 cert784 (by decide +kernel)

theorem node785 : UpperPrefix a [3,4,7,5,8,0] 30 :=
  branch_upper a [3,4,7,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,8,0,0] 30 (by decide +kernel))
  node783
  node784
  (invalid_upper a [3,4,7,5,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,0,8] 30 (by decide +kernel)))

def cert786 : Leaf := ⟨⟨292,296,288,262,76,396,300,40,108⟩,[],[(1,5,3)],⟨11,22,140,41,304,98,193,388,336⟩,⟨11,22,140,41,304,98,193,388,272⟩,[⟨0,1664118832684937812155904,⟨158,22,158,446,304,498,502,390,272⟩⟩,⟨4,1212616646841518484096035,⟨111,239,140,41,493,111,237,388,460⟩⟩,⟨6,1212615169556378092709171,⟨15,159,140,41,447,47,129,391,415⟩⟩,⟨7,1360042701117718143175719,⟨27,31,31,313,313,379,65,263,280⟩⟩]⟩
theorem node786 : UpperPrefix a [3,4,7,5,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,1,0,2] 30 cert786 (by decide +kernel)

def cert787 : Leaf := ⟨⟨480,480,352,450,196,384,288,32,228⟩,[],[(1,5,3)],⟨11,22,140,41,304,98,193,448,276⟩,⟨11,22,140,41,304,98,193,448,272⟩,[⟨0,1281828508510177157193216,⟨286,278,414,446,432,498,498,496,272⟩⟩,⟨3,1238783191254620615740417,⟨499,438,502,241,432,498,241,448,272⟩⟩,⟨4,1212616646841518517650467,⟨111,239,140,41,493,111,237,460,460⟩⟩,⟨2,1212616646842617906070563,⟨107,251,136,41,505,107,233,456,472⟩⟩]⟩
theorem node787 : UpperPrefix a [3,4,7,5,8,1,0,6] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,1,0,6] 30 cert787 (by decide +kernel)

theorem node788 : UpperPrefix a [3,4,7,5,8,1,0] 30 :=
  branch_upper a [3,4,7,5,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,0,1] 30 (by decide +kernel))
  node786
  (invalid_upper a [3,4,7,5,8,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,0,5] 30 (by decide +kernel))
  node787
  (invalid_upper a [3,4,7,5,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,0,8] 30 (by decide +kernel)))

def cert789 : Leaf := ⟨⟨352,361,353,322,73,269,0,105,105⟩,[(6,2)],[(7,2,6),(1,5,3),(2,6,5)],⟨11,22,140,41,304,98,196,449,337⟩,⟨11,22,140,41,304,98,196,384,272⟩,[⟨4,1210262453186696733787171,⟨111,239,204,41,493,111,196,452,460⟩⟩]⟩
theorem node789 : UpperPrefix a [3,4,7,5,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,1,2] 30 cert789 (by decide +kernel)

theorem node790 : UpperPrefix a [3,4,7,5,8,1] 30 :=
  branch_upper a [3,4,7,5,8,1] 30 (by decide) (fin9_cases _
  node788
  (invalid_upper a [3,4,7,5,8,1,1] 30 (by decide +kernel))
  node789
  (invalid_upper a [3,4,7,5,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,1,8] 30 (by decide +kernel)))

def cert791 : Leaf := ⟨⟨372,352,352,324,66,385,306,114,98⟩,[],[(7,2,5)],⟨11,22,140,41,304,100,193,450,338⟩,⟨11,22,140,41,304,100,193,384,272⟩,[⟨3,1423029271028128281545729,⟨467,438,502,499,434,502,449,384,272⟩⟩,⟨0,1361518440643608466972160,⟨30,22,158,446,434,502,194,384,272⟩⟩,⟨2,1214839317268894526211073,⟨475,18,216,505,304,96,449,384,272⟩⟩,⟨1,1210107567535660106514433,⟨9,20,140,41,304,108,237,384,272⟩⟩,⟨4,1210107567534560594887681,⟨11,6,140,41,288,108,237,384,256⟩⟩]⟩
theorem node791 : UpperPrefix a [3,4,7,5,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,2,0] 30 cert791 (by decide +kernel)

def cert792 : Leaf := ⟨⟨308,288,305,278,68,402,308,52,100⟩,[],[(7,2,5),(0,7,2)],⟨11,22,140,41,304,100,194,385,336⟩,⟨11,22,140,41,304,100,194,385,272⟩,[⟨3,2338836399443942229167105,⟨499,374,502,499,306,374,498,465,272⟩⟩,⟨6,1212615169556373797741843,⟨15,159,140,41,447,36,135,391,415⟩⟩,⟨1,1361297079714723952590849,⟨157,20,156,445,304,372,192,389,272⟩⟩]⟩
theorem node792 : UpperPrefix a [3,4,7,5,8,2,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,2,1,0] 30 cert792 (by decide +kernel)

def cert793 : Leaf := ⟨⟨36,289,99,6,3,131,305,51,35⟩,[],[(7,2,5)],⟨11,22,140,41,304,100,194,448,273⟩,⟨11,22,140,41,304,100,194,448,272⟩,[⟨3,1255238659779286713519105,⟨499,246,502,499,498,246,226,448,464⟩⟩,⟨6,1507615500785889949273151,⟨283,287,415,315,315,319,387,384,281⟩⟩,⟨2,1252691891992958450271233,⟨475,18,408,505,304,96,194,448,272⟩⟩,⟨4,1210107572038181730649153,⟨11,6,172,41,296,109,239,493,256⟩⟩,⟨8,1181752424652067570753,⟨11,22,172,41,56,109,239,237,16⟩⟩]⟩
theorem node793 : UpperPrefix a [3,4,7,5,8,2,1,6] 30 :=
  Boolean.leaf_sound a [3,4,7,5,8,2,1,6] 30 cert793 (by decide +kernel)

theorem node794 : UpperPrefix a [3,4,7,5,8,2,1] 30 :=
  branch_upper a [3,4,7,5,8,2,1] 30 (by decide) (fin9_cases _
  node792
  (invalid_upper a [3,4,7,5,8,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,1,5] 30 (by decide +kernel))
  node793
  (invalid_upper a [3,4,7,5,8,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,1,8] 30 (by decide +kernel)))

theorem node795 : UpperPrefix a [3,4,7,5,8,2] 30 :=
  branch_upper a [3,4,7,5,8,2] 30 (by decide) (fin9_cases _
  node791
  node794
  (invalid_upper a [3,4,7,5,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,2,8] 30 (by decide +kernel)))

theorem node796 : UpperPrefix a [3,4,7,5,8] 30 :=
  branch_upper a [3,4,7,5,8] 30 (by decide) (fin9_cases _
  node785
  node790
  node795
  (invalid_upper a [3,4,7,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,8,8] 30 (by decide +kernel)))

theorem node797 : UpperPrefix a [3,4,7,5] 30 :=
  branch_upper a [3,4,7,5] 30 (by decide) (fin9_cases _
  node749
  node760
  node770
  (invalid_upper a [3,4,7,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,5] 30 (by decide +kernel))
  node782
  (invalid_upper a [3,4,7,5,7] 30 (by decide +kernel))
  node796)

def cert798 : Leaf := ⟨⟨112,224,112,48,66,148,308,116,228⟩,[],[(1,5,4)],⟨11,22,140,73,49,98,484,420,308⟩,⟨11,22,140,73,49,98,192,384,272⟩,[⟨0,1295285757993479547659264,⟨494,502,140,236,502,482,192,416,498⟩⟩,⟨3,1238497212746589749120001,⟨499,502,502,113,49,482,192,384,272⟩⟩,⟨8,1181748210000626506877,⟨59,23,191,127,59,127,255,128,17⟩⟩,⟨2,1210107565286055003292705,⟨11,18,136,73,57,123,192,384,272⟩⟩,⟨7,1208926973665337593037857,⟨11,22,12,73,57,123,64,256,272⟩⟩]⟩
theorem node798 : UpperPrefix a [3,4,7,6,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,1] 30 cert798 (by decide +kernel)

def cert799 : Leaf := ⟨⟨112,104,112,50,72,152,56,120,104⟩,[],[(7,2,5),(1,6,3)],⟨11,22,140,73,49,100,194,416,304⟩,⟨11,22,140,73,49,100,194,384,272⟩,[⟨8,1184130834261288803583,⟨59,127,255,127,59,127,255,255,17⟩⟩,⟨0,1298241840005567225275392,⟨494,502,172,236,502,228,482,448,498⟩⟩,⟨2,1437223914350373014340675,⟨75,475,136,73,441,505,203,384,400⟩⟩]⟩
theorem node799 : UpperPrefix a [3,4,7,6,0,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,2,1] 30 cert799 (by decide +kernel)

def cert800 : Leaf := ⟨⟨112,104,114,50,70,146,18,114,98⟩,[],[(7,2,5)],⟨11,22,140,73,49,100,224,386,274⟩,⟨11,22,140,73,49,100,224,384,272⟩,[⟨8,1184130834261288803583,⟨59,127,255,127,59,127,255,255,17⟩⟩,⟨0,1297651760508728121762816,⟨494,502,236,236,502,100,224,448,498⟩⟩,⟨2,1219580256596080107455491,⟨395,475,136,201,249,96,224,384,344⟩⟩,⟨3,1224302749390910782440449,⟨499,502,228,465,497,100,224,384,336⟩⟩]⟩
theorem node800 : UpperPrefix a [3,4,7,6,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,2,5] 30 cert800 (by decide +kernel)

def cert801 : Leaf := ⟨⟨116,104,114,54,70,146,0,118,102⟩,[(6,7)],[(7,2,5),(8,6,6)],⟨11,22,140,73,49,100,448,418,306⟩,⟨11,22,140,73,49,100,448,384,272⟩,[⟨0,1297653850178955221672960,⟨494,502,236,236,502,100,448,448,498⟩⟩,⟨3,1224305127291514034062337,⟨499,502,228,465,497,100,448,448,336⟩⟩]⟩
theorem node801 : UpperPrefix a [3,4,7,6,0,2,8] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,2,8] 30 cert801 (by decide +kernel)

theorem node802 : UpperPrefix a [3,4,7,6,0,2] 30 :=
  branch_upper a [3,4,7,6,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,0,2,0] 30 (by decide +kernel))
  node799
  (invalid_upper a [3,4,7,6,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,2,4] 30 (by decide +kernel))
  node800
  (invalid_upper a [3,4,7,6,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,2,7] 30 (by decide +kernel))
  node801)

def cert803 : Leaf := ⟨⟨228,224,96,166,196,148,308,100,228⟩,[],[(1,6,3)],⟨11,22,140,73,49,352,194,420,308⟩,⟨11,22,140,73,49,352,194,384,272⟩,[⟨0,1295290376434897416102912,⟨494,502,172,236,502,352,482,480,498⟩⟩,⟨3,1238497233012788072287233,⟨499,502,502,113,113,352,482,384,272⟩⟩,⟨8,1181745671434436363377,⟨11,23,140,77,59,127,207,128,17⟩⟩,⟨4,1210402713187944441578561,⟨11,6,140,77,173,493,207,384,260⟩⟩]⟩
theorem node803 : UpperPrefix a [3,4,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,8,1] 30 cert803 (by decide +kernel)

def cert804 : Leaf := ⟨⟨372,352,370,310,322,18,0,114,98⟩,[(6,2)],[(7,2,6)],⟨11,22,140,73,49,352,196,418,306⟩,⟨11,22,140,73,49,352,196,384,272⟩,[⟨0,1297647157407696484049920,⟨494,502,204,236,502,480,196,416,498⟩⟩,⟨3,1243819100945129745157121,⟨499,502,502,497,433,480,486,384,272⟩⟩,⟨2,1214839155420851637060609,⟨443,18,184,505,433,352,192,384,272⟩⟩]⟩
theorem node804 : UpperPrefix a [3,4,7,6,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,8,2] 30 cert804 (by decide +kernel)

def cert805 : Leaf := ⟨⟨208,192,82,146,198,146,274,86,198⟩,[],[(8,5,6)],⟨11,22,140,73,49,352,224,390,278⟩,⟨11,22,140,73,49,352,224,384,272⟩,[⟨0,1295292896198888929895424,⟨494,502,236,236,502,352,224,480,498⟩⟩,⟨3,1238499541107597099666433,⟨499,502,502,113,113,352,224,480,272⟩⟩,⟨5,1297941736064932726055985,⟨399,407,140,205,415,463,205,386,407⟩⟩,⟨2,1210109947688054832497667,⟨11,91,232,73,49,352,224,480,272⟩⟩]⟩
theorem node805 : UpperPrefix a [3,4,7,6,0,8,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,0,8,5] 30 cert805 (by decide +kernel)

theorem node806 : UpperPrefix a [3,4,7,6,0,8] 30 :=
  branch_upper a [3,4,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,0,8,0] 30 (by decide +kernel))
  node803
  node804
  (invalid_upper a [3,4,7,6,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,4] 30 (by decide +kernel))
  node805
  (invalid_upper a [3,4,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,8,8] 30 (by decide +kernel)))

theorem node807 : UpperPrefix a [3,4,7,6,0] 30 :=
  branch_upper a [3,4,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,0,0] 30 (by decide +kernel))
  node798
  node802
  (invalid_upper a [3,4,7,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,0,7] 30 (by decide +kernel))
  node806)

def cert808 : Leaf := ⟨⟨356,353,353,0,325,0,293,101,101⟩,[(3,5),(5,3)],[],⟨11,22,140,73,50,97,484,420,308⟩,⟨11,22,140,73,50,97,192,384,272⟩,[⟨3,1229033997042889224358913,⟨51,470,502,113,50,113,192,384,272⟩⟩,⟨1,1285813291474211113533441,⟨41,468,172,105,508,105,192,384,468⟩⟩,⟨4,1212475675341927624999953,⟨43,7,236,105,43,105,196,492,493⟩⟩,⟨7,1227816439876435724733461,⟨59,279,319,121,59,121,64,256,273⟩⟩]⟩
theorem node808 : UpperPrefix a [3,4,7,6,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,0] 30 cert808 (by decide +kernel)

def cert809 : Leaf := ⟨⟨112,104,114,0,76,154,58,122,106⟩,[(3,6)],[(7,2,5),(2,5,4),(0,6,3)],⟨11,22,140,73,50,100,193,416,304⟩,⟨11,22,140,73,50,100,193,384,272⟩,[⟨8,1184130834261288803583,⟨59,127,255,127,59,127,255,255,17⟩⟩]⟩
theorem node809 : UpperPrefix a [3,4,7,6,1,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,2,0] 30 cert809 (by decide +kernel)

def cert810 : Leaf := ⟨⟨96,97,99,34,69,131,3,99,99⟩,[],[(7,2,5),(2,5,4)],⟨11,22,140,73,50,100,224,385,273⟩,⟨11,22,140,73,50,100,224,384,272⟩,[⟨8,1184130834261288803583,⟨59,127,255,127,59,127,255,255,17⟩⟩,⟨3,1252691964268185998347265,⟨499,118,502,465,50,118,242,384,272⟩⟩,⟨4,1212475754084548333274131,⟨43,111,236,105,43,100,228,492,493⟩⟩]⟩
theorem node810 : UpperPrefix a [3,4,7,6,1,2,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,2,5] 30 cert810 (by decide +kernel)

def cert811 : Leaf := ⟨⟨112,96,115,50,68,146,0,123,107⟩,[(6,7)],[(7,2,5),(2,5,4),(8,6,6)],⟨11,22,140,73,50,100,448,417,305⟩,⟨11,22,140,73,50,100,448,384,272⟩,[⟨0,1210109871270209728302080,⟨26,54,254,72,50,118,448,448,272⟩⟩,⟨3,1210109871270208654560257,⟨19,54,246,65,50,118,448,448,272⟩⟩]⟩
theorem node811 : UpperPrefix a [3,4,7,6,1,2,8] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,2,8] 30 cert811 (by decide +kernel)

theorem node812 : UpperPrefix a [3,4,7,6,1,2] 30 :=
  branch_upper a [3,4,7,6,1,2] 30 (by decide) (fin9_cases _
  node809
  (invalid_upper a [3,4,7,6,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,2,4] 30 (by decide +kernel))
  node810
  (invalid_upper a [3,4,7,6,1,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,2,7] 30 (by decide +kernel))
  node811)

def cert813 : Leaf := ⟨⟨452,448,322,0,452,134,262,66,230⟩,[(3,6)],[(0,6,3)],⟨11,22,140,73,50,352,193,388,304⟩,⟨11,22,140,73,50,352,193,388,272⟩,[⟨3,1800458736462376708672513,⟨499,406,438,369,434,368,499,406,272⟩⟩,⟨4,1212768809856605306749971,⟨11,79,172,77,239,492,237,492,493⟩⟩,⟨5,1212771749582383596316083,⟨11,95,205,77,223,463,205,463,479⟩⟩]⟩
theorem node813 : UpperPrefix a [3,4,7,6,1,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,8,0,2] 30 cert813 (by decide +kernel)

def cert814 : Leaf := ⟨⟨244,224,114,0,196,150,54,0,230⟩,[(3,6),(7,5)],[(8,5,7),(0,6,3)],⟨11,22,140,73,50,352,193,416,276⟩,⟨11,22,140,73,50,352,193,416,272⟩,[⟨3,1238949211949084978449409,⟨499,438,502,241,434,480,241,416,400⟩⟩]⟩
theorem node814 : UpperPrefix a [3,4,7,6,1,8,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,8,0,5] 30 cert814 (by decide +kernel)

theorem node815 : UpperPrefix a [3,4,7,6,1,8,0] 30 :=
  branch_upper a [3,4,7,6,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,0,1] 30 (by decide +kernel))
  node813
  (invalid_upper a [3,4,7,6,1,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,0,4] 30 (by decide +kernel))
  node814
  (invalid_upper a [3,4,7,6,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,0,8] 30 (by decide +kernel)))

def cert816 : Leaf := ⟨⟨356,353,355,294,321,3,0,99,99⟩,[(6,2)],[(7,2,6)],⟨11,22,140,73,50,352,196,417,305⟩,⟨11,22,140,73,50,352,196,384,272⟩,[⟨3,1252691946465443477228545,⟨435,118,502,499,50,370,246,384,272⟩⟩,⟨4,1212476328082396746351635,⟨11,79,236,73,111,492,228,492,493⟩⟩,⟨2,1252691874259553881162753,⟨443,18,424,505,50,352,192,384,272⟩⟩]⟩
theorem node816 : UpperPrefix a [3,4,7,6,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,8,2] 30 cert816 (by decide +kernel)

def cert817 : Leaf := ⟨⟨192,192,67,130,196,130,258,79,207⟩,[],[(8,5,6)],⟨11,22,140,73,50,352,224,389,277⟩,⟨11,22,140,73,50,352,224,384,272⟩,[⟨4,1212476328082396746351635,⟨11,79,236,73,111,492,228,492,493⟩⟩,⟨5,1297941736064932726055985,⟨399,407,140,205,415,463,205,386,407⟩⟩,⟨0,1210109947688329443019776,⟨10,86,254,72,50,352,224,480,272⟩⟩,⟨2,1210109947688054832497683,⟨11,91,232,73,59,352,224,480,273⟩⟩,⟨3,1210109947688328369277953,⟨3,86,246,65,50,352,224,480,272⟩⟩]⟩
theorem node817 : UpperPrefix a [3,4,7,6,1,8,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,1,8,5] 30 cert817 (by decide +kernel)

theorem node818 : UpperPrefix a [3,4,7,6,1,8] 30 :=
  branch_upper a [3,4,7,6,1,8] 30 (by decide) (fin9_cases _
  node815
  (invalid_upper a [3,4,7,6,1,8,1] 30 (by decide +kernel))
  node816
  (invalid_upper a [3,4,7,6,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,4] 30 (by decide +kernel))
  node817
  (invalid_upper a [3,4,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,8,8] 30 (by decide +kernel)))

theorem node819 : UpperPrefix a [3,4,7,6,1] 30 :=
  branch_upper a [3,4,7,6,1] 30 (by decide) (fin9_cases _
  node808
  (invalid_upper a [3,4,7,6,1,1] 30 (by decide +kernel))
  node812
  (invalid_upper a [3,4,7,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,1,7] 30 (by decide +kernel))
  node818)

def cert820 : Leaf := ⟨⟨496,0,371,0,451,0,306,114,226⟩,[(1,4),(3,5),(5,3)],[(2,4,1)],⟨11,22,140,73,52,97,482,418,306⟩,⟨11,22,140,73,52,97,192,384,272⟩,[⟨3,1304739722951700656434177,⟨35,470,502,97,502,97,192,384,466⟩⟩,⟨0,1285813291192731837670400,⟨10,470,140,72,502,96,192,384,466⟩⟩]⟩
theorem node820 : UpperPrefix a [3,4,7,6,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,0] 30 cert820 (by decide +kernel)

def cert821 : Leaf := ⟨⟨96,0,115,34,195,145,307,115,99⟩,[(1,4)],[(2,4,1)],⟨11,22,140,73,52,98,481,417,305⟩,⟨11,22,140,73,52,98,192,384,272⟩,[⟨3,1214913104420972713225217,⟨499,54,246,481,54,114,192,384,274⟩⟩,⟨8,1181748209931907038333,⟨59,23,191,127,63,127,255,128,19⟩⟩,⟨7,1284484837389052893209649,⟨11,279,12,73,319,107,64,256,275⟩⟩,⟨4,1210107565282756469457953,⟨11,6,140,73,45,107,192,384,256⟩⟩]⟩
theorem node821 : UpperPrefix a [3,4,7,6,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,1] 30 cert821 (by decide +kernel)

def cert822 : Leaf := ⟨⟨496,0,370,0,450,146,306,114,226⟩,[(1,4),(3,6)],[(2,4,1),(0,6,3)],⟨11,22,140,73,52,352,193,418,306⟩,⟨11,22,140,73,52,352,193,384,272⟩,[⟨3,1318934296785895665183745,⟨499,438,502,481,438,352,481,384,402⟩⟩]⟩
theorem node822 : UpperPrefix a [3,4,7,6,2,8,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,8,0] 30 cert822 (by decide +kernel)

def cert823 : Leaf := ⟨⟨192,0,65,130,201,153,313,105,233⟩,[(1,4)],[(2,4,1),(1,6,3)],⟨11,22,140,73,52,352,194,417,305⟩,⟨11,22,140,73,52,352,194,384,272⟩,[⟨4,1210402713187944441578561,⟨11,6,140,77,172,493,207,384,260⟩⟩,⟨8,1181745671434436371569,⟨11,23,140,77,63,127,207,128,19⟩⟩,⟨5,1210107564157964680963153,⟨11,23,140,77,31,333,207,384,275⟩⟩]⟩
theorem node823 : UpperPrefix a [3,4,7,6,2,8,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,8,1] 30 cert823 (by decide +kernel)

def cert824 : Leaf := ⟨⟨192,0,83,130,202,138,266,91,203⟩,[(1,4)],[(2,4,1),(8,5,6)],⟨11,22,140,73,52,352,224,387,275⟩,⟨11,22,140,73,52,352,224,384,272⟩,[⟨5,1297941736064932726055985,⟨399,407,140,205,415,463,205,386,407⟩⟩,⟨4,1210109947686955321918467,⟨11,79,236,73,100,352,224,480,256⟩⟩,⟨0,1210109947688329443027968,⟨10,86,254,72,118,352,224,480,274⟩⟩]⟩
theorem node824 : UpperPrefix a [3,4,7,6,2,8,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,2,8,5] 30 cert824 (by decide +kernel)

theorem node825 : UpperPrefix a [3,4,7,6,2,8] 30 :=
  branch_upper a [3,4,7,6,2,8] 30 (by decide) (fin9_cases _
  node822
  node823
  (invalid_upper a [3,4,7,6,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,4] 30 (by decide +kernel))
  node824
  (invalid_upper a [3,4,7,6,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,8,8] 30 (by decide +kernel)))

theorem node826 : UpperPrefix a [3,4,7,6,2] 30 :=
  branch_upper a [3,4,7,6,2] 30 (by decide) (fin9_cases _
  node820
  node821
  (invalid_upper a [3,4,7,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,2,7] 30 (by decide +kernel))
  node825)

def cert827 : Leaf := ⟨⟨356,353,353,0,69,0,293,101,101⟩,[(3,5),(5,3)],[(1,6,3),(1,6,5)],⟨11,22,140,73,304,97,194,420,308⟩,⟨11,22,140,73,304,97,194,384,272⟩,[⟨3,1229034033106801895934977,⟨99,470,502,97,304,97,194,384,272⟩⟩,⟨4,1210255177902980085580867,⟨111,239,172,109,428,109,239,384,388⟩⟩,⟨7,1227816442128175408876613,⟨43,279,319,105,312,105,107,256,272⟩⟩]⟩
theorem node827 : UpperPrefix a [3,4,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,0,1] 30 cert827 (by decide +kernel)

def cert828 : Leaf := ⟨⟨372,353,371,0,71,0,0,119,103⟩,[(3,5),(5,3),(6,2)],[(7,2,6)],⟨11,22,140,73,304,97,196,418,306⟩,⟨11,22,140,73,304,97,196,384,272⟩,[⟨3,1423029217160785894083585,⟨499,470,502,499,432,499,470,384,272⟩⟩]⟩
theorem node828 : UpperPrefix a [3,4,7,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,0,2] 30 cert828 (by decide +kernel)

def cert829 : Leaf := ⟨⟨436,416,306,0,134,0,278,54,166⟩,[(3,5),(5,3)],[],⟨11,22,140,73,304,97,224,390,278⟩,⟨11,22,140,73,304,97,224,384,272⟩,[⟨0,1408881320747834486838272,⟨398,470,398,478,498,502,498,384,336⟩⟩,⟨6,1408879303135201424856077,⟨399,407,399,415,434,439,434,384,272⟩⟩,⟨3,1238497194802285105908737,⟨499,470,502,113,304,113,224,384,272⟩⟩]⟩
theorem node829 : UpperPrefix a [3,4,7,6,8,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,0,5] 30 cert829 (by decide +kernel)

theorem node830 : UpperPrefix a [3,4,7,6,8,0] 30 :=
  branch_upper a [3,4,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,6,8,0,0] 30 (by decide +kernel))
  node827
  node828
  (invalid_upper a [3,4,7,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,4] 30 (by decide +kernel))
  node829
  (invalid_upper a [3,4,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,0,8] 30 (by decide +kernel)))

def cert831 : Leaf := ⟨⟨192,488,64,0,204,396,302,108,236⟩,[(3,6)],[(0,6,3)],⟨11,22,140,73,304,98,193,420,308⟩,⟨11,22,140,73,304,98,193,384,272⟩,[⟨4,1210255463600083661489187,⟨111,239,140,109,493,111,237,388,460⟩⟩,⟨1,1437223878321571323969537,⟨9,404,140,77,436,508,205,384,400⟩⟩,⟨5,1210107564157964680954913,⟨11,22,140,77,281,79,205,384,272⟩⟩,⟨8,1181745669235413091361,⟨11,22,140,77,57,111,205,128,16⟩⟩,⟨2,1210107565283864569971745,⟨11,18,136,73,313,107,201,384,272⟩⟩]⟩
theorem node831 : UpperPrefix a [3,4,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,0] 30 cert831 (by decide +kernel)

#print axioms node831
end Delivery.FiniteExclusion.Sharp4x5
