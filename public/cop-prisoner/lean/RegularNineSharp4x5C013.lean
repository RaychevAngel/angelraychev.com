import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C007
import RegularNineSharp4x5C012
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert832 : Leaf := ⟨⟨352,353,355,290,67,261,0,99,99⟩,[(6,2)],[(7,2,6),(2,6,5)],⟨11,22,140,73,304,98,196,417,305⟩,⟨11,22,140,73,304,98,196,384,272⟩,[⟨3,1252691948780877526371329,⟨435,118,502,499,304,98,246,384,272⟩⟩,⟨4,1210262453186696733787171,⟨111,239,204,105,493,111,196,452,460⟩⟩]⟩
theorem node832 : UpperPrefix a [3,4,7,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,2] 30 cert832 (by decide +kernel)

def cert833 : Leaf := ⟨⟨448,448,323,386,194,384,258,66,198⟩,[],[(0,7,2)],⟨11,22,140,73,304,98,224,385,276⟩,⟨11,22,140,73,304,98,224,385,272⟩,[⟨2,1210257769453005570049059,⟨107,251,216,105,505,107,249,505,472⟩⟩,⟨3,1238453527841061932633089,⟨499,374,502,241,304,370,240,497,272⟩⟩,⟨4,1210257769443110088606755,⟨111,239,204,109,493,111,237,493,460⟩⟩,⟨5,1297941736064932726055985,⟨399,407,140,205,415,463,205,391,407⟩⟩]⟩
theorem node833 : UpperPrefix a [3,4,7,6,8,1,5,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,5,0] 30 cert833 (by decide +kernel)

def cert834 : Leaf := ⟨⟨448,448,323,386,194,388,262,67,195⟩,[],[],⟨11,22,140,73,304,98,224,388,273⟩,⟨11,22,140,73,304,98,224,388,272⟩,[⟨3,1252648178058604600953857,⟨371,246,502,369,304,98,242,502,272⟩⟩,⟨4,1212616646841518484096035,⟨111,239,140,109,493,111,237,388,460⟩⟩,⟨5,1297941736064932726055985,⟨399,407,140,205,415,463,205,390,407⟩⟩,⟨0,1210109950159756704418816,⟨42,118,254,104,304,98,242,502,272⟩⟩,⟨2,1776791543234819065381921,⟨267,274,392,345,313,379,505,384,272⟩⟩]⟩
theorem node834 : UpperPrefix a [3,4,7,6,8,1,5,2] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,1,5,2] 30 cert834 (by decide +kernel)

theorem node835 : UpperPrefix a [3,4,7,6,8,1,5] 30 :=
  branch_upper a [3,4,7,6,8,1,5] 30 (by decide) (fin9_cases _
  node833
  (invalid_upper a [3,4,7,6,8,1,5,1] 30 (by decide +kernel))
  node834
  (invalid_upper a [3,4,7,6,8,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,5,8] 30 (by decide +kernel)))

theorem node836 : UpperPrefix a [3,4,7,6,8,1] 30 :=
  branch_upper a [3,4,7,6,8,1] 30 (by decide) (fin9_cases _
  node831
  (invalid_upper a [3,4,7,6,8,1,1] 30 (by decide +kernel))
  node832
  (invalid_upper a [3,4,7,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,4] 30 (by decide +kernel))
  node835
  (invalid_upper a [3,4,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,1,8] 30 (by decide +kernel)))

def cert837 : Leaf := ⟨⟨372,288,368,0,6,408,318,54,38⟩,[(3,6)],[(7,2,5),(0,6,3)],⟨11,22,140,73,304,100,193,418,306⟩,⟨11,22,140,73,304,100,193,384,272⟩,[⟨3,1437223878321561635144705,⟨3,406,132,65,434,502,193,384,400⟩⟩,⟨6,1437222725400058102039553,⟨11,406,140,9,434,438,129,384,400⟩⟩,⟨1,1210107567817135083225089,⟨41,20,172,109,304,108,237,384,272⟩⟩]⟩
theorem node837 : UpperPrefix a [3,4,7,6,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,2,0] 30 cert837 (by decide +kernel)

def cert838 : Leaf := ⟨⟨64,361,65,2,73,137,317,121,105⟩,[],[(7,2,5),(1,6,3)],⟨11,22,140,73,304,100,194,417,305⟩,⟨11,22,140,73,304,100,194,384,272⟩,[⟨2,1361518440643071592891457,⟨11,18,136,73,440,505,203,384,272⟩⟩,⟨4,1210107567816039866565697,⟨43,6,172,109,296,109,239,384,256⟩⟩,⟨8,1181748202510203487297,⟨43,22,172,109,56,109,239,128,16⟩⟩,⟨5,1210107564157964680954945,⟨11,22,140,77,280,77,207,384,272⟩⟩]⟩
theorem node838 : UpperPrefix a [3,4,7,6,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,2,1] 30 cert838 (by decide +kernel)

def cert839 : Leaf := ⟨⟨36,297,307,38,7,130,6,55,39⟩,[],[(7,2,5)],⟨11,22,140,73,304,100,224,387,275⟩,⟨11,22,140,73,304,100,224,384,272⟩,[⟨6,1408879303135201424856077,⟨399,407,399,415,434,439,434,384,272⟩⟩,⟨3,1214839245421924611785729,⟨499,118,228,465,304,100,224,384,272⟩⟩,⟨4,1210107637551452713387011,⟨43,111,236,73,288,100,224,384,256⟩⟩,⟨8,1181817937923050308611,⟨43,127,236,73,48,100,224,128,16⟩⟩,⟨0,1210107637552551956579328,⟨42,118,236,72,304,100,224,384,272⟩⟩]⟩
theorem node839 : UpperPrefix a [3,4,7,6,8,2,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,2,5] 30 cert839 (by decide +kernel)

theorem node840 : UpperPrefix a [3,4,7,6,8,2] 30 :=
  branch_upper a [3,4,7,6,8,2] 30 (by decide) (fin9_cases _
  node837
  node838
  (invalid_upper a [3,4,7,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,4] 30 (by decide +kernel))
  node839
  (invalid_upper a [3,4,7,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,8] 30 (by decide +kernel)))

theorem node841 : UpperPrefix a [3,4,7,6,8] 30 :=
  branch_upper a [3,4,7,6,8] 30 (by decide) (fin9_cases _
  node830
  node836
  node840
  (invalid_upper a [3,4,7,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,8] 30 (by decide +kernel)))

theorem node842 : UpperPrefix a [3,4,7,6] 30 :=
  branch_upper a [3,4,7,6] 30 (by decide) (fin9_cases _
  node807
  node819
  node826
  (invalid_upper a [3,4,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,7] 30 (by decide +kernel))
  node841)

def cert843 : Leaf := ⟨⟨112,104,368,112,74,28,0,120,104⟩,[(6,2)],[(7,2,6),(8,3,2),(1,5,4),(2,6,5)],⟨11,22,140,265,49,98,196,480,368⟩,⟨11,22,140,265,49,98,196,384,272⟩,[⟨0,1298016092289170675082240,⟨494,502,204,492,502,482,196,416,498⟩⟩]⟩
theorem node843 : UpperPrefix a [3,4,7,8,0,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,1,2] 30 cert843 (by decide +kernel)

def cert844 : Leaf := ⟨⟨244,224,352,244,198,132,4,100,228⟩,[],[(8,3,2),(1,5,4)],⟨11,22,140,265,49,98,224,452,340⟩,⟨11,22,140,265,49,98,224,384,272⟩,[⟨0,1295367183074742406226944,⟨494,502,204,492,502,482,224,480,498⟩⟩,⟨3,1238497807221740562025473,⟨499,502,502,369,113,482,224,384,272⟩⟩,⟨4,1210181514423817972483073,⟨239,6,204,493,101,98,224,384,256⟩⟩]⟩
theorem node844 : UpperPrefix a [3,4,7,8,0,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,1,5] 30 cert844 (by decide +kernel)

theorem node845 : UpperPrefix a [3,4,7,8,0,1] 30 :=
  branch_upper a [3,4,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,1] 30 (by decide +kernel))
  node843
  (invalid_upper a [3,4,7,8,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,4] 30 (by decide +kernel))
  node844
  (invalid_upper a [3,4,7,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,8] 30 (by decide +kernel)))

def cert846 : Leaf := ⟨⟨112,104,370,114,66,146,48,82,98⟩,[],[(7,2,5),(8,3,2)],⟨11,22,140,265,49,100,194,416,336⟩,⟨11,22,140,265,49,100,194,416,272⟩,[⟨0,1298315626981862063481856,⟨494,502,172,492,502,228,482,480,498⟩⟩,⟨2,1371110783590200128832579,⟨331,475,136,265,441,505,459,440,408⟩⟩,⟨3,1338377054314022971638785,⟨499,502,388,465,497,228,482,416,400⟩⟩]⟩
theorem node846 : UpperPrefix a [3,4,7,8,0,2,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,2,1,5] 30 cert846 (by decide +kernel)

def cert847 : Leaf := ⟨⟨96,104,354,98,74,138,40,42,106⟩,[],[(7,2,5),(8,3,2)],⟨11,22,140,265,49,100,194,448,304⟩,⟨11,22,140,265,49,100,194,448,272⟩,[⟨0,1298315626981862063481856,⟨494,502,172,492,502,228,482,448,498⟩⟩,⟨2,1437316166085150674781251,⟨203,475,136,457,505,505,203,457,408⟩⟩,⟨4,1210181377908471498015809,⟨239,38,172,493,101,101,239,493,288⟩⟩]⟩
theorem node847 : UpperPrefix a [3,4,7,8,0,2,1,6] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,2,1,6] 30 cert847 (by decide +kernel)

theorem node848 : UpperPrefix a [3,4,7,8,0,2,1] 30 :=
  branch_upper a [3,4,7,8,0,2,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,2,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,4] 30 (by decide +kernel))
  node846
  node847
  (invalid_upper a [3,4,7,8,0,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,8] 30 (by decide +kernel)))

def cert849 : Leaf := ⟨⟨116,104,370,118,68,128,4,118,102⟩,[],[(7,2,5),(8,3,2)],⟨11,22,140,265,49,100,224,450,338⟩,⟨11,22,140,265,49,100,224,384,272⟩,[⟨0,1297651760508728121762816,⟨494,502,236,492,502,100,224,448,498⟩⟩,⟨3,1224302749390910782440449,⟨499,502,228,465,497,100,224,384,336⟩⟩,⟨1,1210107637552620676055041,⟨57,116,236,281,49,100,224,384,272⟩⟩,⟨4,1210107637551452444951553,⟨43,102,236,265,33,100,224,384,256⟩⟩]⟩
theorem node849 : UpperPrefix a [3,4,7,8,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,2,5] 30 cert849 (by decide +kernel)

theorem node850 : UpperPrefix a [3,4,7,8,0,2] 30 :=
  branch_upper a [3,4,7,8,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,2,0] 30 (by decide +kernel))
  node848
  (invalid_upper a [3,4,7,8,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,4] 30 (by decide +kernel))
  node849
  (invalid_upper a [3,4,7,8,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,8] 30 (by decide +kernel)))

theorem node851 : UpperPrefix a [3,4,7,8,0] 30 :=
  branch_upper a [3,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,0] 30 (by decide +kernel))
  node845
  node850
  (invalid_upper a [3,4,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,8] 30 (by decide +kernel)))

def cert852 : Leaf := ⟨⟨116,105,353,118,69,4,0,101,101⟩,[(6,2)],[(7,2,6),(8,3,2)],⟨11,22,140,265,50,97,196,480,368⟩,⟨11,22,140,265,50,97,196,384,272⟩,[⟨1,1285887060471287517544449,⟨237,468,236,493,496,101,196,384,400⟩⟩,⟨3,1441955576295913260319745,⟨499,470,196,433,498,497,196,384,400⟩⟩,⟨4,1210181586762886987121665,⟨239,70,236,493,34,101,196,384,256⟩⟩]⟩
theorem node852 : UpperPrefix a [3,4,7,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,8,1,0,2] 30 cert852 (by decide +kernel)

def cert853 : Leaf := ⟨⟨244,224,352,244,196,132,4,100,228⟩,[],[(8,3,2)],⟨11,22,140,265,50,97,224,452,340⟩,⟨11,22,140,265,50,97,224,384,272⟩,[⟨0,1370982485048398210941952,⟨398,470,140,268,498,502,498,384,336⟩⟩,⟨1,1295360292215468951076865,⟨493,468,236,493,500,237,228,384,464⟩⟩,⟨3,1238497483032661257620481,⟨499,470,502,369,498,113,224,384,336⟩⟩,⟨4,1210181586762886987121665,⟨239,70,236,493,34,101,224,384,256⟩⟩]⟩
theorem node853 : UpperPrefix a [3,4,7,8,1,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,1,0,5] 30 cert853 (by decide +kernel)

theorem node854 : UpperPrefix a [3,4,7,8,1,0] 30 :=
  branch_upper a [3,4,7,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,1] 30 (by decide +kernel))
  node852
  (invalid_upper a [3,4,7,8,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,4] 30 (by decide +kernel))
  node853
  (invalid_upper a [3,4,7,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,8] 30 (by decide +kernel)))

def cert855 : Leaf := ⟨⟨112,96,353,114,68,137,41,105,107⟩,[],[(7,2,5),(8,3,2),(2,5,4)],⟨11,22,140,265,50,100,225,481,369⟩,⟨11,22,140,265,50,100,192,384,272⟩,[⟨1,1210181514847129949175809,⟨237,52,236,493,48,100,192,384,272⟩⟩,⟨4,1210181514846030437549057,⟨239,38,236,493,34,100,192,384,256⟩⟩,⟨0,1210107565286050709390336,⟨10,22,140,264,50,118,192,384,272⟩⟩,⟨3,1210107565286049635648513,⟨3,22,132,257,50,118,192,384,272⟩⟩]⟩
theorem node855 : UpperPrefix a [3,4,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,8,1,2] 30 cert855 (by decide +kernel)

theorem node856 : UpperPrefix a [3,4,7,8,1] 30 :=
  branch_upper a [3,4,7,8,1] 30 (by decide) (fin9_cases _
  node854
  (invalid_upper a [3,4,7,8,1,1] 30 (by decide +kernel))
  node855
  (invalid_upper a [3,4,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,8] 30 (by decide +kernel)))

def cert857 : Leaf := ⟨⟨144,0,275,146,139,154,50,114,226⟩,[(1,4)],[(8,3,2),(2,4,1)],⟨11,22,140,265,52,97,226,482,370⟩,⟨11,22,140,265,52,97,192,384,272⟩,[⟨6,1210106412364597692491009,⟨11,22,140,265,54,55,140,397,283⟩⟩,⟨0,1285813291192731837670400,⟨10,470,140,264,502,96,192,384,466⟩⟩,⟨3,1285813291192730763928577,⟨3,470,132,257,502,97,192,384,466⟩⟩,⟨5,1210107564158003369223425,⟨11,22,140,265,22,69,204,397,283⟩⟩]⟩
theorem node857 : UpperPrefix a [3,4,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,8,2,0] 30 cert857 (by decide +kernel)

def cert858 : Leaf := ⟨⟨176,0,291,178,131,129,35,99,227⟩,[(1,4)],[(8,3,2),(2,4,1)],⟨11,22,140,265,52,98,225,481,369⟩,⟨11,22,140,265,52,98,192,384,272⟩,[⟨3,1214913104420972713225217,⟨499,54,246,481,54,114,192,384,274⟩⟩,⟨4,1210181514423817972483073,⟨239,6,204,493,36,98,192,384,256⟩⟩,⟨6,1210106412364597692491009,⟨11,22,140,265,54,54,140,397,283⟩⟩]⟩
theorem node858 : UpperPrefix a [3,4,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,8,2,1] 30 cert858 (by decide +kernel)

theorem node859 : UpperPrefix a [3,4,7,8,2] 30 :=
  branch_upper a [3,4,7,8,2] 30 (by decide) (fin9_cases _
  node857
  node858
  (invalid_upper a [3,4,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,8] 30 (by decide +kernel)))

def cert860 : Leaf := ⟨⟨148,137,257,148,0,142,45,45,173⟩,[(4,5)],[(8,3,2),(6,4,4),(1,6,5)],⟨11,22,140,265,112,97,194,420,308⟩,⟨11,22,140,265,112,97,194,384,272⟩,[⟨4,1210181370590104873337857,⟨239,6,172,493,96,101,194,384,256⟩⟩,⟨5,1210107564158003369223489,⟨11,22,140,265,87,69,207,397,283⟩⟩]⟩
theorem node860 : UpperPrefix a [3,4,7,8,6,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,0,1] 30 cert860 (by decide +kernel)

def cert861 : Local := ⟨⟨52,41,307,54,0,30,0,63,47⟩,[(4,5),(6,2)],[(7,2,6),(8,3,2),(6,4,4)]⟩
theorem node861 : UpperPrefix a [3,4,7,8,6,0,2] 30 :=
  local_sound a [3,4,7,8,6,0,2] 30 cert861 (by decide +kernel)

def cert862 : Leaf := ⟨⟨148,136,274,150,0,158,30,30,142⟩,[(4,5)],[(8,3,2),(6,4,4),(5,6,4)],⟨11,22,140,265,112,97,224,390,278⟩,⟨11,22,140,265,112,97,224,384,272⟩,[⟨0,1370991708420435067814912,⟨398,470,140,396,498,502,498,384,336⟩⟩]⟩
theorem node862 : UpperPrefix a [3,4,7,8,6,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,0,5] 30 cert862 (by decide +kernel)

theorem node863 : UpperPrefix a [3,4,7,8,6,0] 30 :=
  branch_upper a [3,4,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,6,0,0] 30 (by decide +kernel))
  node860
  node861
  (invalid_upper a [3,4,7,8,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,0,4] 30 (by decide +kernel))
  node862
  (invalid_upper a [3,4,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,0,8] 30 (by decide +kernel)))

def cert864 : Leaf := ⟨⟨148,136,274,150,0,156,30,62,174⟩,[(4,5)],[(8,3,2),(6,4,4)],⟨11,22,140,265,112,98,193,420,308⟩,⟨11,22,140,265,112,98,193,384,272⟩,[⟨0,1522392498529027522593792,⟨398,438,140,268,498,498,502,384,304⟩⟩,⟨5,1210109870001012582917377,⟨11,22,204,265,86,70,205,461,283⟩⟩]⟩
theorem node864 : UpperPrefix a [3,4,7,8,6,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,1,0] 30 cert864 (by decide +kernel)

def cert865 : Local := ⟨⟨48,41,307,50,0,29,0,59,43⟩,[(4,5),(6,2)],[(7,2,6),(8,3,2),(6,4,4),(2,6,5)]⟩
theorem node865 : UpperPrefix a [3,4,7,8,6,1,2] 30 :=
  local_sound a [3,4,7,8,6,1,2] 30 cert865 (by decide +kernel)

def cert866 : Leaf := ⟨⟨148,137,259,150,0,141,15,15,143⟩,[(4,5)],[(8,3,2),(6,4,4),(5,6,4)],⟨11,22,140,265,112,98,224,389,277⟩,⟨11,22,140,265,112,98,224,384,272⟩,[⟨4,1210181514423817972483073,⟨239,6,204,493,96,98,224,384,256⟩⟩]⟩
theorem node866 : UpperPrefix a [3,4,7,8,6,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,1,5] 30 cert866 (by decide +kernel)

theorem node867 : UpperPrefix a [3,4,7,8,6,1] 30 :=
  branch_upper a [3,4,7,8,6,1] 30 (by decide) (fin9_cases _
  node864
  (invalid_upper a [3,4,7,8,6,1,1] 30 (by decide +kernel))
  node865
  (invalid_upper a [3,4,7,8,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,1,4] 30 (by decide +kernel))
  node866
  (invalid_upper a [3,4,7,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,1,8] 30 (by decide +kernel)))

def cert868 : Leaf := ⟨⟨20,8,275,22,0,155,30,62,46⟩,[(4,5)],[(7,2,5),(8,3,2),(6,4,4)],⟨11,22,140,265,112,100,193,418,306⟩,⟨11,22,140,265,112,100,193,384,272⟩,[⟨5,1210109870001012582917377,⟨11,22,204,265,86,68,205,461,283⟩⟩,⟨0,1437223878321562708886528,⟨10,406,140,264,498,502,192,384,400⟩⟩]⟩
theorem node868 : UpperPrefix a [3,4,7,8,6,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,2,0] 30 cert868 (by decide +kernel)

def cert869 : Leaf := ⟨⟨48,33,307,50,0,147,49,51,35⟩,[(4,5)],[(7,2,5),(8,3,2),(6,4,4)],⟨11,22,140,265,112,100,194,417,305⟩,⟨11,22,140,265,112,100,194,384,272⟩,[⟨2,1437223914350366437672003,⟨75,475,136,265,505,505,203,384,408⟩⟩,⟨3,1214839245428933998431233,⟨499,118,246,465,114,118,242,384,272⟩⟩]⟩
theorem node869 : UpperPrefix a [3,4,7,8,6,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,2,1] 30 cert869 (by decide +kernel)

def cert870 : Local := ⟨⟨20,9,275,22,0,155,31,31,15⟩,[(4,5)],[(7,2,5),(8,3,2),(6,4,4),(5,6,4)]⟩
theorem node870 : UpperPrefix a [3,4,7,8,6,2,5] 30 :=
  local_sound a [3,4,7,8,6,2,5] 30 cert870 (by decide +kernel)

theorem node871 : UpperPrefix a [3,4,7,8,6,2] 30 :=
  branch_upper a [3,4,7,8,6,2] 30 (by decide) (fin9_cases _
  node868
  node869
  (invalid_upper a [3,4,7,8,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,2,4] 30 (by decide +kernel))
  node870
  (invalid_upper a [3,4,7,8,6,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,2,8] 30 (by decide +kernel)))

theorem node872 : UpperPrefix a [3,4,7,8,6] 30 :=
  branch_upper a [3,4,7,8,6] 30 (by decide) (fin9_cases _
  node863
  node867
  node871
  (invalid_upper a [3,4,7,8,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,8] 30 (by decide +kernel)))

theorem node873 : UpperPrefix a [3,4,7,8] 30 :=
  branch_upper a [3,4,7,8] 30 (by decide) (fin9_cases _
  node851
  node856
  node859
  (invalid_upper a [3,4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,5] 30 (by decide +kernel))
  node872
  (invalid_upper a [3,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,8] 30 (by decide +kernel)))

theorem node874 : UpperPrefix a [3,4,7] 30 :=
  branch_upper a [3,4,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [3,4,7,1] [2,0,4,7] 30 (by decide +kernel) node39)
  (PrefixConjugacy.upper aut5 [3,4,7,2] [3,0,4,7] 30 (by decide +kernel) node487)
  (invalid_upper a [3,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,4] 30 (by decide +kernel))
  node797
  node842
  (invalid_upper a [3,4,7,7] 30 (by decide +kernel))
  node873)

def cert875 : Leaf := ⟨⟨500,448,210,0,0,406,278,86,198⟩,[(3,4),(4,3)],[],⟨11,22,268,41,49,230,198,454,470⟩,⟨11,22,268,41,49,96,192,384,272⟩,[⟨0,1295285748986280290821120,⟨494,502,268,236,502,96,192,384,498⟩⟩,⟨3,1238497212711405377031169,⟨499,502,502,49,49,96,192,384,272⟩⟩,⟨5,1295285747191877314290689,⟨463,470,268,205,471,64,192,384,466⟩⟩]⟩
theorem node875 : UpperPrefix a [3,4,8,5,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,0] 30 cert875 (by decide +kernel)

def cert876 : Leaf := ⟨⟨484,488,224,0,452,388,292,100,228⟩,[(3,5)],[(0,5,3)],⟨11,22,268,41,50,97,196,452,468⟩,⟨11,22,268,41,50,97,192,384,272⟩,[⟨1,1297689229683576089608193,⟨493,468,492,237,508,237,192,448,468⟩⟩,⟨3,1219607746603455179916289,⟨499,470,452,49,498,113,192,384,272⟩⟩,⟨4,1212512677303496744109075,⟨107,239,492,41,107,105,196,492,493⟩⟩]⟩
theorem node876 : UpperPrefix a [3,4,8,5,1,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,1,0] 30 cert876 (by decide +kernel)

def cert877 : Leaf := ⟨⟨288,289,35,258,261,387,291,99,227⟩,[],[(2,5,4)],⟨11,22,268,41,50,100,193,449,465⟩,⟨11,22,268,41,50,100,192,384,272⟩,[⟨3,1252692036251494281923585,⟨467,54,502,499,50,118,192,384,272⟩⟩,⟨4,1212473376113578484958227,⟨11,47,492,41,43,100,228,492,493⟩⟩,⟨6,1210106412365102368050495,⟨27,31,287,59,59,63,128,391,287⟩⟩,⟨7,1208926973665889563594047,⟨27,31,287,59,59,127,64,263,287⟩⟩]⟩
theorem node877 : UpperPrefix a [3,4,8,5,1,2] 30 :=
  Boolean.leaf_sound a [3,4,8,5,1,2] 30 cert877 (by decide +kernel)

def cert878 : Leaf := ⟨⟨32,297,35,0,333,0,302,111,111⟩,[(5,6)],[(7,5,5)],⟨11,22,268,41,50,224,193,452,340⟩,⟨11,22,268,41,50,224,193,384,272⟩,[⟨4,1212510305700900391355411,⟨107,239,492,41,107,236,237,492,493⟩⟩,⟨6,1210106412362349293995287,⟨11,31,271,41,59,160,129,391,287⟩⟩,⟨2,1210107567535662236173331,⟨11,27,264,41,59,232,233,384,281⟩⟩,⟨8,1181747921033062515731,⟨11,31,12,41,59,232,233,128,25⟩⟩,⟨1,1210107567535660089737217,⟨9,20,268,41,48,232,233,384,272⟩⟩]⟩
theorem node878 : UpperPrefix a [3,4,8,5,1,7,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,1,7,0] 30 cert878 (by decide +kernel)

def cert879 : Leaf := ⟨⟨36,40,35,6,76,0,299,111,111⟩,[(5,6)],[(8,2,6),(7,5,5)],⟨11,22,268,41,50,224,196,449,337⟩,⟨11,22,268,41,50,224,196,384,272⟩,[⟨4,1212476330474934040003603,⟨11,111,492,105,107,228,228,492,493⟩⟩,⟨6,1210106412362349293995287,⟨11,31,271,41,59,160,133,391,287⟩⟩,⟨0,1210107567542248569603072,⟨10,22,268,56,50,242,246,384,272⟩⟩]⟩
theorem node879 : UpperPrefix a [3,4,8,5,1,7,2] 30 :=
  Boolean.leaf_sound a [3,4,8,5,1,7,2] 30 cert879 (by decide +kernel)

theorem node880 : UpperPrefix a [3,4,8,5,1,7] 30 :=
  branch_upper a [3,4,8,5,1,7] 30 (by decide) (fin9_cases _
  node878
  (invalid_upper a [3,4,8,5,1,7,1] 30 (by decide +kernel))
  node879
  (invalid_upper a [3,4,8,5,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,7,8] 30 (by decide +kernel)))

theorem node881 : UpperPrefix a [3,4,8,5,1] 30 :=
  branch_upper a [3,4,8,5,1] 30 (by decide) (fin9_cases _
  node876
  (invalid_upper a [3,4,8,5,1,1] 30 (by decide +kernel))
  node877
  (invalid_upper a [3,4,8,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,1,6] 30 (by decide +kernel))
  node880
  (invalid_upper a [3,4,8,5,1,8] 30 (by decide +kernel)))

def cert882 : Leaf := ⟨⟨496,0,242,0,450,402,306,114,226⟩,[(1,4),(3,5)],[(2,4,1),(0,5,3)],⟨11,22,268,41,52,97,194,450,466⟩,⟨11,22,268,41,52,97,192,384,272⟩,[⟨3,1316577975039383661718529,⟨483,470,502,225,502,225,192,448,466⟩⟩]⟩
theorem node882 : UpperPrefix a [3,4,8,5,2,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,2,0] 30 cert882 (by decide +kernel)

def cert883 : Leaf := ⟨⟨416,0,161,386,449,401,305,113,225⟩,[(1,4)],[(2,4,1),(1,5,3)],⟨11,22,268,41,52,98,193,449,465⟩,⟨11,22,268,41,52,98,192,384,272⟩,[⟨3,1214913104420972713225217,⟨499,54,502,481,54,114,192,384,274⟩⟩,⟨4,1210107565282758684050467,⟨11,15,268,41,45,107,192,388,268⟩⟩,⟨6,1210106412362353588970807,⟨11,31,271,41,63,43,128,391,287⟩⟩]⟩
theorem node883 : UpperPrefix a [3,4,8,5,2,1] 30 :=
  Boolean.leaf_sound a [3,4,8,5,2,1] 30 cert883 (by decide +kernel)

def cert884 : Leaf := ⟨⟨48,0,51,18,331,0,315,123,107⟩,[(1,4),(5,6)],[(2,4,1),(7,5,5)],⟨11,22,268,41,52,224,195,451,339⟩,⟨11,22,268,41,52,224,192,384,272⟩,[⟨6,1210106412362349294003479,⟨11,31,271,41,63,160,128,391,287⟩⟩,⟨8,1181747921024472589587,⟨11,31,13,41,63,224,224,129,27⟩⟩]⟩
theorem node884 : UpperPrefix a [3,4,8,5,2,7] 30 :=
  Boolean.leaf_sound a [3,4,8,5,2,7] 30 cert884 (by decide +kernel)

theorem node885 : UpperPrefix a [3,4,8,5,2] 30 :=
  branch_upper a [3,4,8,5,2] 30 (by decide) (fin9_cases _
  node882
  node883
  (invalid_upper a [3,4,8,5,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,2,6] 30 (by decide +kernel))
  node884
  (invalid_upper a [3,4,8,5,2,8] 30 (by decide +kernel)))

def cert886 : Leaf := ⟨⟨436,424,146,0,0,406,278,22,134⟩,[(3,5),(4,5)],[(6,4,4),(0,5,3)],⟨11,22,268,41,112,97,198,390,406⟩,⟨11,22,268,41,112,97,192,384,272⟩,[⟨3,1219570781059912746140673,⟨499,470,260,49,112,113,192,384,272⟩⟩,⟨5,1219580021282997162738689,⟨463,470,268,205,80,197,192,384,272⟩⟩]⟩
theorem node886 : UpperPrefix a [3,4,8,5,6,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,6,0] 30 cert886 (by decide +kernel)

def cert887 : Leaf := ⟨⟨32,297,33,2,0,285,317,61,173⟩,[(4,5)],[(6,4,4),(1,5,3)],⟨11,22,268,41,112,98,197,389,405⟩,⟨11,22,268,41,112,98,192,384,272⟩,[⟨7,1208926976484530873075191,⟨11,63,271,57,123,123,127,271,319⟩⟩,⟨4,1210107565282758684050467,⟨11,15,268,41,105,107,192,388,268⟩⟩,⟨2,1210107565286057150776355,⟨11,27,264,57,121,123,192,384,280⟩⟩,⟨8,1181745671427977118755,⟨11,31,12,57,121,123,192,128,24⟩⟩]⟩
theorem node887 : UpperPrefix a [3,4,8,5,6,1] 30 :=
  Boolean.leaf_sound a [3,4,8,5,6,1] 30 cert887 (by decide +kernel)

def cert888 : Leaf := ⟨⟨52,33,51,22,0,403,307,51,163⟩,[(4,5)],[(6,4,4)],⟨11,22,268,41,112,100,195,387,403⟩,⟨11,22,268,41,112,100,192,384,272⟩,[⟨3,1252692036251356842970113,⟨467,54,502,499,114,118,192,384,272⟩⟩,⟨7,1208926973665339807778111,⟨11,31,271,59,123,127,64,263,287⟩⟩,⟨2,1214839173155905473610753,⟨475,18,280,505,112,112,192,384,272⟩⟩,⟨8,1181745671427977135163,⟨11,31,13,59,123,127,192,128,25⟩⟩]⟩
theorem node888 : UpperPrefix a [3,4,8,5,6,2] 30 :=
  Boolean.leaf_sound a [3,4,8,5,6,2] 30 cert888 (by decide +kernel)

def cert889 : Leaf := ⟨⟨308,296,50,278,0,0,318,62,46⟩,[(4,5),(5,6)],[(6,4,4),(7,5,4),(7,5,5)],⟨11,22,268,41,112,224,193,390,278⟩,⟨11,22,268,41,112,224,193,384,272⟩,[⟨0,1560291334228463798490112,⟨398,438,398,446,498,498,502,384,304⟩⟩]⟩
theorem node889 : UpperPrefix a [3,4,8,5,6,7,0] 30 :=
  Boolean.leaf_sound a [3,4,8,5,6,7,0] 30 cert889 (by decide +kernel)

def cert890 : Leaf := ⟨⟨308,297,49,278,0,0,317,61,45⟩,[(4,5),(5,6)],[(6,4,4),(7,5,4),(7,5,5)],⟨11,22,268,41,112,224,194,389,277⟩,⟨11,22,268,41,112,224,194,384,272⟩,[⟨1,1247969509753537426620417,⟨397,20,396,445,112,240,240,384,272⟩⟩]⟩
theorem node890 : UpperPrefix a [3,4,8,5,6,7,1] 30 :=
  Boolean.leaf_sound a [3,4,8,5,6,7,1] 30 cert890 (by decide +kernel)

def cert891 : Local := ⟨⟨52,41,51,22,0,0,315,63,47⟩,[(4,5),(5,6)],[(8,2,6),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node891 : UpperPrefix a [3,4,8,5,6,7,2] 30 :=
  local_sound a [3,4,8,5,6,7,2] 30 cert891 (by decide +kernel)

theorem node892 : UpperPrefix a [3,4,8,5,6,7] 30 :=
  branch_upper a [3,4,8,5,6,7] 30 (by decide) (fin9_cases _
  node889
  node890
  node891
  (invalid_upper a [3,4,8,5,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,7,8] 30 (by decide +kernel)))

theorem node893 : UpperPrefix a [3,4,8,5,6] 30 :=
  branch_upper a [3,4,8,5,6] 30 (by decide) (fin9_cases _
  node886
  node887
  node888
  (invalid_upper a [3,4,8,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,8,5,6,6] 30 (by decide +kernel))
  node892
  (invalid_upper a [3,4,8,5,6,8] 30 (by decide +kernel)))

def cert894 : Leaf := ⟨⟨500,480,208,0,324,406,276,84,196⟩,[(3,5)],[(0,5,3),(1,6,5)],⟨11,22,268,41,176,97,194,452,340⟩,⟨11,22,268,41,176,97,194,384,272⟩,[⟨3,1238497230831082124872705,⟨499,470,502,113,176,113,450,384,272⟩⟩,⟨5,1219580021282997162738689,⟨463,470,268,205,144,197,450,384,272⟩⟩]⟩
theorem node894 : UpperPrefix a [3,4,8,5,7,0,1] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,0,1] 30 cert894 (by decide +kernel)

def cert895 : Leaf := ⟨⟨244,224,210,0,70,150,274,86,198⟩,[(3,5)],[(8,2,6),(0,5,3)],⟨11,22,268,41,176,97,196,450,338⟩,⟨11,22,268,41,176,97,196,384,272⟩,[⟨3,1243819098202947745483777,⟨499,470,470,433,176,497,454,384,272⟩⟩,⟨5,1219580741858937542018049,⟨463,470,332,205,208,197,196,384,272⟩⟩]⟩
theorem node895 : UpperPrefix a [3,4,8,5,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,8,5,7,0,2] 30 cert895 (by decide +kernel)

#print axioms node895
end Delivery.FiniteExclusion.Sharp4x5
