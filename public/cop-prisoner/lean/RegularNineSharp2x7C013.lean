import RegularNineSharp2x7Base
import RegularNineSharp2x7C012
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
theorem node832 : UpperPrefix a [2,4,7,5,8,3,0] 30 :=
  branch_upper a [2,4,7,5,8,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,5,8,3,0,0] 30 (by decide +kernel))
  node830
  (invalid_upper a [2,4,7,5,8,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,0,5] 30 (by decide +kernel))
  node831
  (invalid_upper a [2,4,7,5,8,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,0,8] 30 (by decide +kernel)))

def cert833 : Leaf := ⟨⟨216,200,82,0,202,146,25,94,218⟩,[(3,4)],[(2,0,7),(5,3,3),(0,7,6)],⟨7,19,140,56,304,104,194,385,324⟩,⟨7,19,140,56,304,104,194,385,260⟩,[⟨8,1181820154540656178277,⟨111,59,239,59,59,111,239,161,101⟩⟩]⟩
theorem node833 : UpperPrefix a [2,4,7,5,8,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,3,1,0] 30 cert833 (by decide +kernel)

def cert834 : Leaf := ⟨⟨88,76,81,0,77,21,29,31,89⟩,[(3,4)],[(5,3,3)],⟨7,19,140,56,304,104,194,448,261⟩,⟨7,19,140,56,304,104,194,448,260⟩,[⟨7,1232538812841981367234309,⟨287,283,319,58,315,104,122,379,287⟩⟩,⟨8,1181820154540656178277,⟨111,59,239,59,59,111,239,229,101⟩⟩,⟨1,1214829938530945369899009,⟨269,281,188,56,312,108,252,508,268⟩⟩]⟩
theorem node834 : UpperPrefix a [2,4,7,5,8,3,1,6] 30 :=
  Boolean.leaf_sound a [2,4,7,5,8,3,1,6] 30 cert834 (by decide +kernel)

theorem node835 : UpperPrefix a [2,4,7,5,8,3,1] 30 :=
  branch_upper a [2,4,7,5,8,3,1] 30 (by decide) (fin9_cases _
  node833
  (invalid_upper a [2,4,7,5,8,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,1,5] 30 (by decide +kernel))
  node834
  (invalid_upper a [2,4,7,5,8,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,1,8] 30 (by decide +kernel)))

theorem node836 : UpperPrefix a [2,4,7,5,8,3] 30 :=
  branch_upper a [2,4,7,5,8,3] 30 (by decide) (fin9_cases _
  node832
  node835
  (invalid_upper a [2,4,7,5,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,3,8] 30 (by decide +kernel)))

theorem node837 : UpperPrefix a [2,4,7,5,8] 30 :=
  branch_upper a [2,4,7,5,8] 30 (by decide) (fin9_cases _
  node826
  node829
  (invalid_upper a [2,4,7,5,8,2] 30 (by decide +kernel))
  node836
  (invalid_upper a [2,4,7,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,8,8] 30 (by decide +kernel)))

theorem node838 : UpperPrefix a [2,4,7,5] 30 :=
  branch_upper a [2,4,7,5] 30 (by decide) (fin9_cases _
  node810
  node814
  (invalid_upper a [2,4,7,5,2] 30 (by decide +kernel))
  node815
  (invalid_upper a [2,4,7,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,5,5] 30 (by decide +kernel))
  node823
  (invalid_upper a [2,4,7,5,7] 30 (by decide +kernel))
  node837)

def cert839 : Leaf := ⟨⟨112,0,112,164,70,20,316,124,120⟩,[(1,4)],[(0,4,1),(1,5,4)],⟨7,19,140,88,49,98,488,424,300⟩,⟨7,19,140,88,49,98,192,384,260⟩,[⟨8,1181748209931907170157,⟨23,19,191,127,59,127,255,131,23⟩⟩,⟨7,1227816439876362710429445,⟨279,19,319,122,51,98,64,259,279⟩⟩,⟨3,1210107565565600467136261,⟨23,19,183,114,51,98,192,387,279⟩⟩]⟩
theorem node839 : UpperPrefix a [2,4,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,1] 30 cert839 (by decide +kernel)

def cert840 : Leaf := ⟨⟨56,0,50,166,14,0,318,62,58⟩,[(1,4),(5,3)],[(6,3,5),(0,4,1)],⟨7,19,140,88,49,104,482,418,294⟩,⟨7,19,140,88,49,104,192,384,260⟩,[⟨8,1181748209931907170157,⟨23,19,191,127,59,127,255,131,23⟩⟩,⟨7,1227816439876362710429445,⟨279,19,319,122,51,104,64,259,279⟩⟩]⟩
theorem node840 : UpperPrefix a [2,4,7,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,3] 30 cert840 (by decide +kernel)

def cert841 : Leaf := ⟨⟨480,0,0,422,454,134,292,102,226⟩,[(1,4),(2,7)],[(0,4,1),(3,7,2)],⟨7,19,140,88,49,352,194,392,292⟩,⟨7,19,140,88,49,352,194,392,260⟩,[⟨4,2178303395951648105825345,⟨487,355,428,493,353,353,487,428,388⟩⟩]⟩
theorem node841 : UpperPrefix a [2,4,7,6,0,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,1,3] 30 cert841 (by decide +kernel)

def cert842 : Leaf := ⟨⟨240,0,114,166,198,150,52,0,250⟩,[(1,4),(7,5)],[(0,4,1),(8,5,7)],⟨7,19,140,88,49,352,194,416,268⟩,⟨7,19,140,88,49,352,194,416,260⟩,[⟨3,1212771764247875984518917,⟨87,83,247,82,243,499,242,499,503⟩⟩]⟩
theorem node842 : UpperPrefix a [2,4,7,6,0,8,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,1,5] 30 cert842 (by decide +kernel)

theorem node843 : UpperPrefix a [2,4,7,6,0,8,1] 30 :=
  branch_upper a [2,4,7,6,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,1,2] 30 (by decide +kernel))
  node841
  (invalid_upper a [2,4,7,6,0,8,1,4] 30 (by decide +kernel))
  node842
  (invalid_upper a [2,4,7,6,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,1,8] 30 (by decide +kernel)))

def cert844 : Leaf := ⟨⟨440,0,0,422,398,158,0,62,186⟩,[(1,4),(2,6),(6,2)],[(0,4,1)],⟨7,19,140,88,49,352,200,418,294⟩,⟨7,19,140,88,49,352,200,384,260⟩,[⟨6,1361664861674143797507181,⟨7,147,143,159,435,439,143,384,261⟩⟩]⟩
theorem node844 : UpperPrefix a [2,4,7,6,0,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,3] 30 cert844 (by decide +kernel)

def cert845 : Leaf := ⟨⟨144,0,18,166,198,150,278,30,154⟩,[(1,4)],[(0,4,1),(8,5,6),(5,6,3)],⟨7,19,140,88,49,352,224,394,270⟩,⟨7,19,140,88,49,352,224,384,260⟩,[⟨3,1210109956724114926563077,⟨87,19,247,82,51,371,242,499,375⟩⟩,⟨6,1266885490621225081254925,⟨391,19,399,415,51,288,160,384,389⟩⟩]⟩
theorem node845 : UpperPrefix a [2,4,7,6,0,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,0,8,5] 30 cert845 (by decide +kernel)

theorem node846 : UpperPrefix a [2,4,7,6,0,8] 30 :=
  branch_upper a [2,4,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,0,8,0] 30 (by decide +kernel))
  node843
  (invalid_upper a [2,4,7,6,0,8,2] 30 (by decide +kernel))
  node844
  (invalid_upper a [2,4,7,6,0,8,4] 30 (by decide +kernel))
  node845
  (invalid_upper a [2,4,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,8,8] 30 (by decide +kernel)))

theorem node847 : UpperPrefix a [2,4,7,6,0] 30 :=
  branch_upper a [2,4,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,0,0] 30 (by decide +kernel))
  node839
  (invalid_upper a [2,4,7,6,0,2] 30 (by decide +kernel))
  node840
  (invalid_upper a [2,4,7,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,0,7] 30 (by decide +kernel))
  node846)

def cert848 : Leaf := ⟨⟨248,32,112,32,1,156,316,124,248⟩,[],[(1,4,1),(0,5,4)],⟨7,19,140,88,50,97,488,424,300⟩,⟨7,19,140,88,50,97,192,384,260⟩,[⟨8,1181748209931907170157,⟨23,19,191,127,59,127,255,131,23⟩⟩,⟨2,1210107565286055003309057,⟨3,19,136,88,58,123,192,384,256⟩⟩,⟨7,1208926973665337593054209,⟨7,19,12,88,58,123,64,256,260⟩⟩,⟨3,1210107565286049635648513,⟨7,19,132,80,50,115,192,384,260⟩⟩,⟨6,1210106412364546102543361,⟨7,19,140,24,50,51,128,384,260⟩⟩]⟩
theorem node848 : UpperPrefix a [2,4,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,0] 30 cert848 (by decide +kernel)

def cert849 : Leaf := ⟨⟨168,172,33,165,141,0,301,45,169⟩,[(5,3)],[(6,3,5),(1,4,1)],⟨7,19,140,88,50,104,481,417,293⟩,⟨7,19,140,88,50,104,192,384,260⟩,[⟨4,1328397762437589886829585,⟨487,451,492,493,487,492,192,384,292⟩⟩,⟨8,1181748209931907170157,⟨23,19,191,127,59,127,255,131,23⟩⟩]⟩
theorem node849 : UpperPrefix a [2,4,7,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,3] 30 cert849 (by decide +kernel)

def cert850 : Leaf := ⟨⟨240,228,0,165,197,133,36,101,193⟩,[(2,7)],[(1,4,1),(3,7,2)],⟨7,19,140,88,50,352,193,392,292⟩,⟨7,19,140,88,50,352,193,392,292⟩,[⟨8,1184123589672857466349,⟨71,19,207,95,59,127,207,223,127⟩⟩,⟨4,2178303395388698152403969,⟨487,355,428,492,34,352,485,428,420⟩⟩]⟩
theorem node850 : UpperPrefix a [2,4,7,6,1,8,0,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,0,3,5] 30 cert850 (by decide +kernel)

theorem node851 : UpperPrefix a [2,4,7,6,1,8,0,3] 30 :=
  branch_upper a [2,4,7,6,1,8,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,1,8,0,3,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,3,4] 30 (by decide +kernel))
  node850
  (invalid_upper a [2,4,7,6,1,8,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,3,8] 30 (by decide +kernel)))

def cert852 : Leaf := ⟨⟨112,100,113,37,69,149,52,0,121⟩,[(7,5)],[(1,4,1),(8,5,7)],⟨7,19,140,88,50,352,193,416,268⟩,⟨7,19,140,88,50,352,193,416,260⟩,[⟨3,1212771476021897879342853,⟨87,19,247,82,242,499,243,499,503⟩⟩,⟨7,1227816439605620856966405,⟨263,19,287,90,58,379,91,315,263⟩⟩]⟩
theorem node852 : UpperPrefix a [2,4,7,6,1,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,0,5] 30 cert852 (by decide +kernel)

theorem node853 : UpperPrefix a [2,4,7,6,1,8,0] 30 :=
  branch_upper a [2,4,7,6,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,2] 30 (by decide +kernel))
  node851
  (invalid_upper a [2,4,7,6,1,8,0,4] 30 (by decide +kernel))
  node852
  (invalid_upper a [2,4,7,6,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,0,8] 30 (by decide +kernel)))

def cert854 : Leaf := ⟨⟨184,172,0,165,141,141,0,45,169⟩,[(2,6),(6,2)],[(1,4,1)],⟨7,19,140,88,50,352,200,417,293⟩,⟨7,19,140,88,50,352,200,384,260⟩,[⟨6,1361664861674143797507181,⟨7,147,143,159,435,439,143,384,261⟩⟩,⟨8,1181817729019884369005,⟨71,19,207,95,59,127,207,128,69⟩⟩,⟨4,1214857682981710065566721,⟨487,419,204,76,162,356,204,416,356⟩⟩]⟩
theorem node854 : UpperPrefix a [2,4,7,6,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,3] 30 cert854 (by decide +kernel)

def cert855 : Leaf := ⟨⟨144,132,17,165,197,149,277,29,153⟩,[],[(1,4,1),(8,5,6),(5,6,3)],⟨7,19,140,88,50,352,224,393,269⟩,⟨7,19,140,88,50,352,224,384,260⟩,[⟨3,1210109956728512973065989,⟨87,19,247,80,50,371,242,499,375⟩⟩,⟨6,1266885490621225081246733,⟨391,19,399,415,50,288,160,384,389⟩⟩]⟩
theorem node855 : UpperPrefix a [2,4,7,6,1,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,1,8,5] 30 cert855 (by decide +kernel)

theorem node856 : UpperPrefix a [2,4,7,6,1,8] 30 :=
  branch_upper a [2,4,7,6,1,8] 30 (by decide) (fin9_cases _
  node853
  (invalid_upper a [2,4,7,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,2] 30 (by decide +kernel))
  node854
  (invalid_upper a [2,4,7,6,1,8,4] 30 (by decide +kernel))
  node855
  (invalid_upper a [2,4,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,8,8] 30 (by decide +kernel)))

theorem node857 : UpperPrefix a [2,4,7,6,1] 30 :=
  branch_upper a [2,4,7,6,1] 30 (by decide) (fin9_cases _
  node848
  (invalid_upper a [2,4,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,2] 30 (by decide +kernel))
  node849
  (invalid_upper a [2,4,7,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,1,7] 30 (by decide +kernel))
  node856)

def cert858 : Leaf := ⟨⟨184,40,51,34,66,134,295,39,163⟩,[],[(6,3,4)],⟨7,19,140,88,56,97,482,418,294⟩,⟨7,19,140,88,56,97,192,384,260⟩,[⟨8,1181748209931907170157,⟨23,19,191,127,59,127,255,131,23⟩⟩,⟨3,1214857656031579466630145,⟨487,499,132,80,48,481,192,384,260⟩⟩,⟨4,1214857656030481028744193,⟨487,483,140,72,40,481,192,384,260⟩⟩,⟨2,1210107565286055003309057,⟨3,19,136,88,58,123,192,384,256⟩⟩,⟨7,1208926973665337593054209,⟨7,19,12,88,58,123,64,256,260⟩⟩,⟨0,1210107565286055004341248,⟨6,18,140,88,56,120,192,384,260⟩⟩]⟩
theorem node858 : UpperPrefix a [2,4,7,6,3,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,0] 30 cert858 (by decide +kernel)

def cert859 : Leaf := ⟨⟨168,172,35,160,192,133,295,39,163⟩,[],[(6,3,4)],⟨7,19,140,88,56,98,481,417,293⟩,⟨7,19,140,88,56,98,192,384,260⟩,[⟨4,1224598113362151979615235,⟨487,487,140,76,236,483,192,384,260⟩⟩,⟨8,1181748209931907170157,⟨23,19,191,127,59,127,255,131,23⟩⟩,⟨3,1214857656031579466630145,⟨487,499,132,80,48,226,192,384,260⟩⟩,⟨0,1210107565286055004341248,⟨6,18,140,88,56,122,192,384,260⟩⟩,⟨1,1210107565286055004340225,⟨5,17,140,88,56,120,192,384,260⟩⟩,⟨2,1210107565286055003292673,⟨3,19,136,88,56,122,192,384,256⟩⟩]⟩
theorem node859 : UpperPrefix a [2,4,7,6,3,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,1] 30 cert859 (by decide +kernel)

def cert860 : Leaf := ⟨⟨440,428,304,416,448,132,294,36,160⟩,[],[(6,3,4),(1,7,6)],⟨7,19,140,88,56,352,193,386,292⟩,⟨7,19,140,88,56,352,193,386,260⟩,[⟨0,1720132371346519619535872,⟨406,146,444,380,312,380,508,386,276⟩⟩,⟨3,1233747128718457488540673,⟨487,499,420,112,48,352,481,482,260⟩⟩,⟨4,1233747128717359050654721,⟨487,483,428,104,40,352,481,482,260⟩⟩,⟨2,1210107565286055003292673,⟨3,19,136,88,56,376,193,386,256⟩⟩]⟩
theorem node860 : UpperPrefix a [2,4,7,6,3,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,8,0,1] 30 cert860 (by decide +kernel)

def cert861 : Leaf := ⟨⟨56,44,50,38,70,30,62,0,58⟩,[(7,5)],[(6,3,4),(8,5,7)],⟨7,19,140,88,56,352,193,416,262⟩,⟨7,19,140,88,56,352,193,416,260⟩,[⟨7,1232538808345238118190341,⟨263,275,287,122,58,379,379,315,263⟩⟩,⟨0,1225160110715754362438656,⟨262,278,156,252,188,508,508,444,260⟩⟩]⟩
theorem node861 : UpperPrefix a [2,4,7,6,3,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,8,0,5] 30 cert861 (by decide +kernel)

theorem node862 : UpperPrefix a [2,4,7,6,3,8,0] 30 :=
  branch_upper a [2,4,7,6,3,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,3,8,0,0] 30 (by decide +kernel))
  node860
  (invalid_upper a [2,4,7,6,3,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,0,4] 30 (by decide +kernel))
  node861
  (invalid_upper a [2,4,7,6,3,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,0,8] 30 (by decide +kernel)))

def cert863 : Leaf := ⟨⟨408,392,272,384,448,152,281,28,184⟩,[],[(2,0,7),(6,3,4),(0,7,6)],⟨7,19,140,88,56,352,194,385,292⟩,⟨7,19,140,88,56,352,194,385,260⟩,[⟨1,1720132371346519619534849,⟨405,145,444,380,312,380,508,385,276⟩⟩,⟨5,1212764255592538581251167,⟨79,95,207,95,223,453,207,385,453⟩⟩]⟩
theorem node863 : UpperPrefix a [2,4,7,6,3,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,8,1,0] 30 cert863 (by decide +kernel)

def cert864 : Leaf := ⟨⟨168,172,33,165,197,141,45,0,169⟩,[(7,5)],[(6,3,4),(8,5,7)],⟨7,19,140,88,56,352,194,416,261⟩,⟨7,19,140,88,56,352,194,416,260⟩,[⟨1,1225160110715754362437633,⟨261,277,156,252,188,508,508,444,260⟩⟩,⟨4,1225187834963558197625859,⟨487,487,140,236,172,480,483,416,260⟩⟩]⟩
theorem node864 : UpperPrefix a [2,4,7,6,3,8,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,8,1,5] 30 cert864 (by decide +kernel)

theorem node865 : UpperPrefix a [2,4,7,6,3,8,1] 30 :=
  branch_upper a [2,4,7,6,3,8,1] 30 (by decide) (fin9_cases _
  node863
  (invalid_upper a [2,4,7,6,3,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,1,4] 30 (by decide +kernel))
  node864
  (invalid_upper a [2,4,7,6,3,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,1,8] 30 (by decide +kernel)))

def cert866 : Leaf := ⟨⟨152,136,16,160,192,152,280,31,155⟩,[],[(6,3,4),(8,5,6),(5,6,3)],⟨7,19,140,88,56,352,224,387,263⟩,⟨7,19,140,88,56,352,224,384,260⟩,[⟨0,1210109956728579192521728,⟨94,26,252,92,56,380,252,508,380⟩⟩,⟨1,1210109956728579192520705,⟨93,25,252,92,56,380,252,508,380⟩⟩,⟨2,1210109956728579141142017,⟨91,27,248,88,56,376,248,504,376⟩⟩]⟩
theorem node866 : UpperPrefix a [2,4,7,6,3,8,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,3,8,5] 30 cert866 (by decide +kernel)

theorem node867 : UpperPrefix a [2,4,7,6,3,8] 30 :=
  branch_upper a [2,4,7,6,3,8] 30 (by decide) (fin9_cases _
  node862
  node865
  (invalid_upper a [2,4,7,6,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,4] 30 (by decide +kernel))
  node866
  (invalid_upper a [2,4,7,6,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,8,8] 30 (by decide +kernel)))

theorem node868 : UpperPrefix a [2,4,7,6,3] 30 :=
  branch_upper a [2,4,7,6,3] 30 (by decide) (fin9_cases _
  node858
  node859
  (invalid_upper a [2,4,7,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,3,7] 30 (by decide +kernel))
  node867)

def cert869 : Leaf := ⟨⟨480,484,0,420,196,390,292,100,224⟩,[(2,7)],[(1,6,5),(3,7,2)],⟨7,19,140,88,304,97,194,392,292⟩,⟨7,19,140,88,304,97,194,392,260⟩,[⟨0,1437316166085131414275072,⟨206,478,140,476,444,508,206,396,260⟩⟩,⟨4,2178303395388698152404033,⟨487,355,428,493,288,353,487,428,388⟩⟩]⟩
theorem node869 : UpperPrefix a [2,4,7,6,8,0,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,1,3] 30 cert869 (by decide +kernel)

def cert870 : Leaf := ⟨⟨496,484,352,420,0,390,292,0,232⟩,[(4,7),(7,4)],[(1,6,5)],⟨7,19,140,88,304,97,194,416,268⟩,⟨7,19,140,88,304,97,194,416,260⟩,[⟨0,2414753776313185598964736,⟨334,478,412,476,444,508,478,444,260⟩⟩,⟨3,1212623794785285756366085,⟨103,243,247,242,499,97,242,499,503⟩⟩,⟨4,1266932814550563095053313,⟨487,227,396,460,416,225,226,416,260⟩⟩]⟩
theorem node870 : UpperPrefix a [2,4,7,6,8,0,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,1,5] 30 cert870 (by decide +kernel)

theorem node871 : UpperPrefix a [2,4,7,6,8,0,1] 30 :=
  branch_upper a [2,4,7,6,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,1,2] 30 (by decide +kernel))
  node869
  (invalid_upper a [2,4,7,6,8,0,1,4] 30 (by decide +kernel))
  node870
  (invalid_upper a [2,4,7,6,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,1,8] 30 (by decide +kernel)))

def cert872 : Leaf := ⟨⟨152,140,0,423,143,140,0,47,171⟩,[(2,6),(6,2)],[],⟨7,19,140,88,304,97,200,418,294⟩,⟨7,19,140,88,304,97,200,384,260⟩,[⟨6,1361664861674143797507181,⟨7,147,143,159,435,439,143,384,261⟩⟩,⟨4,1214857673974510810825729,⟨487,419,204,76,288,485,204,384,324⟩⟩,⟨8,1181829443212471702605,⟨103,51,239,127,48,101,239,160,101⟩⟩,⟨5,1210107636215545833985101,⟨71,19,207,95,272,69,207,384,325⟩⟩,⟨1,1210107637376630112911361,⟨101,49,204,92,304,101,204,384,324⟩⟩]⟩
theorem node872 : UpperPrefix a [2,4,7,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,3] 30 cert872 (by decide +kernel)

def cert873 : Leaf := ⟨⟨400,388,272,420,196,406,278,20,152⟩,[],[(5,6,3)],⟨7,19,140,88,304,97,224,386,268⟩,⟨7,19,140,88,304,97,224,386,260⟩,[⟨0,1805153988708901978637312,⟨390,414,396,348,380,508,508,390,260⟩⟩,⟨3,1212623794785285756366085,⟨103,243,247,242,499,97,242,499,503⟩⟩,⟨6,1266894713993261936022541,⟨391,147,399,415,304,161,160,386,389⟩⟩,⟨1,1720123145440383340642305,⟨261,17,396,348,312,381,508,384,260⟩⟩]⟩
theorem node873 : UpperPrefix a [2,4,7,6,8,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,5,1] 30 cert873 (by decide +kernel)

def cert874 : Leaf := ⟨⟨400,388,0,422,134,406,278,22,146⟩,[(2,7)],[(5,6,3),(3,7,2)],⟨7,19,140,88,304,97,224,392,262⟩,⟨7,19,140,88,304,97,224,392,260⟩,[⟨0,1224745921399683060335616,⟨398,478,140,220,508,508,252,396,260⟩⟩,⟨6,2178302221821663710860493,⟨391,275,399,415,306,307,439,399,389⟩⟩]⟩
theorem node874 : UpperPrefix a [2,4,7,6,8,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,0,5,3] 30 cert874 (by decide +kernel)

theorem node875 : UpperPrefix a [2,4,7,6,8,0,5] 30 :=
  branch_upper a [2,4,7,6,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,0,5,0] 30 (by decide +kernel))
  node873
  (invalid_upper a [2,4,7,6,8,0,5,2] 30 (by decide +kernel))
  node874
  (invalid_upper a [2,4,7,6,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,5,8] 30 (by decide +kernel)))

theorem node876 : UpperPrefix a [2,4,7,6,8,0] 30 :=
  branch_upper a [2,4,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,0,0] 30 (by decide +kernel))
  node871
  (invalid_upper a [2,4,7,6,8,0,2] 30 (by decide +kernel))
  node872
  (invalid_upper a [2,4,7,6,8,0,4] 30 (by decide +kernel))
  node875
  (invalid_upper a [2,4,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,0,8] 30 (by decide +kernel)))

def cert877 : Leaf := ⟨⟨368,356,0,292,68,277,308,116,112⟩,[(2,7)],[(0,6,5),(3,7,2)],⟨7,19,140,88,304,98,193,392,292⟩,⟨7,19,140,88,304,98,193,392,260⟩,[⟨7,1227816442136967207169797,⟨279,19,319,122,307,106,123,315,279⟩⟩,⟨1,1437316166085131397496833,⟨205,477,140,476,444,508,197,396,260⟩⟩]⟩
theorem node877 : UpperPrefix a [2,4,7,6,8,1,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,0,3] 30 cert877 (by decide +kernel)

def cert878 : Leaf := ⟨⟨376,360,368,288,0,281,312,0,120⟩,[(4,7),(7,4)],[(0,6,5)],⟨7,19,140,88,304,98,193,416,268⟩,⟨7,19,140,88,304,98,193,416,260⟩,[⟨7,1227816442136967207169797,⟨279,19,319,122,307,106,123,307,279⟩⟩,⟨1,2414753776313185598963713,⟨333,477,412,476,444,508,477,444,260⟩⟩,⟨2,1210255177912871238534145,⟨107,251,184,250,432,106,251,432,256⟩⟩]⟩
theorem node878 : UpperPrefix a [2,4,7,6,8,1,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,0,5] 30 cert878 (by decide +kernel)

theorem node879 : UpperPrefix a [2,4,7,6,8,1,0] 30 :=
  branch_upper a [2,4,7,6,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,0,2] 30 (by decide +kernel))
  node877
  (invalid_upper a [2,4,7,6,8,1,0,4] 30 (by decide +kernel))
  node878
  (invalid_upper a [2,4,7,6,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,0,8] 30 (by decide +kernel)))

def cert880 : Leaf := ⟨⟨304,292,0,423,7,277,0,55,51⟩,[(2,6),(6,2)],[],⟨7,19,140,88,304,98,200,417,293⟩,⟨7,19,140,88,304,98,200,384,260⟩,[⟨3,1229181498937816143507205,⟨407,147,439,242,435,98,224,387,407⟩⟩,⟨6,1361664861674143797507181,⟨7,147,143,159,435,439,143,384,261⟩⟩,⟨7,1227816439876362710429445,⟨279,19,319,122,307,98,104,259,279⟩⟩]⟩
theorem node880 : UpperPrefix a [2,4,7,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,3] 30 cert880 (by decide +kernel)

def cert881 : Leaf := ⟨⟨272,260,273,421,69,277,277,29,25⟩,[],[(5,6,3)],⟨7,19,140,88,304,98,224,393,269⟩,⟨7,19,140,88,304,98,224,384,260⟩,[⟨1,1219571321456631070851073,⟨389,413,140,92,380,508,252,384,260⟩⟩,⟨3,1210109959430837676223749,⟨103,51,247,114,307,98,242,499,375⟩⟩,⟨6,1266885490621225081246733,⟨391,19,399,415,304,34,160,384,389⟩⟩,⟨7,1227816439876362710429445,⟨279,19,319,122,307,98,96,259,279⟩⟩]⟩
theorem node881 : UpperPrefix a [2,4,7,6,8,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,1,5] 30 cert881 (by decide +kernel)

theorem node882 : UpperPrefix a [2,4,7,6,8,1] 30 :=
  branch_upper a [2,4,7,6,8,1] 30 (by decide) (fin9_cases _
  node879
  (invalid_upper a [2,4,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,2] 30 (by decide +kernel))
  node880
  (invalid_upper a [2,4,7,6,8,1,4] 30 (by decide +kernel))
  node881
  (invalid_upper a [2,4,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,1,8] 30 (by decide +kernel)))

def cert883 : Leaf := ⟨⟨408,396,272,388,140,0,286,28,184⟩,[(5,3)],[(6,3,5),(1,7,6)],⟨7,19,140,88,304,104,193,386,292⟩,⟨7,19,140,88,304,104,193,386,260⟩,[⟨5,1210257984385508410143935,⟨79,223,207,223,479,79,197,463,325⟩⟩,⟨0,1720132371346519619535872,⟨406,146,444,380,312,380,508,386,276⟩⟩]⟩
theorem node883 : UpperPrefix a [2,4,7,6,8,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,0,1] 30 cert883 (by decide +kernel)

def cert884 : Leaf := ⟨⟨432,420,307,423,0,0,310,0,179⟩,[(4,7),(5,3),(7,4)],[(6,3,5)],⟨7,19,140,88,304,104,193,416,262⟩,⟨7,19,140,88,304,104,193,416,260⟩,[⟨3,1233869673819361030286597,⟨327,467,471,210,499,98,467,499,327⟩⟩]⟩
theorem node884 : UpperPrefix a [2,4,7,6,8,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,0,5] 30 cert884 (by decide +kernel)

theorem node885 : UpperPrefix a [2,4,7,6,8,3,0] 30 :=
  branch_upper a [2,4,7,6,8,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,6,8,3,0,0] 30 (by decide +kernel))
  node883
  (invalid_upper a [2,4,7,6,8,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,0,4] 30 (by decide +kernel))
  node884
  (invalid_upper a [2,4,7,6,8,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,0,8] 30 (by decide +kernel)))

def cert886 : Leaf := ⟨⟨408,392,274,386,138,0,281,30,186⟩,[(5,3)],[(2,0,7),(6,3,5),(0,7,6)],⟨7,19,140,88,304,104,194,385,292⟩,⟨7,19,140,88,304,104,194,385,260⟩,[⟨5,1212616861783934002279551,⟨79,223,207,223,479,79,207,385,453⟩⟩]⟩
theorem node886 : UpperPrefix a [2,4,7,6,8,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,1,0] 30 cert886 (by decide +kernel)

def cert887 : Leaf := ⟨⟨432,420,307,423,0,0,309,0,179⟩,[(4,7),(5,3),(7,4)],[(6,3,5)],⟨7,19,140,88,304,104,194,416,261⟩,⟨7,19,140,88,304,104,194,416,260⟩,[⟨3,1233869817934549106109701,⟨327,467,471,210,499,96,210,499,327⟩⟩]⟩
theorem node887 : UpperPrefix a [2,4,7,6,8,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,1,5] 30 cert887 (by decide +kernel)

theorem node888 : UpperPrefix a [2,4,7,6,8,3,1] 30 :=
  branch_upper a [2,4,7,6,8,3,1] 30 (by decide) (fin9_cases _
  node886
  (invalid_upper a [2,4,7,6,8,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,1,4] 30 (by decide +kernel))
  node887
  (invalid_upper a [2,4,7,6,8,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,1,8] 30 (by decide +kernel)))

def cert889 : Leaf := ⟨⟨280,268,272,420,12,0,284,31,27⟩,[(5,3)],[(6,3,5),(5,6,3)],⟨7,19,140,88,304,104,224,387,263⟩,⟨7,19,140,88,304,104,224,384,260⟩,[⟨0,1210109959430899466503168,⟨110,50,252,124,312,108,252,508,380⟩⟩,⟨1,1210109959430899466502145,⟨109,49,252,124,312,108,252,508,380⟩⟩,⟨7,1232538806359232355643141,⟨279,275,319,122,307,104,96,259,279⟩⟩]⟩
theorem node889 : UpperPrefix a [2,4,7,6,8,3,5] 30 :=
  Boolean.leaf_sound a [2,4,7,6,8,3,5] 30 cert889 (by decide +kernel)

theorem node890 : UpperPrefix a [2,4,7,6,8,3] 30 :=
  branch_upper a [2,4,7,6,8,3] 30 (by decide) (fin9_cases _
  node885
  node888
  (invalid_upper a [2,4,7,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,4] 30 (by decide +kernel))
  node889
  (invalid_upper a [2,4,7,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,3,8] 30 (by decide +kernel)))

theorem node891 : UpperPrefix a [2,4,7,6,8] 30 :=
  branch_upper a [2,4,7,6,8] 30 (by decide) (fin9_cases _
  node876
  node882
  (invalid_upper a [2,4,7,6,8,2] 30 (by decide +kernel))
  node890
  (invalid_upper a [2,4,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,8,8] 30 (by decide +kernel)))

theorem node892 : UpperPrefix a [2,4,7,6] 30 :=
  branch_upper a [2,4,7,6] 30 (by decide) (fin9_cases _
  node847
  node857
  (invalid_upper a [2,4,7,6,2] 30 (by decide +kernel))
  node868
  (invalid_upper a [2,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,6,7] 30 (by decide +kernel))
  node891)

def cert893 : Local := ⟨⟨248,0,0,228,206,156,0,124,248⟩,[(1,4),(2,6),(6,2)],[(8,3,2),(8,3,6),(0,4,1),(1,5,4)]⟩
theorem node893 : UpperPrefix a [2,4,7,8,0,1,3] 30 :=
  local_sound a [2,4,7,8,0,1,3] 30 cert893 (by decide +kernel)

def cert894 : Leaf := ⟨⟨240,0,368,228,194,144,16,120,248⟩,[(1,4)],[(8,3,2),(0,4,1),(1,5,4)],⟨7,19,140,280,49,98,224,456,332⟩,⟨7,19,140,280,49,98,224,384,260⟩,[⟨2,1210181568749794144298497,⟨115,51,232,506,51,114,224,384,320⟩⟩,⟨3,1210109959150393491668741,⟨119,51,247,307,51,114,242,499,375⟩⟩]⟩
theorem node894 : UpperPrefix a [2,4,7,8,0,1,5] 30 :=
  Boolean.leaf_sound a [2,4,7,8,0,1,5] 30 cert894 (by decide +kernel)

theorem node895 : UpperPrefix a [2,4,7,8,0,1] 30 :=
  branch_upper a [2,4,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,2] 30 (by decide +kernel))
  node893
  (invalid_upper a [2,4,7,8,0,1,4] 30 (by decide +kernel))
  node894
  (invalid_upper a [2,4,7,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,7,8,0,1,8] 30 (by decide +kernel)))

#print axioms node895
end Delivery.FiniteExclusion.Sharp2x7
