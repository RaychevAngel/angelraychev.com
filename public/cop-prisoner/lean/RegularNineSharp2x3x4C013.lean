import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C011
import RegularNineSharp2x3x4C012
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert832 : Leaf := ⟨⟨216,0,144,262,138,138,58,30,158⟩,[(1,6)],[(6,1,0),(8,4,3),(0,6,1)],⟨35,67,14,152,276,112,193,396,300⟩,⟨35,67,14,152,276,112,193,384,288⟩,[⟨5,1212616321369626471859201,⟨15,71,14,152,412,222,207,408,412⟩⟩,⟨2,1210110015523523951451437,⟨35,67,107,251,275,115,195,451,291⟩⟩]⟩
theorem node832 : UpperPrefix a [5,6,1,7,8,4,0] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,4,0] 30 cert832 (by decide +kernel)

def cert833 : Leaf := ⟨⟨88,56,177,289,41,13,57,57,25⟩,[],[(6,1,0),(8,4,3),(2,6,5)],⟨35,67,14,152,276,112,196,393,297⟩,⟨35,67,14,152,276,112,196,384,288⟩,[⟨1,1219570820007029984198657,⟨417,489,508,184,380,120,252,384,288⟩⟩,⟨7,1227816441921454338000231,⟨35,115,319,24,277,115,375,257,291⟩⟩]⟩
theorem node833 : UpperPrefix a [5,6,1,7,8,4,2] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,4,2] 30 cert833 (by decide +kernel)

def cert834 : Leaf := ⟨⟨80,48,49,295,43,11,0,55,31⟩,[(6,3)],[(6,1,0),(7,3,6),(8,4,3)],⟨35,67,14,152,276,112,200,389,293⟩,⟨35,67,14,152,276,112,200,384,288⟩,[⟨2,1210107709680514737692013,⟨35,67,107,251,275,115,235,385,291⟩⟩,⟨3,1210255139236440288806177,⟨35,67,6,144,405,243,192,385,291⟩⟩]⟩
theorem node834 : UpperPrefix a [5,6,1,7,8,4,3] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,4,3] 30 cert834 (by decide +kernel)

theorem node835 : UpperPrefix a [5,6,1,7,8,4] 30 :=
  branch_upper a [5,6,1,7,8,4] 30 (by decide) (fin9_cases _
  node832
  (invalid_upper a [5,6,1,7,8,4,1] 30 (by decide +kernel))
  node833
  node834
  (invalid_upper a [5,6,1,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,4,8] 30 (by decide +kernel)))

theorem node836 : UpperPrefix a [5,6,1,7,8] 30 :=
  branch_upper a [5,6,1,7,8] 30 (by decide) (fin9_cases _
  node823
  (invalid_upper a [5,6,1,7,8,1] 30 (by decide +kernel))
  node827
  node831
  node835
  (invalid_upper a [5,6,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,8] 30 (by decide +kernel)))

theorem node837 : UpperPrefix a [5,6,1,7] 30 :=
  branch_upper a [5,6,1,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,1,7,0] [5,6,0,1,7] 30 (by decide +kernel) node746)
  (invalid_upper a [5,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,2] 30 (by decide +kernel))
  node822
  (invalid_upper a [5,6,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,7] 30 (by decide +kernel))
  node836)

def cert838 : Local := ⟨⟨468,0,432,166,0,0,310,54,150⟩,[(1,5),(4,2),(5,1)],[(6,1,0),(3,4,4),(0,5,0)]⟩
theorem node838 : UpperPrefix a [5,6,1,8,3,0] 30 :=
  local_sound a [5,6,1,8,3,0] 30 cert838 (by decide +kernel)

def cert839 : Leaf := ⟨⟨320,288,305,39,0,275,307,51,151⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,14,280,28,100,209,401,433⟩,⟨35,67,14,280,28,100,192,384,288⟩,[⟨7,1208926976016965415519591,⟨35,119,63,285,29,119,127,285,319⟩⟩,⟨2,1210181496375334599152929,⟨35,67,202,475,218,99,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,14,265,12,103,192,385,291⟩⟩]⟩
theorem node839 : UpperPrefix a [5,6,1,8,3,2] 30 :=
  Boolean.leaf_sound a [5,6,1,8,3,2] 30 cert839 (by decide +kernel)

def cert840 : Leaf := ⟨⟨324,292,289,39,0,263,295,39,135⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,14,280,28,112,197,389,421⟩,⟨35,67,14,280,28,112,192,384,288⟩,[⟨4,1361592948191995398084385,⟨483,67,206,463,206,487,192,387,483⟩⟩,⟨7,1208926976016965415519591,⟨35,119,63,285,29,119,127,285,319⟩⟩]⟩
theorem node840 : UpperPrefix a [5,6,1,8,3,4] 30 :=
  Boolean.leaf_sound a [5,6,1,8,3,4] 30 cert840 (by decide +kernel)

def cert841 : Leaf := ⟨⟨336,304,305,39,0,0,311,55,23⟩,[(4,2),(5,6)],[(6,1,0),(3,4,4),(7,5,5)],⟨35,67,14,280,28,224,213,405,309⟩,⟨35,67,14,280,28,224,192,384,288⟩,[⟨2,1210107567535651498804579,⟨35,99,11,281,24,227,227,385,291⟩⟩]⟩
theorem node841 : UpperPrefix a [5,6,1,8,3,7] 30 :=
  Boolean.leaf_sound a [5,6,1,8,3,7] 30 cert841 (by decide +kernel)

theorem node842 : UpperPrefix a [5,6,1,8,3] 30 :=
  branch_upper a [5,6,1,8,3] 30 (by decide) (fin9_cases _
  node838
  (invalid_upper a [5,6,1,8,3,1] 30 (by decide +kernel))
  node839
  (invalid_upper a [5,6,1,8,3,3] 30 (by decide +kernel))
  node840
  (invalid_upper a [5,6,1,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,3,6] 30 (by decide +kernel))
  node841
  (invalid_upper a [5,6,1,8,3,8] 30 (by decide +kernel)))

def cert843 : Leaf := ⟨⟨476,0,432,164,296,0,316,60,156⟩,[(1,5),(5,1)],[(6,1,0),(0,5,0)],⟨35,67,14,280,148,97,220,412,316⟩,⟨35,67,14,280,148,97,192,384,288⟩,[⟨1,1229181859014683858567169,⟨33,97,508,472,476,97,192,384,288⟩⟩]⟩
theorem node843 : UpperPrefix a [5,6,1,8,7,0] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,0] 30 cert843 (by decide +kernel)

def cert844 : Leaf := ⟨⟨460,0,416,164,296,392,300,60,156⟩,[(1,6)],[(6,1,0),(0,6,1)],⟨35,67,14,280,148,100,193,408,312⟩,⟨35,67,14,280,148,100,193,384,288⟩,[⟨1,1463316851998074237616129,⟨505,457,508,408,444,508,457,392,440⟩⟩,⟨4,1210110160200562472252733,⟨35,67,47,367,231,103,195,451,291⟩⟩]⟩
theorem node844 : UpperPrefix a [5,6,1,8,7,2,0] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,2,0] 30 cert844 (by decide +kernel)

def cert845 : Leaf := ⟨⟨64,32,33,167,35,11,307,51,151⟩,[],[(6,1,0),(8,3,6),(3,6,5)],⟨35,67,14,280,148,100,200,401,305⟩,⟨35,67,14,280,148,100,200,384,288⟩,[⟨2,1210181568432928637080865,⟨35,67,202,475,208,99,202,385,291⟩⟩,⟨4,1210107567604920749180263,⟨35,103,47,265,133,103,239,385,291⟩⟩,⟨7,1208926975985302849504615,⟨35,103,47,281,21,103,111,257,291⟩⟩]⟩
theorem node845 : UpperPrefix a [5,6,1,8,7,2,3] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,2,3] 30 cert845 (by decide +kernel)

def cert846 : Leaf := ⟨⟨80,48,49,39,299,19,0,59,31⟩,[(6,4)],[(6,1,0),(7,4,6)],⟨35,67,14,280,148,100,208,393,297⟩,⟨35,67,14,280,148,100,208,384,288⟩,[⟨8,1182034744023595414909,⟨35,67,47,127,247,103,243,129,35⟩⟩,⟨2,1210181784605710750864673,⟨35,67,202,475,208,99,208,385,291⟩⟩,⟨3,1210107854077176717571449,⟨35,67,7,371,247,103,243,385,291⟩⟩]⟩
theorem node846 : UpperPrefix a [5,6,1,8,7,2,4] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,2,4] 30 cert846 (by decide +kernel)

theorem node847 : UpperPrefix a [5,6,1,8,7,2] 30 :=
  branch_upper a [5,6,1,8,7,2] 30 (by decide) (fin9_cases _
  node844
  (invalid_upper a [5,6,1,8,7,2,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,2,2] 30 (by decide +kernel))
  node845
  node846
  (invalid_upper a [5,6,1,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,2,8] 30 (by decide +kernel)))

def cert848 : Leaf := ⟨⟨204,0,128,134,266,134,46,30,158⟩,[(1,6)],[(6,1,0),(0,6,1)],⟨35,67,14,280,148,104,193,404,308⟩,⟨35,67,14,280,148,104,193,384,288⟩,[⟨4,1210110159637612527220013,⟨39,67,47,367,199,111,195,451,295⟩⟩,⟨5,1212468747421428399244289,⟨7,87,14,408,156,94,223,408,412⟩⟩,⟨8,1184340024082864141613,⟨39,67,47,127,215,111,195,195,39⟩⟩]⟩
theorem node848 : UpperPrefix a [5,6,1,8,7,3,0] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,3,0] 30 cert848 (by decide +kernel)

def cert849 : Leaf := ⟨⟨452,420,417,165,0,389,0,53,149⟩,[(4,6),(6,4)],[(6,1,0)],⟨35,67,14,280,148,104,196,401,305⟩,⟨35,67,14,280,148,104,196,384,288⟩,[⟨1,1219571108593639581810689,⟨425,505,508,376,252,120,252,384,288⟩⟩,⟨3,1361592587909796564325665,⟨419,83,214,467,212,499,212,385,419⟩⟩,⟨4,1210107853794603313460525,⟨39,67,47,367,199,111,199,385,295⟩⟩]⟩
theorem node849 : UpperPrefix a [5,6,1,8,7,3,2] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,3,2] 30 cert849 (by decide +kernel)

def cert850 : Leaf := ⟨⟨76,44,33,39,299,23,0,47,15⟩,[(6,4)],[(6,1,0),(7,4,6),(4,6,5)],⟨35,67,14,280,148,104,208,389,293⟩,⟨35,67,14,280,148,104,208,384,288⟩,[⟨8,1182034181073650349357,⟨39,67,47,127,215,111,210,129,39⟩⟩]⟩
theorem node850 : UpperPrefix a [5,6,1,8,7,3,4] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,3,4] 30 cert850 (by decide +kernel)

theorem node851 : UpperPrefix a [5,6,1,8,7,3] 30 :=
  branch_upper a [5,6,1,8,7,3] 30 (by decide) (fin9_cases _
  node848
  (invalid_upper a [5,6,1,8,7,3,1] 30 (by decide +kernel))
  node849
  (invalid_upper a [5,6,1,8,7,3,3] 30 (by decide +kernel))
  node850
  (invalid_upper a [5,6,1,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,3,8] 30 (by decide +kernel)))

def cert852 : Leaf := ⟨⟨76,0,32,38,298,142,46,46,30⟩,[(1,6)],[(6,1,0),(7,4,5),(0,6,1)],⟨35,67,14,280,148,112,193,396,300⟩,⟨35,67,14,280,148,112,193,384,288⟩,[⟨4,1210183802217244304463137,⟨35,67,206,463,198,99,195,451,291⟩⟩,⟨8,1184340587032809174333,⟨35,67,47,127,247,115,195,195,35⟩⟩]⟩
theorem node852 : UpperPrefix a [5,6,1,8,7,4,0] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,4,0] 30 cert852 (by decide +kernel)

def cert853 : Local := ⟨⟨344,312,305,35,0,399,0,59,27⟩,[(4,6),(6,4)],[(6,1,0),(7,4,5),(2,6,5)]⟩
theorem node853 : UpperPrefix a [5,6,1,8,7,4,2] 30 :=
  local_sound a [5,6,1,8,7,4,2] 30 cert853 (by decide +kernel)

def cert854 : Leaf := ⟨⟨92,28,16,6,10,142,278,62,30⟩,[],[(5,0,7),(6,1,0),(8,3,6),(7,4,5)],⟨35,67,14,280,148,112,200,385,292⟩,⟨35,67,14,280,148,112,200,385,288⟩,[⟨0,1923187505879206156043264,⟨302,366,302,376,508,376,504,508,296⟩⟩]⟩
theorem node854 : UpperPrefix a [5,6,1,8,7,4,3,0] 30 :=
  Boolean.leaf_sound a [5,6,1,8,7,4,3,0] 30 cert854 (by decide +kernel)

def cert855 : Local := ⟨⟨88,56,49,35,0,139,307,59,27⟩,[(4,7)],[(6,1,0),(8,3,6),(7,4,5),(2,7,4)]⟩
theorem node855 : UpperPrefix a [5,6,1,8,7,4,3,2] 30 :=
  local_sound a [5,6,1,8,7,4,3,2] 30 cert855 (by decide +kernel)

theorem node856 : UpperPrefix a [5,6,1,8,7,4,3] 30 :=
  branch_upper a [5,6,1,8,7,4,3] 30 (by decide) (fin9_cases _
  node854
  (invalid_upper a [5,6,1,8,7,4,3,1] 30 (by decide +kernel))
  node855
  (invalid_upper a [5,6,1,8,7,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,3,8] 30 (by decide +kernel)))

theorem node857 : UpperPrefix a [5,6,1,8,7,4] 30 :=
  branch_upper a [5,6,1,8,7,4] 30 (by decide) (fin9_cases _
  node852
  (invalid_upper a [5,6,1,8,7,4,1] 30 (by decide +kernel))
  node853
  node856
  (invalid_upper a [5,6,1,8,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,4,8] 30 (by decide +kernel)))

theorem node858 : UpperPrefix a [5,6,1,8,7] 30 :=
  branch_upper a [5,6,1,8,7] 30 (by decide) (fin9_cases _
  node843
  (invalid_upper a [5,6,1,8,7,1] 30 (by decide +kernel))
  node847
  node851
  node857
  (invalid_upper a [5,6,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,7,8] 30 (by decide +kernel)))

theorem node859 : UpperPrefix a [5,6,1,8] 30 :=
  branch_upper a [5,6,1,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,1,8,0] [5,6,0,1,8] 30 (by decide +kernel) node747)
  (invalid_upper a [5,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,2] 30 (by decide +kernel))
  node842
  (invalid_upper a [5,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,8,6] 30 (by decide +kernel))
  node858
  (invalid_upper a [5,6,1,8,8] 30 (by decide +kernel)))

theorem node860 : UpperPrefix a [5,6,1] 30 :=
  branch_upper a [5,6,1] 30 (by decide) (fin9_cases _
  node805
  (invalid_upper a [5,6,1,1] 30 (by decide +kernel))
  node817
  (invalid_upper a [5,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,6] 30 (by decide +kernel))
  node837
  node859)

theorem node861 : UpperPrefix a [5,6,4,0] 30 :=
  branch_upper a [5,6,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,4,0,1] [5,6,0,1,3] 30 (by decide +kernel) node741)
  (invalid_upper a [5,6,4,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,4,0,3] [5,6,0,2,3] 30 (by decide +kernel) node750)
  (invalid_upper a [5,6,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,4,0,7] [5,6,0,7,3] 30 (by decide +kernel) node767)
  (PrefixConjugacy.upper aut8 [5,6,4,0,8] [5,6,0,8,3] 30 (by decide +kernel) node786))

theorem node862 : UpperPrefix a [5,6,4,1] 30 :=
  branch_upper a [5,6,4,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,4,1,0] [5,6,0,2,1] 30 (by decide +kernel) node749)
  (invalid_upper a [5,6,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,4,1,3] [5,6,1,2,3] 30 (by decide +kernel) node806)
  (invalid_upper a [5,6,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,4,1,7] [5,6,1,7,3] 30 (by decide +kernel) node822)
  (PrefixConjugacy.upper aut8 [5,6,4,1,8] [5,6,1,8,3] 30 (by decide +kernel) node842))

def cert863 : Leaf := ⟨⟨448,416,0,0,427,395,299,43,139⟩,[(2,3),(3,2)],[(6,1,0),(4,2,2),(4,2,3),(2,3,2),(2,3,3)],⟨35,67,28,28,415,491,459,395,427⟩,⟨35,67,28,28,20,96,192,384,288⟩,[⟨3,1210107565283850612393249,⟨35,67,20,20,20,99,192,385,291⟩⟩]⟩
theorem node863 : UpperPrefix a [5,6,4,2] 30 :=
  Boolean.leaf_sound a [5,6,4,2] 30 cert863 (by decide +kernel)

def cert864 : Leaf := ⟨⟨200,168,0,0,43,395,299,43,139⟩,[(2,3),(3,2)],[(6,1,0),(4,2,2),(4,2,3),(2,3,2),(2,3,3)],⟨35,67,28,28,148,363,459,395,299⟩,⟨35,67,28,28,148,96,192,384,288⟩,[⟨8,1181745682449734059297,⟨47,95,28,28,156,127,220,157,47⟩⟩]⟩
theorem node864 : UpperPrefix a [5,6,4,2,7] 30 :=
  Boolean.leaf_sound a [5,6,4,2,7] 30 cert864 (by decide +kernel)

def cert865 : Leaf := ⟨⟨192,160,0,292,168,143,47,47,143⟩,[(2,3)],[(6,1,0),(4,2,2),(8,4,3)],⟨35,67,28,152,276,111,207,399,303⟩,⟨35,67,28,152,276,96,192,384,288⟩,[⟨0,1210107565292673601373184,⟨34,78,28,156,276,108,220,412,288⟩⟩,⟨1,1210107565292673601372161,⟨33,77,28,156,276,108,220,412,288⟩⟩,⟨2,1210107565283851685086497,⟨35,67,24,152,273,99,192,385,291⟩⟩,⟨3,1210107565283850612393249,⟨35,67,20,144,277,99,192,385,291⟩⟩]⟩
theorem node865 : UpperPrefix a [5,6,4,7,8] 30 :=
  Boolean.leaf_sound a [5,6,4,7,8] 30 cert865 (by decide +kernel)

theorem node866 : UpperPrefix a [5,6,4,7] 30 :=
  branch_upper a [5,6,4,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,4,7,0] [5,6,0,2,7] 30 (by decide +kernel) node755)
  (PrefixConjugacy.upper aut4 [5,6,4,7,1] [5,6,1,2,7] 30 (by decide +kernel) node811)
  (invalid_upper a [5,6,4,7,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut4 [5,6,4,7,3] [5,6,4,2,7] 30 (by decide +kernel) node864)
  (invalid_upper a [5,6,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,7,7] 30 (by decide +kernel))
  node865)

def cert867 : Leaf := ⟨⟨328,296,0,0,43,395,299,43,139⟩,[(2,3),(3,2)],[(6,1,0),(4,2,2),(4,2,3),(2,3,2),(2,3,3)],⟨35,67,28,28,276,235,203,395,427⟩,⟨35,67,28,28,276,96,192,384,288⟩,[⟨7,1208926973689585491526945,⟨35,79,28,28,285,111,92,285,319⟩⟩]⟩
theorem node867 : UpperPrefix a [5,6,4,2,8] 30 :=
  Boolean.leaf_sound a [5,6,4,2,8] 30 cert867 (by decide +kernel)

def cert868 : Leaf := ⟨⟨320,288,0,132,264,399,303,47,143⟩,[(2,3)],[(6,1,0),(4,2,2)],⟨35,67,28,280,148,111,207,399,303⟩,⟨35,67,28,280,148,96,192,384,288⟩,[⟨0,1210107565297063062144000,⟨34,86,28,284,156,116,220,412,288⟩⟩,⟨1,1210107565297063062142977,⟨33,85,28,284,156,116,220,412,288⟩⟩,⟨2,1210107565283851685086497,⟨35,67,24,281,144,99,192,385,291⟩⟩,⟨3,1210107565283850612393249,⟨35,67,20,273,148,99,192,385,291⟩⟩,⟨5,1210107564171163155301377,⟨3,87,28,284,156,84,220,412,256⟩⟩,⟨7,1208926973663134276928801,⟨35,67,28,285,20,99,64,257,291⟩⟩]⟩
theorem node868 : UpperPrefix a [5,6,4,8,7] 30 :=
  Boolean.leaf_sound a [5,6,4,8,7] 30 cert868 (by decide +kernel)

theorem node869 : UpperPrefix a [5,6,4,8] 30 :=
  branch_upper a [5,6,4,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,4,8,0] [5,6,0,2,8] 30 (by decide +kernel) node756)
  (PrefixConjugacy.upper aut4 [5,6,4,8,1] [5,6,1,2,8] 30 (by decide +kernel) node816)
  (invalid_upper a [5,6,4,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut4 [5,6,4,8,3] [5,6,4,2,8] 30 (by decide +kernel) node867)
  (invalid_upper a [5,6,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,8,6] 30 (by decide +kernel))
  node868
  (invalid_upper a [5,6,4,8,8] 30 (by decide +kernel)))

theorem node870 : UpperPrefix a [5,6,4] 30 :=
  branch_upper a [5,6,4] 30 (by decide) (fin9_cases _
  node861
  node862
  node863
  (invalid_upper a [5,6,4,3] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,4,6] 30 (by decide +kernel))
  node866
  node869)

theorem node871 : UpperPrefix a [5,6,7,0] 30 :=
  branch_upper a [5,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,7,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,7,0,1] [5,6,0,1,7] 30 (by decide +kernel) node746)
  (invalid_upper a [5,6,7,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,7,0,3] [5,6,0,2,7] 30 (by decide +kernel) node755)
  (invalid_upper a [5,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,0,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,7,0,8] [5,6,0,8,7] 30 (by decide +kernel) node802))

theorem node872 : UpperPrefix a [5,6,7,1] 30 :=
  branch_upper a [5,6,7,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,7,1,0] [5,6,0,7,1] 30 (by decide +kernel) node762)
  (invalid_upper a [5,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,7,1,3] [5,6,1,2,7] 30 (by decide +kernel) node811)
  (invalid_upper a [5,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,1,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,7,1,8] [5,6,1,8,7] 30 (by decide +kernel) node858))

theorem node873 : UpperPrefix a [5,6,7,2] 30 :=
  branch_upper a [5,6,7,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,7,2,0] [5,6,0,7,3] 30 (by decide +kernel) node767)
  (PrefixConjugacy.upper aut4 [5,6,7,2,1] [5,6,1,7,3] 30 (by decide +kernel) node822)
  (invalid_upper a [5,6,7,2,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,7,2,3] [5,6,4,2,7] 30 (by decide +kernel) node864)
  (invalid_upper a [5,6,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,2,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,7,2,8] [5,6,4,8,7] 30 (by decide +kernel) node868))

theorem node874 : UpperPrefix a [5,6,7,8] 30 :=
  branch_upper a [5,6,7,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,7,8,0] [5,6,0,7,8] 30 (by decide +kernel) node783)
  (PrefixConjugacy.upper aut4 [5,6,7,8,1] [5,6,1,7,8] 30 (by decide +kernel) node836)
  (invalid_upper a [5,6,7,8,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut4 [5,6,7,8,3] [5,6,4,7,8] 30 (by decide +kernel) node865)
  (invalid_upper a [5,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,8,8] 30 (by decide +kernel)))

theorem node875 : UpperPrefix a [5,6,7] 30 :=
  branch_upper a [5,6,7] 30 (by decide) (fin9_cases _
  node871
  node872
  node873
  (invalid_upper a [5,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,7,7] 30 (by decide +kernel))
  node874)

theorem node876 : UpperPrefix a [5,6,8,0] 30 :=
  branch_upper a [5,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,8,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,8,0,1] [5,6,0,1,8] 30 (by decide +kernel) node747)
  (invalid_upper a [5,6,8,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,8,0,3] [5,6,0,2,8] 30 (by decide +kernel) node756)
  (invalid_upper a [5,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,8,0,7] [5,6,0,7,8] 30 (by decide +kernel) node783)
  (invalid_upper a [5,6,8,0,8] 30 (by decide +kernel)))

theorem node877 : UpperPrefix a [5,6,8,1] 30 :=
  branch_upper a [5,6,8,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,8,1,0] [5,6,0,8,1] 30 (by decide +kernel) node785)
  (invalid_upper a [5,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,8,1,3] [5,6,1,2,8] 30 (by decide +kernel) node816)
  (invalid_upper a [5,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,8,1,7] [5,6,1,7,8] 30 (by decide +kernel) node836)
  (invalid_upper a [5,6,8,1,8] 30 (by decide +kernel)))

theorem node878 : UpperPrefix a [5,6,8,2] 30 :=
  branch_upper a [5,6,8,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,8,2,0] [5,6,0,8,3] 30 (by decide +kernel) node786)
  (PrefixConjugacy.upper aut4 [5,6,8,2,1] [5,6,1,8,3] 30 (by decide +kernel) node842)
  (invalid_upper a [5,6,8,2,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,8,2,3] [5,6,4,2,8] 30 (by decide +kernel) node867)
  (invalid_upper a [5,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,2,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,8,2,7] [5,6,4,7,8] 30 (by decide +kernel) node865)
  (invalid_upper a [5,6,8,2,8] 30 (by decide +kernel)))

theorem node879 : UpperPrefix a [5,6,8,7] 30 :=
  branch_upper a [5,6,8,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,8,7,0] [5,6,0,8,7] 30 (by decide +kernel) node802)
  (PrefixConjugacy.upper aut4 [5,6,8,7,1] [5,6,1,8,7] 30 (by decide +kernel) node858)
  (invalid_upper a [5,6,8,7,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut4 [5,6,8,7,3] [5,6,4,8,7] 30 (by decide +kernel) node868)
  (invalid_upper a [5,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,7,8] 30 (by decide +kernel)))

theorem node880 : UpperPrefix a [5,6,8] 30 :=
  branch_upper a [5,6,8] 30 (by decide) (fin9_cases _
  node876
  node877
  node878
  (invalid_upper a [5,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,8,6] 30 (by decide +kernel))
  node879
  (invalid_upper a [5,6,8,8] 30 (by decide +kernel)))

theorem node881 : UpperPrefix a [5,6] 30 :=
  branch_upper a [5,6] 30 (by decide) (fin9_cases _
  node804
  node860
  (invalid_upper a [5,6,2] 30 (by decide +kernel))
  (invalid_upper a [5,6,3] 30 (by decide +kernel))
  node870
  (invalid_upper a [5,6,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,6] 30 (by decide +kernel))
  node875
  node880)

def cert882 : Leaf := ⟨⟨468,372,18,5,0,404,308,116,212⟩,[(4,2)],[(1,3,2),(3,4,4)],⟨35,131,13,26,28,372,468,468,372⟩,⟨35,131,13,26,28,96,192,384,288⟩,[⟨0,1304739723373914195231744,⟨34,130,508,506,508,96,192,384,288⟩⟩,⟨5,1210107564158982974866433,⟨31,159,29,30,28,64,192,384,256⟩⟩,⟨6,1210106412363378274862081,⟨63,159,29,30,28,32,128,384,288⟩⟩,⟨7,1208926973664165470405633,⟨63,31,29,30,28,96,64,256,288⟩⟩,⟨8,1181745670253707002881,⟨63,159,29,30,28,96,192,128,32⟩⟩]⟩
theorem node882 : UpperPrefix a [5,7,0,1,3] 30 :=
  Boolean.leaf_sound a [5,7,0,1,3] 30 cert882 (by decide +kernel)

def cert883 : Leaf := ⟨⟨92,124,114,100,0,0,316,124,92⟩,[(4,5),(5,4)],[(1,3,2)],⟨35,131,13,26,84,100,472,408,312⟩,⟨35,131,13,26,84,100,192,384,288⟩,[⟨0,1271618468290978286404608,⟨506,458,508,506,500,500,192,384,304⟩⟩,⟨7,1251428272574110195516425,⟨319,271,269,319,116,116,64,256,304⟩⟩,⟨8,1181748490584614274169,⟨63,143,13,63,127,127,255,132,61⟩⟩]⟩
theorem node883 : UpperPrefix a [5,7,0,1,6,2] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,2] 30 cert883 (by decide +kernel)

def cert884 : Leaf := ⟨⟨216,120,242,225,0,144,56,120,216⟩,[(4,6)],[(1,3,2),(2,6,4)],⟨35,131,13,26,84,104,196,400,304⟩,⟨35,131,13,26,84,104,196,384,288⟩,[⟨8,1184095262588056470779,⟨127,255,61,127,127,127,255,255,61⟩⟩,⟨0,1796825068007113263940608,⟨418,130,508,506,500,504,500,384,416⟩⟩]⟩
theorem node884 : UpperPrefix a [5,7,0,1,6,3,2] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,3,2] 30 cert884 (by decide +kernel)

def cert885 : Leaf := ⟨⟨140,44,162,165,168,148,44,44,140⟩,[],[(1,3,2),(4,6,5)],⟨35,131,13,26,84,104,208,388,292⟩,⟨35,131,13,26,84,104,208,384,288⟩,[⟨8,1184095262588056470779,⟨127,255,61,127,127,127,255,255,61⟩⟩,⟨6,1368646954303854566657825,⟨423,387,399,26,158,431,154,387,423⟩⟩,⟨0,1304739867207627294376960,⟨34,130,508,506,500,104,464,384,288⟩⟩]⟩
theorem node885 : UpperPrefix a [5,7,0,1,6,3,4] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,3,4] 30 cert885 (by decide +kernel)

def cert886 : Leaf := ⟨⟨156,60,178,164,168,148,0,56,220⟩,[(6,7)],[(1,3,2),(8,6,6)],⟨35,131,13,26,84,104,448,388,304⟩,⟨35,131,13,26,84,104,448,388,288⟩,[⟨0,1956428783829794044249088,⟨362,506,508,506,500,360,464,500,288⟩⟩,⟨6,1212467595603784057980193,⟨39,131,13,26,30,47,387,391,423⟩⟩]⟩
theorem node886 : UpperPrefix a [5,7,0,1,6,3,8,2] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,3,8,2] 30 cert886 (by decide +kernel)

def cert887 : Leaf := ⟨⟨200,120,226,225,168,128,0,108,204⟩,[(6,7)],[(1,3,2),(8,6,6)],⟨35,131,13,26,84,104,448,400,292⟩,⟨35,131,13,26,84,104,448,400,288⟩,[⟨0,1304815960026931346277376,⟨34,194,508,506,500,232,448,464,288⟩⟩,⟨2,1210109878515598364869883,⟨35,235,9,59,123,107,491,507,289⟩⟩,⟨4,1422616399165167428961289,⟨359,451,301,367,324,365,448,448,292⟩⟩]⟩
theorem node887 : UpperPrefix a [5,7,0,1,6,3,8,4] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,3,8,4] 30 cert887 (by decide +kernel)

theorem node888 : UpperPrefix a [5,7,0,1,6,3,8] 30 :=
  branch_upper a [5,7,0,1,6,3,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,6,3,8,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,3,8,1] 30 (by decide +kernel))
  node886
  (invalid_upper a [5,7,0,1,6,3,8,3] 30 (by decide +kernel))
  node887
  (invalid_upper a [5,7,0,1,6,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,3,8,8] 30 (by decide +kernel)))

theorem node889 : UpperPrefix a [5,7,0,1,6,3] 30 :=
  branch_upper a [5,7,0,1,6,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,6,3,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,3,1] 30 (by decide +kernel))
  node884
  (invalid_upper a [5,7,0,1,6,3,3] 30 (by decide +kernel))
  node885
  (invalid_upper a [5,7,0,1,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,3,7] 30 (by decide +kernel))
  node888)

def cert890 : Leaf := ⟨⟨28,60,50,165,168,0,316,60,28⟩,[(5,4)],[(1,3,2),(6,4,5)],⟨35,131,13,26,84,112,460,396,300⟩,⟨35,131,13,26,84,112,192,384,288⟩,[⟨8,1181748490584614274169,⟨63,143,13,63,127,127,255,132,61⟩⟩,⟨0,1229033997465034043687936,⟨34,130,508,58,500,112,192,384,288⟩⟩,⟨7,1246705906089041392043017,⟨35,3,269,319,116,112,64,256,288⟩⟩]⟩
theorem node890 : UpperPrefix a [5,7,0,1,6,4] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,4] 30 cert890 (by decide +kernel)

def cert891 : Leaf := ⟨⟨472,376,210,193,0,152,24,120,216⟩,[(4,6)],[(1,3,2),(2,6,4)],⟨35,131,13,26,84,352,196,408,312⟩,⟨35,131,13,26,84,352,196,384,288⟩,[⟨0,1266887007072335032222720,⟨34,130,508,506,500,368,500,384,288⟩⟩,⟨5,1210107600191903162434561,⟨95,223,29,94,84,336,212,384,256⟩⟩,⟨8,1181781703173894571009,⟨127,223,29,94,84,112,212,128,32⟩⟩]⟩
theorem node891 : UpperPrefix a [5,7,0,1,6,8,2] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,8,2] 30 cert891 (by decide +kernel)

def cert892 : Leaf := ⟨⟨340,372,82,69,8,20,20,116,84⟩,[],[(1,3,2),(3,6,4)],⟨35,131,13,26,84,352,200,404,308⟩,⟨35,131,13,26,84,352,200,384,288⟩,[⟨7,1780333320911708336423945,⟨319,271,269,319,372,372,381,256,304⟩⟩,⟨0,1304739579540201096086528,⟨34,130,508,506,500,352,232,384,288⟩⟩,⟨5,1210107600187505115923457,⟨95,223,29,94,84,320,216,384,256⟩⟩,⟨8,1181781698775848059905,⟨127,223,29,94,84,96,216,128,32⟩⟩]⟩
theorem node892 : UpperPrefix a [5,7,0,1,6,8,3] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,8,3] 30 cert892 (by decide +kernel)

def cert893 : Leaf := ⟨⟨400,304,434,416,416,144,292,56,152⟩,[],[(1,3,2),(2,7,6)],⟨35,131,13,26,84,352,208,388,296⟩,⟨35,131,13,26,84,352,208,388,288⟩,[⟨0,1281130381845984359482368,⟨362,506,508,506,500,352,240,500,288⟩⟩,⟨6,1363887694332837502340897,⟨423,131,143,26,30,431,154,391,423⟩⟩,⟨3,1210109911668052565525731,⟨99,243,5,83,87,355,243,503,289⟩⟩]⟩
theorem node893 : UpperPrefix a [5,7,0,1,6,8,4,2] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,8,4,2] 30 cert893 (by decide +kernel)

def cert894 : Leaf := ⟨⟨268,300,290,421,296,12,300,36,12⟩,[],[(1,3,2)],⟨35,131,13,26,84,352,208,392,292⟩,⟨35,131,13,26,84,352,208,392,288⟩,[⟨4,1625786499054473013476473,⟨35,135,399,431,487,355,487,399,289⟩⟩,⟨6,1366276547690382922829601,⟨423,391,399,26,158,431,158,399,423⟩⟩,⟨0,1304666087549681850647552,⟨34,162,508,506,500,352,496,488,288⟩⟩,⟨7,1624495226974810902889481,⟨35,7,269,319,372,368,372,269,288⟩⟩]⟩
theorem node894 : UpperPrefix a [5,7,0,1,6,8,4,3] 30 :=
  Boolean.leaf_sound a [5,7,0,1,6,8,4,3] 30 cert894 (by decide +kernel)

theorem node895 : UpperPrefix a [5,7,0,1,6,8,4] 30 :=
  branch_upper a [5,7,0,1,6,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,7,0,1,6,8,4,0] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,4,1] 30 (by decide +kernel))
  node893
  node894
  (invalid_upper a [5,7,0,1,6,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,7,0,1,6,8,4,8] 30 (by decide +kernel)))

#print axioms node895
end Delivery.FiniteExclusion.Sharp2x3x4
