import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C011
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert768 : Leaf := ⟨⟨0,188,176,292,169,0,60,60,157⟩,[(0,5),(5,1)],[(6,1,0),(6,1,5),(8,4,3),(1,5,0)],⟨35,67,13,152,276,98,220,412,316⟩,⟨35,67,13,152,276,98,192,384,288⟩,[⟨0,1210255427537188405904384,⟨34,98,12,216,476,98,192,384,288⟩⟩]⟩
theorem node768 : UpperPrefix a [5,6,0,7,8,1] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,1] 30 cert768 (by decide +kernel)

def cert769 : Leaf := ⟨⟨216,184,176,288,168,152,56,56,156⟩,[],[(6,1,0),(8,4,3),(1,6,1)],⟨35,67,13,152,276,100,194,408,312⟩,⟨35,67,13,152,276,100,194,384,288⟩,[⟨0,1463316851998074237617152,⟨506,458,508,408,444,508,194,392,440⟩⟩,⟨2,1210257877425016950320417,⟨35,67,75,218,475,99,194,451,291⟩⟩]⟩
theorem node769 : UpperPrefix a [5,6,0,7,8,2,1] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,2,1] 30 cert769 (by decide +kernel)

def cert770 : Local := ⟨⟨84,52,50,295,35,27,0,55,23⟩,[(6,3)],[(6,1,0),(7,3,6),(8,4,3),(3,6,5)]⟩
theorem node770 : UpperPrefix a [5,6,0,7,8,2,3] 30 :=
  local_sound a [5,6,0,7,8,2,3] 30 cert770 (by decide +kernel)

def cert771 : Leaf := ⟨⟨208,176,178,0,171,147,0,59,155⟩,[(3,6),(6,3)],[(6,1,0),(8,4,3),(8,4,6)],⟨35,67,13,152,276,100,208,394,298⟩,⟨35,67,13,152,276,100,208,384,288⟩,[⟨2,1361666446939024326159649,⟨419,75,75,218,475,491,218,385,419⟩⟩,⟨3,1210107709539776176643381,⟨35,67,103,211,311,103,211,385,291⟩⟩]⟩
theorem node771 : UpperPrefix a [5,6,0,7,8,2,4] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,2,4] 30 cert771 (by decide +kernel)

theorem node772 : UpperPrefix a [5,6,0,7,8,2] 30 :=
  branch_upper a [5,6,0,7,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,8,2,0] 30 (by decide +kernel))
  node769
  (invalid_upper a [5,6,0,7,8,2,2] 30 (by decide +kernel))
  node770
  node771
  (invalid_upper a [5,6,0,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,2,8] 30 (by decide +kernel)))

def cert773 : Leaf := ⟨⟨76,44,32,293,41,133,45,61,29⟩,[],[(6,1,0),(7,3,5),(8,4,3),(1,6,1)],⟨35,67,13,152,276,104,194,404,308⟩,⟨35,67,13,152,276,104,194,384,288⟩,[⟨4,1210110015663161939680573,⟨39,67,111,239,295,111,194,451,295⟩⟩]⟩
theorem node773 : UpperPrefix a [5,6,0,7,8,3,1] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,3,1] 30 cert773 (by decide +kernel)

def cert774 : Leaf := ⟨⟨64,32,34,295,43,135,35,55,31⟩,[],[(6,1,0),(7,3,5),(8,4,3)],⟨35,67,13,152,276,104,196,402,306⟩,⟨35,67,13,152,276,104,196,384,288⟩,[⟨4,1210107709820152725953917,⟨39,67,111,239,295,111,231,385,295⟩⟩,⟨3,1210255427466816440526113,⟨35,67,5,210,471,99,196,385,291⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,152,273,107,192,385,291⟩⟩]⟩
theorem node774 : UpperPrefix a [5,6,0,7,8,3,2] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,3,2] 30 cert774 (by decide +kernel)

def cert775 : Local := ⟨⟨76,44,34,0,43,151,0,47,15⟩,[(3,6),(6,3)],[(6,1,0),(7,3,5),(8,4,3),(8,4,6),(4,6,5)]⟩
theorem node775 : UpperPrefix a [5,6,0,7,8,3,4] 30 :=
  local_sound a [5,6,0,7,8,3,4] 30 cert775 (by decide +kernel)

theorem node776 : UpperPrefix a [5,6,0,7,8,3] 30 :=
  branch_upper a [5,6,0,7,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,8,3,0] 30 (by decide +kernel))
  node773
  node774
  (invalid_upper a [5,6,0,7,8,3,3] 30 (by decide +kernel))
  node775
  (invalid_upper a [5,6,0,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,3,8] 30 (by decide +kernel)))

def cert777 : Leaf := ⟨⟨192,160,176,293,169,129,33,61,157⟩,[],[(6,1,0),(8,4,3),(1,6,1)],⟨35,67,13,152,276,112,194,396,300⟩,⟨35,67,13,152,276,112,194,384,288⟩,[⟨2,1210110015523523951418669,⟨35,67,107,251,275,115,194,451,291⟩⟩,⟨3,1210110015523522878725421,⟨35,67,103,243,279,115,194,451,291⟩⟩,⟨4,1210110015240949464124705,⟨35,67,79,202,263,99,194,451,291⟩⟩]⟩
theorem node777 : UpperPrefix a [5,6,0,7,8,4,1] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,4,1] 30 cert777 (by decide +kernel)

def cert778 : Leaf := ⟨⟨216,184,176,288,168,140,56,56,152⟩,[],[(6,1,0),(8,4,3),(2,6,5)],⟨35,67,13,152,276,112,196,386,296⟩,⟨35,67,13,152,276,112,196,386,288⟩,[⟨0,2414338763619854137164800,⟨426,506,508,440,380,376,508,426,288⟩⟩,⟨1,2334033101170780568813569,⟨309,381,317,504,276,376,508,508,288⟩⟩]⟩
theorem node778 : UpperPrefix a [5,6,0,7,8,4,2,1] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,4,2,1] 30 cert778 (by decide +kernel)

def cert779 : Leaf := ⟨⟨208,176,178,290,162,134,58,50,146⟩,[],[(6,1,0),(8,4,3),(2,6,5),(3,7,6)],⟨35,67,13,152,276,112,196,392,290⟩,⟨35,67,13,152,276,112,196,392,288⟩,[⟨0,1226848349055965973185536,⟨426,490,508,248,508,248,252,424,424⟩⟩]⟩
theorem node779 : UpperPrefix a [5,6,0,7,8,4,2,3] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,4,2,3] 30 cert779 (by decide +kernel)

theorem node780 : UpperPrefix a [5,6,0,7,8,4,2] 30 :=
  branch_upper a [5,6,0,7,8,4,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,8,4,2,0] 30 (by decide +kernel))
  node778
  (invalid_upper a [5,6,0,7,8,4,2,2] 30 (by decide +kernel))
  node779
  (invalid_upper a [5,6,0,7,8,4,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,2,8] 30 (by decide +kernel)))

def cert781 : Leaf := ⟨⟨88,24,18,263,43,11,0,31,31⟩,[(6,3)],[(6,1,0),(7,3,6),(8,4,3)],⟨35,67,13,152,276,112,200,390,294⟩,⟨35,67,13,152,276,112,200,384,288⟩,[⟨5,1210256146916864429395457,⟨79,71,79,216,478,216,200,384,328⟩⟩,⟨2,1210107709680514737692013,⟨35,67,107,251,275,115,235,385,291⟩⟩]⟩
theorem node781 : UpperPrefix a [5,6,0,7,8,4,3] 30 :=
  Boolean.leaf_sound a [5,6,0,7,8,4,3] 30 cert781 (by decide +kernel)

theorem node782 : UpperPrefix a [5,6,0,7,8,4] 30 :=
  branch_upper a [5,6,0,7,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,8,4,0] 30 (by decide +kernel))
  node777
  node780
  node781
  (invalid_upper a [5,6,0,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,4,8] 30 (by decide +kernel)))

theorem node783 : UpperPrefix a [5,6,0,7,8] 30 :=
  branch_upper a [5,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,8,0] 30 (by decide +kernel))
  node768
  node772
  node776
  node782
  (invalid_upper a [5,6,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,8,8] 30 (by decide +kernel)))

theorem node784 : UpperPrefix a [5,6,0,7] 30 :=
  branch_upper a [5,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,7,0] 30 (by decide +kernel))
  node762
  (invalid_upper a [5,6,0,7,2] 30 (by decide +kernel))
  node767
  (invalid_upper a [5,6,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,7,7] 30 (by decide +kernel))
  node783)

def cert785 : Leaf := ⟨⟨72,40,34,36,297,412,316,60,156⟩,[],[(6,1,0),(0,2,4)],⟨35,67,13,280,22,252,220,412,444⟩,⟨35,67,13,280,22,96,192,384,288⟩,[⟨1,1285813291755683938566145,⟨33,65,13,504,508,96,192,384,288⟩⟩,⟨7,1208926973680778103244065,⟨35,67,13,285,22,99,76,285,319⟩⟩,⟨4,1210107565282752176604449,⟨35,67,13,269,6,99,192,385,291⟩⟩,⟨8,1181745669222513526049,⟨35,67,13,29,22,99,192,129,35⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,281,18,99,192,385,291⟩⟩]⟩
theorem node785 : UpperPrefix a [5,6,0,8,1] 30 :=
  Boolean.leaf_sound a [5,6,0,8,1] 30 cert785 (by decide +kernel)

def cert786 : Leaf := ⟨⟨64,32,34,39,0,407,311,55,151⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,13,280,28,246,214,406,438⟩,⟨35,67,13,280,28,96,192,384,288⟩,[⟨7,1208926973694796876498209,⟨35,83,29,285,28,115,92,285,319⟩⟩,⟨4,1210107565282752176604449,⟨35,67,13,269,12,99,192,385,291⟩⟩,⟨8,1181745670047147246881,⟨35,67,29,29,28,99,192,129,35⟩⟩,⟨2,1210107565283851685086497,⟨35,67,9,281,24,99,192,385,291⟩⟩]⟩
theorem node786 : UpperPrefix a [5,6,0,8,3] 30 :=
  Boolean.leaf_sound a [5,6,0,8,3] 30 cert786 (by decide +kernel)

def cert787 : Leaf := ⟨⟨0,300,288,165,297,0,317,61,157⟩,[(0,5),(5,1)],[(6,1,0),(6,1,5),(1,5,0)],⟨35,67,13,280,148,98,220,412,316⟩,⟨35,67,13,280,148,98,192,384,288⟩,[⟨4,1210107567604920734500195,⟨35,99,13,269,132,99,227,385,291⟩⟩,⟨7,1208926975985302834824547,⟨35,99,13,285,20,99,99,257,291⟩⟩]⟩
theorem node787 : UpperPrefix a [5,6,0,8,7,1] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,1] 30 cert787 (by decide +kernel)

def cert788 : Leaf := ⟨⟨204,172,160,164,296,136,44,60,156⟩,[],[(6,1,0),(1,6,1)],⟨35,67,13,280,148,100,194,408,312⟩,⟨35,67,13,280,148,100,194,384,288⟩,[⟨0,1463316851998074237617152,⟨506,458,508,408,444,508,194,392,440⟩⟩,⟨4,1210110160200562472219965,⟨35,67,47,367,231,103,194,451,291⟩⟩,⟨8,1184340587032809141565,⟨35,67,47,127,247,103,194,195,35⟩⟩]⟩
theorem node788 : UpperPrefix a [5,6,0,8,7,2,1] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,2,1] 30 cert788 (by decide +kernel)

def cert789 : Leaf := ⟨⟨64,32,34,167,35,11,307,51,151⟩,[],[(6,1,0),(8,3,6),(3,6,5)],⟨35,67,13,280,148,100,200,402,306⟩,⟨35,67,13,280,148,100,200,384,288⟩,[⟨2,1210181568432928637082913,⟨35,67,203,475,210,99,202,385,291⟩⟩,⟨4,1210107567604920751277411,⟨35,103,13,269,132,103,239,385,291⟩⟩,⟨7,1208926975985302851601763,⟨35,103,13,285,20,103,111,257,291⟩⟩]⟩
theorem node789 : UpperPrefix a [5,6,0,8,7,2,3] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,2,3] 30 cert789 (by decide +kernel)

def cert790 : Leaf := ⟨⟨80,48,50,39,299,19,0,59,31⟩,[(6,4)],[(6,1,0),(7,4,6)],⟨35,67,13,280,148,100,208,394,298⟩,⟨35,67,13,280,148,100,208,384,288⟩,[⟨8,1182034744023595414909,⟨35,67,47,127,247,103,243,129,35⟩⟩,⟨2,1210181784605710750866721,⟨35,67,203,475,210,99,208,385,291⟩⟩,⟨3,1210107854077176717571449,⟨35,67,7,371,247,103,243,385,291⟩⟩]⟩
theorem node790 : UpperPrefix a [5,6,0,8,7,2,4] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,2,4] 30 cert790 (by decide +kernel)

theorem node791 : UpperPrefix a [5,6,0,8,7,2] 30 :=
  branch_upper a [5,6,0,8,7,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,8,7,2,0] 30 (by decide +kernel))
  node788
  (invalid_upper a [5,6,0,8,7,2,2] 30 (by decide +kernel))
  node789
  node790
  (invalid_upper a [5,6,0,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,2,8] 30 (by decide +kernel)))

def cert792 : Leaf := ⟨⟨192,160,160,165,297,129,33,61,157⟩,[],[(6,1,0),(1,6,1)],⟨35,67,13,280,148,104,194,404,308⟩,⟨35,67,13,280,148,104,194,384,288⟩,[⟨4,1210110159637612527187245,⟨39,67,47,367,199,111,194,451,295⟩⟩,⟨8,1184340024082864108845,⟨39,67,47,127,215,111,194,195,39⟩⟩,⟨2,1210110159638712027280685,⟨35,67,43,379,211,107,194,451,291⟩⟩,⟨3,1210110159357235977868577,⟨35,67,7,339,214,99,194,451,291⟩⟩]⟩
theorem node792 : UpperPrefix a [5,6,0,8,7,3,1] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,3,1] 30 cert792 (by decide +kernel)

def cert793 : Leaf := ⟨⟨452,420,418,166,0,390,0,54,150⟩,[(4,6),(6,4)],[(6,1,0)],⟨35,67,13,280,148,104,196,402,306⟩,⟨35,67,13,280,148,104,196,384,288⟩,[⟨0,1219571033580282873644032,⟨426,506,44,376,212,120,212,384,288⟩⟩,⟨3,1361592587909796564327713,⟨419,83,215,467,214,499,214,385,419⟩⟩,⟨4,1210107853794603313460525,⟨39,67,47,367,199,111,199,385,295⟩⟩]⟩
theorem node793 : UpperPrefix a [5,6,0,8,7,3,2] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,3,2] 30 cert793 (by decide +kernel)

def cert794 : Leaf := ⟨⟨76,44,34,39,299,23,0,47,15⟩,[(6,4)],[(6,1,0),(7,4,6),(4,6,5)],⟨35,67,13,280,148,104,208,390,294⟩,⟨35,67,13,280,148,104,208,384,288⟩,[⟨8,1182034181073650349357,⟨39,67,47,127,215,111,210,129,39⟩⟩]⟩
theorem node794 : UpperPrefix a [5,6,0,8,7,3,4] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,3,4] 30 cert794 (by decide +kernel)

theorem node795 : UpperPrefix a [5,6,0,8,7,3] 30 :=
  branch_upper a [5,6,0,8,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,8,7,3,0] 30 (by decide +kernel))
  node792
  node793
  (invalid_upper a [5,6,0,8,7,3,3] 30 (by decide +kernel))
  node794
  (invalid_upper a [5,6,0,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,3,8] 30 (by decide +kernel)))

def cert796 : Leaf := ⟨⟨76,44,32,37,297,141,45,45,29⟩,[],[(6,1,0),(7,4,5),(1,6,1)],⟨35,67,13,280,148,112,194,396,300⟩,⟨35,67,13,280,148,112,194,384,288⟩,[⟨4,1210184162505214494072097,⟨35,67,207,463,198,99,194,451,291⟩⟩,⟨8,1184340587032809141565,⟨35,67,47,127,247,115,194,195,35⟩⟩]⟩
theorem node796 : UpperPrefix a [5,6,0,8,7,4,1] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,4,1] 30 cert796 (by decide +kernel)

def cert797 : Local := ⟨⟨344,312,306,35,0,399,0,59,27⟩,[(4,6),(6,4)],[(6,1,0),(7,4,5),(2,6,5)]⟩
theorem node797 : UpperPrefix a [5,6,0,8,7,4,2] 30 :=
  local_sound a [5,6,0,8,7,4,2] 30 cert797 (by decide +kernel)

def cert798 : Leaf := ⟨⟨88,56,48,37,41,137,305,57,29⟩,[],[(6,1,0),(8,3,6),(7,4,5)],⟨35,67,13,280,148,112,200,386,292⟩,⟨35,67,13,280,148,112,200,386,288⟩,[⟨1,1923187505879206156042241,⟨301,365,301,376,508,376,504,508,296⟩⟩,⟨2,1212542752518788389862781,⟨35,67,235,507,243,115,235,387,419⟩⟩]⟩
theorem node798 : UpperPrefix a [5,6,0,8,7,4,3,1] 30 :=
  Boolean.leaf_sound a [5,6,0,8,7,4,3,1] 30 cert798 (by decide +kernel)

def cert799 : Local := ⟨⟨88,56,50,35,0,139,307,59,27⟩,[(4,7)],[(6,1,0),(8,3,6),(7,4,5),(2,7,4)]⟩
theorem node799 : UpperPrefix a [5,6,0,8,7,4,3,2] 30 :=
  local_sound a [5,6,0,8,7,4,3,2] 30 cert799 (by decide +kernel)

theorem node800 : UpperPrefix a [5,6,0,8,7,4,3] 30 :=
  branch_upper a [5,6,0,8,7,4,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,8,7,4,3,0] 30 (by decide +kernel))
  node798
  node799
  (invalid_upper a [5,6,0,8,7,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,3,8] 30 (by decide +kernel)))

theorem node801 : UpperPrefix a [5,6,0,8,7,4] 30 :=
  branch_upper a [5,6,0,8,7,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,8,7,4,0] 30 (by decide +kernel))
  node796
  node797
  node800
  (invalid_upper a [5,6,0,8,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,4,8] 30 (by decide +kernel)))

theorem node802 : UpperPrefix a [5,6,0,8,7] 30 :=
  branch_upper a [5,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,8,7,0] 30 (by decide +kernel))
  node787
  node791
  node795
  node801
  (invalid_upper a [5,6,0,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,7,8] 30 (by decide +kernel)))

theorem node803 : UpperPrefix a [5,6,0,8] 30 :=
  branch_upper a [5,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,8,0] 30 (by decide +kernel))
  node785
  (invalid_upper a [5,6,0,8,2] 30 (by decide +kernel))
  node786
  (invalid_upper a [5,6,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,8,6] 30 (by decide +kernel))
  node802
  (invalid_upper a [5,6,0,8,8] 30 (by decide +kernel)))

theorem node804 : UpperPrefix a [5,6,0] 30 :=
  branch_upper a [5,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,0,0] 30 (by decide +kernel))
  node748
  node757
  (invalid_upper a [5,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,0,6] 30 (by decide +kernel))
  node784
  node803)

theorem node805 : UpperPrefix a [5,6,1,0] 30 :=
  branch_upper a [5,6,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [5,6,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,0,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,1,0,3] [5,6,0,2,1] 30 (by decide +kernel) node749)
  (invalid_upper a [5,6,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,0,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut8 [5,6,1,0,7] [5,6,0,7,1] 30 (by decide +kernel) node762)
  (PrefixConjugacy.upper aut8 [5,6,1,0,8] [5,6,0,8,1] 30 (by decide +kernel) node785))

def cert806 : Leaf := ⟨⟨336,304,305,0,0,403,307,51,147⟩,[(3,4),(4,2)],[(6,1,0),(2,3,3),(2,3,4),(3,4,3),(3,4,4)],⟨35,67,14,28,28,497,465,401,433⟩,⟨35,67,14,28,28,96,192,384,288⟩,[⟨7,1208926973692811367171361,⟨63,95,30,28,28,127,88,285,319⟩⟩]⟩
theorem node806 : UpperPrefix a [5,6,1,2,3] 30 :=
  Boolean.leaf_sound a [5,6,1,2,3] 30 cert806 (by decide +kernel)

def cert807 : Local := ⟨⟨472,0,432,0,298,0,314,58,154⟩,[(1,5),(3,4),(5,1)],[(6,1,0),(2,3,3),(0,5,0)]⟩
theorem node807 : UpperPrefix a [5,6,1,2,7,0] 30 :=
  local_sound a [5,6,1,2,7,0] 30 cert807 (by decide +kernel)

def cert808 : Leaf := ⟨⟨72,40,33,0,43,147,315,59,155⟩,[(3,4)],[(6,1,0),(2,3,3)],⟨35,67,14,28,148,104,465,401,305⟩,⟨35,67,14,28,148,104,192,384,288⟩,[⟨8,1181748004617782609255,⟨47,127,47,29,157,127,255,157,47⟩⟩,⟨4,1210107565282752182895905,⟨39,67,14,12,132,111,192,385,295⟩⟩,⟨7,1208926973663136430703905,⟨39,67,14,28,28,111,64,257,295⟩⟩]⟩
theorem node808 : UpperPrefix a [5,6,1,2,7,3] 30 :=
  Boolean.leaf_sound a [5,6,1,2,7,3] 30 cert808 (by decide +kernel)

def cert809 : Leaf := ⟨⟨80,48,49,0,43,139,315,59,27⟩,[(3,4)],[(6,1,0),(2,3,3),(7,4,5)],⟨35,67,14,28,148,112,457,393,297⟩,⟨35,67,14,28,148,112,192,384,288⟩,[⟨8,1181748004617782609255,⟨47,127,47,29,157,127,255,157,47⟩⟩,⟨3,1210107565283850612393249,⟨35,67,6,20,148,115,192,385,291⟩⟩]⟩
theorem node809 : UpperPrefix a [5,6,1,2,7,4] 30 :=
  Boolean.leaf_sound a [5,6,1,2,7,4] 30 cert809 (by decide +kernel)

def cert810 : Leaf := ⟨⟨64,32,177,0,43,155,59,59,155⟩,[(3,4)],[(6,1,0),(2,3,3)],⟨35,67,14,28,148,352,217,409,313⟩,⟨35,67,14,28,148,352,192,384,288⟩,[⟨8,1184051525458476221729,⟨47,95,14,28,222,127,222,223,47⟩⟩,⟨3,1210107565283850612393249,⟨35,67,6,20,148,355,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,14,12,132,355,192,385,291⟩⟩,⟨7,1208926973663136422315297,⟨35,67,14,28,28,355,64,257,291⟩⟩]⟩
theorem node810 : UpperPrefix a [5,6,1,2,7,8] 30 :=
  Boolean.leaf_sound a [5,6,1,2,7,8] 30 cert810 (by decide +kernel)

theorem node811 : UpperPrefix a [5,6,1,2,7] 30 :=
  branch_upper a [5,6,1,2,7] 30 (by decide) (fin9_cases _
  node807
  (invalid_upper a [5,6,1,2,7,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,7,2] 30 (by decide +kernel))
  node808
  node809
  (invalid_upper a [5,6,1,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,7,7] 30 (by decide +kernel))
  node810)

def cert812 : Local := ⟨⟨472,0,432,0,170,0,314,58,154⟩,[(1,5),(3,4),(5,1)],[(6,1,0),(2,3,3),(0,5,0)]⟩
theorem node812 : UpperPrefix a [5,6,1,2,8,0] 30 :=
  local_sound a [5,6,1,2,8,0] 30 cert812 (by decide +kernel)

def cert813 : Leaf := ⟨⟨320,288,289,0,43,275,307,51,155⟩,[(3,4)],[(6,1,0),(2,3,3)],⟨35,67,14,28,276,104,209,401,433⟩,⟨35,67,14,28,276,104,192,384,288⟩,[⟨7,1208926976011753481618791,⟨39,111,47,29,285,111,127,285,319⟩⟩,⟨3,1210255427466816440526113,⟨35,67,6,214,471,99,192,385,291⟩⟩,⟨4,1210107565282752182895905,⟨39,67,14,12,261,111,192,385,295⟩⟩]⟩
theorem node813 : UpperPrefix a [5,6,1,2,8,3] 30 :=
  Boolean.leaf_sound a [5,6,1,2,8,3] 30 cert813 (by decide +kernel)

def cert814 : Leaf := ⟨⟨64,32,49,0,43,267,315,59,155⟩,[(3,4)],[(6,1,0),(2,3,3)],⟨35,67,14,28,276,112,201,393,425⟩,⟨35,67,14,28,276,112,192,384,288⟩,[⟨7,1208926975941389032670563,⟨47,111,15,28,285,127,127,285,319⟩⟩,⟨8,1181745669229029639457,⟨47,71,14,28,29,127,192,133,47⟩⟩,⟨3,1210107565283850612393249,⟨35,67,6,20,277,115,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,14,12,261,99,192,385,291⟩⟩]⟩
theorem node814 : UpperPrefix a [5,6,1,2,8,4] 30 :=
  Boolean.leaf_sound a [5,6,1,2,8,4] 30 cert814 (by decide +kernel)

def cert815 : Leaf := ⟨⟨336,304,305,0,43,0,315,59,27⟩,[(3,4),(5,6)],[(6,1,0),(2,3,3),(7,5,5)],⟨35,67,14,28,276,224,217,409,313⟩,⟨35,67,14,28,276,224,192,384,288⟩,[⟨3,1210107567535650426111331,⟨35,99,7,20,277,227,227,385,291⟩⟩]⟩
theorem node815 : UpperPrefix a [5,6,1,2,8,7] 30 :=
  Boolean.leaf_sound a [5,6,1,2,8,7] 30 cert815 (by decide +kernel)

theorem node816 : UpperPrefix a [5,6,1,2,8] 30 :=
  branch_upper a [5,6,1,2,8] 30 (by decide) (fin9_cases _
  node812
  (invalid_upper a [5,6,1,2,8,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,8,2] 30 (by decide +kernel))
  node813
  node814
  (invalid_upper a [5,6,1,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,8,6] 30 (by decide +kernel))
  node815
  (invalid_upper a [5,6,1,2,8,8] 30 (by decide +kernel)))

theorem node817 : UpperPrefix a [5,6,1,2] 30 :=
  branch_upper a [5,6,1,2] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut4 [5,6,1,2,0] [5,6,0,1,3] 30 (by decide +kernel) node741)
  (invalid_upper a [5,6,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,2] 30 (by decide +kernel))
  node806
  (invalid_upper a [5,6,1,2,4] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,2,6] 30 (by decide +kernel))
  node811
  node816)

def cert818 : Local := ⟨⟨468,0,432,294,0,0,310,54,150⟩,[(1,5),(4,2),(5,1)],[(6,1,0),(3,4,4),(0,5,0)]⟩
theorem node818 : UpperPrefix a [5,6,1,7,3,0] 30 :=
  local_sound a [5,6,1,7,3,0] 30 cert818 (by decide +kernel)

def cert819 : Leaf := ⟨⟨64,32,177,39,0,147,311,55,23⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,14,152,28,100,465,401,305⟩,⟨35,67,14,152,28,100,192,384,288⟩,[⟨8,1181747998409071576423,⟨55,127,63,152,29,127,255,129,55⟩⟩,⟨7,1360042701115237799576865,⟨291,67,30,24,28,375,64,257,291⟩⟩,⟨2,1210107565283851685086497,⟨35,67,10,152,24,99,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,14,136,12,103,192,385,291⟩⟩]⟩
theorem node819 : UpperPrefix a [5,6,1,7,3,2] 30 :=
  Boolean.leaf_sound a [5,6,1,7,3,2] 30 cert819 (by decide +kernel)

def cert820 : Leaf := ⟨⟨64,32,177,39,0,135,311,55,151⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,14,152,28,112,453,389,293⟩,⟨35,67,14,152,28,112,192,384,288⟩,[⟨8,1181747998409071576423,⟨55,127,63,152,29,127,255,129,55⟩⟩,⟨2,1210107565283851685086497,⟨35,67,10,152,24,115,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,14,136,12,99,192,385,291⟩⟩,⟨7,1208926973663409152738593,⟨35,67,30,24,28,115,64,257,291⟩⟩]⟩
theorem node820 : UpperPrefix a [5,6,1,7,3,4] 30 :=
  Boolean.leaf_sound a [5,6,1,7,3,4] 30 cert820 (by decide +kernel)

def cert821 : Leaf := ⟨⟨64,32,177,39,0,151,55,55,151⟩,[(4,2)],[(6,1,0),(3,4,4)],⟨35,67,14,152,28,352,213,405,309⟩,⟨35,67,14,152,28,352,192,384,288⟩,[⟨8,1184051528612791797025,⟨55,95,30,222,28,127,222,223,55⟩⟩,⟨2,1210107565283851685086497,⟨35,67,10,152,24,355,192,385,291⟩⟩,⟨4,1210107565282752174507297,⟨35,67,14,136,12,355,192,385,291⟩⟩,⟨7,1208926973663409152738593,⟨35,67,30,24,28,355,64,257,291⟩⟩]⟩
theorem node821 : UpperPrefix a [5,6,1,7,3,8] 30 :=
  Boolean.leaf_sound a [5,6,1,7,3,8] 30 cert821 (by decide +kernel)

theorem node822 : UpperPrefix a [5,6,1,7,3] 30 :=
  branch_upper a [5,6,1,7,3] 30 (by decide) (fin9_cases _
  node818
  (invalid_upper a [5,6,1,7,3,1] 30 (by decide +kernel))
  node819
  (invalid_upper a [5,6,1,7,3,3] 30 (by decide +kernel))
  node820
  (invalid_upper a [5,6,1,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,3,7] 30 (by decide +kernel))
  node821)

def cert823 : Leaf := ⟨⟨220,0,176,292,168,0,60,60,156⟩,[(1,5),(5,1)],[(6,1,0),(8,4,3),(0,5,0)],⟨35,67,14,152,276,97,220,412,316⟩,⟨35,67,14,152,276,97,192,384,288⟩,[⟨1,1229181859014683858567169,⟨33,97,508,216,476,97,192,384,288⟩⟩]⟩
theorem node823 : UpperPrefix a [5,6,1,7,8,0] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,0] 30 cert823 (by decide +kernel)

def cert824 : Leaf := ⟨⟨220,0,176,292,168,152,60,60,156⟩,[(1,6)],[(6,1,0),(8,4,3),(0,6,1)],⟨35,67,14,152,276,100,193,408,312⟩,⟨35,67,14,152,276,100,193,384,288⟩,[⟨1,1463316851998074237616129,⟨505,457,508,408,444,508,457,392,440⟩⟩]⟩
theorem node824 : UpperPrefix a [5,6,1,7,8,2,0] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,2,0] 30 cert824 (by decide +kernel)

def cert825 : Local := ⟨⟨84,52,49,295,35,27,0,55,23⟩,[(6,3)],[(6,1,0),(7,3,6),(8,4,3),(3,6,5)]⟩
theorem node825 : UpperPrefix a [5,6,1,7,8,2,3] 30 :=
  local_sound a [5,6,1,7,8,2,3] 30 cert825 (by decide +kernel)

def cert826 : Leaf := ⟨⟨208,176,177,0,171,147,0,59,155⟩,[(3,6),(6,3)],[(6,1,0),(8,4,3),(8,4,6)],⟨35,67,14,152,276,100,208,393,297⟩,⟨35,67,14,152,276,100,208,384,288⟩,[⟨2,1361666446939024326157601,⟨419,75,74,218,475,491,218,385,419⟩⟩,⟨3,1210107709539776176643381,⟨35,67,103,211,311,103,211,385,291⟩⟩]⟩
theorem node826 : UpperPrefix a [5,6,1,7,8,2,4] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,2,4] 30 cert826 (by decide +kernel)

theorem node827 : UpperPrefix a [5,6,1,7,8,2] 30 :=
  branch_upper a [5,6,1,7,8,2] 30 (by decide) (fin9_cases _
  node824
  (invalid_upper a [5,6,1,7,8,2,1] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,2,2] 30 (by decide +kernel))
  node825
  node826
  (invalid_upper a [5,6,1,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,2,8] 30 (by decide +kernel)))

def cert828 : Leaf := ⟨⟨76,0,32,294,42,134,46,62,30⟩,[(1,6)],[(6,1,0),(7,3,5),(8,4,3),(0,6,1)],⟨35,67,14,152,276,104,193,404,308⟩,⟨35,67,14,152,276,104,193,384,288⟩,[⟨4,1210110015663161939713341,⟨39,67,111,239,295,111,195,451,295⟩⟩]⟩
theorem node828 : UpperPrefix a [5,6,1,7,8,3,0] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,3,0] 30 cert828 (by decide +kernel)

def cert829 : Leaf := ⟨⟨64,32,33,291,43,135,35,51,31⟩,[],[(6,1,0),(7,3,5),(8,4,3)],⟨35,67,14,152,276,104,196,401,305⟩,⟨35,67,14,152,276,104,196,384,288⟩,[⟨4,1210107709820152725953917,⟨39,67,111,239,295,111,231,385,295⟩⟩,⟨2,1210255139236443508983073,⟨35,67,10,152,409,107,192,385,291⟩⟩,⟨3,1210255427466816440526113,⟨35,67,6,210,471,99,196,385,291⟩⟩]⟩
theorem node829 : UpperPrefix a [5,6,1,7,8,3,2] 30 :=
  Boolean.leaf_sound a [5,6,1,7,8,3,2] 30 cert829 (by decide +kernel)

def cert830 : Local := ⟨⟨76,44,33,0,43,151,0,47,15⟩,[(3,6),(6,3)],[(6,1,0),(7,3,5),(8,4,3),(8,4,6),(4,6,5)]⟩
theorem node830 : UpperPrefix a [5,6,1,7,8,3,4] 30 :=
  local_sound a [5,6,1,7,8,3,4] 30 cert830 (by decide +kernel)

theorem node831 : UpperPrefix a [5,6,1,7,8,3] 30 :=
  branch_upper a [5,6,1,7,8,3] 30 (by decide) (fin9_cases _
  node828
  (invalid_upper a [5,6,1,7,8,3,1] 30 (by decide +kernel))
  node829
  (invalid_upper a [5,6,1,7,8,3,3] 30 (by decide +kernel))
  node830
  (invalid_upper a [5,6,1,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [5,6,1,7,8,3,8] 30 (by decide +kernel)))

#print axioms node831
end Delivery.FiniteExclusion.Sharp2x3x4
