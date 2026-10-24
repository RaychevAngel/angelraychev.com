import RegularNineSharp2x7Base
import RegularNineSharp2x7C009
import RegularNineSharp2x7C010
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert704 : Leaf := ⟨⟨88,76,146,102,70,30,30,0,90⟩,[(7,5)],[(7,3,2),(8,5,7),(5,7,3)],⟨7,19,76,152,56,352,193,416,262⟩,⟨7,19,76,152,56,352,193,416,260⟩,[⟨0,1215715377749760018482176,⟨286,282,252,152,188,508,508,444,284⟩⟩]⟩
theorem node704 : UpperPrefix a [2,4,6,7,3,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,8,0,5] 30 cert704 (by decide +kernel)

theorem node705 : UpperPrefix a [2,4,6,7,3,8,0] 30 :=
  branch_upper a [2,4,6,7,3,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,3,8,0,0] 30 (by decide +kernel))
  node703
  (invalid_upper a [2,4,6,7,3,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,0,4] 30 (by decide +kernel))
  node704
  (invalid_upper a [2,4,6,7,3,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,0,8] 30 (by decide +kernel)))

def cert706 : Leaf := ⟨⟨344,328,400,320,320,24,281,92,120⟩,[],[(2,0,7),(7,3,2),(0,7,6)],⟨7,19,76,152,56,352,194,385,292⟩,⟨7,19,76,152,56,352,194,385,260⟩,[⟨1,1762652116295214907260929,⟨445,409,380,408,316,380,508,409,308⟩⟩,⟨5,1212764327650132336587871,⟨7,95,79,223,223,449,199,385,389⟩⟩]⟩
theorem node706 : UpperPrefix a [2,4,6,7,3,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,8,1,0] 30 cert706 (by decide +kernel)

def cert707 : Leaf := ⟨⟨88,76,145,101,69,31,29,0,89⟩,[(7,5)],[(7,3,2),(8,5,7),(5,7,3)],⟨7,19,76,152,56,352,194,416,261⟩,⟨7,19,76,152,56,352,194,416,260⟩,[⟨1,1215125079682928037855233,⟨261,281,76,152,188,508,220,444,260⟩⟩]⟩
theorem node707 : UpperPrefix a [2,4,6,7,3,8,1,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,8,1,5] 30 cert707 (by decide +kernel)

theorem node708 : UpperPrefix a [2,4,6,7,3,8,1] 30 :=
  branch_upper a [2,4,6,7,3,8,1] 30 (by decide) (fin9_cases _
  node706
  (invalid_upper a [2,4,6,7,3,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,1,4] 30 (by decide +kernel))
  node707
  (invalid_upper a [2,4,6,7,3,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,1,8] 30 (by decide +kernel)))

def cert709 : Leaf := ⟨⟨40,44,162,38,6,14,270,47,43⟩,[],[(7,3,2),(8,5,6)],⟨7,19,76,152,56,352,224,387,263⟩,⟨7,19,76,152,56,352,224,384,260⟩,[⟨4,1224304843458017242383363,⟨487,487,76,236,108,352,224,480,260⟩⟩,⟨6,1236439139534180371680517,⟨399,411,415,152,186,443,186,385,399⟩⟩,⟨0,1210110019761617356456960,⟨6,22,92,252,124,380,252,508,260⟩⟩]⟩
theorem node709 : UpperPrefix a [2,4,6,7,3,8,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,8,5] 30 cert709 (by decide +kernel)

theorem node710 : UpperPrefix a [2,4,6,7,3,8] 30 :=
  branch_upper a [2,4,6,7,3,8] 30 (by decide) (fin9_cases _
  node705
  node708
  (invalid_upper a [2,4,6,7,3,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,4] 30 (by decide +kernel))
  node709
  (invalid_upper a [2,4,6,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,8,8] 30 (by decide +kernel)))

theorem node711 : UpperPrefix a [2,4,6,7,3] 30 :=
  branch_upper a [2,4,6,7,3] 30 (by decide) (fin9_cases _
  node698
  node702
  (invalid_upper a [2,4,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,7] 30 (by decide +kernel))
  node710)

def cert712 : Leaf := ⟨⟨88,76,144,352,76,26,24,120,120⟩,[],[(7,3,2),(8,4,3),(1,6,5)],⟨7,19,76,152,304,97,194,424,300⟩,⟨7,19,76,152,304,97,194,384,260⟩,[⟨0,1437223914350366464672768,⟨78,478,76,408,444,508,206,384,260⟩⟩,⟨2,1210255175370793912632321,⟨107,251,72,152,440,97,234,384,256⟩⟩,⟨5,1210107708273139857232909,⟨7,19,79,223,272,65,194,384,261⟩⟩]⟩
theorem node712 : UpperPrefix a [2,4,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,0,1] 30 cert712 (by decide +kernel)

def cert713 : Local := ⟨⟨112,100,0,359,71,22,0,119,115⟩,[(2,6),(6,3)],[(7,3,2),(7,3,6),(8,4,3),(3,6,2)]⟩
theorem node713 : UpperPrefix a [2,4,6,7,8,0,3] 30 :=
  local_sound a [2,4,6,7,8,0,3] 30 cert713 (by decide +kernel)

def cert714 : Leaf := ⟨⟨112,100,162,358,70,6,6,100,106⟩,[],[(7,3,2),(8,4,3)],⟨7,19,76,152,304,97,224,386,268⟩,⟨7,19,76,152,304,97,224,386,260⟩,[⟨0,1809876355191769748472832,⟨398,414,348,412,380,508,508,394,260⟩⟩,⟨3,1212623722586954230080769,⟨103,243,68,242,499,97,242,499,503⟩⟩,⟨4,1266788122901734935757825,⟨487,227,332,460,352,225,224,482,260⟩⟩]⟩
theorem node714 : UpperPrefix a [2,4,6,7,8,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,0,5,1] 30 cert714 (by decide +kernel)

def cert715 : Leaf := ⟨⟨112,100,176,356,70,20,20,116,114⟩,[],[(7,3,2),(8,4,3)],⟨7,19,76,152,304,97,224,392,262⟩,⟨7,19,76,152,304,97,224,392,260⟩,[⟨0,1224745921399683026519040,⟨398,478,76,220,508,508,252,396,260⟩⟩,⟨3,1233721852329664143650565,⟨311,275,375,242,307,371,242,499,311⟩⟩,⟨1,1210255463601170072469505,⟨109,253,76,220,508,101,224,396,260⟩⟩]⟩
theorem node715 : UpperPrefix a [2,4,6,7,8,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,0,5,3] 30 cert715 (by decide +kernel)

theorem node716 : UpperPrefix a [2,4,6,7,8,0,5] 30 :=
  branch_upper a [2,4,6,7,8,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,8,0,5,0] 30 (by decide +kernel))
  node714
  (invalid_upper a [2,4,6,7,8,0,5,2] 30 (by decide +kernel))
  node715
  (invalid_upper a [2,4,6,7,8,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,5,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,5,8] 30 (by decide +kernel)))

theorem node717 : UpperPrefix a [2,4,6,7,8,0] 30 :=
  branch_upper a [2,4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,8,0,0] 30 (by decide +kernel))
  node712
  (invalid_upper a [2,4,6,7,8,0,2] 30 (by decide +kernel))
  node713
  (invalid_upper a [2,4,6,7,8,0,4] 30 (by decide +kernel))
  node716
  (invalid_upper a [2,4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,0,8] 30 (by decide +kernel)))

def cert718 : Leaf := ⟨⟨112,100,176,356,68,21,52,124,120⟩,[],[(7,3,2),(8,4,3),(0,6,5)],⟨7,19,76,152,304,98,193,424,300⟩,⟨7,19,76,152,304,98,193,384,260⟩,[⟨1,1437223914350366447894529,⟨77,477,76,408,444,508,197,384,260⟩⟩,⟨3,1210109878330860011496709,⟨39,19,103,242,307,98,243,499,311⟩⟩]⟩
theorem node718 : UpperPrefix a [2,4,6,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,1,0] 30 cert718 (by decide +kernel)

def cert719 : Local := ⟨⟨112,100,0,359,71,21,0,119,115⟩,[(2,6),(6,3)],[(7,3,2),(7,3,6),(8,4,3),(3,6,2)]⟩
theorem node719 : UpperPrefix a [2,4,6,7,8,1,3] 30 :=
  local_sound a [2,4,6,7,8,1,3] 30 cert719 (by decide +kernel)

def cert720 : Leaf := ⟨⟨112,96,177,353,65,17,17,116,121⟩,[],[(2,0,7),(7,3,2),(8,4,3)],⟨7,19,76,152,304,98,224,385,268⟩,⟨7,19,76,152,304,98,224,385,260⟩,[⟨1,1809876355191769748471809,⟨397,413,348,412,380,508,508,385,260⟩⟩,⟨3,1212623725120229020476673,⟨103,243,100,242,499,98,242,499,503⟩⟩]⟩
theorem node720 : UpperPrefix a [2,4,6,7,8,1,5,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,1,5,0] 30 cert720 (by decide +kernel)

def cert721 : Leaf := ⟨⟨80,68,145,325,69,21,21,85,81⟩,[],[(7,3,2),(8,4,3)],⟨7,19,76,152,304,98,224,392,261⟩,⟨7,19,76,152,304,98,224,392,260⟩,[⟨1,1224745921399683026518017,⟨397,477,76,220,508,508,252,396,260⟩⟩,⟨3,1233721854860739910774533,⟨311,275,375,242,307,98,242,499,311⟩⟩,⟨5,1763205515092024544474165,⟨399,411,463,411,415,463,453,394,389⟩⟩]⟩
theorem node721 : UpperPrefix a [2,4,6,7,8,1,5,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,1,5,3] 30 cert721 (by decide +kernel)

theorem node722 : UpperPrefix a [2,4,6,7,8,1,5] 30 :=
  branch_upper a [2,4,6,7,8,1,5] 30 (by decide) (fin9_cases _
  node720
  (invalid_upper a [2,4,6,7,8,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,5,2] 30 (by decide +kernel))
  node721
  (invalid_upper a [2,4,6,7,8,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,5,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,5,8] 30 (by decide +kernel)))

theorem node723 : UpperPrefix a [2,4,6,7,8,1] 30 :=
  branch_upper a [2,4,6,7,8,1] 30 (by decide) (fin9_cases _
  node718
  (invalid_upper a [2,4,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,2] 30 (by decide +kernel))
  node719
  (invalid_upper a [2,4,6,7,8,1,4] 30 (by decide +kernel))
  node722
  (invalid_upper a [2,4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,1,8] 30 (by decide +kernel)))

def cert724 : Leaf := ⟨⟨120,108,0,352,72,0,47,111,107⟩,[(2,5),(5,2)],[(7,3,2),(7,3,5),(8,4,3)],⟨7,19,76,152,304,104,227,419,295⟩,⟨7,19,76,152,304,104,192,384,260⟩,[⟨4,1214839173292794680706049,⟨487,451,108,136,292,108,192,384,292⟩⟩,⟨0,1210107567693998379238400,⟨38,18,108,152,308,108,236,408,308⟩⟩,⟨1,1210107567693998379237377,⟨37,17,108,152,308,108,236,408,308⟩⟩,⟨2,1210107567693998353024001,⟨35,19,104,152,304,104,232,408,304⟩⟩]⟩
theorem node724 : UpperPrefix a [2,4,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,8,3] 30 cert724 (by decide +kernel)

theorem node725 : UpperPrefix a [2,4,6,7,8] 30 :=
  branch_upper a [2,4,6,7,8] 30 (by decide) (fin9_cases _
  node717
  node723
  (invalid_upper a [2,4,6,7,8,2] 30 (by decide +kernel))
  node724
  (invalid_upper a [2,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,8,8] 30 (by decide +kernel)))

theorem node726 : UpperPrefix a [2,4,6,7] 30 :=
  branch_upper a [2,4,6,7] 30 (by decide) (fin9_cases _
  node687
  node694
  (invalid_upper a [2,4,6,7,2] 30 (by decide +kernel))
  node711
  (invalid_upper a [2,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,7] 30 (by decide +kernel))
  node725)

def cert727 : Leaf := ⟨⟨368,0,304,100,322,272,312,120,248⟩,[(1,4)],[(0,4,1),(1,5,4)],⟨7,19,76,280,49,98,232,424,428⟩,⟨7,19,76,280,49,98,192,384,260⟩,[⟨7,1208926976080255986696037,⟨55,19,127,283,51,119,127,283,319⟩⟩,⟨2,1210181568749794144298497,⟨115,51,232,506,51,114,192,384,320⟩⟩,⟨3,1210107567694323698056965,⟨55,19,119,275,51,98,226,403,311⟩⟩]⟩
theorem node727 : UpperPrefix a [2,4,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,0,1] 30 cert727 (by decide +kernel)

def cert728 : Leaf := ⟨⟨504,0,0,230,458,0,298,106,234⟩,[(1,4),(2,5),(5,2)],[(0,4,1)],⟨7,19,76,280,49,104,226,418,422⟩,⟨7,19,76,280,49,104,192,384,260⟩,[⟨2,1210181496797615783683585,⟨51,19,232,506,51,232,192,384,288⟩⟩,⟨4,1214839173292794680706049,⟨487,451,108,264,485,108,192,384,292⟩⟩]⟩
theorem node728 : UpperPrefix a [2,4,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,8,0,3] 30 cert728 (by decide +kernel)

def cert729 : Leaf := ⟨⟨368,0,306,102,322,0,314,122,122⟩,[(1,4),(5,6)],[(0,4,1),(7,5,5)],⟨7,19,76,280,49,224,234,426,302⟩,⟨7,19,76,280,49,224,192,384,260⟩,[⟨2,1210181499049415597368833,⟨51,19,232,506,51,224,224,384,288⟩⟩,⟨3,1210107567535925304114949,⟨23,19,119,275,51,224,224,387,279⟩⟩]⟩
theorem node729 : UpperPrefix a [2,4,6,8,0,7] 30 :=
  Boolean.leaf_sound a [2,4,6,8,0,7] 30 cert729 (by decide +kernel)

theorem node730 : UpperPrefix a [2,4,6,8,0] 30 :=
  branch_upper a [2,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,0,0] 30 (by decide +kernel))
  node727
  (invalid_upper a [2,4,6,8,0,2] 30 (by decide +kernel))
  node728
  (invalid_upper a [2,4,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,0,6] 30 (by decide +kernel))
  node729
  (invalid_upper a [2,4,6,8,0,8] 30 (by decide +kernel)))

def cert731 : Leaf := ⟨⟨112,96,304,100,65,20,316,124,248⟩,[],[(1,4,1),(0,5,4)],⟨7,19,76,280,50,97,232,424,428⟩,⟨7,19,76,280,50,97,192,384,260⟩,[⟨7,1208926976080255986696037,⟨55,19,127,283,51,119,127,283,319⟩⟩,⟨3,1210107565444722907635461,⟨55,19,119,275,50,115,194,403,311⟩⟩,⟨8,1181745830094806671109,⟨55,19,127,27,50,115,194,147,55⟩⟩,⟨2,1210107565286050708341761,⟨3,19,72,280,50,115,192,384,256⟩⟩]⟩
theorem node731 : UpperPrefix a [2,4,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,1,0] 30 cert731 (by decide +kernel)

def cert732 : Leaf := ⟨⟨104,108,0,101,77,0,301,109,233⟩,[(2,5),(5,2)],[(1,4,1)],⟨7,19,76,280,50,104,225,417,421⟩,⟨7,19,76,280,50,104,192,384,260⟩,[⟨4,1328397762437589886829585,⟨487,451,492,493,487,492,192,384,292⟩⟩,⟨7,1208926976080255995084661,⟨55,19,127,283,55,127,127,283,319⟩⟩,⟨8,1181745830094815067957,⟨55,19,127,27,55,127,194,147,55⟩⟩]⟩
theorem node732 : UpperPrefix a [2,4,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,8,1,3] 30 cert732 (by decide +kernel)

def cert733 : Leaf := ⟨⟨368,356,304,100,324,0,308,124,120⟩,[(5,6)],[(1,4,1),(7,5,5)],⟨7,19,76,280,50,224,193,424,300⟩,⟨7,19,76,280,50,224,193,384,260⟩,[⟨0,1763703580700529371644928,⟨446,410,492,408,446,492,508,384,420⟩⟩,⟨3,1210109877897927308058373,⟨23,19,119,275,50,242,243,499,279⟩⟩]⟩
theorem node733 : UpperPrefix a [2,4,6,8,1,7,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,1,7,0] 30 cert733 (by decide +kernel)

def cert734 : Local := ⟨⟨112,100,0,101,69,0,309,117,113⟩,[(2,6),(5,6)],[(8,3,6),(1,4,1),(7,5,5),(3,6,2)]⟩
theorem node734 : UpperPrefix a [2,4,6,8,1,7,3] 30 :=
  local_sound a [2,4,6,8,1,7,3] 30 cert734 (by decide +kernel)

def cert735 : Leaf := ⟨⟨368,356,305,69,325,0,0,93,89⟩,[(5,6),(6,5)],[(1,4,1),(7,5,5),(7,5,6)],⟨7,19,76,280,50,224,224,393,269⟩,⟨7,19,76,280,50,224,224,384,260⟩,[⟨3,1210110454358679611449093,⟨23,19,119,275,114,242,242,499,279⟩⟩,⟨5,1214857600756932257252353,⟨399,411,76,280,154,192,192,384,260⟩⟩]⟩
theorem node735 : UpperPrefix a [2,4,6,8,1,7,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,1,7,5] 30 cert735 (by decide +kernel)

theorem node736 : UpperPrefix a [2,4,6,8,1,7] 30 :=
  branch_upper a [2,4,6,8,1,7] 30 (by decide) (fin9_cases _
  node733
  (invalid_upper a [2,4,6,8,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,7,2] 30 (by decide +kernel))
  node734
  (invalid_upper a [2,4,6,8,1,7,4] 30 (by decide +kernel))
  node735
  (invalid_upper a [2,4,6,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,7,8] 30 (by decide +kernel)))

theorem node737 : UpperPrefix a [2,4,6,8,1] 30 :=
  branch_upper a [2,4,6,8,1] 30 (by decide) (fin9_cases _
  node731
  (invalid_upper a [2,4,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,2] 30 (by decide +kernel))
  node732
  (invalid_upper a [2,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,1,6] 30 (by decide +kernel))
  node736
  (invalid_upper a [2,4,6,8,1,8] 30 (by decide +kernel)))

def cert738 : Leaf := ⟨⟨120,108,304,100,68,22,52,116,240⟩,[],[(1,6,5)],⟨7,19,76,280,56,97,194,416,420⟩,⟨7,19,76,280,56,97,194,384,260⟩,[⟨0,1437223914350366464672768,⟨78,478,76,408,444,508,206,384,260⟩⟩,⟨7,1208926976077988243963749,⟨55,19,127,283,59,119,127,283,319⟩⟩,⟨8,1184056156843718876933,⟨55,19,127,27,58,99,226,227,55⟩⟩,⟨3,1215152803936758819456001,⟨487,499,68,272,176,481,226,384,260⟩⟩]⟩
theorem node738 : UpperPrefix a [2,4,6,8,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,0,1] 30 cert738 (by decide +kernel)

def cert739 : Leaf := ⟨⟨40,44,290,38,6,14,14,46,170⟩,[],[],⟨7,19,76,280,56,97,224,386,390⟩,⟨7,19,76,280,56,97,224,384,260⟩,[⟨0,1224302911315925152039936,⟨398,414,92,284,124,508,252,384,260⟩⟩,⟨4,1224302965456972626789379,⟨487,487,76,268,108,481,224,384,260⟩⟩,⟨6,1236512926510464472472837,⟨399,411,415,411,186,443,186,385,399⟩⟩,⟨7,1208926976077988243963749,⟨55,19,127,283,59,119,127,283,319⟩⟩,⟨8,1184056156843718876933,⟨55,19,127,27,58,99,224,227,55⟩⟩]⟩
theorem node739 : UpperPrefix a [2,4,6,8,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,0,5] 30 cert739 (by decide +kernel)

theorem node740 : UpperPrefix a [2,4,6,8,3,0] 30 :=
  branch_upper a [2,4,6,8,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,3,0,0] 30 (by decide +kernel))
  node738
  (invalid_upper a [2,4,6,8,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,0,4] 30 (by decide +kernel))
  node739
  (invalid_upper a [2,4,6,8,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,0,8] 30 (by decide +kernel)))

def cert741 : Leaf := ⟨⟨360,360,288,96,320,265,300,104,232⟩,[],[(0,6,5)],⟨7,19,76,280,56,98,193,416,420⟩,⟨7,19,76,280,56,98,193,384,260⟩,[⟨1,1437223914350366447894529,⟨77,477,76,408,444,508,197,384,260⟩⟩,⟨4,1300893846851014685099011,⟨487,487,204,396,492,483,481,384,260⟩⟩,⟨7,1208926976077988243963749,⟨55,19,127,283,59,119,127,283,319⟩⟩,⟨2,1212468750940140459820545,⟨51,19,122,408,56,114,251,408,440⟩⟩]⟩
theorem node741 : UpperPrefix a [2,4,6,8,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,1,0] 30 cert741 (by decide +kernel)

def cert742 : Leaf := ⟨⟨72,76,257,69,69,13,13,77,201⟩,[],[],⟨7,19,76,280,56,98,224,385,389⟩,⟨7,19,76,280,56,98,224,384,260⟩,[⟨1,1224302911315925152038913,⟨397,413,92,284,124,508,252,384,260⟩⟩,⟨4,1224598401592528133424131,⟨487,487,76,332,236,483,224,384,260⟩⟩,⟨5,1766156994143818072732725,⟨399,411,463,411,415,463,453,384,389⟩⟩,⟨7,1208926976077988243963749,⟨55,19,127,283,59,119,127,283,319⟩⟩,⟨8,1184056156843718876933,⟨55,19,127,27,58,98,224,227,55⟩⟩]⟩
theorem node742 : UpperPrefix a [2,4,6,8,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,1,5] 30 cert742 (by decide +kernel)

theorem node743 : UpperPrefix a [2,4,6,8,3,1] 30 :=
  branch_upper a [2,4,6,8,3,1] 30 (by decide) (fin9_cases _
  node741
  (invalid_upper a [2,4,6,8,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,1,4] 30 (by decide +kernel))
  node742
  (invalid_upper a [2,4,6,8,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,1,8] 30 (by decide +kernel)))

def cert744 : Leaf := ⟨⟨120,104,307,98,66,0,39,103,99⟩,[(5,6)],[(7,5,5)],⟨7,19,76,280,56,224,227,419,295⟩,⟨7,19,76,280,56,224,192,384,260⟩,[⟨8,1184058267906044206853,⟨23,19,127,27,58,224,224,227,23⟩⟩,⟨2,1210107567535960736400897,⟨19,19,120,280,56,224,224,392,280⟩⟩,⟨3,1214857658283379280315393,⟨487,499,100,272,48,224,224,384,260⟩⟩,⟨4,1214857658282280842429441,⟨487,483,108,264,40,224,224,384,260⟩⟩,⟨0,1210107567535960737448960,⟨22,18,124,280,56,224,224,392,284⟩⟩]⟩
theorem node744 : UpperPrefix a [2,4,6,8,3,7] 30 :=
  Boolean.leaf_sound a [2,4,6,8,3,7] 30 cert744 (by decide +kernel)

theorem node745 : UpperPrefix a [2,4,6,8,3] 30 :=
  branch_upper a [2,4,6,8,3] 30 (by decide) (fin9_cases _
  node740
  node743
  (invalid_upper a [2,4,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,3,6] 30 (by decide +kernel))
  node744
  (invalid_upper a [2,4,6,8,3,8] 30 (by decide +kernel)))

def cert746 : Leaf := ⟨⟨112,228,48,100,68,22,52,124,120⟩,[],[(1,6,5)],⟨7,19,76,280,176,97,194,424,300⟩,⟨7,19,76,280,176,97,194,384,260⟩,[⟨0,1437223914350366464672768,⟨78,478,76,408,444,508,206,384,260⟩⟩,⟨8,1184344751982855150861,⟨39,115,127,127,242,115,242,243,39⟩⟩,⟨3,1210110164366610954018053,⟨39,115,119,371,242,115,242,499,295⟩⟩,⟨7,1534770263373677381813313,⟨303,283,365,280,48,357,367,256,292⟩⟩]⟩
theorem node746 : UpperPrefix a [2,4,6,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,0,1] 30 cert746 (by decide +kernel)

def cert747 : Leaf := ⟨⟨240,228,0,228,69,148,308,116,240⟩,[(2,6)],[(8,3,6),(3,6,2)],⟨7,19,76,280,176,97,200,386,292⟩,⟨7,19,76,280,176,97,200,386,260⟩,[⟨1,2055413759870096633233409,⟨301,381,76,348,508,365,476,508,260⟩⟩,⟨0,1436802251322251733107712,⟨206,478,76,348,508,356,204,462,260⟩⟩]⟩
theorem node747 : UpperPrefix a [2,4,6,8,7,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,0,3,1] 30 cert747 (by decide +kernel)

def cert748 : Local := ⟨⟨208,196,0,199,0,150,279,87,211⟩,[(2,6),(4,7)],[(8,3,6),(3,6,2),(5,7,4)]⟩
theorem node748 : UpperPrefix a [2,4,6,8,7,0,3,5] 30 :=
  local_sound a [2,4,6,8,7,0,3,5] 30 cert748 (by decide +kernel)

theorem node749 : UpperPrefix a [2,4,6,8,7,0,3] 30 :=
  branch_upper a [2,4,6,8,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,7,0,3,0] 30 (by decide +kernel))
  node747
  (invalid_upper a [2,4,6,8,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,3,4] 30 (by decide +kernel))
  node748
  (invalid_upper a [2,4,6,8,7,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,3,8] 30 (by decide +kernel)))

def cert750 : Leaf := ⟨⟨176,164,178,166,0,150,0,62,186⟩,[(4,6),(6,4)],[],⟨7,19,76,280,176,97,224,394,270⟩,⟨7,19,76,280,176,97,224,384,260⟩,[⟨6,1236512926510464472472837,⟨399,411,415,411,186,443,186,385,399⟩⟩,⟨0,1224303199546301306373120,⟨398,478,92,348,252,508,252,384,260⟩⟩,⟨8,1184344751982855150861,⟨39,115,127,127,242,115,242,243,39⟩⟩,⟨3,1210110164366610954018053,⟨39,115,119,371,242,115,242,499,295⟩⟩]⟩
theorem node750 : UpperPrefix a [2,4,6,8,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,0,5] 30 cert750 (by decide +kernel)

theorem node751 : UpperPrefix a [2,4,6,8,7,0] 30 :=
  branch_upper a [2,4,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,8,7,0,0] 30 (by decide +kernel))
  node746
  (invalid_upper a [2,4,6,8,7,0,2] 30 (by decide +kernel))
  node749
  (invalid_upper a [2,4,6,8,7,0,4] 30 (by decide +kernel))
  node750
  (invalid_upper a [2,4,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,0,8] 30 (by decide +kernel)))

def cert752 : Leaf := ⟨⟨368,352,304,96,320,273,308,120,120⟩,[],[(0,6,5)],⟨7,19,76,280,176,98,193,424,300⟩,⟨7,19,76,280,176,98,193,384,260⟩,[⟨1,1437223914350366447894529,⟨77,477,76,408,444,508,197,384,260⟩⟩,⟨7,1459212397395965383816245,⟨303,283,367,283,319,367,321,256,293⟩⟩,⟨2,1212468750939865581913089,⟨35,19,122,408,184,114,251,408,440⟩⟩,⟨3,1210109878599140848540933,⟨39,51,119,307,242,114,243,499,295⟩⟩]⟩
theorem node752 : UpperPrefix a [2,4,6,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,1,0] 30 cert752 (by decide +kernel)

def cert753 : Leaf := ⟨⟨64,68,0,103,71,21,295,103,99⟩,[(2,6)],[(8,3,6),(3,6,2)],⟨7,19,76,280,176,98,200,417,293⟩,⟨7,19,76,280,176,98,200,384,260⟩,[⟨7,1761443854551422507955317,⟨303,283,367,283,319,367,367,256,293⟩⟩,⟨4,1361666158707537945297953,⟨7,131,76,460,417,487,204,384,260⟩⟩,⟨5,1210107564157951796061217,⟨7,19,76,282,147,71,204,384,260⟩⟩]⟩
theorem node753 : UpperPrefix a [2,4,6,8,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,1,3] 30 cert753 (by decide +kernel)

def cert754 : Leaf := ⟨⟨280,268,275,7,0,285,0,31,27⟩,[(4,6),(6,4)],[],⟨7,19,76,280,176,98,224,393,269⟩,⟨7,19,76,280,176,98,224,384,260⟩,[⟨5,1460974060188367250797621,⟨399,411,463,411,415,463,453,384,389⟩⟩,⟨7,1459212397395965383816245,⟨303,283,367,283,319,367,357,256,293⟩⟩,⟨6,1236217778605280824663301,⟨399,411,415,411,176,186,176,385,399⟩⟩]⟩
theorem node754 : UpperPrefix a [2,4,6,8,7,1,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,1,5] 30 cert754 (by decide +kernel)

theorem node755 : UpperPrefix a [2,4,6,8,7,1] 30 :=
  branch_upper a [2,4,6,8,7,1] 30 (by decide) (fin9_cases _
  node752
  (invalid_upper a [2,4,6,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,1,2] 30 (by decide +kernel))
  node753
  (invalid_upper a [2,4,6,8,7,1,4] 30 (by decide +kernel))
  node754
  (invalid_upper a [2,4,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,1,8] 30 (by decide +kernel)))

def cert756 : Leaf := ⟨⟨344,332,0,102,334,0,270,110,106⟩,[(2,5),(5,2)],[],⟨7,19,76,280,176,104,193,418,294⟩,⟨7,19,76,280,176,104,193,384,260⟩,[⟨0,1214839157535771271889920,⟨446,410,124,280,180,124,508,384,292⟩⟩,⟨7,1459212397395965383816245,⟨303,283,367,283,319,367,321,256,293⟩⟩,⟨4,1214839209321591699670017,⟨487,451,108,264,164,108,449,384,292⟩⟩,⟨5,1210107852388327941485629,⟨7,83,79,351,215,79,193,384,261⟩⟩]⟩
theorem node756 : UpperPrefix a [2,4,6,8,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,3,0] 30 cert756 (by decide +kernel)

def cert757 : Leaf := ⟨⟨344,332,0,101,333,0,269,109,105⟩,[(2,5),(5,2)],[],⟨7,19,76,280,176,104,194,417,293⟩,⟨7,19,76,280,176,104,194,384,260⟩,[⟨1,1214839157535762681954305,⟨445,409,124,280,180,124,252,384,292⟩⟩,⟨7,1761443854551422507955317,⟨303,283,367,283,319,367,367,256,293⟩⟩,⟨4,1214839209321591699670017,⟨487,451,108,264,164,108,194,384,292⟩⟩,⟨5,1210107852388327941485629,⟨7,83,79,351,215,79,194,384,261⟩⟩]⟩
theorem node757 : UpperPrefix a [2,4,6,8,7,3,1] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,3,1] 30 cert757 (by decide +kernel)

def cert758 : Leaf := ⟨⟨472,460,0,199,0,0,0,95,219⟩,[(2,5),(4,6),(5,2),(6,4)],[],⟨7,19,76,280,176,104,224,387,263⟩,⟨7,19,76,280,176,104,224,384,260⟩,[⟨5,1460974060188367250797621,⟨399,411,463,411,415,463,453,384,389⟩⟩]⟩
theorem node758 : UpperPrefix a [2,4,6,8,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,6,8,7,3,5] 30 cert758 (by decide +kernel)

theorem node759 : UpperPrefix a [2,4,6,8,7,3] 30 :=
  branch_upper a [2,4,6,8,7,3] 30 (by decide) (fin9_cases _
  node756
  node757
  (invalid_upper a [2,4,6,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,3,4] 30 (by decide +kernel))
  node758
  (invalid_upper a [2,4,6,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,3,8] 30 (by decide +kernel)))

theorem node760 : UpperPrefix a [2,4,6,8,7] 30 :=
  branch_upper a [2,4,6,8,7] 30 (by decide) (fin9_cases _
  node751
  node755
  (invalid_upper a [2,4,6,8,7,2] 30 (by decide +kernel))
  node759
  (invalid_upper a [2,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,7,8] 30 (by decide +kernel)))

theorem node761 : UpperPrefix a [2,4,6,8] 30 :=
  branch_upper a [2,4,6,8] 30 (by decide) (fin9_cases _
  node730
  node737
  (invalid_upper a [2,4,6,8,2] 30 (by decide +kernel))
  node745
  (invalid_upper a [2,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,8,6] 30 (by decide +kernel))
  node760
  (invalid_upper a [2,4,6,8,8] 30 (by decide +kernel)))

theorem node762 : UpperPrefix a [2,4,6] 30 :=
  branch_upper a [2,4,6] 30 (by decide) (fin9_cases _
  node622
  node644
  (invalid_upper a [2,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,4] 30 (by decide +kernel))
  node680
  (invalid_upper a [2,4,6,6] 30 (by decide +kernel))
  node726
  node761)

def cert763 : Leaf := ⟨⟨504,0,352,0,460,396,300,108,232⟩,[(1,3),(3,1)],[(1,4,1),(1,4,3)],⟨7,19,140,25,50,360,488,488,364⟩,⟨7,19,140,25,50,96,192,384,260⟩,[⟨0,1266886860137792986416128,⟨502,18,492,508,50,96,192,384,484⟩⟩,⟨4,1266886860136624755311617,⟨487,3,492,493,34,96,192,384,484⟩⟩]⟩
theorem node763 : UpperPrefix a [2,4,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,7,0,1] 30 cert763 (by decide +kernel)

def cert764 : Leaf := ⟨⟨496,0,354,0,454,390,294,102,226⟩,[(1,3),(3,1)],[],⟨7,19,140,25,56,354,482,482,358⟩,⟨7,19,140,25,56,96,192,384,260⟩,[⟨0,1214857656032130298283008,⟨486,498,156,508,60,96,192,384,260⟩⟩,⟨3,1233858019022494883648517,⟨487,499,487,499,242,96,192,384,485⟩⟩,⟨4,1214857656030481030841345,⟨487,483,140,493,44,96,192,384,260⟩⟩]⟩
theorem node764 : UpperPrefix a [2,4,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,7,0,3] 30 cert764 (by decide +kernel)

def cert765 : Leaf := ⟨⟨184,0,49,0,0,157,317,61,185⟩,[(1,3),(3,1),(4,5)],[(6,4,4)],⟨7,19,140,25,112,98,488,424,300⟩,⟨7,19,140,25,112,98,192,384,260⟩,[⟨1,1361519017103811289284609,⟨13,25,140,25,500,508,192,384,260⟩⟩,⟨8,1181748490584665945205,⟨15,59,143,59,127,127,255,128,5⟩⟩]⟩
theorem node765 : UpperPrefix a [2,4,7,0,6,1] 30 :=
  Boolean.leaf_sound a [2,4,7,0,6,1] 30 cert765 (by decide +kernel)

def cert766 : Leaf := ⟨⟨144,0,51,0,0,151,319,63,187⟩,[(1,3),(3,1),(4,5)],[(6,4,4)],⟨7,19,140,25,112,104,482,418,294⟩,⟨7,19,140,25,112,104,192,384,260⟩,[⟨8,1181748490584665945205,⟨15,59,143,59,127,127,255,128,5⟩⟩,⟨3,1210107565286049635636229,⟨7,19,135,19,112,114,192,384,261⟩⟩,⟨5,1210107564157952047715333,⟨15,27,143,27,80,74,192,384,261⟩⟩]⟩
theorem node766 : UpperPrefix a [2,4,7,0,6,3] 30 :=
  Boolean.leaf_sound a [2,4,7,0,6,3] 30 cert766 (by decide +kernel)

def cert767 : Leaf := ⟨⟨440,0,306,0,0,158,316,62,186⟩,[(1,3),(3,1),(4,5)],[(6,4,4)],⟨7,19,140,25,112,352,194,424,300⟩,⟨7,19,140,25,112,352,194,384,260⟩,[⟨0,1266886661876742483870720,⟨502,114,444,508,112,368,210,384,388⟩⟩]⟩
theorem node767 : UpperPrefix a [2,4,7,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,7,0,6,8,1] 30 cert767 (by decide +kernel)

#print axioms node767
end Delivery.FiniteExclusion.Sharp2x7
