import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C007
import RegularNineSharp2x3x4C008
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
theorem node576 : UpperPrefix a [2,5,7,8,6,4,0] 30 :=
  branch_upper a [2,5,7,8,6,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,6,4,0,0] 30 (by decide +kernel))
  node574
  (invalid_upper a [2,5,7,8,6,4,0,2] 30 (by decide +kernel))
  node575
  (invalid_upper a [2,5,7,8,6,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,0,8] 30 (by decide +kernel)))

def cert577 : Leaf := ⟨⟨48,20,305,37,161,0,53,61,29⟩,[(5,4)],[(7,2,4),(8,3,2),(6,4,5)],⟨7,35,140,280,84,112,194,393,297⟩,⟨7,35,140,280,84,112,194,384,288⟩,[⟨1,1219579971187091646971905,⟨397,445,140,312,124,124,508,396,312⟩⟩,⟨3,1210107638080660061584917,⟨119,51,247,307,119,115,194,384,290⟩⟩]⟩
theorem node577 : UpperPrefix a [2,5,7,8,6,4,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,4,1] 30 cert577 (by decide +kernel)

def cert578 : Local := ⟨⟨48,20,0,39,171,0,0,55,23⟩,[(2,6),(5,4),(6,2)],[(7,2,4),(8,3,2),(8,3,6),(6,4,5),(3,6,4)]⟩
theorem node578 : UpperPrefix a [2,5,7,8,6,4,3] 30 :=
  local_sound a [2,5,7,8,6,4,3] 30 cert578 (by decide +kernel)

theorem node579 : UpperPrefix a [2,5,7,8,6,4] 30 :=
  branch_upper a [2,5,7,8,6,4] 30 (by decide) (fin9_cases _
  node576
  node577
  (invalid_upper a [2,5,7,8,6,4,2] 30 (by decide +kernel))
  node578
  (invalid_upper a [2,5,7,8,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,4,8] 30 (by decide +kernel)))

theorem node580 : UpperPrefix a [2,5,7,8,6] 30 :=
  branch_upper a [2,5,7,8,6] 30 (by decide) (fin9_cases _
  node566
  node567
  (invalid_upper a [2,5,7,8,6,2] 30 (by decide +kernel))
  node573
  node579
  (invalid_upper a [2,5,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,8] 30 (by decide +kernel)))

theorem node581 : UpperPrefix a [2,5,7,8] 30 :=
  branch_upper a [2,5,7,8] 30 (by decide) (fin9_cases _
  node552
  node558
  (invalid_upper a [2,5,7,8,2] 30 (by decide +kernel))
  node562
  (invalid_upper a [2,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,5] 30 (by decide +kernel))
  node580
  (invalid_upper a [2,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,8] 30 (by decide +kernel)))

theorem node582 : UpperPrefix a [2,5,7] 30 :=
  branch_upper a [2,5,7] 30 (by decide) (fin9_cases _
  node464
  node505
  (invalid_upper a [2,5,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,5] 30 (by decide +kernel))
  node544
  (invalid_upper a [2,5,7,7] 30 (by decide +kernel))
  node581)

def cert583 : Leaf := ⟨⟨0,408,176,422,0,408,312,120,216⟩,[(0,4),(4,0)],[(2,0,3),(1,4,3)],⟨7,35,268,25,22,248,216,472,504⟩,⟨7,35,268,25,22,96,192,384,288⟩,[⟨0,1247960428519835460174848,⟨22,50,492,508,22,96,192,384,288⟩⟩,⟨6,1210106412389142273066389,⟨31,59,287,25,31,40,157,415,319⟩⟩]⟩
theorem node583 : UpperPrefix a [2,5,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,1] 30 cert583 (by decide +kernel)

def cert584 : Leaf := ⟨⟨304,272,50,294,0,402,306,114,210⟩,[(4,2)],[(2,0,3),(3,4,4)],⟨7,35,268,25,28,242,210,466,498⟩,⟨7,35,268,25,28,96,192,384,288⟩,[⟨0,1214839173189165703496704,⟨502,482,284,508,28,96,192,384,288⟩⟩,⟨6,1210106412393540319577477,⟨31,59,287,25,29,56,157,415,319⟩⟩,⟨7,1208926973694327515121029,⟨31,59,287,25,29,120,93,287,319⟩⟩]⟩
theorem node584 : UpperPrefix a [2,5,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,8,0,3] 30 cert584 (by decide +kernel)

def cert585 : Leaf := ⟨⟨120,88,240,68,392,24,280,88,216⟩,[],[(2,0,3),(1,5,1)],⟨7,35,268,25,84,98,216,408,440⟩,⟨7,35,268,25,84,98,192,384,288⟩,[⟨0,1247997393820110946305024,⟨246,50,476,508,212,98,192,384,288⟩⟩,⟨5,1210144547718435745825793,⟨223,91,476,89,212,74,192,384,256⟩⟩,⟨7,1208926974226086375732245,⟨7,35,271,59,127,98,64,256,288⟩⟩,⟨8,1181746232174612329493,⟨7,35,15,59,127,98,192,128,32⟩⟩]⟩
theorem node585 : UpperPrefix a [2,5,8,0,6,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,1] 30 cert585 (by decide +kernel)

def cert586 : Leaf := ⟨⟨120,88,240,100,416,16,304,112,208⟩,[],[(2,0,3)],⟨7,35,268,25,84,104,194,400,432⟩,⟨7,35,268,25,84,104,194,384,288⟩,[⟨0,1430869029313596198224896,⟨470,502,444,508,468,508,466,384,436⟩⟩,⟨1,1751943781219319525670913,⟨397,445,396,413,500,508,508,384,436⟩⟩,⟨3,1219580022408964715054081,⟨471,499,260,209,84,96,450,384,288⟩⟩,⟨7,1208926974226086375732245,⟨7,35,271,59,127,106,66,256,288⟩⟩,⟨8,1181746232174612329493,⟨7,35,15,59,127,106,194,128,32⟩⟩]⟩
theorem node586 : UpperPrefix a [2,5,8,0,6,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,3,1] 30 cert586 (by decide +kernel)

def cert587 : Leaf := ⟨⟨424,392,162,422,418,402,290,34,130⟩,[],[(2,0,3),(4,6,5)],⟨7,35,268,25,84,104,208,386,418⟩,⟨7,35,268,25,84,104,208,384,288⟩,[⟨0,1224302533432259634004992,⟨502,498,380,508,116,124,208,384,304⟩⟩,⟨6,1373387767530789331420455,⟨391,423,399,153,157,431,152,387,423⟩⟩,⟨3,1219580166524427668816897,⟨471,499,340,209,84,96,208,384,288⟩⟩]⟩
theorem node587 : UpperPrefix a [2,5,8,0,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,3,4] 30 cert587 (by decide +kernel)

theorem node588 : UpperPrefix a [2,5,8,0,6,3] 30 :=
  branch_upper a [2,5,8,0,6,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,6,3,0] 30 (by decide +kernel))
  node586
  (invalid_upper a [2,5,8,0,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,3,3] 30 (by decide +kernel))
  node587
  (invalid_upper a [2,5,8,0,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,3,8] 30 (by decide +kernel)))

def cert589 : Leaf := ⟨⟨440,408,176,420,424,0,312,56,152⟩,[(5,4)],[(2,0,3),(6,4,5)],⟨7,35,268,25,84,112,194,392,424⟩,⟨7,35,268,25,84,112,194,384,288⟩,[⟨0,1266886662507724719260672,⟨502,114,444,508,500,112,226,384,288⟩⟩,⟨1,1560291334228464084189185,⟨397,445,396,445,500,500,508,384,304⟩⟩]⟩
theorem node589 : UpperPrefix a [2,5,8,0,6,4,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,4,1] 30 cert589 (by decide +kernel)

def cert590 : Leaf := ⟨⟨304,272,50,294,426,0,306,50,146⟩,[(5,4)],[(2,0,3),(6,4,5),(3,6,4)],⟨7,35,268,25,84,112,200,386,418⟩,⟨7,35,268,25,84,112,200,384,288⟩,[⟨0,1224302482205944176444416,⟨438,418,380,508,116,112,252,384,288⟩⟩,⟨7,1208926974226090737956245,⟨7,43,271,59,127,123,75,263,303⟩⟩]⟩
theorem node590 : UpperPrefix a [2,5,8,0,6,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,4,3] 30 cert590 (by decide +kernel)

theorem node591 : UpperPrefix a [2,5,8,0,6,4] 30 :=
  branch_upper a [2,5,8,0,6,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,6,4,0] 30 (by decide +kernel))
  node589
  (invalid_upper a [2,5,8,0,6,4,2] 30 (by decide +kernel))
  node590
  (invalid_upper a [2,5,8,0,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,4,8] 30 (by decide +kernel)))

def cert592 : Leaf := ⟨⟨376,344,112,356,296,0,312,120,88⟩,[(5,6)],[(2,0,3),(7,5,5)],⟨7,35,268,25,84,224,194,408,312⟩,⟨7,35,268,25,84,224,194,384,288⟩,[⟨0,1266886664689155788768256,⟨502,114,444,508,500,224,226,384,288⟩⟩,⟨1,1560245217368279810310145,⟨397,445,396,445,500,500,508,384,304⟩⟩]⟩
theorem node592 : UpperPrefix a [2,5,8,0,6,7,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,7,1] 30 cert592 (by decide +kernel)

def cert593 : Local := ⟨⟨336,336,83,326,267,0,275,113,83⟩,[(5,6)],[(2,0,3),(5,1,7),(7,5,5),(3,6,4)]⟩
theorem node593 : UpperPrefix a [2,5,8,0,6,7,3,1] 30 :=
  local_sound a [2,5,8,0,6,7,3,1] 30 cert593 (by decide +kernel)

def cert594 : Leaf := ⟨⟨352,320,98,358,298,0,306,98,66⟩,[(5,6)],[(2,0,3),(7,5,5),(3,6,4),(4,7,6)],⟨7,35,268,25,84,224,200,400,290⟩,⟨7,35,268,25,84,224,200,400,288⟩,[⟨0,1224413234763233563247616,⟨502,434,508,508,244,240,252,432,288⟩⟩]⟩
theorem node594 : UpperPrefix a [2,5,8,0,6,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,7,3,4] 30 cert594 (by decide +kernel)

theorem node595 : UpperPrefix a [2,5,8,0,6,7,3] 30 :=
  branch_upper a [2,5,8,0,6,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,6,7,3,0] 30 (by decide +kernel))
  node593
  (invalid_upper a [2,5,8,0,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,7,3,3] 30 (by decide +kernel))
  node594
  (invalid_upper a [2,5,8,0,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,7,3,8] 30 (by decide +kernel)))

def cert596 : Leaf := ⟨⟨96,64,99,102,299,0,299,107,75⟩,[(5,6)],[(2,0,3),(7,5,5)],⟨7,35,268,25,84,224,208,394,298⟩,⟨7,35,268,25,84,224,208,384,288⟩,[⟨4,1247997180424901362758685,⟨135,35,399,431,231,226,227,384,288⟩⟩,⟨8,1181747921033062556689,⟨7,35,12,27,127,234,251,128,32⟩⟩,⟨3,1210107567535650426102801,⟨7,35,260,19,119,226,243,384,288⟩⟩]⟩
theorem node596 : UpperPrefix a [2,5,8,0,6,7,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,6,7,4] 30 cert596 (by decide +kernel)

theorem node597 : UpperPrefix a [2,5,8,0,6,7] 30 :=
  branch_upper a [2,5,8,0,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,6,7,0] 30 (by decide +kernel))
  node592
  (invalid_upper a [2,5,8,0,6,7,2] 30 (by decide +kernel))
  node595
  node596
  (invalid_upper a [2,5,8,0,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,7,8] 30 (by decide +kernel)))

theorem node598 : UpperPrefix a [2,5,8,0,6] 30 :=
  branch_upper a [2,5,8,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,6,0] 30 (by decide +kernel))
  node585
  (invalid_upper a [2,5,8,0,6,2] 30 (by decide +kernel))
  node588
  node591
  (invalid_upper a [2,5,8,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,6,6] 30 (by decide +kernel))
  node597
  (invalid_upper a [2,5,8,0,6,8] 30 (by decide +kernel)))

def cert599 : Leaf := ⟨⟨248,216,240,196,328,152,16,88,216⟩,[],[(2,0,3),(8,2,4),(1,5,1)],⟨7,35,268,25,148,98,200,464,368⟩,⟨7,35,268,25,148,98,200,384,288⟩,[⟨0,1404730154848981238154240,⟨502,434,476,508,212,502,476,384,432⟩⟩,⟨5,1210144547718435745825793,⟨223,91,476,89,212,74,200,384,256⟩⟩]⟩
theorem node599 : UpperPrefix a [2,5,8,0,7,1,3] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,1,3] 30 cert599 (by decide +kernel)

def cert600 : Leaf := ⟨⟨120,88,112,100,360,24,0,120,88⟩,[(6,4)],[(2,0,3),(8,2,4),(7,4,6),(1,5,1)],⟨7,35,268,25,148,98,208,456,360⟩,⟨7,35,268,25,148,98,208,384,288⟩,[⟨0,1247997700135254351676416,⟨246,114,476,508,212,98,208,384,288⟩⟩]⟩
theorem node600 : UpperPrefix a [2,5,8,0,7,1,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,1,4] 30 cert600 (by decide +kernel)

theorem node601 : UpperPrefix a [2,5,8,0,7,1] 30 :=
  branch_upper a [2,5,8,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,1,2] 30 (by decide +kernel))
  node599
  node600
  (invalid_upper a [2,5,8,0,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,1,8] 30 (by decide +kernel)))

def cert602 : Leaf := ⟨⟨184,152,176,164,296,144,56,120,216⟩,[],[(2,0,3),(8,2,4)],⟨7,35,268,25,148,104,194,464,368⟩,⟨7,35,268,25,148,104,194,384,288⟩,[⟨0,1409433912717812763198464,⟨470,502,444,508,148,508,466,400,436⟩⟩,⟨1,1664340193631002621902849,⟨29,445,284,25,148,508,508,400,436⟩⟩,⟨6,1210106412375573531870661,⟨7,43,271,25,157,59,159,415,303⟩⟩]⟩
theorem node602 : UpperPrefix a [2,5,8,0,7,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,3,1] 30 cert602 (by decide +kernel)

def cert603 : Leaf := ⟨⟨104,72,98,102,362,18,0,106,74⟩,[(6,4)],[(2,0,3),(8,2,4),(7,4,6),(4,6,5)],⟨7,35,268,25,148,104,208,450,354⟩,⟨7,35,268,25,148,104,208,384,288⟩,[⟨0,1224302821660161884554240,⟨502,498,380,508,244,124,208,384,288⟩⟩]⟩
theorem node603 : UpperPrefix a [2,5,8,0,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,3,4] 30 cert603 (by decide +kernel)

theorem node604 : UpperPrefix a [2,5,8,0,7,3] 30 :=
  branch_upper a [2,5,8,0,7,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,3,0] 30 (by decide +kernel))
  node602
  (invalid_upper a [2,5,8,0,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,3] 30 (by decide +kernel))
  node603
  (invalid_upper a [2,5,8,0,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,3,8] 30 (by decide +kernel)))

def cert605 : Leaf := ⟨⟨56,24,49,36,297,137,57,121,89⟩,[],[(2,0,3),(8,2,4),(7,4,5)],⟨7,35,268,25,148,112,194,456,360⟩,⟨7,35,268,25,148,112,194,384,288⟩,[⟨1,1512929318256264854110209,⟨13,57,268,25,148,500,508,384,304⟩⟩,⟨6,1210106412375573531870661,⟨7,43,271,25,157,59,159,415,303⟩⟩]⟩
theorem node605 : UpperPrefix a [2,5,8,0,7,4,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,4,1] 30 cert605 (by decide +kernel)

def cert606 : Leaf := ⟨⟨88,88,82,70,330,138,18,120,90⟩,[],[(2,0,3),(5,1,7),(8,2,4),(7,4,5)],⟨7,35,268,25,148,112,200,386,352⟩,⟨7,35,268,25,148,112,200,386,288⟩,[⟨0,1720150962344100828808192,⟨438,434,380,508,436,372,508,386,288⟩⟩]⟩
theorem node606 : UpperPrefix a [2,5,8,0,7,4,3,1] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,4,3,1] 30 cert606 (by decide +kernel)

def cert607 : Leaf := ⟨⟨56,24,50,38,298,138,50,58,26⟩,[],[(2,0,3),(8,2,4),(7,4,5)],⟨7,35,268,25,148,112,200,448,290⟩,⟨7,35,268,25,148,112,200,448,288⟩,[⟨0,1224394792522759481066496,⟨502,434,508,508,244,112,252,496,288⟩⟩,⟨6,1370666872793141478049191,⟨263,303,271,25,157,319,157,415,303⟩⟩]⟩
theorem node607 : UpperPrefix a [2,5,8,0,7,4,3,6] 30 :=
  Boolean.leaf_sound a [2,5,8,0,7,4,3,6] 30 cert607 (by decide +kernel)

theorem node608 : UpperPrefix a [2,5,8,0,7,4,3] 30 :=
  branch_upper a [2,5,8,0,7,4,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,4,3,0] 30 (by decide +kernel))
  node606
  (invalid_upper a [2,5,8,0,7,4,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,3,5] 30 (by decide +kernel))
  node607
  (invalid_upper a [2,5,8,0,7,4,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,3,8] 30 (by decide +kernel)))

theorem node609 : UpperPrefix a [2,5,8,0,7,4] 30 :=
  branch_upper a [2,5,8,0,7,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,4,0] 30 (by decide +kernel))
  node605
  (invalid_upper a [2,5,8,0,7,4,2] 30 (by decide +kernel))
  node608
  (invalid_upper a [2,5,8,0,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,4,8] 30 (by decide +kernel)))

theorem node610 : UpperPrefix a [2,5,8,0,7] 30 :=
  branch_upper a [2,5,8,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,7,0] 30 (by decide +kernel))
  node601
  (invalid_upper a [2,5,8,0,7,2] 30 (by decide +kernel))
  node604
  node609
  (invalid_upper a [2,5,8,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,7,8] 30 (by decide +kernel)))

theorem node611 : UpperPrefix a [2,5,8,0] 30 :=
  branch_upper a [2,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,0,0] 30 (by decide +kernel))
  node583
  (invalid_upper a [2,5,8,0,2] 30 (by decide +kernel))
  node584
  (invalid_upper a [2,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,0,5] 30 (by decide +kernel))
  node598
  node610
  (invalid_upper a [2,5,8,0,8] 30 (by decide +kernel)))

def cert612 : Leaf := ⟨⟨312,280,48,289,0,408,312,120,216⟩,[(4,0)],[(2,0,4),(0,4,3)],⟨7,35,268,26,21,248,216,472,504⟩,⟨7,35,268,26,21,96,192,384,288⟩,[⟨1,1247960428519835460173825,⟨21,49,492,508,21,96,192,384,288⟩⟩,⟨6,1210106412393529582159237,⟨31,59,287,26,29,48,157,415,319⟩⟩,⟨7,1208926973694316777702789,⟨31,59,287,26,29,112,93,287,319⟩⟩]⟩
theorem node612 : UpperPrefix a [2,5,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,0] 30 cert612 (by decide +kernel)

def cert613 : Leaf := ⟨⟨496,0,240,484,0,404,308,116,212⟩,[(1,5),(4,2)],[(3,4,4),(0,5,1)],⟨7,35,268,26,28,97,208,464,496⟩,⟨7,35,268,26,28,97,192,384,288⟩,[⟨1,1252876863942681812795393,⟨501,481,476,508,476,481,192,384,288⟩⟩]⟩
theorem node613 : UpperPrefix a [2,5,8,1,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,3,0] 30 cert613 (by decide +kernel)

def cert614 : Leaf := ⟨⟨352,340,97,357,0,261,293,101,197⟩,[(4,2)],[(3,4,4)],⟨7,35,268,26,28,112,193,449,481⟩,⟨7,35,268,26,28,112,192,384,288⟩,[⟨1,1224302389209250699149313,⟨501,481,316,508,60,112,192,384,288⟩⟩,⟨4,1219691207275398082593801,⟨455,483,461,463,205,96,192,384,288⟩⟩,⟨7,1208926975946129476339141,⟨31,59,287,26,29,123,127,287,319⟩⟩]⟩
theorem node614 : UpperPrefix a [2,5,8,1,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,3,4] 30 cert614 (by decide +kernel)

def cert615 : Leaf := ⟨⟨304,276,51,293,0,0,309,117,85⟩,[(4,2),(5,6)],[(3,4,4),(7,5,5)],⟨7,35,268,26,28,224,209,465,369⟩,⟨7,35,268,26,28,224,192,384,288⟩,[⟨6,1210106412395732900398501,⟨31,59,287,26,29,191,157,415,319⟩⟩,⟨1,1214839175510784503447553,⟨501,481,284,56,28,224,224,384,288⟩⟩]⟩
theorem node615 : UpperPrefix a [2,5,8,1,3,7] 30 :=
  Boolean.leaf_sound a [2,5,8,1,3,7] 30 cert615 (by decide +kernel)

theorem node616 : UpperPrefix a [2,5,8,1,3] 30 :=
  branch_upper a [2,5,8,1,3] 30 (by decide) (fin9_cases _
  node613
  (invalid_upper a [2,5,8,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,3] 30 (by decide +kernel))
  node614
  (invalid_upper a [2,5,8,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,3,6] 30 (by decide +kernel))
  node615
  (invalid_upper a [2,5,8,1,3,8] 30 (by decide +kernel)))

def cert617 : Leaf := ⟨⟨112,0,242,68,392,20,284,92,222⟩,[(1,5)],[(0,5,1)],⟨7,35,268,26,84,97,216,408,440⟩,⟨7,35,268,26,84,97,192,384,288⟩,[⟨1,1210144530865121112621057,⟨245,49,476,24,212,113,192,384,288⟩⟩,⟨5,1210144547718435745825793,⟨223,91,476,26,212,89,192,384,256⟩⟩,⟨7,1208926974226086375748629,⟨7,35,271,59,127,99,64,256,290⟩⟩,⟨8,1181746232174612345877,⟨7,35,15,59,127,99,192,128,34⟩⟩,⟨3,1210107565846800565826581,⟨7,35,263,51,119,99,192,384,290⟩⟩]⟩
theorem node617 : UpperPrefix a [2,5,8,1,6,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,0] 30 cert617 (by decide +kernel)

def cert618 : Leaf := ⟨⟨120,92,112,100,288,21,52,100,212⟩,[],[],⟨7,35,268,26,84,104,193,400,416⟩,⟨7,35,268,26,84,104,193,400,288⟩,[⟨1,1430278733503237492572161,⟨469,501,444,508,468,508,209,400,436⟩⟩,⟨7,1208926976482314401609173,⟨7,43,271,59,127,123,127,319,303⟩⟩,⟨0,1373416590574999696049152,⟨398,446,396,414,84,508,212,400,436⟩⟩,⟨8,1184058830600447046677,⟨7,35,15,59,127,106,235,251,32⟩⟩,⟨3,1370769536837088200098817,⟨471,499,388,466,84,480,209,400,288⟩⟩]⟩
theorem node618 : UpperPrefix a [2,5,8,1,6,3,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,3,0,4] 30 cert618 (by decide +kernel)

theorem node619 : UpperPrefix a [2,5,8,1,6,3,0] 30 :=
  branch_upper a [2,5,8,1,6,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,1,6,3,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,0,3] 30 (by decide +kernel))
  node618
  (invalid_upper a [2,5,8,1,6,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,0,8] 30 (by decide +kernel)))

def cert620 : Leaf := ⟨⟨296,264,161,357,417,273,289,33,129⟩,[],[(4,6,5)],⟨7,35,268,26,84,104,208,385,417⟩,⟨7,35,268,26,84,104,208,384,288⟩,[⟨1,1224302533432259634003969,⟨501,497,380,508,116,124,208,384,304⟩⟩,⟨2,1224302479385971725960705,⟨419,419,360,506,112,104,208,384,288⟩⟩,⟨6,1373461554507082024240431,⟨391,423,399,415,149,431,144,387,423⟩⟩,⟨3,1219580166524427668816897,⟨471,499,340,466,84,96,208,384,288⟩⟩,⟨7,1208926976477894779384853,⟨7,35,271,59,127,106,123,256,288⟩⟩]⟩
theorem node620 : UpperPrefix a [2,5,8,1,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,3,4] 30 cert620 (by decide +kernel)

theorem node621 : UpperPrefix a [2,5,8,1,6,3] 30 :=
  branch_upper a [2,5,8,1,6,3] 30 (by decide) (fin9_cases _
  node619
  (invalid_upper a [2,5,8,1,6,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,3] 30 (by decide +kernel))
  node620
  (invalid_upper a [2,5,8,1,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,3,8] 30 (by decide +kernel)))

def cert622 : Leaf := ⟨⟨312,284,48,261,393,0,284,28,156⟩,[(5,4)],[(6,4,5)],⟨7,35,268,26,84,112,193,392,424⟩,⟨7,35,268,26,84,112,193,384,288⟩,[⟨1,1247997198546021219565569,⟨245,113,396,444,244,112,241,384,288⟩⟩,⟨5,1210144475660566829990913,⟨223,91,396,26,212,80,217,384,256⟩⟩,⟨7,1208926974226090737956245,⟨7,43,271,59,127,123,65,263,303⟩⟩,⟨0,1247997178174201060656128,⟨134,34,396,446,244,112,192,384,288⟩⟩]⟩
theorem node622 : UpperPrefix a [2,5,8,1,6,4,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,4,0] 30 cert622 (by decide +kernel)

def cert623 : Leaf := ⟨⟨416,404,161,421,425,0,293,37,133⟩,[(5,4)],[(6,4,5),(3,6,4)],⟨7,35,268,26,84,112,200,385,417⟩,⟨7,35,268,26,84,112,200,384,288⟩,[⟨1,1224302482205944176443393,⟨437,417,380,508,116,112,252,384,288⟩⟩,⟨4,1219690865001826402436105,⟨455,419,461,463,196,96,205,384,288⟩⟩]⟩
theorem node623 : UpperPrefix a [2,5,8,1,6,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,4,3] 30 cert623 (by decide +kernel)

theorem node624 : UpperPrefix a [2,5,8,1,6,4] 30 :=
  branch_upper a [2,5,8,1,6,4] 30 (by decide) (fin9_cases _
  node622
  (invalid_upper a [2,5,8,1,6,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,4,2] 30 (by decide +kernel))
  node623
  (invalid_upper a [2,5,8,1,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,4,8] 30 (by decide +kernel)))

def cert625 : Leaf := ⟨⟨376,344,0,353,299,0,314,0,91⟩,[(2,7),(5,6),(7,2)],[(7,5,5)],⟨7,35,268,26,84,224,193,392,304⟩,⟨7,35,268,26,84,224,193,392,288⟩,[⟨2,1323702636154089900115457,⟨227,99,392,442,506,226,227,392,288⟩⟩]⟩
theorem node625 : UpperPrefix a [2,5,8,1,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,7,0,3] 30 cert625 (by decide +kernel)

def cert626 : Leaf := ⟨⟨304,276,49,293,289,0,308,101,29⟩,[(5,6)],[(7,5,5)],⟨7,35,268,26,84,224,193,400,296⟩,⟨7,35,268,26,84,224,193,400,288⟩,[⟨1,1267043498112948083097601,⟨501,241,444,508,500,224,241,432,288⟩⟩,⟨3,1210147150411990796713493,⟨247,115,503,115,247,226,243,499,288⟩⟩,⟨6,1361222139814192948069799,⟨7,295,271,27,21,431,141,415,295⟩⟩]⟩
theorem node626 : UpperPrefix a [2,5,8,1,6,7,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,7,0,4] 30 cert626 (by decide +kernel)

theorem node627 : UpperPrefix a [2,5,8,1,6,7,0] 30 :=
  branch_upper a [2,5,8,1,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,1,6,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,0,2] 30 (by decide +kernel))
  node625
  node626
  (invalid_upper a [2,5,8,1,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,0,8] 30 (by decide +kernel)))

def cert628 : Leaf := ⟨⟨368,340,112,356,296,0,309,116,84⟩,[(5,6)],[(7,5,5),(3,6,4)],⟨7,35,268,26,84,224,200,385,304⟩,⟨7,35,268,26,84,224,200,385,288⟩,[⟨1,1805153558897422135984129,⟨405,433,380,508,372,500,508,385,304⟩⟩,⟨0,1748457346589388412027904,⟨270,318,268,286,372,500,508,388,304⟩⟩]⟩
theorem node628 : UpperPrefix a [2,5,8,1,6,7,3,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,7,3,0] 30 cert628 (by decide +kernel)

def cert629 : Leaf := ⟨⟨288,260,35,293,299,0,311,39,7⟩,[(5,6)],[(7,5,5),(3,6,4),(4,7,6)],⟨7,35,268,26,84,224,200,400,289⟩,⟨7,35,268,26,84,224,200,400,288⟩,[⟨6,1370740659756227078800815,⟨263,295,399,415,21,431,141,415,295⟩⟩]⟩
theorem node629 : UpperPrefix a [2,5,8,1,6,7,3,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,7,3,4] 30 cert629 (by decide +kernel)

theorem node630 : UpperPrefix a [2,5,8,1,6,7,3] 30 :=
  branch_upper a [2,5,8,1,6,7,3] 30 (by decide) (fin9_cases _
  node628
  (invalid_upper a [2,5,8,1,6,7,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,3,3] 30 (by decide +kernel))
  node629
  (invalid_upper a [2,5,8,1,6,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,3,8] 30 (by decide +kernel)))

def cert631 : Leaf := ⟨⟨352,324,98,356,290,0,294,102,78⟩,[(5,6)],[(7,5,5)],⟨7,35,268,26,84,224,208,385,296⟩,⟨7,35,268,26,84,224,208,385,288⟩,[⟨0,1824018097131597562905600,⟨286,382,268,286,116,500,500,508,368⟩⟩,⟨3,1210147150411990796713493,⟨247,115,503,115,247,226,243,499,288⟩⟩,⟨4,1247997180424901362758685,⟨135,35,399,431,231,226,227,385,288⟩⟩]⟩
theorem node631 : UpperPrefix a [2,5,8,1,6,7,4,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,7,4,0] 30 cert631 (by decide +kernel)

def cert632 : Leaf := ⟨⟨376,348,0,356,298,0,302,0,95⟩,[(2,7),(5,6),(7,2)],[(7,5,5)],⟨7,35,268,26,84,224,208,392,289⟩,⟨7,35,268,26,84,224,208,392,288⟩,[⟨0,1210147726888137772762112,⟨254,122,508,122,244,244,244,508,368⟩⟩]⟩
theorem node632 : UpperPrefix a [2,5,8,1,6,7,4,3] 30 :=
  Boolean.leaf_sound a [2,5,8,1,6,7,4,3] 30 cert632 (by decide +kernel)

theorem node633 : UpperPrefix a [2,5,8,1,6,7,4] 30 :=
  branch_upper a [2,5,8,1,6,7,4] 30 (by decide) (fin9_cases _
  node631
  (invalid_upper a [2,5,8,1,6,7,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,4,2] 30 (by decide +kernel))
  node632
  (invalid_upper a [2,5,8,1,6,7,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,4,8] 30 (by decide +kernel)))

theorem node634 : UpperPrefix a [2,5,8,1,6,7] 30 :=
  branch_upper a [2,5,8,1,6,7] 30 (by decide) (fin9_cases _
  node627
  (invalid_upper a [2,5,8,1,6,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,2] 30 (by decide +kernel))
  node630
  node633
  (invalid_upper a [2,5,8,1,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,7,8] 30 (by decide +kernel)))

theorem node635 : UpperPrefix a [2,5,8,1,6] 30 :=
  branch_upper a [2,5,8,1,6] 30 (by decide) (fin9_cases _
  node617
  (invalid_upper a [2,5,8,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,2] 30 (by decide +kernel))
  node621
  node624
  (invalid_upper a [2,5,8,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,6,6] 30 (by decide +kernel))
  node634
  (invalid_upper a [2,5,8,1,6,8] 30 (by decide +kernel)))

def cert636 : Leaf := ⟨⟨184,0,178,132,264,156,28,92,222⟩,[(1,5)],[(8,2,4),(0,5,1)],⟨7,35,268,26,148,97,216,472,376⟩,⟨7,35,268,26,148,97,192,384,288⟩,[⟨1,1210144530865121112621057,⟨245,49,476,24,212,113,192,384,288⟩⟩,⟨5,1210144547718435745825793,⟨223,91,476,26,212,89,192,384,256⟩⟩,⟨6,1210106412375562794452357,⟨7,43,271,26,157,59,157,415,303⟩⟩]⟩
theorem node636 : UpperPrefix a [2,5,8,1,7,0] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,0] 30 cert636 (by decide +kernel)

def cert637 : Leaf := ⟨⟨168,140,160,164,296,132,44,44,204⟩,[],[(8,2,4)],⟨7,35,268,26,148,104,193,400,352⟩,⟨7,35,268,26,148,104,193,400,288⟩,[⟨0,1666756717105551926363136,⟨158,446,412,158,148,508,508,400,436⟩⟩,⟨1,1411241693637036299255809,⟨469,501,444,508,148,508,209,400,436⟩⟩,⟨4,1399004818952398335794495,⟨7,295,303,367,199,367,193,451,295⟩⟩,⟨6,1212504489123111823869317,⟨159,59,415,26,157,56,157,415,447⟩⟩]⟩
theorem node637 : UpperPrefix a [2,5,8,1,7,3,0,4] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,3,0,4] 30 cert637 (by decide +kernel)

def cert638 : Leaf := ⟨⟨168,140,176,164,296,132,44,44,156⟩,[],[(8,2,4)],⟨7,35,268,26,148,104,193,448,304⟩,⟨7,35,268,26,148,104,193,448,288⟩,[⟨0,2278247836412852595065856,⟨286,446,284,286,404,508,508,500,436⟩⟩,⟨1,1427733082838932638400513,⟨469,501,444,508,404,508,209,464,436⟩⟩,⟨6,1361222139827391450203567,⟨7,303,271,31,157,319,157,415,303⟩⟩,⟨4,1210144837495480757796373,⟨231,99,495,107,231,106,195,448,288⟩⟩]⟩
theorem node638 : UpperPrefix a [2,5,8,1,7,3,0,6] 30 :=
  Boolean.leaf_sound a [2,5,8,1,7,3,0,6] 30 cert638 (by decide +kernel)

theorem node639 : UpperPrefix a [2,5,8,1,7,3,0] 30 :=
  branch_upper a [2,5,8,1,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,8,1,7,3,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,0,3] 30 (by decide +kernel))
  node637
  (invalid_upper a [2,5,8,1,7,3,0,5] 30 (by decide +kernel))
  node638
  (invalid_upper a [2,5,8,1,7,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,8,1,7,3,0,8] 30 (by decide +kernel)))

#print axioms node639
end Delivery.FiniteExclusion.Sharp2x3x4
