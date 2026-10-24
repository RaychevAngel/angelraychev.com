import RegularNineSharp2x2x5Base
import RegularNineSharp2x2x5C002
import RegularNineSharp2x2x5C003
import RegularNineSharp2x2x5C004
import RegularNineSharp2x2x5C005
import RegularNineSharp2x2x5C006
import RegularNineSharp2x2x5C007
import RegularNineSharp2x2x5C008
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Bounds BoundTreeRows Extremal
def cert576 : Leaf := ⟨⟨492,0,0,370,0,0,318,126,238⟩,[(1,5),(2,4),(4,2),(5,1)],[],⟨19,67,44,140,56,97,454,390,278⟩,⟨19,67,44,140,56,97,192,384,272⟩,[⟨0,1214839173155635038520320,⟨478,458,60,156,60,508,192,384,276⟩⟩]⟩
theorem node576 : UpperPrefix a [4,6,5,7,3,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,0] 30 cert576 (by decide +kernel)

def cert577 : Leaf := ⟨⟨172,188,0,49,0,0,317,61,173⟩,[(2,4),(4,2),(5,1)],[(6,1,5)],⟨19,67,44,140,56,98,453,389,277⟩,⟨19,67,44,140,56,98,192,384,272⟩,[⟨1,1214839173153431711907841,⟨477,457,60,156,60,96,192,384,276⟩⟩,⟨8,1181747998409075770487,⟨55,127,63,157,63,127,255,128,21⟩⟩]⟩
theorem node577 : UpperPrefix a [4,6,5,7,3,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,1] 30 cert577 (by decide +kernel)

def cert578 : Leaf := ⟨⟨448,400,0,371,0,403,275,83,195⟩,[(2,4),(4,2)],[(2,5,2),(2,5,4)],⟨19,67,44,140,56,100,451,387,275⟩,⟨19,67,44,140,56,100,192,384,272⟩,[⟨3,1292931482886843942512401,⟨467,451,36,230,499,100,194,451,467⟩⟩,⟨5,1292931481479470132700945,⟨467,451,12,206,475,68,194,451,467⟩⟩]⟩
theorem node578 : UpperPrefix a [4,6,5,7,3,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,2] 30 cert578 (by decide +kernel)

def cert579 : Leaf := ⟨⟨488,0,0,306,0,154,314,62,174⟩,[(1,6),(2,4),(4,2)],[(0,6,1)],⟨19,67,44,140,56,352,193,390,278⟩,⟨19,67,44,140,56,352,193,384,272⟩,[⟨2,1210110019746473235840285,⟨19,67,123,251,123,355,227,483,275⟩⟩,⟨6,1214838002217528595579905,⟨415,395,60,156,60,288,393,384,276⟩⟩]⟩
theorem node579 : UpperPrefix a [4,6,5,7,3,8,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,8,0] 30 cert579 (by decide +kernel)

def cert580 : Leaf := ⟨⟨448,400,0,369,0,145,273,125,237⟩,[(2,4),(4,2)],[(1,6,1)],⟨19,67,44,140,56,352,194,389,277⟩,⟨19,67,44,140,56,352,194,384,272⟩,[⟨2,1210110019746473235807517,⟨19,67,123,251,123,355,226,483,275⟩⟩,⟨3,1210110019745647529387281,⟨19,67,102,230,115,355,226,483,275⟩⟩,⟨5,1210110014116149068915985,⟨19,67,78,206,91,323,194,451,275⟩⟩]⟩
theorem node580 : UpperPrefix a [4,6,5,7,3,8,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,8,1] 30 cert580 (by decide +kernel)

def cert581 : Leaf := ⟨⟨488,440,0,0,0,155,0,123,235⟩,[(2,4),(3,6),(4,2),(6,3)],[],⟨19,67,44,140,56,352,196,387,275⟩,⟨19,67,44,140,56,352,196,384,272⟩,[⟨2,1612606299922600682374229,⟨435,483,443,409,443,483,499,384,401⟩⟩]⟩
theorem node581 : UpperPrefix a [4,6,5,7,3,8,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,3,8,2] 30 cert581 (by decide +kernel)

theorem node582 : UpperPrefix a [4,6,5,7,3,8] 30 :=
  branch_upper a [4,6,5,7,3,8] 30 (by decide) (fin9_cases _
  node579
  node580
  node581
  (invalid_upper a [4,6,5,7,3,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,8,8] 30 (by decide +kernel)))

theorem node583 : UpperPrefix a [4,6,5,7,3] 30 :=
  branch_upper a [4,6,5,7,3] 30 (by decide) (fin9_cases _
  node576
  node577
  node578
  (invalid_upper a [4,6,5,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,3,7] 30 (by decide +kernel))
  node582)

def cert584 : Leaf := ⟨⟨492,0,386,290,142,0,302,46,174⟩,[(1,5),(5,1)],[],⟨19,67,44,140,304,97,206,398,286⟩,⟨19,67,44,140,304,97,192,384,272⟩,[⟨0,1214839173155360160613376,⟨478,458,60,140,316,508,192,384,276⟩⟩,⟨6,1214838002219457044284417,⟨415,395,60,140,316,445,128,384,276⟩⟩,⟨4,1210255445585706283189761,⟨239,111,46,140,494,111,192,392,460⟩⟩]⟩
theorem node584 : UpperPrefix a [4,6,5,7,8,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,0] 30 cert584 (by decide +kernel)

def cert585 : Leaf := ⟨⟨428,0,400,304,140,0,316,60,172⟩,[(1,6),(5,1)],[(6,1,5),(0,6,1),(0,6,5)],⟨19,67,44,140,304,98,193,396,284⟩,⟨19,67,44,140,304,98,193,384,272⟩,[⟨1,1501095783720293923553281,⟨477,457,444,412,444,508,457,392,412⟩⟩]⟩
theorem node585 : UpperPrefix a [4,6,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,1,0] 30 cert585 (by decide +kernel)

def cert586 : Leaf := ⟨⟨424,440,403,0,139,0,0,59,171⟩,[(3,6),(5,1),(6,3)],[(6,1,5)],⟨19,67,44,140,304,98,196,393,281⟩,⟨19,67,44,140,304,98,196,384,272⟩,[⟨2,1266886645869571167274103,⟨51,115,443,409,307,115,499,384,273⟩⟩]⟩
theorem node586 : UpperPrefix a [4,6,5,7,8,1,2] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,1,2] 30 cert586 (by decide +kernel)

def cert587 : Leaf := ⟨⟨292,308,275,307,7,0,0,55,39⟩,[(5,1),(6,3)],[(6,1,5),(7,3,6)],⟨19,67,44,140,304,98,200,389,277⟩,⟨19,67,44,140,304,98,200,384,272⟩,[⟨3,1266886645869570094580855,⟨51,115,439,405,307,115,499,384,273⟩⟩]⟩
theorem node587 : UpperPrefix a [4,6,5,7,8,1,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,1,3] 30 cert587 (by decide +kernel)

theorem node588 : UpperPrefix a [4,6,5,7,8,1] 30 :=
  branch_upper a [4,6,5,7,8,1] 30 (by decide) (fin9_cases _
  node585
  (invalid_upper a [4,6,5,7,8,1,1] 30 (by decide +kernel))
  node586
  node587
  (invalid_upper a [4,6,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,1,8] 30 (by decide +kernel)))

def cert589 : Leaf := ⟨⟨360,0,448,352,74,392,314,122,106⟩,[(1,6)],[(2,5,2),(0,6,1)],⟨19,67,44,140,304,100,193,394,282⟩,⟨19,67,44,140,304,100,193,384,272⟩,[⟨1,1210107567606028859604993,⟨53,109,44,140,308,108,237,384,272⟩⟩,⟨4,1210107567604929348011009,⟨39,111,44,140,292,110,239,384,256⟩⟩,⟨7,1227816439597086756881461,⟨19,67,319,285,307,375,67,256,273⟩⟩]⟩
theorem node589 : UpperPrefix a [4,6,5,7,8,2,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,2,0] 30 cert589 (by decide +kernel)

def cert590 : Leaf := ⟨⟨480,416,448,352,200,384,289,112,232⟩,[],[(4,0,7),(2,5,2),(1,6,1),(0,7,6)],⟨19,67,44,140,304,100,194,385,280⟩,⟨19,67,44,140,304,100,194,385,272⟩,[⟨3,1212623690789077954799377,⟨211,67,100,230,499,100,194,451,467⟩⟩]⟩
theorem node590 : UpperPrefix a [4,6,5,7,8,2,1,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,2,1,0] 30 cert590 (by decide +kernel)

def cert591 : Leaf := ⟨⟨480,416,448,352,193,384,288,96,225⟩,[],[(2,5,2),(1,6,1),(3,7,3)],⟨19,67,44,140,304,100,194,392,273⟩,⟨19,67,44,140,304,100,194,392,272⟩,[⟨4,1212616342848573374465537,⟨239,111,44,140,428,108,238,392,396⟩⟩,⟨0,1212616342849672886092800,⟨254,110,44,140,444,108,238,392,412⟩⟩]⟩
theorem node591 : UpperPrefix a [4,6,5,7,8,2,1,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,2,1,3] 30 cert591 (by decide +kernel)

theorem node592 : UpperPrefix a [4,6,5,7,8,2,1] 30 :=
  branch_upper a [4,6,5,7,8,2,1] 30 (by decide) (fin9_cases _
  node590
  (invalid_upper a [4,6,5,7,8,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,1,2] 30 (by decide +kernel))
  node591
  (invalid_upper a [4,6,5,7,8,2,1,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,1,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,1,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,1,8] 30 (by decide +kernel)))

def cert593 : Leaf := ⟨⟨352,304,338,370,66,282,0,115,99⟩,[(6,3)],[(7,3,6),(2,5,2),(3,6,5)],⟨19,67,44,140,304,100,200,387,275⟩,⟨19,67,44,140,304,100,200,384,272⟩,[⟨0,1210110022498851550135296,⟨54,110,108,252,308,108,252,508,272⟩⟩]⟩
theorem node593 : UpperPrefix a [4,6,5,7,8,2,3] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,2,3] 30 cert593 (by decide +kernel)

theorem node594 : UpperPrefix a [4,6,5,7,8,2] 30 :=
  branch_upper a [4,6,5,7,8,2] 30 (by decide) (fin9_cases _
  node589
  node592
  (invalid_upper a [4,6,5,7,8,2,2] 30 (by decide +kernel))
  node593
  (invalid_upper a [4,6,5,7,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,2,8] 30 (by decide +kernel)))

def cert595 : Leaf := ⟨⟨356,0,0,368,70,404,310,118,102⟩,[(1,6),(2,5)],[(7,3,5),(3,5,2),(0,6,1)],⟨19,67,44,140,304,104,193,390,278⟩,⟨19,67,44,140,304,104,193,384,272⟩,[⟨1,1210107567606028859604993,⟨53,109,44,140,308,108,237,384,272⟩⟩]⟩
theorem node595 : UpperPrefix a [4,6,5,7,8,3,0] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,3,0] 30 cert595 (by decide +kernel)

def cert596 : Leaf := ⟨⟨356,308,0,96,69,132,309,117,101⟩,[(2,5)],[(7,3,5),(3,5,2),(1,6,1)],⟨19,67,44,140,304,104,194,389,277⟩,⟨19,67,44,140,304,104,194,384,272⟩,[⟨0,1210107567606028859606016,⟨54,110,44,140,308,108,238,384,272⟩⟩,⟨4,1210107567604929347978241,⟨39,111,44,140,292,108,238,384,256⟩⟩,⟨8,1181747991399684899841,⟨55,111,44,140,52,108,238,128,16⟩⟩]⟩
theorem node596 : UpperPrefix a [4,6,5,7,8,3,1] 30 :=
  Boolean.leaf_sound a [4,6,5,7,8,3,1] 30 cert596 (by decide +kernel)

def cert597 : Local := ⟨⟨352,304,0,0,67,407,0,115,99⟩,[(2,5),(3,6),(6,3)],[(7,3,5),(3,5,2),(2,6,5)]⟩
theorem node597 : UpperPrefix a [4,6,5,7,8,3,2] 30 :=
  local_sound a [4,6,5,7,8,3,2] 30 cert597 (by decide +kernel)

theorem node598 : UpperPrefix a [4,6,5,7,8,3] 30 :=
  branch_upper a [4,6,5,7,8,3] 30 (by decide) (fin9_cases _
  node595
  node596
  node597
  (invalid_upper a [4,6,5,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,3,8] 30 (by decide +kernel)))

theorem node599 : UpperPrefix a [4,6,5,7,8] 30 :=
  branch_upper a [4,6,5,7,8] 30 (by decide) (fin9_cases _
  node584
  node588
  node594
  node598
  (invalid_upper a [4,6,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,8,8] 30 (by decide +kernel)))

theorem node600 : UpperPrefix a [4,6,5,7] 30 :=
  branch_upper a [4,6,5,7] 30 (by decide) (fin9_cases _
  node557
  node565
  node575
  node583
  (invalid_upper a [4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,7,7] 30 (by decide +kernel))
  node599)

theorem node601 : UpperPrefix a [4,6,5] 30 :=
  branch_upper a [4,6,5] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut29 [4,6,5,0] [2,4,8,5] 30 (by decide +kernel) node446)
  (PrefixConjugacy.upper aut39 [4,6,5,1] [2,4,5,8] 30 (by decide +kernel) node214)
  (invalid_upper a [4,6,5,2] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [4,6,5,6] 30 (by decide +kernel))
  node600
  (PrefixConjugacy.upper aut26 [4,6,5,8] [4,6,5,7] 30 (by decide +kernel) node600))

theorem node602 : UpperPrefix a [4,6,7] 30 :=
  branch_upper a [4,6,7] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut27 [4,6,7,0] [2,4,6,8] 30 (by decide +kernel) node309)
  (PrefixConjugacy.upper aut37 [4,6,7,1] [2,4,8,6] 30 (by decide +kernel) node490)
  (invalid_upper a [4,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [4,6,7,5] [4,6,5,7] 30 (by decide +kernel) node600)
  (invalid_upper a [4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [4,6,7,7] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut22 [4,6,7,8] [4,5,6,8] 30 (by decide +kernel) node543))

theorem node603 : UpperPrefix a [4,6,8] 30 :=
  branch_upper a [4,6,8] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut26 [4,6,8,0] [2,4,5,7] 30 (by decide +kernel) node185)
  (PrefixConjugacy.upper aut36 [4,6,8,1] [2,4,7,5] 30 (by decide +kernel) node352)
  (invalid_upper a [4,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,8,4] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut21 [4,6,8,5] [4,6,5,7] 30 (by decide +kernel) node600)
  (invalid_upper a [4,6,8,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut27 [4,6,8,7] [4,5,6,8] 30 (by decide +kernel) node543)
  (invalid_upper a [4,6,8,8] 30 (by decide +kernel)))

theorem node604 : UpperPrefix a [4,6] 30 :=
  branch_upper a [4,6] 30 (by decide) (fin9_cases _
  node548
  node549
  (invalid_upper a [4,6,2] 30 (by decide +kernel))
  (invalid_upper a [4,6,3] 30 (by decide +kernel))
  (invalid_upper a [4,6,4] 30 (by decide +kernel))
  node601
  (invalid_upper a [4,6,6] 30 (by decide +kernel))
  node602
  node603)

theorem node605 : UpperPrefix a [4] 30 :=
  branch_upper a [4] 30 (by decide) (fin9_cases _
  (invalid_upper a [4,0] 30 (by decide +kernel))
  (invalid_upper a [4,1] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [4,2] [2,4] 30 (by decide +kernel) node513)
  (PrefixConjugacy.upper aut15 [4,3] [2,4] 30 (by decide +kernel) node513)
  (invalid_upper a [4,4] 30 (by decide +kernel))
  node547
  node604
  (PrefixConjugacy.upper aut12 [4,7] [4,6] 30 (by decide +kernel) node604)
  (PrefixConjugacy.upper aut11 [4,8] [4,5] 30 (by decide +kernel) node547))

theorem node606 : UpperPrefix a [] 30 :=
  branch_upper a [] 30 (by decide) (fin9_cases _
  (invalid_upper a [0] 30 (by decide +kernel))
  (invalid_upper a [1] 30 (by decide +kernel))
  node514
  (PrefixConjugacy.upper aut5 [3] [2] 30 (by decide +kernel) node514)
  node605
  (PrefixConjugacy.upper aut4 [5] [4] 30 (by decide +kernel) node605)
  (PrefixConjugacy.upper aut3 [6] [4] 30 (by decide +kernel) node605)
  (PrefixConjugacy.upper aut2 [7] [4] 30 (by decide +kernel) node605)
  (PrefixConjugacy.upper aut1 [8] [4] 30 (by decide +kernel) node605))

#print axioms node606
end Delivery.FiniteExclusion.Sharp2x2x5
