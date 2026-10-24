import RegularNineSharp2x2x5Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Bounds BoundTreeRows Extremal
def cert0 : Local := ⟨⟨0,0,0,0,448,400,304,112,224⟩,[(0,3),(1,2),(2,1),(3,0)],[(2,0,1),(2,0,2),(3,1,0),(3,1,3),(0,2,0),(0,2,3),(1,3,1),(1,3,2)]⟩
theorem node0 : UpperPrefix a [2,3,0,1] 30 :=
  local_sound a [2,3,0,1] 30 cert0 (by decide +kernel)

def cert1 : Leaf := ⟨⟨472,0,0,450,450,402,306,114,226⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0)],⟨7,11,13,28,498,482,482,482,498⟩,⟨7,11,13,28,48,96,192,384,272⟩,[⟨5,1210107564157988394188255,⟨7,15,15,31,31,65,199,399,287⟩⟩]⟩
theorem node1 : UpperPrefix a [2,3,0,4] 30 :=
  Boolean.leaf_sound a [2,3,0,4] 30 cert1 (by decide +kernel)

theorem node2 : UpperPrefix a [2,3,0] 30 :=
  branch_upper a [2,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,0,0] 30 (by decide +kernel))
  node0
  (invalid_upper a [2,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,0,3] 30 (by decide +kernel))
  node1
  (PrefixConjugacy.upper aut4 [2,3,0,5] [2,3,0,4] 30 (by decide +kernel) node1)
  (PrefixConjugacy.upper aut3 [2,3,0,6] [2,3,0,4] 30 (by decide +kernel) node1)
  (PrefixConjugacy.upper aut2 [2,3,0,7] [2,3,0,4] 30 (by decide +kernel) node1)
  (PrefixConjugacy.upper aut1 [2,3,0,8] [2,3,0,4] 30 (by decide +kernel) node1))

def cert3 : Local := ⟨⟨0,0,0,0,448,400,304,112,224⟩,[(0,2),(1,3),(2,1),(3,0)],[(2,0,1),(2,0,3),(3,1,0),(3,1,2),(1,2,0),(1,2,3),(0,3,1),(0,3,2)]⟩
theorem node3 : UpperPrefix a [2,3,1,0] 30 :=
  local_sound a [2,3,1,0] 30 cert3 (by decide +kernel)

def cert4 : Leaf := ⟨⟨0,468,0,449,449,401,305,113,225⟩,[(0,2),(2,1)],[(2,0,1),(3,1,0),(3,1,2),(1,2,0)],⟨7,11,14,28,497,481,481,481,497⟩,⟨7,11,14,28,48,96,192,384,272⟩,[⟨5,1210107564157988394188255,⟨7,15,15,31,31,65,199,399,287⟩⟩]⟩
theorem node4 : UpperPrefix a [2,3,1,4] 30 :=
  Boolean.leaf_sound a [2,3,1,4] 30 cert4 (by decide +kernel)

theorem node5 : UpperPrefix a [2,3,1] 30 :=
  branch_upper a [2,3,1] 30 (by decide) (fin9_cases _
  node3
  (invalid_upper a [2,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,1,3] 30 (by decide +kernel))
  node4
  (PrefixConjugacy.upper aut4 [2,3,1,5] [2,3,1,4] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut3 [2,3,1,6] [2,3,1,4] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut2 [2,3,1,7] [2,3,1,4] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut1 [2,3,1,8] [2,3,1,4] 30 (by decide +kernel) node4))

def cert6 : Leaf := ⟨⟨24,20,34,18,451,403,275,83,195⟩,[],[(2,0,1),(3,1,0),(5,3,2)],⟨7,11,28,44,499,483,451,451,467⟩,⟨7,11,28,44,48,96,192,384,272⟩,[⟨6,1210106412362349298204061,⟨7,11,31,47,63,32,129,391,287⟩⟩,⟨7,1208926973663136493747613,⟨7,11,31,47,63,96,65,263,287⟩⟩,⟨8,1181745669224730344861,⟨7,11,31,47,63,96,193,135,31⟩⟩,⟨0,1210107565283853904905216,⟨6,10,28,44,60,96,192,388,284⟩⟩]⟩
theorem node6 : UpperPrefix a [2,3,4,5] 30 :=
  Boolean.leaf_sound a [2,3,4,5] 30 cert6 (by decide +kernel)

def cert7 : Leaf := ⟨⟨120,116,97,49,66,17,305,113,225⟩,[],[(2,0,1),(3,1,0),(1,5,4)],⟨7,11,28,76,49,98,480,416,432⟩,⟨7,11,28,76,49,98,192,384,272⟩,[⟨7,1208926976203981124599167,⟨23,63,63,127,63,127,127,257,279⟩⟩,⟨8,1181748210069361196415,⟨23,63,63,127,63,127,255,129,23⟩⟩]⟩
theorem node7 : UpperPrefix a [2,3,4,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,0,1] 30 cert7 (by decide +kernel)

def cert8 : Leaf := ⟨⟨104,100,99,51,66,0,307,115,99⟩,[(5,6)],[(2,0,1),(3,1,0),(7,5,5)],⟨7,11,28,76,49,224,482,418,306⟩,⟨7,11,28,76,49,224,192,384,272⟩,[⟨8,1181747928182067625343,⟨7,31,31,127,63,255,255,129,23⟩⟩,⟨4,1210107567534551988182029,⟨7,11,15,111,33,224,224,384,256⟩⟩]⟩
theorem node8 : UpperPrefix a [2,3,4,6,0,7] 30 :=
  Boolean.leaf_sound a [2,3,4,6,0,7] 30 cert8 (by decide +kernel)

def cert9 : Leaf := ⟨⟨488,484,480,416,448,128,288,96,224⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,49,352,194,416,432⟩,⟨7,11,28,76,49,352,194,384,272⟩,[⟨0,1307478758799739032962048,⟨494,234,444,492,508,492,194,388,444⟩⟩,⟨1,1617393230220710011994113,⟨405,445,444,492,445,492,508,384,404⟩⟩,⟨4,1212764193666942293253645,⟨15,11,79,79,227,480,194,416,480⟩⟩]⟩
theorem node9 : UpperPrefix a [2,3,4,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,0,8,1] 30 cert9 (by decide +kernel)

def cert10 : Leaf := ⟨⟨72,68,99,51,66,131,259,83,195⟩,[],[(2,0,1),(3,1,0),(8,5,6)],⟨7,11,28,76,49,352,224,386,402⟩,⟨7,11,28,76,49,352,224,384,272⟩,[⟨7,1208926973669744261004671,⟨7,15,31,95,63,383,127,257,279⟩⟩,⟨4,1210109875629361015561229,⟨7,11,15,79,33,352,224,480,256⟩⟩,⟨5,1229116933925909472222221,⟨391,139,415,463,145,320,192,384,272⟩⟩]⟩
theorem node10 : UpperPrefix a [2,3,4,6,0,8,5] 30 :=
  Boolean.leaf_sound a [2,3,4,6,0,8,5] 30 cert10 (by decide +kernel)

theorem node11 : UpperPrefix a [2,3,4,6,0,8] 30 :=
  branch_upper a [2,3,4,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,6,0,8,0] 30 (by decide +kernel))
  node9
  (invalid_upper a [2,3,4,6,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,8,4] 30 (by decide +kernel))
  node10
  (invalid_upper a [2,3,4,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,8,8] 30 (by decide +kernel)))

theorem node12 : UpperPrefix a [2,3,4,6,0] 30 :=
  branch_upper a [2,3,4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,6,0,0] 30 (by decide +kernel))
  node7
  (invalid_upper a [2,3,4,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,6] 30 (by decide +kernel))
  node8
  node11)

def cert13 : Leaf := ⟨⟨120,116,98,50,65,18,306,114,226⟩,[],[(2,0,1),(3,1,0),(0,5,4)],⟨7,11,28,76,50,97,480,416,432⟩,⟨7,11,28,76,50,97,192,384,272⟩,[⟨7,1208926976203981124599167,⟨23,63,63,127,63,127,127,257,279⟩⟩,⟨8,1181748210069361196415,⟨23,63,63,127,63,127,255,129,23⟩⟩]⟩
theorem node13 : UpperPrefix a [2,3,4,6,1,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,0] 30 cert13 (by decide +kernel)

def cert14 : Leaf := ⟨⟨104,100,99,51,65,0,307,115,99⟩,[(5,6)],[(2,0,1),(3,1,0),(7,5,5)],⟨7,11,28,76,50,224,481,417,305⟩,⟨7,11,28,76,50,224,192,384,272⟩,[⟨8,1181747928182067625343,⟨7,31,31,127,63,255,255,129,23⟩⟩,⟨4,1210107567534551988182029,⟨7,11,15,111,34,224,224,384,256⟩⟩]⟩
theorem node14 : UpperPrefix a [2,3,4,6,1,7] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,7] 30 cert14 (by decide +kernel)

def cert15 : Leaf := ⟨⟨248,244,224,177,192,144,48,112,224⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,50,352,193,416,432⟩,⟨7,11,28,76,50,352,193,384,272⟩,[⟨1,1307478758799739032961025,⟨493,233,444,492,508,492,233,388,444⟩⟩,⟨8,1184051514435055942973,⟨7,11,31,79,63,127,193,193,23⟩⟩,⟨0,1314571477254881293108224,⟨406,446,444,492,438,480,192,384,400⟩⟩]⟩
theorem node15 : UpperPrefix a [2,3,4,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,8,0] 30 cert15 (by decide +kernel)

def cert16 : Leaf := ⟨⟨72,68,99,51,65,131,259,83,195⟩,[],[(2,0,1),(3,1,0),(8,5,6)],⟨7,11,28,76,50,352,224,385,401⟩,⟨7,11,28,76,50,352,224,384,272⟩,[⟨7,1208926973669744261004671,⟨7,15,31,95,63,383,127,257,279⟩⟩,⟨4,1210109875629361015561229,⟨7,11,15,79,34,352,224,480,256⟩⟩,⟨5,1229116933925909472222221,⟨391,139,415,463,18,320,192,384,272⟩⟩]⟩
theorem node16 : UpperPrefix a [2,3,4,6,1,8,5] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,8,5] 30 cert16 (by decide +kernel)

theorem node17 : UpperPrefix a [2,3,4,6,1,8] 30 :=
  branch_upper a [2,3,4,6,1,8] 30 (by decide) (fin9_cases _
  node15
  (invalid_upper a [2,3,4,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,4] 30 (by decide +kernel))
  node16
  (invalid_upper a [2,3,4,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,8] 30 (by decide +kernel)))

theorem node18 : UpperPrefix a [2,3,4,6,1] 30 :=
  branch_upper a [2,3,4,6,1] 30 (by decide) (fin9_cases _
  node13
  (invalid_upper a [2,3,4,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,6] 30 (by decide +kernel))
  node14
  node17)

def cert19 : Leaf := ⟨⟨8,4,227,179,67,2,307,115,99⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,176,97,482,418,306⟩,⟨7,11,28,76,176,97,192,384,272⟩,[⟨8,1181748206908264742271,⟨7,47,63,127,191,127,255,129,23⟩⟩,⟨7,1227816439876087832386573,⟨263,43,319,367,48,97,64,256,272⟩⟩,⟨4,1210107565564227151207437,⟨7,43,47,111,160,97,192,384,256⟩⟩,⟨5,1210107564157951779281933,⟨7,11,31,79,144,65,192,384,272⟩⟩,⟨6,1210106412362347079277581,⟨7,11,31,15,176,33,128,384,272⟩⟩]⟩
theorem node19 : UpperPrefix a [2,3,4,6,7,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,0] 30 cert19 (by decide +kernel)

def cert20 : Leaf := ⟨⟨8,4,227,179,67,1,307,115,99⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,176,98,481,417,305⟩,⟨7,11,28,76,176,98,192,384,272⟩,[⟨8,1181748206908264742271,⟨7,47,63,127,191,127,255,129,23⟩⟩,⟨7,1227816439876087832386573,⟨263,43,319,367,48,98,64,256,272⟩⟩,⟨4,1210107565564227151207437,⟨7,43,47,111,160,98,192,384,256⟩⟩,⟨5,1210107564157951779281933,⟨7,11,31,79,144,66,192,384,272⟩⟩,⟨6,1210106412362347079277581,⟨7,11,31,15,176,34,128,384,272⟩⟩]⟩
theorem node20 : UpperPrefix a [2,3,4,6,7,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,1] 30 cert20 (by decide +kernel)

def cert21 : Leaf := ⟨⟨72,68,195,147,323,19,18,115,99⟩,[],[(2,0,1),(3,1,0),(8,5,4)],⟨7,11,28,76,176,352,193,418,306⟩,⟨7,11,28,76,176,352,193,384,272⟩,[⟨5,1210110158231395735175101,⟨15,11,95,79,223,335,203,463,351⟩⟩,⟨7,1227816439876087832386573,⟨263,43,319,367,48,352,65,256,272⟩⟩,⟨4,1210107565282752174496781,⟨7,11,15,79,160,352,193,384,256⟩⟩]⟩
theorem node21 : UpperPrefix a [2,3,4,6,7,8,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,8,0] 30 cert21 (by decide +kernel)

def cert22 : Leaf := ⟨⟨72,68,195,147,323,19,17,115,99⟩,[],[(2,0,1),(3,1,0),(8,5,4)],⟨7,11,28,76,176,352,194,417,305⟩,⟨7,11,28,76,176,352,194,384,272⟩,[⟨5,1210110158231395735175101,⟨15,11,95,79,223,335,203,463,351⟩⟩,⟨7,1227816439876087832386573,⟨263,43,319,367,48,352,66,256,272⟩⟩,⟨4,1210107565282752174496781,⟨7,11,15,79,160,352,194,384,256⟩⟩]⟩
theorem node22 : UpperPrefix a [2,3,4,6,7,8,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,8,1] 30 cert22 (by decide +kernel)

def cert23 : Leaf := ⟨⟨184,180,163,179,0,147,0,51,163⟩,[(4,6),(6,4)],[(2,0,1),(3,1,0),(8,5,4),(8,5,6)],⟨7,11,28,76,176,352,224,387,275⟩,⟨7,11,28,76,176,352,224,384,272⟩,[⟨6,1266913160741733692087311,⟨391,399,415,415,176,304,176,384,272⟩⟩]⟩
theorem node23 : UpperPrefix a [2,3,4,6,7,8,5] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,8,5] 30 cert23 (by decide +kernel)

theorem node24 : UpperPrefix a [2,3,4,6,7,8] 30 :=
  branch_upper a [2,3,4,6,7,8] 30 (by decide) (fin9_cases _
  node21
  node22
  (invalid_upper a [2,3,4,6,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,8,4] 30 (by decide +kernel))
  node23
  (invalid_upper a [2,3,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,8,8] 30 (by decide +kernel)))

theorem node25 : UpperPrefix a [2,3,4,6,7] 30 :=
  branch_upper a [2,3,4,6,7] 30 (by decide) (fin9_cases _
  node19
  node20
  (invalid_upper a [2,3,4,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,7] 30 (by decide +kernel))
  node24)

def cert26 : Leaf := ⟨⟨488,484,480,416,192,386,289,96,224⟩,[],[(2,0,1),(3,1,0),(1,6,5)],⟨7,11,28,76,304,97,194,416,432⟩,⟨7,11,28,76,304,97,194,384,272⟩,[⟨4,1210255499980709548809741,⟨111,43,239,111,482,107,194,384,448⟩⟩,⟨0,1437223878321567016420352,⟨6,10,412,76,444,508,194,384,404⟩⟩]⟩
theorem node26 : UpperPrefix a [2,3,4,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,0,1] 30 cert26 (by decide +kernel)

def cert27 : Leaf := ⟨⟨264,260,483,419,195,258,259,3,131⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,304,97,224,386,402⟩,⟨7,11,28,76,304,97,224,384,272⟩,[⟨4,1210255499980709548809741,⟨111,43,239,111,482,107,226,384,448⟩⟩,⟨5,1229116933925909472222221,⟨391,139,415,463,272,193,192,384,272⟩⟩,⟨6,1229115782130304772217869,⟨391,139,415,399,304,161,160,384,272⟩⟩,⟨7,1208926973944609251531789,⟨7,43,63,111,304,97,96,256,272⟩⟩]⟩
theorem node27 : UpperPrefix a [2,3,4,6,8,0,5] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,0,5] 30 cert27 (by decide +kernel)

theorem node28 : UpperPrefix a [2,3,4,6,8,0] 30 :=
  branch_upper a [2,3,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,6,8,0,0] 30 (by decide +kernel))
  node26
  (invalid_upper a [2,3,4,6,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,0,4] 30 (by decide +kernel))
  node27
  (invalid_upper a [2,3,4,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,0,8] 30 (by decide +kernel)))

def cert29 : Leaf := ⟨⟨488,484,480,416,192,385,290,96,224⟩,[],[(2,0,1),(3,1,0),(0,6,5)],⟨7,11,28,76,304,98,193,416,432⟩,⟨7,11,28,76,304,98,193,384,272⟩,[⟨4,1210255214002133210799629,⟨111,43,239,111,416,98,235,384,384⟩⟩,⟨1,1437223878321567016419329,⟨5,9,412,76,444,508,193,384,404⟩⟩]⟩
theorem node29 : UpperPrefix a [2,3,4,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,1,0] 30 cert29 (by decide +kernel)

def cert30 : Leaf := ⟨⟨264,260,419,435,131,257,275,19,131⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,304,98,224,385,401⟩,⟨7,11,28,76,304,98,224,384,272⟩,[⟨6,1418324036100940715006991,⟨391,399,415,415,432,435,432,384,272⟩⟩,⟨5,1229116933925909472222221,⟨391,139,415,463,272,66,192,384,272⟩⟩,⟨4,1210107565564227151207437,⟨7,43,47,111,288,98,224,384,256⟩⟩,⟨7,1208926973944609251531789,⟨7,43,63,111,304,98,96,256,272⟩⟩]⟩
theorem node30 : UpperPrefix a [2,3,4,6,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,1,5] 30 cert30 (by decide +kernel)

theorem node31 : UpperPrefix a [2,3,4,6,8,1] 30 :=
  branch_upper a [2,3,4,6,8,1] 30 (by decide) (fin9_cases _
  node29
  (invalid_upper a [2,3,4,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,1,4] 30 (by decide +kernel))
  node30
  (invalid_upper a [2,3,4,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,1,8] 30 (by decide +kernel)))

def cert32 : Leaf := ⟨⟨104,100,99,51,67,0,51,115,99⟩,[(5,6)],[(2,0,1),(3,1,0),(7,5,5)],⟨7,11,28,76,304,224,227,419,307⟩,⟨7,11,28,76,304,224,192,384,272⟩,[⟨8,1184634728402868501917,⟨7,11,31,111,127,235,235,239,31⟩⟩,⟨4,1210107567534551988182029,⟨7,11,15,111,288,224,224,384,256⟩⟩]⟩
theorem node32 : UpperPrefix a [2,3,4,6,8,7] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,7] 30 cert32 (by decide +kernel)

theorem node33 : UpperPrefix a [2,3,4,6,8] 30 :=
  branch_upper a [2,3,4,6,8] 30 (by decide) (fin9_cases _
  node28
  node31
  (invalid_upper a [2,3,4,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,6] 30 (by decide +kernel))
  node32
  (invalid_upper a [2,3,4,6,8,8] 30 (by decide +kernel)))

theorem node34 : UpperPrefix a [2,3,4,6] 30 :=
  branch_upper a [2,3,4,6] 30 (by decide) (fin9_cases _
  node12
  node18
  (invalid_upper a [2,3,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,6] 30 (by decide +kernel))
  node25
  node33)

theorem node35 : UpperPrefix a [2,3,4] 30 :=
  branch_upper a [2,3,4] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut15 [2,3,4,0] [2,3,1,4] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut15 [2,3,4,1] [2,3,0,4] 30 (by decide +kernel) node1)
  (invalid_upper a [2,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,4] 30 (by decide +kernel))
  node6
  node34
  (PrefixConjugacy.upper aut17 [2,3,4,7] [2,3,4,6] 30 (by decide +kernel) node34)
  (PrefixConjugacy.upper aut16 [2,3,4,8] [2,3,4,5] 30 (by decide +kernel) node6))

theorem node36 : UpperPrefix a [2,3] 30 :=
  branch_upper a [2,3] 30 (by decide) (fin9_cases _
  node2
  node5
  (invalid_upper a [2,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,3] 30 (by decide +kernel))
  node35
  (PrefixConjugacy.upper aut4 [2,3,5] [2,3,4] 30 (by decide +kernel) node35)
  (PrefixConjugacy.upper aut3 [2,3,6] [2,3,4] 30 (by decide +kernel) node35)
  (PrefixConjugacy.upper aut2 [2,3,7] [2,3,4] 30 (by decide +kernel) node35)
  (PrefixConjugacy.upper aut1 [2,3,8] [2,3,4] 30 (by decide +kernel) node35))

def cert37 : Leaf := ⟨⟨424,424,416,384,392,392,296,104,232⟩,[],[(2,0,2),(0,2,0),(1,4,1)],⟨7,19,13,44,50,488,456,456,472⟩,⟨7,19,13,44,50,96,192,384,272⟩,[⟨4,1212475679564067279209491,⟨7,15,13,44,47,96,232,492,493⟩⟩,⟨6,1210106412365102383267263,⟨7,31,31,63,63,63,129,391,287⟩⟩]⟩
theorem node37 : UpperPrefix a [2,4,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,1] 30 cert37 (by decide +kernel)

def cert38 : Leaf := ⟨⟨408,392,402,402,0,402,274,82,194⟩,[(4,3)],[(2,0,2),(0,2,0),(5,3,4)],⟨7,19,13,44,56,482,450,450,466⟩,⟨7,19,13,44,56,96,192,384,272⟩,[⟨3,1219580022514449111843841,⟨487,499,229,36,48,96,192,384,272⟩⟩,⟨6,1210106412365102383267263,⟨7,31,31,63,63,63,129,391,287⟩⟩]⟩
theorem node38 : UpperPrefix a [2,4,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,3] 30 cert38 (by decide +kernel)

def cert39 : Leaf := ⟨⟨56,40,50,18,0,410,314,58,170⟩,[(4,5)],[(2,0,2),(0,2,0),(6,4,4)],⟨7,19,13,44,112,490,458,394,410⟩,⟨7,19,13,44,112,96,192,384,272⟩,[⟨7,1208926973665339822994879,⟨7,31,15,63,127,127,65,263,287⟩⟩,⟨8,1181745671428059592127,⟨7,31,15,63,127,127,193,135,31⟩⟩]⟩
theorem node39 : UpperPrefix a [2,4,0,5,6] 30 :=
  Boolean.leaf_sound a [2,4,0,5,6] 30 cert39 (by decide +kernel)

def cert40 : Leaf := ⟨⟨232,232,226,194,72,152,296,104,232⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,44,176,98,456,456,344⟩,⟨7,19,13,44,176,98,192,384,272⟩,[⟨8,1181747925435503273467,⟨7,31,13,47,191,127,255,135,31⟩⟩,⟨4,1212473360210211882140707,⟨7,15,13,45,173,111,192,448,460⟩⟩,⟨1,1266886859716061555589121,⟨453,17,477,508,176,96,192,384,272⟩⟩]⟩
theorem node40 : UpperPrefix a [2,4,0,5,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,7,1] 30 cert40 (by decide +kernel)

def cert41 : Leaf := ⟨⟨112,96,114,82,66,18,306,114,226⟩,[],[(2,0,2),(0,2,0),(3,5,3)],⟨7,19,13,44,176,104,450,450,338⟩,⟨7,19,13,44,176,104,192,384,272⟩,[⟨8,1181747925435503273467,⟨7,31,13,47,191,127,255,135,31⟩⟩,⟨7,1208926975914949209630099,⟨7,31,13,44,63,108,109,263,287⟩⟩]⟩
theorem node41 : UpperPrefix a [2,4,0,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,7,3] 30 cert41 (by decide +kernel)

def cert42 : Leaf := ⟨⟨40,40,34,2,330,154,56,106,234⟩,[],[(2,0,2),(0,2,0),(8,5,4)],⟨7,19,13,44,176,352,194,456,344⟩,⟨7,19,13,44,176,352,194,384,272⟩,[⟨4,1210402713187937978680387,⟨7,15,13,172,172,493,199,384,264⟩⟩,⟨6,1210106412362353604175347,⟨7,31,13,45,191,303,135,391,287⟩⟩,⟨7,1208926973663140799718899,⟨7,31,13,45,63,367,71,263,287⟩⟩]⟩
theorem node42 : UpperPrefix a [2,4,0,5,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,7,8,1] 30 cert42 (by decide +kernel)

def cert43 : Leaf := ⟨⟨176,160,178,146,322,146,50,114,226⟩,[],[(2,0,2),(0,2,0),(8,5,4)],⟨7,19,13,44,176,352,200,450,338⟩,⟨7,19,13,44,176,352,200,384,272⟩,[⟨3,1664340193613821250673677,⟨7,19,23,439,432,498,499,384,272⟩⟩,⟨6,1210106412362353620952499,⟨7,31,13,45,191,303,141,391,287⟩⟩]⟩
theorem node43 : UpperPrefix a [2,4,0,5,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,7,8,3] 30 cert43 (by decide +kernel)

theorem node44 : UpperPrefix a [2,4,0,5,7,8] 30 :=
  branch_upper a [2,4,0,5,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,7,8,0] 30 (by decide +kernel))
  node42
  (invalid_upper a [2,4,0,5,7,8,2] 30 (by decide +kernel))
  node43
  (invalid_upper a [2,4,0,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,8,8] 30 (by decide +kernel)))

theorem node45 : UpperPrefix a [2,4,0,5,7] 30 :=
  branch_upper a [2,4,0,5,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,7,0] 30 (by decide +kernel))
  node40
  (invalid_upper a [2,4,0,5,7,2] 30 (by decide +kernel))
  node41
  (invalid_upper a [2,4,0,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,7,7] 30 (by decide +kernel))
  node44)

def cert46 : Leaf := ⟨⟨232,232,226,194,200,136,40,104,232⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,44,304,98,200,456,472⟩,⟨7,19,13,44,304,98,192,384,272⟩,[⟨4,1212621258527528785282083,⟨111,239,45,45,493,111,192,448,460⟩⟩,⟨8,1184056015863697515955,⟨7,31,13,45,63,111,237,239,31⟩⟩,⟨1,1266886859716061555589121,⟨453,17,477,508,304,96,192,384,272⟩⟩]⟩
theorem node46 : UpperPrefix a [2,4,0,5,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,8,1] 30 cert46 (by decide +kernel)

def cert47 : Leaf := ⟨⟨112,96,114,82,194,18,50,114,226⟩,[],[(2,0,2),(0,2,0),(3,5,3)],⟨7,19,13,44,304,104,194,450,466⟩,⟨7,19,13,44,304,104,192,384,272⟩,[⟨8,1184058267663500715411,⟨7,31,13,44,63,108,237,239,31⟩⟩,⟨7,1208926975914949209630099,⟨7,31,13,44,319,108,109,263,287⟩⟩]⟩
theorem node47 : UpperPrefix a [2,4,0,5,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,8,3] 30 cert47 (by decide +kernel)

def cert48 : Leaf := ⟨⟨120,104,114,82,74,0,58,122,106⟩,[(5,6)],[(2,0,2),(0,2,0),(7,5,5)],⟨7,19,13,44,304,224,202,458,346⟩,⟨7,19,13,44,304,224,192,384,272⟩,[⟨8,1184058267663509104019,⟨7,31,13,44,63,237,237,239,31⟩⟩]⟩
theorem node48 : UpperPrefix a [2,4,0,5,8,7] 30 :=
  Boolean.leaf_sound a [2,4,0,5,8,7] 30 cert48 (by decide +kernel)

theorem node49 : UpperPrefix a [2,4,0,5,8] 30 :=
  branch_upper a [2,4,0,5,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,8,0] 30 (by decide +kernel))
  node46
  (invalid_upper a [2,4,0,5,8,2] 30 (by decide +kernel))
  node47
  (invalid_upper a [2,4,0,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,8,6] 30 (by decide +kernel))
  node48
  (invalid_upper a [2,4,0,5,8,8] 30 (by decide +kernel)))

theorem node50 : UpperPrefix a [2,4,0,5] 30 :=
  branch_upper a [2,4,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,0] 30 (by decide +kernel))
  node37
  (invalid_upper a [2,4,0,5,2] 30 (by decide +kernel))
  node38
  (invalid_upper a [2,4,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,5] 30 (by decide +kernel))
  node39
  node45
  node49)

def cert51 : Leaf := ⟨⟨120,104,112,48,72,408,312,120,232⟩,[],[(2,0,2),(0,2,0),(1,4,1)],⟨7,19,13,76,50,488,488,424,440⟩,⟨7,19,13,76,50,96,192,384,272⟩,[⟨7,1208926973665337605776691,⟨7,23,13,76,63,127,64,259,279⟩⟩,⟨8,1181745671425842373939,⟨7,23,13,76,63,127,192,131,23⟩⟩]⟩
theorem node51 : UpperPrefix a [2,4,0,6,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,1] 30 cert51 (by decide +kernel)

def cert52 : Leaf := ⟨⟨56,40,50,50,66,402,306,50,162⟩,[],[(2,0,2),(0,2,0),(6,3,4)],⟨7,19,13,76,56,482,482,418,434⟩,⟨7,19,13,76,56,96,192,384,272⟩,[⟨7,1208926973665337605776691,⟨7,23,13,76,63,127,64,259,279⟩⟩,⟨8,1181745671425842373939,⟨7,23,13,76,63,127,192,131,23⟩⟩,⟨3,1219580022514449111843841,⟨487,499,229,68,48,96,192,384,272⟩⟩]⟩
theorem node52 : UpperPrefix a [2,4,0,6,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,3] 30 cert52 (by decide +kernel)

def cert53 : Leaf := ⟨⟨120,104,112,48,72,152,312,120,104⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,76,176,98,488,424,312⟩,⟨7,19,13,76,176,98,192,384,272⟩,[⟨1,1437224743012695728193537,⟨13,477,13,76,504,508,192,384,464⟩⟩,⟨8,1181748206908264871295,⟨7,23,47,127,191,127,255,131,23⟩⟩,⟨7,1284484837389052905923891,⟨7,279,13,76,319,111,64,259,279⟩⟩]⟩
theorem node53 : UpperPrefix a [2,4,0,6,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,1] 30 cert53 (by decide +kernel)

def cert54 : Leaf := ⟨⟨184,168,178,178,10,0,314,58,170⟩,[(5,3)],[(2,0,2),(0,2,0),(6,3,5)],⟨7,19,13,76,176,104,482,418,306⟩,⟨7,19,13,76,176,104,192,384,272⟩,[⟨8,1181748206908264871295,⟨7,23,47,127,191,127,255,131,23⟩⟩]⟩
theorem node54 : UpperPrefix a [2,4,0,6,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,3] 30 cert54 (by decide +kernel)

def cert55 : Leaf := ⟨⟨88,72,82,18,330,154,24,122,106⟩,[],[(2,0,2),(0,2,0),(8,5,4)],⟨7,19,13,76,176,352,194,424,312⟩,⟨7,19,13,76,176,352,194,384,272⟩,[⟨5,1210110158231404118156787,⟨15,95,13,77,223,335,207,463,351⟩⟩,⟨7,1284484837389061514732915,⟨7,279,13,77,319,367,79,259,279⟩⟩]⟩
theorem node55 : UpperPrefix a [2,4,0,6,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,8,1] 30 cert55 (by decide +kernel)

def cert56 : Leaf := ⟨⟨208,192,210,146,322,146,18,114,226⟩,[],[(2,0,2),(0,2,0),(8,5,4),(3,6,3)],⟨7,19,13,76,176,352,200,418,306⟩,⟨7,19,13,76,176,352,200,384,272⟩,[⟨5,1210110158231404116059571,⟨15,95,13,76,223,335,205,463,351⟩⟩]⟩
theorem node56 : UpperPrefix a [2,4,0,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,8,3] 30 cert56 (by decide +kernel)

def cert57 : Leaf := ⟨⟨216,200,210,146,0,154,0,90,202⟩,[(4,6),(6,4)],[(2,0,2),(0,2,0),(8,5,4),(8,5,6)],⟨7,19,13,76,176,352,224,394,282⟩,⟨7,19,13,76,176,352,224,384,272⟩,[⟨5,1286108149741648046335283,⟨7,407,13,76,415,463,205,387,407⟩⟩]⟩
theorem node57 : UpperPrefix a [2,4,0,6,7,8,5] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,8,5] 30 cert57 (by decide +kernel)

theorem node58 : UpperPrefix a [2,4,0,6,7,8] 30 :=
  branch_upper a [2,4,0,6,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,7,8,0] 30 (by decide +kernel))
  node55
  (invalid_upper a [2,4,0,6,7,8,2] 30 (by decide +kernel))
  node56
  (invalid_upper a [2,4,0,6,7,8,4] 30 (by decide +kernel))
  node57
  (invalid_upper a [2,4,0,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,8,8] 30 (by decide +kernel)))

theorem node59 : UpperPrefix a [2,4,0,6,7] 30 :=
  branch_upper a [2,4,0,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,7,0] 30 (by decide +kernel))
  node53
  (invalid_upper a [2,4,0,6,7,2] 30 (by decide +kernel))
  node54
  (invalid_upper a [2,4,0,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,7] 30 (by decide +kernel))
  node58)

def cert60 : Leaf := ⟨⟨232,232,224,160,200,136,40,104,232⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,76,304,98,232,424,440⟩,⟨7,19,13,76,304,98,192,384,272⟩,[⟨1,1437224743012695728193537,⟨13,477,13,76,504,508,192,384,464⟩⟩,⟨4,1210255463600109356057635,⟨111,239,45,76,493,111,192,392,460⟩⟩,⟨8,1184056015861480302003,⟨7,23,13,76,63,111,237,239,23⟩⟩]⟩
theorem node60 : UpperPrefix a [2,4,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,1] 30 cert60 (by decide +kernel)

def cert61 : Leaf := ⟨⟨184,168,178,178,138,0,58,58,170⟩,[(5,3)],[(2,0,2),(0,2,0),(6,3,5)],⟨7,19,13,76,304,104,226,418,434⟩,⟨7,19,13,76,304,104,192,384,272⟩,[⟨8,1184058549136262309267,⟨7,23,45,108,63,108,237,239,23⟩⟩]⟩
theorem node61 : UpperPrefix a [2,4,0,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,3] 30 cert61 (by decide +kernel)

def cert62 : Leaf := ⟨⟨120,104,114,50,74,0,58,122,106⟩,[(5,6)],[(2,0,2),(0,2,0),(7,5,5)],⟨7,19,13,76,304,224,234,426,314⟩,⟨7,19,13,76,304,224,192,384,272⟩,[⟨8,1184058267661293987219,⟨7,23,13,108,63,237,237,239,23⟩⟩]⟩
theorem node62 : UpperPrefix a [2,4,0,6,8,7] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,7] 30 cert62 (by decide +kernel)

theorem node63 : UpperPrefix a [2,4,0,6,8] 30 :=
  branch_upper a [2,4,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,8,0] 30 (by decide +kernel))
  node60
  (invalid_upper a [2,4,0,6,8,2] 30 (by decide +kernel))
  node61
  (invalid_upper a [2,4,0,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,6] 30 (by decide +kernel))
  node62
  (invalid_upper a [2,4,0,6,8,8] 30 (by decide +kernel)))

#print axioms node63
end Delivery.FiniteExclusion.Sharp2x2x5
