import RegularNineSharp2x2x2x3Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x2x3
open Bounds BoundTreeRows Extremal
def cert0 : Local := ⟨⟨0,0,0,0,448,448,304,112,176⟩,[(0,3),(1,2),(2,1),(3,0)],[(2,0,1),(2,0,2),(3,1,0),(3,1,3),(0,2,0),(0,2,3),(1,3,1),(1,3,2)]⟩
theorem node0 : UpperPrefix a [2,3,0,1] 30 :=
  local_sound a [2,3,0,1] 30 cert0 (by decide +kernel)

def cert1 : Leaf := ⟨⟨472,0,0,450,450,450,306,114,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0)],⟨7,11,13,28,498,498,482,482,482⟩,⟨7,11,13,28,48,48,192,384,320⟩,[⟨5,1210107564157958236961855,⟨7,15,15,31,31,31,192,384,320⟩⟩]⟩
theorem node1 : UpperPrefix a [2,3,0,4] 30 :=
  Boolean.leaf_sound a [2,3,0,4] 30 cert1 (by decide +kernel)

def cert2 : Leaf := ⟨⟨488,0,0,418,450,450,306,114,178⟩,[(1,2),(2,1)],[(2,0,1),(2,0,2),(3,1,0),(0,2,0)],⟨7,11,13,76,434,434,498,434,498⟩,⟨7,11,13,76,48,48,192,384,320⟩,[⟨4,1210107565282795244461519,⟨7,15,15,79,32,32,207,399,335⟩⟩]⟩
theorem node2 : UpperPrefix a [2,3,0,6] 30 :=
  Boolean.leaf_sound a [2,3,0,6] 30 cert2 (by decide +kernel)

theorem node3 : UpperPrefix a [2,3,0] 30 :=
  branch_upper a [2,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,0,0] 30 (by decide +kernel))
  node0
  (invalid_upper a [2,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,0,3] 30 (by decide +kernel))
  node1
  (PrefixConjugacy.upper aut3 [2,3,0,5] [2,3,0,4] 30 (by decide +kernel) node1)
  node2
  (PrefixConjugacy.upper aut2 [2,3,0,7] [2,3,0,6] 30 (by decide +kernel) node2)
  (PrefixConjugacy.upper aut1 [2,3,0,8] [2,3,0,6] 30 (by decide +kernel) node2))

def cert4 : Local := ⟨⟨0,0,0,0,448,448,304,112,176⟩,[(0,2),(1,3),(2,1),(3,0)],[(2,0,1),(2,0,3),(3,1,0),(3,1,2),(1,2,0),(1,2,3),(0,3,1),(0,3,2)]⟩
theorem node4 : UpperPrefix a [2,3,1,0] 30 :=
  local_sound a [2,3,1,0] 30 cert4 (by decide +kernel)

def cert5 : Leaf := ⟨⟨0,468,0,449,449,449,305,113,177⟩,[(0,2),(2,1)],[(2,0,1),(3,1,0),(3,1,2),(1,2,0)],⟨7,11,14,28,497,497,481,481,481⟩,⟨7,11,14,28,48,48,192,384,320⟩,[⟨5,1210107564157958236961855,⟨7,15,15,31,31,31,192,384,320⟩⟩]⟩
theorem node5 : UpperPrefix a [2,3,1,4] 30 :=
  Boolean.leaf_sound a [2,3,1,4] 30 cert5 (by decide +kernel)

def cert6 : Leaf := ⟨⟨0,484,0,417,449,449,305,113,177⟩,[(0,2),(2,1)],[(2,0,1),(3,1,0),(3,1,2),(1,2,0)],⟨7,11,14,76,433,433,497,433,497⟩,⟨7,11,14,76,48,48,192,384,320⟩,[⟨4,1210107565282795244461519,⟨7,15,15,79,32,32,207,399,335⟩⟩]⟩
theorem node6 : UpperPrefix a [2,3,1,6] 30 :=
  Boolean.leaf_sound a [2,3,1,6] 30 cert6 (by decide +kernel)

theorem node7 : UpperPrefix a [2,3,1] 30 :=
  branch_upper a [2,3,1] 30 (by decide) (fin9_cases _
  node4
  (invalid_upper a [2,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,1,3] 30 (by decide +kernel))
  node5
  (PrefixConjugacy.upper aut3 [2,3,1,5] [2,3,1,4] 30 (by decide +kernel) node5)
  node6
  (PrefixConjugacy.upper aut2 [2,3,1,7] [2,3,1,6] 30 (by decide +kernel) node6)
  (PrefixConjugacy.upper aut1 [2,3,1,8] [2,3,1,6] 30 (by decide +kernel) node6))

def cert8 : Leaf := ⟨⟨8,4,35,19,451,451,259,67,131⟩,[],[(2,0,1),(3,1,0),(4,2,3),(5,3,2)],⟨7,11,28,44,499,499,451,451,451⟩,⟨7,11,28,44,48,48,192,384,320⟩,[⟨6,1210106412362353534336061,⟨7,11,31,47,63,63,128,384,256⟩⟩,⟨7,1208926973663140729879613,⟨7,11,31,47,63,63,64,256,320⟩⟩,⟨8,1181745669228966476861,⟨7,11,31,47,63,63,192,128,64⟩⟩]⟩
theorem node8 : UpperPrefix a [2,3,4,5] 30 :=
  Boolean.leaf_sound a [2,3,4,5] 30 cert8 (by decide +kernel)

def cert9 : Leaf := ⟨⟨328,324,354,338,322,258,258,66,130⟩,[],[(2,0,1),(3,1,0),(4,2,3),(5,3,2)],⟨7,11,28,44,49,112,450,386,450⟩,⟨7,11,28,44,49,112,192,384,320⟩,[⟨0,1224302389454723659858944,⟨462,458,60,44,508,124,192,384,320⟩⟩,⟨7,1208926984955735152786943,⟨7,31,31,63,63,127,127,319,383⟩⟩]⟩
theorem node9 : UpperPrefix a [2,3,4,5,0,6] 30 :=
  Boolean.leaf_sound a [2,3,4,5,0,6] 30 cert9 (by decide +kernel)

def cert10 : Leaf := ⟨⟨8,4,227,163,194,67,291,99,163⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,49,176,482,418,354⟩,⟨7,11,28,76,49,176,192,384,320⟩,[⟨4,1285813291191632862912013,⟨15,11,463,79,483,480,192,384,320⟩⟩,⟨8,1181752458200127086063,⟨7,31,31,127,49,183,255,191,127⟩⟩,⟨5,1210107564157951779281933,⟨7,11,31,79,17,144,192,384,320⟩⟩,⟨6,1210106412362347079277581,⟨7,11,31,15,49,176,128,384,256⟩⟩,⟨7,1208926973663134274821133,⟨7,11,31,79,49,48,64,256,320⟩⟩]⟩
theorem node10 : UpperPrefix a [2,3,4,6,0,7] 30 :=
  Boolean.leaf_sound a [2,3,4,6,0,7] 30 cert10 (by decide +kernel)

def cert11 : Leaf := ⟨⟨8,4,355,291,322,67,291,99,163⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,49,304,226,418,482⟩,⟨7,11,28,76,49,304,192,384,320⟩,[⟨4,1285813291191632862912013,⟨15,11,463,79,483,480,192,384,320⟩⟩,⟨7,1208926987206961583611391,⟨7,15,31,95,55,319,127,319,383⟩⟩,⟨5,1210107564157951779281933,⟨7,11,31,79,17,272,192,384,320⟩⟩,⟨6,1210106412362347079277581,⟨7,11,31,15,49,304,128,384,256⟩⟩,⟨8,1181745669222511418381,⟨7,11,31,79,49,48,192,128,64⟩⟩]⟩
theorem node11 : UpperPrefix a [2,3,4,6,0,8] 30 :=
  Boolean.leaf_sound a [2,3,4,6,0,8] 30 cert11 (by decide +kernel)

theorem node12 : UpperPrefix a [2,3,4,6,0] 30 :=
  branch_upper a [2,3,4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,6,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut60 [2,3,4,6,0,1] [2,3,4,5,0,6] 30 (by decide +kernel) node9)
  (invalid_upper a [2,3,4,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,0,6] 30 (by decide +kernel))
  node10
  node11)

def cert13 : Leaf := ⟨⟨328,324,353,337,321,257,257,65,129⟩,[],[(2,0,1),(3,1,0),(4,2,3),(5,3,2)],⟨7,11,28,44,50,112,449,385,449⟩,⟨7,11,28,44,50,112,192,384,320⟩,[⟨1,1224302389454723659857921,⟨461,457,60,44,508,124,192,384,320⟩⟩,⟨7,1208926984955735152786943,⟨7,31,31,63,63,127,127,319,383⟩⟩]⟩
theorem node13 : UpperPrefix a [2,3,4,5,1,6] 30 :=
  Boolean.leaf_sound a [2,3,4,5,1,6] 30 cert13 (by decide +kernel)

def cert14 : Leaf := ⟨⟨248,244,224,176,192,64,48,112,176⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,50,176,193,416,352⟩,⟨7,11,28,76,50,176,193,384,320⟩,[⟨8,1184634761985279131135,⟨7,31,31,127,127,255,255,255,127⟩⟩,⟨0,1553198561372065133757440,⟨182,446,444,492,182,176,508,392,492⟩⟩,⟨1,1328729407796726222290945,⟨493,457,444,492,508,444,457,384,320⟩⟩]⟩
theorem node14 : UpperPrefix a [2,3,4,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,7,0] 30 cert14 (by decide +kernel)

def cert15 : Leaf := ⟨⟨120,116,99,51,65,67,0,115,51⟩,[(6,5)],[(2,0,1),(3,1,0),(7,5,6)],⟨7,11,28,76,50,176,224,385,321⟩,⟨7,11,28,76,50,176,224,384,320⟩,[⟨8,1184634761985279131135,⟨7,31,31,127,127,255,255,255,127⟩⟩]⟩
theorem node15 : UpperPrefix a [2,3,4,6,1,7,5] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,7,5] 30 cert15 (by decide +kernel)

def cert16 : Leaf := ⟨⟨216,212,194,146,193,67,0,115,179⟩,[(6,7)],[(2,0,1),(3,1,0),(8,6,6)],⟨7,11,28,76,50,176,448,417,353⟩,⟨7,11,28,76,50,176,448,384,320⟩,[⟨5,1210109870000965300550717,⟨7,11,31,79,31,223,448,448,320⟩⟩,⟨0,1210109871126865207362560,⟨6,10,28,76,62,252,448,448,320⟩⟩]⟩
theorem node16 : UpperPrefix a [2,3,4,6,1,7,8] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,7,8] 30 cert16 (by decide +kernel)

theorem node17 : UpperPrefix a [2,3,4,6,1,7] 30 :=
  branch_upper a [2,3,4,6,1,7] 30 (by decide) (fin9_cases _
  node14
  (invalid_upper a [2,3,4,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,7,4] 30 (by decide +kernel))
  node15
  (invalid_upper a [2,3,4,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,7,7] 30 (by decide +kernel))
  node16)

def cert18 : Leaf := ⟨⟨376,372,352,304,320,64,304,112,176⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,50,304,193,416,480⟩,⟨7,11,28,76,50,304,193,384,320⟩,[⟨0,1553493708679110169461760,⟨182,446,444,492,182,444,508,392,492⟩⟩,⟨1,1328729407796726222290945,⟨493,457,444,492,508,444,457,384,320⟩⟩,⟨7,1208926987206961583611391,⟨7,15,31,95,55,319,127,319,383⟩⟩]⟩
theorem node18 : UpperPrefix a [2,3,4,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,8,0] 30 cert18 (by decide +kernel)

def cert19 : Leaf := ⟨⟨104,100,99,35,65,67,259,99,163⟩,[],[(2,0,1),(3,1,0),(8,5,6)],⟨7,11,28,76,50,304,224,385,449⟩,⟨7,11,28,76,50,304,224,384,320⟩,[⟨4,1266914601888117427281421,⟨399,395,463,463,226,352,224,384,320⟩⟩,⟨7,1208926987206961583611391,⟨7,15,31,95,55,319,127,319,383⟩⟩]⟩
theorem node19 : UpperPrefix a [2,3,4,6,1,8,5] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1,8,5] 30 cert19 (by decide +kernel)

theorem node20 : UpperPrefix a [2,3,4,6,1,8] 30 :=
  branch_upper a [2,3,4,6,1,8] 30 (by decide) (fin9_cases _
  node18
  (invalid_upper a [2,3,4,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,4] 30 (by decide +kernel))
  node19
  (invalid_upper a [2,3,4,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,8,8] 30 (by decide +kernel)))

theorem node21 : UpperPrefix a [2,3,4,6,1] 30 :=
  branch_upper a [2,3,4,6,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut63 [2,3,4,6,1,0] [2,3,4,5,1,6] 30 (by decide +kernel) node13)
  (invalid_upper a [2,3,4,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,1,6] 30 (by decide +kernel))
  node17
  node20)

def cert22 : Leaf := ⟨⟨8,4,227,179,67,2,307,115,51⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,176,49,482,418,354⟩,⟨7,11,28,76,176,49,192,384,320⟩,[⟨8,1181762430220834676191,⟨39,47,63,127,183,49,255,191,127⟩⟩,⟨7,1246705905666828924886029,⟨39,267,319,367,48,49,64,256,320⟩⟩,⟨6,1210106412503084567632909,⟨39,11,63,47,176,49,128,384,256⟩⟩,⟨4,1210107565282752174496781,⟨7,11,15,79,160,33,192,384,320⟩⟩,⟨5,1210107564157951779281933,⟨7,11,31,79,144,17,192,384,320⟩⟩]⟩
theorem node22 : UpperPrefix a [2,3,4,6,7,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,0] 30 cert22 (by decide +kernel)

def cert23 : Leaf := ⟨⟨8,4,227,179,67,1,307,115,51⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,176,50,481,417,353⟩,⟨7,11,28,76,176,50,192,384,320⟩,[⟨8,1181762430220834676191,⟨39,47,63,127,183,51,255,191,127⟩⟩,⟨7,1246705905666828924886029,⟨39,267,319,367,48,50,64,256,320⟩⟩,⟨6,1210106412503084567632909,⟨39,11,63,47,176,50,128,384,256⟩⟩,⟨4,1210107565282752174496781,⟨7,11,15,79,160,34,192,384,320⟩⟩,⟨5,1210107564157951779281933,⟨7,11,31,79,144,18,192,384,320⟩⟩]⟩
theorem node23 : UpperPrefix a [2,3,4,6,7,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,1] 30 cert23 (by decide +kernel)

def cert24 : Leaf := ⟨⟨184,180,160,176,256,128,51,115,179⟩,[],[(2,0,1),(3,1,0),(8,5,4)],⟨7,11,28,76,176,304,227,419,355⟩,⟨7,11,28,76,176,304,192,384,320⟩,[⟨6,1210106425886340103019535,⟨7,15,31,31,176,304,176,432,304⟩⟩,⟨0,1210107578807887785362432,⟨6,14,28,92,180,316,252,444,380⟩⟩,⟨1,1210107578807887785361409,⟨5,13,28,92,180,316,252,444,380⟩⟩]⟩
theorem node24 : UpperPrefix a [2,3,4,6,7,8] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,8] 30 cert24 (by decide +kernel)

theorem node25 : UpperPrefix a [2,3,4,6,7] 30 :=
  branch_upper a [2,3,4,6,7] 30 (by decide) (fin9_cases _
  node22
  node23
  (invalid_upper a [2,3,4,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,7] 30 (by decide +kernel))
  node24)

def cert26 : Leaf := ⟨⟨296,292,355,291,67,258,289,35,163⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,304,49,194,416,480⟩,⟨7,11,28,76,304,49,194,384,320⟩,[⟨4,1437224815066987338161677,⟨79,11,463,79,482,491,194,384,320⟩⟩,⟨7,1208926990155851763006973,⟨39,11,63,111,319,55,127,319,383⟩⟩,⟨6,1210253986455674244045837,⟨39,11,191,47,432,177,130,384,256⟩⟩]⟩
theorem node26 : UpperPrefix a [2,3,4,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,0,1] 30 cert26 (by decide +kernel)

def cert27 : Leaf := ⟨⟨328,324,355,291,67,322,259,67,131⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,304,49,224,386,450⟩,⟨7,11,28,76,304,49,224,384,320⟩,[⟨4,1418326053705877730369037,⟨399,395,463,463,480,483,480,384,320⟩⟩,⟨7,1208926990155851763006973,⟨39,11,63,111,319,55,127,319,383⟩⟩,⟨5,1248015623229424907852813,⟨135,395,415,463,272,17,192,384,320⟩⟩]⟩
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

def cert29 : Leaf := ⟨⟨40,36,355,291,67,1,290,35,179⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,304,50,193,416,480⟩,⟨7,11,28,76,304,50,193,384,320⟩,[⟨7,1208926990155851763006973,⟨39,11,63,111,319,55,127,319,383⟩⟩,⟨4,1210255211292936559959565,⟨79,11,207,79,416,162,203,384,322⟩⟩,⟨6,1210253986455674244045837,⟨39,11,191,47,432,178,129,384,256⟩⟩,⟨8,1181745809959999773709,⟨39,11,63,111,48,50,193,128,64⟩⟩]⟩
theorem node29 : UpperPrefix a [2,3,4,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,1,0] 30 cert29 (by decide +kernel)

def cert30 : Leaf := ⟨⟨264,260,355,307,67,257,259,67,131⟩,[],[(2,0,1),(3,1,0)],⟨7,11,28,76,304,50,224,385,449⟩,⟨7,11,28,76,304,50,224,384,320⟩,[⟨7,1208926990155851763006973,⟨39,11,63,111,319,55,127,319,383⟩⟩,⟨4,1248016200814977606491149,⟨135,395,399,463,352,226,224,384,320⟩⟩,⟨5,1248015623229424907852813,⟨135,395,415,463,272,146,192,384,320⟩⟩,⟨6,1210106412503084567632909,⟨39,11,63,47,304,50,160,384,256⟩⟩]⟩
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

def cert32 : Leaf := ⟨⟨184,180,224,176,128,256,51,115,179⟩,[],[(2,0,1),(3,1,0),(8,4,5)],⟨7,11,28,76,304,176,227,419,355⟩,⟨7,11,28,76,304,176,192,384,320⟩,[⟨0,1210107572065682477548544,⟨6,10,28,108,316,180,252,444,380⟩⟩,⟨1,1210107572065682477547521,⟨5,9,28,108,316,180,252,444,380⟩⟩,⟨6,1210106419144134799399949,⟨7,11,31,47,304,176,176,432,304⟩⟩]⟩
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
  node21
  (invalid_upper a [2,3,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,6] 30 (by decide +kernel))
  node25
  node33)

theorem node35 : UpperPrefix a [2,3,4] 30 :=
  branch_upper a [2,3,4] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut30 [2,3,4,0] [2,3,1,4] 30 (by decide +kernel) node5)
  (PrefixConjugacy.upper aut30 [2,3,4,1] [2,3,0,4] 30 (by decide +kernel) node1)
  (invalid_upper a [2,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,4] 30 (by decide +kernel))
  node8
  node34
  (PrefixConjugacy.upper aut2 [2,3,4,7] [2,3,4,6] 30 (by decide +kernel) node34)
  (PrefixConjugacy.upper aut1 [2,3,4,8] [2,3,4,6] 30 (by decide +kernel) node34))

def cert36 : Leaf := ⟨⟨72,68,130,66,323,323,307,115,51⟩,[],[(2,0,1),(3,1,0),(7,3,2)],⟨7,11,76,140,307,307,499,435,371⟩,⟨7,11,76,140,48,48,192,384,320⟩,[⟨4,1210107565282778028416461,⟨7,11,79,143,32,32,207,399,335⟩⟩,⟨5,1210107564157977633201613,⟨7,11,79,143,16,16,207,399,335⟩⟩,⟨8,1181745669248365338061,⟨7,11,79,143,48,48,207,143,79⟩⟩,⟨0,1210107565283877539808256,⟨6,10,76,140,48,48,204,396,332⟩⟩]⟩
theorem node36 : UpperPrefix a [2,3,6,7] 30 :=
  Boolean.leaf_sound a [2,3,6,7] 30 cert36 (by decide +kernel)

theorem node37 : UpperPrefix a [2,3,6] 30 :=
  branch_upper a [2,3,6] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut30 [2,3,6,0] [2,3,1,6] 30 (by decide +kernel) node6)
  (PrefixConjugacy.upper aut30 [2,3,6,1] [2,3,0,6] 30 (by decide +kernel) node2)
  (invalid_upper a [2,3,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut30 [2,3,6,4] [2,3,4,6] 30 (by decide +kernel) node34)
  (PrefixConjugacy.upper aut33 [2,3,6,5] [2,3,4,6] 30 (by decide +kernel) node34)
  (invalid_upper a [2,3,6,6] 30 (by decide +kernel))
  node36
  (PrefixConjugacy.upper aut31 [2,3,6,8] [2,3,6,7] 30 (by decide +kernel) node36))

theorem node38 : UpperPrefix a [2,3] 30 :=
  branch_upper a [2,3] 30 (by decide) (fin9_cases _
  node3
  node7
  (invalid_upper a [2,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,3] 30 (by decide +kernel))
  node35
  (PrefixConjugacy.upper aut3 [2,3,5] [2,3,4] 30 (by decide +kernel) node35)
  node37
  (PrefixConjugacy.upper aut2 [2,3,7] [2,3,6] 30 (by decide +kernel) node37)
  (PrefixConjugacy.upper aut1 [2,3,8] [2,3,6] 30 (by decide +kernel) node37))

def cert39 : Leaf := ⟨⟨424,424,416,384,392,456,296,104,168⟩,[],[(2,0,2),(4,1,4),(0,2,0),(1,4,1)],⟨7,19,13,44,50,504,456,456,456⟩,⟨7,19,13,44,50,48,192,384,320⟩,[⟨6,1210106412365102316026943,⟨7,31,31,63,63,63,128,384,256⟩⟩]⟩
theorem node39 : UpperPrefix a [2,4,0,5,1] 30 :=
  Boolean.leaf_sound a [2,4,0,5,1] 30 cert39 (by decide +kernel)

def cert40 : Leaf := ⟨⟨408,392,402,402,0,450,274,82,146⟩,[(4,3)],[(2,0,2),(0,2,0),(5,3,4)],⟨7,19,13,44,56,498,450,450,450⟩,⟨7,19,13,44,56,48,192,384,320⟩,[⟨3,1224302388962134384968705,⟨487,499,453,36,48,48,192,384,320⟩⟩,⟨6,1210106412365102316026943,⟨7,31,31,63,63,63,128,384,256⟩⟩]⟩
theorem node40 : UpperPrefix a [2,4,0,5,3] 30 :=
  Boolean.leaf_sound a [2,4,0,5,3] 30 cert40 (by decide +kernel)

def cert41 : Leaf := ⟨⟨344,328,338,338,0,266,282,90,154⟩,[(4,3)],[(2,0,2),(0,2,0),(5,3,4)],⟨7,19,13,44,56,112,450,386,450⟩,⟨7,19,13,44,56,112,192,384,320⟩,[⟨7,1208926984955735152786943,⟨7,31,31,63,63,127,127,319,383⟩⟩]⟩
theorem node41 : UpperPrefix a [2,4,0,5,3,6] 30 :=
  Boolean.leaf_sound a [2,4,0,5,3,6] 30 cert41 (by decide +kernel)

def cert42 : Leaf := ⟨⟨360,360,352,320,328,264,296,104,168⟩,[],[(2,0,2),(4,1,4),(0,2,0),(1,4,1)],⟨7,19,13,44,50,112,456,392,456⟩,⟨7,19,13,44,50,112,192,384,320⟩,[⟨7,1208926984955735152786943,⟨7,31,31,63,63,127,127,319,383⟩⟩]⟩
theorem node42 : UpperPrefix a [2,4,0,5,1,6] 30 :=
  Boolean.leaf_sound a [2,4,0,5,1,6] 30 cert42 (by decide +kernel)

def cert43 : Leaf := ⟨⟨56,40,50,18,138,74,314,122,58⟩,[],[(2,0,2),(0,2,0),(7,5,4)],⟨7,19,13,44,112,176,458,394,330⟩,⟨7,19,13,44,112,176,192,384,320⟩,[⟨8,1181752446678889915899,⟨7,31,13,47,127,191,255,191,127⟩⟩,⟨6,1210106412362353536951355,⟨7,31,13,47,63,191,128,384,256⟩⟩]⟩
theorem node43 : UpperPrefix a [2,4,0,5,6,7] 30 :=
  Boolean.leaf_sound a [2,4,0,5,6,7] 30 cert43 (by decide +kernel)

theorem node44 : UpperPrefix a [2,4,0,5,6] 30 :=
  branch_upper a [2,4,0,5,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut51 [2,4,0,5,6,1] [2,4,0,5,3,6] 30 (by decide +kernel) node41)
  (invalid_upper a [2,4,0,5,6,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut51 [2,4,0,5,6,3] [2,4,0,5,1,6] 30 (by decide +kernel) node42)
  (invalid_upper a [2,4,0,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,6,6] 30 (by decide +kernel))
  node43
  (PrefixConjugacy.upper aut52 [2,4,0,5,6,8] [2,4,0,5,6,7] 30 (by decide +kernel) node43))

theorem node45 : UpperPrefix a [2,4,0,5] 30 :=
  branch_upper a [2,4,0,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,5,0] 30 (by decide +kernel))
  node39
  (invalid_upper a [2,4,0,5,2] 30 (by decide +kernel))
  node40
  (invalid_upper a [2,4,0,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,5,5] 30 (by decide +kernel))
  node44
  (PrefixConjugacy.upper aut2 [2,4,0,5,7] [2,4,0,5,6] 30 (by decide +kernel) node44)
  (PrefixConjugacy.upper aut1 [2,4,0,5,8] [2,4,0,5,6] 30 (by decide +kernel) node44))

def cert46 : Leaf := ⟨⟨232,232,224,160,200,72,296,104,168⟩,[],[(2,0,2),(4,1,4),(0,2,0),(1,4,1)],⟨7,19,13,76,50,176,488,424,360⟩,⟨7,19,13,76,50,176,192,384,320⟩,[⟨8,1181752458200126586349,⟨7,19,31,127,51,183,255,191,127⟩⟩]⟩
theorem node46 : UpperPrefix a [2,4,0,6,1,7] 30 :=
  Boolean.leaf_sound a [2,4,0,6,1,7] 30 cert46 (by decide +kernel)

theorem node47 : UpperPrefix a [2,4,0,6,1] 30 :=
  branch_upper a [2,4,0,6,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,1,2] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut36 [2,4,0,6,1,3] [2,4,0,5,1,6] 30 (by decide +kernel) node42)
  (invalid_upper a [2,4,0,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,1,6] 30 (by decide +kernel))
  node46
  (PrefixConjugacy.upper aut37 [2,4,0,6,1,8] [2,4,0,6,1,7] 30 (by decide +kernel) node46))

def cert48 : Leaf := ⟨⟨24,8,18,434,450,450,306,114,178⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,76,56,434,482,418,482⟩,⟨7,19,13,76,56,48,192,384,320⟩,[⟨3,1224302388962134384968705,⟨487,499,453,68,48,48,192,384,320⟩⟩,⟨5,1210107564157951783494707,⟨7,23,13,76,31,23,192,384,320⟩⟩,⟨6,1210106412362347083490355,⟨7,23,13,12,63,55,128,384,256⟩⟩,⟨7,1208926973663134279033907,⟨7,23,13,76,63,55,64,256,320⟩⟩,⟨8,1181745669222515631155,⟨7,23,13,76,63,55,192,128,64⟩⟩]⟩
theorem node48 : UpperPrefix a [2,4,0,6,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,3] 30 cert48 (by decide +kernel)

def cert49 : Leaf := ⟨⟨488,488,480,416,328,0,296,104,168⟩,[(5,1)],[(2,0,2),(4,1,5),(0,2,0)],⟨7,19,13,76,176,50,488,424,360⟩,⟨7,19,13,76,176,50,192,384,320⟩,[⟨1,1437224743012695728193537,⟨13,477,13,76,504,508,192,384,320⟩⟩]⟩
theorem node49 : UpperPrefix a [2,4,0,6,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,1] 30 cert49 (by decide +kernel)

def cert50 : Leaf := ⟨⟨24,8,18,178,74,194,314,122,186⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,76,176,56,482,418,354⟩,⟨7,19,13,76,176,56,192,384,320⟩,[⟨8,1181761726533401310717,⟨7,19,47,127,183,63,255,191,127⟩⟩,⟨5,1210107564157951787689009,⟨7,19,13,76,151,31,192,384,320⟩⟩,⟨6,1210106412362347087684657,⟨7,19,13,12,183,63,128,384,256⟩⟩,⟨7,1208926973663134283228209,⟨7,19,13,76,55,63,64,256,320⟩⟩]⟩
theorem node50 : UpperPrefix a [2,4,0,6,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,3] 30 cert50 (by decide +kernel)

def cert51 : Leaf := ⟨⟨176,160,178,178,256,128,58,122,186⟩,[],[(2,0,2),(0,2,0),(8,5,4)],⟨7,19,13,76,176,304,234,426,362⟩,⟨7,19,13,76,176,304,192,384,320⟩,[⟨6,1210106425886340103017485,⟨7,19,15,31,176,304,176,432,304⟩⟩,⟨3,1210107578807843634025485,⟨7,19,7,87,176,304,240,432,368⟩⟩,⟨1,1210107578807844707762177,⟨5,17,13,92,176,304,240,432,368⟩⟩]⟩
theorem node51 : UpperPrefix a [2,4,0,6,7,8] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,8] 30 cert51 (by decide +kernel)

theorem node52 : UpperPrefix a [2,4,0,6,7] 30 :=
  branch_upper a [2,4,0,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,7,0] 30 (by decide +kernel))
  node49
  (invalid_upper a [2,4,0,6,7,2] 30 (by decide +kernel))
  node50
  (invalid_upper a [2,4,0,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,7] 30 (by decide +kernel))
  node51)

def cert53 : Leaf := ⟨⟨488,488,480,416,200,0,296,104,168⟩,[(5,1)],[(2,0,2),(4,1,5),(0,2,0)],⟨7,19,13,76,304,50,232,424,488⟩,⟨7,19,13,76,304,50,192,384,320⟩,[⟨1,1437224743012695728193537,⟨13,477,13,76,504,508,192,384,320⟩⟩]⟩
theorem node53 : UpperPrefix a [2,4,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,1] 30 cert53 (by decide +kernel)

def cert54 : Leaf := ⟨⟨24,8,18,306,74,322,314,58,186⟩,[],[(2,0,2),(0,2,0)],⟨7,19,13,76,304,56,226,418,482⟩,⟨7,19,13,76,304,56,192,384,320⟩,[⟨7,1208926990015114285147643,⟨7,55,13,111,319,63,127,319,383⟩⟩,⟨6,1210253986314936764097585,⟨7,147,13,12,439,191,128,384,256⟩⟩,⟨5,1210107564157951787689009,⟨7,19,13,76,279,31,192,384,320⟩⟩,⟨8,1181745669222519825457,⟨7,19,13,76,55,63,192,128,64⟩⟩]⟩
theorem node54 : UpperPrefix a [2,4,0,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,3] 30 cert54 (by decide +kernel)

def cert55 : Leaf := ⟨⟨200,200,194,130,202,330,8,106,186⟩,[],[(2,0,2),(0,2,0),(8,4,5)],⟨7,19,13,76,304,176,194,424,360⟩,⟨7,19,13,76,304,176,194,384,320⟩,[⟨4,1210255175264182308963395,⟨79,207,13,77,428,160,207,396,333⟩⟩,⟨5,1210108140618753573938291,⟨7,31,13,77,351,223,207,396,333⟩⟩]⟩
theorem node55 : UpperPrefix a [2,4,0,6,8,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,7,1] 30 cert55 (by decide +kernel)

def cert56 : Leaf := ⟨⟨176,160,178,178,130,258,50,50,178⟩,[],[(2,0,2),(0,2,0),(8,4,5),(3,6,3)],⟨7,19,13,76,304,176,200,418,354⟩,⟨7,19,13,76,304,176,200,384,320⟩,[⟨6,1212615185978677269865801,⟨39,179,13,47,435,178,191,435,439⟩⟩]⟩
theorem node56 : UpperPrefix a [2,4,0,6,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,7,3] 30 cert56 (by decide +kernel)

def cert57 : Local := ⟨⟨120,104,114,50,74,330,0,122,58⟩,[(6,5)],[(2,0,2),(0,2,0),(8,4,5),(7,5,6)]⟩
theorem node57 : UpperPrefix a [2,4,0,6,8,7,5] 30 :=
  local_sound a [2,4,0,6,8,7,5] 30 cert57 (by decide +kernel)

theorem node58 : UpperPrefix a [2,4,0,6,8,7] 30 :=
  branch_upper a [2,4,0,6,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,8,7,0] 30 (by decide +kernel))
  node55
  (invalid_upper a [2,4,0,6,8,7,2] 30 (by decide +kernel))
  node56
  (invalid_upper a [2,4,0,6,8,7,4] 30 (by decide +kernel))
  node57
  (invalid_upper a [2,4,0,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,7,8] 30 (by decide +kernel)))

theorem node59 : UpperPrefix a [2,4,0,6,8] 30 :=
  branch_upper a [2,4,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,8,0] 30 (by decide +kernel))
  node53
  (invalid_upper a [2,4,0,6,8,2] 30 (by decide +kernel))
  node54
  (invalid_upper a [2,4,0,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,6] 30 (by decide +kernel))
  node58
  (invalid_upper a [2,4,0,6,8,8] 30 (by decide +kernel)))

theorem node60 : UpperPrefix a [2,4,0,6] 30 :=
  branch_upper a [2,4,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,0] 30 (by decide +kernel))
  node47
  (invalid_upper a [2,4,0,6,2] 30 (by decide +kernel))
  node48
  (invalid_upper a [2,4,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,6] 30 (by decide +kernel))
  node52
  node59)

theorem node61 : UpperPrefix a [2,4,0] 30 :=
  branch_upper a [2,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut48 [2,4,0,1] [2,3,0,4] 30 (by decide +kernel) node1)
  (invalid_upper a [2,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,4] 30 (by decide +kernel))
  node45
  node60
  (PrefixConjugacy.upper aut2 [2,4,0,7] [2,4,0,6] 30 (by decide +kernel) node60)
  (PrefixConjugacy.upper aut1 [2,4,0,8] [2,4,0,6] 30 (by decide +kernel) node60))

def cert62 : Leaf := ⟨⟨0,0,496,464,460,460,296,104,168⟩,[(0,2),(1,4)],[(1,2,0),(0,4,1)],⟨7,19,14,44,49,504,456,456,456⟩,⟨7,19,14,44,49,48,192,384,320⟩,[⟨2,1266886859715511798735873,⟨451,19,458,488,51,50,192,384,320⟩⟩,⟨4,1266886859714412288148485,⟨455,3,463,493,33,32,192,384,320⟩⟩]⟩
theorem node62 : UpperPrefix a [2,4,1,5,0] 30 :=
  Boolean.leaf_sound a [2,4,1,5,0] 30 cert62 (by decide +kernel)

def cert63 : Leaf := ⟨⟨0,456,465,465,0,449,273,81,145⟩,[(0,2),(4,3)],[(1,2,0),(5,3,4)],⟨7,19,14,44,56,497,449,449,449⟩,⟨7,19,14,44,56,48,192,384,320⟩,[⟨2,1224302388998144463472129,⟨499,499,506,56,56,48,192,384,320⟩⟩,⟨3,1281081683393794498626565,⟨487,499,487,485,496,48,192,384,320⟩⟩]⟩
theorem node63 : UpperPrefix a [2,4,1,5,3] 30 :=
  Boolean.leaf_sound a [2,4,1,5,3] 30 cert63 (by decide +kernel)

#print axioms node63
end Delivery.FiniteExclusion.Sharp2x2x2x3
