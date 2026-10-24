import RegularNineSharp3x3x3Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def cert0 : Local := ⟨⟨0,0,0,480,456,464,312,120,184⟩,[(0,1),(1,0),(2,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(1,2,0),(1,2,1)]⟩
theorem node0 : UpperPrefix a [2,0,1] 30 :=
  local_sound a [2,0,1] 30 cert0 (by decide +kernel)

def cert1 : Local := ⟨⟨0,0,498,480,456,464,312,120,184⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(1,3,2)]⟩
theorem node1 : UpperPrefix a [2,0,3,1] 30 :=
  local_sound a [2,0,3,1] 30 cert1 (by decide +kernel)

def cert2 : Local := ⟨⟨0,0,466,0,458,466,282,90,154⟩,[(0,1),(1,0),(3,4)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(5,3,3)]⟩
theorem node2 : UpperPrefix a [2,0,3,5] 30 :=
  local_sound a [2,0,3,5] 30 cert2 (by decide +kernel)

def cert3 : Leaf := ⟨⟨0,0,2,418,458,466,314,122,186⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1)],⟨7,7,13,88,434,442,498,434,498⟩,⟨7,7,13,88,48,40,192,384,320⟩,[⟨4,1210107565282752185007679,⟨7,7,15,79,39,47,192,384,320⟩⟩,⟨5,1210107564157951789792831,⟨7,7,15,95,23,15,192,384,320⟩⟩,⟨6,1210106412362347089788479,⟨7,7,15,31,55,47,128,384,256⟩⟩,⟨7,1208926973663134285332031,⟨7,7,15,95,55,47,64,256,320⟩⟩,⟨8,1181745669222521929279,⟨7,7,15,95,55,47,192,128,64⟩⟩]⟩
theorem node3 : UpperPrefix a [2,0,3,6] 30 :=
  Boolean.leaf_sound a [2,0,3,6] 30 cert3 (by decide +kernel)

theorem node4 : UpperPrefix a [2,0,3] 30 :=
  branch_upper a [2,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,3,0] 30 (by decide +kernel))
  node1
  (invalid_upper a [2,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,0,3,4] 30 (by decide +kernel))
  node2
  node3
  (PrefixConjugacy.upper aut2 [2,0,3,7] [2,0,3,6] 30 (by decide +kernel) node3)
  (PrefixConjugacy.upper aut1 [2,0,3,8] [2,0,3,6] 30 (by decide +kernel) node3))

theorem node5 : UpperPrefix a [2,0] 30 :=
  branch_upper a [2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,0] 30 (by decide +kernel))
  node0
  (invalid_upper a [2,0,2] 30 (by decide +kernel))
  node4
  (PrefixConjugacy.upper aut6 [2,0,4] [2,0,3] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut3 [2,0,5] [2,0,3] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut9 [2,0,6] [2,0,3] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut11 [2,0,7] [2,0,3] 30 (by decide +kernel) node4)
  (PrefixConjugacy.upper aut10 [2,0,8] [2,0,3] 30 (by decide +kernel) node4))

def cert6 : Local := ⟨⟨0,497,0,0,458,450,298,106,170⟩,[(0,1),(2,3),(3,2)],[(2,0,0),(4,2,1),(0,3,1)]⟩
theorem node6 : UpperPrefix a [2,3,4,0] 30 :=
  local_sound a [2,3,4,0] 30 cert6 (by decide +kernel)

def cert7 : Leaf := ⟨⟨0,273,258,257,451,451,291,99,163⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,26,497,489,481,481,481⟩,⟨7,14,21,26,48,40,192,384,320⟩,[⟨3,1361519017103809949205515,⟨7,7,21,23,500,501,192,384,320⟩⟩,⟨5,1210107564157954469953087,⟨15,15,31,31,31,15,192,384,320⟩⟩,⟨6,1210106412362349769948735,⟨15,15,31,31,63,47,128,384,256⟩⟩,⟨7,1208926973663136965492287,⟨15,15,31,31,63,47,64,256,320⟩⟩]⟩
theorem node7 : UpperPrefix a [2,3,4,1] 30 :=
  Boolean.leaf_sound a [2,3,4,1] 30 cert7 (by decide +kernel)

def cert8 : Leaf := ⟨⟨0,465,458,0,459,451,259,67,131⟩,[(0,1),(3,4)],[(2,0,0),(4,2,1),(5,3,3)],⟨7,14,21,56,499,491,451,451,451⟩,⟨7,14,21,56,48,40,192,384,320⟩,[⟨3,1224302388891765640791043,⟨455,455,469,48,48,32,192,384,320⟩⟩]⟩
theorem node8 : UpperPrefix a [2,3,4,5] 30 :=
  Boolean.leaf_sound a [2,3,4,5] 30 cert8 (by decide +kernel)

def cert9 : Local := ⟨⟨0,496,0,418,458,450,298,106,170⟩,[(0,1),(2,4)],[(2,0,0),(4,2,1),(0,4,2)]⟩
theorem node9 : UpperPrefix a [2,3,4,6,0] 30 :=
  local_sound a [2,3,4,6,0] 30 cert9 (by decide +kernel)

def cert10 : Leaf := ⟨⟨0,433,418,417,393,449,289,97,161⟩,[(0,1)],[(2,0,0),(3,1,4),(4,2,1),(1,4,2)],⟨7,14,21,88,50,425,481,417,481⟩,⟨7,14,21,88,50,40,192,384,320⟩,[⟨6,1210106412364546117227579,⟨7,15,21,31,55,63,128,384,256⟩⟩]⟩
theorem node10 : UpperPrefix a [2,3,4,6,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1] 30 cert10 (by decide +kernel)

def cert11 : Leaf := ⟨⟨0,49,42,163,75,2,299,107,43⟩,[(0,1)],[(2,0,0),(4,2,1),(7,4,3)],⟨7,14,21,88,176,41,482,418,354⟩,⟨7,14,21,88,176,41,192,384,320⟩,[⟨8,1181761796902141285883,⟨39,47,21,127,183,47,255,191,127⟩⟩,⟨6,1210106412714190806471739,⟨39,47,21,63,183,47,128,384,256⟩⟩]⟩
theorem node11 : UpperPrefix a [2,3,4,6,7,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,0] 30 cert11 (by decide +kernel)

def cert12 : Local := ⟨⟨0,369,354,419,323,0,291,99,35⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(4,2,1),(7,4,3)]⟩
theorem node12 : UpperPrefix a [2,3,4,6,7,1] 30 :=
  local_sound a [2,3,4,6,7,1] 30 cert12 (by decide +kernel)

def cert13 : Local := ⟨⟨0,49,42,163,267,67,43,43,43⟩,[(0,1)],[(2,0,0),(4,2,1),(6,3,5),(7,4,3),(8,5,4)]⟩
theorem node13 : UpperPrefix a [2,3,4,6,7,8] 30 :=
  local_sound a [2,3,4,6,7,8] 30 cert13 (by decide +kernel)

theorem node14 : UpperPrefix a [2,3,4,6,7] 30 :=
  branch_upper a [2,3,4,6,7] 30 (by decide) (fin9_cases _
  node11
  node12
  (invalid_upper a [2,3,4,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,7] 30 (by decide +kernel))
  node13)

def cert15 : Leaf := ⟨⟨0,49,42,291,75,2,299,43,171⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,88,304,41,226,418,482⟩,⟨7,14,21,88,304,41,192,384,320⟩,[⟨7,1208926990366957997651455,⟨39,47,55,127,319,47,127,319,383⟩⟩,⟨6,1210253986666780482884667,⟨39,47,149,191,439,47,128,384,256⟩⟩,⟨8,1181746021066238612539,⟨39,47,21,127,55,47,192,128,64⟩⟩]⟩
theorem node15 : UpperPrefix a [2,3,4,6,8,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,0] 30 cert15 (by decide +kernel)

def cert16 : Leaf := ⟨⟨0,369,354,291,67,0,291,99,163⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(4,2,1)],⟨7,14,21,88,304,42,225,417,481⟩,⟨7,14,21,88,304,42,192,384,320⟩,[⟨7,1208926990366957997651455,⟨39,47,55,127,319,47,127,319,383⟩⟩]⟩
theorem node16 : UpperPrefix a [2,3,4,6,8,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,1] 30 cert16 (by decide +kernel)

def cert17 : Leaf := ⟨⟨0,177,170,162,202,258,43,43,171⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,88,304,168,227,419,355⟩,⟨7,14,21,88,304,168,192,384,320⟩,[⟨6,1210253986596411738707003,⟨7,47,149,191,439,175,128,384,256⟩⟩,⟨8,1182322129976968641599,⟨7,15,31,95,127,239,192,128,64⟩⟩,⟨0,1210107572065682355913728,⟨6,14,20,120,312,184,248,440,376⟩⟩]⟩
theorem node17 : UpperPrefix a [2,3,4,6,8,7] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,7] 30 cert17 (by decide +kernel)

theorem node18 : UpperPrefix a [2,3,4,6,8] 30 :=
  branch_upper a [2,3,4,6,8] 30 (by decide) (fin9_cases _
  node15
  node16
  (invalid_upper a [2,3,4,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,6] 30 (by decide +kernel))
  node17
  (invalid_upper a [2,3,4,6,8,8] 30 (by decide +kernel)))

theorem node19 : UpperPrefix a [2,3,4,6] 30 :=
  branch_upper a [2,3,4,6] 30 (by decide) (fin9_cases _
  node9
  node10
  (invalid_upper a [2,3,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,6] 30 (by decide +kernel))
  node14
  node18)

theorem node20 : UpperPrefix a [2,3,4] 30 :=
  branch_upper a [2,3,4] 30 (by decide) (fin9_cases _
  node6
  node7
  (invalid_upper a [2,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,4] 30 (by decide +kernel))
  node8
  node19
  (PrefixConjugacy.upper aut2 [2,3,4,7] [2,3,4,6] 30 (by decide +kernel) node19)
  (PrefixConjugacy.upper aut1 [2,3,4,8] [2,3,4,6] 30 (by decide +kernel) node19))

def cert21 : Leaf := ⟨⟨0,497,464,450,456,464,272,80,144⟩,[(0,1)],[(2,0,0),(3,1,4),(0,3,1),(1,4,3)],⟨7,14,37,25,50,504,464,464,464⟩,⟨7,14,37,25,50,40,192,384,320⟩,[⟨5,1323666153021274154075139,⟨7,463,5,473,475,456,192,384,320⟩⟩]⟩
theorem node21 : UpperPrefix a [2,3,5,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,0,1] 30 cert21 (by decide +kernel)

def cert22 : Leaf := ⟨⟨0,49,26,34,386,466,306,114,178⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,37,25,112,442,466,402,466⟩,⟨7,14,37,25,112,40,192,384,320⟩,[⟨3,1224302388892040518697987,⟨471,471,501,465,112,32,192,384,320⟩⟩,⟨6,1210106412362349239366719,⟨7,15,39,31,63,47,128,384,256⟩⟩,⟨7,1208926973663136434910271,⟨7,15,39,31,127,47,64,256,320⟩⟩,⟨8,1181745669224671507519,⟨7,15,39,31,127,47,192,128,64⟩⟩]⟩
theorem node22 : UpperPrefix a [2,3,5,0,6] 30 :=
  Boolean.leaf_sound a [2,3,5,0,6] 30 cert22 (by decide +kernel)

theorem node23 : UpperPrefix a [2,3,5,0] 30 :=
  branch_upper a [2,3,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,0,0] 30 (by decide +kernel))
  node21
  (invalid_upper a [2,3,5,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,5] 30 (by decide +kernel))
  node22
  (PrefixConjugacy.upper aut2 [2,3,5,0,7] [2,3,5,0,6] 30 (by decide +kernel) node22)
  (PrefixConjugacy.upper aut1 [2,3,5,0,8] [2,3,5,0,6] 30 (by decide +kernel) node22))

def cert24 : Leaf := ⟨⟨0,305,282,289,449,467,273,81,145⟩,[(0,1)],[(2,0,0)],⟨7,14,37,26,497,505,465,465,465⟩,⟨7,14,37,26,48,40,192,384,320⟩,[⟨1,1233765604630651611381761,⟨469,476,501,24,48,40,192,384,320⟩⟩,⟨3,1281081683323700632355843,⟨471,471,501,467,48,480,192,384,320⟩⟩,⟨5,1247960427112391855047683,⟨7,463,5,475,16,456,192,384,320⟩⟩,⟨6,1210106412362349239366719,⟨7,15,39,31,63,47,128,384,256⟩⟩,⟨7,1208926973663136434910271,⟨7,15,39,31,63,47,64,256,320⟩⟩]⟩
theorem node24 : UpperPrefix a [2,3,5,1] 30 :=
  Boolean.leaf_sound a [2,3,5,1] 30 cert24 (by decide +kernel)

def cert25 : Leaf := ⟨⟨0,417,0,419,0,467,307,115,179⟩,[(0,1),(2,4),(4,2)],[(2,0,0)],⟨7,14,37,88,49,442,466,402,466⟩,⟨7,14,37,88,49,40,192,384,320⟩,[⟨3,1224302388892040522892291,⟨471,471,501,84,501,32,192,384,320⟩⟩,⟨4,1210107565282752187094079,⟨7,15,39,79,39,47,192,384,320⟩⟩,⟨6,1210106412364820993037375,⟨23,31,55,31,55,63,128,384,256⟩⟩]⟩
theorem node25 : UpperPrefix a [2,3,5,6,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,0] 30 cert25 (by decide +kernel)

def cert26 : Leaf := ⟨⟨0,49,18,387,9,467,275,83,147⟩,[(0,1)],[(2,0,0),(3,1,4)],⟨7,14,37,88,50,441,465,401,465⟩,⟨7,14,37,88,50,40,192,384,320⟩,[⟨5,1285813290066834078303235,⟨7,15,5,472,475,8,192,384,320⟩⟩,⟨6,1210106412364820993037375,⟨23,31,55,31,55,63,128,384,256⟩⟩,⟨7,1208926973665608188580927,⟨23,31,55,95,55,63,64,256,320⟩⟩,⟨8,1181745671696425178175,⟨23,31,55,95,55,63,192,128,64⟩⟩]⟩
theorem node26 : UpperPrefix a [2,3,5,6,1] 30 :=
  Boolean.leaf_sound a [2,3,5,6,1] 30 cert26 (by decide +kernel)

def cert27 : Local := ⟨⟨0,368,0,418,330,338,314,122,58⟩,[(0,1),(2,5)],[(2,0,0),(7,4,3),(0,5,2)]⟩
theorem node27 : UpperPrefix a [2,3,5,6,7,0] 30 :=
  local_sound a [2,3,5,6,7,0] 30 cert27 (by decide +kernel)

def cert28 : Local := ⟨⟨0,369,338,417,321,0,305,113,49⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(7,4,3),(1,5,2)]⟩
theorem node28 : UpperPrefix a [2,3,5,6,7,1] 30 :=
  local_sound a [2,3,5,6,7,1] 30 cert28 (by decide +kernel)

def cert29 : Leaf := ⟨⟨0,353,330,419,323,0,291,99,35⟩,[(0,1),(5,3)],[(2,0,0),(7,4,3),(4,5,5)],⟨7,14,37,88,176,56,451,387,323⟩,⟨7,14,37,88,176,56,192,384,320⟩,[⟨3,1224302388892040518697987,⟨471,471,501,80,176,48,192,384,320⟩⟩]⟩
theorem node29 : UpperPrefix a [2,3,5,6,7,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,4] 30 cert29 (by decide +kernel)

def cert30 : Leaf := ⟨⟨0,49,26,163,259,83,51,51,51⟩,[(0,1)],[(2,0,0),(6,3,5),(7,4,3),(8,5,4)],⟨7,14,37,88,176,296,211,403,339⟩,⟨7,14,37,88,176,296,192,384,320⟩,[⟨3,1224302388892040518697987,⟨471,471,501,80,176,288,192,384,320⟩⟩]⟩
theorem node30 : UpperPrefix a [2,3,5,6,7,8] 30 :=
  Boolean.leaf_sound a [2,3,5,6,7,8] 30 cert30 (by decide +kernel)

theorem node31 : UpperPrefix a [2,3,5,6,7] 30 :=
  branch_upper a [2,3,5,6,7] 30 (by decide) (fin9_cases _
  node27
  node28
  (invalid_upper a [2,3,5,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,3] 30 (by decide +kernel))
  node29
  (invalid_upper a [2,3,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,7,7] 30 (by decide +kernel))
  node30)

def cert32 : Leaf := ⟨⟨0,496,0,418,194,466,306,114,178⟩,[(0,1),(2,5)],[(2,0,0),(0,5,2)],⟨7,14,37,88,304,41,210,402,466⟩,⟨7,14,37,88,304,41,192,384,320⟩,[⟨3,1224302388894239550342147,⟨471,471,501,80,308,501,192,384,320⟩⟩]⟩
theorem node32 : UpperPrefix a [2,3,5,6,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,0] 30 cert32 (by decide +kernel)

def cert33 : Local := ⟨⟨0,497,466,417,193,0,305,113,177⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(1,5,2)]⟩
theorem node33 : UpperPrefix a [2,3,5,6,8,1] 30 :=
  local_sound a [2,3,5,6,8,1] 30 cert33 (by decide +kernel)

def cert34 : Leaf := ⟨⟨0,353,330,291,67,0,291,99,163⟩,[(0,1),(5,3)],[(2,0,0),(4,5,5)],⟨7,14,37,88,304,56,195,387,451⟩,⟨7,14,37,88,304,56,192,384,320⟩,[⟨3,1224302388892040518697987,⟨471,471,501,80,304,48,192,384,320⟩⟩,⟨7,1208926990296589262386687,⟨7,47,39,127,319,63,127,319,383⟩⟩]⟩
theorem node34 : UpperPrefix a [2,3,5,6,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,4] 30 cert34 (by decide +kernel)

def cert35 : Leaf := ⟨⟨0,305,282,418,66,274,307,51,51⟩,[(0,1)],[(2,0,0)],⟨7,14,37,88,304,168,211,403,339⟩,⟨7,14,37,88,304,168,192,384,320⟩,[⟨3,1224302388892040518697987,⟨471,471,501,80,304,160,192,384,320⟩⟩,⟨6,1210253986596411747619903,⟨7,47,39,191,439,175,128,384,256⟩⟩,⟨7,1246705905528290472383551,⟨7,271,55,351,311,319,64,256,320⟩⟩,⟨0,1210107572065682355913728,⟨6,14,36,120,312,184,248,440,376⟩⟩]⟩
theorem node35 : UpperPrefix a [2,3,5,6,8,7] 30 :=
  Boolean.leaf_sound a [2,3,5,6,8,7] 30 cert35 (by decide +kernel)

theorem node36 : UpperPrefix a [2,3,5,6,8] 30 :=
  branch_upper a [2,3,5,6,8] 30 (by decide) (fin9_cases _
  node32
  node33
  (invalid_upper a [2,3,5,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,3] 30 (by decide +kernel))
  node34
  (invalid_upper a [2,3,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,8,6] 30 (by decide +kernel))
  node35
  (invalid_upper a [2,3,5,6,8,8] 30 (by decide +kernel)))

theorem node37 : UpperPrefix a [2,3,5,6] 30 :=
  branch_upper a [2,3,5,6] 30 (by decide) (fin9_cases _
  node25
  node26
  (invalid_upper a [2,3,5,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,6,6] 30 (by decide +kernel))
  node31
  node36)

theorem node38 : UpperPrefix a [2,3,5] 30 :=
  branch_upper a [2,3,5] 30 (by decide) (fin9_cases _
  node23
  node24
  (invalid_upper a [2,3,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,5] 30 (by decide +kernel))
  node37
  (PrefixConjugacy.upper aut2 [2,3,5,7] [2,3,5,6] 30 (by decide +kernel) node37)
  (PrefixConjugacy.upper aut1 [2,3,5,8] [2,3,5,6] 30 (by decide +kernel) node37))

def cert39 : Leaf := ⟨⟨0,497,432,386,456,464,304,112,176⟩,[(0,1)],[(2,0,0),(3,1,4),(0,3,1),(1,4,3)],⟨7,14,69,25,50,440,496,432,496⟩,⟨7,14,69,25,50,40,192,384,320⟩,[⟨5,1210107564157953926759427,⟨7,15,69,25,27,8,192,384,320⟩⟩,⟨6,1210106412362349226755075,⟨7,15,5,25,59,40,128,384,256⟩⟩]⟩
theorem node39 : UpperPrefix a [2,3,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,0,1] 30 cert39 (by decide +kernel)

def cert40 : Leaf := ⟨⟨0,497,432,482,320,0,304,112,176⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(0,3,1)],⟨7,14,69,25,176,42,496,432,368⟩,⟨7,14,69,25,176,42,192,384,320⟩,[⟨1,1437224743012691166101505,⟨5,12,69,477,496,508,192,384,320⟩⟩]⟩
theorem node40 : UpperPrefix a [2,3,6,0,7,1] 30 :=
  Boolean.leaf_sound a [2,3,6,0,7,1] 30 cert40 (by decide +kernel)

def cert41 : Leaf := ⟨⟨0,225,170,226,74,0,298,106,170⟩,[(0,1),(5,3)],[(2,0,0),(0,3,1),(4,5,5)],⟨7,14,69,25,176,56,482,418,354⟩,⟨7,14,69,25,176,56,192,384,320⟩,[⟨8,1181762430240663244743,⟨47,47,127,59,187,56,255,191,127⟩⟩]⟩
theorem node41 : UpperPrefix a [2,3,6,0,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,0,7,4] 30 cert41 (by decide +kernel)

def cert42 : Local := ⟨⟨0,241,186,224,328,208,56,120,184⟩,[(0,1)],[(2,0,0),(0,3,1),(8,5,4),(1,6,2)]⟩
theorem node42 : UpperPrefix a [2,3,6,0,7,8,1] 30 :=
  local_sound a [2,3,6,0,7,8,1] 30 cert42 (by decide +kernel)

def cert43 : Local := ⟨⟨0,113,58,98,330,82,0,122,58⟩,[(0,1),(6,4)],[(2,0,0),(0,3,1),(7,4,6),(8,5,4)]⟩
theorem node43 : UpperPrefix a [2,3,6,0,7,8,4] 30 :=
  local_sound a [2,3,6,0,7,8,4] 30 cert43 (by decide +kernel)

def cert44 : Local := ⟨⟨0,241,186,226,0,210,0,122,186⟩,[(0,1),(4,6),(6,4)],[(2,0,0),(0,3,1),(8,5,4),(8,5,6)]⟩
theorem node44 : UpperPrefix a [2,3,6,0,7,8,5] 30 :=
  local_sound a [2,3,6,0,7,8,5] 30 cert44 (by decide +kernel)

theorem node45 : UpperPrefix a [2,3,6,0,7,8] 30 :=
  branch_upper a [2,3,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,7,8,0] 30 (by decide +kernel))
  node42
  (invalid_upper a [2,3,6,0,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,8,3] 30 (by decide +kernel))
  node43
  node44
  (invalid_upper a [2,3,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,8,8] 30 (by decide +kernel)))

theorem node46 : UpperPrefix a [2,3,6,0,7] 30 :=
  branch_upper a [2,3,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,7,0] 30 (by decide +kernel))
  node40
  (invalid_upper a [2,3,6,0,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,3] 30 (by decide +kernel))
  node41
  (invalid_upper a [2,3,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,7,7] 30 (by decide +kernel))
  node45)

def cert47 : Leaf := ⟨⟨0,497,432,482,192,0,304,112,176⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(0,3,1)],⟨7,14,69,25,304,42,240,432,496⟩,⟨7,14,69,25,304,42,192,384,320⟩,[⟨1,1437224743012691166101505,⟨5,12,69,477,496,508,192,384,320⟩⟩]⟩
theorem node47 : UpperPrefix a [2,3,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,6,0,8,1] 30 cert47 (by decide +kernel)

def cert48 : Leaf := ⟨⟨0,353,298,354,74,0,298,106,170⟩,[(0,1),(5,3)],[(2,0,0),(0,3,1),(4,5,5)],⟨7,14,69,25,304,56,226,418,482⟩,⟨7,14,69,25,304,56,192,384,320⟩,[⟨7,1208926990296612835929559,⟨7,47,111,59,319,59,127,319,383⟩⟩]⟩
theorem node48 : UpperPrefix a [2,3,6,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,0,8,4] 30 cert48 (by decide +kernel)

def cert49 : Leaf := ⟨⟨0,433,442,416,136,272,312,56,184⟩,[(0,1)],[(2,0,0),(0,3,1),(1,6,2)],⟨7,14,69,25,304,168,194,432,368⟩,⟨7,14,69,25,304,168,194,384,320⟩,[⟨6,1212615181123242492431367,⟨7,47,47,185,432,184,187,432,440⟩⟩]⟩
theorem node49 : UpperPrefix a [2,3,6,0,8,7,1] 30 :=
  Boolean.leaf_sound a [2,3,6,0,8,7,1] 30 cert49 (by decide +kernel)

def cert50 : Leaf := ⟨⟨0,81,26,66,202,82,298,122,186⟩,[(0,1)],[(2,0,0),(0,3,1),(8,4,6)],⟨7,14,69,25,304,168,208,418,354⟩,⟨7,14,69,25,304,168,208,384,320⟩,[⟨5,1210107564157962600754647,⟨7,15,79,27,287,137,223,391,335⟩⟩,⟨7,1208926973663145096293847,⟨7,15,79,27,319,41,95,263,335⟩⟩]⟩
theorem node50 : UpperPrefix a [2,3,6,0,8,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,0,8,7,4] 30 cert50 (by decide +kernel)

def cert51 : Local := ⟨⟨0,369,314,354,74,338,0,122,58⟩,[(0,1),(6,5)],[(2,0,0),(0,3,1),(7,5,6)]⟩
theorem node51 : UpperPrefix a [2,3,6,0,8,7,5] 30 :=
  local_sound a [2,3,6,0,8,7,5] 30 cert51 (by decide +kernel)

theorem node52 : UpperPrefix a [2,3,6,0,8,7] 30 :=
  branch_upper a [2,3,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,8,7,0] 30 (by decide +kernel))
  node49
  (invalid_upper a [2,3,6,0,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,7,3] 30 (by decide +kernel))
  node50
  node51
  (invalid_upper a [2,3,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,7,8] 30 (by decide +kernel)))

theorem node53 : UpperPrefix a [2,3,6,0,8] 30 :=
  branch_upper a [2,3,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,8,0] 30 (by decide +kernel))
  node47
  (invalid_upper a [2,3,6,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,3] 30 (by decide +kernel))
  node48
  (invalid_upper a [2,3,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,8,6] 30 (by decide +kernel))
  node52
  (invalid_upper a [2,3,6,0,8,8] 30 (by decide +kernel)))

theorem node54 : UpperPrefix a [2,3,6,0] 30 :=
  branch_upper a [2,3,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,0,0] 30 (by decide +kernel))
  node39
  (invalid_upper a [2,3,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,0,6] 30 (by decide +kernel))
  node46
  node53)

def cert55 : Leaf := ⟨⟨0,481,456,481,393,0,297,105,169⟩,[(0,1),(5,3)],[(2,0,0),(4,5,5)],⟨7,14,37,26,112,56,449,385,449⟩,⟨7,14,37,26,112,56,192,384,320⟩,[⟨1,1233765604982701490962433,⟨501,508,501,56,112,56,192,384,320⟩⟩]⟩
theorem node55 : UpperPrefix a [2,3,5,1,6,4] 30 :=
  Boolean.leaf_sound a [2,3,5,1,6,4] 30 cert55 (by decide +kernel)

def cert56 : Leaf := ⟨⟨0,241,176,225,192,81,305,113,177⟩,[(0,1)],[(2,0,0)],⟨7,14,69,26,49,168,496,432,368⟩,⟨7,14,69,26,49,168,192,384,320⟩,[⟨1,1328397762368389367726081,⟨501,492,469,508,501,488,192,384,320⟩⟩,⟨3,1437224743012690104943627,⟨7,7,69,471,501,501,192,384,320⟩⟩,⟨8,1181752457949774843847,⟨31,31,127,27,59,187,255,191,127⟩⟩]⟩
theorem node56 : UpperPrefix a [2,3,6,1,0,7] 30 :=
  Boolean.leaf_sound a [2,3,6,1,0,7] 30 cert56 (by decide +kernel)

def cert57 : Leaf := ⟨⟨0,369,304,353,320,81,305,113,177⟩,[(0,1)],[(2,0,0)],⟨7,14,69,26,49,296,240,432,496⟩,⟨7,14,69,26,49,296,192,384,320⟩,[⟨1,1328397762368389367726081,⟨501,492,469,508,501,488,192,384,320⟩⟩,⟨3,1437224743012690104943627,⟨7,7,69,471,501,501,192,384,320⟩⟩,⟨7,1208926987206985698758631,⟨15,15,95,27,59,319,127,319,383⟩⟩]⟩
theorem node57 : UpperPrefix a [2,3,6,1,0,8] 30 :=
  Boolean.leaf_sound a [2,3,6,1,0,8] 30 cert57 (by decide +kernel)

theorem node58 : UpperPrefix a [2,3,6,1,0] 30 :=
  branch_upper a [2,3,6,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut93 [2,3,6,1,0,4] [2,3,5,1,6,4] 30 (by decide +kernel) node55)
  (invalid_upper a [2,3,6,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,0,6] 30 (by decide +kernel))
  node56
  node57)

def cert59 : Leaf := ⟨⟨0,241,176,225,65,210,305,113,177⟩,[(0,1)],[(2,0,0),(1,3,5)],⟨7,14,69,26,176,41,496,432,368⟩,⟨7,14,69,26,176,41,192,384,320⟩,[⟨3,1437224743012690100749323,⟨7,7,69,471,500,501,192,384,320⟩⟩,⟨8,1181762535793779511239,⟨47,47,127,59,187,43,255,191,127⟩⟩]⟩
theorem node59 : UpperPrefix a [2,3,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,3,6,1,7,0] 30 cert59 (by decide +kernel)

def cert60 : Local := ⟨⟨0,480,0,480,330,0,298,106,170⟩,[(0,1),(2,6),(5,3)],[(2,0,0),(4,5,5),(0,6,2)]⟩
theorem node60 : UpperPrefix a [2,3,6,1,7,4,0] 30 :=
  local_sound a [2,3,6,1,7,4,0] 30 cert60 (by decide +kernel)

def cert61 : Local := ⟨⟨0,481,426,481,0,0,0,107,171⟩,[(0,1),(4,6),(5,3),(6,4)],[(2,0,0),(4,5,5)]⟩
theorem node61 : UpperPrefix a [2,3,6,1,7,4,5] 30 :=
  local_sound a [2,3,6,1,7,4,5] 30 cert61 (by decide +kernel)

def cert62 : Local := ⟨⟨0,225,170,225,75,0,0,107,171⟩,[(0,1),(5,3),(6,7)],[(2,0,0),(4,5,5),(8,6,6)]⟩
theorem node62 : UpperPrefix a [2,3,6,1,7,4,8] 30 :=
  local_sound a [2,3,6,1,7,4,8] 30 cert62 (by decide +kernel)

theorem node63 : UpperPrefix a [2,3,6,1,7,4] 30 :=
  branch_upper a [2,3,6,1,7,4] 30 (by decide) (fin9_cases _
  node60
  (invalid_upper a [2,3,6,1,7,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,4,4] 30 (by decide +kernel))
  node61
  (invalid_upper a [2,3,6,1,7,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,4,7] 30 (by decide +kernel))
  node62)

#print axioms node63
end Delivery.FiniteExclusion.Sharp3x3x3
