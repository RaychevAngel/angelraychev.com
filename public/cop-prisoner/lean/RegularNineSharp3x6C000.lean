import RegularNineSharp3x6Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert0 : Local := ⟨⟨0,0,0,480,456,408,312,120,240⟩,[(0,1),(1,0),(2,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(1,2,0),(1,2,1)]⟩
theorem node0 : UpperPrefix a [2,0,1] 30 :=
  local_sound a [2,0,1] 30 cert0 (by decide +kernel)

def cert1 : Local := ⟨⟨0,0,498,480,456,408,312,120,240⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(1,3,2)]⟩
theorem node1 : UpperPrefix a [2,0,3,1] 30 :=
  local_sound a [2,0,3,1] 30 cert1 (by decide +kernel)

def cert2 : Local := ⟨⟨0,0,466,0,458,410,282,90,210⟩,[(0,1),(1,0),(3,4)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(5,3,3)]⟩
theorem node2 : UpperPrefix a [2,0,3,5] 30 :=
  local_sound a [2,0,3,5] 30 cert2 (by decide +kernel)

def cert3 : Leaf := ⟨⟨0,0,2,418,458,410,314,122,242⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1)],⟨7,7,13,88,434,498,498,434,442⟩,⟨7,7,13,88,48,96,192,384,264⟩,[⟨4,1210107565282752243900303,⟨7,7,15,79,32,96,195,391,271⟩⟩,⟨5,1210107564157951848685455,⟨7,7,15,95,16,64,195,391,271⟩⟩,⟨6,1210106412362347148681103,⟨7,7,15,31,48,32,131,391,271⟩⟩,⟨7,1208926973663134344224655,⟨7,7,15,95,48,96,67,263,271⟩⟩,⟨8,1181745669222580821903,⟨7,7,15,95,48,96,195,135,15⟩⟩]⟩
theorem node3 : UpperPrefix a [2,0,3,6] 30 :=
  Boolean.leaf_sound a [2,0,3,6] 30 cert3 (by decide +kernel)

def cert4 : Leaf := ⟨⟨0,0,2,354,458,410,314,122,242⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1)],⟨7,7,13,152,370,370,498,498,378⟩,⟨7,7,13,152,48,96,192,384,264⟩,[⟨4,1210107565282752243900303,⟨7,7,15,143,32,96,195,391,271⟩⟩,⟨5,1210107564157951848685455,⟨7,7,15,159,16,64,195,391,271⟩⟩,⟨6,1210106412362347148681103,⟨7,7,15,159,48,32,131,391,271⟩⟩,⟨7,1208926973663134344224655,⟨7,7,15,31,48,96,67,263,271⟩⟩,⟨8,1181745669222580821903,⟨7,7,15,159,48,96,195,135,15⟩⟩]⟩
theorem node4 : UpperPrefix a [2,0,3,7] 30 :=
  Boolean.leaf_sound a [2,0,3,7] 30 cert4 (by decide +kernel)

def cert5 : Leaf := ⟨⟨0,0,226,226,202,154,58,122,242⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1)],⟨7,7,13,280,242,242,242,498,506⟩,⟨7,7,13,280,48,96,192,384,264⟩,[⟨8,1184058280825375104911,⟨7,7,15,31,48,112,243,247,15⟩⟩,⟨4,1210107565282752243900303,⟨7,7,15,271,32,96,195,391,271⟩⟩]⟩
theorem node5 : UpperPrefix a [2,0,3,8] 30 :=
  Boolean.leaf_sound a [2,0,3,8] 30 cert5 (by decide +kernel)

theorem node6 : UpperPrefix a [2,0,3] 30 :=
  branch_upper a [2,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,3,0] 30 (by decide +kernel))
  node1
  (invalid_upper a [2,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,0,3,4] 30 (by decide +kernel))
  node2
  node3
  node4
  node5)

theorem node7 : UpperPrefix a [2,0] 30 :=
  branch_upper a [2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,0] 30 (by decide +kernel))
  node0
  (invalid_upper a [2,0,2] 30 (by decide +kernel))
  node6
  (PrefixConjugacy.upper aut5 [2,0,4] [2,0,3] 30 (by decide +kernel) node6)
  (PrefixConjugacy.upper aut4 [2,0,5] [2,0,3] 30 (by decide +kernel) node6)
  (PrefixConjugacy.upper aut3 [2,0,6] [2,0,3] 30 (by decide +kernel) node6)
  (PrefixConjugacy.upper aut2 [2,0,7] [2,0,3] 30 (by decide +kernel) node6)
  (PrefixConjugacy.upper aut1 [2,0,8] [2,0,3] 30 (by decide +kernel) node6))

def cert8 : Local := ⟨⟨0,497,0,0,458,394,298,106,226⟩,[(0,1),(2,3),(3,2)],[(2,0,0),(4,2,1),(0,3,1)]⟩
theorem node8 : UpperPrefix a [2,3,4,0] 30 :=
  local_sound a [2,3,4,0] 30 cert8 (by decide +kernel)

def cert9 : Leaf := ⟨⟨0,273,258,257,451,387,291,99,227⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,26,497,481,481,481,489⟩,⟨7,14,21,26,48,96,192,384,264⟩,[⟨3,1212473369236095372362763,⟨7,7,21,23,48,96,192,500,501⟩⟩,⟨5,1210107564157954470067999,⟨15,15,31,31,31,64,192,387,271⟩⟩,⟨6,1210106412362349770063647,⟨15,15,31,31,63,32,128,387,271⟩⟩,⟨7,1208926973663136965607199,⟨15,15,31,31,63,96,64,259,271⟩⟩]⟩
theorem node9 : UpperPrefix a [2,3,4,1] 30 :=
  Boolean.leaf_sound a [2,3,4,1] 30 cert9 (by decide +kernel)

def cert10 : Leaf := ⟨⟨0,273,266,0,459,395,267,75,195⟩,[(0,1),(3,4)],[(2,0,0),(4,2,1),(5,3,3)],⟨7,14,21,56,499,483,451,451,459⟩,⟨7,14,21,56,48,96,192,384,264⟩,[⟨6,1210106412362349233192223,⟨7,15,31,63,63,32,128,387,271⟩⟩,⟨7,1208926973663136428735775,⟨7,15,31,63,63,96,64,259,271⟩⟩]⟩
theorem node10 : UpperPrefix a [2,3,4,5] 30 :=
  Boolean.leaf_sound a [2,3,4,5] 30 cert10 (by decide +kernel)

def cert11 : Local := ⟨⟨0,496,0,418,458,394,298,106,226⟩,[(0,1),(2,4)],[(2,0,0),(4,2,1),(0,4,2)]⟩
theorem node11 : UpperPrefix a [2,3,4,6,0] 30 :=
  local_sound a [2,3,4,6,0] 30 cert11 (by decide +kernel)

def cert12 : Leaf := ⟨⟨0,113,106,33,73,393,297,105,225⟩,[(0,1)],[(2,0,0),(4,2,1),(1,4,2)],⟨7,14,21,88,50,481,481,417,425⟩,⟨7,14,21,88,50,96,192,384,264⟩,[⟨7,1208926973665337607877951,⟨7,15,23,95,63,127,64,259,271⟩⟩,⟨8,1181745671425844475199,⟨7,15,23,95,63,127,192,131,15⟩⟩]⟩
theorem node12 : UpperPrefix a [2,3,4,6,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1] 30 cert12 (by decide +kernel)

def cert13 : Leaf := ⟨⟨0,81,74,163,75,10,299,107,99⟩,[(0,1)],[(2,0,0),(4,2,1),(7,4,3)],⟨7,14,21,88,176,97,482,418,298⟩,⟨7,14,21,88,176,97,192,384,264⟩,[⟨8,1181748206908264871295,⟨7,47,23,127,191,127,255,131,47⟩⟩,⟨5,1210107564157951781508363,⟨7,15,21,95,144,65,192,387,271⟩⟩]⟩
theorem node13 : UpperPrefix a [2,3,4,6,7,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,0] 30 cert13 (by decide +kernel)

def cert14 : Leaf := ⟨⟨0,81,74,163,75,9,299,107,99⟩,[(0,1)],[(2,0,0),(4,2,1),(7,4,3)],⟨7,14,21,88,176,98,481,417,297⟩,⟨7,14,21,88,176,98,192,384,264⟩,[⟨8,1181748206908264871295,⟨7,47,23,127,191,127,255,131,47⟩⟩,⟨5,1210107564157951781508363,⟨7,15,21,95,144,67,192,387,271⟩⟩]⟩
theorem node14 : UpperPrefix a [2,3,4,6,7,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,1] 30 cert14 (by decide +kernel)

def cert15 : Leaf := ⟨⟨0,49,42,163,267,11,43,43,99⟩,[(0,1)],[(2,0,0),(4,2,1),(7,4,3),(8,5,4)],⟨7,14,21,88,176,352,227,419,299⟩,⟨7,14,21,88,176,352,192,384,264⟩,[⟨6,1210401560269725470168363,⟨7,15,21,31,181,439,128,387,271⟩⟩]⟩
theorem node15 : UpperPrefix a [2,3,4,6,7,8] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,8] 30 cert15 (by decide +kernel)

theorem node16 : UpperPrefix a [2,3,4,6,7] 30 :=
  branch_upper a [2,3,4,6,7] 30 (by decide) (fin9_cases _
  node13
  node14
  (invalid_upper a [2,3,4,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,7] 30 (by decide +kernel))
  node15)

def cert17 : Leaf := ⟨⟨0,49,42,419,75,10,43,43,227⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,88,304,97,226,418,426⟩,⟨7,14,21,88,304,97,192,384,264⟩,[⟨7,1208926976214001358345627,⟨7,47,21,127,311,97,101,279,319⟩⟩,⟨8,1184056297306335614235,⟨7,47,21,127,55,97,224,227,47⟩⟩,⟨6,1210253986314936762111259,⟨7,15,149,159,439,33,128,387,271⟩⟩]⟩
theorem node17 : UpperPrefix a [2,3,4,6,8,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,0] 30 cert17 (by decide +kernel)

def cert18 : Leaf := ⟨⟨0,49,42,419,75,9,43,43,227⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,88,304,98,225,417,425⟩,⟨7,14,21,88,304,98,192,384,264⟩,[⟨7,1208926973962201544660379,⟨7,47,21,127,311,99,69,279,319⟩⟩,⟨8,1184056297306335614235,⟨7,47,21,127,55,99,224,227,47⟩⟩,⟨6,1210253986314936762111259,⟨7,15,149,159,439,35,128,387,271⟩⟩]⟩
theorem node18 : UpperPrefix a [2,3,4,6,8,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,1] 30 cert18 (by decide +kernel)

def cert19 : Leaf := ⟨⟨0,305,298,291,75,0,299,43,99⟩,[(0,1),(5,6)],[(2,0,0),(4,2,1),(7,5,5)],⟨7,14,21,88,304,224,227,419,299⟩,⟨7,14,21,88,304,224,192,384,264⟩,[⟨6,1210253986314936762111259,⟨7,15,149,159,439,160,128,387,271⟩⟩]⟩
theorem node19 : UpperPrefix a [2,3,4,6,8,7] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,7] 30 cert19 (by decide +kernel)

theorem node20 : UpperPrefix a [2,3,4,6,8] 30 :=
  branch_upper a [2,3,4,6,8] 30 (by decide) (fin9_cases _
  node17
  node18
  (invalid_upper a [2,3,4,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,6] 30 (by decide +kernel))
  node19
  (invalid_upper a [2,3,4,6,8,8] 30 (by decide +kernel)))

theorem node21 : UpperPrefix a [2,3,4,6] 30 :=
  branch_upper a [2,3,4,6] 30 (by decide) (fin9_cases _
  node11
  node12
  (invalid_upper a [2,3,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,6] 30 (by decide +kernel))
  node16
  node20)

def cert22 : Local := ⟨⟨0,496,0,354,458,394,298,106,226⟩,[(0,1),(2,4)],[(2,0,0),(4,2,1),(0,4,2)]⟩
theorem node22 : UpperPrefix a [2,3,4,7,0] 30 :=
  local_sound a [2,3,4,7,0] 30 cert22 (by decide +kernel)

def cert23 : Leaf := ⟨⟨0,17,10,353,457,393,297,105,225⟩,[(0,1)],[(2,0,0),(4,2,1),(1,4,2)],⟨7,14,21,152,50,353,481,481,361⟩,⟨7,14,21,152,50,96,192,384,264⟩,[⟨5,1210107564157951785702683,⟨7,15,21,159,23,64,192,387,271⟩⟩,⟨6,1210106412362347085698331,⟨7,15,21,159,55,32,128,387,271⟩⟩,⟨7,1208926973663134281241883,⟨7,15,21,31,55,96,64,259,271⟩⟩,⟨8,1181745669222517839131,⟨7,15,21,159,55,96,192,131,15⟩⟩]⟩
theorem node23 : UpperPrefix a [2,3,4,7,1] 30 :=
  Boolean.leaf_sound a [2,3,4,7,1] 30 cert23 (by decide +kernel)

def cert24 : Leaf := ⟨⟨0,401,394,291,0,395,299,43,163⟩,[(0,1),(4,5)],[(2,0,0),(4,2,1),(6,4,4)],⟨7,14,21,152,112,355,483,419,299⟩,⟨7,14,21,152,112,96,192,384,264⟩,[⟨5,1210107564157951781508363,⟨7,15,21,159,80,64,192,387,271⟩⟩]⟩
theorem node24 : UpperPrefix a [2,3,4,7,6] 30 :=
  Boolean.leaf_sound a [2,3,4,7,6] 30 cert24 (by decide +kernel)

def cert25 : Leaf := ⟨⟨0,240,232,352,200,138,40,104,224⟩,[(0,1)],[(2,0,0),(4,2,1),(8,4,3),(1,6,5)],⟨7,14,21,152,304,97,194,480,360⟩,⟨7,14,21,152,304,97,194,384,264⟩,[⟨0,1437224526839916029545984,⟨78,78,478,408,504,506,194,384,264⟩⟩]⟩
theorem node25 : UpperPrefix a [2,3,4,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,4,7,8,0,1] 30 cert25 (by decide +kernel)

def cert26 : Leaf := ⟨⟨0,240,234,354,202,138,10,106,226⟩,[(0,1)],[(2,0,0),(4,2,1),(8,4,3)],⟨7,14,21,152,304,97,224,450,330⟩,⟨7,14,21,152,304,97,224,384,264⟩,[⟨0,1380445664758226779901440,⟨398,398,478,216,504,506,504,384,264⟩⟩]⟩
theorem node26 : UpperPrefix a [2,3,4,7,8,0,5] 30 :=
  Boolean.leaf_sound a [2,3,4,7,8,0,5] 30 cert26 (by decide +kernel)

theorem node27 : UpperPrefix a [2,3,4,7,8,0] 30 :=
  branch_upper a [2,3,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,7,8,0,0] 30 (by decide +kernel))
  node25
  (invalid_upper a [2,3,4,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,4] 30 (by decide +kernel))
  node26
  (invalid_upper a [2,3,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,8] 30 (by decide +kernel)))

def cert28 : Leaf := ⟨⟨0,240,234,352,200,137,42,104,224⟩,[(0,1)],[(2,0,0),(4,2,1),(8,4,3)],⟨7,14,21,152,304,98,193,480,360⟩,⟨7,14,21,152,304,98,193,384,264⟩,[⟨0,1361518440643065151491072,⟨6,14,30,152,440,506,192,384,264⟩⟩,⟨1,1361518440643065151488001,⟨5,12,29,152,440,504,193,384,264⟩⟩]⟩
theorem node28 : UpperPrefix a [2,3,4,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,4,7,8,1,0] 30 cert28 (by decide +kernel)

def cert29 : Leaf := ⟨⟨0,17,10,355,203,137,11,107,227⟩,[(0,1)],[(2,0,0),(4,2,1),(8,4,3)],⟨7,14,21,152,304,98,224,449,329⟩,⟨7,14,21,152,304,98,224,384,264⟩,[⟨5,1210107564157951785702683,⟨7,15,21,159,279,67,192,387,271⟩⟩,⟨6,1210106412362347085698331,⟨7,15,21,159,311,35,160,387,271⟩⟩,⟨7,1208926973663134281241883,⟨7,15,21,31,311,99,96,259,271⟩⟩]⟩
theorem node29 : UpperPrefix a [2,3,4,7,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,4,7,8,1,5] 30 cert29 (by decide +kernel)

theorem node30 : UpperPrefix a [2,3,4,7,8,1] 30 :=
  branch_upper a [2,3,4,7,8,1] 30 (by decide) (fin9_cases _
  node28
  (invalid_upper a [2,3,4,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,4] 30 (by decide +kernel))
  node29
  (invalid_upper a [2,3,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,8] 30 (by decide +kernel)))

theorem node31 : UpperPrefix a [2,3,4,7,8] 30 :=
  branch_upper a [2,3,4,7,8] 30 (by decide) (fin9_cases _
  node27
  node30
  (invalid_upper a [2,3,4,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,8] 30 (by decide +kernel)))

theorem node32 : UpperPrefix a [2,3,4,7] 30 :=
  branch_upper a [2,3,4,7] 30 (by decide) (fin9_cases _
  node22
  node23
  (invalid_upper a [2,3,4,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,5] 30 (by decide +kernel))
  node24
  (invalid_upper a [2,3,4,7,7] 30 (by decide +kernel))
  node31)

def cert33 : Local := ⟨⟨0,496,0,226,458,394,298,106,226⟩,[(0,1),(2,4)],[(2,0,0),(4,2,1),(0,4,2)]⟩
theorem node33 : UpperPrefix a [2,3,4,8,0] 30 :=
  local_sound a [2,3,4,8,0] 30 cert33 (by decide +kernel)

def cert34 : Leaf := ⟨⟨0,241,226,225,193,129,33,97,225⟩,[(0,1)],[(2,0,0),(4,2,1),(1,4,2)],⟨7,14,21,280,50,225,225,481,489⟩,⟨7,14,21,280,50,96,192,384,264⟩,[⟨3,1210181532756180431799315,⟨119,247,21,501,119,96,192,384,484⟩⟩,⟨8,1184058276427315942811,⟨7,15,21,31,55,100,245,247,15⟩⟩]⟩
theorem node34 : UpperPrefix a [2,3,4,8,1] 30 :=
  Boolean.leaf_sound a [2,3,4,8,1] 30 cert34 (by decide +kernel)

def cert35 : Leaf := ⟨⟨0,177,170,163,0,139,43,43,163⟩,[(0,1),(4,5)],[(2,0,0),(4,2,1),(6,4,4)],⟨7,14,21,280,112,227,227,419,427⟩,⟨7,14,21,280,112,96,192,384,264⟩,[⟨8,1184056031224567829899,⟨7,15,21,31,116,116,245,247,15⟩⟩]⟩
theorem node35 : UpperPrefix a [2,3,4,8,6] 30 :=
  Boolean.leaf_sound a [2,3,4,8,6] 30 cert35 (by decide +kernel)

def cert36 : Leaf := ⟨⟨0,17,10,227,75,138,43,107,227⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,280,176,97,226,482,362⟩,⟨7,14,21,280,176,97,192,384,264⟩,[⟨8,1184058843775324263819,⟨7,15,53,63,245,117,245,247,15⟩⟩,⟨5,1210107564157951781508363,⟨7,15,21,287,144,65,192,387,271⟩⟩,⟨6,1210106412362347081504011,⟨7,15,21,287,176,33,128,387,271⟩⟩,⟨7,1208926973663134277047563,⟨7,15,21,287,48,97,64,259,271⟩⟩]⟩
theorem node36 : UpperPrefix a [2,3,4,8,7,0] 30 :=
  Boolean.leaf_sound a [2,3,4,8,7,0] 30 cert36 (by decide +kernel)

def cert37 : Leaf := ⟨⟨0,17,10,227,75,137,43,107,227⟩,[(0,1)],[(2,0,0),(4,2,1)],⟨7,14,21,280,176,98,225,481,361⟩,⟨7,14,21,280,176,98,192,384,264⟩,[⟨8,1184344540876685579691,⟨7,47,85,127,245,119,245,247,47⟩⟩,⟨5,1210107564157951781508363,⟨7,15,21,287,144,67,192,387,271⟩⟩,⟨6,1210106412362347081504011,⟨7,15,21,287,176,35,128,387,271⟩⟩,⟨7,1208926973663134277047563,⟨7,15,21,287,48,99,64,259,271⟩⟩]⟩
theorem node37 : UpperPrefix a [2,3,4,8,7,1] 30 :=
  Boolean.leaf_sound a [2,3,4,8,7,1] 30 cert37 (by decide +kernel)

theorem node38 : UpperPrefix a [2,3,4,8,7] 30 :=
  branch_upper a [2,3,4,8,7] 30 (by decide) (fin9_cases _
  node36
  node37
  (invalid_upper a [2,3,4,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,7,8] 30 (by decide +kernel)))

theorem node39 : UpperPrefix a [2,3,4,8] 30 :=
  branch_upper a [2,3,4,8] 30 (by decide) (fin9_cases _
  node33
  node34
  (invalid_upper a [2,3,4,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,8,5] 30 (by decide +kernel))
  node35
  node38
  (invalid_upper a [2,3,4,8,8] 30 (by decide +kernel)))

theorem node40 : UpperPrefix a [2,3,4] 30 :=
  branch_upper a [2,3,4] 30 (by decide) (fin9_cases _
  node8
  node9
  (invalid_upper a [2,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,4] 30 (by decide +kernel))
  node10
  node21
  node32
  node39)

def cert41 : Leaf := ⟨⟨0,433,408,386,392,408,280,88,208⟩,[(0,1)],[(2,0,0),(0,3,1),(1,4,3)],⟨7,14,37,25,50,496,464,464,472⟩,⟨7,14,37,25,50,96,192,384,264⟩,[⟨5,1323666153021274154075139,⟨7,463,5,473,475,64,192,384,456⟩⟩,⟨6,1210106412364828375023167,⟨31,31,63,31,63,63,128,384,267⟩⟩]⟩
theorem node41 : UpperPrefix a [2,3,5,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,0,1] 30 cert41 (by decide +kernel)

def cert42 : Leaf := ⟨⟨0,305,282,290,0,410,314,58,178⟩,[(0,1),(4,5)],[(2,0,0),(0,3,1),(6,4,4)],⟨7,14,37,25,112,498,466,402,410⟩,⟨7,14,37,25,112,96,192,384,264⟩,[⟨7,1208926973665340290006591,⟨15,15,63,31,127,127,64,256,267⟩⟩]⟩
theorem node42 : UpperPrefix a [2,3,5,0,6] 30 :=
  Boolean.leaf_sound a [2,3,5,0,6] 30 cert42 (by decide +kernel)

def cert43 : Leaf := ⟨⟨0,241,218,224,72,152,312,120,240⟩,[(0,1)],[(2,0,0),(0,3,1),(1,5,2)],⟨7,14,37,25,176,98,464,464,344⟩,⟨7,14,37,25,176,98,192,384,264⟩,[⟨8,1181747925435433417855,⟨7,15,47,31,191,127,255,128,11⟩⟩]⟩
theorem node43 : UpperPrefix a [2,3,5,0,7,1] 30 :=
  Boolean.leaf_sound a [2,3,5,0,7,1] 30 cert43 (by decide +kernel)

def cert44 : Leaf := ⟨⟨0,113,90,98,74,138,298,106,98⟩,[(0,1)],[(2,0,0),(0,3,1),(7,4,5)],⟨7,14,37,25,176,112,450,450,330⟩,⟨7,14,37,25,176,112,192,384,264⟩,[⟨8,1181747925435433417855,⟨7,15,47,31,191,127,255,128,11⟩⟩,⟨4,1219580022407797557691395,⟨455,463,229,201,160,96,192,384,264⟩⟩]⟩
theorem node44 : UpperPrefix a [2,3,5,0,7,4] 30 :=
  Boolean.leaf_sound a [2,3,5,0,7,4] 30 cert44 (by decide +kernel)

def cert45 : Leaf := ⟨⟨0,49,26,34,330,154,58,122,242⟩,[(0,1)],[(2,0,0),(0,3,1),(8,5,4)],⟨7,14,37,25,176,352,210,466,346⟩,⟨7,14,37,25,176,352,192,384,264⟩,[⟨6,1210106412362349230961691,⟨7,15,37,31,191,288,128,384,267⟩⟩,⟨7,1208926973663136426505243,⟨7,15,37,31,63,352,64,256,267⟩⟩]⟩
theorem node45 : UpperPrefix a [2,3,5,0,7,8] 30 :=
  Boolean.leaf_sound a [2,3,5,0,7,8] 30 cert45 (by decide +kernel)

theorem node46 : UpperPrefix a [2,3,5,0,7] 30 :=
  branch_upper a [2,3,5,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,0,7,0] 30 (by decide +kernel))
  node43
  (invalid_upper a [2,3,5,0,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,7,3] 30 (by decide +kernel))
  node44
  (invalid_upper a [2,3,5,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,7,7] 30 (by decide +kernel))
  node45)

def cert47 : Leaf := ⟨⟨0,497,466,480,200,400,272,80,208⟩,[(0,1)],[(2,0,0),(0,3,1),(1,5,2)],⟨7,14,37,25,304,98,208,464,472⟩,⟨7,14,37,25,304,98,192,384,264⟩,[⟨3,1210255571652373273904163,⟨39,103,37,213,501,103,192,384,320⟩⟩,⟨5,1248108289295357683172355,⟨7,463,5,473,464,67,192,384,456⟩⟩]⟩
theorem node47 : UpperPrefix a [2,3,5,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,5,0,8,1] 30 cert47 (by decide +kernel)

def cert48 : Leaf := ⟨⟨0,305,282,290,202,394,266,74,194⟩,[(0,1)],[(2,0,0),(0,3,1)],⟨7,14,37,25,304,112,194,450,458⟩,⟨7,14,37,25,304,112,192,384,264⟩,[⟨4,1219580022407797557691395,⟨455,463,229,201,288,96,192,384,264⟩⟩,⟨5,1219580021282997162476547,⟨455,463,197,217,272,80,192,384,264⟩⟩,⟨6,1210106412362353534336063,⟨7,15,47,31,319,63,128,384,267⟩⟩,⟨7,1208926973663140729879615,⟨7,15,47,31,319,127,64,256,267⟩⟩]⟩
theorem node48 : UpperPrefix a [2,3,5,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,0,8,4] 30 cert48 (by decide +kernel)

def cert49 : Leaf := ⟨⟨0,305,282,290,74,0,314,122,114⟩,[(0,1),(5,6)],[(2,0,0),(0,3,1),(7,5,5)],⟨7,14,37,25,304,224,210,466,346⟩,⟨7,14,37,25,304,224,192,384,264⟩,[⟨6,1210106412362349230961691,⟨7,15,37,31,319,160,128,384,267⟩⟩]⟩
theorem node49 : UpperPrefix a [2,3,5,0,8,7] 30 :=
  Boolean.leaf_sound a [2,3,5,0,8,7] 30 cert49 (by decide +kernel)

theorem node50 : UpperPrefix a [2,3,5,0,8] 30 :=
  branch_upper a [2,3,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,0,8,0] 30 (by decide +kernel))
  node47
  (invalid_upper a [2,3,5,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,8,3] 30 (by decide +kernel))
  node48
  (invalid_upper a [2,3,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,8,6] 30 (by decide +kernel))
  node49
  (invalid_upper a [2,3,5,0,8,8] 30 (by decide +kernel)))

theorem node51 : UpperPrefix a [2,3,5,0] 30 :=
  branch_upper a [2,3,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,0,0] 30 (by decide +kernel))
  node41
  (invalid_upper a [2,3,5,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,0,5] 30 (by decide +kernel))
  node42
  node46
  node50)

def cert52 : Leaf := ⟨⟨0,497,0,481,0,408,312,120,240⟩,[(0,1),(2,4),(4,2)],[(2,0,0)],⟨7,14,37,26,49,496,464,464,472⟩,⟨7,14,37,26,49,96,192,384,264⟩,[⟨0,1247960428519766738600960,⟨6,494,36,506,48,96,192,384,488⟩⟩,⟨1,1257432885750708839907329,⟨501,508,245,508,245,96,192,384,488⟩⟩]⟩
theorem node52 : UpperPrefix a [2,3,5,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,1,0] 30 cert52 (by decide +kernel)

def cert53 : Leaf := ⟨⟨0,305,282,289,0,411,283,27,147⟩,[(0,1),(4,5)],[(2,0,0),(6,4,4)],⟨7,14,37,26,112,497,465,401,409⟩,⟨7,14,37,26,112,96,192,384,264⟩,[⟨5,1247960427112391855047683,⟨7,463,5,475,80,64,192,384,456⟩⟩,⟨7,1208926973665340290006591,⟨15,15,63,31,127,127,64,256,267⟩⟩]⟩
theorem node53 : UpperPrefix a [2,3,5,1,6] 30 :=
  Boolean.leaf_sound a [2,3,5,1,6] 30 cert53 (by decide +kernel)

def cert54 : Leaf := ⟨⟨0,496,0,480,328,408,312,120,240⟩,[(0,1),(2,5)],[(2,0,0),(0,5,2)],⟨7,14,37,26,176,97,464,464,344⟩,⟨7,14,37,26,176,97,192,384,264⟩,[⟨1,1257432885541939073777665,⟨501,508,245,472,180,245,192,384,456⟩⟩]⟩
theorem node54 : UpperPrefix a [2,3,5,1,7,0] 30 :=
  Boolean.leaf_sound a [2,3,5,1,7,0] 30 cert54 (by decide +kernel)

def cert55 : Leaf := ⟨⟨0,113,90,97,75,139,267,75,67⟩,[(0,1)],[(2,0,0),(7,4,5)],⟨7,14,37,26,176,112,449,449,329⟩,⟨7,14,37,26,176,112,192,384,264⟩,[⟨8,1181747925435433417855,⟨7,15,47,31,191,127,255,128,11⟩⟩,⟨4,1257432885362237633463299,⟨455,463,229,459,160,96,192,384,456⟩⟩,⟨5,1257432884237437238248451,⟨455,463,197,475,144,80,192,384,456⟩⟩]⟩
theorem node55 : UpperPrefix a [2,3,5,1,7,4] 30 :=
  Boolean.leaf_sound a [2,3,5,1,7,4] 30 cert55 (by decide +kernel)

def cert56 : Leaf := ⟨⟨0,240,216,224,328,152,56,120,240⟩,[(0,1)],[(2,0,0),(8,5,4)],⟨7,14,37,26,176,352,193,464,344⟩,⟨7,14,37,26,176,352,193,384,264⟩,[⟨0,1664340193613556975930880,⟨30,30,446,26,432,504,506,384,264⟩⟩,⟨1,1219875206456054436331521,⟨501,508,245,440,176,500,245,384,280⟩⟩]⟩
theorem node56 : UpperPrefix a [2,3,5,1,7,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,1,7,8,0] 30 cert56 (by decide +kernel)

def cert57 : Leaf := ⟨⟨0,49,26,33,331,27,0,123,115⟩,[(0,1),(6,4)],[(2,0,0),(7,4,6),(8,5,4)],⟨7,14,37,26,176,352,208,449,329⟩,⟨7,14,37,26,176,352,208,384,264⟩,[⟨6,1210106412362357829334143,⟨7,15,39,31,191,303,159,384,267⟩⟩]⟩
theorem node57 : UpperPrefix a [2,3,5,1,7,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,1,7,8,4] 30 cert57 (by decide +kernel)

theorem node58 : UpperPrefix a [2,3,5,1,7,8] 30 :=
  branch_upper a [2,3,5,1,7,8] 30 (by decide) (fin9_cases _
  node56
  (invalid_upper a [2,3,5,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,8,3] 30 (by decide +kernel))
  node57
  (invalid_upper a [2,3,5,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,8,8] 30 (by decide +kernel)))

theorem node59 : UpperPrefix a [2,3,5,1,7] 30 :=
  branch_upper a [2,3,5,1,7] 30 (by decide) (fin9_cases _
  node54
  (invalid_upper a [2,3,5,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,3] 30 (by decide +kernel))
  node55
  (invalid_upper a [2,3,5,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,7,7] 30 (by decide +kernel))
  node58)

def cert60 : Leaf := ⟨⟨0,496,0,480,200,408,312,120,240⟩,[(0,1),(2,5)],[(2,0,0),(0,5,2)],⟨7,14,37,26,304,97,208,464,472⟩,⟨7,14,37,26,304,97,192,384,264⟩,[⟨1,1257581396240777342091265,⟨501,508,245,472,500,245,192,384,456⟩⟩]⟩
theorem node60 : UpperPrefix a [2,3,5,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,1,8,0] 30 cert60 (by decide +kernel)

def cert61 : Leaf := ⟨⟨0,305,274,289,195,387,259,67,195⟩,[(0,1)],[(2,0,0)],⟨7,14,37,26,304,112,193,449,457⟩,⟨7,14,37,26,304,112,192,384,264⟩,[⟨3,1212473376563240859862027,⟨7,7,37,55,500,112,240,500,501⟩⟩,⟨4,1257432957419831671391235,⟨455,463,229,459,288,96,192,384,456⟩⟩,⟨5,1257432956295031276176387,⟨455,463,197,475,272,80,192,384,456⟩⟩,⟨6,1210106412362353534336063,⟨7,15,47,31,319,63,128,384,267⟩⟩,⟨7,1208926973663140729879615,⟨7,15,47,31,319,127,64,256,267⟩⟩]⟩
theorem node61 : UpperPrefix a [2,3,5,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,1,8,4] 30 cert61 (by decide +kernel)

def cert62 : Leaf := ⟨⟨0,369,338,353,67,0,275,83,83⟩,[(0,1),(5,6)],[(2,0,0),(7,5,5)],⟨7,14,37,26,304,224,209,465,345⟩,⟨7,14,37,26,304,224,192,384,264⟩,[⟨3,1212473376563240859862027,⟨7,7,37,55,500,240,240,500,501⟩⟩,⟨5,1247960427112391855047683,⟨7,463,5,475,272,192,192,384,456⟩⟩]⟩
theorem node62 : UpperPrefix a [2,3,5,1,8,7] 30 :=
  Boolean.leaf_sound a [2,3,5,1,8,7] 30 cert62 (by decide +kernel)

theorem node63 : UpperPrefix a [2,3,5,1,8] 30 :=
  branch_upper a [2,3,5,1,8] 30 (by decide) (fin9_cases _
  node60
  (invalid_upper a [2,3,5,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,8,3] 30 (by decide +kernel))
  node61
  (invalid_upper a [2,3,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,1,8,6] 30 (by decide +kernel))
  node62
  (invalid_upper a [2,3,5,1,8,8] 30 (by decide +kernel)))

#print axioms node63
end Delivery.FiniteExclusion.Sharp3x6
