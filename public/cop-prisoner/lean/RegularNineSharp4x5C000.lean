import RegularNineSharp4x5Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert0 : Local := ⟨⟨0,0,497,480,456,408,312,120,232⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(0,1,2),(1,2,0),(1,2,1)]⟩
theorem node0 : UpperPrefix a [2,0,1,4] 30 :=
  local_sound a [2,0,1,4] 30 cert0 (by decide +kernel)

theorem node1 : UpperPrefix a [2,0,1] 30 :=
  branch_upper a [2,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,0,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,0,1,3] 30 (by decide +kernel))
  node0
  (PrefixConjugacy.upper aut4 [2,0,1,5] [2,0,1,4] 30 (by decide +kernel) node0)
  (PrefixConjugacy.upper aut3 [2,0,1,6] [2,0,1,4] 30 (by decide +kernel) node0)
  (PrefixConjugacy.upper aut2 [2,0,1,7] [2,0,1,4] 30 (by decide +kernel) node0)
  (PrefixConjugacy.upper aut1 [2,0,1,8] [2,0,1,4] 30 (by decide +kernel) node0))

def cert2 : Local := ⟨⟨0,0,480,0,456,408,312,120,232⟩,[(0,1),(1,0),(3,0)],[(2,0,0),(2,0,1),(0,1,3),(1,3,3)]⟩
theorem node2 : UpperPrefix a [2,0,4,1] 30 :=
  local_sound a [2,0,4,1] 30 cert2 (by decide +kernel)

def cert3 : Leaf := ⟨⟨0,0,480,464,456,408,280,88,200⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(5,3,2)],⟨7,7,28,41,50,488,456,456,472⟩,⟨7,7,28,41,50,96,192,384,272⟩,[⟨0,1266886860137930425369600,⟨502,502,508,508,50,96,192,384,272⟩⟩,⟨1,1304767447638498933211137,⟨493,493,508,233,508,96,192,384,500⟩⟩]⟩
theorem node3 : UpperPrefix a [2,0,4,5,1] 30 :=
  Boolean.leaf_sound a [2,0,4,5,1] 30 cert3 (by decide +kernel)

def cert4 : Local := ⟨⟨0,0,0,466,0,403,275,83,195⟩,[(0,1),(1,0),(2,4),(4,3)],[(2,0,0),(2,0,1),(5,3,2),(5,3,4),(3,4,2)]⟩
theorem node4 : UpperPrefix a [2,0,4,5,3] 30 :=
  local_sound a [2,0,4,5,3] 30 cert4 (by decide +kernel)

def cert5 : Local := ⟨⟨0,0,419,402,0,411,283,27,139⟩,[(0,1),(1,0),(4,5)],[(2,0,0),(2,0,1),(5,3,2),(6,4,4)]⟩
theorem node5 : UpperPrefix a [2,0,4,5,6] 30 :=
  local_sound a [2,0,4,5,6] 30 cert5 (by decide +kernel)

def cert6 : Leaf := ⟨⟨0,0,480,466,328,408,280,88,200⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(5,3,2),(1,5,3)],⟨7,7,28,41,176,98,456,456,344⟩,⟨7,7,28,41,176,98,192,384,272⟩,[⟨0,1266886859821820832384000,⟨502,502,476,508,176,114,192,384,272⟩⟩]⟩
theorem node6 : UpperPrefix a [2,0,4,5,7,1] 30 :=
  Boolean.leaf_sound a [2,0,4,5,7,1] 30 cert6 (by decide +kernel)

def cert7 : Leaf := ⟨⟨0,0,227,210,67,147,275,83,195⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(5,3,2)],⟨7,7,28,41,176,104,450,450,338⟩,⟨7,7,28,41,176,104,192,384,272⟩,[⟨3,1266914583877565597879815,⟨455,455,471,499,176,496,192,384,272⟩⟩,⟨8,1181747925435500724223,⟨7,7,31,47,191,127,255,135,31⟩⟩]⟩
theorem node7 : UpperPrefix a [2,0,4,5,7,3] 30 :=
  Boolean.leaf_sound a [2,0,4,5,7,3] 30 cert7 (by decide +kernel)

def cert8 : Leaf := ⟨⟨0,0,35,18,331,155,27,91,203⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(5,3,2),(8,5,4)],⟨7,7,28,41,176,352,202,458,346⟩,⟨7,7,28,41,176,352,192,384,272⟩,[⟨6,1210106412362353593249719,⟨7,7,31,43,191,303,131,391,287⟩⟩,⟨7,1208926973663140788793271,⟨7,7,31,43,63,367,67,263,287⟩⟩]⟩
theorem node8 : UpperPrefix a [2,0,4,5,7,8] 30 :=
  Boolean.leaf_sound a [2,0,4,5,7,8] 30 cert8 (by decide +kernel)

theorem node9 : UpperPrefix a [2,0,4,5,7] 30 :=
  branch_upper a [2,0,4,5,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,5,7,0] 30 (by decide +kernel))
  node6
  (invalid_upper a [2,0,4,5,7,2] 30 (by decide +kernel))
  node7
  (invalid_upper a [2,0,4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,5,7,7] 30 (by decide +kernel))
  node8)

def cert10 : Leaf := ⟨⟨0,0,35,18,203,155,27,91,203⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(5,3,2)],⟨7,7,28,41,304,234,202,458,474⟩,⟨7,7,28,41,304,96,192,384,272⟩,[⟨8,1184058267659154960279,⟨7,7,31,43,63,104,235,239,31⟩⟩,⟨6,1210106412362349298266007,⟨7,7,31,43,319,32,131,391,287⟩⟩,⟨7,1208926973663136493809559,⟨7,7,31,43,319,96,67,263,287⟩⟩]⟩
theorem node10 : UpperPrefix a [2,0,4,5,8] 30 :=
  Boolean.leaf_sound a [2,0,4,5,8] 30 cert10 (by decide +kernel)

theorem node11 : UpperPrefix a [2,0,4,5] 30 :=
  branch_upper a [2,0,4,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,5,0] 30 (by decide +kernel))
  node3
  (invalid_upper a [2,0,4,5,2] 30 (by decide +kernel))
  node4
  (invalid_upper a [2,0,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,5,5] 30 (by decide +kernel))
  node5
  node9
  node10)

def cert12 : Leaf := ⟨⟨0,0,480,432,456,408,312,120,232⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1)],⟨7,7,28,73,50,488,488,424,440⟩,⟨7,7,28,73,50,96,192,384,272⟩,[⟨0,1266886860137930425369600,⟨502,502,508,508,50,96,192,384,272⟩⟩,⟨1,1304767447638498933211137,⟨493,493,508,233,508,96,192,384,500⟩⟩]⟩
theorem node12 : UpperPrefix a [2,0,4,6,1] 30 :=
  Boolean.leaf_sound a [2,0,4,6,1] 30 cert12 (by decide +kernel)

def cert13 : Local := ⟨⟨0,0,0,434,451,403,307,51,163⟩,[(0,1),(1,0),(2,4)],[(2,0,0),(2,0,1),(6,3,4),(3,4,2)]⟩
theorem node13 : UpperPrefix a [2,0,4,6,3] 30 :=
  local_sound a [2,0,4,6,3] 30 cert13 (by decide +kernel)

def cert14 : Leaf := ⟨⟨0,0,99,34,75,9,315,123,107⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1)],⟨7,7,28,73,176,98,488,424,312⟩,⟨7,7,28,73,176,98,192,384,272⟩,[⟨7,1303374303602006455103255,⟨263,263,319,107,319,107,64,259,279⟩⟩,⟨8,1181748206908264873855,⟨7,7,63,127,191,127,255,131,23⟩⟩,⟨4,1210107565564231446171143,⟨7,7,47,107,168,107,192,384,256⟩⟩]⟩
theorem node14 : UpperPrefix a [2,0,4,6,7,1] 30 :=
  Boolean.leaf_sound a [2,0,4,6,7,1] 30 cert14 (by decide +kernel)

def cert15 : Local := ⟨⟨0,0,419,434,267,0,315,59,171⟩,[(0,1),(1,0),(5,3)],[(2,0,0),(2,0,1),(6,3,5)]⟩
theorem node15 : UpperPrefix a [2,0,4,6,7,3] 30 :=
  local_sound a [2,0,4,6,7,3] 30 cert15 (by decide +kernel)

def cert16 : Local := ⟨⟨0,0,225,178,329,153,57,121,233⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(8,5,4),(1,6,3)]⟩
theorem node16 : UpperPrefix a [2,0,4,6,7,8,1] 30 :=
  local_sound a [2,0,4,6,7,8,1] 30 cert16 (by decide +kernel)

def cert17 : Leaf := ⟨⟨0,0,195,146,323,147,19,115,227⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(8,5,4)],⟨7,7,28,73,176,352,200,418,306⟩,⟨7,7,28,73,176,352,200,384,272⟩,[⟨3,1266886646081226082881031,⟨407,407,439,499,176,368,496,384,272⟩⟩,⟨5,1210110158231404325072823,⟨15,15,95,75,223,335,203,463,351⟩⟩]⟩
theorem node17 : UpperPrefix a [2,0,4,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,0,4,6,7,8,3] 30 cert17 (by decide +kernel)

def cert18 : Local := ⟨⟨0,0,227,178,0,155,0,123,235⟩,[(0,1),(1,0),(4,6),(6,4)],[(2,0,0),(2,0,1),(8,5,4),(8,5,6)]⟩
theorem node18 : UpperPrefix a [2,0,4,6,7,8,5] 30 :=
  local_sound a [2,0,4,6,7,8,5] 30 cert18 (by decide +kernel)

theorem node19 : UpperPrefix a [2,0,4,6,7,8] 30 :=
  branch_upper a [2,0,4,6,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,6,7,8,0] 30 (by decide +kernel))
  node16
  (invalid_upper a [2,0,4,6,7,8,2] 30 (by decide +kernel))
  node17
  (invalid_upper a [2,0,4,6,7,8,4] 30 (by decide +kernel))
  node18
  (invalid_upper a [2,0,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,7,8,8] 30 (by decide +kernel)))

theorem node20 : UpperPrefix a [2,0,4,6,7] 30 :=
  branch_upper a [2,0,4,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,6,7,0] 30 (by decide +kernel))
  node14
  (invalid_upper a [2,0,4,6,7,2] 30 (by decide +kernel))
  node15
  (invalid_upper a [2,0,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,7,7] 30 (by decide +kernel))
  node19)

def cert21 : Leaf := ⟨⟨0,0,99,34,203,9,43,107,235⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1)],⟨7,7,28,73,304,98,232,424,440⟩,⟨7,7,28,73,304,98,192,384,272⟩,[⟨4,1210255500051082856369671,⟨111,111,239,107,488,107,192,384,448⟩⟩,⟨8,1184056297327808360215,⟨7,7,63,107,63,107,232,235,23⟩⟩,⟨7,1208926973944613550829335,⟨7,7,63,107,319,107,64,259,279⟩⟩]⟩
theorem node21 : UpperPrefix a [2,0,4,6,8,1] 30 :=
  Boolean.leaf_sound a [2,0,4,6,8,1] 30 cert21 (by decide +kernel)

def cert22 : Local := ⟨⟨0,0,419,434,139,0,315,59,171⟩,[(0,1),(1,0),(5,3)],[(2,0,0),(2,0,1),(6,3,5)]⟩
theorem node22 : UpperPrefix a [2,0,4,6,8,3] 30 :=
  local_sound a [2,0,4,6,8,3] 30 cert22 (by decide +kernel)

def cert23 : Local := ⟨⟨0,0,355,306,75,0,315,123,107⟩,[(0,1),(1,0),(5,6)],[(2,0,0),(2,0,1),(7,5,5)]⟩
theorem node23 : UpperPrefix a [2,0,4,6,8,7] 30 :=
  local_sound a [2,0,4,6,8,7] 30 cert23 (by decide +kernel)

theorem node24 : UpperPrefix a [2,0,4,6,8] 30 :=
  branch_upper a [2,0,4,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,6,8,0] 30 (by decide +kernel))
  node21
  (invalid_upper a [2,0,4,6,8,2] 30 (by decide +kernel))
  node22
  (invalid_upper a [2,0,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,8,6] 30 (by decide +kernel))
  node23
  (invalid_upper a [2,0,4,6,8,8] 30 (by decide +kernel)))

theorem node25 : UpperPrefix a [2,0,4,6] 30 :=
  branch_upper a [2,0,4,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,6,0] 30 (by decide +kernel))
  node12
  (invalid_upper a [2,0,4,6,2] 30 (by decide +kernel))
  node13
  (invalid_upper a [2,0,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,6,6] 30 (by decide +kernel))
  node20
  node24)

def cert26 : Leaf := ⟨⟨0,0,480,368,456,408,312,120,232⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1)],⟨7,7,28,137,50,360,488,488,376⟩,⟨7,7,28,137,50,96,192,384,272⟩,[⟨0,1266886860137930425369600,⟨502,502,508,508,50,96,192,384,272⟩⟩,⟨1,1304767447638498933211137,⟨493,493,508,233,508,96,192,384,500⟩⟩]⟩
theorem node26 : UpperPrefix a [2,0,4,7,1] 30 :=
  Boolean.leaf_sound a [2,0,4,7,1] 30 cert26 (by decide +kernel)

def cert27 : Local := ⟨⟨0,0,0,370,451,403,307,115,227⟩,[(0,1),(1,0),(2,4)],[(2,0,0),(2,0,1),(3,4,2)]⟩
theorem node27 : UpperPrefix a [2,0,4,7,3] 30 :=
  local_sound a [2,0,4,7,3] 30 cert27 (by decide +kernel)

def cert28 : Local := ⟨⟨0,0,419,306,0,409,315,59,171⟩,[(0,1),(1,0),(4,5)],[(2,0,0),(2,0,1),(6,4,4)]⟩
theorem node28 : UpperPrefix a [2,0,4,7,6,1] 30 :=
  local_sound a [2,0,4,7,6,1] 30 cert28 (by decide +kernel)

def cert29 : Local := ⟨⟨0,0,291,306,0,403,315,59,43⟩,[(0,1),(1,0),(4,5)],[(2,0,0),(2,0,1),(7,3,5),(6,4,4)]⟩
theorem node29 : UpperPrefix a [2,0,4,7,6,3] 30 :=
  local_sound a [2,0,4,7,6,3] 30 cert29 (by decide +kernel)

def cert30 : Local := ⟨⟨0,0,419,306,0,155,315,59,171⟩,[(0,1),(1,0),(4,5)],[(2,0,0),(2,0,1),(6,4,4)]⟩
theorem node30 : UpperPrefix a [2,0,4,7,6,8] 30 :=
  local_sound a [2,0,4,7,6,8] 30 cert30 (by decide +kernel)

theorem node31 : UpperPrefix a [2,0,4,7,6] 30 :=
  branch_upper a [2,0,4,7,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,7,6,0] 30 (by decide +kernel))
  node28
  (invalid_upper a [2,0,4,7,6,2] 30 (by decide +kernel))
  node29
  (invalid_upper a [2,0,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,6,7] 30 (by decide +kernel))
  node30)

def cert32 : Local := ⟨⟨0,0,355,370,75,281,0,123,107⟩,[(0,1),(1,0),(6,3)],[(2,0,0),(2,0,1),(7,3,6)]⟩
theorem node32 : UpperPrefix a [2,0,4,7,8,1,3] 30 :=
  local_sound a [2,0,4,7,8,1,3] 30 cert32 (by decide +kernel)

def cert33 : Leaf := ⟨⟨0,0,480,368,200,408,280,120,232⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1)],⟨7,7,28,137,304,98,224,456,344⟩,⟨7,7,28,137,304,98,224,384,272⟩,[⟨0,1266886841807422322902016,⟨502,502,476,508,304,114,224,384,272⟩⟩,⟨1,1380445664758211621683201,⟨397,397,476,137,500,508,500,384,336⟩⟩]⟩
theorem node33 : UpperPrefix a [2,0,4,7,8,1,5] 30 :=
  Boolean.leaf_sound a [2,0,4,7,8,1,5] 30 cert33 (by decide +kernel)

theorem node34 : UpperPrefix a [2,0,4,7,8,1] 30 :=
  branch_upper a [2,0,4,7,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,7,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,1,2] 30 (by decide +kernel))
  node32
  (invalid_upper a [2,0,4,7,8,1,4] 30 (by decide +kernel))
  node33
  (invalid_upper a [2,0,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,1,8] 30 (by decide +kernel)))

def cert35 : Leaf := ⟨⟨0,0,352,370,72,403,313,120,104⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(7,3,5)],⟨7,7,28,137,304,104,194,480,368⟩,⟨7,7,28,137,304,104,194,384,272⟩,[⟨0,1361518440643058717426688,⟨6,6,28,136,436,508,194,384,272⟩⟩,⟨1,1361518440643058717425665,⟨5,5,28,137,436,508,192,384,272⟩⟩]⟩
theorem node35 : UpperPrefix a [2,0,4,7,8,3,1] 30 :=
  Boolean.leaf_sound a [2,0,4,7,8,3,1] 30 cert35 (by decide +kernel)

def cert36 : Leaf := ⟨⟨0,0,354,370,74,402,282,122,106⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1),(7,3,5)],⟨7,7,28,137,304,104,224,450,338⟩,⟨7,7,28,137,304,104,224,384,272⟩,[⟨0,1224302533429923180184576,⟨502,502,124,508,308,124,228,384,272⟩⟩]⟩
theorem node36 : UpperPrefix a [2,0,4,7,8,3,5] 30 :=
  Boolean.leaf_sound a [2,0,4,7,8,3,5] 30 cert36 (by decide +kernel)

theorem node37 : UpperPrefix a [2,0,4,7,8,3] 30 :=
  branch_upper a [2,0,4,7,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,7,8,3,0] 30 (by decide +kernel))
  node35
  (invalid_upper a [2,0,4,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,3,4] 30 (by decide +kernel))
  node36
  (invalid_upper a [2,0,4,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,3,8] 30 (by decide +kernel)))

theorem node38 : UpperPrefix a [2,0,4,7,8] 30 :=
  branch_upper a [2,0,4,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,7,8,0] 30 (by decide +kernel))
  node34
  (invalid_upper a [2,0,4,7,8,2] 30 (by decide +kernel))
  node37
  (invalid_upper a [2,0,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,8,8] 30 (by decide +kernel)))

theorem node39 : UpperPrefix a [2,0,4,7] 30 :=
  branch_upper a [2,0,4,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,7,0] 30 (by decide +kernel))
  node26
  (invalid_upper a [2,0,4,7,2] 30 (by decide +kernel))
  node27
  (invalid_upper a [2,0,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,7,5] 30 (by decide +kernel))
  node31
  (invalid_upper a [2,0,4,7,7] 30 (by decide +kernel))
  node38)

def cert40 : Leaf := ⟨⟨0,0,480,240,456,408,312,120,232⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1)],⟨7,7,28,265,50,232,232,488,504⟩,⟨7,7,28,265,50,96,192,384,272⟩,[⟨0,1266886860137930425369600,⟨502,502,508,508,50,96,192,384,272⟩⟩,⟨1,1304841379011456823984129,⟨493,493,508,489,508,96,192,384,500⟩⟩]⟩
theorem node40 : UpperPrefix a [2,0,4,8,1] 30 :=
  Boolean.leaf_sound a [2,0,4,8,1] 30 cert40 (by decide +kernel)

def cert41 : Local := ⟨⟨0,0,0,242,451,403,307,115,227⟩,[(0,1),(1,0),(2,4)],[(2,0,0),(2,0,1),(3,4,2)]⟩
theorem node41 : UpperPrefix a [2,0,4,8,3] 30 :=
  local_sound a [2,0,4,8,3] 30 cert41 (by decide +kernel)

def cert42 : Leaf := ⟨⟨0,0,419,178,0,395,299,43,171⟩,[(0,1),(1,0),(4,5)],[(2,0,0),(2,0,1),(6,4,4)],⟨7,7,28,265,112,234,234,426,442⟩,⟨7,7,28,265,112,96,192,384,272⟩,[⟨4,1210181568854041591549447,⟨103,103,239,491,96,96,192,384,256⟩⟩]⟩
theorem node42 : UpperPrefix a [2,0,4,8,6] 30 :=
  Boolean.leaf_sound a [2,0,4,8,6] 30 cert42 (by decide +kernel)

def cert43 : Leaf := ⟨⟨0,0,259,18,331,267,299,107,235⟩,[(0,1),(1,0)],[(2,0,0),(2,0,1)],⟨7,7,28,265,176,106,234,490,378⟩,⟨7,7,28,265,176,96,192,384,272⟩,[⟨4,1210181568854041591549447,⟨103,103,239,491,160,96,192,384,256⟩⟩,⟨7,1208926975914985699622815,⟨7,7,31,271,63,96,107,271,287⟩⟩,⟨5,1210107564158003390398367,⟨7,7,31,271,159,64,203,399,287⟩⟩,⟨6,1210106412362398690394015,⟨7,7,31,271,191,32,139,399,287⟩⟩]⟩
theorem node43 : UpperPrefix a [2,0,4,8,7] 30 :=
  Boolean.leaf_sound a [2,0,4,8,7] 30 cert43 (by decide +kernel)

theorem node44 : UpperPrefix a [2,0,4,8] 30 :=
  branch_upper a [2,0,4,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,8,0] 30 (by decide +kernel))
  node40
  (invalid_upper a [2,0,4,8,2] 30 (by decide +kernel))
  node41
  (invalid_upper a [2,0,4,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,8,5] 30 (by decide +kernel))
  node42
  node43
  (invalid_upper a [2,0,4,8,8] 30 (by decide +kernel)))

theorem node45 : UpperPrefix a [2,0,4] 30 :=
  branch_upper a [2,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,4,0] 30 (by decide +kernel))
  node2
  (invalid_upper a [2,0,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,0,4,4] 30 (by decide +kernel))
  node11
  node25
  node39
  node44)

theorem node46 : UpperPrefix a [2,0] 30 :=
  branch_upper a [2,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,0,0] 30 (by decide +kernel))
  node1
  (invalid_upper a [2,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,0,3] 30 (by decide +kernel))
  node45
  (PrefixConjugacy.upper aut4 [2,0,5] [2,0,4] 30 (by decide +kernel) node45)
  (PrefixConjugacy.upper aut3 [2,0,6] [2,0,4] 30 (by decide +kernel) node45)
  (PrefixConjugacy.upper aut2 [2,0,7] [2,0,4] 30 (by decide +kernel) node45)
  (PrefixConjugacy.upper aut1 [2,0,8] [2,0,4] 30 (by decide +kernel) node45))

def cert47 : Local := ⟨⟨0,0,0,498,450,402,306,114,226⟩,[(0,1),(1,2),(2,3)],[(2,0,0),(3,1,0),(3,1,1),(0,2,1),(0,2,2)]⟩
theorem node47 : UpperPrefix a [2,3,0] 30 :=
  local_sound a [2,3,0] 30 cert47 (by decide +kernel)

def cert48 : Local := ⟨⟨0,0,0,496,449,401,305,113,225⟩,[(0,1),(1,2),(2,1)],[(2,0,0),(3,1,0),(3,1,1),(1,2,0)]⟩
theorem node48 : UpperPrefix a [2,3,1] 30 :=
  local_sound a [2,3,1] 30 cert48 (by decide +kernel)

def cert49 : Local := ⟨⟨0,0,0,482,450,402,306,114,226⟩,[(0,1),(1,2),(2,3)],[(2,0,0),(3,1,0),(3,1,1),(0,2,1),(0,2,2)]⟩
theorem node49 : UpperPrefix a [2,3,0,4] 30 :=
  local_sound a [2,3,0,4] 30 cert49 (by decide +kernel)

def cert50 : Leaf := ⟨⟨0,0,291,274,451,403,275,83,195⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(5,3,2)],⟨7,14,28,41,499,483,451,451,467⟩,⟨7,14,28,41,48,96,192,384,272⟩,[⟨6,1210106412362349298199959,⟨7,15,31,41,63,32,129,391,287⟩⟩,⟨7,1208926973663136493743511,⟨7,15,31,41,63,96,65,263,287⟩⟩]⟩
theorem node50 : UpperPrefix a [2,3,4,5] 30 :=
  Boolean.leaf_sound a [2,3,4,5] 30 cert50 (by decide +kernel)

def cert51 : Leaf := ⟨⟨0,0,355,306,322,402,306,114,226⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(0,4,2)],⟨7,14,28,73,49,482,482,418,434⟩,⟨7,14,28,73,49,96,192,384,272⟩,[⟨7,1208926973665337605647671,⟨7,15,31,73,63,127,64,257,279⟩⟩]⟩
theorem node51 : UpperPrefix a [2,3,4,6,0] 30 :=
  Boolean.leaf_sound a [2,3,4,6,0] 30 cert51 (by decide +kernel)

def cert52 : Leaf := ⟨⟨0,0,99,50,65,403,307,115,227⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1)],⟨7,14,28,73,50,481,481,417,433⟩,⟨7,14,28,73,50,96,192,384,272⟩,[⟨7,1208926973665337605647671,⟨7,15,31,73,63,127,64,257,279⟩⟩,⟨8,1181745671425842244919,⟨7,15,31,73,63,127,192,129,23⟩⟩]⟩
theorem node52 : UpperPrefix a [2,3,4,6,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,1] 30 cert52 (by decide +kernel)

def cert53 : Local := ⟨⟨0,0,483,0,323,0,307,115,227⟩,[(0,1),(1,2),(3,5),(5,3)],[(2,0,0),(3,1,0),(3,1,1)]⟩
theorem node53 : UpperPrefix a [2,3,4,6,7,0] 30 :=
  local_sound a [2,3,4,6,7,0] 30 cert53 (by decide +kernel)

def cert54 : Leaf := ⟨⟨0,0,227,178,67,145,307,115,227⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1)],⟨7,14,28,73,176,98,481,417,305⟩,⟨7,14,28,73,176,98,192,384,272⟩,[⟨8,1181748206908264742271,⟨7,47,63,127,191,127,255,129,23⟩⟩]⟩
theorem node54 : UpperPrefix a [2,3,4,6,7,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,1] 30 cert54 (by decide +kernel)

def cert55 : Leaf := ⟨⟨0,0,99,50,323,147,51,115,99⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(8,5,4)],⟨7,14,28,73,176,352,227,419,307⟩,⟨7,14,28,73,176,352,192,384,272⟩,[⟨7,1284484837389052897406231,⟨7,15,287,73,319,361,64,257,279⟩⟩]⟩
theorem node55 : UpperPrefix a [2,3,4,6,7,8] 30 :=
  Boolean.leaf_sound a [2,3,4,6,7,8] 30 cert55 (by decide +kernel)

theorem node56 : UpperPrefix a [2,3,4,6,7] 30 :=
  branch_upper a [2,3,4,6,7] 30 (by decide) (fin9_cases _
  node53
  node54
  (invalid_upper a [2,3,4,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,7,7] 30 (by decide +kernel))
  node55)

def cert57 : Local := ⟨⟨0,0,483,0,195,0,307,115,227⟩,[(0,1),(1,2),(3,5),(5,3)],[(2,0,0),(3,1,0),(3,1,1)]⟩
theorem node57 : UpperPrefix a [2,3,4,6,8,0] 30 :=
  local_sound a [2,3,4,6,8,0] 30 cert57 (by decide +kernel)

def cert58 : Leaf := ⟨⟨0,0,451,402,131,401,307,51,163⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1)],⟨7,14,28,73,304,98,225,417,433⟩,⟨7,14,28,73,304,98,192,384,272⟩,[⟨6,1361517287721554102193159,⟨7,15,31,9,432,435,128,384,272⟩⟩,⟨5,1210107564157956078447895,⟨7,15,31,73,287,75,192,385,279⟩⟩]⟩
theorem node58 : UpperPrefix a [2,3,4,6,8,1] 30 :=
  Boolean.leaf_sound a [2,3,4,6,8,1] 30 cert58 (by decide +kernel)

def cert59 : Local := ⟨⟨0,0,355,306,67,0,307,115,99⟩,[(0,1),(1,2),(5,6)],[(2,0,0),(3,1,0),(3,1,1),(7,5,5)]⟩
theorem node59 : UpperPrefix a [2,3,4,6,8,7] 30 :=
  local_sound a [2,3,4,6,8,7] 30 cert59 (by decide +kernel)

theorem node60 : UpperPrefix a [2,3,4,6,8] 30 :=
  branch_upper a [2,3,4,6,8] 30 (by decide) (fin9_cases _
  node57
  node58
  (invalid_upper a [2,3,4,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,8,6] 30 (by decide +kernel))
  node59
  (invalid_upper a [2,3,4,6,8,8] 30 (by decide +kernel)))

theorem node61 : UpperPrefix a [2,3,4,6] 30 :=
  branch_upper a [2,3,4,6] 30 (by decide) (fin9_cases _
  node51
  node52
  (invalid_upper a [2,3,4,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,6,6] 30 (by decide +kernel))
  node56
  node60)

def cert62 : Local := ⟨⟨0,0,481,368,450,400,304,112,224⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(0,4,2),(1,5,4)]⟩
theorem node62 : UpperPrefix a [2,3,4,7,0,1] 30 :=
  local_sound a [2,3,4,7,0,1] 30 cert62 (by decide +kernel)

def cert63 : Local := ⟨⟨0,0,483,370,450,146,306,114,226⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(0,4,2)]⟩
theorem node63 : UpperPrefix a [2,3,4,7,0,8] 30 :=
  local_sound a [2,3,4,7,0,8] 30 cert63 (by decide +kernel)

#print axioms node63
end Delivery.FiniteExclusion.Sharp4x5
