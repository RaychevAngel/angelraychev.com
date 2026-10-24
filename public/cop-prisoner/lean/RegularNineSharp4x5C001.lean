import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
theorem node64 : UpperPrefix a [2,3,4,7,0] 30 :=
  branch_upper a [2,3,4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,7,0,0] 30 (by decide +kernel))
  node62
  (invalid_upper a [2,3,4,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,0,7] 30 (by decide +kernel))
  node63)

def cert65 : Leaf := ⟨⟨0,0,481,368,449,400,305,113,225⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1)],⟨7,14,28,137,50,97,480,480,368⟩,⟨7,14,28,137,50,97,192,384,272⟩,[⟨1,1304767447145921750499329,⟨493,492,508,233,508,233,192,384,468⟩⟩]⟩
theorem node65 : UpperPrefix a [2,3,4,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,4,7,1,0] 30 cert65 (by decide +kernel)

def cert66 : Local := ⟨⟨0,0,483,0,449,147,0,115,227⟩,[(0,1),(1,2),(3,6),(6,3)],[(2,0,0),(3,1,0),(3,1,1)]⟩
theorem node66 : UpperPrefix a [2,3,4,7,1,8,0] 30 :=
  local_sound a [2,3,4,7,1,8,0] 30 cert66 (by decide +kernel)

def cert67 : Local := ⟨⟨0,0,227,114,193,147,275,115,227⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(8,5,6)]⟩
theorem node67 : UpperPrefix a [2,3,4,7,1,8,5] 30 :=
  local_sound a [2,3,4,7,1,8,5] 30 cert67 (by decide +kernel)

theorem node68 : UpperPrefix a [2,3,4,7,1,8] 30 :=
  branch_upper a [2,3,4,7,1,8] 30 (by decide) (fin9_cases _
  node66
  (invalid_upper a [2,3,4,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,8,4] 30 (by decide +kernel))
  node67
  (invalid_upper a [2,3,4,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,8,8] 30 (by decide +kernel)))

theorem node69 : UpperPrefix a [2,3,4,7,1] 30 :=
  branch_upper a [2,3,4,7,1] 30 (by decide) (fin9_cases _
  node65
  (invalid_upper a [2,3,4,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,1,7] 30 (by decide +kernel))
  node68)

def cert70 : Local := ⟨⟨0,0,419,306,0,403,307,51,163⟩,[(0,1),(1,2),(4,5)],[(2,0,0),(3,1,0),(3,1,1),(6,4,4)]⟩
theorem node70 : UpperPrefix a [2,3,4,7,6] 30 :=
  local_sound a [2,3,4,7,6] 30 cert70 (by decide +kernel)

def cert71 : Local := ⟨⟨0,0,481,368,193,402,305,113,225⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(1,6,5)]⟩
theorem node71 : UpperPrefix a [2,3,4,7,8,0,1] 30 :=
  local_sound a [2,3,4,7,8,0,1] 30 cert71 (by decide +kernel)

def cert72 : Leaf := ⟨⟨0,0,483,370,195,384,257,115,227⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1)],⟨7,14,28,137,304,97,224,450,338⟩,⟨7,14,28,137,304,97,224,384,272⟩,[⟨1,1210107709680514738683905,⟨5,108,124,233,304,97,224,384,272⟩⟩,⟨4,1210107709890521459592199,⟨39,111,111,233,288,97,224,384,256⟩⟩]⟩
theorem node72 : UpperPrefix a [2,3,4,7,8,0,5] 30 :=
  Boolean.leaf_sound a [2,3,4,7,8,0,5] 30 cert72 (by decide +kernel)

theorem node73 : UpperPrefix a [2,3,4,7,8,0] 30 :=
  branch_upper a [2,3,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,7,8,0,0] 30 (by decide +kernel))
  node71
  (invalid_upper a [2,3,4,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,4] 30 (by decide +kernel))
  node72
  (invalid_upper a [2,3,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,0,8] 30 (by decide +kernel)))

def cert74 : Local := ⟨⟨0,0,483,0,195,401,0,115,227⟩,[(0,1),(1,2),(3,6),(6,3)],[(2,0,0),(3,1,0),(3,1,1)]⟩
theorem node74 : UpperPrefix a [2,3,4,7,8,1,0] 30 :=
  local_sound a [2,3,4,7,8,1,0] 30 cert74 (by decide +kernel)

def cert75 : Local := ⟨⟨0,0,482,0,194,400,274,114,226⟩,[(0,1),(1,2),(3,7)],[(2,0,0),(3,1,0),(3,1,1),(0,7,3)]⟩
theorem node75 : UpperPrefix a [2,3,4,7,8,1,5,0] 30 :=
  local_sound a [2,3,4,7,8,1,5,0] 30 cert75 (by decide +kernel)

def cert76 : Local := ⟨⟨0,0,419,306,131,401,275,51,163⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1),(6,7,6)]⟩
theorem node76 : UpperPrefix a [2,3,4,7,8,1,5,6] 30 :=
  local_sound a [2,3,4,7,8,1,5,6] 30 cert76 (by decide +kernel)

theorem node77 : UpperPrefix a [2,3,4,7,8,1,5] 30 :=
  branch_upper a [2,3,4,7,8,1,5] 30 (by decide) (fin9_cases _
  node75
  (invalid_upper a [2,3,4,7,8,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,5,5] 30 (by decide +kernel))
  node76
  (invalid_upper a [2,3,4,7,8,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,5,8] 30 (by decide +kernel)))

theorem node78 : UpperPrefix a [2,3,4,7,8,1] 30 :=
  branch_upper a [2,3,4,7,8,1] 30 (by decide) (fin9_cases _
  node74
  (invalid_upper a [2,3,4,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,4] 30 (by decide +kernel))
  node77
  (invalid_upper a [2,3,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,1,8] 30 (by decide +kernel)))

theorem node79 : UpperPrefix a [2,3,4,7,8] 30 :=
  branch_upper a [2,3,4,7,8] 30 (by decide) (fin9_cases _
  node73
  node78
  (invalid_upper a [2,3,4,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,8,8] 30 (by decide +kernel)))

theorem node80 : UpperPrefix a [2,3,4,7] 30 :=
  branch_upper a [2,3,4,7] 30 (by decide) (fin9_cases _
  node64
  node69
  (invalid_upper a [2,3,4,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,7,5] 30 (by decide +kernel))
  node70
  (invalid_upper a [2,3,4,7,7] 30 (by decide +kernel))
  node79)

def cert81 : Leaf := ⟨⟨0,0,259,18,451,403,307,115,227⟩,[(0,1),(1,2)],[(2,0,0),(3,1,0),(3,1,1)],⟨7,14,28,265,243,227,227,483,499⟩,⟨7,14,28,265,48,96,192,384,272⟩,[⟨5,1210107564158003386195343,⟨7,15,31,271,16,64,203,399,287⟩⟩,⟨6,1210106412362398686190991,⟨7,15,31,271,48,32,139,399,287⟩⟩,⟨7,1208926973663185881734543,⟨7,15,31,271,48,96,75,271,287⟩⟩]⟩
theorem node81 : UpperPrefix a [2,3,4,8] 30 :=
  Boolean.leaf_sound a [2,3,4,8] 30 cert81 (by decide +kernel)

theorem node82 : UpperPrefix a [2,3,4] 30 :=
  branch_upper a [2,3,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,4,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [2,3,4,1] [2,3,0,4] 30 (by decide +kernel) node49)
  (invalid_upper a [2,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,4,4] 30 (by decide +kernel))
  node50
  node61
  node80
  node81)

theorem node83 : UpperPrefix a [2,3] 30 :=
  branch_upper a [2,3] 30 (by decide) (fin9_cases _
  node47
  node48
  (invalid_upper a [2,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,3] 30 (by decide +kernel))
  node82
  (PrefixConjugacy.upper aut4 [2,3,5] [2,3,4] 30 (by decide +kernel) node82)
  (PrefixConjugacy.upper aut3 [2,3,6] [2,3,4] 30 (by decide +kernel) node82)
  (PrefixConjugacy.upper aut2 [2,3,7] [2,3,4] 30 (by decide +kernel) node82)
  (PrefixConjugacy.upper aut1 [2,3,8] [2,3,4] 30 (by decide +kernel) node82))

def cert84 : Leaf := ⟨⟨0,40,0,18,458,410,314,122,234⟩,[(0,1),(2,3)],[(2,0,0),(0,2,2)],⟨7,22,13,41,506,490,458,458,474⟩,⟨7,22,13,41,48,96,192,384,272⟩,[⟨6,1210106412362349300819347,⟨7,31,13,45,63,32,129,391,287⟩⟩,⟨7,1208926973663136496362899,⟨7,31,13,45,63,96,65,263,287⟩⟩,⟨8,1181745669224732960147,⟨7,31,13,45,63,96,193,135,31⟩⟩]⟩
theorem node84 : UpperPrefix a [2,4,0,5] 30 :=
  Boolean.leaf_sound a [2,4,0,5] 30 cert84 (by decide +kernel)

def cert85 : Leaf := ⟨⟨0,488,0,432,456,408,312,120,232⟩,[(0,1),(2,3)],[(2,0,0),(0,2,2)],⟨7,22,13,73,50,488,488,424,440⟩,⟨7,22,13,73,50,96,192,384,272⟩,[⟨1,1219580022514450859032577,⟨493,508,237,237,496,96,192,384,272⟩⟩]⟩
theorem node85 : UpperPrefix a [2,4,0,6,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,1] 30 cert85 (by decide +kernel)

def cert86 : Local := ⟨⟨0,424,0,434,450,402,306,50,162⟩,[(0,1),(2,3)],[(2,0,0),(0,2,2),(6,3,4),(3,4,1)]⟩
theorem node86 : UpperPrefix a [2,4,0,6,3] 30 :=
  local_sound a [2,4,0,6,3] 30 cert86 (by decide +kernel)

def cert87 : Leaf := ⟨⟨0,232,0,178,74,152,314,122,234⟩,[(0,1),(2,3)],[(2,0,0),(0,2,2)],⟨7,22,13,73,176,98,488,424,312⟩,⟨7,22,13,73,176,98,192,384,272⟩,[⟨8,1181748206908264871295,⟨7,23,47,127,191,127,255,131,23⟩⟩]⟩
theorem node87 : UpperPrefix a [2,4,0,6,7,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,7,1] 30 cert87 (by decide +kernel)

def cert88 : Local := ⟨⟨0,424,0,434,266,0,314,58,170⟩,[(0,1),(2,3),(5,3)],[(2,0,0),(0,2,2),(6,3,5)]⟩
theorem node88 : UpperPrefix a [2,4,0,6,7,3] 30 :=
  local_sound a [2,4,0,6,7,3] 30 cert88 (by decide +kernel)

def cert89 : Local := ⟨⟨0,232,0,178,330,154,58,122,234⟩,[(0,1),(2,3)],[(2,0,0),(0,2,2),(8,5,4)]⟩
theorem node89 : UpperPrefix a [2,4,0,6,7,8] 30 :=
  local_sound a [2,4,0,6,7,8] 30 cert89 (by decide +kernel)

theorem node90 : UpperPrefix a [2,4,0,6,7] 30 :=
  branch_upper a [2,4,0,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,7,0] 30 (by decide +kernel))
  node87
  (invalid_upper a [2,4,0,6,7,2] 30 (by decide +kernel))
  node88
  (invalid_upper a [2,4,0,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,7,7] 30 (by decide +kernel))
  node89)

def cert91 : Leaf := ⟨⟨0,488,0,418,202,392,298,106,234⟩,[(0,1),(2,3)],[(2,0,0),(0,2,2)],⟨7,22,13,73,304,98,232,424,440⟩,⟨7,22,13,73,304,98,192,384,272⟩,[⟨4,1210255463600074998416419,⟨111,239,45,109,493,111,192,384,460⟩⟩]⟩
theorem node91 : UpperPrefix a [2,4,0,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,0,6,8,1] 30 cert91 (by decide +kernel)

def cert92 : Local := ⟨⟨0,424,0,434,138,0,314,58,170⟩,[(0,1),(2,3),(5,3)],[(2,0,0),(0,2,2),(6,3,5)]⟩
theorem node92 : UpperPrefix a [2,4,0,6,8,3] 30 :=
  local_sound a [2,4,0,6,8,3] 30 cert92 (by decide +kernel)

def cert93 : Local := ⟨⟨0,360,0,306,74,0,314,122,106⟩,[(0,1),(2,3),(5,6)],[(2,0,0),(0,2,2),(7,5,5)]⟩
theorem node93 : UpperPrefix a [2,4,0,6,8,7] 30 :=
  local_sound a [2,4,0,6,8,7] 30 cert93 (by decide +kernel)

theorem node94 : UpperPrefix a [2,4,0,6,8] 30 :=
  branch_upper a [2,4,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,8,0] 30 (by decide +kernel))
  node91
  (invalid_upper a [2,4,0,6,8,2] 30 (by decide +kernel))
  node92
  (invalid_upper a [2,4,0,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,8,6] 30 (by decide +kernel))
  node93
  (invalid_upper a [2,4,0,6,8,8] 30 (by decide +kernel)))

theorem node95 : UpperPrefix a [2,4,0,6] 30 :=
  branch_upper a [2,4,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,6,0] 30 (by decide +kernel))
  node85
  (invalid_upper a [2,4,0,6,2] 30 (by decide +kernel))
  node86
  (invalid_upper a [2,4,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,6,6] 30 (by decide +kernel))
  node90
  node94)

theorem node96 : UpperPrefix a [2,4,0] 30 :=
  branch_upper a [2,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut10 [2,4,0,1] [2,3,0,4] 30 (by decide +kernel) node49)
  (invalid_upper a [2,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,0,4] 30 (by decide +kernel))
  node84
  node95
  (PrefixConjugacy.upper aut12 [2,4,0,7] [2,4,0,6] 30 (by decide +kernel) node95)
  (PrefixConjugacy.upper aut11 [2,4,0,8] [2,4,0,5] 30 (by decide +kernel) node84))

def cert97 : Leaf := ⟨⟨0,489,481,0,0,393,297,105,233⟩,[(0,1),(3,4),(4,3)],[(2,0,0),(1,2,0)],⟨7,22,14,41,49,488,456,456,472⟩,⟨7,22,14,41,49,96,192,384,272⟩,[⟨4,1212473369217406827234311,⟨7,15,15,41,41,96,192,480,488⟩⟩]⟩
theorem node97 : UpperPrefix a [2,4,1,5,0] 30 :=
  Boolean.leaf_sound a [2,4,1,5,0] 30 cert97 (by decide +kernel)

def cert98 : Local := ⟨⟨0,457,465,464,0,401,273,81,193⟩,[(0,1),(4,3)],[(2,0,0),(1,2,0),(5,3,4),(3,4,1)]⟩
theorem node98 : UpperPrefix a [2,4,1,5,3] 30 :=
  local_sound a [2,4,1,5,3] 30 cert98 (by decide +kernel)

def cert99 : Leaf := ⟨⟨0,297,305,272,0,409,313,57,169⟩,[(0,1),(4,5)],[(2,0,0),(1,2,0),(6,4,4)],⟨7,22,14,41,112,489,457,393,409⟩,⟨7,22,14,41,112,96,192,384,272⟩,[⟨7,1208926973665339822994879,⟨7,31,15,63,127,127,65,263,287⟩⟩]⟩
theorem node99 : UpperPrefix a [2,4,1,5,6] 30 :=
  Boolean.leaf_sound a [2,4,1,5,6] 30 cert99 (by decide +kernel)

def cert100 : Local := ⟨⟨0,488,496,0,328,408,312,120,232⟩,[(0,1),(3,5)],[(2,0,0),(1,2,0),(0,5,3)]⟩
theorem node100 : UpperPrefix a [2,4,1,5,7,0] 30 :=
  local_sound a [2,4,1,5,7,0] 30 cert100 (by decide +kernel)

def cert101 : Leaf := ⟨⟨0,225,241,208,65,145,305,113,225⟩,[(0,1)],[(2,0,0),(1,2,0)],⟨7,22,14,41,176,104,449,449,337⟩,⟨7,22,14,41,176,104,192,384,272⟩,[⟨3,1276359316843304888306695,⟨455,471,471,497,176,496,192,384,272⟩⟩,⟨8,1181747925435503273471,⟨7,31,15,47,191,127,255,135,31⟩⟩]⟩
theorem node101 : UpperPrefix a [2,4,1,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,1,5,7,3] 30 cert101 (by decide +kernel)

def cert102 : Leaf := ⟨⟨0,41,49,16,329,153,57,121,233⟩,[(0,1)],[(2,0,0),(1,2,0),(8,5,4)],⟨7,22,14,41,176,352,201,457,345⟩,⟨7,22,14,41,176,352,192,384,272⟩,[⟨6,1210106412362353602078135,⟨7,31,15,45,191,303,129,391,287⟩⟩,⟨7,1208926973663140797621687,⟨7,31,15,45,63,367,65,263,287⟩⟩]⟩
theorem node102 : UpperPrefix a [2,4,1,5,7,8] 30 :=
  Boolean.leaf_sound a [2,4,1,5,7,8] 30 cert102 (by decide +kernel)

theorem node103 : UpperPrefix a [2,4,1,5,7] 30 :=
  branch_upper a [2,4,1,5,7] 30 (by decide) (fin9_cases _
  node100
  (invalid_upper a [2,4,1,5,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,2] 30 (by decide +kernel))
  node101
  (invalid_upper a [2,4,1,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,7,7] 30 (by decide +kernel))
  node102)

def cert104 : Leaf := ⟨⟨0,41,49,16,201,153,57,121,233⟩,[(0,1)],[(2,0,0),(1,2,0)],⟨7,22,14,41,304,233,201,457,473⟩,⟨7,22,14,41,304,96,192,384,272⟩,[⟨8,1184058267659188970903,⟨7,31,15,41,63,104,237,239,31⟩⟩,⟨6,1210106412362349298722199,⟨7,31,15,41,319,32,129,391,287⟩⟩,⟨7,1208926973663136494265751,⟨7,31,15,41,319,96,65,263,287⟩⟩]⟩
theorem node104 : UpperPrefix a [2,4,1,5,8] 30 :=
  Boolean.leaf_sound a [2,4,1,5,8] 30 cert104 (by decide +kernel)

theorem node105 : UpperPrefix a [2,4,1,5] 30 :=
  branch_upper a [2,4,1,5] 30 (by decide) (fin9_cases _
  node97
  (invalid_upper a [2,4,1,5,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,2] 30 (by decide +kernel))
  node98
  (invalid_upper a [2,4,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,5,5] 30 (by decide +kernel))
  node99
  node103
  node104)

def cert106 : Local := ⟨⟨0,425,433,432,392,0,313,57,169⟩,[(0,1),(5,3)],[(2,0,0),(1,2,0),(6,3,5)]⟩
theorem node106 : UpperPrefix a [2,4,1,6,0,3] 30 :=
  local_sound a [2,4,1,6,0,3] 30 cert106 (by decide +kernel)

def cert107 : Local := ⟨⟨0,361,369,304,328,0,313,121,105⟩,[(0,1),(5,6)],[(2,0,0),(1,2,0),(7,5,5)]⟩
theorem node107 : UpperPrefix a [2,4,1,6,0,7] 30 :=
  local_sound a [2,4,1,6,0,7] 30 cert107 (by decide +kernel)

def cert108 : Leaf := ⟨⟨0,73,81,16,72,153,313,121,233⟩,[(0,1)],[(2,0,0),(1,2,0)],⟨7,22,14,73,49,352,232,424,440⟩,⟨7,22,14,73,49,352,192,384,272⟩,[⟨7,1208926973665337605776695,⟨7,23,15,73,63,383,64,259,279⟩⟩,⟨8,1181745671425842373943,⟨7,23,15,73,63,127,192,131,23⟩⟩,⟨5,1210107564157956086965559,⟨7,23,15,73,31,335,192,387,279⟩⟩]⟩
theorem node108 : UpperPrefix a [2,4,1,6,0,8] 30 :=
  Boolean.leaf_sound a [2,4,1,6,0,8] 30 cert108 (by decide +kernel)

theorem node109 : UpperPrefix a [2,4,1,6,0] 30 :=
  branch_upper a [2,4,1,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,6,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,0,2] 30 (by decide +kernel))
  node106
  (invalid_upper a [2,4,1,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,0,6] 30 (by decide +kernel))
  node107
  node108)

def cert110 : Leaf := ⟨⟨0,297,305,304,321,401,305,49,161⟩,[(0,1)],[(2,0,0),(1,2,0),(6,3,4),(3,4,1)],⟨7,22,14,73,56,481,481,417,433⟩,⟨7,22,14,73,56,96,192,384,272⟩,[⟨7,1208926973665337605776695,⟨7,23,15,73,63,127,64,259,279⟩⟩]⟩
theorem node110 : UpperPrefix a [2,4,1,6,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,3] 30 cert110 (by decide +kernel)

def cert111 : Leaf := ⟨⟨0,361,369,0,329,0,313,121,105⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(1,2,0)],⟨7,22,14,73,176,97,488,424,312⟩,⟨7,22,14,73,176,97,192,384,272⟩,[⟨7,1284484837670527874245911,⟨7,279,47,105,319,105,64,259,279⟩⟩]⟩
theorem node111 : UpperPrefix a [2,4,1,6,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,0] 30 cert111 (by decide +kernel)

def cert112 : Local := ⟨⟨0,425,433,432,265,0,313,57,169⟩,[(0,1),(5,3)],[(2,0,0),(1,2,0),(6,3,5)]⟩
theorem node112 : UpperPrefix a [2,4,1,6,7,3] 30 :=
  local_sound a [2,4,1,6,7,3] 30 cert112 (by decide +kernel)

def cert113 : Leaf := ⟨⟨0,73,81,16,329,153,57,121,105⟩,[(0,1)],[(2,0,0),(1,2,0),(8,5,4)],⟨7,22,14,73,176,352,233,425,313⟩,⟨7,22,14,73,176,352,192,384,272⟩,[⟨7,1284484837389052905923895,⟨7,279,15,73,319,367,64,259,279⟩⟩,⟨5,1210107564157956086965559,⟨7,23,15,73,159,335,192,387,279⟩⟩]⟩
theorem node113 : UpperPrefix a [2,4,1,6,7,8] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,8] 30 cert113 (by decide +kernel)

theorem node114 : UpperPrefix a [2,4,1,6,7] 30 :=
  branch_upper a [2,4,1,6,7] 30 (by decide) (fin9_cases _
  node111
  (invalid_upper a [2,4,1,6,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,2] 30 (by decide +kernel))
  node112
  (invalid_upper a [2,4,1,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,7] 30 (by decide +kernel))
  node113)

def cert115 : Leaf := ⟨⟨0,489,481,0,201,0,297,105,233⟩,[(0,1),(3,5),(5,3)],[(2,0,0),(1,2,0)],⟨7,22,14,73,304,97,232,424,440⟩,⟨7,22,14,73,304,97,192,384,272⟩,[⟨4,1210255464022285838189575,⟨111,239,111,109,488,109,192,384,448⟩⟩]⟩
theorem node115 : UpperPrefix a [2,4,1,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,0] 30 cert115 (by decide +kernel)

def cert116 : Local := ⟨⟨0,425,433,432,137,0,313,57,169⟩,[(0,1),(5,3)],[(2,0,0),(1,2,0),(6,3,5)]⟩
theorem node116 : UpperPrefix a [2,4,1,6,8,3] 30 :=
  local_sound a [2,4,1,6,8,3] 30 cert116 (by decide +kernel)

def cert117 : Local := ⟨⟨0,361,369,304,73,0,313,121,105⟩,[(0,1),(5,6)],[(2,0,0),(1,2,0),(7,5,5)]⟩
theorem node117 : UpperPrefix a [2,4,1,6,8,7] 30 :=
  local_sound a [2,4,1,6,8,7] 30 cert117 (by decide +kernel)

theorem node118 : UpperPrefix a [2,4,1,6,8] 30 :=
  branch_upper a [2,4,1,6,8] 30 (by decide) (fin9_cases _
  node115
  (invalid_upper a [2,4,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,2] 30 (by decide +kernel))
  node116
  (invalid_upper a [2,4,1,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,6] 30 (by decide +kernel))
  node117
  (invalid_upper a [2,4,1,6,8,8] 30 (by decide +kernel)))

theorem node119 : UpperPrefix a [2,4,1,6] 30 :=
  branch_upper a [2,4,1,6] 30 (by decide) (fin9_cases _
  node109
  (invalid_upper a [2,4,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,2] 30 (by decide +kernel))
  node110
  (invalid_upper a [2,4,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,6] 30 (by decide +kernel))
  node114
  node118)

def cert120 : Leaf := ⟨⟨0,105,113,112,72,145,313,121,105⟩,[(0,1)],[(2,0,0),(1,2,0),(7,3,5)],⟨7,22,14,137,49,104,480,480,368⟩,⟨7,22,14,137,49,104,192,384,272⟩,[⟨8,1181747927628010022007,⟨7,23,15,137,55,127,255,128,19⟩⟩]⟩
theorem node120 : UpperPrefix a [2,4,1,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,1,7,0,3] 30 cert120 (by decide +kernel)

def cert121 : Local := ⟨⟨0,361,369,368,328,25,0,121,105⟩,[(0,1),(6,3)],[(2,0,0),(1,2,0),(7,3,6)]⟩
theorem node121 : UpperPrefix a [2,4,1,7,0,8,3] 30 :=
  local_sound a [2,4,1,7,0,8,3] 30 cert121 (by decide +kernel)

def cert122 : Leaf := ⟨⟨0,225,241,112,192,145,273,121,233⟩,[(0,1)],[(2,0,0),(1,2,0),(8,5,6)],⟨7,22,14,137,49,352,224,456,344⟩,⟨7,22,14,137,49,352,224,384,272⟩,[⟨3,1210110019746197285112839,⟨7,23,87,241,49,352,224,480,272⟩⟩]⟩
theorem node122 : UpperPrefix a [2,4,1,7,0,8,5] 30 :=
  Boolean.leaf_sound a [2,4,1,7,0,8,5] 30 cert122 (by decide +kernel)

theorem node123 : UpperPrefix a [2,4,1,7,0,8] 30 :=
  branch_upper a [2,4,1,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,7,0,8,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,8,2] 30 (by decide +kernel))
  node121
  (invalid_upper a [2,4,1,7,0,8,4] 30 (by decide +kernel))
  node122
  (invalid_upper a [2,4,1,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,8,8] 30 (by decide +kernel)))

theorem node124 : UpperPrefix a [2,4,1,7,0] 30 :=
  branch_upper a [2,4,1,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,2] 30 (by decide +kernel))
  node120
  (invalid_upper a [2,4,1,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,0,7] 30 (by decide +kernel))
  node123)

def cert125 : Leaf := ⟨⟨0,169,177,48,129,401,305,113,225⟩,[(0,1)],[(2,0,0),(1,2,0),(3,4,1)],⟨7,22,14,137,56,353,481,481,369⟩,⟨7,22,14,137,56,96,192,384,272⟩,[⟨6,1210106412364571918624183,⟨7,23,15,141,63,63,141,399,279⟩⟩,⟨8,1181745671447350764983,⟨7,23,15,141,63,127,205,143,23⟩⟩]⟩
theorem node125 : UpperPrefix a [2,4,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,1,7,3] 30 cert125 (by decide +kernel)

def cert126 : Leaf := ⟨⟨0,393,401,272,0,409,313,57,169⟩,[(0,1),(4,5)],[(2,0,0),(1,2,0),(6,4,4)],⟨7,22,14,137,112,361,489,425,313⟩,⟨7,22,14,137,112,96,192,384,272⟩,[⟨5,1210107564157977586967959,⟨7,23,15,141,95,72,205,399,279⟩⟩]⟩
theorem node126 : UpperPrefix a [2,4,1,7,6] 30 :=
  Boolean.leaf_sound a [2,4,1,7,6] 30 cert126 (by decide +kernel)

def cert127 : Local := ⟨⟨0,361,369,368,73,280,0,121,105⟩,[(0,1),(6,3)],[(2,0,0),(1,2,0),(7,3,6)]⟩
theorem node127 : UpperPrefix a [2,4,1,7,8,0,3] 30 :=
  local_sound a [2,4,1,7,8,0,3] 30 cert127 (by decide +kernel)

#print axioms node127
end Delivery.FiniteExclusion.Sharp4x5
