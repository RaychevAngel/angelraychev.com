import RegularNineSharp3x3x3Base
import RegularNineSharp3x3x3C000
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def cert64 : Local := ⟨⟨0,240,0,224,330,210,58,122,186⟩,[(0,1),(2,6)],[(2,0,0),(8,5,4),(0,6,2)]⟩
theorem node64 : UpperPrefix a [2,3,6,1,7,8,0] 30 :=
  local_sound a [2,3,6,1,7,8,0] 30 cert64 (by decide +kernel)

def cert65 : Leaf := ⟨⟨0,113,50,97,323,83,0,115,51⟩,[(0,1),(6,4)],[(2,0,0),(7,4,6),(8,5,4)],⟨7,14,69,26,176,296,208,417,353⟩,⟨7,14,69,26,176,296,208,384,320⟩,[⟨3,1361519305334186100917259,⟨7,7,69,87,500,501,208,384,320⟩⟩]⟩
theorem node65 : UpperPrefix a [2,3,6,1,7,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,1,7,8,4] 30 cert65 (by decide +kernel)

def cert66 : Leaf := ⟨⟨0,241,184,225,0,209,0,121,185⟩,[(0,1),(4,6),(6,4)],[(2,0,0),(8,5,4),(8,5,6)],⟨7,14,69,26,176,296,224,401,337⟩,⟨7,14,69,26,176,296,224,384,320⟩,[⟨1,1233765856906928815603713,⟨501,508,469,120,240,296,240,384,336⟩⟩]⟩
theorem node66 : UpperPrefix a [2,3,6,1,7,8,5] 30 :=
  Boolean.leaf_sound a [2,3,6,1,7,8,5] 30 cert66 (by decide +kernel)

theorem node67 : UpperPrefix a [2,3,6,1,7,8] 30 :=
  branch_upper a [2,3,6,1,7,8] 30 (by decide) (fin9_cases _
  node64
  (invalid_upper a [2,3,6,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,3] 30 (by decide +kernel))
  node65
  node66
  (invalid_upper a [2,3,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,8,8] 30 (by decide +kernel)))

theorem node68 : UpperPrefix a [2,3,6,1,7] 30 :=
  branch_upper a [2,3,6,1,7] 30 (by decide) (fin9_cases _
  node59
  (invalid_upper a [2,3,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,3] 30 (by decide +kernel))
  node63
  (invalid_upper a [2,3,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,7,7] 30 (by decide +kernel))
  node67)

def cert69 : Leaf := ⟨⟨0,369,304,353,65,338,305,113,177⟩,[(0,1)],[(2,0,0),(1,3,5)],⟨7,14,69,26,304,41,240,432,496⟩,⟨7,14,69,26,304,41,192,384,320⟩,[⟨3,1437224743012690100749323,⟨7,7,69,471,500,501,192,384,320⟩⟩,⟨7,1208926990507714773495255,⟨39,47,111,59,319,41,127,319,383⟩⟩]⟩
theorem node69 : UpperPrefix a [2,3,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,0] 30 cert69 (by decide +kernel)

def cert70 : Leaf := ⟨⟨0,496,0,480,200,336,312,120,184⟩,[(0,1),(2,6)],[(2,0,0),(0,6,2)],⟨7,14,69,26,304,168,193,432,368⟩,⟨7,14,69,26,304,168,193,384,320⟩,[⟨1,1224523786202047900286977,⟨501,508,469,440,432,184,469,384,324⟩⟩]⟩
theorem node70 : UpperPrefix a [2,3,6,1,8,7,0] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,7,0] 30 cert70 (by decide +kernel)

def cert71 : Leaf := ⟨⟨0,81,18,65,195,83,291,115,179⟩,[(0,1)],[(2,0,0),(8,4,6)],⟨7,14,69,26,304,168,208,417,353⟩,⟨7,14,69,26,304,168,208,384,320⟩,[⟨3,1361519305334186100917259,⟨7,7,69,87,500,501,208,384,320⟩⟩,⟨5,1210107564157962600754647,⟨7,15,79,27,287,137,223,391,335⟩⟩,⟨7,1208926973663145096293847,⟨7,15,79,27,319,41,95,263,335⟩⟩]⟩
theorem node71 : UpperPrefix a [2,3,6,1,8,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,7,4] 30 cert71 (by decide +kernel)

def cert72 : Leaf := ⟨⟨0,369,312,353,73,337,0,121,57⟩,[(0,1),(6,5)],[(2,0,0),(7,5,6)],⟨7,14,69,26,304,168,224,401,337⟩,⟨7,14,69,26,304,168,224,384,320⟩,[⟨1,1233766145132906920804353,⟨501,508,469,120,368,232,224,384,320⟩⟩]⟩
theorem node72 : UpperPrefix a [2,3,6,1,8,7,5] 30 :=
  Boolean.leaf_sound a [2,3,6,1,8,7,5] 30 cert72 (by decide +kernel)

theorem node73 : UpperPrefix a [2,3,6,1,8,7] 30 :=
  branch_upper a [2,3,6,1,8,7] 30 (by decide) (fin9_cases _
  node70
  (invalid_upper a [2,3,6,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,3] 30 (by decide +kernel))
  node71
  node72
  (invalid_upper a [2,3,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,7,8] 30 (by decide +kernel)))

theorem node74 : UpperPrefix a [2,3,6,1,8] 30 :=
  branch_upper a [2,3,6,1,8] 30 (by decide) (fin9_cases _
  node69
  (invalid_upper a [2,3,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut94 [2,3,6,1,8,4] [2,3,6,1,7,4] 30 (by decide +kernel) node63)
  (invalid_upper a [2,3,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,8,6] 30 (by decide +kernel))
  node73
  (invalid_upper a [2,3,6,1,8,8] 30 (by decide +kernel)))

theorem node75 : UpperPrefix a [2,3,6,1] 30 :=
  branch_upper a [2,3,6,1] 30 (by decide) (fin9_cases _
  node58
  (invalid_upper a [2,3,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,1,6] 30 (by decide +kernel))
  node68
  node74)

def cert76 : Local := ⟨⟨0,464,0,0,458,386,266,74,138⟩,[(0,1),(2,4),(3,4)],[(2,0,0),(4,2,1),(5,3,3),(0,4,2)]⟩
theorem node76 : UpperPrefix a [2,3,4,5,0,6] 30 :=
  local_sound a [2,3,4,5,0,6] 30 cert76 (by decide +kernel)

def cert77 : Local := ⟨⟨0,0,466,0,456,402,282,90,154⟩,[(0,1),(1,0),(3,4)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(5,3,3)]⟩
theorem node77 : UpperPrefix a [2,0,3,5,1,6] 30 :=
  local_sound a [2,0,3,5,1,6] 30 cert77 (by decide +kernel)

def cert78 : Local := ⟨⟨0,465,410,0,456,337,281,89,153⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(1,6,2)]⟩
theorem node78 : UpperPrefix a [2,3,6,5,0,7,1] 30 :=
  local_sound a [2,3,6,5,0,7,1] 30 cert78 (by decide +kernel)

def cert79 : Leaf := ⟨⟨0,464,410,0,458,338,266,90,154⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,49,168,208,386,322⟩,⟨7,14,69,56,49,168,208,384,320⟩,[⟨0,1229061886075831139175424,⟨422,430,494,120,248,168,248,384,360⟩⟩]⟩
theorem node79 : UpperPrefix a [2,3,6,5,0,7,4] 30 :=
  Boolean.leaf_sound a [2,3,6,5,0,7,4] 30 cert79 (by decide +kernel)

def cert80 : Local := ⟨⟨0,209,154,0,202,83,0,91,155⟩,[(0,1),(3,4),(6,7)],[(2,0,0),(5,3,3),(8,6,6)]⟩
theorem node80 : UpperPrefix a [2,3,6,5,0,7,8] 30 :=
  local_sound a [2,3,6,5,0,7,8] 30 cert80 (by decide +kernel)

theorem node81 : UpperPrefix a [2,3,6,5,0,7] 30 :=
  branch_upper a [2,3,6,5,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,5,0,7,0] 30 (by decide +kernel))
  node78
  (invalid_upper a [2,3,6,5,0,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,0,7,3] 30 (by decide +kernel))
  node79
  (invalid_upper a [2,3,6,5,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,0,7,7] 30 (by decide +kernel))
  node80)

theorem node82 : UpperPrefix a [2,3,6,5,0] 30 :=
  branch_upper a [2,3,6,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,5,0,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut54 [2,3,6,5,0,1] [2,3,4,5,0,6] 30 (by decide +kernel) node76)
  (invalid_upper a [2,3,6,5,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,0,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut57 [2,3,6,5,0,4] [2,0,3,5,1,6] 30 (by decide +kernel) node77)
  (invalid_upper a [2,3,6,5,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,0,6] 30 (by decide +kernel))
  node81
  (PrefixConjugacy.upper aut55 [2,3,6,5,0,8] [2,3,6,5,0,7] 30 (by decide +kernel) node81))

def cert83 : Leaf := ⟨⟨0,481,458,482,386,0,290,98,162⟩,[(0,1),(5,3)],[(2,0,0),(0,3,1),(4,5,5)],⟨7,14,37,25,112,56,450,386,450⟩,⟨7,14,37,25,112,56,192,384,320⟩,[⟨3,1224302388892040518697987,⟨471,471,501,465,112,48,192,384,320⟩⟩]⟩
theorem node83 : UpperPrefix a [2,3,5,0,6,4] 30 :=
  Boolean.leaf_sound a [2,3,5,0,6,4] 30 cert83 (by decide +kernel)

def cert84 : Local := ⟨⟨0,0,482,480,392,0,296,104,168⟩,[(0,1),(1,0),(5,3)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(1,3,2),(4,5,5)]⟩
theorem node84 : UpperPrefix a [2,0,3,1,6,4] 30 :=
  local_sound a [2,0,3,1,6,4] 30 cert84 (by decide +kernel)

theorem node85 : UpperPrefix a [2,3,6,5,1] 30 :=
  branch_upper a [2,3,6,5,1] 30 (by decide) (fin9_cases _
  (PrefixConjugacy.upper aut90 [2,3,6,5,1,0] [2,3,5,0,6,4] 30 (by decide +kernel) node83)
  (invalid_upper a [2,3,6,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,1,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut93 [2,3,6,5,1,4] [2,0,3,1,6,4] 30 (by decide +kernel) node84)
  (invalid_upper a [2,3,6,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,1,6] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut92 [2,3,6,5,1,7] [2,3,6,0,8,4] 30 (by decide +kernel) node48)
  (PrefixConjugacy.upper aut91 [2,3,6,5,1,8] [2,3,6,0,7,4] 30 (by decide +kernel) node41))

def cert86 : Leaf := ⟨⟨0,209,154,0,75,194,283,91,155⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,176,41,466,402,338⟩,⟨7,14,69,56,176,41,192,384,320⟩,[⟨8,1181762254318802800583,⟨47,47,127,56,187,43,255,191,127⟩⟩,⟨4,1210107565353120918668291,⟨39,47,69,40,160,41,192,384,320⟩⟩]⟩
theorem node86 : UpperPrefix a [2,3,6,5,7,0] 30 :=
  Boolean.leaf_sound a [2,3,6,5,7,0] 30 cert86 (by decide +kernel)

def cert87 : Local := ⟨⟨0,465,402,0,323,0,275,83,147⟩,[(0,1),(3,4),(5,1)],[(2,0,0),(3,1,5),(5,3,3)]⟩
theorem node87 : UpperPrefix a [2,3,6,5,7,1] 30 :=
  local_sound a [2,3,6,5,7,1] 30 cert87 (by decide +kernel)

def cert88 : Local := ⟨⟨0,0,426,480,202,0,298,106,170⟩,[(0,1),(1,0),(5,3)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(4,5,5)]⟩
theorem node88 : UpperPrefix a [2,0,6,1,8,4] 30 :=
  local_sound a [2,0,6,1,8,4] 30 cert88 (by decide +kernel)

def cert89 : Leaf := ⟨⟨0,208,154,0,330,210,27,91,155⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3),(8,5,4)],⟨7,14,69,56,176,296,211,403,339⟩,⟨7,14,69,56,176,296,192,384,320⟩,[⟨0,1210107578807906984791040,⟨6,14,94,56,184,296,248,440,376⟩⟩]⟩
theorem node89 : UpperPrefix a [2,3,6,5,7,8] 30 :=
  Boolean.leaf_sound a [2,3,6,5,7,8] 30 cert89 (by decide +kernel)

theorem node90 : UpperPrefix a [2,3,6,5,7] 30 :=
  branch_upper a [2,3,6,5,7] 30 (by decide) (fin9_cases _
  node86
  node87
  (invalid_upper a [2,3,6,5,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut95 [2,3,6,5,7,4] [2,0,6,1,8,4] 30 (by decide +kernel) node88)
  (invalid_upper a [2,3,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,7,7] 30 (by decide +kernel))
  node89)

def cert91 : Leaf := ⟨⟨0,337,282,0,75,322,283,91,155⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,304,41,210,402,466⟩,⟨7,14,69,56,304,41,192,384,320⟩,[⟨7,1208926990507714773495255,⟨39,47,111,59,319,41,127,319,383⟩⟩,⟨4,1210107565353120918668291,⟨39,47,69,40,288,41,192,384,320⟩⟩]⟩
theorem node91 : UpperPrefix a [2,3,6,5,8,0] 30 :=
  Boolean.leaf_sound a [2,3,6,5,8,0] 30 cert91 (by decide +kernel)

def cert92 : Local := ⟨⟨0,465,402,0,195,0,275,83,147⟩,[(0,1),(3,4),(5,1)],[(2,0,0),(3,1,5),(5,3,3)]⟩
theorem node92 : UpperPrefix a [2,3,6,5,8,1] 30 :=
  local_sound a [2,3,6,5,8,1] 30 cert92 (by decide +kernel)

def cert93 : Local := ⟨⟨0,0,426,480,330,0,298,106,170⟩,[(0,1),(1,0),(5,3)],[(2,0,0),(2,0,1),(0,1,0),(0,1,1),(4,5,5)]⟩
theorem node93 : UpperPrefix a [2,0,6,1,7,4] 30 :=
  local_sound a [2,0,6,1,7,4] 30 cert93 (by decide +kernel)

def cert94 : Leaf := ⟨⟨0,400,410,0,138,274,283,91,155⟩,[(0,1),(3,4)],[(2,0,0),(5,3,3)],⟨7,14,69,56,304,168,211,403,339⟩,⟨7,14,69,56,304,168,192,384,320⟩,[⟨0,1210107572065705978235904,⟨6,14,110,56,312,184,248,440,376⟩⟩,⟨6,1210106419144201371388935,⟨7,15,47,56,312,184,184,440,312⟩⟩]⟩
theorem node94 : UpperPrefix a [2,3,6,5,8,7] 30 :=
  Boolean.leaf_sound a [2,3,6,5,8,7] 30 cert94 (by decide +kernel)

theorem node95 : UpperPrefix a [2,3,6,5,8] 30 :=
  branch_upper a [2,3,6,5,8] 30 (by decide) (fin9_cases _
  node91
  node92
  (invalid_upper a [2,3,6,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,8,3] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut94 [2,3,6,5,8,4] [2,0,6,1,7,4] 30 (by decide +kernel) node93)
  (invalid_upper a [2,3,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,8,6] 30 (by decide +kernel))
  node94
  (invalid_upper a [2,3,6,5,8,8] 30 (by decide +kernel)))

theorem node96 : UpperPrefix a [2,3,6,5] 30 :=
  branch_upper a [2,3,6,5] 30 (by decide) (fin9_cases _
  node82
  node85
  (invalid_upper a [2,3,6,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,5,6] 30 (by decide +kernel))
  node90
  node95)

def cert97 : Local := ⟨⟨0,497,432,353,450,0,305,113,177⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(1,5,4)]⟩
theorem node97 : UpperPrefix a [2,3,6,7,0,1] 30 :=
  local_sound a [2,3,6,7,0,1] 30 cert97 (by decide +kernel)

def cert98 : Leaf := ⟨⟨0,225,170,99,202,0,298,106,170⟩,[(0,1),(5,3)],[(2,0,0),(4,5,5)],⟨7,14,69,152,49,56,482,418,354⟩,⟨7,14,69,152,49,56,192,384,320⟩,[⟨8,1181761956245388103111,⟨55,63,127,187,49,56,255,191,127⟩⟩,⟨0,1219570781303936681772032,⟨454,494,68,184,48,56,192,384,320⟩⟩]⟩
theorem node98 : UpperPrefix a [2,3,6,7,0,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,4] 30 cert98 (by decide +kernel)

def cert99 : Leaf := ⟨⟨0,177,186,289,136,145,57,57,185⟩,[(0,1)],[(2,0,0),(1,6,2)],⟨7,14,69,152,49,296,194,432,368⟩,⟨7,14,69,152,49,296,194,384,320⟩,[⟨6,1212467609119021780175879,⟨7,15,31,184,49,424,187,424,440⟩⟩,⟨8,1181889786609705440379,⟨7,79,69,223,55,127,199,132,69⟩⟩]⟩
theorem node99 : UpperPrefix a [2,3,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,1] 30 cert99 (by decide +kernel)

def cert100 : Leaf := ⟨⟨0,496,442,0,458,210,0,122,186⟩,[(0,1),(3,6),(6,3)],[(2,0,0)],⟨7,14,69,152,49,296,208,418,354⟩,⟨7,14,69,152,49,296,208,384,320⟩,[⟨0,1238506769349207993093120,⟨422,494,494,216,248,360,216,416,360⟩⟩]⟩
theorem node100 : UpperPrefix a [2,3,6,7,0,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,4] 30 cert100 (by decide +kernel)

def cert101 : Leaf := ⟨⟨0,113,58,99,74,82,282,120,58⟩,[(0,1)],[(2,0,0),(8,5,6)],⟨7,14,69,152,49,296,224,386,336⟩,⟨7,14,69,152,49,296,224,386,320⟩,[⟨7,1530047894584238298645731,⟨311,319,341,25,51,319,375,311,341⟩⟩,⟨0,1323465311970033419682816,⟨230,494,68,504,368,360,224,482,320⟩⟩]⟩
theorem node101 : UpperPrefix a [2,3,6,7,0,8,5,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,0,8,5,1] 30 cert101 (by decide +kernel)

def cert102 : Local := ⟨⟨0,225,170,0,202,195,267,107,171⟩,[(0,1),(3,7)],[(2,0,0),(8,5,6),(4,7,3)]⟩
theorem node102 : UpperPrefix a [2,3,6,7,0,8,5,4] 30 :=
  local_sound a [2,3,6,7,0,8,5,4] 30 cert102 (by decide +kernel)

theorem node103 : UpperPrefix a [2,3,6,7,0,8,5] 30 :=
  branch_upper a [2,3,6,7,0,8,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,8,5,0] 30 (by decide +kernel))
  node101
  (invalid_upper a [2,3,6,7,0,8,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,5,3] 30 (by decide +kernel))
  node102
  (invalid_upper a [2,3,6,7,0,8,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,5,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,5,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,5,8] 30 (by decide +kernel)))

theorem node104 : UpperPrefix a [2,3,6,7,0,8] 30 :=
  branch_upper a [2,3,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,8,0] 30 (by decide +kernel))
  node99
  (invalid_upper a [2,3,6,7,0,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,3] 30 (by decide +kernel))
  node100
  node103
  (invalid_upper a [2,3,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,8,8] 30 (by decide +kernel)))

theorem node105 : UpperPrefix a [2,3,6,7,0] 30 :=
  branch_upper a [2,3,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,0,0] 30 (by decide +kernel))
  node97
  (invalid_upper a [2,3,6,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,3] 30 (by decide +kernel))
  node98
  (invalid_upper a [2,3,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,0,7] 30 (by decide +kernel))
  node104)

def cert106 : Leaf := ⟨⟨0,241,178,96,201,210,304,112,176⟩,[(0,1)],[(2,0,0),(3,1,4)],⟨7,14,69,152,50,41,496,432,368⟩,⟨7,14,69,152,50,41,192,384,320⟩,[⟨8,1181761956245388103111,⟨55,63,127,187,51,57,255,191,127⟩⟩,⟨0,1285813291192733985145856,⟨6,14,68,472,506,40,192,384,320⟩⟩,⟨1,1285813291192733985144833,⟨5,12,69,472,504,41,192,384,320⟩⟩]⟩
theorem node106 : UpperPrefix a [2,3,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,0] 30 cert106 (by decide +kernel)

def cert107 : Leaf := ⟨⟨0,225,162,99,201,0,291,99,163⟩,[(0,1),(5,3)],[(2,0,0),(3,1,4),(4,5,5)],⟨7,14,69,152,50,56,481,417,353⟩,⟨7,14,69,152,50,56,192,384,320⟩,[⟨8,1181761956245388103111,⟨55,63,127,187,51,56,255,191,127⟩⟩]⟩
theorem node107 : UpperPrefix a [2,3,6,7,1,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,4] 30 cert107 (by decide +kernel)

def cert108 : Local := ⟨⟨0,496,0,354,456,210,306,114,178⟩,[(0,1),(2,6)],[(2,0,0),(3,1,4),(0,6,2)]⟩
theorem node108 : UpperPrefix a [2,3,6,7,1,8,0] 30 :=
  local_sound a [2,3,6,7,1,8,0] 30 cert108 (by decide +kernel)

def cert109 : Leaf := ⟨⟨0,497,434,0,457,209,0,113,177⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(3,1,4)],⟨7,14,69,152,50,296,208,417,353⟩,⟨7,14,69,152,50,296,208,384,320⟩,[⟨1,1229043301409016693915649,⟨421,492,493,216,48,360,216,416,360⟩⟩]⟩
theorem node109 : UpperPrefix a [2,3,6,7,1,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8,4] 30 cert109 (by decide +kernel)

def cert110 : Leaf := ⟨⟨0,97,34,99,73,83,275,115,51⟩,[(0,1)],[(2,0,0),(3,1,4),(8,5,6)],⟨7,14,69,152,50,296,224,401,337⟩,⟨7,14,69,152,50,296,224,384,320⟩,[⟨7,1530047894575442205623395,⟨311,319,341,24,51,319,375,260,341⟩⟩,⟨4,1210107565282752258393187,⟨7,15,69,136,35,303,231,388,325⟩⟩]⟩
theorem node110 : UpperPrefix a [2,3,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,1,8,5] 30 cert110 (by decide +kernel)

theorem node111 : UpperPrefix a [2,3,6,7,1,8] 30 :=
  branch_upper a [2,3,6,7,1,8] 30 (by decide) (fin9_cases _
  node108
  (invalid_upper a [2,3,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,3] 30 (by decide +kernel))
  node109
  node110
  (invalid_upper a [2,3,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,8,8] 30 (by decide +kernel)))

theorem node112 : UpperPrefix a [2,3,6,7,1] 30 :=
  branch_upper a [2,3,6,7,1] 30 (by decide) (fin9_cases _
  node106
  (invalid_upper a [2,3,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,3] 30 (by decide +kernel))
  node107
  (invalid_upper a [2,3,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,1,7] 30 (by decide +kernel))
  node111)

def cert113 : Leaf := ⟨⟨0,225,170,289,137,128,41,57,185⟩,[(0,1)],[(2,0,0),(8,4,3),(1,6,2)],⟨7,14,69,152,304,41,194,432,368⟩,⟨7,14,69,152,304,41,194,384,320⟩,[⟨4,1210107709749784066151547,⟨39,111,69,239,295,111,231,388,325⟩⟩,⟨6,1212615171896186009289731,⟨39,47,37,152,440,41,171,408,440⟩⟩]⟩
theorem node113 : UpperPrefix a [2,3,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,0,1] 30 cert113 (by decide +kernel)

def cert114 : Leaf := ⟨⟨0,241,184,0,203,208,0,123,187⟩,[(0,1),(3,6),(6,3)],[(2,0,0),(8,4,3),(8,4,6)],⟨7,14,69,152,304,41,208,418,354⟩,⟨7,14,69,152,304,41,208,384,320⟩,[⟨1,1210107709539785848651777,⟨37,108,109,216,308,109,216,384,328⟩⟩]⟩
theorem node114 : UpperPrefix a [2,3,6,7,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,0,4] 30 cert114 (by decide +kernel)

def cert115 : Leaf := ⟨⟨0,224,170,354,202,194,10,122,186⟩,[(0,1)],[(2,0,0),(8,4,3)],⟨7,14,69,152,304,41,224,402,338⟩,⟨7,14,69,152,304,41,224,384,320⟩,[⟨0,1380445664758226779901440,⟨398,398,478,216,504,506,504,384,344⟩⟩,⟨4,1210107709749784066151547,⟨39,111,69,239,295,111,231,388,325⟩⟩]⟩
theorem node115 : UpperPrefix a [2,3,6,7,8,0,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,0,5] 30 cert115 (by decide +kernel)

theorem node116 : UpperPrefix a [2,3,6,7,8,0] 30 :=
  branch_upper a [2,3,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,6,7,8,0,0] 30 (by decide +kernel))
  node113
  (invalid_upper a [2,3,6,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,0,3] 30 (by decide +kernel))
  node114
  node115
  (invalid_upper a [2,3,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,0,8] 30 (by decide +kernel)))

def cert117 : Local := ⟨⟨0,240,0,354,194,0,50,114,178⟩,[(0,1),(2,6),(5,1)],[(2,0,0),(3,1,5),(8,4,3),(0,6,2)]⟩
theorem node117 : UpperPrefix a [2,3,6,7,8,1,0] 30 :=
  local_sound a [2,3,6,7,8,1,0] 30 cert117 (by decide +kernel)

def cert118 : Local := ⟨⟨0,241,178,0,195,0,0,115,179⟩,[(0,1),(3,6),(5,1),(6,3)],[(2,0,0),(3,1,5),(8,4,3),(8,4,6)]⟩
theorem node118 : UpperPrefix a [2,3,6,7,8,1,4] 30 :=
  local_sound a [2,3,6,7,8,1,4] 30 cert118 (by decide +kernel)

def cert119 : Leaf := ⟨⟨0,225,162,355,195,0,3,115,179⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(8,4,3)],⟨7,14,69,152,304,42,224,401,337⟩,⟨7,14,69,152,304,42,224,384,320⟩,[⟨4,1210107709749784066151547,⟨39,111,69,239,295,111,231,388,325⟩⟩]⟩
theorem node119 : UpperPrefix a [2,3,6,7,8,1,5] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,1,5] 30 cert119 (by decide +kernel)

theorem node120 : UpperPrefix a [2,3,6,7,8,1] 30 :=
  branch_upper a [2,3,6,7,8,1] 30 (by decide) (fin9_cases _
  node117
  (invalid_upper a [2,3,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,3] 30 (by decide +kernel))
  node118
  node119
  (invalid_upper a [2,3,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,1,8] 30 (by decide +kernel)))

def cert121 : Leaf := ⟨⟨0,224,170,354,202,0,43,107,171⟩,[(0,1),(5,3)],[(2,0,0),(8,4,3),(4,5,5)],⟨7,14,69,152,304,56,227,419,355⟩,⟨7,14,69,152,304,56,192,384,320⟩,[⟨0,1210107581354339407498240,⟨6,46,110,184,304,56,248,440,376⟩⟩]⟩
theorem node121 : UpperPrefix a [2,3,6,7,8,4] 30 :=
  Boolean.leaf_sound a [2,3,6,7,8,4] 30 cert121 (by decide +kernel)

theorem node122 : UpperPrefix a [2,3,6,7,8] 30 :=
  branch_upper a [2,3,6,7,8] 30 (by decide) (fin9_cases _
  node116
  node120
  (invalid_upper a [2,3,6,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,3] 30 (by decide +kernel))
  node121
  (invalid_upper a [2,3,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,8,8] 30 (by decide +kernel)))

theorem node123 : UpperPrefix a [2,3,6,7] 30 :=
  branch_upper a [2,3,6,7] 30 (by decide) (fin9_cases _
  node105
  node112
  (invalid_upper a [2,3,6,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,6,7,7] 30 (by decide +kernel))
  node122)

def cert124 : Local := ⟨⟨0,497,432,225,450,0,305,113,177⟩,[(0,1),(5,1)],[(2,0,0),(3,1,5),(1,5,4)]⟩
theorem node124 : UpperPrefix a [2,3,6,8,0,1] 30 :=
  local_sound a [2,3,6,8,0,1] 30 cert124 (by decide +kernel)

def cert125 : Leaf := ⟨⟨0,353,298,99,330,0,298,106,170⟩,[(0,1),(5,3)],[(2,0,0),(4,5,5)],⟨7,14,69,280,49,56,226,418,482⟩,⟨7,14,69,280,49,56,192,384,320⟩,[⟨7,1208926989811644456211919,⟨55,63,119,319,49,59,127,319,383⟩⟩,⟨0,1219570781303936681772032,⟨454,494,68,312,48,56,192,384,320⟩⟩]⟩
theorem node125 : UpperPrefix a [2,3,6,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,4] 30 cert125 (by decide +kernel)

def cert126 : Leaf := ⟨⟨0,241,186,161,136,272,56,56,185⟩,[(0,1)],[(2,0,0),(8,3,5),(1,6,2)],⟨7,14,69,280,49,168,194,432,368⟩,⟨7,14,69,280,49,168,194,384,320⟩,[⟨6,1212541396447357907764227,⟨55,191,21,440,49,168,179,424,440⟩⟩,⟨0,1210181388640787264177152,⟨102,238,68,440,48,168,226,384,320⟩⟩]⟩
theorem node126 : UpperPrefix a [2,3,6,8,0,7,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,1] 30 cert126 (by decide +kernel)

def cert127 : Leaf := ⟨⟨0,240,186,224,200,336,42,120,184⟩,[(0,1)],[(2,0,0),(8,3,5)],⟨7,14,69,280,49,168,208,386,352⟩,⟨7,14,69,280,49,168,208,386,320⟩,[⟨0,1644630136568359917980672,⟨422,430,494,376,504,424,504,418,360⟩⟩,⟨1,1531228492874671409070081,⟨285,284,381,280,57,168,504,424,360⟩⟩]⟩
theorem node127 : UpperPrefix a [2,3,6,8,0,7,4,1] 30 :=
  Boolean.leaf_sound a [2,3,6,8,0,7,4,1] 30 cert127 (by decide +kernel)

#print axioms node127
end Delivery.FiniteExclusion.Sharp3x3x3
