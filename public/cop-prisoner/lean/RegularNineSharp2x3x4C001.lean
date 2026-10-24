import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C000
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
theorem node64 : UpperPrefix a [2,3,5,7,6,8,0] 30 :=
  branch_upper a [2,3,5,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,6,8,0,0] 30 (by decide +kernel))
  node62
  (invalid_upper a [2,3,5,7,6,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,0,3] 30 (by decide +kernel))
  node63
  (invalid_upper a [2,3,5,7,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,0,8] 30 (by decide +kernel)))

def cert65 : Leaf := ⟨⟨376,372,336,356,416,16,305,112,80⟩,[],[(3,1,0),(0,7,6)],⟨7,11,44,152,84,352,194,385,304⟩,⟨7,11,44,152,84,352,194,385,288⟩,[⟨1,1795708682097153715208193,⟨389,397,316,444,380,380,508,385,308⟩⟩,⟨7,1322263769814955715468319,⟨7,271,303,319,375,352,67,257,288⟩⟩,⟨2,1323462866796910733165569,⟨227,491,296,440,368,352,226,481,288⟩⟩]⟩
theorem node65 : UpperPrefix a [2,3,5,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,8,1,0] 30 cert65 (by decide +kernel)

def cert66 : Leaf := ⟨⟨328,324,323,0,387,7,261,103,71⟩,[(3,7)],[(3,1,0),(4,7,3)],⟨7,11,44,152,84,352,194,400,289⟩,⟨7,11,44,152,84,352,194,400,288⟩,[⟨7,2247847602709205991037983,⟨263,271,303,319,375,352,355,305,288⟩⟩,⟨5,1210110014116441126673429,⟨23,75,95,219,87,320,202,475,256⟩⟩]⟩
theorem node66 : UpperPrefix a [2,3,5,7,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,8,1,4] 30 cert66 (by decide +kernel)

theorem node67 : UpperPrefix a [2,3,5,7,6,8,1] 30 :=
  branch_upper a [2,3,5,7,6,8,1] 30 (by decide) (fin9_cases _
  node65
  (invalid_upper a [2,3,5,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,3] 30 (by decide +kernel))
  node66
  (invalid_upper a [2,3,5,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,1,8] 30 (by decide +kernel)))

def cert68 : Leaf := ⟨⟨424,420,387,0,419,135,0,39,135⟩,[(3,6),(6,3)],[(3,1,0)],⟨7,11,44,152,84,352,208,387,291⟩,⟨7,11,44,152,84,352,208,384,288⟩,[⟨4,1342619754150994507734047,⟨391,399,431,431,487,352,481,384,288⟩⟩,⟨6,1382961627705053178559797,⟨391,139,431,155,415,431,155,385,423⟩⟩]⟩
theorem node68 : UpperPrefix a [2,3,5,7,6,8,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,6,8,4] 30 cert68 (by decide +kernel)

theorem node69 : UpperPrefix a [2,3,5,7,6,8] 30 :=
  branch_upper a [2,3,5,7,6,8] 30 (by decide) (fin9_cases _
  node64
  node67
  (invalid_upper a [2,3,5,7,6,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,3] 30 (by decide +kernel))
  node68
  (invalid_upper a [2,3,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,8,8] 30 (by decide +kernel)))

theorem node70 : UpperPrefix a [2,3,5,7,6] 30 :=
  branch_upper a [2,3,5,7,6] 30 (by decide) (fin9_cases _
  node56
  node60
  (invalid_upper a [2,3,5,7,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,3] 30 (by decide +kernel))
  node61
  (invalid_upper a [2,3,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,6,7] 30 (by decide +kernel))
  node69)

def cert71 : Leaf := ⟨⟨200,196,192,324,224,134,5,84,212⟩,[],[(3,1,0),(5,2,4),(8,4,3),(1,6,5)],⟨7,11,44,152,276,97,194,464,368⟩,⟨7,11,44,152,276,97,194,384,288⟩,[⟨0,1361518440669786902889472,⟨30,10,444,152,284,508,218,412,444⟩⟩,⟨4,1210107712142321275903071,⟨39,111,111,239,295,97,231,384,288⟩⟩]⟩
theorem node71 : UpperPrefix a [2,3,5,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,0,1] 30 cert71 (by decide +kernel)

def cert72 : Leaf := ⟨⟨216,208,211,0,227,146,0,83,211⟩,[(3,6),(6,3)],[(3,1,0),(5,2,4),(8,4,3),(8,4,6)],⟨7,11,44,152,276,97,208,450,354⟩,⟨7,11,44,152,276,97,208,384,288⟩,[⟨2,1389908412186242393850881,⟨419,491,490,216,472,491,216,384,418⟩⟩]⟩
theorem node72 : UpperPrefix a [2,3,5,7,8,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,0,4] 30 cert72 (by decide +kernel)

theorem node73 : UpperPrefix a [2,3,5,7,8,0] 30 :=
  branch_upper a [2,3,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,8,0,0] 30 (by decide +kernel))
  node71
  (invalid_upper a [2,3,5,7,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,3] 30 (by decide +kernel))
  node72
  (invalid_upper a [2,3,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,0,8] 30 (by decide +kernel)))

def cert74 : Leaf := ⟨⟨200,196,192,324,224,133,6,84,212⟩,[],[(3,1,0),(5,2,4),(8,4,3),(0,6,5)],⟨7,11,44,152,276,98,193,464,368⟩,⟨7,11,44,152,276,98,193,384,288⟩,[⟨1,1361518440669786902888449,⟨29,9,444,152,284,508,217,412,444⟩⟩,⟨4,1210107709890521462217791,⟨39,111,111,239,295,103,193,384,289⟩⟩]⟩
theorem node74 : UpperPrefix a [2,3,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,1,0] 30 cert74 (by decide +kernel)

def cert75 : Leaf := ⟨⟨152,148,147,0,163,149,0,87,215⟩,[(3,6),(6,3)],[(3,1,0),(5,2,4),(8,4,3),(8,4,6)],⟨7,11,44,152,276,98,208,449,353⟩,⟨7,11,44,152,276,98,208,384,288⟩,[⟨6,1210106412379965043629365,⟨7,11,47,155,279,47,155,411,311⟩⟩]⟩
theorem node75 : UpperPrefix a [2,3,5,7,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,1,4] 30 cert75 (by decide +kernel)

theorem node76 : UpperPrefix a [2,3,5,7,8,1] 30 :=
  branch_upper a [2,3,5,7,8,1] 30 (by decide) (fin9_cases _
  node74
  (invalid_upper a [2,3,5,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,3] 30 (by decide +kernel))
  node75
  (invalid_upper a [2,3,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,1,8] 30 (by decide +kernel)))

def cert77 : Local := ⟨⟨200,196,209,325,225,133,6,69,197⟩,[],[(3,1,0),(5,2,4),(8,4,3),(4,5,2),(1,7,6)]⟩
theorem node77 : UpperPrefix a [2,3,5,7,8,4,0,1] 30 :=
  local_sound a [2,3,5,7,8,4,0,1] 30 cert77 (by decide +kernel)

def cert78 : Leaf := ⟨⟨136,132,147,263,163,135,6,7,135⟩,[],[(3,1,0),(5,2,4),(8,4,3),(4,5,2)],⟨7,11,44,152,276,112,193,448,290⟩,⟨7,11,44,152,276,112,193,448,288⟩,[⟨6,1380111605765814891961653,⟨279,27,319,155,279,319,155,411,311⟩⟩]⟩
theorem node78 : UpperPrefix a [2,3,5,7,8,4,0,6] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,4,0,6] 30 cert78 (by decide +kernel)

theorem node79 : UpperPrefix a [2,3,5,7,8,4,0] 30 :=
  branch_upper a [2,3,5,7,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,7,8,4,0,0] 30 (by decide +kernel))
  node77
  (invalid_upper a [2,3,5,7,8,4,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,5] 30 (by decide +kernel))
  node78
  (invalid_upper a [2,3,5,7,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,0,8] 30 (by decide +kernel)))

def cert80 : Leaf := ⟨⟨8,4,211,327,99,135,5,71,71⟩,[],[(3,1,0),(5,2,4),(8,4,3),(4,5,2)],⟨7,11,44,152,276,112,194,449,353⟩,⟨7,11,44,152,276,112,194,384,288⟩,[⟨7,1360042701115237799566357,⟨23,11,319,27,279,369,66,256,288⟩⟩,⟨6,1210106412362347079277589,⟨7,11,47,155,279,49,130,384,288⟩⟩]⟩
theorem node80 : UpperPrefix a [2,3,5,7,8,4,1] 30 :=
  Boolean.leaf_sound a [2,3,5,7,8,4,1] 30 cert80 (by decide +kernel)

theorem node81 : UpperPrefix a [2,3,5,7,8,4] 30 :=
  branch_upper a [2,3,5,7,8,4] 30 (by decide) (fin9_cases _
  node79
  node80
  (invalid_upper a [2,3,5,7,8,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,4,8] 30 (by decide +kernel)))

theorem node82 : UpperPrefix a [2,3,5,7,8] 30 :=
  branch_upper a [2,3,5,7,8] 30 (by decide) (fin9_cases _
  node73
  node76
  (invalid_upper a [2,3,5,7,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,3] 30 (by decide +kernel))
  node81
  (invalid_upper a [2,3,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,8,8] 30 (by decide +kernel)))

theorem node83 : UpperPrefix a [2,3,5,7] 30 :=
  branch_upper a [2,3,5,7] 30 (by decide) (fin9_cases _
  node46
  node52
  (invalid_upper a [2,3,5,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,7,5] 30 (by decide +kernel))
  node70
  (invalid_upper a [2,3,5,7,7] 30 (by decide +kernel))
  node82)

def cert84 : Leaf := ⟨⟨280,272,275,35,0,403,275,83,211⟩,[(4,0)],[(2,0,4),(3,1,0)],⟨7,11,44,280,21,242,210,466,498⟩,⟨7,11,44,280,21,96,192,384,288⟩,[⟨5,1210181603336169347619861,⟨87,219,223,475,87,64,192,384,256⟩⟩,⟨6,1210106412389680318487965,⟨23,27,63,287,23,34,155,415,319⟩⟩,⟨7,1208926973690467514031517,⟨23,27,63,287,23,98,91,287,319⟩⟩]⟩
theorem node84 : UpperPrefix a [2,3,5,8,0] 30 :=
  Boolean.leaf_sound a [2,3,5,8,0] 30 cert84 (by decide +kernel)

def cert85 : Leaf := ⟨⟨0,500,464,228,0,404,308,116,212⟩,[(0,4),(4,0)],[(3,1,0),(3,1,4)],⟨7,11,44,280,22,97,208,464,496⟩,⟨7,11,44,280,22,97,192,384,288⟩,[⟨1,1285887222354585648103425,⟨37,237,236,476,508,97,192,384,288⟩⟩,⟨0,1361592984221965012173824,⟨86,218,492,476,86,508,192,388,492⟩⟩]⟩
theorem node85 : UpperPrefix a [2,3,5,8,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,8,1,0] 30 cert85 (by decide +kernel)

def cert86 : Leaf := ⟨⟨0,324,339,103,0,263,263,71,199⟩,[(0,4),(4,0)],[(3,1,0),(3,1,4),(4,5,2)],⟨7,11,44,280,22,112,193,449,481⟩,⟨7,11,44,280,22,112,192,384,288⟩,[⟨7,1208926975948864414260733,⟨23,27,63,287,23,119,127,287,319⟩⟩,⟨5,1210181603336169347619861,⟨87,219,223,475,87,81,192,384,256⟩⟩]⟩
theorem node86 : UpperPrefix a [2,3,5,8,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,1,4] 30 cert86 (by decide +kernel)

def cert87 : Leaf := ⟨⟨0,340,339,103,0,0,279,87,87⟩,[(0,4),(4,0),(5,6)],[(3,1,0),(3,1,4),(7,5,5)],⟨7,11,44,280,22,224,209,465,369⟩,⟨7,11,44,280,22,224,192,384,288⟩,[⟨5,1210181603336169347619861,⟨87,219,223,475,87,192,192,384,256⟩⟩]⟩
theorem node87 : UpperPrefix a [2,3,5,8,1,7] 30 :=
  Boolean.leaf_sound a [2,3,5,8,1,7] 30 cert87 (by decide +kernel)

theorem node88 : UpperPrefix a [2,3,5,8,1] 30 :=
  branch_upper a [2,3,5,8,1] 30 (by decide) (fin9_cases _
  node85
  (invalid_upper a [2,3,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,1,3] 30 (by decide +kernel))
  node86
  (invalid_upper a [2,3,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,1,6] 30 (by decide +kernel))
  node87
  (invalid_upper a [2,3,5,8,1,8] 30 (by decide +kernel)))

def cert89 : Leaf := ⟨⟨328,324,320,228,384,262,276,84,212⟩,[],[(3,1,0),(1,6,5)],⟨7,11,44,280,84,97,194,400,432⟩,⟨7,11,44,280,84,97,194,384,288⟩,[⟨0,1383036621648346697696256,⟨478,218,444,412,476,508,194,396,444⟩⟩,⟨5,1210181603336169347619861,⟨87,219,223,475,87,81,194,384,256⟩⟩,⟨4,1210107568097501943700511,⟨7,15,47,303,103,97,227,384,288⟩⟩,⟨7,1208926976477884044024863,⟨7,15,47,319,119,97,99,256,288⟩⟩]⟩
theorem node89 : UpperPrefix a [2,3,5,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,8,6,0,1] 30 cert89 (by decide +kernel)

def cert90 : Leaf := ⟨⟨8,4,67,167,387,6,263,7,135⟩,[],[(3,1,0)],⟨7,11,44,280,84,97,208,386,418⟩,⟨7,11,44,280,84,97,208,384,288⟩,[⟨4,1342619754150994507734047,⟨391,399,431,431,487,225,481,384,288⟩⟩,⟨5,1210181603336169347619861,⟨87,219,223,475,87,81,209,384,256⟩⟩,⟨6,1380674231439904595819541,⟨391,139,431,411,415,419,155,384,416⟩⟩,⟨7,1208926976477884044024863,⟨7,15,47,319,119,97,113,256,288⟩⟩,⟨8,1181748483972280622111,⟨7,15,47,63,119,97,241,128,32⟩⟩]⟩
theorem node90 : UpperPrefix a [2,3,5,8,6,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,6,0,4] 30 cert90 (by decide +kernel)

theorem node91 : UpperPrefix a [2,3,5,8,6,0] 30 :=
  branch_upper a [2,3,5,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,8,6,0,0] 30 (by decide +kernel))
  node89
  (invalid_upper a [2,3,5,8,6,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,0,3] 30 (by decide +kernel))
  node90
  (invalid_upper a [2,3,5,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,0,8] 30 (by decide +kernel)))

def cert92 : Leaf := ⟨⟨328,324,320,228,384,261,276,84,212⟩,[],[(3,1,0),(0,6,5)],⟨7,11,44,280,84,98,193,400,432⟩,⟨7,11,44,280,84,98,193,384,288⟩,[⟨1,1383036621648346697695233,⟨477,217,444,412,476,508,217,396,444⟩⟩,⟨5,1210181603336169347619861,⟨87,219,223,475,87,66,209,384,256⟩⟩,⟨4,1210107565845702130015263,⟨7,15,47,303,103,99,193,384,288⟩⟩,⟨7,1208926974226084230339615,⟨7,15,47,319,119,99,65,256,288⟩⟩]⟩
theorem node92 : UpperPrefix a [2,3,5,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,8,6,1,0] 30 cert92 (by decide +kernel)

def cert93 : Leaf := ⟨⟨8,4,67,167,387,5,263,7,135⟩,[],[(3,1,0)],⟨7,11,44,280,84,98,208,385,417⟩,⟨7,11,44,280,84,98,208,384,288⟩,[⟨4,1796852377970218693041183,⟨391,399,431,431,487,483,481,384,416⟩⟩,⟨5,1210181603336169347619861,⟨87,219,223,475,87,66,209,384,256⟩⟩,⟨6,1229263356082896596155413,⟨391,139,431,411,415,34,155,384,288⟩⟩,⟨7,1208926974226084230339615,⟨7,15,47,319,119,99,113,256,288⟩⟩,⟨8,1181746232172466936863,⟨7,15,47,63,119,99,241,128,32⟩⟩]⟩
theorem node93 : UpperPrefix a [2,3,5,8,6,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,6,1,4] 30 cert93 (by decide +kernel)

theorem node94 : UpperPrefix a [2,3,5,8,6,1] 30 :=
  branch_upper a [2,3,5,8,6,1] 30 (by decide) (fin9_cases _
  node92
  (invalid_upper a [2,3,5,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,1,3] 30 (by decide +kernel))
  node93
  (invalid_upper a [2,3,5,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,1,8] 30 (by decide +kernel)))

def cert95 : Leaf := ⟨⟨264,260,275,167,387,0,263,7,135⟩,[(5,4)],[(3,1,0),(6,4,5),(4,5,2)],⟨7,11,44,280,84,112,195,387,419⟩,⟨7,11,44,280,84,112,192,384,288⟩,[⟨5,1210181603336169347619861,⟨87,219,223,475,87,81,192,384,256⟩⟩,⟨7,1208926974226084230339615,⟨7,15,47,319,119,113,64,256,288⟩⟩]⟩
theorem node95 : UpperPrefix a [2,3,5,8,6,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,6,4] 30 cert95 (by decide +kernel)

def cert96 : Leaf := ⟨⟨8,4,339,103,259,0,279,23,87⟩,[(5,6)],[(3,1,0),(7,5,5)],⟨7,11,44,280,84,224,211,403,307⟩,⟨7,11,44,280,84,224,192,384,288⟩,[⟨5,1210181603336169347619861,⟨87,219,223,475,87,192,192,384,256⟩⟩,⟨6,1210180199338641917484053,⟨7,139,175,411,23,160,128,384,288⟩⟩,⟨4,1210107567534551988182037,⟨7,11,47,267,103,224,224,384,288⟩⟩,⟨8,1181747921022325103637,⟨7,11,47,27,119,224,224,128,32⟩⟩]⟩
theorem node96 : UpperPrefix a [2,3,5,8,6,7] 30 :=
  Boolean.leaf_sound a [2,3,5,8,6,7] 30 cert96 (by decide +kernel)

theorem node97 : UpperPrefix a [2,3,5,8,6] 30 :=
  branch_upper a [2,3,5,8,6] 30 (by decide) (fin9_cases _
  node91
  node94
  (invalid_upper a [2,3,5,8,6,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,3] 30 (by decide +kernel))
  node95
  (invalid_upper a [2,3,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,6,6] 30 (by decide +kernel))
  node96
  (invalid_upper a [2,3,5,8,6,8] 30 (by decide +kernel)))

def cert98 : Leaf := ⟨⟨232,228,192,228,96,134,37,116,212⟩,[],[(3,1,0),(1,6,5)],⟨7,11,44,280,148,97,194,464,368⟩,⟨7,11,44,280,148,97,194,384,288⟩,[⟨8,1182037000221456079967,⟨7,47,47,127,247,113,247,128,32⟩⟩,⟨0,1361518440669778312954880,⟨30,10,444,284,156,508,218,412,444⟩⟩,⟨4,1210107856609353072647263,⟨7,47,47,367,231,97,231,384,288⟩⟩]⟩
theorem node98 : UpperPrefix a [2,3,5,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,0,1] 30 cert98 (by decide +kernel)

def cert99 : Leaf := ⟨⟨72,68,83,103,323,6,0,87,87⟩,[(6,4)],[(3,1,0),(7,4,6)],⟨7,11,44,280,148,97,208,450,354⟩,⟨7,11,44,280,148,97,208,384,288⟩,[⟨5,1210181855537679760890901,⟨87,203,223,475,215,65,209,384,256⟩⟩,⟨8,1182036995823409568799,⟨7,47,47,127,247,97,241,128,32⟩⟩,⟨4,1210107567534551988182037,⟨7,11,47,267,135,97,225,384,288⟩⟩]⟩
theorem node99 : UpperPrefix a [2,3,5,8,7,0,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,0,4] 30 cert99 (by decide +kernel)

theorem node100 : UpperPrefix a [2,3,5,8,7,0] 30 :=
  branch_upper a [2,3,5,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,3,5,8,7,0,0] 30 (by decide +kernel))
  node98
  (invalid_upper a [2,3,5,8,7,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,0,3] 30 (by decide +kernel))
  node99
  (invalid_upper a [2,3,5,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,0,8] 30 (by decide +kernel)))

def cert101 : Leaf := ⟨⟨200,196,192,228,320,133,6,84,212⟩,[],[(3,1,0),(0,6,5)],⟨7,11,44,280,148,98,193,464,368⟩,⟨7,11,44,280,148,98,193,384,288⟩,[⟨1,1361518440669778312953857,⟨29,9,444,284,156,508,217,412,444⟩⟩,⟨4,1210107854357553258961983,⟨7,47,47,367,231,103,193,384,289⟩⟩,⟨5,1210181891566476779854869,⟨87,203,223,475,215,66,193,384,256⟩⟩,⟨8,1182034744023595883583,⟨7,47,47,127,247,103,193,128,33⟩⟩]⟩
theorem node101 : UpperPrefix a [2,3,5,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,1,0] 30 cert101 (by decide +kernel)

def cert102 : Leaf := ⟨⟨72,68,83,103,323,21,0,87,87⟩,[(6,4)],[(3,1,0),(7,4,6)],⟨7,11,44,280,148,98,208,449,353⟩,⟨7,11,44,280,148,98,208,384,288⟩,[⟨5,1210181855537679760890901,⟨87,203,223,475,215,66,209,384,256⟩⟩,⟨8,1182034744023595883583,⟨7,47,47,127,247,103,241,128,33⟩⟩,⟨4,1210107565282752174496789,⟨7,11,47,267,135,98,193,384,288⟩⟩]⟩
theorem node102 : UpperPrefix a [2,3,5,8,7,1,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,1,4] 30 cert102 (by decide +kernel)

theorem node103 : UpperPrefix a [2,3,5,8,7,1] 30 :=
  branch_upper a [2,3,5,8,7,1] 30 (by decide) (fin9_cases _
  node101
  (invalid_upper a [2,3,5,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,1,3] 30 (by decide +kernel))
  node102
  (invalid_upper a [2,3,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,1,8] 30 (by decide +kernel)))

def cert104 : Leaf := ⟨⟨8,4,83,103,323,135,7,71,71⟩,[],[(3,1,0),(7,4,5),(4,5,2)],⟨7,11,44,280,148,112,195,451,355⟩,⟨7,11,44,280,148,112,192,384,288⟩,[⟨5,1210181891566476779854869,⟨87,203,223,475,215,81,192,384,256⟩⟩,⟨8,1182034744023595883551,⟨7,47,47,127,247,113,192,128,32⟩⟩,⟨6,1210106412362347079277589,⟨7,11,47,283,151,49,128,384,288⟩⟩]⟩
theorem node104 : UpperPrefix a [2,3,5,8,7,4] 30 :=
  Boolean.leaf_sound a [2,3,5,8,7,4] 30 cert104 (by decide +kernel)

theorem node105 : UpperPrefix a [2,3,5,8,7] 30 :=
  branch_upper a [2,3,5,8,7] 30 (by decide) (fin9_cases _
  node100
  node103
  (invalid_upper a [2,3,5,8,7,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,3] 30 (by decide +kernel))
  node104
  (invalid_upper a [2,3,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,7,8] 30 (by decide +kernel)))

theorem node106 : UpperPrefix a [2,3,5,8] 30 :=
  branch_upper a [2,3,5,8] 30 (by decide) (fin9_cases _
  node84
  node88
  (invalid_upper a [2,3,5,8,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,8,5] 30 (by decide +kernel))
  node97
  node105
  (invalid_upper a [2,3,5,8,8] 30 (by decide +kernel)))

theorem node107 : UpperPrefix a [2,3,5] 30 :=
  branch_upper a [2,3,5] 30 (by decide) (fin9_cases _
  node14
  node22
  (invalid_upper a [2,3,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,3,5,5] 30 (by decide +kernel))
  node42
  node83
  node106)

theorem node108 : UpperPrefix a [2,3] 30 :=
  branch_upper a [2,3] 30 (by decide) (fin9_cases _
  node2
  node9
  (invalid_upper a [2,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,3,3] 30 (by decide +kernel))
  node13
  node107
  (PrefixConjugacy.upper aut3 [2,3,6] [2,3,5] 30 (by decide +kernel) node107)
  (PrefixConjugacy.upper aut2 [2,3,7] [2,3,5] 30 (by decide +kernel) node107)
  (PrefixConjugacy.upper aut1 [2,3,8] [2,3,5] 30 (by decide +kernel) node107))

def cert109 : Leaf := ⟨⟨432,400,434,416,0,400,304,112,208⟩,[(4,2)],[(0,2,0),(1,3,2),(3,4,4)],⟨7,35,13,26,28,496,464,464,496⟩,⟨7,35,13,26,28,96,192,384,288⟩,[⟨2,1323666154991598990003201,⟨3,35,491,506,506,96,192,384,288⟩⟩,⟨6,1210106412396419590538667,⟨31,63,29,31,29,63,157,415,319⟩⟩]⟩
theorem node109 : UpperPrefix a [2,5,0,1,3] 30 :=
  Boolean.leaf_sound a [2,5,0,1,3] 30 cert109 (by decide +kernel)

def cert110 : Leaf := ⟨⟨104,88,98,96,40,408,312,120,216⟩,[],[(0,2,0),(1,3,2)],⟨7,35,13,26,84,504,472,408,440⟩,⟨7,35,13,26,84,96,192,384,288⟩,[⟨2,1323666154991598990003201,⟨3,35,491,506,506,96,192,384,288⟩⟩,⟨7,1208926973669770379806123,⟨15,63,13,31,84,127,85,271,319⟩⟩,⟨8,1181745675858616403371,⟨15,63,13,31,84,127,213,143,63⟩⟩,⟨4,1210107565282752176587785,⟨7,35,13,15,68,96,192,384,288⟩⟩]⟩
theorem node110 : UpperPrefix a [2,5,0,1,6] 30 :=
  Boolean.leaf_sound a [2,5,0,1,6] 30 cert110 (by decide +kernel)

def cert111 : Leaf := ⟨⟨168,152,162,160,40,408,312,120,216⟩,[],[(0,2,0),(1,3,2)],⟨7,35,13,26,148,376,472,472,376⟩,⟨7,35,13,26,148,96,192,384,288⟩,[⟨2,1323666154991598990003201,⟨3,35,491,506,506,96,192,384,288⟩⟩,⟨6,1210106412375562826433963,⟨7,47,13,31,157,63,157,415,303⟩⟩,⟨8,1181745682438258574763,⟨7,47,13,31,157,127,221,159,47⟩⟩,⟨4,1210107565282752176587785,⟨7,35,13,15,132,96,192,384,288⟩⟩]⟩
theorem node111 : UpperPrefix a [2,5,0,1,7] 30 :=
  Boolean.leaf_sound a [2,5,0,1,7] 30 cert111 (by decide +kernel)

def cert112 : Leaf := ⟨⟨296,280,290,288,40,408,312,120,216⟩,[],[(0,2,0),(1,3,2)],⟨7,35,13,26,276,248,216,472,504⟩,⟨7,35,13,26,276,96,192,384,288⟩,[⟨2,1323666154991598990003201,⟨3,35,491,506,506,96,192,384,288⟩⟩,⟨6,1210106412388789169309113,⟨7,35,13,31,287,39,157,415,319⟩⟩,⟨7,1208926973689576364852665,⟨7,35,13,31,287,103,93,287,319⟩⟩,⟨4,1210107565282752176587785,⟨7,35,13,15,260,96,192,384,288⟩⟩]⟩
theorem node112 : UpperPrefix a [2,5,0,1,8] 30 :=
  Boolean.leaf_sound a [2,5,0,1,8] 30 cert112 (by decide +kernel)

theorem node113 : UpperPrefix a [2,5,0,1] 30 :=
  branch_upper a [2,5,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,1,2] 30 (by decide +kernel))
  node109
  (invalid_upper a [2,5,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,1,5] 30 (by decide +kernel))
  node110
  node111
  node112)

def cert114 : Leaf := ⟨⟨0,472,498,416,0,408,312,120,216⟩,[(0,4),(4,0)],[(0,2,0),(0,2,4)],⟨7,35,13,88,22,504,472,408,440⟩,⟨7,35,13,88,22,96,192,384,288⟩,[⟨2,1323666154991598990003201,⟨3,35,491,504,506,96,192,384,288⟩⟩,⟨1,1323666154991598991048705,⟨5,33,493,504,508,96,192,384,288⟩⟩]⟩
theorem node114 : UpperPrefix a [2,5,0,6,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,1] 30 cert114 (by decide +kernel)

def cert115 : Leaf := ⟨⟨496,464,496,416,0,400,304,112,208⟩,[(4,2)],[(0,2,0),(3,4,4),(1,5,1)],⟨7,35,13,88,28,98,464,400,432⟩,⟨7,35,13,88,28,98,192,384,288⟩,[⟨2,1323666154850861501648385,⟨35,35,491,504,506,98,192,384,288⟩⟩]⟩
theorem node115 : UpperPrefix a [2,5,0,6,3,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,3,1] 30 cert115 (by decide +kernel)

def cert116 : Leaf := ⟨⟨496,464,498,0,0,0,306,114,210⟩,[(3,5),(4,2),(5,3)],[(0,2,0),(3,4,4)],⟨7,35,13,88,28,112,450,386,418⟩,⟨7,35,13,88,28,112,192,384,288⟩,[⟨2,1314212180639428630285313,⟨451,491,491,504,506,504,192,384,296⟩⟩]⟩
theorem node116 : UpperPrefix a [2,5,0,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,0,6,3,4] 30 cert116 (by decide +kernel)

def cert117 : Leaf := ⟨⟨368,336,370,290,0,0,306,114,82⟩,[(4,2),(5,6)],[(0,2,0),(3,4,4),(7,5,5)],⟨7,35,13,88,28,224,466,402,306⟩,⟨7,35,13,88,28,224,192,384,288⟩,[⟨2,1285813294288958727916545,⟨3,35,43,504,506,224,224,384,288⟩⟩]⟩
theorem node117 : UpperPrefix a [2,5,0,6,3,7] 30 :=
  Boolean.leaf_sound a [2,5,0,6,3,7] 30 cert117 (by decide +kernel)

def cert118 : Leaf := ⟨⟨240,208,242,162,0,146,50,114,210⟩,[(4,2)],[(0,2,0),(3,4,4)],⟨7,35,13,88,28,352,210,402,434⟩,⟨7,35,13,88,28,352,192,384,288⟩,[⟨2,1285813292037158914231297,⟨3,35,43,504,506,352,192,384,288⟩⟩,⟨8,1184051546209337886115,⟨23,63,29,92,28,127,221,223,63⟩⟩]⟩
theorem node118 : UpperPrefix a [2,5,0,6,3,8] 30 :=
  Boolean.leaf_sound a [2,5,0,6,3,8] 30 cert118 (by decide +kernel)

theorem node119 : UpperPrefix a [2,5,0,6,3] 30 :=
  branch_upper a [2,5,0,6,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,3,0] 30 (by decide +kernel))
  node115
  (invalid_upper a [2,5,0,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,3,3] 30 (by decide +kernel))
  node116
  (invalid_upper a [2,5,0,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,3,6] 30 (by decide +kernel))
  node117
  node118)

def cert120 : Leaf := ⟨⟨344,344,336,384,328,280,280,88,88⟩,[],[(0,2,0),(7,4,3),(1,5,1)],⟨7,35,13,88,148,98,472,408,312⟩,⟨7,35,13,88,148,98,192,384,288⟩,[⟨2,1323666154850861501648385,⟨35,35,491,504,506,98,192,384,288⟩⟩,⟨5,1212475664954864874554403,⟨7,7,13,88,220,79,216,476,477⟩⟩]⟩
theorem node120 : UpperPrefix a [2,5,0,6,7,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,1] 30 cert120 (by decide +kernel)

def cert121 : Leaf := ⟨⟨56,24,50,162,42,0,314,58,26⟩,[(5,3)],[(0,2,0),(6,3,5),(7,4,3)],⟨7,35,13,88,148,104,466,402,306⟩,⟨7,35,13,88,148,104,192,384,288⟩,[⟨2,1285813292037158914231297,⟨3,35,43,504,506,104,192,384,288⟩⟩,⟨8,1181748215704421326335,⟨7,47,47,127,151,127,255,151,47⟩⟩]⟩
theorem node121 : UpperPrefix a [2,5,0,6,7,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,3] 30 cert121 (by decide +kernel)

def cert122 : Leaf := ⟨⟨120,88,114,0,106,0,314,122,90⟩,[(3,5),(5,3)],[(0,2,0),(7,4,3),(7,4,5)],⟨7,35,13,88,148,112,458,394,298⟩,⟨7,35,13,88,148,112,192,384,288⟩,[⟨2,1314202939252993266027521,⟨451,491,491,504,506,504,192,384,296⟩⟩,⟨8,1181748215704421326335,⟨7,47,47,127,151,127,255,151,47⟩⟩]⟩
theorem node122 : UpperPrefix a [2,5,0,6,7,4] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,4] 30 cert122 (by decide +kernel)

def cert123 : Leaf := ⟨⟨344,344,336,384,328,24,280,88,88⟩,[],[(0,2,0),(7,4,3)],⟨7,35,13,88,148,352,194,408,312⟩,⟨7,35,13,88,148,352,194,384,288⟩,[⟨1,1730582451861733443633153,⟨405,445,445,504,404,504,508,384,424⟩⟩,⟨2,1323666083074742440431105,⟨99,35,491,504,506,352,194,384,288⟩⟩,⟨5,1212763931357702984041539,⟨95,223,13,93,148,477,223,400,412⟩⟩]⟩
theorem node123 : UpperPrefix a [2,5,0,6,7,8,1] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,8,1] 30 cert123 (by decide +kernel)

def cert124 : Leaf := ⟨⟨112,80,114,162,98,18,50,114,82⟩,[],[(0,2,0),(7,4,3)],⟨7,35,13,88,148,352,200,402,306⟩,⟨7,35,13,88,148,352,200,384,288⟩,[⟨2,1285813436152346990087169,⟨3,35,107,504,506,352,232,384,288⟩⟩,⟨3,1276506623110786531204117,⟨407,435,439,499,407,352,482,384,288⟩⟩,⟨8,1184339755834359301539,⟨7,47,13,92,221,127,221,223,47⟩⟩]⟩
theorem node124 : UpperPrefix a [2,5,0,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,5,0,6,7,8,3] 30 cert124 (by decide +kernel)

def cert125 : Local := ⟨⟨360,332,354,0,362,14,0,110,78⟩,[(3,6),(6,4)],[(0,2,0),(7,4,3),(7,4,6),(4,6,3)]⟩
theorem node125 : UpperPrefix a [2,5,0,6,7,8,4] 30 :=
  local_sound a [2,5,0,6,7,8,4] 30 cert125 (by decide +kernel)

theorem node126 : UpperPrefix a [2,5,0,6,7,8] 30 :=
  branch_upper a [2,5,0,6,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,7,8,0] 30 (by decide +kernel))
  node123
  (invalid_upper a [2,5,0,6,7,8,2] 30 (by decide +kernel))
  node124
  node125
  (invalid_upper a [2,5,0,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,8,8] 30 (by decide +kernel)))

theorem node127 : UpperPrefix a [2,5,0,6,7] 30 :=
  branch_upper a [2,5,0,6,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,0,6,7,0] 30 (by decide +kernel))
  node120
  (invalid_upper a [2,5,0,6,7,2] 30 (by decide +kernel))
  node121
  node122
  (invalid_upper a [2,5,0,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,0,6,7,7] 30 (by decide +kernel))
  node126)

#print axioms node127
end Delivery.FiniteExclusion.Sharp2x3x4
