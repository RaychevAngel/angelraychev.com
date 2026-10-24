import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C006
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def cert448 : Local := ⟨⟨368,336,0,358,427,19,0,115,83⟩,[(2,6),(6,2)],[(2,0,3),(7,2,4),(3,6,4)]⟩
theorem node448 : UpperPrefix a [2,5,7,0,6,8,3] 30 :=
  local_sound a [2,5,7,0,6,8,3] 30 cert448 (by decide +kernel)

def cert449 : Leaf := ⟨⟨120,88,115,68,128,27,0,123,91⟩,[],[(2,0,3),(7,2,4)],⟨7,35,140,25,84,352,208,394,298⟩,⟨7,35,140,25,84,352,208,384,288⟩,[⟨8,1184123585627937719457,⟨95,59,221,25,92,127,221,223,59⟩⟩,⟨1,1210107637341789724082177,⟨93,57,220,25,84,352,208,384,288⟩⟩,⟨5,1210107636215889817240577,⟨95,27,220,25,84,320,208,384,256⟩⟩,⟨0,1210107637341789321430016,⟨86,50,220,24,84,352,208,384,288⟩⟩,⟨3,1210107637341788247688193,⟨87,51,212,17,84,352,208,384,288⟩⟩]⟩
theorem node449 : UpperPrefix a [2,5,7,0,6,8,4] 30 :=
  Boolean.leaf_sound a [2,5,7,0,6,8,4] 30 cert449 (by decide +kernel)

theorem node450 : UpperPrefix a [2,5,7,0,6,8] 30 :=
  branch_upper a [2,5,7,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,6,8,0] 30 (by decide +kernel))
  node447
  (invalid_upper a [2,5,7,0,6,8,2] 30 (by decide +kernel))
  node448
  node449
  (invalid_upper a [2,5,7,0,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,8,8] 30 (by decide +kernel)))

theorem node451 : UpperPrefix a [2,5,7,0,6] 30 :=
  branch_upper a [2,5,7,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,6,0] 30 (by decide +kernel))
  node441
  (invalid_upper a [2,5,7,0,6,2] 30 (by decide +kernel))
  node445
  node446
  (invalid_upper a [2,5,7,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,6,7] 30 (by decide +kernel))
  node450)

def cert452 : Leaf := ⟨⟨472,472,0,452,200,408,0,88,216⟩,[(2,6),(6,2)],[(2,0,3),(1,5,1)],⟨7,35,140,25,276,98,200,464,368⟩,⟨7,35,140,25,276,98,200,384,288⟩,[⟨0,1404877728801570914567168,⟨502,434,476,508,468,502,476,384,432⟩⟩,⟨5,1212623743310584947409953,⟨71,3,220,221,476,71,220,476,477⟩⟩]⟩
theorem node452 : UpperPrefix a [2,5,7,0,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,7,0,8,1,3] 30 cert452 (by decide +kernel)

def cert453 : Leaf := ⟨⟨184,152,48,164,168,152,296,120,216⟩,[],[(2,0,3),(8,4,6),(1,5,1)],⟨7,35,140,25,276,98,208,456,360⟩,⟨7,35,140,25,276,98,208,384,288⟩,[⟨0,1247997700135185632199680,⟨246,98,476,508,468,98,208,384,288⟩⟩,⟨6,1210106412371171676931249,⟨15,35,157,25,287,47,157,415,291⟩⟩]⟩
theorem node453 : UpperPrefix a [2,5,7,0,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,0,8,1,4] 30 cert453 (by decide +kernel)

theorem node454 : UpperPrefix a [2,5,7,0,8,1] 30 :=
  branch_upper a [2,5,7,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,1,2] 30 (by decide +kernel))
  node452
  node453
  (invalid_upper a [2,5,7,0,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,1,8] 30 (by decide +kernel)))

def cert455 : Leaf := ⟨⟨184,152,304,164,168,144,56,120,216⟩,[],[(2,0,3)],⟨7,35,140,25,276,104,194,464,368⟩,⟨7,35,140,25,276,104,194,384,288⟩,[⟨0,1409433912717812763198464,⟨470,502,444,508,276,508,466,400,436⟩⟩,⟨1,1664340193631002621902849,⟨29,445,140,25,276,508,508,400,436⟩⟩,⟨6,1210106412371171676931313,⟨15,35,157,25,287,47,159,415,291⟩⟩,⟨8,1181818430506138615317,⟨103,35,239,59,127,106,194,128,32⟩⟩]⟩
theorem node455 : UpperPrefix a [2,5,7,0,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,0,8,3,1] 30 cert455 (by decide +kernel)

def cert456 : Leaf := ⟨⟨168,136,34,166,170,146,298,106,202⟩,[],[(2,0,3),(8,4,6),(4,6,5)],⟨7,35,140,25,276,104,208,450,354⟩,⟨7,35,140,25,276,104,208,384,288⟩,[⟨0,1224302605487379770770432,⟨502,498,252,508,372,124,208,384,288⟩⟩,⟨6,1210106412371171676931249,⟨15,35,157,25,287,47,157,415,291⟩⟩]⟩
theorem node456 : UpperPrefix a [2,5,7,0,8,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,0,8,3,4] 30 cert456 (by decide +kernel)

theorem node457 : UpperPrefix a [2,5,7,0,8,3] 30 :=
  branch_upper a [2,5,7,0,8,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,8,3,0] 30 (by decide +kernel))
  node455
  (invalid_upper a [2,5,7,0,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,3,3] 30 (by decide +kernel))
  node456
  (invalid_upper a [2,5,7,0,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,3,8] 30 (by decide +kernel)))

def cert458 : Leaf := ⟨⟨496,464,0,484,224,384,304,112,208⟩,[(2,7)],[(2,0,3),(3,7,2)],⟨7,35,140,25,276,112,194,392,352⟩,⟨7,35,140,25,276,112,194,392,288⟩,[⟨0,1715511480082659925820416,⟨502,370,444,508,404,368,502,444,288⟩⟩,⟨1,1664063492461100911034369,⟨157,445,156,29,276,500,508,412,304⟩⟩]⟩
theorem node458 : UpperPrefix a [2,5,7,0,8,4,1,3] 30 :=
  Boolean.leaf_sound a [2,5,7,0,8,4,1,3] 30 cert458 (by decide +kernel)

def cert459 : Leaf := ⟨⟨432,400,304,420,168,384,304,48,152⟩,[],[(2,0,3)],⟨7,35,140,25,276,112,194,448,296⟩,⟨7,35,140,25,276,112,194,448,288⟩,[⟨0,1266859027857736098382848,⟨502,242,444,508,276,112,226,448,288⟩⟩,⟨1,1541558669571538969690113,⟨285,445,444,25,276,500,508,500,432⟩⟩,⟨6,1370666872795444460799217,⟨287,315,157,25,287,319,415,415,315⟩⟩,⟨3,1212622015872229037866005,⟨71,99,231,243,503,243,194,448,482⟩⟩]⟩
theorem node459 : UpperPrefix a [2,5,7,0,8,4,1,6] 30 :=
  Boolean.leaf_sound a [2,5,7,0,8,4,1,6] 30 cert459 (by decide +kernel)

theorem node460 : UpperPrefix a [2,5,7,0,8,4,1] 30 :=
  branch_upper a [2,5,7,0,8,4,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,8,4,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,1,2] 30 (by decide +kernel))
  node458
  (invalid_upper a [2,5,7,0,8,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,1,5] 30 (by decide +kernel))
  node459
  (invalid_upper a [2,5,7,0,8,4,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,1,8] 30 (by decide +kernel)))

def cert461 : Leaf := ⟨⟨424,392,0,422,170,394,0,106,202⟩,[(2,6),(6,2)],[(2,0,3)],⟨7,35,140,25,276,112,200,450,354⟩,⟨7,35,140,25,276,112,200,384,288⟩,[⟨0,1214839374584305398318080,⟨502,434,252,508,372,116,252,384,288⟩⟩,⟨4,1361666230765131983373361,⟨71,419,204,205,455,487,204,386,419⟩⟩,⟨6,1210106412371175971898545,⟨15,43,157,25,287,63,157,415,299⟩⟩]⟩
theorem node461 : UpperPrefix a [2,5,7,0,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,7,0,8,4,3] 30 cert461 (by decide +kernel)

theorem node462 : UpperPrefix a [2,5,7,0,8,4] 30 :=
  branch_upper a [2,5,7,0,8,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,8,4,0] 30 (by decide +kernel))
  node460
  (invalid_upper a [2,5,7,0,8,4,2] 30 (by decide +kernel))
  node461
  (invalid_upper a [2,5,7,0,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,4,8] 30 (by decide +kernel)))

theorem node463 : UpperPrefix a [2,5,7,0,8] 30 :=
  branch_upper a [2,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,8,0] 30 (by decide +kernel))
  node454
  (invalid_upper a [2,5,7,0,8,2] 30 (by decide +kernel))
  node457
  node462
  (invalid_upper a [2,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,8,8] 30 (by decide +kernel)))

theorem node464 : UpperPrefix a [2,5,7,0] 30 :=
  branch_upper a [2,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,0,0] 30 (by decide +kernel))
  node439
  (invalid_upper a [2,5,7,0,2] 30 (by decide +kernel))
  node440
  (invalid_upper a [2,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,0,5] 30 (by decide +kernel))
  node451
  (invalid_upper a [2,5,7,0,7] 30 (by decide +kernel))
  node463)

def cert465 : Leaf := ⟨⟨184,152,48,161,0,408,312,120,216⟩,[(4,0)],[(2,0,4),(0,4,3)],⟨7,35,140,26,21,376,472,472,376⟩,⟨7,35,140,26,21,96,192,384,288⟩,[⟨1,1247960428519835460173825,⟨21,49,492,508,21,96,192,384,288⟩⟩,⟨6,1210106412378140127151265,⟨31,59,157,26,29,63,157,415,315⟩⟩,⟨8,1181745685015559292065,⟨31,59,157,26,29,127,221,159,59⟩⟩]⟩
theorem node465 : UpperPrefix a [2,5,7,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,1,0] 30 cert465 (by decide +kernel)

def cert466 : Leaf := ⟨⟨496,0,368,484,0,404,308,116,212⟩,[(1,5),(4,2)],[(3,4,4),(0,5,1)],⟨7,35,140,26,28,97,464,464,368⟩,⟨7,35,140,26,28,97,192,384,288⟩,[⟨1,1252876863942681812795393,⟨501,481,476,508,476,481,192,384,288⟩⟩]⟩
theorem node466 : UpperPrefix a [2,5,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,1,3,0] 30 cert466 (by decide +kernel)

def cert467 : Leaf := ⟨⟨224,196,97,229,0,133,293,101,197⟩,[(4,2)],[(3,4,4)],⟨7,35,140,26,28,112,449,449,353⟩,⟨7,35,140,26,28,112,192,384,288⟩,[⟨4,1373431200244494031275049,⟨455,483,205,463,205,487,192,450,483⟩⟩,⟨1,1224302389209250699149313,⟨501,481,188,508,60,112,192,384,288⟩⟩,⟨8,1181747936823962944737,⟨31,59,157,26,28,127,255,159,59⟩⟩]⟩
theorem node467 : UpperPrefix a [2,5,7,1,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,1,3,4] 30 cert467 (by decide +kernel)

def cert468 : Leaf := ⟨⟨176,148,51,132,0,149,53,117,213⟩,[(4,2)],[(3,4,4)],⟨7,35,140,26,28,352,209,465,369⟩,⟨7,35,140,26,28,352,192,384,288⟩,[⟨8,1184123585618810913953,⟨95,59,221,26,92,127,221,223,59⟩⟩,⟨1,1214839173258984689762305,⟨501,481,156,56,28,352,192,384,288⟩⟩,⟨6,1210106412378140127151265,⟨31,59,157,26,28,319,157,415,315⟩⟩,⟨0,1210107565284195686155264,⟨30,58,156,26,28,352,192,384,288⟩⟩,⟨5,1210107564158295779312641,⟨31,27,156,26,28,320,192,384,256⟩⟩]⟩
theorem node468 : UpperPrefix a [2,5,7,1,3,8] 30 :=
  Boolean.leaf_sound a [2,5,7,1,3,8] 30 cert468 (by decide +kernel)

theorem node469 : UpperPrefix a [2,5,7,1,3] 30 :=
  branch_upper a [2,5,7,1,3] 30 (by decide) (fin9_cases _
  node466
  (invalid_upper a [2,5,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,3,3] 30 (by decide +kernel))
  node467
  (invalid_upper a [2,5,7,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,3,7] 30 (by decide +kernel))
  node468)

def cert470 : Local := ⟨⟨368,0,0,356,426,278,0,118,86⟩,[(1,5),(2,6),(6,2)],[(7,2,4),(0,5,1),(3,6,4)]⟩
theorem node470 : UpperPrefix a [2,5,7,1,6,0,3] 30 :=
  local_sound a [2,5,7,1,6,0,3] 30 cert470 (by decide +kernel)

def cert471 : Leaf := ⟨⟨120,0,112,100,168,28,44,124,92⟩,[(1,5)],[(7,2,4),(0,5,1)],⟨7,35,140,26,84,97,208,392,296⟩,⟨7,35,140,26,84,97,208,384,288⟩,[⟨1,1247997700135254351675393,⟨245,113,476,508,212,113,208,384,288⟩⟩,⟨8,1184131079901340237557,⟨127,59,255,59,127,127,255,255,59⟩⟩]⟩
theorem node471 : UpperPrefix a [2,5,7,1,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,0,4] 30 cert471 (by decide +kernel)

def cert472 : Local := ⟨⟨120,0,114,100,170,30,0,126,94⟩,[(1,5),(6,7)],[(7,2,4),(0,5,1),(8,6,6)]⟩
theorem node472 : UpperPrefix a [2,5,7,1,6,0,8] 30 :=
  local_sound a [2,5,7,1,6,0,8] 30 cert472 (by decide +kernel)

theorem node473 : UpperPrefix a [2,5,7,1,6,0] 30 :=
  branch_upper a [2,5,7,1,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,1,6,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,0,2] 30 (by decide +kernel))
  node470
  node471
  (invalid_upper a [2,5,7,1,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,0,7] 30 (by decide +kernel))
  node472)

def cert474 : Leaf := ⟨⟨120,92,112,100,160,21,52,116,84⟩,[],[(7,2,4)],⟨7,35,140,26,84,104,193,400,304⟩,⟨7,35,140,26,84,104,193,384,288⟩,[⟨8,1184131079901340237557,⟨127,59,255,59,127,127,255,255,59⟩⟩,⟨1,1430278733503237492572161,⟨469,501,444,508,468,508,209,384,436⟩⟩,⟨0,1373416590574999696049152,⟨398,446,140,414,84,508,212,384,436⟩⟩,⟨3,1219653809385259553260545,⟨471,499,132,466,84,224,209,384,288⟩⟩]⟩
theorem node474 : UpperPrefix a [2,5,7,1,6,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,3,0] 30 cert474 (by decide +kernel)

def cert475 : Leaf := ⟨⟨104,72,97,101,169,17,41,105,73⟩,[],[(7,2,4),(4,6,5)],⟨7,35,140,26,84,104,208,385,289⟩,⟨7,35,140,26,84,104,208,384,288⟩,[⟨8,1184131079901340237557,⟨127,59,255,59,127,127,255,255,59⟩⟩,⟨1,1224302605489853671931905,⟨501,497,252,508,116,124,208,384,304⟩⟩,⟨2,1224302479385971725960705,⟨419,419,232,506,112,104,208,384,288⟩⟩]⟩
theorem node475 : UpperPrefix a [2,5,7,1,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,3,4] 30 cert475 (by decide +kernel)

def cert476 : Leaf := ⟨⟨120,92,113,100,160,20,0,117,85⟩,[(6,7)],[(7,2,4),(8,6,6)],⟨7,35,140,26,84,104,448,401,305⟩,⟨7,35,140,26,84,104,448,384,288⟩,[⟨1,1224304839275268847697921,⟨501,497,252,508,116,124,448,448,304⟩⟩,⟨0,1210109871267873400292352,⟨62,42,252,26,116,104,448,448,288⟩⟩,⟨3,1219582472367436882510849,⟨471,499,212,466,84,96,448,448,288⟩⟩]⟩
theorem node476 : UpperPrefix a [2,5,7,1,6,3,8] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,3,8] 30 cert476 (by decide +kernel)

theorem node477 : UpperPrefix a [2,5,7,1,6,3] 30 :=
  branch_upper a [2,5,7,1,6,3] 30 (by decide) (fin9_cases _
  node474
  (invalid_upper a [2,5,7,1,6,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,3,3] 30 (by decide +kernel))
  node475
  (invalid_upper a [2,5,7,1,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,3,7] 30 (by decide +kernel))
  node476)

def cert478 : Leaf := ⟨⟨56,28,49,37,169,0,60,61,29⟩,[(5,4)],[(7,2,4),(6,4,5)],⟨7,35,140,26,84,112,193,392,296⟩,⟨7,35,140,26,84,112,193,384,288⟩,[⟨8,1184131079901340237557,⟨127,59,255,59,127,127,255,255,59⟩⟩,⟨1,1247997198546021219565569,⟨245,113,396,444,244,112,241,384,288⟩⟩]⟩
theorem node478 : UpperPrefix a [2,5,7,1,6,4,0] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,4,0] 30 cert478 (by decide +kernel)

def cert479 : Local := ⟨⟨304,276,0,293,427,0,0,55,23⟩,[(2,6),(5,4),(6,2)],[(7,2,4),(6,4,5),(3,6,4)]⟩
theorem node479 : UpperPrefix a [2,5,7,1,6,4,3] 30 :=
  local_sound a [2,5,7,1,6,4,3] 30 cert479 (by decide +kernel)

def cert480 : Local := ⟨⟨56,28,51,37,171,0,0,63,31⟩,[(5,4),(6,7)],[(7,2,4),(6,4,5),(8,6,6)]⟩
theorem node480 : UpperPrefix a [2,5,7,1,6,4,8] 30 :=
  local_sound a [2,5,7,1,6,4,8] 30 cert480 (by decide +kernel)

theorem node481 : UpperPrefix a [2,5,7,1,6,4] 30 :=
  branch_upper a [2,5,7,1,6,4] 30 (by decide) (fin9_cases _
  node478
  (invalid_upper a [2,5,7,1,6,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,4,2] 30 (by decide +kernel))
  node479
  (invalid_upper a [2,5,7,1,6,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,4,7] 30 (by decide +kernel))
  node480)

def cert482 : Leaf := ⟨⟨112,84,0,101,161,21,52,117,85⟩,[(2,7)],[(7,2,4),(3,7,2)],⟨7,35,140,26,84,352,193,392,304⟩,⟨7,35,140,26,84,352,193,392,288⟩,[⟨1,1791069344080428499206145,⟨501,369,396,444,500,368,501,396,288⟩⟩,⟨8,1184123585618810913953,⟨95,59,221,26,84,127,221,223,59⟩⟩]⟩
theorem node482 : UpperPrefix a [2,5,7,1,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,8,0,3] 30 cert482 (by decide +kernel)

def cert483 : Leaf := ⟨⟨72,76,81,69,137,13,12,77,77⟩,[],[(7,2,4),(4,7,2)],⟨7,35,140,26,84,352,193,400,296⟩,⟨7,35,140,26,84,352,193,400,288⟩,[⟨1,1267043495790779525234689,⟨501,241,444,508,500,352,241,432,288⟩⟩,⟨5,1212764003398585293472779,⟨95,223,221,95,84,468,221,400,400⟩⟩,⟨8,1184123585618810913953,⟨95,59,221,26,84,127,221,223,59⟩⟩]⟩
theorem node483 : UpperPrefix a [2,5,7,1,6,8,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,8,0,4] 30 cert483 (by decide +kernel)

theorem node484 : UpperPrefix a [2,5,7,1,6,8,0] 30 :=
  branch_upper a [2,5,7,1,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,1,6,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,0,2] 30 (by decide +kernel))
  node482
  node483
  (invalid_upper a [2,5,7,1,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,0,8] 30 (by decide +kernel)))

def cert485 : Leaf := ⟨⟨368,340,0,357,425,21,0,117,85⟩,[(2,6),(6,2)],[(7,2,4),(3,6,4)],⟨7,35,140,26,84,352,200,401,305⟩,⟨7,35,140,26,84,352,200,384,288⟩,[⟨1,1224302551345503090507777,⟨501,433,252,508,84,372,252,384,304⟩⟩]⟩
theorem node485 : UpperPrefix a [2,5,7,1,6,8,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,8,3] 30 cert485 (by decide +kernel)

def cert486 : Leaf := ⟨⟨112,84,114,100,160,20,36,124,92⟩,[],[(7,2,4)],⟨7,35,140,26,84,352,208,385,296⟩,⟨7,35,140,26,84,352,208,385,288⟩,[⟨0,1885408357742623631344640,⟨382,314,508,314,372,368,500,508,288⟩⟩,⟨8,1184123585618810913953,⟨95,59,221,26,84,127,221,223,59⟩⟩,⟨1,1266787623918413078855681,⟨501,241,508,376,372,352,240,497,288⟩⟩,⟨3,1210109947688397088853013,⟨87,51,247,19,87,354,243,499,288⟩⟩]⟩
theorem node486 : UpperPrefix a [2,5,7,1,6,8,4,0] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,8,4,0] 30 cert486 (by decide +kernel)

def cert487 : Leaf := ⟨⟨352,324,0,357,417,5,293,101,69⟩,[(2,7)],[(7,2,4),(3,7,2)],⟨7,35,140,26,84,352,208,392,289⟩,⟨7,35,140,26,84,352,208,392,288⟩,[⟨1,1224350978558893291995137,⟨373,305,252,508,84,368,244,508,288⟩⟩,⟨4,1786346959472040950691037,⟨391,291,399,431,487,355,487,399,290⟩⟩]⟩
theorem node487 : UpperPrefix a [2,5,7,1,6,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,6,8,4,3] 30 cert487 (by decide +kernel)

theorem node488 : UpperPrefix a [2,5,7,1,6,8,4] 30 :=
  branch_upper a [2,5,7,1,6,8,4] 30 (by decide) (fin9_cases _
  node486
  (invalid_upper a [2,5,7,1,6,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,4,2] 30 (by decide +kernel))
  node487
  (invalid_upper a [2,5,7,1,6,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,4,8] 30 (by decide +kernel)))

theorem node489 : UpperPrefix a [2,5,7,1,6,8] 30 :=
  branch_upper a [2,5,7,1,6,8] 30 (by decide) (fin9_cases _
  node484
  (invalid_upper a [2,5,7,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,2] 30 (by decide +kernel))
  node485
  node488
  (invalid_upper a [2,5,7,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,8,8] 30 (by decide +kernel)))

theorem node490 : UpperPrefix a [2,5,7,1,6] 30 :=
  branch_upper a [2,5,7,1,6] 30 (by decide) (fin9_cases _
  node473
  (invalid_upper a [2,5,7,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,2] 30 (by decide +kernel))
  node477
  node481
  (invalid_upper a [2,5,7,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,6,7] 30 (by decide +kernel))
  node489)

def cert491 : Leaf := ⟨⟨504,0,0,484,232,412,0,124,220⟩,[(1,5),(2,6),(6,2)],[(0,5,1)],⟨7,35,140,26,276,97,200,464,368⟩,⟨7,35,140,26,276,97,200,384,288⟩,[⟨1,1366397820658590109663233,⟨501,433,204,220,468,501,204,384,432⟩⟩]⟩
theorem node491 : UpperPrefix a [2,5,7,1,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,0,3] 30 cert491 (by decide +kernel)

def cert492 : Leaf := ⟨⟨184,0,48,164,168,156,300,124,220⟩,[(1,5)],[(8,4,6),(0,5,1)],⟨7,35,140,26,276,97,208,456,360⟩,⟨7,35,140,26,276,97,208,384,288⟩,[⟨1,1247997700135185632198657,⟨245,97,476,508,468,97,208,384,288⟩⟩,⟨6,1210106412371162550125745,⟨7,35,157,27,287,39,157,415,291⟩⟩]⟩
theorem node492 : UpperPrefix a [2,5,7,1,8,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,0,4] 30 cert492 (by decide +kernel)

theorem node493 : UpperPrefix a [2,5,7,1,8,0] 30 :=
  branch_upper a [2,5,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,0,2] 30 (by decide +kernel))
  node491
  node492
  (invalid_upper a [2,5,7,1,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,0,8] 30 (by decide +kernel)))

def cert494 : Leaf := ⟨⟨184,156,304,164,160,148,52,116,212⟩,[],[],⟨7,35,140,26,276,104,193,464,368⟩,⟨7,35,140,26,276,104,193,384,288⟩,[⟨0,1664340193631002621903872,⟨30,446,140,30,276,508,508,400,436⟩⟩,⟨1,1408843616907454057545729,⟨469,501,444,508,276,508,209,400,436⟩⟩,⟨6,1210106412371162550125745,⟨7,35,157,27,287,47,157,415,291⟩⟩,⟨8,1181818430506138615317,⟨103,35,239,59,127,106,195,128,32⟩⟩,⟨3,1219653809385259553260545,⟨471,499,132,466,276,224,209,384,288⟩⟩]⟩
theorem node494 : UpperPrefix a [2,5,7,1,8,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,3,0] 30 cert494 (by decide +kernel)

def cert495 : Leaf := ⟨⟨168,140,32,164,168,148,300,44,204⟩,[],[(8,4,6),(4,6,5)],⟨7,35,140,26,276,104,208,385,352⟩,⟨7,35,140,26,276,104,208,385,288⟩,[⟨0,2367089736180577676035072,⟨382,314,508,282,372,376,500,508,288⟩⟩,⟨1,1507646900305041598447617,⟨501,497,508,508,372,380,464,465,304⟩⟩,⟨6,1212615169582813668328889,⟨7,35,157,159,415,47,157,415,447⟩⟩]⟩
theorem node495 : UpperPrefix a [2,5,7,1,8,3,4,0] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,3,4,0] 30 cert495 (by decide +kernel)

def cert496 : Leaf := ⟨⟨40,12,33,37,41,21,301,45,13⟩,[],[(8,4,6),(4,6,5)],⟨7,35,140,26,276,104,208,448,289⟩,⟨7,35,140,26,276,104,208,448,288⟩,[⟨1,1226892931895584837599233,⟨501,501,252,508,500,252,208,464,500⟩⟩,⟨6,1370666872791037287482545,⟨287,315,157,283,287,319,157,415,315⟩⟩,⟨7,1539492634219764155190293,⟨287,315,319,283,287,362,379,362,288⟩⟩]⟩
theorem node496 : UpperPrefix a [2,5,7,1,8,3,4,6] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,3,4,6] 30 cert496 (by decide +kernel)

theorem node497 : UpperPrefix a [2,5,7,1,8,3,4] 30 :=
  branch_upper a [2,5,7,1,8,3,4] 30 (by decide) (fin9_cases _
  node495
  (invalid_upper a [2,5,7,1,8,3,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,4,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,4,3] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,4,5] 30 (by decide +kernel))
  node496
  (invalid_upper a [2,5,7,1,8,3,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,4,8] 30 (by decide +kernel)))

theorem node498 : UpperPrefix a [2,5,7,1,8,3] 30 :=
  branch_upper a [2,5,7,1,8,3] 30 (by decide) (fin9_cases _
  node494
  (invalid_upper a [2,5,7,1,8,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,3] 30 (by decide +kernel))
  node497
  (invalid_upper a [2,5,7,1,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,3,8] 30 (by decide +kernel)))

def cert499 : Leaf := ⟨⟨176,148,0,164,162,134,54,54,214⟩,[(2,7)],[(3,7,2)],⟨7,35,140,26,276,112,193,392,352⟩,⟨7,35,140,26,276,112,193,392,288⟩,[⟨0,1664063492461100913132544,⟨158,446,156,158,276,500,508,412,304⟩⟩,⟨6,1212615169582817971684795,⟨7,47,157,159,415,191,157,415,447⟩⟩,⟨8,1184124132782192489621,⟨71,43,207,59,127,123,197,207,42⟩⟩]⟩
theorem node499 : UpperPrefix a [2,5,7,1,8,4,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,4,0,3] 30 cert499 (by decide +kernel)

def cert500 : Leaf := ⟨⟨432,276,304,292,40,260,308,52,28⟩,[],[],⟨7,35,140,26,276,112,193,448,296⟩,⟨7,35,140,26,276,112,193,448,288⟩,[⟨0,1541558669572088725505024,⟨286,446,444,286,276,500,508,500,432⟩⟩,⟨1,1266859030109535912067073,⟨501,241,444,508,276,112,241,480,288⟩⟩,⟨6,1370666872791037287482545,⟨287,315,157,283,287,319,157,415,315⟩⟩,⟨3,1212617404186210610478101,⟨71,99,231,243,503,243,193,448,482⟩⟩,⟨7,2276181801043830791767041,⟨287,315,284,282,276,378,379,362,296⟩⟩]⟩
theorem node500 : UpperPrefix a [2,5,7,1,8,4,0,6] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,4,0,6] 30 cert500 (by decide +kernel)

theorem node501 : UpperPrefix a [2,5,7,1,8,4,0] 30 :=
  branch_upper a [2,5,7,1,8,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,1,8,4,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,2] 30 (by decide +kernel))
  node499
  (invalid_upper a [2,5,7,1,8,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,5] 30 (by decide +kernel))
  node500
  (invalid_upper a [2,5,7,1,8,4,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,0,8] 30 (by decide +kernel)))

def cert502 : Leaf := ⟨⟨168,140,0,165,169,141,0,109,205⟩,[(2,6),(6,2)],[],⟨7,35,140,26,276,112,200,449,353⟩,⟨7,35,140,26,276,112,200,384,288⟩,[⟨1,1214839227794555285798913,⟨501,433,204,56,372,116,204,384,288⟩⟩,⟨4,1361666230765131983373369,⟨71,419,205,207,455,487,205,386,419⟩⟩,⟨6,1210106412371166845093041,⟨7,43,157,27,287,63,157,415,299⟩⟩,⟨8,1181818289772962149493,⟨71,43,207,59,127,127,207,130,43⟩⟩]⟩
theorem node502 : UpperPrefix a [2,5,7,1,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,7,1,8,4,3] 30 cert502 (by decide +kernel)

theorem node503 : UpperPrefix a [2,5,7,1,8,4] 30 :=
  branch_upper a [2,5,7,1,8,4] 30 (by decide) (fin9_cases _
  node501
  (invalid_upper a [2,5,7,1,8,4,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,2] 30 (by decide +kernel))
  node502
  (invalid_upper a [2,5,7,1,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,4,8] 30 (by decide +kernel)))

theorem node504 : UpperPrefix a [2,5,7,1,8] 30 :=
  branch_upper a [2,5,7,1,8] 30 (by decide) (fin9_cases _
  node493
  (invalid_upper a [2,5,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,2] 30 (by decide +kernel))
  node498
  node503
  (invalid_upper a [2,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,8,8] 30 (by decide +kernel)))

theorem node505 : UpperPrefix a [2,5,7,1] 30 :=
  branch_upper a [2,5,7,1] 30 (by decide) (fin9_cases _
  node465
  (invalid_upper a [2,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,2] 30 (by decide +kernel))
  node469
  (invalid_upper a [2,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,1,5] 30 (by decide +kernel))
  node490
  (invalid_upper a [2,5,7,1,7] 30 (by decide +kernel))
  node504)

def cert506 : Leaf := ⟨⟨216,216,81,129,0,153,281,89,217⟩,[(4,0)],[(2,0,4),(1,5,1)],⟨7,35,140,88,21,98,472,408,312⟩,⟨7,35,140,88,21,98,192,384,288⟩,[⟨5,1212475664948330123756577,⟨23,27,204,92,21,95,204,476,477⟩⟩,⟨8,1181748210000626637949,⟨23,59,191,127,23,127,255,130,59⟩⟩]⟩
theorem node506 : UpperPrefix a [2,5,7,6,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,1] 30 cert506 (by decide +kernel)

def cert507 : Leaf := ⟨⟨184,152,51,163,0,0,307,51,147⟩,[(4,0),(5,3)],[(2,0,4),(6,3,5)],⟨7,35,140,88,21,104,466,402,306⟩,⟨7,35,140,88,21,104,192,384,288⟩,[⟨8,1181748210000626637949,⟨23,59,191,127,23,127,255,130,59⟩⟩,⟨3,1219580022408964715054081,⟨471,499,132,80,213,96,192,384,288⟩⟩]⟩
theorem node507 : UpperPrefix a [2,5,7,6,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,3] 30 cert507 (by decide +kernel)

def cert508 : Leaf := ⟨⟨376,344,370,0,0,0,314,122,90⟩,[(3,5),(4,0),(5,3)],[(2,0,4)],⟨7,35,140,88,21,112,458,394,298⟩,⟨7,35,140,88,21,112,192,384,288⟩,[⟨0,1219570781303940977263616,⟨454,494,172,120,20,120,192,384,296⟩⟩,⟨7,1426155832156960823729173,⟨279,315,319,379,279,379,64,256,298⟩⟩]⟩
theorem node508 : UpperPrefix a [2,5,7,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,4] 30 cert508 (by decide +kernel)

def cert509 : Leaf := ⟨⟨216,216,81,129,0,153,25,89,217⟩,[(4,0)],[(2,0,4)],⟨7,35,140,88,21,352,194,408,312⟩,⟨7,35,140,88,21,352,194,384,288⟩,[⟨1,1550782037370609251385345,⟨21,53,428,508,21,492,508,384,292⟩⟩,⟨5,1212763931340729338037315,⟨95,223,156,93,29,477,223,388,412⟩⟩,⟨8,1184051528548893213921,⟨31,59,221,93,29,127,223,223,59⟩⟩]⟩
theorem node509 : UpperPrefix a [2,5,7,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,8,1] 30 cert509 (by decide +kernel)

def cert510 : Leaf := ⟨⟨496,464,0,419,0,147,0,115,211⟩,[(2,6),(4,0),(6,2)],[(2,0,4)],⟨7,35,140,88,21,352,200,402,306⟩,⟨7,35,140,88,21,352,200,384,288⟩,[⟨3,1276506623110786531204117,⟨407,435,439,499,407,352,482,384,288⟩⟩]⟩
theorem node510 : UpperPrefix a [2,5,7,6,0,8,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,8,3] 30 cert510 (by decide +kernel)

def cert511 : Leaf := ⟨⟨360,328,355,0,0,11,299,107,75⟩,[(3,6),(4,0)],[(2,0,4),(4,6,3)],⟨7,35,140,88,21,352,208,394,298⟩,⟨7,35,140,88,21,352,208,384,288⟩,[⟨7,1718942556346682935647253,⟨279,307,319,379,279,362,379,256,288⟩⟩]⟩
theorem node511 : UpperPrefix a [2,5,7,6,0,8,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,0,8,4] 30 cert511 (by decide +kernel)

#print axioms node511
end Delivery.FiniteExclusion.Sharp2x3x4
