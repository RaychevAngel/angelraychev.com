import RegularNineSharp2x2x5Base
import RegularNineSharp2x2x5C006
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Bounds BoundTreeRows Extremal
def cert448 : Leaf := ⟨⟨496,0,240,416,450,384,264,104,236⟩,[(1,4)],[(0,4,1),(1,5,4)],⟨7,19,268,76,49,98,224,392,408⟩,⟨7,19,268,76,49,98,224,384,272⟩,[⟨2,1210144477455106841781761,⟨243,115,392,200,115,114,224,384,306⟩⟩,⟨4,1210144476890851353560065,⟨239,107,396,204,105,98,224,384,256⟩⟩,⟨3,1210107565566150222822925,⟨23,19,311,119,51,98,224,384,274⟩⟩]⟩
theorem node448 : UpperPrefix a [2,4,8,6,0,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,1,5] 30 cert448 (by decide +kernel)

theorem node449 : UpperPrefix a [2,4,8,6,0,1] 30 :=
  branch_upper a [2,4,8,6,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,1,2] 30 (by decide +kernel))
  node447
  (invalid_upper a [2,4,8,6,0,1,4] 30 (by decide +kernel))
  node448
  (invalid_upper a [2,4,8,6,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,1,8] 30 (by decide +kernel)))

def cert450 : Leaf := ⟨⟨440,0,178,434,398,0,306,50,162⟩,[(1,4),(5,3)],[(6,3,5),(0,4,1)],⟨7,19,268,76,49,104,226,418,434⟩,⟨7,19,268,76,49,104,192,384,272⟩,[⟨2,1285813291474206813332481,⟨3,467,296,104,499,104,192,384,466⟩⟩,⟨3,1285813291192730763928577,⟨7,467,260,68,499,96,192,384,466⟩⟩]⟩
theorem node450 : UpperPrefix a [2,4,8,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,3] 30 cert450 (by decide +kernel)

def cert451 : Leaf := ⟨⟨376,0,114,290,330,0,296,106,110⟩,[(1,4),(5,6)],[(0,4,1),(7,5,5)],⟨7,19,268,76,49,224,194,424,312⟩,⟨7,19,268,76,49,224,194,384,272⟩,[⟨2,1210144479355062934578689,⟨243,115,424,232,115,224,242,384,274⟩⟩,⟨4,1210144479353757399778305,⟨239,107,428,236,105,224,226,384,256⟩⟩]⟩
theorem node451 : UpperPrefix a [2,4,8,6,0,7,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,0,7,1] 30 cert451 (by decide +kernel)

def cert452 : Local := ⟨⟨368,0,114,306,326,0,310,118,102⟩,[(1,4),(5,6)],[(0,4,1),(7,5,5),(3,6,3)]⟩
theorem node452 : UpperPrefix a [2,4,8,6,0,7,3] 30 :=
  local_sound a [2,4,8,6,0,7,3] 30 cert452 (by decide +kernel)

def cert453 : Local := ⟨⟨376,0,114,306,334,0,0,126,110⟩,[(1,4),(5,6),(6,5)],[(0,4,1),(7,5,5),(7,5,6)]⟩
theorem node453 : UpperPrefix a [2,4,8,6,0,7,5] 30 :=
  local_sound a [2,4,8,6,0,7,5] 30 cert453 (by decide +kernel)

theorem node454 : UpperPrefix a [2,4,8,6,0,7] 30 :=
  branch_upper a [2,4,8,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,0,7,0] 30 (by decide +kernel))
  node451
  (invalid_upper a [2,4,8,6,0,7,2] 30 (by decide +kernel))
  node452
  (invalid_upper a [2,4,8,6,0,7,4] 30 (by decide +kernel))
  node453
  (invalid_upper a [2,4,8,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,7,8] 30 (by decide +kernel)))

theorem node455 : UpperPrefix a [2,4,8,6,0] 30 :=
  branch_upper a [2,4,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,0,0] 30 (by decide +kernel))
  node449
  (invalid_upper a [2,4,8,6,0,2] 30 (by decide +kernel))
  node450
  (invalid_upper a [2,4,8,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,0,6] 30 (by decide +kernel))
  node454
  (invalid_upper a [2,4,8,6,0,8] 30 (by decide +kernel)))

def cert456 : Leaf := ⟨⟨112,32,240,432,1,20,316,124,236⟩,[],[(1,4,1),(0,5,4)],⟨7,19,268,76,50,97,232,424,440⟩,⟨7,19,268,76,50,97,192,384,272⟩,[⟨3,1210107565568349246086669,⟨23,19,311,119,50,115,192,384,272⟩⟩,⟨7,1208926973947632908525069,⟨23,19,319,127,50,115,64,256,272⟩⟩,⟨8,1181745953721145122317,⟨23,19,63,127,50,115,192,128,16⟩⟩,⟨2,1210107565286050708341761,⟨3,19,264,72,50,115,192,384,272⟩⟩,⟨6,1210106412364546102543361,⟨7,19,268,12,50,51,128,384,272⟩⟩]⟩
theorem node456 : UpperPrefix a [2,4,8,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,0] 30 cert456 (by decide +kernel)

def cert457 : Leaf := ⟨⟨440,428,177,417,397,0,288,33,161⟩,[(5,3)],[(6,3,5),(1,4,1)],⟨7,19,268,76,50,104,193,416,432⟩,⟨7,19,268,76,50,104,193,384,272⟩,[⟨2,1285849950775173609161729,⟨195,467,424,232,498,104,193,384,400⟩⟩,⟨3,1285813038991151631172609,⟨71,467,260,68,498,96,193,384,400⟩⟩,⟨4,1210144479424126143955969,⟨239,107,428,236,34,104,233,384,256⟩⟩]⟩
theorem node457 : UpperPrefix a [2,4,8,6,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,3,0] 30 cert457 (by decide +kernel)

def cert458 : Leaf := ⟨⟨432,420,176,432,389,0,276,53,165⟩,[(5,3)],[(6,3,5),(1,4,1)],⟨7,19,268,76,50,104,224,385,401⟩,⟨7,19,268,76,50,104,224,384,272⟩,[⟨3,1408881320747833410737165,⟨391,467,391,471,498,499,498,384,336⟩⟩,⟨0,1210109878163761120936960,⟨6,18,300,108,50,104,236,492,272⟩⟩]⟩
theorem node458 : UpperPrefix a [2,4,8,6,1,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,3,5] 30 cert458 (by decide +kernel)

theorem node459 : UpperPrefix a [2,4,8,6,1,3] 30 :=
  branch_upper a [2,4,8,6,1,3] 30 (by decide) (fin9_cases _
  node457
  (invalid_upper a [2,4,8,6,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,3,4] 30 (by decide +kernel))
  node458
  (invalid_upper a [2,4,8,6,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,3,8] 30 (by decide +kernel)))

def cert460 : Leaf := ⟨⟨368,352,113,289,321,0,296,105,105⟩,[(5,6)],[(1,4,1),(7,5,5)],⟨7,19,268,76,50,224,193,424,312⟩,⟨7,19,268,76,50,224,193,384,272⟩,[⟨2,1266886664132940340954625,⟨499,115,440,506,50,242,243,384,272⟩⟩,⟨3,1210107567542797251681293,⟨7,19,279,119,50,242,243,384,272⟩⟩,⟨4,1210144479353757399778305,⟨239,107,428,236,34,224,233,384,256⟩⟩]⟩
theorem node460 : UpperPrefix a [2,4,8,6,1,7,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,7,0] 30 cert460 (by decide +kernel)

def cert461 : Leaf := ⟨⟨368,356,96,288,325,0,292,117,101⟩,[(5,6)],[(1,4,1),(7,5,5),(3,6,3)],⟨7,19,268,76,50,224,200,417,305⟩,⟨7,19,268,76,50,224,200,384,272⟩,[⟨0,1210110454343042742617088,⟨6,18,268,108,122,236,236,492,272⟩⟩,⟨4,1210110454341943230989313,⟨7,3,268,108,106,236,236,492,256⟩⟩]⟩
theorem node461 : UpperPrefix a [2,4,8,6,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,7,3] 30 cert461 (by decide +kernel)

def cert462 : Leaf := ⟨⟨112,100,113,305,69,0,0,125,109⟩,[(5,6),(6,5)],[(1,4,1),(7,5,5),(7,5,6)],⟨7,19,268,76,50,224,224,393,281⟩,⟨7,19,268,76,50,224,224,384,272⟩,[⟨3,1210110454343561326369805,⟨7,19,279,119,114,224,224,480,272⟩⟩,⟨8,1184634728933225405453,⟨7,19,31,127,114,224,224,224,16⟩⟩]⟩
theorem node462 : UpperPrefix a [2,4,8,6,1,7,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,1,7,5] 30 cert462 (by decide +kernel)

theorem node463 : UpperPrefix a [2,4,8,6,1,7] 30 :=
  branch_upper a [2,4,8,6,1,7] 30 (by decide) (fin9_cases _
  node460
  (invalid_upper a [2,4,8,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,2] 30 (by decide +kernel))
  node461
  (invalid_upper a [2,4,8,6,1,7,4] 30 (by decide +kernel))
  node462
  (invalid_upper a [2,4,8,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,7,8] 30 (by decide +kernel)))

theorem node464 : UpperPrefix a [2,4,8,6,1] 30 :=
  branch_upper a [2,4,8,6,1] 30 (by decide) (fin9_cases _
  node456
  (invalid_upper a [2,4,8,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,2] 30 (by decide +kernel))
  node459
  (invalid_upper a [2,4,8,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,1,6] 30 (by decide +kernel))
  node463
  (invalid_upper a [2,4,8,6,1,8] 30 (by decide +kernel)))

def cert465 : Leaf := ⟨⟨312,300,176,432,324,274,304,48,160⟩,[],[(6,3,4),(1,6,5)],⟨7,19,268,76,56,97,194,416,432⟩,⟨7,19,268,76,56,97,194,384,272⟩,[⟨0,1437223914350373028496384,⟨78,478,268,76,444,508,206,384,404⟩⟩,⟨2,1295875756003312890020865,⟨483,499,264,200,440,225,482,384,400⟩⟩,⟨3,1295875756003311817327617,⟨487,499,260,196,432,225,482,384,400⟩⟩,⟨7,1208926973945433885261325,⟨23,19,319,127,59,99,66,256,274⟩⟩]⟩
theorem node465 : UpperPrefix a [2,4,8,6,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,0,1] 30 cert465 (by decide +kernel)

def cert466 : Leaf := ⟨⟨24,12,147,435,71,18,275,19,131⟩,[],[(6,3,4)],⟨7,19,268,76,56,97,224,386,402⟩,⟨7,19,268,76,56,97,224,384,272⟩,[⟨5,1297683481647887879906583,⟨391,407,399,205,415,193,192,387,407⟩⟩,⟨2,1219580598975202487960577,⟨483,499,264,72,120,225,224,384,272⟩⟩,⟨3,1219580598975201415267329,⟨487,499,260,68,112,225,224,384,272⟩⟩,⟨7,1208926973945433885261325,⟨23,19,319,127,59,99,96,256,274⟩⟩,⟨8,1181745951522121858573,⟨23,19,63,127,59,99,224,128,18⟩⟩]⟩
theorem node466 : UpperPrefix a [2,4,8,6,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,0,5] 30 cert466 (by decide +kernel)

theorem node467 : UpperPrefix a [2,4,8,6,3,0] 30 :=
  branch_upper a [2,4,8,6,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,3,0,0] 30 (by decide +kernel))
  node465
  (invalid_upper a [2,4,8,6,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,4] 30 (by decide +kernel))
  node466
  (invalid_upper a [2,4,8,6,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,0,8] 30 (by decide +kernel)))

def cert468 : Leaf := ⟨⟨312,300,176,432,324,273,304,48,160⟩,[],[(6,3,4),(0,6,5)],⟨7,19,268,76,56,98,193,416,432⟩,⟨7,19,268,76,56,98,193,384,272⟩,[⟨1,1437223914350364438560769,⟨77,477,268,76,444,508,201,384,404⟩⟩,⟨2,1295580608098133537195009,⟨483,499,264,72,440,482,225,384,400⟩⟩,⟨3,1295580608098132464501761,⟨487,499,260,68,432,482,225,384,400⟩⟩,⟨7,1208926976197233698946573,⟨23,19,319,127,59,98,99,256,274⟩⟩]⟩
theorem node468 : UpperPrefix a [2,4,8,6,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,1,0] 30 cert468 (by decide +kernel)

def cert469 : Leaf := ⟨⟨280,268,145,401,325,273,273,17,129⟩,[],[(6,3,4)],⟨7,19,268,76,56,98,224,385,401⟩,⟨7,19,268,76,56,98,224,384,272⟩,[⟨1,1219580544833066022469633,⟨389,413,268,92,124,508,252,388,284⟩⟩,⟨5,1297978629553080126022967,⟨391,407,399,205,415,463,205,387,407⟩⟩,⟨2,1219580598975202487960577,⟨483,499,264,72,120,482,224,384,272⟩⟩,⟨3,1219580598975201415267329,⟨487,499,260,68,112,482,224,384,272⟩⟩,⟨7,1208926973945433885261325,⟨23,19,319,127,59,98,96,256,274⟩⟩]⟩
theorem node469 : UpperPrefix a [2,4,8,6,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,1,5] 30 cert469 (by decide +kernel)

theorem node470 : UpperPrefix a [2,4,8,6,3,1] 30 :=
  branch_upper a [2,4,8,6,3,1] 30 (by decide) (fin9_cases _
  node468
  (invalid_upper a [2,4,8,6,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,1,4] 30 (by decide +kernel))
  node469
  (invalid_upper a [2,4,8,6,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,1,8] 30 (by decide +kernel)))

def cert471 : Leaf := ⟨⟨56,44,51,307,67,0,307,51,35⟩,[(5,6)],[(6,3,4),(7,5,5)],⟨7,19,268,76,56,224,227,419,307⟩,⟨7,19,268,76,56,224,192,384,272⟩,[⟨2,1219580024766799754036225,⟨483,499,280,120,56,224,224,384,272⟩⟩,⟨3,1219580024766248925529089,⟨487,499,260,100,48,224,224,384,272⟩⟩,⟨8,1181747921572080925709,⟨7,19,31,127,59,224,224,128,18⟩⟩]⟩
theorem node471 : UpperPrefix a [2,4,8,6,3,7] 30 :=
  Boolean.leaf_sound a [2,4,8,6,3,7] 30 cert471 (by decide +kernel)

theorem node472 : UpperPrefix a [2,4,8,6,3] 30 :=
  branch_upper a [2,4,8,6,3] 30 (by decide) (fin9_cases _
  node467
  node470
  (invalid_upper a [2,4,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,3,6] 30 (by decide +kernel))
  node471
  (invalid_upper a [2,4,8,6,3,8] 30 (by decide +kernel)))

def cert473 : Leaf := ⟨⟨208,196,208,400,68,150,20,124,236⟩,[],[(1,6,5)],⟨7,19,268,76,176,97,194,424,312⟩,⟨7,19,268,76,176,97,194,384,272⟩,[⟨0,1437223914350373028496384,⟨78,478,268,76,444,508,206,384,404⟩⟩,⟨3,1210107853870468531508237,⟨39,115,295,119,242,115,242,384,336⟩⟩,⟨5,1210110158231399522510293,⟨7,91,271,77,223,73,207,463,351⟩⟩,⟨8,1182034255840430543885,⟨39,115,47,127,242,115,242,128,80⟩⟩]⟩
theorem node473 : UpperPrefix a [2,4,8,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,1] 30 cert473 (by decide +kernel)

def cert474 : Leaf := ⟨⟨464,384,193,385,259,388,261,51,163⟩,[],[(3,6,3)],⟨7,19,268,76,176,97,200,418,306⟩,⟨7,19,268,76,176,97,200,384,272⟩,[⟨5,1210110158231399522510229,⟨7,91,271,77,223,73,205,463,351⟩⟩,⟨1,1210110159427668173389825,⟨37,121,268,76,252,105,204,460,348⟩⟩,⟨2,1437223878321562707837953,⟨3,403,264,72,434,499,200,384,400⟩⟩,⟨4,1210110159426568661763073,⟨39,107,268,76,236,105,204,460,332⟩⟩,⟨6,1437222725400058102039553,⟨7,403,268,12,434,435,136,384,400⟩⟩]⟩
theorem node474 : UpperPrefix a [2,4,8,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,3] 30 cert474 (by decide +kernel)

def cert475 : Leaf := ⟨⟨432,420,176,432,0,404,0,62,174⟩,[(4,6),(6,4)],[],⟨7,19,268,76,176,97,224,394,282⟩,⟨7,19,268,76,176,97,224,384,272⟩,[⟨6,1247996024694144546919437,⟨135,19,399,415,178,51,178,384,272⟩⟩,⟨0,1219580833063476827784192,⟨398,478,268,92,252,252,252,396,348⟩⟩,⟨1,1210107853589039826337793,⟨37,121,268,92,252,121,252,396,348⟩⟩,⟨3,1210107853870468531508237,⟨39,115,295,119,242,115,242,384,336⟩⟩]⟩
theorem node475 : UpperPrefix a [2,4,8,6,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,0,5] 30 cert475 (by decide +kernel)

theorem node476 : UpperPrefix a [2,4,8,6,7,0] 30 :=
  branch_upper a [2,4,8,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,7,0,0] 30 (by decide +kernel))
  node473
  (invalid_upper a [2,4,8,6,7,0,2] 30 (by decide +kernel))
  node474
  (invalid_upper a [2,4,8,6,7,0,4] 30 (by decide +kernel))
  node475
  (invalid_upper a [2,4,8,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,0,8] 30 (by decide +kernel)))

def cert477 : Leaf := ⟨⟨464,448,208,400,320,401,280,120,232⟩,[],[(0,6,5)],⟨7,19,268,76,176,98,193,424,312⟩,⟨7,19,268,76,176,98,193,384,272⟩,[⟨1,1437223914350364438560769,⟨77,477,268,76,444,508,201,384,404⟩⟩,⟨2,1266886664201247500830209,⟨499,115,440,506,176,114,243,384,272⟩⟩,⟨5,1210110158231399522510229,⟨7,91,271,77,223,74,205,463,351⟩⟩,⟨3,1210107567821523449320461,⟨7,19,295,119,176,114,243,384,272⟩⟩]⟩
theorem node477 : UpperPrefix a [2,4,8,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,0] 30 cert477 (by decide +kernel)

def cert478 : Leaf := ⟨⟨208,196,192,384,71,132,260,119,231⟩,[],[(3,6,3)],⟨7,19,268,76,176,98,200,417,305⟩,⟨7,19,268,76,176,98,200,384,272⟩,[⟨5,1210110158231399522510229,⟨7,91,271,77,223,74,205,463,351⟩⟩,⟨0,1210110159427668173390848,⟨38,122,268,76,252,106,204,460,348⟩⟩,⟨4,1210110159426568661763073,⟨39,107,268,76,236,106,204,460,332⟩⟩,⟨8,1181748206895348356109,⟨7,19,47,127,176,114,251,128,16⟩⟩,⟨1,1210110159357299429212161,⟨5,89,268,76,252,104,204,460,348⟩⟩]⟩
theorem node478 : UpperPrefix a [2,4,8,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,3] 30 cert478 (by decide +kernel)

def cert479 : Leaf := ⟨⟨432,420,176,432,0,404,0,61,173⟩,[(4,6),(6,4)],[],⟨7,19,268,76,176,98,224,393,281⟩,⟨7,19,268,76,176,98,224,384,272⟩,[⟨6,1247996024694144546903053,⟨135,19,399,415,176,50,176,384,272⟩⟩,⟨1,1219580833063476836171777,⟨397,477,268,92,252,508,252,396,348⟩⟩,⟨0,1210107853589039826338816,⟨38,122,268,92,252,122,252,396,348⟩⟩,⟨3,1210107853870468531491853,⟨39,115,295,119,240,114,240,384,336⟩⟩]⟩
theorem node479 : UpperPrefix a [2,4,8,6,7,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,1,5] 30 cert479 (by decide +kernel)

theorem node480 : UpperPrefix a [2,4,8,6,7,1] 30 :=
  branch_upper a [2,4,8,6,7,1] 30 (by decide) (fin9_cases _
  node477
  (invalid_upper a [2,4,8,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,2] 30 (by decide +kernel))
  node478
  (invalid_upper a [2,4,8,6,7,1,4] 30 (by decide +kernel))
  node479
  (invalid_upper a [2,4,8,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,1,8] 30 (by decide +kernel)))

def cert481 : Leaf := ⟨⟨392,396,129,385,269,0,270,29,173⟩,[(5,3)],[(4,1,7),(6,3,5),(1,7,6)],⟨7,19,268,76,176,104,193,386,304⟩,⟨7,19,268,76,176,104,193,386,272⟩,[⟨5,1212513080834181485962645,⟨207,91,463,205,223,72,205,463,479⟩⟩]⟩
theorem node481 : UpperPrefix a [2,4,8,6,7,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,3,0,1] 30 cert481 (by decide +kernel)

def cert482 : Leaf := ⟨⟨400,388,147,403,0,0,278,23,135⟩,[(4,7),(5,3)],[(6,3,5),(5,7,4)],⟨7,19,268,76,176,104,193,416,274⟩,⟨7,19,268,76,176,104,193,416,272⟩,[⟨3,2353363588496618222044169,⟨327,467,261,327,498,499,467,498,400⟩⟩]⟩
theorem node482 : UpperPrefix a [2,4,8,6,7,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,3,0,5] 30 cert482 (by decide +kernel)

theorem node483 : UpperPrefix a [2,4,8,6,7,3,0] 30 :=
  branch_upper a [2,4,8,6,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,6,7,3,0,0] 30 (by decide +kernel))
  node481
  (invalid_upper a [2,4,8,6,7,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,0,4] 30 (by decide +kernel))
  node482
  (invalid_upper a [2,4,8,6,7,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,0,8] 30 (by decide +kernel)))

def cert484 : Leaf := ⟨⟨408,396,144,400,268,0,285,28,172⟩,[(5,3)],[(6,3,5),(0,7,6)],⟨7,19,268,76,176,104,194,385,304⟩,⟨7,19,268,76,176,104,194,385,272⟩,[⟨5,1212512936718993410106837,⟨207,91,463,205,223,73,207,463,479⟩⟩,⟨1,1776809992509968574578689,⟨133,405,300,380,444,380,508,385,276⟩⟩]⟩
theorem node484 : UpperPrefix a [2,4,8,6,7,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,3,1,0] 30 cert484 (by decide +kernel)

def cert485 : Leaf := ⟨⟨280,268,19,275,0,0,285,31,15⟩,[(4,7),(5,3)],[(6,3,5),(5,7,4)],⟨7,19,268,76,176,104,194,416,273⟩,⟨7,19,268,76,176,104,194,416,272⟩,[⟨7,1293929572888075618624983,⟨263,279,303,109,319,109,367,303,279⟩⟩]⟩
theorem node485 : UpperPrefix a [2,4,8,6,7,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,3,1,5] 30 cert485 (by decide +kernel)

theorem node486 : UpperPrefix a [2,4,8,6,7,3,1] 30 :=
  branch_upper a [2,4,8,6,7,3,1] 30 (by decide) (fin9_cases _
  node484
  (invalid_upper a [2,4,8,6,7,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,4] 30 (by decide +kernel))
  node485
  (invalid_upper a [2,4,8,6,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,1,8] 30 (by decide +kernel)))

def cert487 : Leaf := ⟨⟨432,420,179,435,0,0,0,55,167⟩,[(4,6),(5,3),(6,4)],[(6,3,5)],⟨7,19,268,76,176,104,224,387,275⟩,⟨7,19,268,76,176,104,224,384,272⟩,[⟨3,1408881320747833410737165,⟨391,467,391,471,498,499,498,384,336⟩⟩]⟩
theorem node487 : UpperPrefix a [2,4,8,6,7,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,6,7,3,5] 30 cert487 (by decide +kernel)

theorem node488 : UpperPrefix a [2,4,8,6,7,3] 30 :=
  branch_upper a [2,4,8,6,7,3] 30 (by decide) (fin9_cases _
  node483
  node486
  (invalid_upper a [2,4,8,6,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,4] 30 (by decide +kernel))
  node487
  (invalid_upper a [2,4,8,6,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,3,8] 30 (by decide +kernel)))

theorem node489 : UpperPrefix a [2,4,8,6,7] 30 :=
  branch_upper a [2,4,8,6,7] 30 (by decide) (fin9_cases _
  node476
  node480
  (invalid_upper a [2,4,8,6,7,2] 30 (by decide +kernel))
  node488
  (invalid_upper a [2,4,8,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,7,8] 30 (by decide +kernel)))

theorem node490 : UpperPrefix a [2,4,8,6] 30 :=
  branch_upper a [2,4,8,6] 30 (by decide) (fin9_cases _
  node455
  node464
  (invalid_upper a [2,4,8,6,2] 30 (by decide +kernel))
  node472
  (invalid_upper a [2,4,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,6,6] 30 (by decide +kernel))
  node489
  (invalid_upper a [2,4,8,6,8] 30 (by decide +kernel)))

def cert491 : Leaf := ⟨⟨248,0,128,256,206,156,60,124,236⟩,[(1,4)],[(8,2,3),(0,4,1),(1,5,4)],⟨7,19,268,140,49,98,232,488,376⟩,⟨7,19,268,140,49,98,192,384,272⟩,[⟨4,1210107565282777977848833,⟨7,3,268,140,33,106,204,396,256⟩⟩,⟨5,1210107564157977582642177,⟨7,19,268,140,19,74,204,396,274⟩⟩,⟨6,1210106412362372882637825,⟨7,19,268,140,51,42,140,396,274⟩⟩]⟩
theorem node491 : UpperPrefix a [2,4,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,1] 30 cert491 (by decide +kernel)

def cert492 : Leaf := ⟨⟨120,0,112,368,78,148,50,114,98⟩,[(1,4)],[(8,2,3),(7,3,5),(0,4,1)],⟨7,19,268,140,49,104,226,482,370⟩,⟨7,19,268,140,49,104,192,384,272⟩,[⟨1,1210107567535677303160833,⟨5,17,268,140,49,104,236,396,272⟩⟩,⟨2,1285813291192731836621825,⟨3,467,264,136,499,104,192,384,466⟩⟩,⟨3,1285813291192730763928577,⟨7,467,260,132,499,96,192,384,466⟩⟩]⟩
theorem node492 : UpperPrefix a [2,4,8,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,0,3] 30 cert492 (by decide +kernel)

theorem node493 : UpperPrefix a [2,4,8,7,0] 30 :=
  branch_upper a [2,4,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,8,7,0,0] 30 (by decide +kernel))
  node491
  (invalid_upper a [2,4,8,7,0,2] 30 (by decide +kernel))
  node492
  (invalid_upper a [2,4,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,0,8] 30 (by decide +kernel)))

def cert494 : Leaf := ⟨⟨248,160,128,256,129,156,60,124,236⟩,[],[(8,2,3),(1,4,1),(0,5,4)],⟨7,19,268,140,50,97,232,488,376⟩,⟨7,19,268,140,50,97,192,384,272⟩,[⟨6,1210106412364571905901569,⟨7,19,268,140,50,59,140,396,272⟩⟩,⟨2,1210107565286050708341761,⟨3,19,264,136,50,115,192,384,272⟩⟩,⟨3,1210107565286049635648513,⟨7,19,260,132,50,115,192,384,272⟩⟩,⟨4,1210107565282777977848833,⟨7,3,268,140,34,105,204,396,256⟩⟩,⟨5,1210107564157977582633985,⟨7,19,268,140,18,73,204,396,272⟩⟩]⟩
theorem node494 : UpperPrefix a [2,4,8,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,0] 30 cert494 (by decide +kernel)

def cert495 : Leaf := ⟨⟨120,108,96,352,77,132,48,113,97⟩,[],[(8,2,3),(7,3,5),(1,4,1)],⟨7,19,268,140,50,104,193,480,368⟩,⟨7,19,268,140,50,104,193,384,272⟩,[⟨0,1210107567535677303161856,⟨6,18,268,140,50,104,236,396,272⟩⟩,⟨2,1285813038991152703865857,⟨67,467,264,136,498,104,193,384,400⟩⟩,⟨3,1285813038991151631172609,⟨71,467,260,132,498,96,193,384,400⟩⟩,⟨4,1210107567534577791534081,⟨7,3,268,140,34,104,237,396,256⟩⟩]⟩
theorem node495 : UpperPrefix a [2,4,8,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,3,0] 30 cert495 (by decide +kernel)

def cert496 : Leaf := ⟨⟨120,104,112,368,72,144,24,121,105⟩,[],[(8,2,3),(7,3,5),(1,4,1)],⟨7,19,268,140,50,104,224,449,337⟩,⟨7,19,268,140,50,104,224,384,272⟩,[⟨2,1224302785630815106631169,⟨499,467,360,232,498,104,224,384,336⟩⟩,⟨0,1210110022419755404624896,⟨54,18,364,236,50,104,236,492,272⟩⟩]⟩
theorem node496 : UpperPrefix a [2,4,8,7,1,3,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,1,3,5] 30 cert496 (by decide +kernel)

theorem node497 : UpperPrefix a [2,4,8,7,1,3] 30 :=
  branch_upper a [2,4,8,7,1,3] 30 (by decide) (fin9_cases _
  node495
  (invalid_upper a [2,4,8,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,4] 30 (by decide +kernel))
  node496
  (invalid_upper a [2,4,8,7,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,3,8] 30 (by decide +kernel)))

theorem node498 : UpperPrefix a [2,4,8,7,1] 30 :=
  branch_upper a [2,4,8,7,1] 30 (by decide) (fin9_cases _
  node494
  (invalid_upper a [2,4,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,2] 30 (by decide +kernel))
  node497
  (invalid_upper a [2,4,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,1,8] 30 (by decide +kernel)))

def cert499 : Leaf := ⟨⟨248,172,128,256,132,146,51,115,227⟩,[],[(8,2,3)],⟨7,19,268,140,56,97,226,482,370⟩,⟨7,19,268,140,56,97,192,384,272⟩,[⟨2,1219580022514450184537089,⟨483,499,264,136,56,225,192,384,272⟩⟩,⟨3,1219580022514449111843841,⟨487,499,260,132,48,225,192,384,272⟩⟩,⟨6,1210106412364571905901569,⟨7,19,268,140,58,59,140,396,272⟩⟩,⟨0,1210107565286076512732160,⟨6,18,268,140,56,120,204,396,272⟩⟩,⟨1,1210107565286076512731137,⟨5,17,268,140,56,121,204,396,272⟩⟩,⟨4,1210107565282777977848833,⟨7,3,268,140,40,105,204,396,256⟩⟩,⟨5,1210107564157977582633985,⟨7,19,268,140,24,73,204,396,272⟩⟩]⟩
theorem node499 : UpperPrefix a [2,4,8,7,3,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,0] 30 cert499 (by decide +kernel)

def cert500 : Leaf := ⟨⟨248,236,176,304,132,145,50,112,224⟩,[],[(8,2,3),(0,6,5)],⟨7,19,268,140,56,98,193,480,368⟩,⟨7,19,268,140,56,98,193,384,272⟩,[⟨1,1361518440643091034537985,⟨5,29,268,140,444,508,205,396,284⟩⟩,⟨2,1219875170419629537362945,⟨483,499,264,136,184,482,225,384,272⟩⟩,⟨3,1219875170419628464669697,⟨487,499,260,132,176,482,225,384,272⟩⟩,⟨6,1210106412364571905885185,⟨7,19,268,140,56,58,141,396,272⟩⟩]⟩
theorem node500 : UpperPrefix a [2,4,8,7,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,1,0] 30 cert500 (by decide +kernel)

def cert501 : Leaf := ⟨⟨184,172,160,288,132,145,19,115,227⟩,[],[(8,2,3)],⟨7,19,268,140,56,98,224,449,337⟩,⟨7,19,268,140,56,98,224,384,272⟩,[⟨6,1210106412368969952445505,⟨7,19,268,140,58,59,191,396,272⟩⟩,⟨2,1219580598975202487960577,⟨483,499,264,136,120,482,224,384,272⟩⟩,⟨3,1219580598975201415267329,⟨487,499,260,132,112,482,224,384,272⟩⟩,⟨0,1210107565290474559243264,⟨6,18,268,140,56,122,252,396,272⟩⟩,⟨1,1210107565290474559242241,⟨5,17,268,140,56,120,252,396,272⟩⟩,⟨4,1210107565282777977848833,⟨7,3,268,140,40,106,236,396,256⟩⟩]⟩
theorem node501 : UpperPrefix a [2,4,8,7,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,3,1,5] 30 cert501 (by decide +kernel)

theorem node502 : UpperPrefix a [2,4,8,7,3,1] 30 :=
  branch_upper a [2,4,8,7,3,1] 30 (by decide) (fin9_cases _
  node500
  (invalid_upper a [2,4,8,7,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,4] 30 (by decide +kernel))
  node501
  (invalid_upper a [2,4,8,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,1,8] 30 (by decide +kernel)))

theorem node503 : UpperPrefix a [2,4,8,7,3] 30 :=
  branch_upper a [2,4,8,7,3] 30 (by decide) (fin9_cases _
  node499
  node502
  (invalid_upper a [2,4,8,7,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,3,8] 30 (by decide +kernel)))

def cert504 : Leaf := ⟨⟨184,32,128,256,0,158,63,63,175⟩,[(4,5)],[(8,2,3),(6,4,4)],⟨7,19,268,140,112,97,234,426,314⟩,⟨7,19,268,140,112,97,192,384,272⟩,[⟨0,1210107565286076512732160,⟨6,18,268,140,120,120,204,396,272⟩⟩,⟨1,1210107565286076512731137,⟨5,17,268,140,120,121,204,396,272⟩⟩,⟨4,1210107565282777977848833,⟨7,3,268,140,104,105,204,396,256⟩⟩,⟨5,1210107564157977582633985,⟨7,19,268,140,88,73,204,396,272⟩⟩,⟨2,1210107565286050708341761,⟨3,19,264,136,114,115,192,384,272⟩⟩,⟨3,1210107565286049635648513,⟨7,19,260,132,114,115,192,384,272⟩⟩,⟨7,1208926973665333298086913,⟨7,19,268,12,114,115,64,256,272⟩⟩]⟩
theorem node504 : UpperPrefix a [2,4,8,7,6,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,0] 30 cert504 (by decide +kernel)

def cert505 : Leaf := ⟨⟨176,164,176,304,0,149,52,60,172⟩,[(4,5)],[(8,2,3),(6,4,4),(0,6,5)],⟨7,19,268,140,112,98,193,424,312⟩,⟨7,19,268,140,112,98,193,384,272⟩,[⟨1,1437223914350426682032129,⟨77,477,268,140,508,508,205,396,412⟩⟩,⟨3,1210107712643422623931917,⟨55,51,375,247,114,114,243,384,304⟩⟩]⟩
theorem node505 : UpperPrefix a [2,4,8,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,1,0] 30 cert505 (by decide +kernel)

def cert506 : Local := ⟨⟨56,44,51,307,0,29,0,63,47⟩,[(4,5),(6,3)],[(8,2,3),(7,3,6),(6,4,4)]⟩
theorem node506 : UpperPrefix a [2,4,8,7,6,1,3] 30 :=
  local_sound a [2,4,8,7,6,1,3] 30 cert506 (by decide +kernel)

def cert507 : Leaf := ⟨⟨152,140,145,273,0,157,29,29,141⟩,[(4,5)],[(8,2,3),(6,4,4),(5,6,4)],⟨7,19,268,140,112,98,224,393,281⟩,⟨7,19,268,140,112,98,224,384,272⟩,[⟨1,1219580544833081424216065,⟨397,413,268,140,124,508,252,396,272⟩⟩]⟩
theorem node507 : UpperPrefix a [2,4,8,7,6,1,5] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,1,5] 30 cert507 (by decide +kernel)

theorem node508 : UpperPrefix a [2,4,8,7,6,1] 30 :=
  branch_upper a [2,4,8,7,6,1] 30 (by decide) (fin9_cases _
  node505
  (invalid_upper a [2,4,8,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,2] 30 (by decide +kernel))
  node506
  (invalid_upper a [2,4,8,7,6,1,4] 30 (by decide +kernel))
  node507
  (invalid_upper a [2,4,8,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,1,8] 30 (by decide +kernel)))

def cert509 : Leaf := ⟨⟨56,44,32,288,0,132,63,63,47⟩,[(4,5)],[(8,2,3),(7,3,5),(6,4,4)],⟨7,19,268,140,112,104,227,419,307⟩,⟨7,19,268,140,112,104,192,384,272⟩,[⟨0,1210107568105224326349824,⟨6,50,268,140,120,120,252,396,304⟩⟩,⟨1,1210107568105224326348801,⟨5,49,268,140,120,120,252,396,304⟩⟩,⟨4,1210107568097527744955393,⟨7,35,268,140,104,104,236,396,288⟩⟩]⟩
theorem node509 : UpperPrefix a [2,4,8,7,6,3] 30 :=
  Boolean.leaf_sound a [2,4,8,7,6,3] 30 cert509 (by decide +kernel)

theorem node510 : UpperPrefix a [2,4,8,7,6] 30 :=
  branch_upper a [2,4,8,7,6] 30 (by decide) (fin9_cases _
  node504
  node508
  (invalid_upper a [2,4,8,7,6,2] 30 (by decide +kernel))
  node509
  (invalid_upper a [2,4,8,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,6,8] 30 (by decide +kernel)))

theorem node511 : UpperPrefix a [2,4,8,7] 30 :=
  branch_upper a [2,4,8,7] 30 (by decide) (fin9_cases _
  node493
  node498
  (invalid_upper a [2,4,8,7,2] 30 (by decide +kernel))
  node503
  (invalid_upper a [2,4,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,5] 30 (by decide +kernel))
  node510
  (invalid_upper a [2,4,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,8,7,8] 30 (by decide +kernel)))

#print axioms node511
end Delivery.FiniteExclusion.Sharp2x2x5
