import RegularNineSharp3x6Base
import RegularNineSharp3x6C006
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node448 : UpperPrefix a [3,4,5,7,8] 30 :=
  branch_upper a [3,4,5,7,8] 30 (by decide) (fin9_cases _
  node443
  node446
  node447
  (invalid_upper a [3,4,5,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,8,8] 30 (by decide +kernel)))

theorem node449 : UpperPrefix a [3,4,5,7] 30 :=
  branch_upper a [3,4,5,7] 30 (by decide) (fin9_cases _
  node427
  node433
  node434
  (invalid_upper a [3,4,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,7,5] 30 (by decide +kernel))
  node442
  (invalid_upper a [3,4,5,7,7] 30 (by decide +kernel))
  node448)

def cert450 : Leaf := ⟨⟨468,481,0,198,0,390,262,70,198⟩,[(2,4),(4,2)],[(4,1,0),(5,2,1),(0,4,1)],⟨11,22,37,280,49,230,198,454,462⟩,⟨11,22,37,280,49,96,192,384,264⟩,[⟨3,1210181514706734986575361,⟨247,22,119,502,119,96,192,384,482⟩⟩]⟩
theorem node450 : UpperPrefix a [3,4,5,8,0] 30 :=
  Boolean.leaf_sound a [3,4,5,8,0] 30 cert450 (by decide +kernel)

def cert451 : Leaf := ⟨⟨404,424,0,196,396,396,268,76,196⟩,[(2,5)],[(4,1,0),(5,2,1),(0,5,2)],⟨11,22,37,280,50,97,196,452,460⟩,⟨11,22,37,280,50,97,192,384,264⟩,[⟨1,1300340804888244264370177,⟨493,508,485,472,508,485,192,384,264⟩⟩,⟨6,1210106412364820988849161,⟨11,22,55,283,54,55,128,384,265⟩⟩]⟩
theorem node451 : UpperPrefix a [3,4,5,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,5,8,1,0] 30 cert451 (by decide +kernel)

def cert452 : Leaf := ⟨⟨464,288,456,195,260,393,265,73,193⟩,[],[(4,1,0),(5,2,1),(2,5,4)],⟨11,22,37,280,50,100,193,449,457⟩,⟨11,22,37,280,50,100,192,384,264⟩,[⟨1,1214876138945188757504001,⟨493,244,485,280,48,228,192,384,264⟩⟩,⟨0,1210107565286325587299328,⟨10,22,54,280,50,118,192,384,264⟩⟩,⟨3,1210107565286324513557505,⟨3,22,55,272,50,118,192,384,256⟩⟩,⟨6,1210106412364820980452353,⟨11,22,55,280,50,54,128,384,264⟩⟩,⟨7,1208926973665608175995905,⟨11,22,55,280,50,118,64,256,264⟩⟩]⟩
theorem node452 : UpperPrefix a [3,4,5,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,8,1,2] 30 cert452 (by decide +kernel)

def cert453 : Leaf := ⟨⟨340,360,328,71,332,0,269,77,69⟩,[(5,6)],[(4,1,0),(5,2,1),(7,5,5)],⟨11,22,37,280,50,224,197,453,333⟩,⟨11,22,37,280,50,224,192,384,264⟩,[⟨1,1214876141196988571189249,⟨493,244,485,280,48,224,224,384,264⟩⟩,⟨0,1210107567535926377712640,⟨10,22,54,280,50,224,224,384,264⟩⟩]⟩
theorem node453 : UpperPrefix a [3,4,5,8,1,7] 30 :=
  Boolean.leaf_sound a [3,4,5,8,1,7] 30 cert453 (by decide +kernel)

theorem node454 : UpperPrefix a [3,4,5,8,1] 30 :=
  branch_upper a [3,4,5,8,1] 30 (by decide) (fin9_cases _
  node451
  (invalid_upper a [3,4,5,8,1,1] 30 (by decide +kernel))
  node452
  (invalid_upper a [3,4,5,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,1,6] 30 (by decide +kernel))
  node453
  (invalid_upper a [3,4,5,8,1,8] 30 (by decide +kernel)))

def cert455 : Local := ⟨⟨464,0,458,195,0,395,267,75,195⟩,[(1,4),(4,2)],[(4,1,0),(5,2,1),(5,2,4),(2,4,1)]⟩
theorem node455 : UpperPrefix a [3,4,5,8,2] 30 :=
  local_sound a [3,4,5,8,2] 30 cert455 (by decide +kernel)

def cert456 : Local := ⟨⟨404,424,0,134,0,398,270,14,134⟩,[(2,5),(4,5)],[(4,1,0),(5,2,1),(6,4,4),(0,5,2)]⟩
theorem node456 : UpperPrefix a [3,4,5,8,6,0] 30 :=
  local_sound a [3,4,5,8,6,0] 30 cert456 (by decide +kernel)

def cert457 : Leaf := ⟨⟨148,169,138,133,0,141,13,13,133⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4),(1,5,2)],⟨11,22,37,280,112,98,197,389,397⟩,⟨11,22,37,280,112,98,192,384,264⟩,[⟨8,1184058845974318128393,⟨15,54,55,63,114,114,246,247,15⟩⟩]⟩
theorem node457 : UpperPrefix a [3,4,5,8,6,1] 30 :=
  Boolean.leaf_sound a [3,4,5,8,6,1] 30 cert457 (by decide +kernel)

def cert458 : Leaf := ⟨⟨400,425,394,131,0,395,267,11,131⟩,[(4,5)],[(4,1,0),(5,2,1),(6,4,4)],⟨11,22,37,280,112,100,195,387,395⟩,⟨11,22,37,280,112,100,192,384,264⟩,[⟨2,1224302388894241419953155,⟨459,475,505,280,112,120,192,384,264⟩⟩]⟩
theorem node458 : UpperPrefix a [3,4,5,8,6,2] 30 :=
  Boolean.leaf_sound a [3,4,5,8,6,2] 30 cert458 (by decide +kernel)

def cert459 : Local := ⟨⟨276,297,266,7,0,0,271,15,7⟩,[(4,5),(5,6)],[(4,1,0),(5,2,1),(6,4,4),(7,5,4),(7,5,5)]⟩
theorem node459 : UpperPrefix a [3,4,5,8,6,7] 30 :=
  local_sound a [3,4,5,8,6,7] 30 cert459 (by decide +kernel)

theorem node460 : UpperPrefix a [3,4,5,8,6] 30 :=
  branch_upper a [3,4,5,8,6] 30 (by decide) (fin9_cases _
  node456
  node457
  node458
  (invalid_upper a [3,4,5,8,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,6,6] 30 (by decide +kernel))
  node459
  (invalid_upper a [3,4,5,8,6,8] 30 (by decide +kernel)))

def cert461 : Leaf := ⟨⟨212,224,0,198,78,142,6,78,198⟩,[(2,5)],[(4,1,0),(5,2,1),(0,5,2)],⟨11,22,37,280,176,97,198,454,334⟩,⟨11,22,37,280,176,97,192,384,264⟩,[⟨8,1184344540876731970825,⟨47,86,39,127,246,119,246,247,47⟩⟩,⟨3,1210107853514226772485121,⟨3,86,37,338,246,101,192,384,256⟩⟩]⟩
theorem node461 : UpperPrefix a [3,4,5,8,7,0] 30 :=
  Boolean.leaf_sound a [3,4,5,8,7,0] 30 cert461 (by decide +kernel)

def cert462 : Leaf := ⟨⟨212,232,202,196,76,140,12,72,196⟩,[],[(4,1,0),(5,2,1),(1,5,2)],⟨11,22,37,280,176,98,193,388,328⟩,⟨11,22,37,280,176,98,193,388,264⟩,[⟨0,1663491643383990533032960,⟨10,158,446,280,442,378,506,414,264⟩⟩,⟨8,1184058843775311672585,⟨15,54,39,63,246,118,247,247,15⟩⟩]⟩
theorem node462 : UpperPrefix a [3,4,5,8,7,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,5,8,7,1,0,2] 30 cert462 (by decide +kernel)

def cert463 : Leaf := ⟨⟨148,169,138,133,77,141,12,13,133⟩,[],[(4,1,0),(5,2,1),(1,5,2),(6,7,4)],⟨11,22,37,280,176,98,193,448,268⟩,⟨11,22,37,280,176,98,193,448,264⟩,[⟨8,1184058843775311672585,⟨15,54,39,63,246,118,247,247,15⟩⟩]⟩
theorem node463 : UpperPrefix a [3,4,5,8,7,1,0,6] 30 :=
  Boolean.leaf_sound a [3,4,5,8,7,1,0,6] 30 cert463 (by decide +kernel)

theorem node464 : UpperPrefix a [3,4,5,8,7,1,0] 30 :=
  branch_upper a [3,4,5,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,5,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,0,1] 30 (by decide +kernel))
  node462
  (invalid_upper a [3,4,5,8,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,0,5] 30 (by decide +kernel))
  node463
  (invalid_upper a [3,4,5,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,0,8] 30 (by decide +kernel)))

def cert465 : Leaf := ⟨⟨208,233,202,193,73,141,9,73,193⟩,[],[(4,1,0),(5,2,1),(1,5,2),(2,6,5)],⟨11,22,37,280,176,98,196,449,329⟩,⟨11,22,37,280,176,98,196,384,264⟩,[⟨8,1184347425995234850057,⟨47,118,37,127,246,114,246,247,47⟩⟩]⟩
theorem node465 : UpperPrefix a [3,4,5,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,5,8,7,1,2] 30 cert465 (by decide +kernel)

theorem node466 : UpperPrefix a [3,4,5,8,7,1] 30 :=
  branch_upper a [3,4,5,8,7,1] 30 (by decide) (fin9_cases _
  node464
  (invalid_upper a [3,4,5,8,7,1,1] 30 (by decide +kernel))
  node465
  (invalid_upper a [3,4,5,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,1,8] 30 (by decide +kernel)))

def cert467 : Leaf := ⟨⟨208,232,202,194,74,139,10,74,194⟩,[],[(4,1,0),(5,2,1),(0,6,5)],⟨11,22,37,280,176,100,193,450,330⟩,⟨11,22,37,280,176,100,193,384,264⟩,[⟨2,1224302460949636434625539,⟨459,475,505,280,176,120,449,384,264⟩⟩,⟨8,1184058843775311672585,⟨15,54,39,63,246,118,247,247,15⟩⟩]⟩
theorem node467 : UpperPrefix a [3,4,5,8,7,2,0] 30 :=
  Boolean.leaf_sound a [3,4,5,8,7,2,0] 30 cert467 (by decide +kernel)

def cert468 : Leaf := ⟨⟨208,225,194,195,67,131,1,75,195⟩,[],[(4,1,0),(5,2,1)],⟨11,22,37,280,176,100,194,449,329⟩,⟨11,22,37,280,176,100,194,384,264⟩,[⟨2,1697461374384897861354563,⟨459,475,505,280,440,505,459,384,264⟩⟩,⟨8,1184347425995234866441,⟨47,118,39,127,246,118,246,247,47⟩⟩,⟨3,1210107853588993555055617,⟨39,118,39,336,242,118,242,384,256⟩⟩]⟩
theorem node468 : UpperPrefix a [3,4,5,8,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,5,8,7,2,1] 30 cert468 (by decide +kernel)

theorem node469 : UpperPrefix a [3,4,5,8,7,2] 30 :=
  branch_upper a [3,4,5,8,7,2] 30 (by decide) (fin9_cases _
  node467
  node468
  (invalid_upper a [3,4,5,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,2,8] 30 (by decide +kernel)))

theorem node470 : UpperPrefix a [3,4,5,8,7] 30 :=
  branch_upper a [3,4,5,8,7] 30 (by decide) (fin9_cases _
  node461
  node466
  node469
  (invalid_upper a [3,4,5,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,7,8] 30 (by decide +kernel)))

theorem node471 : UpperPrefix a [3,4,5,8] 30 :=
  branch_upper a [3,4,5,8] 30 (by decide) (fin9_cases _
  node450
  node454
  node455
  (invalid_upper a [3,4,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,8,5] 30 (by decide +kernel))
  node460
  node470
  (invalid_upper a [3,4,5,8,8] 30 (by decide +kernel)))

theorem node472 : UpperPrefix a [3,4,5] 30 :=
  branch_upper a [3,4,5] 30 (by decide) (fin9_cases _
  node400
  node401
  node402
  (invalid_upper a [3,4,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,5,5] 30 (by decide +kernel))
  node426
  node449
  node471)

def cert473 : Leaf := ⟨⟨432,424,424,418,396,0,296,40,160⟩,[(5,2)],[(4,1,0),(6,2,5),(1,4,3),(2,5,4)],⟨11,22,69,25,50,100,480,416,424⟩,⟨11,22,69,25,50,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,50,246,192,384,264⟩⟩]⟩
theorem node473 : UpperPrefix a [3,4,6,0,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,1,2] 30 cert473 (by decide +kernel)

def cert474 : Leaf := ⟨⟨116,104,40,102,76,0,301,109,101⟩,[(5,6)],[(4,1,0),(1,4,3),(7,5,5)],⟨11,22,69,25,50,224,484,420,300⟩,⟨11,22,69,25,50,224,192,384,264⟩,[⟨8,1181747927910135688319,⟨11,31,127,27,63,255,255,128,9⟩⟩,⟨0,1210107567535926377712640,⟨10,22,118,24,50,224,224,384,264⟩⟩]⟩
theorem node474 : UpperPrefix a [3,4,6,0,1,7] 30 :=
  Boolean.leaf_sound a [3,4,6,0,1,7] 30 cert474 (by decide +kernel)

def cert475 : Leaf := ⟨⟨368,360,296,354,328,136,296,104,224⟩,[],[(4,1,0),(1,4,3)],⟨11,22,69,25,50,352,196,416,424⟩,⟨11,22,69,25,50,352,196,384,264⟩,[⟨0,1253024023640727981427712,⟨506,246,502,440,242,498,246,384,392⟩⟩,⟨2,1315087988200010034447379,⟨411,443,489,409,443,480,480,384,264⟩⟩,⟨7,1208926973665340017370171,⟨11,31,69,27,63,383,68,256,265⟩⟩]⟩
theorem node475 : UpperPrefix a [3,4,6,0,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,1,8,2] 30 cert475 (by decide +kernel)

def cert476 : Leaf := ⟨⟨80,105,40,66,77,137,265,77,197⟩,[],[(4,1,0),(1,4,3),(8,5,6)],⟨11,22,69,25,50,352,224,388,396⟩,⟨11,22,69,25,50,352,224,384,264⟩,[⟨7,1208926973669747207498879,⟨11,31,95,27,63,383,127,256,265⟩⟩,⟨2,1210109875630462942053395,⟨11,27,65,25,59,352,224,480,264⟩⟩,⟨5,1219570743867767195173907,⟨395,415,69,25,411,320,192,384,264⟩⟩]⟩
theorem node476 : UpperPrefix a [3,4,6,0,1,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,1,8,5] 30 cert476 (by decide +kernel)

theorem node477 : UpperPrefix a [3,4,6,0,1,8] 30 :=
  branch_upper a [3,4,6,0,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,8,1] 30 (by decide +kernel))
  node475
  (invalid_upper a [3,4,6,0,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,8,4] 30 (by decide +kernel))
  node476
  (invalid_upper a [3,4,6,0,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,8,8] 30 (by decide +kernel)))

theorem node478 : UpperPrefix a [3,4,6,0,1] 30 :=
  branch_upper a [3,4,6,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,1] 30 (by decide +kernel))
  node473
  (invalid_upper a [3,4,6,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,1,6] 30 (by decide +kernel))
  node474
  node477)

def cert479 : Leaf := ⟨⟨304,0,298,290,330,394,298,42,162⟩,[(1,4)],[(4,1,0),(6,2,4),(2,4,1)],⟨11,22,69,25,52,482,482,418,426⟩,⟨11,22,69,25,52,96,192,384,264⟩,[⟨0,1252729002111147382418432,⟨506,246,502,506,246,96,192,384,488⟩⟩,⟨7,1208926973665340017370171,⟨11,31,69,27,63,127,64,256,265⟩⟩]⟩
theorem node479 : UpperPrefix a [3,4,6,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,2] 30 cert479 (by decide +kernel)

def cert480 : Leaf := ⟨⟨208,200,138,194,74,140,10,106,226⟩,[],[(4,1,0),(2,6,5)],⟨11,22,69,25,176,98,196,416,296⟩,⟨11,22,69,25,176,98,196,384,264⟩,[⟨8,1184347566765703298559,⟨47,127,127,127,255,127,255,255,47⟩⟩,⟨0,1252728878056067919023104,⟨506,246,502,440,176,114,246,384,408⟩⟩,⟨5,1210110158231339609371963,⟨15,95,69,95,223,79,196,453,271⟩⟩]⟩
theorem node480 : UpperPrefix a [3,4,6,0,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,1,2] 30 cert480 (by decide +kernel)

def cert481 : Leaf := ⟨⟨404,393,394,390,0,397,0,15,135⟩,[(4,6),(6,4)],[(4,1,0)],⟨11,22,69,25,176,98,224,388,268⟩,⟨11,22,69,25,176,98,224,384,264⟩,[⟨5,1447277352713637925495867,⟨395,415,197,411,415,463,453,384,265⟩⟩,⟨6,1238495951498398986669095,⟨395,415,415,25,185,443,185,384,264⟩⟩]⟩
theorem node481 : UpperPrefix a [3,4,6,0,7,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,1,5] 30 cert481 (by decide +kernel)

def cert482 : Leaf := ⟨⟨80,73,10,66,79,141,0,111,103⟩,[(6,7)],[(4,1,0),(8,6,6)],⟨11,22,69,25,176,98,448,420,300⟩,⟨11,22,69,25,176,98,448,384,264⟩,[⟨7,1435600564840879669388347,⟨11,287,69,283,319,367,320,256,265⟩⟩,⟨5,1210109870000963471815995,⟨11,31,69,31,223,79,453,453,267⟩⟩,⟨2,1210109871126863314682915,⟨11,27,65,25,249,107,448,448,264⟩⟩]⟩
theorem node482 : UpperPrefix a [3,4,6,0,7,1,8] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,1,8] 30 cert482 (by decide +kernel)

theorem node483 : UpperPrefix a [3,4,6,0,7,1] 30 :=
  branch_upper a [3,4,6,0,7,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,7,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,1,1] 30 (by decide +kernel))
  node480
  (invalid_upper a [3,4,6,0,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,1,4] 30 (by decide +kernel))
  node481
  (invalid_upper a [3,4,6,0,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,1,7] 30 (by decide +kernel))
  node482)

def cert484 : Leaf := ⟨⟨52,168,170,38,14,0,302,46,38⟩,[(5,2)],[(4,1,0),(6,2,5)],⟨11,22,69,25,176,100,482,418,298⟩,⟨11,22,69,25,176,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,178,246,192,384,264⟩⟩,⟨8,1181748066173722881151,⟨11,63,127,27,191,127,255,128,9⟩⟩,⟨7,1218371706769611322033155,⟨267,319,101,25,48,100,64,256,264⟩⟩]⟩
theorem node484 : UpperPrefix a [3,4,6,0,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,2] 30 cert484 (by decide +kernel)

def cert485 : Leaf := ⟨⟨84,73,10,68,333,13,13,109,101⟩,[],[(4,1,0),(8,5,4),(1,6,2)],⟨11,22,69,25,176,352,194,420,300⟩,⟨11,22,69,25,176,352,194,384,264⟩,[⟨7,1596161027650984925471835,⟨267,319,357,283,319,357,367,256,265⟩⟩,⟨5,1210107852388330378900827,⟨15,95,69,95,223,325,207,385,271⟩⟩]⟩
theorem node485 : UpperPrefix a [3,4,6,0,7,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,8,1] 30 cert485 (by decide +kernel)

def cert486 : Leaf := ⟨⟨16,200,138,2,334,142,10,110,230⟩,[],[(4,1,0),(8,5,4)],⟨11,22,69,25,176,352,196,418,298⟩,⟨11,22,69,25,176,352,196,384,264⟩,[⟨0,1215171304802025737325568,⟨506,246,502,440,176,498,246,384,280⟩⟩,⟨5,1210110158231339609371931,⟨15,95,69,95,223,325,196,453,271⟩⟩,⟨2,1210107565283851953505283,⟨11,27,65,25,176,352,192,384,264⟩⟩,⟨6,1210106412362347347706883,⟨11,31,5,25,176,288,132,384,264⟩⟩,⟨7,1208926973663134543250435,⟨11,31,69,25,48,352,68,256,264⟩⟩]⟩
theorem node486 : UpperPrefix a [3,4,6,0,7,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,8,2] 30 cert486 (by decide +kernel)

def cert487 : Leaf := ⟨⟨180,161,162,166,0,135,0,39,167⟩,[(4,6),(6,4)],[(4,1,0),(8,5,4),(8,5,6)],⟨11,22,69,25,176,352,224,390,270⟩,⟨11,22,69,25,176,352,224,384,264⟩,[⟨6,1238495951496184931027975,⟨395,415,415,25,176,304,176,384,264⟩⟩,⟨3,1212476544289225764379649,⟨7,86,87,87,240,498,240,498,502⟩⟩]⟩
theorem node487 : UpperPrefix a [3,4,6,0,7,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,7,8,5] 30 cert487 (by decide +kernel)

theorem node488 : UpperPrefix a [3,4,6,0,7,8] 30 :=
  branch_upper a [3,4,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,7,8,0] 30 (by decide +kernel))
  node485
  node486
  (invalid_upper a [3,4,6,0,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,8,4] 30 (by decide +kernel))
  node487
  (invalid_upper a [3,4,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,8,8] 30 (by decide +kernel)))

theorem node489 : UpperPrefix a [3,4,6,0,7] 30 :=
  branch_upper a [3,4,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,7,0] 30 (by decide +kernel))
  node483
  node484
  (invalid_upper a [3,4,6,0,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,7,7] 30 (by decide +kernel))
  node488)

def cert490 : Leaf := ⟨⟨432,480,418,418,130,388,290,34,162⟩,[],[(4,1,0),(2,6,5)],⟨11,22,69,25,304,98,196,416,424⟩,⟨11,22,69,25,304,98,196,384,264⟩,[⟨0,1252876452004122109971456,⟨506,246,502,440,432,98,246,384,408⟩⟩,⟨3,1212621131187581145748481,⟨103,246,103,247,498,98,246,498,502⟩⟩,⟨6,1437222725400064812909603,⟨11,415,5,409,441,443,132,384,264⟩⟩]⟩
theorem node490 : UpperPrefix a [3,4,6,0,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,1,2] 30 cert490 (by decide +kernel)

def cert491 : Leaf := ⟨⟨404,449,384,390,135,389,261,5,133⟩,[],[(4,1,0)],⟨11,22,69,25,304,98,224,388,396⟩,⟨11,22,69,25,304,98,224,384,264⟩,[⟨3,1212475968736670065497089,⟨39,118,69,119,498,98,240,498,502⟩⟩,⟨5,1447277352713637925495867,⟨395,415,197,411,415,463,453,384,265⟩⟩,⟨6,1238495951494000403285027,⟨395,415,397,25,313,443,185,384,264⟩⟩,⟨1,1255090238937968581541889,⟨397,212,453,477,496,96,224,384,396⟩⟩]⟩
theorem node491 : UpperPrefix a [3,4,6,0,8,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,1,5] 30 cert491 (by decide +kernel)

theorem node492 : UpperPrefix a [3,4,6,0,8,1] 30 :=
  branch_upper a [3,4,6,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,1,1] 30 (by decide +kernel))
  node490
  (invalid_upper a [3,4,6,0,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,1,4] 30 (by decide +kernel))
  node491
  (invalid_upper a [3,4,6,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,1,8] 30 (by decide +kernel)))

def cert493 : Leaf := ⟨⟨432,416,418,418,134,0,294,38,166⟩,[(5,2)],[(4,1,0),(6,2,5)],⟨11,22,69,25,304,100,226,418,426⟩,⟨11,22,69,25,304,100,192,384,264⟩,[⟨0,1215024613582863133068288,⟨506,246,502,472,498,246,192,384,264⟩⟩,⟨3,1212623717942617116644353,⟨103,246,101,247,498,100,208,498,502⟩⟩,⟨2,1210107565283851953505283,⟨11,27,65,25,304,96,192,384,264⟩⟩]⟩
theorem node493 : UpperPrefix a [3,4,6,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,2] 30 cert493 (by decide +kernel)

def cert494 : Leaf := ⟨⟨340,321,258,324,69,0,293,101,101⟩,[(5,6)],[(4,1,0),(7,5,5),(1,6,2)],⟨11,22,69,25,304,224,194,420,300⟩,⟨11,22,69,25,304,224,194,384,264⟩,[⟨3,1212475970636626158294017,⟨7,118,101,119,498,240,242,498,502⟩⟩,⟨5,1210107564157954220368987,⟨11,31,69,27,287,197,207,384,265⟩⟩]⟩
theorem node494 : UpperPrefix a [3,4,6,0,8,7,1] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,7,1] 30 cert494 (by decide +kernel)

def cert495 : Leaf := ⟨⟨372,352,290,358,70,0,290,102,102⟩,[(5,6)],[(4,1,0),(7,5,5)],⟨11,22,69,25,304,224,196,418,298⟩,⟨11,22,69,25,304,224,196,384,264⟩,[⟨0,1214876159212280433642496,⟨506,246,502,440,304,226,246,384,280⟩⟩,⟨3,1212621131011659285304321,⟨103,246,103,247,498,242,246,498,502⟩⟩]⟩
theorem node495 : UpperPrefix a [3,4,6,0,8,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,7,2] 30 cert495 (by decide +kernel)

def cert496 : Leaf := ⟨⟨340,353,290,326,71,0,0,71,71⟩,[(5,6),(6,5)],[(4,1,0),(7,5,5),(7,5,6)],⟨11,22,69,25,304,224,224,390,270⟩,⟨11,22,69,25,304,224,224,384,264⟩,[⟨3,1212476547097378461717505,⟨7,118,101,119,498,240,240,498,502⟩⟩,⟨5,1219570743867765047690243,⟨395,415,69,25,272,192,192,384,264⟩⟩]⟩
theorem node496 : UpperPrefix a [3,4,6,0,8,7,5] 30 :=
  Boolean.leaf_sound a [3,4,6,0,8,7,5] 30 cert496 (by decide +kernel)

theorem node497 : UpperPrefix a [3,4,6,0,8,7] 30 :=
  branch_upper a [3,4,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,8,7,0] 30 (by decide +kernel))
  node494
  node495
  (invalid_upper a [3,4,6,0,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,7,4] 30 (by decide +kernel))
  node496
  (invalid_upper a [3,4,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,7,8] 30 (by decide +kernel)))

theorem node498 : UpperPrefix a [3,4,6,0,8] 30 :=
  branch_upper a [3,4,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,8,0] 30 (by decide +kernel))
  node492
  node493
  (invalid_upper a [3,4,6,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,8,6] 30 (by decide +kernel))
  node497
  (invalid_upper a [3,4,6,0,8,8] 30 (by decide +kernel)))

theorem node499 : UpperPrefix a [3,4,6,0] 30 :=
  branch_upper a [3,4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0,0] 30 (by decide +kernel))
  node478
  node479
  (invalid_upper a [3,4,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,0,6] 30 (by decide +kernel))
  node489
  node498)

def cert500 : Leaf := ⟨⟨0,361,296,0,332,396,300,108,228⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(0,4,1)],⟨11,22,69,26,49,484,484,420,428⟩,⟨11,22,69,26,49,96,192,384,264⟩,[⟨7,1208926973665340017370171,⟨11,31,69,27,63,127,64,256,265⟩⟩]⟩
theorem node500 : UpperPrefix a [3,4,6,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,1,0] 30 cert500 (by decide +kernel)

def cert501 : Local := ⟨⟨0,0,424,0,457,393,297,41,161⟩,[(0,3),(1,4),(3,1)],[(4,1,0),(4,1,3),(6,2,4),(1,3,0),(2,4,1),(2,4,3)]⟩
theorem node501 : UpperPrefix a [3,4,6,1,2] 30 :=
  local_sound a [3,4,6,1,2] 30 cert501 (by decide +kernel)

def cert502 : Local := ⟨⟨0,489,0,0,333,0,301,109,229⟩,[(0,3),(2,5),(3,1),(5,2)],[(4,1,0),(4,1,3),(1,3,0)]⟩
theorem node502 : UpperPrefix a [3,4,6,1,7,0] 30 :=
  local_sound a [3,4,6,1,7,0] 30 cert502 (by decide +kernel)

def cert503 : Local := ⟨⟨0,425,424,0,269,0,301,45,165⟩,[(0,3),(3,1),(5,2)],[(4,1,0),(4,1,3),(6,2,5),(1,3,0)]⟩
theorem node503 : UpperPrefix a [3,4,6,1,7,2] 30 :=
  local_sound a [3,4,6,1,7,2] 30 cert503 (by decide +kernel)

def cert504 : Local := ⟨⟨0,232,0,0,332,140,44,108,228⟩,[(0,3),(2,6),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(8,5,4),(0,6,2)]⟩
theorem node504 : UpperPrefix a [3,4,6,1,7,8,0] 30 :=
  local_sound a [3,4,6,1,7,8,0] 30 cert504 (by decide +kernel)

def cert505 : Local := ⟨⟨0,233,168,0,333,141,41,109,229⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(8,5,4)]⟩
theorem node505 : UpperPrefix a [3,4,6,1,7,8,2] 30 :=
  local_sound a [3,4,6,1,7,8,2] 30 cert505 (by decide +kernel)

def cert506 : Local := ⟨⟨0,233,168,0,0,141,0,109,229⟩,[(0,3),(3,1),(4,6),(6,4)],[(4,1,0),(4,1,3),(1,3,0),(8,5,4),(8,5,6)]⟩
theorem node506 : UpperPrefix a [3,4,6,1,7,8,5] 30 :=
  local_sound a [3,4,6,1,7,8,5] 30 cert506 (by decide +kernel)

theorem node507 : UpperPrefix a [3,4,6,1,7,8] 30 :=
  branch_upper a [3,4,6,1,7,8] 30 (by decide) (fin9_cases _
  node504
  (invalid_upper a [3,4,6,1,7,8,1] 30 (by decide +kernel))
  node505
  (invalid_upper a [3,4,6,1,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,8,4] 30 (by decide +kernel))
  node506
  (invalid_upper a [3,4,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,8,8] 30 (by decide +kernel)))

theorem node508 : UpperPrefix a [3,4,6,1,7] 30 :=
  branch_upper a [3,4,6,1,7] 30 (by decide) (fin9_cases _
  node502
  (invalid_upper a [3,4,6,1,7,1] 30 (by decide +kernel))
  node503
  (invalid_upper a [3,4,6,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,7,7] 30 (by decide +kernel))
  node507)

def cert509 : Local := ⟨⟨0,489,0,0,205,0,301,109,229⟩,[(0,3),(2,5),(3,1),(5,2)],[(4,1,0),(4,1,3),(1,3,0)]⟩
theorem node509 : UpperPrefix a [3,4,6,1,8,0] 30 :=
  local_sound a [3,4,6,1,8,0] 30 cert509 (by decide +kernel)

def cert510 : Local := ⟨⟨0,425,424,0,141,0,301,45,165⟩,[(0,3),(3,1),(5,2)],[(4,1,0),(4,1,3),(6,2,5),(1,3,0)]⟩
theorem node510 : UpperPrefix a [3,4,6,1,8,2] 30 :=
  local_sound a [3,4,6,1,8,2] 30 cert510 (by decide +kernel)

def cert511 : Local := ⟨⟨0,361,296,0,77,0,301,109,101⟩,[(0,3),(3,1),(5,6)],[(4,1,0),(4,1,3),(1,3,0),(7,5,5)]⟩
theorem node511 : UpperPrefix a [3,4,6,1,8,7] 30 :=
  local_sound a [3,4,6,1,8,7] 30 cert511 (by decide +kernel)

#print axioms node511
end Delivery.FiniteExclusion.Sharp3x6
