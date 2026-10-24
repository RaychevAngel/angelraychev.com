import RegularNineSharp2x7Base
import RegularNineSharp2x7C007
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert512 : Leaf := ⟨⟨48,36,82,166,6,30,54,54,50⟩,[],[(6,3,2),(7,4,3)],⟨7,19,44,88,176,97,200,386,262⟩,⟨7,19,44,88,176,97,200,384,260⟩,[⟨8,1184347426027678332159,⟨47,127,47,127,255,127,255,255,5⟩⟩,⟨0,1224303253585101453263872,⟨462,478,124,92,252,508,200,384,268⟩⟩,⟨3,1236440292451544898621189,⟨407,403,439,80,178,499,192,387,407⟩⟩]⟩
theorem node512 : UpperPrefix a [2,4,5,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,0,3] 30 cert512 (by decide +kernel)

def cert513 : Leaf := ⟨⟨56,44,82,166,14,30,0,62,58⟩,[(6,7)],[(6,3,2),(7,4,3),(8,6,6)],⟨7,19,44,88,176,97,448,394,270⟩,⟨7,19,44,88,176,97,448,384,260⟩,[⟨0,1224305271197734515246080,⟨462,478,124,92,252,508,448,448,268⟩⟩]⟩
theorem node513 : UpperPrefix a [2,4,5,6,7,0,8] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,0,8] 30 cert513 (by decide +kernel)

theorem node514 : UpperPrefix a [2,4,5,6,7,0] 30 :=
  branch_upper a [2,4,5,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,6,7,0,0] 30 (by decide +kernel))
  node511
  (invalid_upper a [2,4,5,6,7,0,2] 30 (by decide +kernel))
  node512
  (invalid_upper a [2,4,5,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,0,7] 30 (by decide +kernel))
  node513)

def cert515 : Leaf := ⟨⟨56,44,80,164,12,29,60,60,56⟩,[],[(6,3,2),(7,4,3),(0,6,5)],⟨7,19,44,88,176,98,193,392,268⟩,⟨7,19,44,88,176,98,193,384,260⟩,[⟨8,1184347426027678332159,⟨47,127,47,127,255,127,255,255,5⟩⟩,⟨1,1508788075998994030919681,⟨477,477,444,476,444,508,457,384,404⟩⟩]⟩
theorem node515 : UpperPrefix a [2,4,5,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,1,0] 30 cert515 (by decide +kernel)

def cert516 : Leaf := ⟨⟨48,36,81,165,5,29,53,53,49⟩,[],[(6,3,2),(7,4,3)],⟨7,19,44,88,176,98,200,385,261⟩,⟨7,19,44,88,176,98,200,384,260⟩,[⟨8,1184347426027678332159,⟨47,127,47,127,255,127,255,255,5⟩⟩,⟨1,1224303253585101453262849,⟨461,477,124,92,252,508,200,384,268⟩⟩,⟨3,1236145144546365545778949,⟨407,403,439,80,176,242,192,387,407⟩⟩]⟩
theorem node516 : UpperPrefix a [2,4,5,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,1,3] 30 cert516 (by decide +kernel)

def cert517 : Leaf := ⟨⟨56,44,81,165,13,29,0,61,57⟩,[(6,7)],[(6,3,2),(7,4,3),(8,6,6)],⟨7,19,44,88,176,98,448,393,269⟩,⟨7,19,44,88,176,98,448,384,260⟩,[⟨1,1224305271197734515245057,⟨461,477,124,92,252,508,448,448,268⟩⟩]⟩
theorem node517 : UpperPrefix a [2,4,5,6,7,1,8] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,1,8] 30 cert517 (by decide +kernel)

theorem node518 : UpperPrefix a [2,4,5,6,7,1] 30 :=
  branch_upper a [2,4,5,6,7,1] 30 (by decide) (fin9_cases _
  node515
  (invalid_upper a [2,4,5,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,1,2] 30 (by decide +kernel))
  node516
  (invalid_upper a [2,4,5,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,1,7] 30 (by decide +kernel))
  node517)

def cert519 : Leaf := ⟨⟨304,292,0,391,263,0,279,23,19⟩,[(2,5),(5,3)],[(6,3,2),(6,3,5),(7,4,3),(3,5,2)],⟨7,19,44,88,176,104,451,387,263⟩,⟨7,19,44,88,176,104,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,88,144,72,192,384,260⟩⟩]⟩
theorem node519 : UpperPrefix a [2,4,5,6,7,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,3] 30 cert519 (by decide +kernel)

def cert520 : Leaf := ⟨⟨56,44,80,164,268,28,62,60,56⟩,[],[(6,3,2),(7,4,3),(8,5,4),(1,7,6)],⟨7,19,44,88,176,352,193,386,268⟩,⟨7,19,44,88,176,352,193,386,260⟩,[⟨0,1795708681813484010210304,⟨390,406,300,380,444,380,508,386,260⟩⟩]⟩
theorem node520 : UpperPrefix a [2,4,5,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,8,0,1] 30 cert520 (by decide +kernel)

def cert521 : Leaf := ⟨⟨56,44,80,164,268,30,62,52,58⟩,[],[(6,3,2),(7,4,3),(8,5,4)],⟨7,19,44,88,176,352,193,392,262⟩,⟨7,19,44,88,176,352,193,392,260⟩,[⟨0,1225160110707233113768960,⟨278,278,188,252,188,508,508,412,276⟩⟩,⟨1,1210402713191509247655937,⟨21,21,188,92,188,508,193,392,276⟩⟩]⟩
theorem node521 : UpperPrefix a [2,4,5,6,7,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,8,0,3] 30 cert521 (by decide +kernel)

theorem node522 : UpperPrefix a [2,4,5,6,7,8,0] 30 :=
  branch_upper a [2,4,5,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,6,7,8,0,0] 30 (by decide +kernel))
  node520
  (invalid_upper a [2,4,5,6,7,8,0,2] 30 (by decide +kernel))
  node521
  (invalid_upper a [2,4,5,6,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,0,8] 30 (by decide +kernel)))

def cert523 : Local := ⟨⟨56,40,82,162,266,26,57,62,58⟩,[],[(2,0,7),(6,3,2),(7,4,3),(8,5,4),(0,7,6)]⟩
theorem node523 : UpperPrefix a [2,4,5,6,7,8,1,0] 30 :=
  local_sound a [2,4,5,6,7,8,1,0] 30 cert523 (by decide +kernel)

def cert524 : Leaf := ⟨⟨40,44,65,165,269,13,45,37,41⟩,[],[(6,3,2),(7,4,3),(8,5,4)],⟨7,19,44,88,176,352,194,392,261⟩,⟨7,19,44,88,176,352,194,392,260⟩,[⟨1,1225160110707233113767937,⟨277,277,188,252,188,508,508,412,276⟩⟩,⟨4,1554951019649904984196161,⟨487,355,428,493,164,353,487,428,388⟩⟩]⟩
theorem node524 : UpperPrefix a [2,4,5,6,7,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,8,1,3] 30 cert524 (by decide +kernel)

theorem node525 : UpperPrefix a [2,4,5,6,7,8,1] 30 :=
  branch_upper a [2,4,5,6,7,8,1] 30 (by decide) (fin9_cases _
  node523
  (invalid_upper a [2,4,5,6,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,1,2] 30 (by decide +kernel))
  node524
  (invalid_upper a [2,4,5,6,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,1,8] 30 (by decide +kernel)))

def cert526 : Leaf := ⟨⟨48,36,80,164,260,28,52,55,51⟩,[],[(6,3,2),(7,4,3),(8,5,4)],⟨7,19,44,88,176,352,200,387,263⟩,⟨7,19,44,88,176,352,200,384,260⟩,[⟨0,1210110163874063362032640,⟨14,94,44,92,252,380,252,508,260⟩⟩,⟨1,1210110163874063362031617,⟨13,93,44,92,252,380,252,508,260⟩⟩,⟨3,1236440292451544898621189,⟨407,403,439,80,178,499,192,387,407⟩⟩]⟩
theorem node526 : UpperPrefix a [2,4,5,6,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,8,3] 30 cert526 (by decide +kernel)

theorem node527 : UpperPrefix a [2,4,5,6,7,8] 30 :=
  branch_upper a [2,4,5,6,7,8] 30 (by decide) (fin9_cases _
  node522
  node525
  (invalid_upper a [2,4,5,6,7,8,2] 30 (by decide +kernel))
  node526
  (invalid_upper a [2,4,5,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,8,8] 30 (by decide +kernel)))

theorem node528 : UpperPrefix a [2,4,5,6,7] 30 :=
  branch_upper a [2,4,5,6,7] 30 (by decide) (fin9_cases _
  node514
  node518
  (invalid_upper a [2,4,5,6,7,2] 30 (by decide +kernel))
  node519
  (invalid_upper a [2,4,5,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,7,7] 30 (by decide +kernel))
  node527)

def cert529 : Leaf := ⟨⟨312,300,336,388,140,270,268,12,136⟩,[],[(6,3,2),(1,6,5)],⟨7,19,44,88,304,97,194,392,396⟩,⟨7,19,44,88,304,97,194,384,260⟩,[⟨0,1508788075998994030920704,⟨478,478,444,476,444,508,458,384,404⟩⟩,⟨4,1229033942822329800197121,⟨487,99,428,72,288,97,226,384,388⟩⟩,⟨5,1233784014219753785656321,⟨463,475,396,88,272,449,202,384,388⟩⟩,⟨7,1208926973944609253626893,⟨7,19,47,127,304,97,66,256,261⟩⟩]⟩
theorem node529 : UpperPrefix a [2,4,5,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,0,1] 30 cert529 (by decide +kernel)

def cert530 : Leaf := ⟨⟨48,36,82,390,134,30,278,22,146⟩,[],[(6,3,2)],⟨7,19,44,88,304,97,200,386,390⟩,⟨7,19,44,88,304,97,200,384,260⟩,[⟨0,1224302965354725301552128,⟨462,478,124,92,380,508,200,384,268⟩⟩,⟨3,1236587866404134575042309,⟨407,403,439,210,435,499,192,387,407⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,88,272,449,200,384,260⟩⟩,⟨7,1208926976196409084089421,⟨7,19,47,127,304,101,111,256,261⟩⟩,⟨8,1181748202497320686669,⟨7,19,47,127,48,101,239,128,5⟩⟩]⟩
theorem node530 : UpperPrefix a [2,4,5,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,0,3] 30 cert530 (by decide +kernel)

theorem node531 : UpperPrefix a [2,4,5,6,8,0] 30 :=
  branch_upper a [2,4,5,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,6,8,0,0] 30 (by decide +kernel))
  node529
  (invalid_upper a [2,4,5,6,8,0,2] 30 (by decide +kernel))
  node530
  (invalid_upper a [2,4,5,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,0,8] 30 (by decide +kernel)))

def cert532 : Leaf := ⟨⟨312,300,336,388,140,269,268,12,136⟩,[],[(6,3,2),(0,6,5)],⟨7,19,44,88,304,98,193,392,396⟩,⟨7,19,44,88,304,98,193,384,260⟩,[⟨1,1508788075998994030919681,⟨477,477,444,476,444,508,457,384,404⟩⟩,⟨4,1229033942822329800197121,⟨487,99,428,72,288,98,225,384,388⟩⟩,⟨5,1233784014219753785656321,⟨463,475,396,88,272,202,449,384,388⟩⟩,⟨7,1208926973944609253626893,⟨7,19,47,127,304,98,65,256,261⟩⟩]⟩
theorem node532 : UpperPrefix a [2,4,5,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,1,0] 30 cert532 (by decide +kernel)

def cert533 : Leaf := ⟨⟨48,36,81,389,133,21,277,21,145⟩,[],[(6,3,2)],⟨7,19,44,88,304,98,200,385,389⟩,⟨7,19,44,88,304,98,200,384,260⟩,[⟨1,1224302965354725301551105,⟨461,477,124,92,380,508,200,384,268⟩⟩,⟨3,1236292718778231175655173,⟨407,403,439,242,435,226,224,387,407⟩⟩,⟨5,1214858231260882236605441,⟨463,475,76,88,344,202,200,384,260⟩⟩,⟨7,1208926976196409084097645,⟨7,19,47,127,307,103,111,256,261⟩⟩,⟨8,1181748202497320694893,⟨7,19,47,127,51,103,239,128,5⟩⟩]⟩
theorem node533 : UpperPrefix a [2,4,5,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,1,3] 30 cert533 (by decide +kernel)

theorem node534 : UpperPrefix a [2,4,5,6,8,1] 30 :=
  branch_upper a [2,4,5,6,8,1] 30 (by decide) (fin9_cases _
  node532
  (invalid_upper a [2,4,5,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,1,2] 30 (by decide +kernel))
  node533
  (invalid_upper a [2,4,5,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,1,8] 30 (by decide +kernel)))

def cert535 : Leaf := ⟨⟨432,420,0,391,135,0,279,23,147⟩,[(2,5),(5,3)],[(6,3,2),(6,3,5),(3,5,2)],⟨7,19,44,88,304,104,195,387,391⟩,⟨7,19,44,88,304,104,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,88,272,72,192,384,260⟩⟩]⟩
theorem node535 : UpperPrefix a [2,4,5,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,3] 30 cert535 (by decide +kernel)

def cert536 : Leaf := ⟨⟨56,44,64,263,15,0,287,31,27⟩,[(5,6)],[(6,3,2),(7,5,5)],⟨7,19,44,88,304,224,203,395,271⟩,⟨7,19,44,88,304,224,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,88,272,192,192,384,260⟩⟩,⟨8,1181747921022327198733,⟨7,19,47,127,48,224,224,128,5⟩⟩,⟨0,1210107567535651501900800,⟨6,18,44,124,304,224,224,384,260⟩⟩,⟨1,1210107567535651501899777,⟨5,17,44,124,304,224,224,384,260⟩⟩,⟨4,1210107567534551990273025,⟨7,3,44,108,288,224,224,384,260⟩⟩]⟩
theorem node536 : UpperPrefix a [2,4,5,6,8,7] 30 :=
  Boolean.leaf_sound a [2,4,5,6,8,7] 30 cert536 (by decide +kernel)

theorem node537 : UpperPrefix a [2,4,5,6,8] 30 :=
  branch_upper a [2,4,5,6,8] 30 (by decide) (fin9_cases _
  node531
  node534
  (invalid_upper a [2,4,5,6,8,2] 30 (by decide +kernel))
  node535
  (invalid_upper a [2,4,5,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,8,6] 30 (by decide +kernel))
  node536
  (invalid_upper a [2,4,5,6,8,8] 30 (by decide +kernel)))

theorem node538 : UpperPrefix a [2,4,5,6] 30 :=
  branch_upper a [2,4,5,6] 30 (by decide) (fin9_cases _
  node508
  node509
  (invalid_upper a [2,4,5,6,2] 30 (by decide +kernel))
  node510
  (invalid_upper a [2,4,5,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,6,6] 30 (by decide +kernel))
  node528
  node537)

def cert539 : Leaf := ⟨⟨248,0,208,68,206,140,268,76,200⟩,[(1,4)],[(0,4,1),(1,5,4)],⟨7,19,44,152,49,98,456,456,332⟩,⟨7,19,44,152,49,98,192,384,260⟩,[⟨8,1181747927902888066933,⟨23,19,63,155,55,127,255,131,23⟩⟩,⟨4,1229033996795156584465409,⟨487,35,492,136,33,98,192,384,452⟩⟩,⟨5,1233931948460315799200769,⟨463,475,460,218,475,202,192,384,452⟩⟩]⟩
theorem node539 : UpperPrefix a [2,4,5,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,7,0,1] 30 cert539 (by decide +kernel)

def cert540 : Leaf := ⟨⟨368,0,0,326,326,406,278,86,82⟩,[(1,4),(2,5)],[(7,3,5),(0,4,1),(3,5,2)],⟨7,19,44,152,49,104,450,450,326⟩,⟨7,19,44,152,49,104,192,384,260⟩,[⟨5,1215005516983095761314817,⟨463,475,12,218,475,72,192,384,260⟩⟩]⟩
theorem node540 : UpperPrefix a [2,4,5,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,0,3] 30 cert540 (by decide +kernel)

def cert541 : Leaf := ⟨⟨48,0,466,326,6,150,20,94,218⟩,[(1,4)],[(0,4,1)],⟨7,19,44,152,49,352,194,456,332⟩,⟨7,19,44,152,49,352,194,384,260⟩,[⟨3,1210110019756917523705605,⟨23,19,119,242,51,371,242,499,279⟩⟩,⟨5,1233932020517909837128705,⟨463,475,460,218,475,320,202,384,388⟩⟩,⟨8,1184195629893702283013,⟨23,19,127,218,51,115,194,195,23⟩⟩,⟨6,1210106412364820980592389,⟨23,19,63,154,51,307,130,387,279⟩⟩,⟨7,1208926973665608176135941,⟨23,19,63,26,51,371,66,259,279⟩⟩]⟩
theorem node541 : UpperPrefix a [2,4,5,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,7,0,8,1] 30 cert541 (by decide +kernel)

def cert542 : Leaf := ⟨⟨368,0,338,326,326,30,0,86,90⟩,[(1,4),(6,3)],[(7,3,6),(0,4,1)],⟨7,19,44,152,49,352,200,450,326⟩,⟨7,19,44,152,49,352,200,384,260⟩,[⟨3,1210402713191503866523397,⟨23,19,183,146,179,499,192,387,279⟩⟩,⟨5,1215005661098283837170689,⟨463,475,76,218,475,320,200,384,260⟩⟩]⟩
theorem node542 : UpperPrefix a [2,4,5,7,0,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,0,8,3] 30 cert542 (by decide +kernel)

theorem node543 : UpperPrefix a [2,4,5,7,0,8] 30 :=
  branch_upper a [2,4,5,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,0,8,0] 30 (by decide +kernel))
  node541
  (invalid_upper a [2,4,5,7,0,8,2] 30 (by decide +kernel))
  node542
  (invalid_upper a [2,4,5,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,8,8] 30 (by decide +kernel)))

theorem node544 : UpperPrefix a [2,4,5,7,0] 30 :=
  branch_upper a [2,4,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,0,0] 30 (by decide +kernel))
  node539
  (invalid_upper a [2,4,5,7,0,2] 30 (by decide +kernel))
  node540
  (invalid_upper a [2,4,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,0,7] 30 (by decide +kernel))
  node543)

def cert545 : Leaf := ⟨⟨248,232,208,64,201,140,264,72,200⟩,[],[(1,4,1),(0,5,4)],⟨7,19,44,152,50,97,456,456,332⟩,⟨7,19,44,152,50,97,192,384,260⟩,[⟨8,1181747927902888066933,⟨23,19,63,155,55,127,255,131,23⟩⟩,⟨2,1212475666056822409676289,⟨19,19,58,216,50,115,192,456,472⟩⟩,⟨4,1229033996795156584465409,⟨487,35,492,136,34,97,192,384,452⟩⟩,⟨5,1233784086277349971067905,⟨463,475,460,152,218,449,192,384,452⟩⟩]⟩
theorem node545 : UpperPrefix a [2,4,5,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,7,1,0] 30 cert545 (by decide +kernel)

def cert546 : Leaf := ⟨⟨96,100,0,101,69,133,293,101,97⟩,[(2,5)],[(7,3,5),(1,4,1),(3,5,2)],⟨7,19,44,152,50,104,449,449,325⟩,⟨7,19,44,152,50,104,192,384,260⟩,[⟨4,1328416245210460615345169,⟨487,451,492,493,487,492,192,384,292⟩⟩,⟨8,1181747927902888066933,⟨23,19,63,155,55,127,255,131,23⟩⟩]⟩
theorem node546 : UpperPrefix a [2,4,5,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,1,3] 30 cert546 (by decide +kernel)

def cert547 : Leaf := ⟨⟨176,164,401,261,133,149,20,21,217⟩,[],[(1,4,1)],⟨7,19,44,152,50,352,193,392,324⟩,⟨7,19,44,152,50,352,193,392,260⟩,[⟨6,1212762743511476507672383,⟨31,31,191,159,191,447,131,395,415⟩⟩,⟨3,1210109875646677250199301,⟨23,19,55,242,50,371,243,499,279⟩⟩,⟨5,1214857654800129933181953,⟨463,475,12,152,218,320,449,392,260⟩⟩,⟨8,1184051514705626418949,⟨23,19,63,216,50,115,195,203,23⟩⟩]⟩
theorem node547 : UpperPrefix a [2,4,5,7,1,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,1,8,0,3] 30 cert547 (by decide +kernel)

def cert548 : Leaf := ⟨⟨368,356,337,357,325,0,308,0,121⟩,[(5,7),(7,5)],[(1,4,1)],⟨7,19,44,152,50,352,193,448,268⟩,⟨7,19,44,152,50,352,193,448,260⟩,[⟨7,1265595375977387443609357,⟨279,19,319,319,50,371,115,371,279⟩⟩,⟨3,1212771476022447635156741,⟨87,19,247,242,242,499,243,499,503⟩⟩]⟩
theorem node548 : UpperPrefix a [2,4,5,7,1,8,0,6] 30 :=
  Boolean.leaf_sound a [2,4,5,7,1,8,0,6] 30 cert548 (by decide +kernel)

theorem node549 : UpperPrefix a [2,4,5,7,1,8,0] 30 :=
  branch_upper a [2,4,5,7,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,0,2] 30 (by decide +kernel))
  node547
  (invalid_upper a [2,4,5,7,1,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,0,5] 30 (by decide +kernel))
  node548
  (invalid_upper a [2,4,5,7,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,0,8] 30 (by decide +kernel)))

def cert550 : Leaf := ⟨⟨304,292,337,325,261,29,0,85,89⟩,[(6,3)],[(7,3,6),(1,4,1)],⟨7,19,44,152,50,352,200,449,325⟩,⟨7,19,44,152,50,352,200,384,260⟩,[⟨3,1210402713191503866515205,⟨23,19,183,144,178,499,192,387,279⟩⟩,⟨5,1214858087145694160749569,⟨463,475,76,216,218,320,200,384,260⟩⟩,⟨6,1210106412364820980584197,⟨23,19,63,152,50,307,136,387,279⟩⟩]⟩
theorem node550 : UpperPrefix a [2,4,5,7,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,1,8,3] 30 cert550 (by decide +kernel)

theorem node551 : UpperPrefix a [2,4,5,7,1,8] 30 :=
  branch_upper a [2,4,5,7,1,8] 30 (by decide) (fin9_cases _
  node549
  (invalid_upper a [2,4,5,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,2] 30 (by decide +kernel))
  node550
  (invalid_upper a [2,4,5,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,8,8] 30 (by decide +kernel)))

theorem node552 : UpperPrefix a [2,4,5,7,1] 30 :=
  branch_upper a [2,4,5,7,1] 30 (by decide) (fin9_cases _
  node545
  (invalid_upper a [2,4,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,2] 30 (by decide +kernel))
  node546
  (invalid_upper a [2,4,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,1,7] 30 (by decide +kernel))
  node551)

def cert553 : Leaf := ⟨⟨296,300,0,327,0,391,263,71,195⟩,[(2,4),(4,2)],[],⟨7,19,44,152,56,355,451,451,327⟩,⟨7,19,44,152,56,96,192,384,260⟩,[⟨4,1224302388996220323365891,⟨487,487,44,140,44,96,192,384,260⟩⟩,⟨3,1214857656031579466630145,⟨487,499,36,144,48,96,192,384,260⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,152,24,64,192,384,260⟩⟩,⟨6,1210106412362621961518879,⟨23,23,63,159,63,32,128,387,279⟩⟩,⟨7,1208926973663409157062431,⟨23,23,63,31,63,96,64,259,279⟩⟩]⟩
theorem node553 : UpperPrefix a [2,4,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,3] 30 cert553 (by decide +kernel)

def cert554 : Leaf := ⟨⟨56,44,146,6,0,158,286,30,26⟩,[(4,5)],[(6,4,4)],⟨7,19,44,152,112,97,458,394,270⟩,⟨7,19,44,152,112,97,192,384,260⟩,[⟨0,1224302388893970313774080,⟨462,478,60,156,124,508,192,384,260⟩⟩,⟨8,1181748490577969741183,⟨7,55,63,191,127,127,255,129,7⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,152,80,449,192,384,260⟩⟩,⟨7,1227816439596811878944005,⟨263,19,319,24,114,115,64,257,263⟩⟩]⟩
theorem node554 : UpperPrefix a [2,4,5,7,6,0] 30 :=
  Boolean.leaf_sound a [2,4,5,7,6,0] 30 cert554 (by decide +kernel)

def cert555 : Leaf := ⟨⟨56,44,145,5,0,157,285,29,25⟩,[(4,5)],[(6,4,4)],⟨7,19,44,152,112,98,457,393,269⟩,⟨7,19,44,152,112,98,192,384,260⟩,[⟨1,1224302388893970313773057,⟨461,477,60,156,124,508,192,384,260⟩⟩,⟨8,1181748490577969741183,⟨7,55,63,191,127,127,255,129,7⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,152,80,202,192,384,260⟩⟩,⟨7,1227816439596811878927621,⟨263,19,319,24,112,114,64,257,263⟩⟩]⟩
theorem node555 : UpperPrefix a [2,4,5,7,6,1] 30 :=
  Boolean.leaf_sound a [2,4,5,7,6,1] 30 cert555 (by decide +kernel)

def cert556 : Leaf := ⟨⟨304,292,0,263,0,407,279,23,19⟩,[(2,5),(4,5)],[(7,3,5),(6,4,4),(3,5,2)],⟨7,19,44,152,112,104,451,387,263⟩,⟨7,19,44,152,112,104,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,152,80,72,192,384,260⟩⟩]⟩
theorem node556 : UpperPrefix a [2,4,5,7,6,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,6,3] 30 cert556 (by decide +kernel)

def cert557 : Leaf := ⟨⟨304,292,402,262,0,150,278,30,26⟩,[(4,5)],[(6,4,4)],⟨7,19,44,152,112,352,193,394,270⟩,⟨7,19,44,152,112,352,193,384,260⟩,[⟨0,1224302337106976957268992,⟨398,414,60,156,124,380,508,384,260⟩⟩,⟨3,1210109875646402372160773,⟨7,19,55,242,114,371,243,499,263⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,152,80,320,449,384,260⟩⟩,⟨7,1227816439596811878944005,⟨263,19,319,24,114,371,65,257,263⟩⟩]⟩
theorem node557 : UpperPrefix a [2,4,5,7,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,5,7,6,8,0] 30 cert557 (by decide +kernel)

def cert558 : Leaf := ⟨⟨304,292,401,261,0,149,277,29,25⟩,[(4,5)],[(6,4,4)],⟨7,19,44,152,112,352,194,393,269⟩,⟨7,19,44,152,112,352,194,384,260⟩,[⟨1,1224302337106976957267969,⟨397,413,60,156,124,380,508,384,260⟩⟩,⟨3,1210110019761865326022405,⟨23,19,119,242,114,371,242,499,279⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,152,80,320,202,384,260⟩⟩,⟨7,1227816439596811878944005,⟨263,19,319,24,114,371,66,257,263⟩⟩]⟩
theorem node558 : UpperPrefix a [2,4,5,7,6,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,7,6,8,1] 30 cert558 (by decide +kernel)

def cert559 : Leaf := ⟨⟨304,292,275,295,0,31,0,55,51⟩,[(4,5),(6,3)],[(7,3,6),(6,4,4)],⟨7,19,44,152,112,352,200,387,263⟩,⟨7,19,44,152,112,352,200,384,260⟩,[⟨3,1236440292451270020582661,⟨391,403,439,144,242,499,192,385,391⟩⟩]⟩
theorem node559 : UpperPrefix a [2,4,5,7,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,6,8,3] 30 cert559 (by decide +kernel)

theorem node560 : UpperPrefix a [2,4,5,7,6,8] 30 :=
  branch_upper a [2,4,5,7,6,8] 30 (by decide) (fin9_cases _
  node557
  node558
  (invalid_upper a [2,4,5,7,6,8,2] 30 (by decide +kernel))
  node559
  (invalid_upper a [2,4,5,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,6,8,8] 30 (by decide +kernel)))

theorem node561 : UpperPrefix a [2,4,5,7,6] 30 :=
  branch_upper a [2,4,5,7,6] 30 (by decide) (fin9_cases _
  node554
  node555
  (invalid_upper a [2,4,5,7,6,2] 30 (by decide +kernel))
  node556
  (invalid_upper a [2,4,5,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,6,7] 30 (by decide +kernel))
  node560)

def cert562 : Leaf := ⟨⟨176,164,144,292,196,150,52,52,240⟩,[],[(8,4,3),(1,6,5)],⟨7,19,44,152,304,97,194,392,324⟩,⟨7,19,44,152,304,97,194,392,260⟩,[⟨0,1378849210743820993430528,⟨478,478,444,156,444,508,458,392,412⟩⟩,⟨3,1228999485844595475181317,⟨311,19,375,242,307,115,242,499,311⟩⟩,⟨6,1210253986314939175810079,⟨15,159,47,159,447,33,139,395,261⟩⟩]⟩
theorem node562 : UpperPrefix a [2,4,5,7,8,0,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,0,1,3] 30 cert562 (by decide +kernel)

def cert563 : Leaf := ⟨⟨112,100,80,356,68,22,52,52,120⟩,[],[(8,4,3),(1,6,5)],⟨7,19,44,152,304,97,194,448,268⟩,⟨7,19,44,152,304,97,194,448,260⟩,[⟨0,1508529821581964781552640,⟨478,478,444,412,444,508,458,448,284⟩⟩,⟨3,1212623722586954230080769,⟨103,243,100,242,499,97,242,499,503⟩⟩,⟨7,1265595375970790373801741,⟨279,19,319,319,307,99,114,371,279⟩⟩]⟩
theorem node563 : UpperPrefix a [2,4,5,7,8,0,1,6] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,0,1,6] 30 cert563 (by decide +kernel)

theorem node564 : UpperPrefix a [2,4,5,7,8,0,1] 30 :=
  branch_upper a [2,4,5,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,1,2] 30 (by decide +kernel))
  node562
  (invalid_upper a [2,4,5,7,8,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,1,5] 30 (by decide +kernel))
  node563
  (invalid_upper a [2,4,5,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,1,8] 30 (by decide +kernel)))

def cert565 : Leaf := ⟨⟨56,44,18,294,78,30,0,60,122⟩,[(6,3)],[(7,3,6),(8,4,3)],⟨7,19,44,152,304,97,200,386,324⟩,⟨7,19,44,152,304,97,200,386,260⟩,[⟨0,1507647404285373631693824,⟨478,478,380,476,380,508,456,458,276⟩⟩,⟨6,1210253986314939175810079,⟨15,159,47,159,447,33,139,395,261⟩⟩]⟩
theorem node565 : UpperPrefix a [2,4,5,7,8,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,0,3,1] 30 cert565 (by decide +kernel)

def cert566 : Leaf := ⟨⟨112,100,82,358,70,22,0,54,114⟩,[(6,3)],[(7,3,6),(8,4,3)],⟨7,19,44,152,304,97,200,448,262⟩,⟨7,19,44,152,304,97,200,448,260⟩,[⟨3,1234014550118247813050117,⟨279,275,439,178,435,499,242,499,279⟩⟩,⟨0,1227111986543105846281216,⟨462,478,252,220,508,508,200,448,460⟩⟩]⟩
theorem node566 : UpperPrefix a [2,4,5,7,8,0,3,6] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,0,3,6] 30 cert566 (by decide +kernel)

theorem node567 : UpperPrefix a [2,4,5,7,8,0,3] 30 :=
  branch_upper a [2,4,5,7,8,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,8,0,3,0] 30 (by decide +kernel))
  node565
  (invalid_upper a [2,4,5,7,8,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,3,5] 30 (by decide +kernel))
  node566
  (invalid_upper a [2,4,5,7,8,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,3,8] 30 (by decide +kernel)))

theorem node568 : UpperPrefix a [2,4,5,7,8,0] 30 :=
  branch_upper a [2,4,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,8,0,0] 30 (by decide +kernel))
  node564
  (invalid_upper a [2,4,5,7,8,0,2] 30 (by decide +kernel))
  node567
  (invalid_upper a [2,4,5,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,0,8] 30 (by decide +kernel)))

def cert569 : Leaf := ⟨⟨184,172,144,288,204,153,56,48,248⟩,[],[(8,4,3),(0,6,5)],⟨7,19,44,152,304,98,193,392,324⟩,⟨7,19,44,152,304,98,193,392,260⟩,[⟨1,1378849210743820993429505,⟨477,477,444,156,444,508,457,392,412⟩⟩,⟨6,1210253986314939184198719,⟨15,159,47,159,447,47,129,395,261⟩⟩,⟨2,1210255175370793912632321,⟨107,251,40,152,440,106,225,392,256⟩⟩]⟩
theorem node569 : UpperPrefix a [2,4,5,7,8,1,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,1,0,3] 30 cert569 (by decide +kernel)

def cert570 : Leaf := ⟨⟨112,100,80,356,68,21,52,52,120⟩,[],[(8,4,3),(0,6,5)],⟨7,19,44,152,304,98,193,448,268⟩,⟨7,19,44,152,304,98,193,448,260⟩,[⟨1,1508529821581964781551617,⟨477,477,444,412,444,508,457,448,284⟩⟩,⟨3,1212623581005040944653569,⟨103,243,36,242,499,98,243,499,503⟩⟩,⟨7,1265595378222590187519757,⟨279,19,319,319,307,98,115,371,279⟩⟩]⟩
theorem node570 : UpperPrefix a [2,4,5,7,8,1,0,6] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,1,0,6] 30 cert570 (by decide +kernel)

theorem node571 : UpperPrefix a [2,4,5,7,8,1,0] 30 :=
  branch_upper a [2,4,5,7,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,7,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,0,2] 30 (by decide +kernel))
  node569
  (invalid_upper a [2,4,5,7,8,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,0,5] 30 (by decide +kernel))
  node570
  (invalid_upper a [2,4,5,7,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,0,8] 30 (by decide +kernel)))

def cert572 : Leaf := ⟨⟨120,104,81,353,73,25,0,124,121⟩,[(6,3)],[(2,0,7),(7,3,6),(8,4,3)],⟨7,19,44,152,304,98,200,385,324⟩,⟨7,19,44,152,304,98,200,385,260⟩,[⟨1,1507647404285373631692801,⟨477,477,380,476,380,508,456,457,276⟩⟩]⟩
theorem node572 : UpperPrefix a [2,4,5,7,8,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,1,3,0] 30 cert572 (by decide +kernel)

def cert573 : Leaf := ⟨⟨112,100,81,357,69,21,0,61,113⟩,[(6,3)],[(7,3,6),(8,4,3)],⟨7,19,44,152,304,98,200,448,261⟩,⟨7,19,44,152,304,98,200,448,260⟩,[⟨1,1227111986543105846280193,⟨461,477,252,220,508,508,200,448,460⟩⟩,⟨3,1233719404462669250637573,⟨279,275,311,178,307,98,242,499,279⟩⟩]⟩
theorem node573 : UpperPrefix a [2,4,5,7,8,1,3,6] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,1,3,6] 30 cert573 (by decide +kernel)

theorem node574 : UpperPrefix a [2,4,5,7,8,1,3] 30 :=
  branch_upper a [2,4,5,7,8,1,3] 30 (by decide) (fin9_cases _
  node572
  (invalid_upper a [2,4,5,7,8,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,3,5] 30 (by decide +kernel))
  node573
  (invalid_upper a [2,4,5,7,8,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,3,8] 30 (by decide +kernel)))

theorem node575 : UpperPrefix a [2,4,5,7,8,1] 30 :=
  branch_upper a [2,4,5,7,8,1] 30 (by decide) (fin9_cases _
  node571
  (invalid_upper a [2,4,5,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,2] 30 (by decide +kernel))
  node574
  (invalid_upper a [2,4,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,1,8] 30 (by decide +kernel)))

#print axioms node575
end Delivery.FiniteExclusion.Sharp2x7
