import RegularNineSharp3x6Base
import RegularNineSharp3x6C007
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
theorem node512 : UpperPrefix a [3,4,6,1,8] 30 :=
  branch_upper a [3,4,6,1,8] 30 (by decide) (fin9_cases _
  node509
  (invalid_upper a [3,4,6,1,8,1] 30 (by decide +kernel))
  node510
  (invalid_upper a [3,4,6,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,8,6] 30 (by decide +kernel))
  node511
  (invalid_upper a [3,4,6,1,8,8] 30 (by decide +kernel)))

theorem node513 : UpperPrefix a [3,4,6,1] 30 :=
  branch_upper a [3,4,6,1] 30 (by decide) (fin9_cases _
  node500
  (invalid_upper a [3,4,6,1,1] 30 (by decide +kernel))
  node501
  (invalid_upper a [3,4,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,1,6] 30 (by decide +kernel))
  node508
  node512)

def cert514 : Leaf := ⟨⟨500,0,426,0,458,386,290,98,226⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0),(0,4,1),(0,4,3)],⟨11,22,69,28,49,482,482,418,426⟩,⟨11,22,69,28,49,96,192,384,264⟩,[⟨3,1212473369218503117116417,⟨3,22,69,22,49,96,192,480,482⟩⟩]⟩
theorem node514 : UpperPrefix a [3,4,6,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,2,0] 30 cert514 (by decide +kernel)

def cert515 : Leaf := ⟨⟨436,0,424,0,457,393,297,41,161⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,69,28,50,481,481,417,425⟩,⟨11,22,69,28,50,96,192,384,264⟩,[⟨1,1214876138874820281761793,⟨493,252,485,252,56,96,192,384,264⟩⟩,⟨6,1285811850040851347543323,⟨11,415,5,415,443,32,128,385,267⟩⟩]⟩
theorem node515 : UpperPrefix a [3,4,6,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,2,1] 30 cert515 (by decide +kernel)

def cert516 : Local := ⟨⟨500,0,0,0,331,0,299,107,227⟩,[(1,3),(2,5),(3,1),(5,2)],[(4,1,0),(2,3,0)]⟩
theorem node516 : UpperPrefix a [3,4,6,2,7,0] 30 :=
  local_sound a [3,4,6,2,7,0] 30 cert516 (by decide +kernel)

def cert517 : Leaf := ⟨⟨180,0,170,0,11,137,299,43,163⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,69,28,176,98,481,417,297⟩,⟨11,22,69,28,176,98,192,384,264⟩,[⟨6,1361664861674144047043883,⟨11,159,5,159,433,443,128,385,267⟩⟩,⟨8,1181748066173722885503,⟨11,63,127,63,191,127,255,129,11⟩⟩]⟩
theorem node517 : UpperPrefix a [3,4,6,2,7,1] 30 :=
  Boolean.leaf_sound a [3,4,6,2,7,1] 30 cert517 (by decide +kernel)

def cert518 : Leaf := ⟨⟨116,0,42,0,331,139,43,107,99⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0),(8,5,4)],⟨11,22,69,28,176,352,227,419,299⟩,⟨11,22,69,28,176,352,192,384,264⟩,[⟨7,1284484837389051022554395,⟨11,287,69,287,319,357,64,257,267⟩⟩]⟩
theorem node518 : UpperPrefix a [3,4,6,2,7,8] 30 :=
  Boolean.leaf_sound a [3,4,6,2,7,8] 30 cert518 (by decide +kernel)

theorem node519 : UpperPrefix a [3,4,6,2,7] 30 :=
  branch_upper a [3,4,6,2,7] 30 (by decide) (fin9_cases _
  node516
  node517
  (invalid_upper a [3,4,6,2,7,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,7,7] 30 (by decide +kernel))
  node518)

def cert520 : Local := ⟨⟨500,0,0,0,203,0,299,107,227⟩,[(1,3),(2,5),(3,1),(5,2)],[(4,1,0),(2,3,0)]⟩
theorem node520 : UpperPrefix a [3,4,6,2,8,0] 30 :=
  local_sound a [3,4,6,2,8,0] 30 cert520 (by decide +kernel)

def cert521 : Leaf := ⟨⟨404,0,394,0,139,393,299,43,163⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,69,28,304,98,225,417,425⟩,⟨11,22,69,28,304,98,192,384,264⟩,[⟨6,1361664861674144047043883,⟨11,159,5,159,433,443,128,385,267⟩⟩,⟨5,1210107564157954203596091,⟨11,31,69,31,287,79,192,385,267⟩⟩]⟩
theorem node521 : UpperPrefix a [3,4,6,2,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,2,8,1] 30 cert521 (by decide +kernel)

def cert522 : Local := ⟨⟨372,0,298,0,75,0,299,107,99⟩,[(1,3),(3,1),(5,6)],[(4,1,0),(2,3,0),(7,5,5)]⟩
theorem node522 : UpperPrefix a [3,4,6,2,8,7] 30 :=
  local_sound a [3,4,6,2,8,7] 30 cert522 (by decide +kernel)

theorem node523 : UpperPrefix a [3,4,6,2,8] 30 :=
  branch_upper a [3,4,6,2,8] 30 (by decide) (fin9_cases _
  node520
  node521
  (invalid_upper a [3,4,6,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,8,6] 30 (by decide +kernel))
  node522
  (invalid_upper a [3,4,6,2,8,8] 30 (by decide +kernel)))

theorem node524 : UpperPrefix a [3,4,6,2] 30 :=
  branch_upper a [3,4,6,2] 30 (by decide) (fin9_cases _
  node514
  node515
  (invalid_upper a [3,4,6,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,2,6] 30 (by decide +kernel))
  node519
  node523)

def cert525 : Leaf := ⟨⟨84,73,10,0,78,398,270,78,198⟩,[(3,4)],[(4,1,0),(5,3,3),(0,4,1)],⟨11,22,69,56,49,486,454,390,398⟩,⟨11,22,69,56,49,96,192,384,264⟩,[⟨7,1208926973665889504752955,⟨27,31,69,63,63,127,64,257,283⟩⟩,⟨8,1181745671977741350203,⟨27,31,69,63,63,127,192,129,27⟩⟩]⟩
theorem node525 : UpperPrefix a [3,4,6,5,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,0] 30 cert525 (by decide +kernel)

def cert526 : Leaf := ⟨⟨84,73,8,0,77,397,269,77,197⟩,[(3,4)],[(4,1,0),(5,3,3)],⟨11,22,69,56,50,485,453,389,397⟩,⟨11,22,69,56,50,96,192,384,264⟩,[⟨1,1214876138874822429245441,⟨493,252,485,56,56,96,192,384,264⟩⟩,⟨7,1208926973665889504752955,⟨27,31,69,63,63,127,64,257,283⟩⟩,⟨8,1181745671977741350203,⟨27,31,69,63,63,127,192,129,27⟩⟩]⟩
theorem node526 : UpperPrefix a [3,4,6,5,1] 30 :=
  Boolean.leaf_sound a [3,4,6,5,1] 30 cert526 (by decide +kernel)

def cert527 : Local := ⟨⟨400,0,394,0,459,395,267,11,131⟩,[(1,4),(3,4)],[(4,1,0),(6,2,4),(5,3,3),(2,4,1)]⟩
theorem node527 : UpperPrefix a [3,4,6,5,2] 30 :=
  local_sound a [3,4,6,5,2] 30 cert527 (by decide +kernel)

def cert528 : Leaf := ⟨⟨468,457,0,0,335,0,270,78,198⟩,[(2,5),(3,4),(5,2)],[(4,1,0),(5,3,3)],⟨11,22,69,56,176,97,454,390,270⟩,⟨11,22,69,56,176,97,192,384,264⟩,[⟨0,1219570781022463852545024,⟨458,478,68,56,184,96,192,384,264⟩⟩]⟩
theorem node528 : UpperPrefix a [3,4,6,5,7,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,0] 30 cert528 (by decide +kernel)

def cert529 : Leaf := ⟨⟨148,201,136,0,15,141,269,13,133⟩,[(3,4)],[(4,1,0),(5,3,3)],⟨11,22,69,56,176,98,453,389,269⟩,⟨11,22,69,56,176,98,192,384,264⟩,[⟨8,1181748066173722885503,⟨11,63,127,63,191,127,255,129,11⟩⟩,⟨1,1214876138698900300365825,⟨461,220,453,56,184,96,192,384,264⟩⟩,⟨6,1219569592074365544956963,⟨395,415,5,57,185,443,128,384,264⟩⟩]⟩
theorem node529 : UpperPrefix a [3,4,6,5,7,1] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,1] 30 cert529 (by decide +kernel)

def cert530 : Local := ⟨⟨404,393,394,0,271,0,271,15,135⟩,[(3,4),(5,2)],[(4,1,0),(6,2,5),(5,3,3)]⟩
theorem node530 : UpperPrefix a [3,4,6,5,7,2] 30 :=
  local_sound a [3,4,6,5,7,2] 30 cert530 (by decide +kernel)

def cert531 : Leaf := ⟨⟨20,73,10,0,335,143,15,15,7⟩,[(3,4)],[(4,1,0),(5,3,3),(8,5,4)],⟨11,22,69,56,176,352,199,391,271⟩,⟨11,22,69,56,176,352,192,384,264⟩,[⟨7,1331708502217747206255899,⟨267,287,69,319,319,357,64,257,267⟩⟩,⟨6,1219569592072162226734083,⟨395,415,5,56,184,288,128,384,264⟩⟩]⟩
theorem node531 : UpperPrefix a [3,4,6,5,7,8] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,8] 30 cert531 (by decide +kernel)

theorem node532 : UpperPrefix a [3,4,6,5,7] 30 :=
  branch_upper a [3,4,6,5,7] 30 (by decide) (fin9_cases _
  node528
  node529
  node530
  (invalid_upper a [3,4,6,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,7] 30 (by decide +kernel))
  node531)

def cert533 : Leaf := ⟨⟨468,457,0,0,207,0,270,78,198⟩,[(2,5),(3,4),(5,2)],[(4,1,0),(5,3,3)],⟨11,22,69,56,304,97,198,390,398⟩,⟨11,22,69,56,304,97,192,384,264⟩,[⟨0,1219570781022463852545024,⟨458,478,68,56,312,96,192,384,264⟩⟩]⟩
theorem node533 : UpperPrefix a [3,4,6,5,8,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,0] 30 cert533 (by decide +kernel)

def cert534 : Leaf := ⟨⟨148,201,136,0,143,397,13,13,133⟩,[(3,4)],[(4,1,0),(5,3,3)],⟨11,22,69,56,304,98,197,389,397⟩,⟨11,22,69,56,304,98,192,384,264⟩,[⟨1,1214876138698900300365825,⟨461,220,453,56,312,96,192,384,264⟩⟩,⟨6,1219569592074365544956963,⟨395,415,5,57,313,443,128,384,264⟩⟩,⟨8,1184051512233914545435,⟨11,31,69,63,63,103,196,197,11⟩⟩]⟩
theorem node534 : UpperPrefix a [3,4,6,5,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,1] 30 cert534 (by decide +kernel)

def cert535 : Local := ⟨⟨404,393,394,0,143,0,271,15,135⟩,[(3,4),(5,2)],[(4,1,0),(6,2,5),(5,3,3)]⟩
theorem node535 : UpperPrefix a [3,4,6,5,8,2] 30 :=
  local_sound a [3,4,6,5,8,2] 30 cert535 (by decide +kernel)

def cert536 : Local := ⟨⟨340,329,266,0,79,0,271,79,71⟩,[(3,4),(5,6)],[(4,1,0),(5,3,3),(7,5,5)]⟩
theorem node536 : UpperPrefix a [3,4,6,5,8,7] 30 :=
  local_sound a [3,4,6,5,8,7] 30 cert536 (by decide +kernel)

theorem node537 : UpperPrefix a [3,4,6,5,8] 30 :=
  branch_upper a [3,4,6,5,8] 30 (by decide) (fin9_cases _
  node533
  node534
  node535
  (invalid_upper a [3,4,6,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,6] 30 (by decide +kernel))
  node536
  (invalid_upper a [3,4,6,5,8,8] 30 (by decide +kernel)))

theorem node538 : UpperPrefix a [3,4,6,5] 30 :=
  branch_upper a [3,4,6,5] 30 (by decide) (fin9_cases _
  node525
  node526
  node527
  (invalid_upper a [3,4,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,6] 30 (by decide +kernel))
  node532
  node537)

def cert539 : Leaf := ⟨⟨244,97,168,100,70,4,300,108,228⟩,[],[(4,1,0),(0,4,1),(1,5,4)],⟨11,22,69,152,49,98,484,420,300⟩,⟨11,22,69,152,49,98,192,384,264⟩,[⟨8,1181748068777815239789,⟨27,55,127,155,55,127,255,128,9⟩⟩,⟨3,1210107565424862978640897,⟨3,54,119,144,49,98,192,384,256⟩⟩,⟨7,1208926973804146641079297,⟨11,54,119,24,49,98,64,256,264⟩⟩]⟩
theorem node539 : UpperPrefix a [3,4,6,7,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,1] 30 cert539 (by decide +kernel)

def cert540 : Leaf := ⟨⟨180,161,170,38,134,0,302,46,166⟩,[(5,2)],[(4,1,0),(6,2,5),(0,4,1)],⟨11,22,69,152,49,100,482,418,298⟩,⟨11,22,69,152,49,100,192,384,264⟩,[⟨8,1181748068777815239789,⟨27,55,127,155,55,127,255,128,9⟩⟩,⟨3,1210107565424862978657281,⟨3,54,119,144,51,118,192,384,256⟩⟩]⟩
theorem node540 : UpperPrefix a [3,4,6,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,2] 30 cert540 (by decide +kernel)

def cert541 : Leaf := ⟨⟨212,193,130,356,204,132,4,108,228⟩,[],[(4,1,0),(0,4,1),(1,6,2)],⟨11,22,69,152,49,352,194,420,300⟩,⟨11,22,69,152,49,352,194,384,264⟩,[⟨8,1181889786609688409353,⟨79,22,69,223,55,119,194,133,79⟩⟩,⟨3,1210107718406237943243777,⟨71,22,69,210,55,352,194,416,352⟩⟩,⟨5,1210107708273139933000969,⟨79,22,69,223,23,325,194,389,335⟩⟩]⟩
theorem node541 : UpperPrefix a [3,4,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,1] 30 cert541 (by decide +kernel)

def cert542 : Leaf := ⟨⟨208,201,138,354,202,138,10,72,226⟩,[],[(4,1,0),(0,4,1)],⟨11,22,69,152,49,352,196,386,296⟩,⟨11,22,69,152,49,352,196,386,264⟩,[⟨2,1767374482775956906837123,⟨411,443,505,409,441,376,505,411,264⟩⟩,⟨5,1212476385504354737861897,⟨79,22,69,223,87,453,196,455,463⟩⟩,⟨8,1184195629618935657737,⟨79,22,69,223,55,119,196,199,79⟩⟩]⟩
theorem node542 : UpperPrefix a [3,4,6,7,0,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,2,1] 30 cert542 (by decide +kernel)

def cert543 : Local := ⟨⟨212,201,138,102,206,142,10,0,198⟩,[(7,5)],[(4,1,0),(0,4,1),(8,5,7),(5,7,3)]⟩
theorem node543 : UpperPrefix a [3,4,6,7,0,8,2,5] 30 :=
  local_sound a [3,4,6,7,0,8,2,5] 30 cert543 (by decide +kernel)

theorem node544 : UpperPrefix a [3,4,6,7,0,8,2] 30 :=
  branch_upper a [3,4,6,7,0,8,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,8,2,0] 30 (by decide +kernel))
  node542
  (invalid_upper a [3,4,6,7,0,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,2,4] 30 (by decide +kernel))
  node543
  (invalid_upper a [3,4,6,7,0,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,2,8] 30 (by decide +kernel)))

def cert545 : Leaf := ⟨⟨148,225,162,6,206,134,262,14,134⟩,[],[(4,1,0),(0,4,1),(8,5,6)],⟨11,22,69,152,49,352,224,390,270⟩,⟨11,22,69,152,49,352,224,384,264⟩,[⟨3,1210110028752846784308225,⟨71,22,69,242,55,352,224,480,352⟩⟩,⟨5,1219570743867765047690243,⟨395,415,69,152,17,320,192,384,264⟩⟩,⟨6,1219569592072160347685891,⟨395,415,5,152,49,288,160,384,264⟩⟩]⟩
theorem node545 : UpperPrefix a [3,4,6,7,0,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,5] 30 cert545 (by decide +kernel)

theorem node546 : UpperPrefix a [3,4,6,7,0,8] 30 :=
  branch_upper a [3,4,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,8,0] 30 (by decide +kernel))
  node541
  node544
  (invalid_upper a [3,4,6,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,4] 30 (by decide +kernel))
  node545
  (invalid_upper a [3,4,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,8] 30 (by decide +kernel)))

theorem node547 : UpperPrefix a [3,4,6,7,0] 30 :=
  branch_upper a [3,4,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,0] 30 (by decide +kernel))
  node539
  node540
  (invalid_upper a [3,4,6,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,7] 30 (by decide +kernel))
  node546)

def cert548 : Leaf := ⟨⟨116,97,0,101,69,0,301,109,229⟩,[(2,5),(5,2)],[(4,1,0)],⟨11,22,69,152,50,97,484,420,300⟩,⟨11,22,69,152,50,97,192,384,264⟩,[⟨1,1300340804888244264370177,⟨493,508,485,472,508,485,192,384,264⟩⟩,⟨8,1181748068777815239789,⟨27,55,127,155,55,127,255,128,9⟩⟩,⟨7,1208926973806483111701513,⟨27,54,119,27,54,119,64,256,265⟩⟩,⟨3,1210107565427199449263105,⟨19,54,119,146,54,119,192,384,256⟩⟩]⟩
theorem node548 : UpperPrefix a [3,4,6,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,0] 30 cert548 (by decide +kernel)

def cert549 : Leaf := ⟨⟨176,169,168,33,141,0,297,41,161⟩,[(5,2)],[(4,1,0),(6,2,5),(2,5,4)],⟨11,22,69,152,50,100,481,417,297⟩,⟨11,22,69,152,50,100,192,384,264⟩,[⟨1,1214876138945189025939457,⟨493,252,485,152,56,228,192,384,264⟩⟩,⟨8,1181748068777815239789,⟨27,55,127,155,55,127,255,128,9⟩⟩]⟩
theorem node549 : UpperPrefix a [3,4,6,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,2] 30 cert549 (by decide +kernel)

def cert550 : Leaf := ⟨⟨244,224,0,356,196,140,44,100,228⟩,[(2,6)],[(4,1,0),(0,6,2)],⟨11,22,69,152,50,352,193,420,300⟩,⟨11,22,69,152,50,352,193,384,264⟩,[⟨1,1225224764622342062342145,⟨493,508,485,152,440,484,485,384,264⟩⟩,⟨8,1184195629618952434953,⟨79,22,69,223,54,119,197,197,79⟩⟩,⟨3,1210402713191229005251585,⟨3,22,69,144,178,502,197,384,256⟩⟩]⟩
theorem node550 : UpperPrefix a [3,4,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,0] 30 cert550 (by decide +kernel)

def cert551 : Leaf := ⟨⟨208,201,136,353,201,137,9,105,225⟩,[],[(4,1,0)],⟨11,22,69,152,50,352,196,417,297⟩,⟨11,22,69,152,50,352,196,384,264⟩,[⟨1,1214876174903617300725761,⟨493,252,485,152,120,352,228,384,264⟩⟩,⟨2,1314202544484471975969811,⟨411,443,489,409,443,352,480,384,264⟩⟩,⟨8,1184195629618935657737,⟨79,22,69,223,54,119,196,197,79⟩⟩,⟨5,1210110014116149180249353,⟨79,22,69,223,22,325,196,453,335⟩⟩]⟩
theorem node551 : UpperPrefix a [3,4,6,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,2] 30 cert551 (by decide +kernel)

def cert552 : Leaf := ⟨⟨148,233,160,5,205,133,261,13,133⟩,[],[(4,1,0),(8,5,6)],⟨11,22,69,152,50,352,224,389,269⟩,⟨11,22,69,152,50,352,224,384,264⟩,[⟨1,1214878638372613472387073,⟨493,252,485,248,120,352,224,480,360⟩⟩,⟨5,1219570743867767195173907,⟨395,415,69,153,411,320,192,384,264⟩⟩,⟨6,1219569592072162495169555,⟨395,415,5,153,443,288,160,384,264⟩⟩,⟨3,1210110028752846784300033,⟨71,22,69,240,50,352,224,480,352⟩⟩]⟩
theorem node552 : UpperPrefix a [3,4,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,5] 30 cert552 (by decide +kernel)

theorem node553 : UpperPrefix a [3,4,6,7,1,8] 30 :=
  branch_upper a [3,4,6,7,1,8] 30 (by decide) (fin9_cases _
  node550
  (invalid_upper a [3,4,6,7,1,8,1] 30 (by decide +kernel))
  node551
  (invalid_upper a [3,4,6,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,4] 30 (by decide +kernel))
  node552
  (invalid_upper a [3,4,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,8] 30 (by decide +kernel)))

theorem node554 : UpperPrefix a [3,4,6,7,1] 30 :=
  branch_upper a [3,4,6,7,1] 30 (by decide) (fin9_cases _
  node548
  (invalid_upper a [3,4,6,7,1,1] 30 (by decide +kernel))
  node549
  (invalid_upper a [3,4,6,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,7] 30 (by decide +kernel))
  node553)

def cert555 : Local := ⟨⟨432,0,0,290,459,0,298,42,162⟩,[(1,4),(2,5),(5,2)],[(4,1,0),(6,2,4),(2,4,1),(0,5,4)]⟩
theorem node555 : UpperPrefix a [3,4,6,7,2,0] 30 :=
  local_sound a [3,4,6,7,2,0] 30 cert555 (by decide +kernel)

def cert556 : Leaf := ⟨⟨48,0,170,35,75,9,299,43,163⟩,[(1,4)],[(4,1,0),(6,2,4),(2,4,1)],⟨11,22,69,152,52,98,481,417,297⟩,⟨11,22,69,152,52,98,192,384,264⟩,[⟨8,1181748068777815239789,⟨27,55,127,155,55,127,255,128,9⟩⟩,⟨7,1208926973804284080040969,⟨27,54,119,27,54,114,64,256,265⟩⟩]⟩
theorem node556 : UpperPrefix a [3,4,6,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,1] 30 cert556 (by decide +kernel)

def cert557 : Local := ⟨⟨432,0,0,290,458,138,298,42,162⟩,[(1,4),(2,6)],[(4,1,0),(6,2,4),(2,4,1),(0,6,2)]⟩
theorem node557 : UpperPrefix a [3,4,6,7,2,8,0] 30 :=
  local_sound a [3,4,6,7,2,8,0] 30 cert557 (by decide +kernel)

def cert558 : Local := ⟨⟨432,0,426,289,457,137,297,41,161⟩,[(1,4)],[(4,1,0),(6,2,4),(2,4,1),(1,6,2)]⟩
theorem node558 : UpperPrefix a [3,4,6,7,2,8,1] 30 :=
  local_sound a [3,4,6,7,2,8,1] 30 cert558 (by decide +kernel)

def cert559 : Leaf := ⟨⟨144,0,170,3,203,139,267,11,131⟩,[(1,4)],[(4,1,0),(6,2,4),(2,4,1),(8,5,6)],⟨11,22,69,152,52,352,224,387,267⟩,⟨11,22,69,152,52,352,224,384,264⟩,[⟨5,1337860490240429694919707,⟨395,415,453,411,415,320,192,384,393⟩⟩]⟩
theorem node559 : UpperPrefix a [3,4,6,7,2,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,8,5] 30 cert559 (by decide +kernel)

theorem node560 : UpperPrefix a [3,4,6,7,2,8] 30 :=
  branch_upper a [3,4,6,7,2,8] 30 (by decide) (fin9_cases _
  node557
  node558
  (invalid_upper a [3,4,6,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,4] 30 (by decide +kernel))
  node559
  (invalid_upper a [3,4,6,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,8] 30 (by decide +kernel)))

theorem node561 : UpperPrefix a [3,4,6,7,2] 30 :=
  branch_upper a [3,4,6,7,2] 30 (by decide) (fin9_cases _
  node555
  node556
  (invalid_upper a [3,4,6,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,7] 30 (by decide +kernel))
  node560)

def cert562 : Leaf := ⟨⟨212,193,0,357,205,0,5,101,229⟩,[(2,5),(5,2)],[(4,1,0),(8,4,3),(1,6,2),(1,6,5)],⟨11,22,69,152,304,97,194,420,300⟩,⟨11,22,69,152,304,97,194,384,264⟩,[⟨3,1210255607786723404424193,⟨103,246,101,210,502,101,194,384,320⟩⟩,⟨5,1210107708273139933000969,⟨79,22,69,223,279,69,194,389,335⟩⟩]⟩
theorem node562 : UpperPrefix a [3,4,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,1] 30 cert562 (by decide +kernel)

def cert563 : Leaf := ⟨⟨240,225,0,355,203,0,35,99,227⟩,[(2,5),(5,2)],[(4,1,0),(8,4,3)],⟨11,22,69,152,304,97,196,418,298⟩,⟨11,22,69,152,304,97,196,384,264⟩,[⟨2,1219570745134540015010819,⟨411,443,105,152,304,105,224,384,264⟩⟩,⟨3,1210255463671535328568321,⟨103,246,101,210,502,101,228,384,256⟩⟩]⟩
theorem node563 : UpperPrefix a [3,4,6,7,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,2] 30 cert563 (by decide +kernel)

def cert564 : Leaf := ⟨⟨148,201,0,263,207,0,15,15,135⟩,[(2,5),(5,2)],[(4,1,0),(8,4,3)],⟨11,22,69,152,304,97,224,390,270⟩,⟨11,22,69,152,304,97,224,384,264⟩,[⟨5,1295276181546271203402779,⟨395,415,69,411,415,69,196,384,265⟩⟩,⟨6,1219569592072160347685891,⟨395,415,5,152,304,33,160,384,264⟩⟩]⟩
theorem node564 : UpperPrefix a [3,4,6,7,8,0,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,5] 30 cert564 (by decide +kernel)

theorem node565 : UpperPrefix a [3,4,6,7,8,0] 30 :=
  branch_upper a [3,4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,8,0,0] 30 (by decide +kernel))
  node562
  node563
  (invalid_upper a [3,4,6,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,4] 30 (by decide +kernel))
  node564
  (invalid_upper a [3,4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,8] 30 (by decide +kernel)))

def cert566 : Leaf := ⟨⟨212,200,0,356,204,140,14,108,228⟩,[(2,6)],[(4,1,0),(8,4,3),(0,6,2)],⟨11,22,69,152,304,98,193,420,300⟩,⟨11,22,69,152,304,98,193,384,264⟩,[⟨1,1361518440643065168265217,⟨9,28,69,152,440,508,197,384,264⟩⟩,⟨5,1210110014116149188637961,⟨79,22,69,223,279,70,197,453,335⟩⟩]⟩
theorem node566 : UpperPrefix a [3,4,6,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,0] 30 cert566 (by decide +kernel)

def cert567 : Local := ⟨⟨240,224,162,354,194,132,35,106,226⟩,[],[(3,0,7),(4,1,0),(8,4,3),(2,6,5),(0,7,6)]⟩
theorem node567 : UpperPrefix a [3,4,6,7,8,1,2,0] 30 :=
  local_sound a [3,4,6,7,8,1,2,0] 30 cert567 (by decide +kernel)

def cert568 : Local := ⟨⟨208,201,138,355,0,141,11,0,195⟩,[(4,7),(7,4)],[(4,1,0),(8,4,3),(2,6,5),(5,7,3)]⟩
theorem node568 : UpperPrefix a [3,4,6,7,8,1,2,5] 30 :=
  local_sound a [3,4,6,7,8,1,2,5] 30 cert568 (by decide +kernel)

theorem node569 : UpperPrefix a [3,4,6,7,8,1,2] 30 :=
  branch_upper a [3,4,6,7,8,1,2] 30 (by decide) (fin9_cases _
  node567
  (invalid_upper a [3,4,6,7,8,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,2,4] 30 (by decide +kernel))
  node568
  (invalid_upper a [3,4,6,7,8,1,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,2,8] 30 (by decide +kernel)))

def cert570 : Leaf := ⟨⟨208,193,130,323,195,129,3,74,199⟩,[],[(3,0,7),(4,1,0),(8,4,3)],⟨11,22,69,152,304,98,224,385,268⟩,⟨11,22,69,152,304,98,224,385,264⟩,[⟨2,1210257769453001140864035,⟨107,251,105,216,505,107,249,505,264⟩⟩,⟨5,1449721546303404441084987,⟨395,415,197,411,415,463,453,385,393⟩⟩]⟩
theorem node570 : UpperPrefix a [3,4,6,7,8,1,5,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,5,0] 30 cert570 (by decide +kernel)

def cert571 : Leaf := ⟨⟨148,136,138,262,142,140,14,11,135⟩,[],[(4,1,0),(8,4,3)],⟨11,22,69,152,304,98,224,388,265⟩,⟨11,22,69,152,304,98,224,388,264⟩,[⟨5,1489815544547612151522363,⟨395,415,453,411,415,463,453,388,265⟩⟩,⟨6,2414365205732938497395879,⟨395,415,415,409,313,443,441,399,264⟩⟩,⟨0,1210110022340521814459392,⟨106,22,108,250,304,106,250,510,376⟩⟩]⟩
theorem node571 : UpperPrefix a [3,4,6,7,8,1,5,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,5,2] 30 cert571 (by decide +kernel)

theorem node572 : UpperPrefix a [3,4,6,7,8,1,5] 30 :=
  branch_upper a [3,4,6,7,8,1,5] 30 (by decide) (fin9_cases _
  node570
  (invalid_upper a [3,4,6,7,8,1,5,1] 30 (by decide +kernel))
  node571
  (invalid_upper a [3,4,6,7,8,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,5,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,5,8] 30 (by decide +kernel)))

theorem node573 : UpperPrefix a [3,4,6,7,8,1] 30 :=
  branch_upper a [3,4,6,7,8,1] 30 (by decide) (fin9_cases _
  node566
  (invalid_upper a [3,4,6,7,8,1,1] 30 (by decide +kernel))
  node569
  (invalid_upper a [3,4,6,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,4] 30 (by decide +kernel))
  node572
  (invalid_upper a [3,4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,8] 30 (by decide +kernel)))

def cert574 : Local := ⟨⟨180,168,0,294,142,0,46,46,166⟩,[(2,6),(5,2)],[(4,1,0),(6,2,5),(8,4,3),(0,6,2),(0,6,5)]⟩
theorem node574 : UpperPrefix a [3,4,6,7,8,2,0] 30 :=
  local_sound a [3,4,6,7,8,2,0] 30 cert574 (by decide +kernel)

def cert575 : Leaf := ⟨⟨148,137,138,293,141,0,13,45,165⟩,[(5,2)],[(4,1,0),(6,2,5),(8,4,3),(1,6,2)],⟨11,22,69,152,304,100,194,417,297⟩,⟨11,22,69,152,304,100,194,384,264⟩,[⟨5,1210107708273139924612361,⟨79,22,69,223,279,68,194,389,335⟩⟩]⟩
theorem node575 : UpperPrefix a [3,4,6,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,1] 30 cert575 (by decide +kernel)

#print axioms node575
end Delivery.FiniteExclusion.Sharp3x6
