import RegularNineSharp2x3x4Base
import RegularNineSharp2x3x4C007
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
theorem node512 : UpperPrefix a [2,5,7,6,0,8] 30 :=
  branch_upper a [2,5,7,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,6,0,8,0] 30 (by decide +kernel))
  node509
  (invalid_upper a [2,5,7,6,0,8,2] 30 (by decide +kernel))
  node510
  node511
  (invalid_upper a [2,5,7,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,8,8] 30 (by decide +kernel)))

theorem node513 : UpperPrefix a [2,5,7,6,0] 30 :=
  branch_upper a [2,5,7,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,6,0,0] 30 (by decide +kernel))
  node506
  (invalid_upper a [2,5,7,6,0,2] 30 (by decide +kernel))
  node507
  node508
  (invalid_upper a [2,5,7,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,0,7] 30 (by decide +kernel))
  node512)

def cert514 : Leaf := ⟨⟨0,0,114,38,0,30,318,126,94⟩,[(0,4),(1,5),(4,0)],[(0,5,1)],⟨7,35,140,88,22,97,472,408,312⟩,⟨7,35,140,88,22,97,192,384,288⟩,[⟨7,1426155832156960823729173,⟨279,315,319,379,279,379,64,256,298⟩⟩,⟨8,1181748210000626637949,⟨23,59,191,127,23,127,255,130,59⟩⟩]⟩
theorem node514 : UpperPrefix a [2,5,7,6,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,0] 30 cert514 (by decide +kernel)

def cert515 : Leaf := ⟨⟨0,156,51,167,0,0,311,55,151⟩,[(0,4),(4,0),(5,3)],[(6,3,5)],⟨7,35,140,88,22,104,465,401,305⟩,⟨7,35,140,88,22,104,192,384,288⟩,[⟨3,1219727884591930543178769,⟨471,499,132,209,471,96,192,384,288⟩⟩,⟨8,1181748210000626637949,⟨23,59,191,127,23,127,255,130,59⟩⟩]⟩
theorem node515 : UpperPrefix a [2,5,7,6,1,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,3] 30 cert515 (by decide +kernel)

def cert516 : Leaf := ⟨⟨0,476,369,0,0,0,317,125,221⟩,[(0,4),(3,5),(4,0),(5,3)],[],⟨7,35,140,88,22,112,457,393,297⟩,⟨7,35,140,88,22,112,192,384,288⟩,[⟨1,1219570781866893082361857,⟨453,493,172,124,508,124,192,384,296⟩⟩]⟩
theorem node516 : UpperPrefix a [2,5,7,6,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,4] 30 cert516 (by decide +kernel)

def cert517 : Leaf := ⟨⟨0,92,112,38,0,28,62,124,92⟩,[(0,4),(4,0)],[],⟨7,35,140,88,22,352,193,408,312⟩,⟨7,35,140,88,22,352,193,384,288⟩,[⟨0,1550782037370609251386368,⟨22,54,428,508,22,492,508,384,292⟩⟩,⟨1,1247960284404578664841217,⟨5,33,428,508,20,352,193,384,288⟩⟩,⟨7,1567826828894854288808981,⟨279,51,319,379,279,362,379,256,288⟩⟩,⟨8,1184123580922532611249,⟨95,59,221,93,95,127,221,223,59⟩⟩]⟩
theorem node517 : UpperPrefix a [2,5,7,6,1,8,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,8,0] 30 cert517 (by decide +kernel)

def cert518 : Leaf := ⟨⟨0,468,0,423,0,151,0,119,215⟩,[(0,4),(2,6),(4,0),(6,2)],[],⟨7,35,140,88,22,352,200,401,305⟩,⟨7,35,140,88,22,352,200,384,288⟩,[⟨3,1276506623110786531204117,⟨407,435,439,499,407,352,482,384,288⟩⟩]⟩
theorem node518 : UpperPrefix a [2,5,7,6,1,8,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,8,3] 30 cert518 (by decide +kernel)

def cert519 : Leaf := ⟨⟨0,332,355,0,0,15,303,111,79⟩,[(0,4),(3,6),(4,0)],[(4,6,3)],⟨7,35,140,88,22,352,208,393,297⟩,⟨7,35,140,88,22,352,208,384,288⟩,[⟨7,1567826828894854288808981,⟨279,51,319,379,279,362,379,256,288⟩⟩]⟩
theorem node519 : UpperPrefix a [2,5,7,6,1,8,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,1,8,4] 30 cert519 (by decide +kernel)

theorem node520 : UpperPrefix a [2,5,7,6,1,8] 30 :=
  branch_upper a [2,5,7,6,1,8] 30 (by decide) (fin9_cases _
  node517
  (invalid_upper a [2,5,7,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,2] 30 (by decide +kernel))
  node518
  node519
  (invalid_upper a [2,5,7,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,8,8] 30 (by decide +kernel)))

theorem node521 : UpperPrefix a [2,5,7,6,1] 30 :=
  branch_upper a [2,5,7,6,1] 30 (by decide) (fin9_cases _
  node514
  (invalid_upper a [2,5,7,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,2] 30 (by decide +kernel))
  node515
  node516
  (invalid_upper a [2,5,7,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,1,7] 30 (by decide +kernel))
  node520)

def cert522 : Leaf := ⟨⟨112,0,114,166,0,22,310,118,86⟩,[(1,5),(4,2)],[(3,4,4),(0,5,1)],⟨7,35,140,88,28,97,466,402,306⟩,⟨7,35,140,88,28,97,192,384,288⟩,[⟨8,1181748209931907169405,⟨23,59,191,127,63,127,255,130,59⟩⟩,⟨7,1341153235465234195446805,⟨279,35,319,379,319,99,64,256,290⟩⟩]⟩
theorem node522 : UpperPrefix a [2,5,7,6,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,0] 30 cert522 (by decide +kernel)

def cert523 : Leaf := ⟨⟨208,212,81,133,0,149,277,85,213⟩,[(4,2)],[(3,4,4),(1,5,1)],⟨7,35,140,88,28,98,465,401,305⟩,⟨7,35,140,88,28,98,192,384,288⟩,[⟨5,1212473359119279553774625,⟨23,27,156,92,28,95,220,476,477⟩⟩,⟨8,1181748209931907169405,⟨23,59,191,127,63,127,255,130,59⟩⟩]⟩
theorem node523 : UpperPrefix a [2,5,7,6,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,1] 30 cert523 (by decide +kernel)

def cert524 : Leaf := ⟨⟨496,468,371,0,0,0,291,99,195⟩,[(3,5),(4,2),(5,3)],[(3,4,4)],⟨7,35,140,88,28,112,451,387,291⟩,⟨7,35,140,88,28,112,192,384,288⟩,[⟨2,1219580022690376339948545,⟨451,491,168,120,56,120,192,384,296⟩⟩,⟨4,1219580022407797557691393,⟨455,483,140,72,12,96,192,384,288⟩⟩]⟩
theorem node524 : UpperPrefix a [2,5,7,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,4] 30 cert524 (by decide +kernel)

def cert525 : Leaf := ⟨⟨112,84,80,132,0,23,55,119,87⟩,[(4,2)],[(3,4,4)],⟨7,35,140,88,28,352,211,403,307⟩,⟨7,35,140,88,28,352,192,384,288⟩,[⟨8,1184051528548893213857,⟨31,59,221,92,28,127,221,223,59⟩⟩,⟨7,1341153235465234195430421,⟨279,35,319,379,319,352,64,256,288⟩⟩,⟨0,1210107565291286291284992,⟨22,58,156,92,28,380,220,384,312⟩⟩,⟨1,1210107565291286291283969,⟨21,57,156,92,28,380,220,384,312⟩⟩,⟨5,1210107564165386384442369,⟨23,27,156,92,28,348,220,384,280⟩⟩]⟩
theorem node525 : UpperPrefix a [2,5,7,6,3,8] 30 :=
  Boolean.leaf_sound a [2,5,7,6,3,8] 30 cert525 (by decide +kernel)

theorem node526 : UpperPrefix a [2,5,7,6,3] 30 :=
  branch_upper a [2,5,7,6,3] 30 (by decide) (fin9_cases _
  node522
  node523
  (invalid_upper a [2,5,7,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,3] 30 (by decide +kernel))
  node524
  (invalid_upper a [2,5,7,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,3,7] 30 (by decide +kernel))
  node525)

def cert527 : Leaf := ⟨⟨120,0,368,36,104,30,60,124,92⟩,[(1,5)],[(0,5,1),(1,6,5)],⟨7,35,140,88,276,97,194,408,312⟩,⟨7,35,140,88,276,97,194,384,288⟩,[⟨7,1426155832156960823729173,⟨279,315,319,379,279,379,322,256,298⟩⟩,⟨8,1181818747165487431189,⟨103,35,239,123,127,99,194,128,34⟩⟩]⟩
theorem node527 : UpperPrefix a [2,5,7,6,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,0,1] 30 cert527 (by decide +kernel)

def cert528 : Leaf := ⟨⟨496,0,0,422,226,406,0,118,214⟩,[(1,5),(2,6),(6,2)],[(0,5,1)],⟨7,35,140,88,276,97,200,402,306⟩,⟨7,35,140,88,276,97,200,384,288⟩,[⟨3,1427917496215994717199381,⟨407,435,439,499,407,499,482,384,418⟩⟩]⟩
theorem node528 : UpperPrefix a [2,5,7,6,8,0,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,0,3] 30 cert528 (by decide +kernel)

def cert529 : Leaf := ⟨⟨232,0,96,0,232,140,300,110,206⟩,[(1,5),(3,6)],[(8,4,6),(0,5,1),(4,6,3)],⟨7,35,140,88,276,97,208,394,298⟩,⟨7,35,140,88,276,97,208,384,288⟩,[⟨1,1210109943228463907340289,⟨109,33,220,92,348,109,220,476,288⟩⟩]⟩
theorem node529 : UpperPrefix a [2,5,7,6,8,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,0,4] 30 cert529 (by decide +kernel)

theorem node530 : UpperPrefix a [2,5,7,6,8,0] 30 :=
  branch_upper a [2,5,7,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,6,8,0,0] 30 (by decide +kernel))
  node527
  (invalid_upper a [2,5,7,6,8,0,2] 30 (by decide +kernel))
  node528
  node529
  (invalid_upper a [2,5,7,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,0,8] 30 (by decide +kernel)))

def cert531 : Leaf := ⟨⟨88,92,336,4,72,29,28,92,92⟩,[],[(1,5,1),(0,6,5)],⟨7,35,140,88,276,98,193,408,312⟩,⟨7,35,140,88,276,98,193,384,288⟩,[⟨5,1212620933064445385507873,⟨7,3,156,220,476,79,221,476,477⟩⟩,⟨7,1567826828894854288808981,⟨279,51,319,379,279,362,379,256,288⟩⟩,⟨8,1181820998965301132821,⟨103,35,239,123,127,98,227,128,32⟩⟩]⟩
theorem node531 : UpperPrefix a [2,5,7,6,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,1,0] 30 cert531 (by decide +kernel)

def cert532 : Leaf := ⟨⟨432,404,0,421,161,405,0,53,149⟩,[(2,6),(6,2)],[(1,5,1)],⟨7,35,140,88,276,98,200,401,305⟩,⟨7,35,140,88,276,98,200,384,288⟩,[⟨3,1276506623110786531204117,⟨407,435,439,499,407,482,482,384,288⟩⟩,⟨6,1373498447997497194464305,⟨407,435,140,157,407,439,140,386,435⟩⟩]⟩
theorem node532 : UpperPrefix a [2,5,7,6,8,1,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,1,3] 30 cert532 (by decide +kernel)

def cert533 : Leaf := ⟨⟨200,204,65,0,201,141,269,77,205⟩,[(3,6)],[(8,4,6),(1,5,1),(4,6,3)],⟨7,35,140,88,276,98,208,393,297⟩,⟨7,35,140,88,276,98,208,384,288⟩,[⟨5,1212476025242835647202337,⟨79,3,220,92,476,79,220,476,477⟩⟩]⟩
theorem node533 : UpperPrefix a [2,5,7,6,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,1,4] 30 cert533 (by decide +kernel)

theorem node534 : UpperPrefix a [2,5,7,6,8,1] 30 :=
  branch_upper a [2,5,7,6,8,1] 30 (by decide) (fin9_cases _
  node531
  (invalid_upper a [2,5,7,6,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,2] 30 (by decide +kernel))
  node532
  node533
  (invalid_upper a [2,5,7,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,1,8] 30 (by decide +kernel)))

def cert535 : Leaf := ⟨⟨312,284,306,294,34,0,310,54,22⟩,[(5,3)],[(6,3,5)],⟨7,35,140,88,276,104,193,402,306⟩,⟨7,35,140,88,276,104,193,384,288⟩,[⟨0,1219579970899053657457664,⟨406,434,172,124,276,108,252,384,288⟩⟩,⟨7,1577271561860593579236373,⟨279,307,319,379,279,362,379,256,288⟩⟩,⟨3,1219580022408964715054081,⟨471,499,132,80,276,96,209,384,288⟩⟩]⟩
theorem node535 : UpperPrefix a [2,5,7,6,8,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,3,0] 30 cert535 (by decide +kernel)

def cert536 : Leaf := ⟨⟨56,28,305,165,33,0,53,53,21⟩,[(5,3)],[(6,3,5)],⟨7,35,140,88,276,104,194,401,305⟩,⟨7,35,140,88,276,104,194,384,288⟩,[⟨1,1219579970903593438412801,⟨405,445,172,124,276,124,508,384,296⟩⟩,⟨3,1219580022408964715054081,⟨471,499,132,80,276,96,450,384,288⟩⟩,⟨7,1275040104705127881907221,⟨279,307,319,379,279,362,322,256,288⟩⟩,⟨8,1181818711981115325973,⟨103,35,239,123,127,106,194,128,32⟩⟩]⟩
theorem node536 : UpperPrefix a [2,5,7,6,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,3,1] 30 cert536 (by decide +kernel)

def cert537 : Local := ⟨⟨168,140,35,0,171,0,303,47,143⟩,[(3,6),(5,3)],[(6,3,5),(8,4,6),(4,6,3),(4,6,5)]⟩
theorem node537 : UpperPrefix a [2,5,7,6,8,3,4] 30 :=
  local_sound a [2,5,7,6,8,3,4] 30 cert537 (by decide +kernel)

theorem node538 : UpperPrefix a [2,5,7,6,8,3] 30 :=
  branch_upper a [2,5,7,6,8,3] 30 (by decide) (fin9_cases _
  node535
  node536
  (invalid_upper a [2,5,7,6,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,3] 30 (by decide +kernel))
  node537
  (invalid_upper a [2,5,7,6,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,3,8] 30 (by decide +kernel)))

def cert539 : Leaf := ⟨⟨368,340,370,0,106,0,306,122,90⟩,[(3,5),(5,3)],[],⟨7,35,140,88,276,112,193,394,298⟩,⟨7,35,140,88,276,112,193,384,288⟩,[⟨0,1219570747527158537126912,⟨406,446,172,124,276,124,252,384,296⟩⟩,⟨7,1728387289312426521058325,⟨279,315,319,379,279,379,379,256,298⟩⟩,⟨2,1219570799318339485172737,⟨451,491,168,120,272,120,193,384,296⟩⟩,⟨3,1210107638185869580467221,⟨71,35,231,115,375,115,193,384,290⟩⟩]⟩
theorem node539 : UpperPrefix a [2,5,7,6,8,4,0] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,4,0] 30 cert539 (by decide +kernel)

def cert540 : Leaf := ⟨⟨368,340,369,0,105,0,305,121,89⟩,[(3,5),(5,3)],[],⟨7,35,140,88,276,112,194,393,297⟩,⟨7,35,140,88,276,112,194,384,288⟩,[⟨1,1219570747531556583636993,⟨405,445,172,124,276,124,508,384,296⟩⟩,⟨7,1426155832156960823729173,⟨279,315,319,379,279,379,322,256,298⟩⟩,⟨2,1219570799318339485172737,⟨451,491,168,120,272,120,450,384,296⟩⟩,⟨3,1210107638185869580467221,⟨71,35,231,115,375,115,194,384,290⟩⟩]⟩
theorem node540 : UpperPrefix a [2,5,7,6,8,4,1] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,4,1] 30 cert540 (by decide +kernel)

def cert541 : Leaf := ⟨⟨496,468,0,0,227,0,0,119,215⟩,[(2,6),(3,5),(5,3),(6,2)],[],⟨7,35,140,88,276,112,200,387,291⟩,⟨7,35,140,88,276,112,200,384,288⟩,[⟨3,1427917496215994717199381,⟨407,435,439,499,407,499,482,384,418⟩⟩]⟩
theorem node541 : UpperPrefix a [2,5,7,6,8,4,3] 30 :=
  Boolean.leaf_sound a [2,5,7,6,8,4,3] 30 cert541 (by decide +kernel)

theorem node542 : UpperPrefix a [2,5,7,6,8,4] 30 :=
  branch_upper a [2,5,7,6,8,4] 30 (by decide) (fin9_cases _
  node539
  node540
  (invalid_upper a [2,5,7,6,8,4,2] 30 (by decide +kernel))
  node541
  (invalid_upper a [2,5,7,6,8,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,4,8] 30 (by decide +kernel)))

theorem node543 : UpperPrefix a [2,5,7,6,8] 30 :=
  branch_upper a [2,5,7,6,8] 30 (by decide) (fin9_cases _
  node530
  node534
  (invalid_upper a [2,5,7,6,8,2] 30 (by decide +kernel))
  node538
  node542
  (invalid_upper a [2,5,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,8,8] 30 (by decide +kernel)))

theorem node544 : UpperPrefix a [2,5,7,6] 30 :=
  branch_upper a [2,5,7,6] 30 (by decide) (fin9_cases _
  node513
  node521
  (invalid_upper a [2,5,7,6,2] 30 (by decide +kernel))
  node526
  (invalid_upper a [2,5,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,6,7] 30 (by decide +kernel))
  node543)

def cert545 : Leaf := ⟨⟨152,152,273,129,0,153,25,89,217⟩,[(4,0)],[(2,0,4),(8,3,2),(1,5,1)],⟨7,35,140,280,21,98,216,472,376⟩,⟨7,35,140,280,21,98,192,384,288⟩,[⟨5,1212549596039808744948769,⟨23,19,204,476,21,87,204,476,477⟩⟩,⟨6,1210106412378135429530785,⟨23,51,157,282,21,55,157,415,315⟩⟩]⟩
theorem node545 : UpperPrefix a [2,5,7,8,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,1] 30 cert545 (by decide +kernel)

def cert546 : Leaf := ⟨⟨168,136,305,161,0,129,41,121,217⟩,[(4,0)],[(2,0,4),(8,3,2)],⟨7,35,140,280,21,104,194,464,368⟩,⟨7,35,140,280,21,104,194,384,288⟩,[⟨1,1512929318249882272661505,⟨21,53,140,280,21,492,508,384,292⟩⟩,⟨4,1210107637481083700784661,⟨103,35,239,267,103,104,194,384,288⟩⟩,⟨6,1210106412378135429530849,⟨23,51,157,282,21,63,159,415,315⟩⟩]⟩
theorem node546 : UpperPrefix a [2,5,7,8,0,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,3,1] 30 cert546 (by decide +kernel)

def cert547 : Leaf := ⟨⟨168,136,291,163,0,147,35,99,195⟩,[(4,0)],[(2,0,4),(8,3,2),(4,6,5)],⟨7,35,140,280,21,104,208,450,354⟩,⟨7,35,140,280,21,104,208,384,288⟩,[⟨6,1210106412378135429530785,⟨23,51,157,282,21,63,157,415,315⟩⟩,⟨3,1219580310639340866765825,⟨471,499,132,336,213,96,208,384,288⟩⟩]⟩
theorem node547 : UpperPrefix a [2,5,7,8,0,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,3,4] 30 cert547 (by decide +kernel)

theorem node548 : UpperPrefix a [2,5,7,8,0,3] 30 :=
  branch_upper a [2,5,7,8,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,0,3,0] 30 (by decide +kernel))
  node546
  (invalid_upper a [2,5,7,8,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,3] 30 (by decide +kernel))
  node547
  (invalid_upper a [2,5,7,8,0,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,3,8] 30 (by decide +kernel)))

def cert549 : Leaf := ⟨⟨248,216,368,224,0,136,56,120,216⟩,[(4,0)],[(2,0,4),(8,3,2)],⟨7,35,140,280,21,112,194,456,360⟩,⟨7,35,140,280,21,112,194,384,288⟩,[⟨0,1446687112635328692225024,⟨454,494,140,444,508,508,454,388,428⟩⟩,⟨1,1664340193606894903361537,⟨29,445,140,284,21,508,508,388,428⟩⟩]⟩
theorem node549 : UpperPrefix a [2,5,7,8,0,4,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,0,4,1] 30 cert549 (by decide +kernel)

def cert550 : Local := ⟨⟨248,216,0,227,0,139,0,123,219⟩,[(2,6),(4,0),(6,2)],[(2,0,4),(8,3,2),(8,3,6)]⟩
theorem node550 : UpperPrefix a [2,5,7,8,0,4,3] 30 :=
  local_sound a [2,5,7,8,0,4,3] 30 cert550 (by decide +kernel)

theorem node551 : UpperPrefix a [2,5,7,8,0,4] 30 :=
  branch_upper a [2,5,7,8,0,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,0,4,0] 30 (by decide +kernel))
  node549
  (invalid_upper a [2,5,7,8,0,4,2] 30 (by decide +kernel))
  node550
  (invalid_upper a [2,5,7,8,0,4,4] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,4,8] 30 (by decide +kernel)))

theorem node552 : UpperPrefix a [2,5,7,8,0] 30 :=
  branch_upper a [2,5,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,0,0] 30 (by decide +kernel))
  node545
  (invalid_upper a [2,5,7,8,0,2] 30 (by decide +kernel))
  node548
  node551
  (invalid_upper a [2,5,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,0,8] 30 (by decide +kernel)))

def cert553 : Leaf := ⟨⟨0,0,368,230,0,158,60,124,222⟩,[(0,4),(1,5),(4,0)],[(8,3,2),(0,5,1)],⟨7,35,140,280,22,97,216,472,376⟩,⟨7,35,140,280,22,97,192,384,288⟩,[⟨1,1210181496375334602276865,⟨5,33,204,476,20,97,192,384,288⟩⟩]⟩
theorem node553 : UpperPrefix a [2,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,0] 30 cert553 (by decide +kernel)

def cert554 : Leaf := ⟨⟨0,92,370,102,0,22,54,118,86⟩,[(0,4),(4,0)],[(8,3,2)],⟨7,35,140,280,22,104,193,464,368⟩,⟨7,35,140,280,22,104,193,384,288⟩,[⟨0,1512929318249882272662528,⟨22,54,140,280,22,492,508,384,292⟩⟩,⟨7,1511158430818668691620881,⟨23,51,12,281,23,362,379,256,288⟩⟩,⟨3,1219801815683413457241105,⟨471,499,196,465,471,224,209,384,288⟩⟩]⟩
theorem node554 : UpperPrefix a [2,5,7,8,1,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,3,0] 30 cert554 (by decide +kernel)

def cert555 : Leaf := ⟨⟨0,76,355,103,0,23,39,103,71⟩,[(0,4),(4,0)],[(8,3,2),(4,6,5)],⟨7,35,140,280,22,104,208,449,353⟩,⟨7,35,140,280,22,104,208,384,288⟩,[⟨7,1511158430818668691620881,⟨23,51,12,281,23,362,379,256,288⟩⟩,⟨3,1219801815683413457241105,⟨471,499,196,465,471,224,209,384,288⟩⟩]⟩
theorem node555 : UpperPrefix a [2,5,7,8,1,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,3,4] 30 cert555 (by decide +kernel)

theorem node556 : UpperPrefix a [2,5,7,8,1,3] 30 :=
  branch_upper a [2,5,7,8,1,3] 30 (by decide) (fin9_cases _
  node554
  (invalid_upper a [2,5,7,8,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,3] 30 (by decide +kernel))
  node555
  (invalid_upper a [2,5,7,8,1,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,3,8] 30 (by decide +kernel)))

def cert557 : Leaf := ⟨⟨0,12,259,39,0,143,15,79,95⟩,[(0,4),(4,0)],[(8,3,2)],⟨7,35,140,280,22,112,201,457,361⟩,⟨7,35,140,280,22,112,192,384,288⟩,[⟨4,1210181496374235090666513,⟨7,35,204,461,7,99,192,384,290⟩⟩,⟨5,1210181495249503414912017,⟨23,19,204,477,23,81,192,384,256⟩⟩,⟨6,1210106412373462505112753,⟨23,51,157,283,23,55,157,415,315⟩⟩,⟨7,1360042701115036204549137,⟨31,315,12,281,31,379,64,256,298⟩⟩]⟩
theorem node557 : UpperPrefix a [2,5,7,8,1,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,1,4] 30 cert557 (by decide +kernel)

theorem node558 : UpperPrefix a [2,5,7,8,1] 30 :=
  branch_upper a [2,5,7,8,1] 30 (by decide) (fin9_cases _
  node553
  (invalid_upper a [2,5,7,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,2] 30 (by decide +kernel))
  node556
  node557
  (invalid_upper a [2,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,1,8] 30 (by decide +kernel)))

def cert559 : Leaf := ⟨⟨176,0,306,166,0,150,54,118,214⟩,[(1,5),(4,2)],[(8,3,2),(3,4,4),(0,5,1)],⟨7,35,140,280,28,97,210,466,370⟩,⟨7,35,140,280,28,97,192,384,288⟩,[⟨6,1210106412375833327060129,⟨23,35,157,282,28,55,157,415,291⟩⟩]⟩
theorem node559 : UpperPrefix a [2,5,7,8,3,0] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,0] 30 cert559 (by decide +kernel)

def cert560 : Leaf := ⟨⟨144,148,273,133,0,149,21,85,213⟩,[(4,2)],[(8,3,2),(3,4,4),(1,5,1)],⟨7,35,140,280,28,98,209,465,369⟩,⟨7,35,140,280,28,98,192,384,288⟩,[⟨5,1212473359117067647714337,⟨23,3,156,476,28,87,220,476,477⟩⟩,⟨6,1210106412375833327060129,⟨23,35,157,282,28,55,157,415,291⟩⟩]⟩
theorem node560 : UpperPrefix a [2,5,7,8,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,1] 30 cert560 (by decide +kernel)

def cert561 : Leaf := ⟨⟨160,132,290,166,0,134,39,103,199⟩,[(4,2)],[(8,3,2),(3,4,4)],⟨7,35,140,280,28,112,195,451,355⟩,⟨7,35,140,280,28,112,192,384,288⟩,[⟨4,1373431200244494031275049,⟨455,483,205,463,205,487,192,450,483⟩⟩,⟨6,1210106412375833327060129,⟨23,35,157,282,28,55,157,415,291⟩⟩,⟨0,1210107567549137747444736,⟨22,34,156,280,28,116,252,412,288⟩⟩]⟩
theorem node561 : UpperPrefix a [2,5,7,8,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,3,4] 30 cert561 (by decide +kernel)

theorem node562 : UpperPrefix a [2,5,7,8,3] 30 :=
  branch_upper a [2,5,7,8,3] 30 (by decide) (fin9_cases _
  node559
  node560
  (invalid_upper a [2,5,7,8,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,3] 30 (by decide +kernel))
  node561
  (invalid_upper a [2,5,7,8,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,3,8] 30 (by decide +kernel)))

def cert563 : Leaf := ⟨⟨112,0,368,100,160,22,52,124,92⟩,[(1,5)],[(7,2,4),(8,3,2),(0,5,1),(1,6,5)],⟨7,35,140,280,84,97,194,408,312⟩,⟨7,35,140,280,84,97,194,384,288⟩,[⟨3,1210107638080660061584917,⟨119,51,247,307,119,115,194,384,290⟩⟩]⟩
theorem node563 : UpperPrefix a [2,5,7,8,6,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,0,1] 30 cert563 (by decide +kernel)

def cert564 : Local := ⟨⟨112,0,0,102,170,22,0,118,86⟩,[(1,5),(2,6),(6,2)],[(7,2,4),(8,3,2),(8,3,6),(0,5,1),(3,6,4)]⟩
theorem node564 : UpperPrefix a [2,5,7,8,6,0,3] 30 :=
  local_sound a [2,5,7,8,6,0,3] 30 cert564 (by decide +kernel)

def cert565 : Leaf := ⟨⟨104,0,352,100,168,12,44,110,78⟩,[(1,5)],[(7,2,4),(8,3,2),(0,5,1)],⟨7,35,140,280,84,97,208,394,298⟩,⟨7,35,140,280,84,97,208,384,288⟩,[⟨1,1210109943235427659939841,⟨117,49,220,280,84,117,220,476,312⟩⟩,⟨4,1247997180424901362775069,⟨135,35,399,431,231,99,227,384,290⟩⟩]⟩
theorem node565 : UpperPrefix a [2,5,7,8,6,0,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,0,4] 30 cert565 (by decide +kernel)

theorem node566 : UpperPrefix a [2,5,7,8,6,0] 30 :=
  branch_upper a [2,5,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,6,0,0] 30 (by decide +kernel))
  node563
  (invalid_upper a [2,5,7,8,6,0,2] 30 (by decide +kernel))
  node564
  node565
  (invalid_upper a [2,5,7,8,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,0,8] 30 (by decide +kernel)))

def cert567 : Leaf := ⟨⟨64,68,337,69,137,5,29,93,93⟩,[],[(7,2,4),(8,3,2),(1,5,1)],⟨7,35,140,280,84,98,217,409,313⟩,⟨7,35,140,280,84,98,192,384,288⟩,[⟨5,1212473359118991793062945,⟨7,19,156,476,84,87,220,476,477⟩⟩,⟨3,1210107565846800565810197,⟨7,35,135,307,119,98,192,384,288⟩⟩,⟨4,1210107565845702127924245,⟨7,35,143,299,103,98,192,384,288⟩⟩]⟩
theorem node567 : UpperPrefix a [2,5,7,8,6,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,1] 30 cert567 (by decide +kernel)

def cert568 : Leaf := ⟨⟨88,92,336,68,136,20,30,124,92⟩,[],[(5,1,7),(7,2,4),(8,3,2),(1,7,6)],⟨7,35,140,280,84,104,193,386,304⟩,⟨7,35,140,280,84,104,193,386,288⟩,[⟨0,1786263949131455515067392,⟨398,446,396,312,380,380,508,398,312⟩⟩]⟩
theorem node568 : UpperPrefix a [2,5,7,8,6,3,0,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,3,0,1] 30 cert568 (by decide +kernel)

def cert569 : Local := ⟨⟨104,76,371,0,171,7,46,0,79⟩,[(3,7),(7,3)],[(7,2,4),(8,3,2),(4,7,2)]⟩
theorem node569 : UpperPrefix a [2,5,7,8,6,3,0,4] 30 :=
  local_sound a [2,5,7,8,6,3,0,4] 30 cert569 (by decide +kernel)

theorem node570 : UpperPrefix a [2,5,7,8,6,3,0] 30 :=
  branch_upper a [2,5,7,8,6,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,5,7,8,6,3,0,0] 30 (by decide +kernel))
  node568
  (invalid_upper a [2,5,7,8,6,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,0,3] 30 (by decide +kernel))
  node569
  (invalid_upper a [2,5,7,8,6,3,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,0,8] 30 (by decide +kernel)))

def cert571 : Leaf := ⟨⟨40,12,305,101,161,5,37,53,85⟩,[],[(7,2,4),(8,3,2)],⟨7,35,140,280,84,104,194,401,305⟩,⟨7,35,140,280,84,104,194,384,288⟩,[⟨1,1219570747815054792196097,⟨397,445,140,312,124,124,508,396,312⟩⟩,⟨3,1219580022408964715054081,⟨471,499,132,272,84,96,450,384,288⟩⟩,⟨4,1210107637481083700784661,⟨103,35,239,267,103,104,194,384,288⟩⟩,⟨6,1210180199338641928111403,⟨7,39,141,415,20,175,131,387,295⟩⟩]⟩
theorem node571 : UpperPrefix a [2,5,7,8,6,3,1] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,3,1] 30 cert571 (by decide +kernel)

def cert572 : Leaf := ⟨⟨40,12,288,100,168,20,44,47,15⟩,[],[(7,2,4),(8,3,2),(4,6,5)],⟨7,35,140,280,84,104,208,387,291⟩,⟨7,35,140,280,84,104,208,384,288⟩,[⟨0,1210109950096380217263104,⟨118,50,252,280,116,124,252,508,312⟩⟩,⟨1,1210109950096380217262081,⟨117,49,252,280,116,124,252,508,312⟩⟩,⟨6,1373424661018934605137195,⟨391,423,141,415,20,431,144,387,423⟩⟩]⟩
theorem node572 : UpperPrefix a [2,5,7,8,6,3,4] 30 :=
  Boolean.leaf_sound a [2,5,7,8,6,3,4] 30 cert572 (by decide +kernel)

theorem node573 : UpperPrefix a [2,5,7,8,6,3] 30 :=
  branch_upper a [2,5,7,8,6,3] 30 (by decide) (fin9_cases _
  node570
  node571
  (invalid_upper a [2,5,7,8,6,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,3] 30 (by decide +kernel))
  node572
  (invalid_upper a [2,5,7,8,6,3,5] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,6] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,5,7,8,6,3,8] 30 (by decide +kernel)))

def cert574 : Local := ⟨⟨24,28,273,5,137,0,30,61,29⟩,[(5,4)],[(5,1,7),(7,2,4),(8,3,2),(6,4,5),(1,7,6)]⟩
theorem node574 : UpperPrefix a [2,5,7,8,6,4,0,1] 30 :=
  local_sound a [2,5,7,8,6,4,0,1] 30 cert574 (by decide +kernel)

def cert575 : Local := ⟨⟨48,20,0,39,163,0,54,0,23⟩,[(2,7),(5,4),(7,3)],[(7,2,4),(8,3,2),(8,3,7),(6,4,5),(3,7,2)]⟩
theorem node575 : UpperPrefix a [2,5,7,8,6,4,0,3] 30 :=
  local_sound a [2,5,7,8,6,4,0,3] 30 cert575 (by decide +kernel)

#print axioms node575
end Delivery.FiniteExclusion.Sharp2x3x4
