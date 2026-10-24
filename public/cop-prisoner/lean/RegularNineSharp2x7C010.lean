import RegularNineSharp2x7Base
import RegularNineSharp2x7C009
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert640 : Local := ⟨⟨352,356,0,0,71,0,295,103,99⟩,[(2,6),(3,1),(5,6)],[(4,1,3),(7,5,5),(3,6,2)]⟩
theorem node640 : UpperPrefix a [2,4,6,1,8,7,3] 30 :=
  local_sound a [2,4,6,1,8,7,3] 30 cert640 (by decide +kernel)

def cert641 : Local := ⟨⟨360,364,291,0,79,0,0,111,107⟩,[(3,1),(5,6),(6,5)],[(4,1,3),(7,5,5),(7,5,6)]⟩
theorem node641 : UpperPrefix a [2,4,6,1,8,7,5] 30 :=
  local_sound a [2,4,6,1,8,7,5] 30 cert641 (by decide +kernel)

theorem node642 : UpperPrefix a [2,4,6,1,8,7] 30 :=
  branch_upper a [2,4,6,1,8,7] 30 (by decide) (fin9_cases _
  node639
  (invalid_upper a [2,4,6,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,7,2] 30 (by decide +kernel))
  node640
  (invalid_upper a [2,4,6,1,8,7,4] 30 (by decide +kernel))
  node641
  (invalid_upper a [2,4,6,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,7,8] 30 (by decide +kernel)))

theorem node643 : UpperPrefix a [2,4,6,1,8] 30 :=
  branch_upper a [2,4,6,1,8] 30 (by decide) (fin9_cases _
  node637
  (invalid_upper a [2,4,6,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,2] 30 (by decide +kernel))
  node638
  (invalid_upper a [2,4,6,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,6] 30 (by decide +kernel))
  node642
  (invalid_upper a [2,4,6,1,8,8] 30 (by decide +kernel)))

theorem node644 : UpperPrefix a [2,4,6,1] 30 :=
  branch_upper a [2,4,6,1] 30 (by decide) (fin9_cases _
  node623
  (invalid_upper a [2,4,6,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,2] 30 (by decide +kernel))
  node624
  (invalid_upper a [2,4,6,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,6] 30 (by decide +kernel))
  node634
  node643)

def cert645 : Leaf := ⟨⟨88,0,18,0,78,414,286,94,218⟩,[(1,4),(3,4)],[(5,3,3),(0,4,1)],⟨7,19,76,56,49,490,458,394,398⟩,⟨7,19,76,56,49,96,192,384,260⟩,[⟨7,1208926973665889504755005,⟨7,27,95,63,63,127,64,257,263⟩⟩,⟨8,1181745671977741352253,⟨7,27,95,63,63,127,192,129,7⟩⟩]⟩
theorem node645 : UpperPrefix a [2,4,6,5,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,0] 30 cert645 (by decide +kernel)

def cert646 : Leaf := ⟨⟨408,396,384,0,397,396,268,12,136⟩,[(3,4)],[(5,3,3),(1,4,1),(0,5,4)],⟨7,19,76,56,50,97,456,392,396⟩,⟨7,19,76,56,50,97,192,384,260⟩,[⟨4,1266886859749596662334465,⟨487,35,460,492,34,97,192,384,452⟩⟩,⟨6,1229032771784728300768517,⟨391,27,415,58,58,59,128,385,391⟩⟩]⟩
theorem node646 : UpperPrefix a [2,4,6,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,1,0] 30 cert646 (by decide +kernel)

def cert647 : Leaf := ⟨⟨456,460,0,0,461,0,269,77,201⟩,[(2,5),(3,4),(5,2)],[(5,3,3),(1,4,1)],⟨7,19,76,56,50,104,449,385,389⟩,⟨7,19,76,56,50,104,192,384,260⟩,[⟨4,1328416245210460615345169,⟨487,451,492,493,487,492,192,384,292⟩⟩]⟩
theorem node647 : UpperPrefix a [2,4,6,5,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,1,3] 30 cert647 (by decide +kernel)

def cert648 : Local := ⟨⟨344,332,273,0,333,0,285,93,89⟩,[(3,4),(5,6)],[(5,3,3),(1,4,1),(7,5,5)]⟩
theorem node648 : UpperPrefix a [2,4,6,5,1,7] 30 :=
  local_sound a [2,4,6,5,1,7] 30 cert648 (by decide +kernel)

def cert649 : Leaf := ⟨⟨24,12,17,0,13,157,285,29,153⟩,[(3,4)],[(5,3,3),(1,4,1)],⟨7,19,76,56,50,352,201,393,397⟩,⟨7,19,76,56,50,352,192,384,260⟩,[⟨6,1229327919689907653594373,⟨391,27,415,186,186,443,128,385,391⟩⟩,⟨7,1208926973665889504755005,⟨7,27,95,63,63,383,64,257,263⟩⟩,⟨8,1181745671977741352253,⟨7,27,95,63,63,127,192,129,7⟩⟩]⟩
theorem node649 : UpperPrefix a [2,4,6,5,1,8] 30 :=
  Boolean.leaf_sound a [2,4,6,5,1,8] 30 cert649 (by decide +kernel)

theorem node650 : UpperPrefix a [2,4,6,5,1] 30 :=
  branch_upper a [2,4,6,5,1] 30 (by decide) (fin9_cases _
  node646
  (invalid_upper a [2,4,6,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,2] 30 (by decide +kernel))
  node647
  (invalid_upper a [2,4,6,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,1,6] 30 (by decide +kernel))
  node648
  node649)

def cert651 : Leaf := ⟨⟨408,396,403,0,0,391,263,7,131⟩,[(3,4),(4,3)],[(5,3,3),(5,3,4)],⟨7,19,76,56,56,483,451,387,391⟩,⟨7,19,76,56,56,96,192,384,260⟩,[⟨3,1214857656031579466630145,⟨487,499,68,48,48,96,192,384,260⟩⟩,⟨4,1214857656030481028744193,⟨487,483,76,40,40,96,192,384,260⟩⟩,⟨6,1236143991625143332900101,⟨391,411,415,56,56,56,128,385,391⟩⟩]⟩
theorem node651 : UpperPrefix a [2,4,6,5,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,3] 30 cert651 (by decide +kernel)

def cert652 : Leaf := ⟨⟨216,204,144,0,76,158,28,92,216⟩,[(3,4)],[(5,3,3),(1,6,5)],⟨7,19,76,56,176,97,194,392,268⟩,⟨7,19,76,56,176,97,194,384,260⟩,[⟨8,1184347566765703298559,⟨47,127,127,127,255,127,255,255,47⟩⟩,⟨0,1503466190334005444346880,⟨454,478,476,444,444,508,454,384,388⟩⟩]⟩
theorem node652 : UpperPrefix a [2,4,6,5,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,0,1] 30 cert652 (by decide +kernel)

def cert653 : Leaf := ⟨⟨400,388,0,0,263,406,279,23,147⟩,[(2,6),(3,4)],[(5,3,3),(3,6,2)],⟨7,19,76,56,176,97,200,386,262⟩,⟨7,19,76,56,176,97,200,384,260⟩,[⟨6,1236439139530322685742341,⟨391,411,415,186,186,443,152,385,391⟩⟩]⟩
theorem node653 : UpperPrefix a [2,4,6,5,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,0,3] 30 cert653 (by decide +kernel)

def cert654 : Leaf := ⟨⟨208,196,147,0,71,150,0,95,219⟩,[(3,4),(6,7)],[(5,3,3),(8,6,6)],⟨7,19,76,56,176,97,448,394,270⟩,⟨7,19,76,56,176,97,448,384,260⟩,[⟨3,1210109878036190895131909,⟨39,19,119,50,242,115,499,499,295⟩⟩]⟩
theorem node654 : UpperPrefix a [2,4,6,5,7,0,8] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,0,8] 30 cert654 (by decide +kernel)

theorem node655 : UpperPrefix a [2,4,6,5,7,0] 30 :=
  branch_upper a [2,4,6,5,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,5,7,0,0] 30 (by decide +kernel))
  node652
  (invalid_upper a [2,4,6,5,7,0,2] 30 (by decide +kernel))
  node653
  (invalid_upper a [2,4,6,5,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,0,7] 30 (by decide +kernel))
  node654)

def cert656 : Leaf := ⟨⟨216,204,144,0,76,157,28,92,216⟩,[(3,4)],[(5,3,3),(0,6,5)],⟨7,19,76,56,176,98,193,392,268⟩,⟨7,19,76,56,176,98,193,384,260⟩,[⟨8,1184347566765703298559,⟨47,127,127,127,255,127,255,255,47⟩⟩,⟨1,1503466190334005444345857,⟨453,477,476,444,444,508,193,384,388⟩⟩]⟩
theorem node656 : UpperPrefix a [2,4,6,5,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,1,0] 30 cert656 (by decide +kernel)

def cert657 : Leaf := ⟨⟨448,452,0,0,327,389,263,71,195⟩,[(2,6),(3,4)],[(5,3,3),(3,6,2)],⟨7,19,76,56,176,98,200,385,261⟩,⟨7,19,76,56,176,98,200,384,260⟩,[⟨4,1404268986238548564771873,⟨487,419,460,493,417,487,460,384,324⟩⟩]⟩
theorem node657 : UpperPrefix a [2,4,6,5,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,1,3] 30 cert657 (by decide +kernel)

def cert658 : Leaf := ⟨⟨216,204,145,0,77,157,0,93,217⟩,[(3,4),(6,7)],[(5,3,3),(8,6,6)],⟨7,19,76,56,176,98,448,393,269⟩,⟨7,19,76,56,176,98,448,384,260⟩,[⟨1,1219573681342827212570625,⟨453,477,76,124,252,508,448,448,260⟩⟩]⟩
theorem node658 : UpperPrefix a [2,4,6,5,7,1,8] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,1,8] 30 cert658 (by decide +kernel)

theorem node659 : UpperPrefix a [2,4,6,5,7,1] 30 :=
  branch_upper a [2,4,6,5,7,1] 30 (by decide) (fin9_cases _
  node656
  (invalid_upper a [2,4,6,5,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,1,2] 30 (by decide +kernel))
  node657
  (invalid_upper a [2,4,6,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,1,7] 30 (by decide +kernel))
  node658)

def cert660 : Leaf := ⟨⟨472,460,0,0,335,0,263,71,195⟩,[(2,5),(3,4),(5,2)],[(5,3,3)],⟨7,19,76,56,176,104,451,387,263⟩,⟨7,19,76,56,176,104,192,384,260⟩,[⟨3,1214857655926026350363649,⟨455,467,68,48,176,96,192,384,260⟩⟩,⟨4,1214857656065665409221633,⟨487,451,108,44,164,108,192,384,292⟩⟩]⟩
theorem node660 : UpperPrefix a [2,4,6,5,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,3] 30 cert660 (by decide +kernel)

def cert661 : Leaf := ⟨⟨208,196,146,0,326,150,22,94,218⟩,[(3,4)],[(5,3,3),(8,5,4)],⟨7,19,76,56,176,352,193,394,270⟩,⟨7,19,76,56,176,352,193,384,260⟩,[⟨0,1214857604139045350278144,⟨398,410,124,60,188,380,508,384,268⟩⟩,⟨3,1210109875643653593091333,⟨7,19,87,50,242,371,243,499,263⟩⟩]⟩
theorem node661 : UpperPrefix a [2,4,6,5,7,8,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,0] 30 cert661 (by decide +kernel)

def cert662 : Leaf := ⟨⟨144,132,147,0,263,151,21,31,155⟩,[(3,4)],[(5,3,3),(8,5,4)],⟨7,19,76,56,176,352,194,393,269⟩,⟨7,19,76,56,176,352,194,384,260⟩,[⟨3,1210110163874029744770309,⟨7,83,87,114,242,371,242,499,263⟩⟩,⟨6,1229327919689907653594373,⟨391,27,415,186,186,443,130,385,391⟩⟩]⟩
theorem node662 : UpperPrefix a [2,4,6,5,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,5,7,8,1] 30 cert662 (by decide +kernel)

def cert663 : Local := ⟨⟨208,196,0,0,327,151,23,87,211⟩,[(2,6),(3,4)],[(5,3,3),(8,5,4),(3,6,2)]⟩
theorem node663 : UpperPrefix a [2,4,6,5,7,8,3] 30 :=
  local_sound a [2,4,6,5,7,8,3] 30 cert663 (by decide +kernel)

theorem node664 : UpperPrefix a [2,4,6,5,7,8] 30 :=
  branch_upper a [2,4,6,5,7,8] 30 (by decide) (fin9_cases _
  node661
  node662
  (invalid_upper a [2,4,6,5,7,8,2] 30 (by decide +kernel))
  node663
  (invalid_upper a [2,4,6,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,8,8] 30 (by decide +kernel)))

theorem node665 : UpperPrefix a [2,4,6,5,7] 30 :=
  branch_upper a [2,4,6,5,7] 30 (by decide) (fin9_cases _
  node655
  node659
  (invalid_upper a [2,4,6,5,7,2] 30 (by decide +kernel))
  node660
  (invalid_upper a [2,4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,7,7] 30 (by decide +kernel))
  node664)

def cert666 : Leaf := ⟨⟨472,460,400,0,204,394,264,72,200⟩,[(3,4)],[(5,3,3),(1,6,5)],⟨7,19,76,56,304,97,194,392,396⟩,⟨7,19,76,56,304,97,194,384,260⟩,[⟨0,1503466190334005444346880,⟨454,478,476,444,444,508,454,384,388⟩⟩,⟨4,1229033942822329800197121,⟨487,99,460,40,288,97,226,384,388⟩⟩,⟨2,1210255175370793912632321,⟨107,251,72,184,440,97,234,384,256⟩⟩]⟩
theorem node666 : UpperPrefix a [2,4,6,5,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,0,1] 30 cert666 (by decide +kernel)

def cert667 : Leaf := ⟨⟨464,452,0,0,198,406,278,86,210⟩,[(2,6),(3,4)],[(5,3,3),(3,6,2)],⟨7,19,76,56,304,97,200,386,390⟩,⟨7,19,76,56,304,97,200,384,260⟩,[⟨0,1224302947340326006162432,⟨454,478,76,124,380,508,204,384,260⟩⟩]⟩
theorem node667 : UpperPrefix a [2,4,6,5,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,0,3] 30 cert667 (by decide +kernel)

theorem node668 : UpperPrefix a [2,4,6,5,8,0] 30 :=
  branch_upper a [2,4,6,5,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,5,8,0,0] 30 (by decide +kernel))
  node666
  (invalid_upper a [2,4,6,5,8,0,2] 30 (by decide +kernel))
  node667
  (invalid_upper a [2,4,6,5,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,0,8] 30 (by decide +kernel)))

def cert669 : Leaf := ⟨⟨464,452,400,0,196,405,276,92,216⟩,[(3,4)],[(5,3,3),(0,6,5)],⟨7,19,76,56,304,98,193,392,396⟩,⟨7,19,76,56,304,98,193,384,260⟩,[⟨1,1503466190334005444345857,⟨453,477,476,444,444,508,193,384,388⟩⟩,⟨3,1210109878049385034786053,⟨39,19,103,50,307,98,243,499,311⟩⟩]⟩
theorem node669 : UpperPrefix a [2,4,6,5,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,1,0] 30 cert669 (by decide +kernel)

def cert670 : Leaf := ⟨⟨448,452,0,0,199,389,263,71,195⟩,[(2,6),(3,4)],[(5,3,3),(3,6,2)],⟨7,19,76,56,304,98,200,385,389⟩,⟨7,19,76,56,304,98,200,384,260⟩,[⟨4,1404268986238548564771873,⟨487,419,460,493,417,487,460,384,324⟩⟩]⟩
theorem node670 : UpperPrefix a [2,4,6,5,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,1,3] 30 cert670 (by decide +kernel)

theorem node671 : UpperPrefix a [2,4,6,5,8,1] 30 :=
  branch_upper a [2,4,6,5,8,1] 30 (by decide) (fin9_cases _
  node669
  (invalid_upper a [2,4,6,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,1,2] 30 (by decide +kernel))
  node670
  (invalid_upper a [2,4,6,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,1,8] 30 (by decide +kernel)))

def cert672 : Leaf := ⟨⟨472,460,0,0,207,0,263,71,195⟩,[(2,5),(3,4),(5,2)],[(5,3,3)],⟨7,19,76,56,304,104,195,387,391⟩,⟨7,19,76,56,304,104,192,384,260⟩,[⟨3,1214857655926026350363649,⟨455,467,68,48,304,96,192,384,260⟩⟩,⟨4,1214857656065665409221633,⟨487,451,108,44,292,108,192,384,292⟩⟩]⟩
theorem node672 : UpperPrefix a [2,4,6,5,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,3] 30 cert672 (by decide +kernel)

def cert673 : Leaf := ⟨⟨344,332,274,0,78,0,286,94,90⟩,[(3,4),(5,6)],[(5,3,3),(7,5,5)],⟨7,19,76,56,304,224,193,394,270⟩,⟨7,19,76,56,304,224,193,384,260⟩,[⟨0,1214857604139045350278144,⟨398,410,124,60,316,252,508,384,268⟩⟩]⟩
theorem node673 : UpperPrefix a [2,4,6,5,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,7,0] 30 cert673 (by decide +kernel)

def cert674 : Local := ⟨⟨344,328,274,0,74,0,281,94,90⟩,[(3,4),(5,6)],[(2,0,7),(5,3,3),(7,5,5),(0,7,6)]⟩
theorem node674 : UpperPrefix a [2,4,6,5,8,7,1,0] 30 :=
  local_sound a [2,4,6,5,8,7,1,0] 30 cert674 (by decide +kernel)

def cert675 : Leaf := ⟨⟨336,324,275,0,71,0,277,87,83⟩,[(3,4),(5,6)],[(5,3,3),(7,5,5)],⟨7,19,76,56,304,224,194,392,261⟩,⟨7,19,76,56,304,224,194,392,260⟩,[⟨3,1233722286766430767755013,⟨279,275,375,114,371,242,242,499,279⟩⟩]⟩
theorem node675 : UpperPrefix a [2,4,6,5,8,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,5,8,7,1,3] 30 cert675 (by decide +kernel)

theorem node676 : UpperPrefix a [2,4,6,5,8,7,1] 30 :=
  branch_upper a [2,4,6,5,8,7,1] 30 (by decide) (fin9_cases _
  node674
  (invalid_upper a [2,4,6,5,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,2] 30 (by decide +kernel))
  node675
  (invalid_upper a [2,4,6,5,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,1,8] 30 (by decide +kernel)))

def cert677 : Local := ⟨⟨336,324,0,0,71,0,279,87,83⟩,[(2,6),(3,4),(5,6)],[(5,3,3),(7,5,5),(3,6,2)]⟩
theorem node677 : UpperPrefix a [2,4,6,5,8,7,3] 30 :=
  local_sound a [2,4,6,5,8,7,3] 30 cert677 (by decide +kernel)

theorem node678 : UpperPrefix a [2,4,6,5,8,7] 30 :=
  branch_upper a [2,4,6,5,8,7] 30 (by decide) (fin9_cases _
  node673
  node676
  (invalid_upper a [2,4,6,5,8,7,2] 30 (by decide +kernel))
  node677
  (invalid_upper a [2,4,6,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,7,8] 30 (by decide +kernel)))

theorem node679 : UpperPrefix a [2,4,6,5,8] 30 :=
  branch_upper a [2,4,6,5,8] 30 (by decide) (fin9_cases _
  node668
  node671
  (invalid_upper a [2,4,6,5,8,2] 30 (by decide +kernel))
  node672
  (invalid_upper a [2,4,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,8,6] 30 (by decide +kernel))
  node678
  (invalid_upper a [2,4,6,5,8,8] 30 (by decide +kernel)))

theorem node680 : UpperPrefix a [2,4,6,5] 30 :=
  branch_upper a [2,4,6,5] 30 (by decide) (fin9_cases _
  node645
  node650
  (invalid_upper a [2,4,6,5,2] 30 (by decide +kernel))
  node651
  (invalid_upper a [2,4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,5,6] 30 (by decide +kernel))
  node665
  node679)

def cert681 : Leaf := ⟨⟨112,0,176,100,70,20,316,124,120⟩,[(1,4)],[(7,3,2),(0,4,1),(1,5,4)],⟨7,19,76,152,49,98,488,424,300⟩,⟨7,19,76,152,49,98,192,384,260⟩,[⟨8,1181748086318461878133,⟨55,19,127,155,55,127,255,155,55⟩⟩,⟨3,1210107567694323698052869,⟨55,19,119,146,51,98,226,403,311⟩⟩]⟩
theorem node681 : UpperPrefix a [2,4,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,1] 30 cert681 (by decide +kernel)

def cert682 : Leaf := ⟨⟨376,0,0,358,334,0,302,110,106⟩,[(1,4),(2,5),(5,2)],[(7,3,2),(7,3,5),(0,4,1)],⟨7,19,76,152,49,104,482,418,294⟩,⟨7,19,76,152,49,104,192,384,260⟩,[⟨4,1214839173292794680706049,⟨487,451,108,136,485,108,192,384,292⟩⟩]⟩
theorem node682 : UpperPrefix a [2,4,6,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,3] 30 cert682 (by decide +kernel)

def cert683 : Leaf := ⟨⟨376,0,432,356,332,12,300,108,104⟩,[(1,4)],[(7,3,2),(0,4,1)],⟨7,19,76,152,49,352,194,424,300⟩,⟨7,19,76,152,49,352,194,384,260⟩,[⟨1,1536734841617598450237441,⟨445,409,492,152,441,484,492,384,420⟩⟩,⟨4,1229033942892698544374785,⟨487,99,492,136,97,352,194,384,420⟩⟩]⟩
theorem node683 : UpperPrefix a [2,4,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,8,1] 30 cert683 (by decide +kernel)

def cert684 : Local := ⟨⟨368,0,0,358,326,22,0,118,114⟩,[(1,4),(2,6),(6,3)],[(7,3,2),(7,3,6),(0,4,1),(3,6,2)]⟩
theorem node684 : UpperPrefix a [2,4,6,7,0,8,3] 30 :=
  local_sound a [2,4,6,7,0,8,3] 30 cert684 (by decide +kernel)

def cert685 : Leaf := ⟨⟨120,0,160,102,78,12,268,126,122⟩,[(1,4)],[(7,3,2),(0,4,1),(8,5,6)],⟨7,19,76,152,49,352,224,394,270⟩,⟨7,19,76,152,49,352,224,384,260⟩,[⟨1,1210110019745648605134849,⟨5,17,76,252,49,352,224,480,260⟩⟩,⟨4,1210110019744549093508097,⟨7,3,76,236,33,352,224,480,260⟩⟩]⟩
theorem node685 : UpperPrefix a [2,4,6,7,0,8,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,0,8,5] 30 cert685 (by decide +kernel)

theorem node686 : UpperPrefix a [2,4,6,7,0,8] 30 :=
  branch_upper a [2,4,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,0,8,0] 30 (by decide +kernel))
  node683
  (invalid_upper a [2,4,6,7,0,8,2] 30 (by decide +kernel))
  node684
  (invalid_upper a [2,4,6,7,0,8,4] 30 (by decide +kernel))
  node685
  (invalid_upper a [2,4,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,8,8] 30 (by decide +kernel)))

theorem node687 : UpperPrefix a [2,4,6,7,0] 30 :=
  branch_upper a [2,4,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,0,0] 30 (by decide +kernel))
  node681
  (invalid_upper a [2,4,6,7,0,2] 30 (by decide +kernel))
  node682
  (invalid_upper a [2,4,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,0,7] 30 (by decide +kernel))
  node686)

def cert688 : Leaf := ⟨⟨112,96,176,100,65,20,316,124,120⟩,[],[(7,3,2),(1,4,1),(0,5,4)],⟨7,19,76,152,50,97,488,424,300⟩,⟨7,19,76,152,50,97,192,384,260⟩,[⟨8,1181748086318461878133,⟨55,19,127,155,55,127,255,155,55⟩⟩,⟨3,1210107565444722907631365,⟨55,19,119,146,50,115,194,403,311⟩⟩,⟨2,1210107565286050708341761,⟨3,19,72,152,50,115,192,384,256⟩⟩]⟩
theorem node688 : UpperPrefix a [2,4,6,7,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,1,0] 30 cert688 (by decide +kernel)

def cert689 : Leaf := ⟨⟨104,108,0,101,77,0,301,109,105⟩,[(2,5),(5,2)],[(7,3,2),(7,3,5),(1,4,1)],⟨7,19,76,152,50,104,481,417,293⟩,⟨7,19,76,152,50,104,192,384,260⟩,[⟨4,1328397762437589886829585,⟨487,451,492,493,487,492,192,384,292⟩⟩,⟨8,1181748086318461878133,⟨55,19,127,155,55,127,255,155,55⟩⟩]⟩
theorem node689 : UpperPrefix a [2,4,6,7,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,7,1,3] 30 cert689 (by decide +kernel)

def cert690 : Leaf := ⟨⟨368,356,432,356,324,4,292,108,104⟩,[],[(7,3,2),(1,4,1)],⟨7,19,76,152,50,352,193,424,300⟩,⟨7,19,76,152,50,352,193,384,260⟩,[⟨0,1763703580700529371644928,⟨446,410,492,408,446,492,508,384,420⟩⟩,⟨3,1210109875646402372160773,⟨7,19,87,242,50,371,243,499,263⟩⟩,⟨4,1229033942892698544374785,⟨487,99,492,136,34,352,225,384,420⟩⟩]⟩
theorem node690 : UpperPrefix a [2,4,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,1,8,0] 30 cert690 (by decide +kernel)

def cert691 : Local := ⟨⟨368,356,0,357,325,21,0,117,113⟩,[(2,6),(6,3)],[(7,3,2),(7,3,6),(1,4,1),(3,6,2)]⟩
theorem node691 : UpperPrefix a [2,4,6,7,1,8,3] 30 :=
  local_sound a [2,4,6,7,1,8,3] 30 cert691 (by decide +kernel)

def cert692 : Leaf := ⟨⟨48,36,177,37,5,21,277,61,57⟩,[],[(7,3,2),(1,4,1),(8,5,6)],⟨7,19,76,152,50,352,224,393,269⟩,⟨7,19,76,152,50,352,224,384,260⟩,[⟨6,1236439139534180371680517,⟨399,411,415,152,186,443,186,385,399⟩⟩,⟨3,1210110019761590447983877,⟨7,19,87,242,50,371,242,499,263⟩⟩]⟩
theorem node692 : UpperPrefix a [2,4,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,1,8,5] 30 cert692 (by decide +kernel)

theorem node693 : UpperPrefix a [2,4,6,7,1,8] 30 :=
  branch_upper a [2,4,6,7,1,8] 30 (by decide) (fin9_cases _
  node690
  (invalid_upper a [2,4,6,7,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,8,2] 30 (by decide +kernel))
  node691
  (invalid_upper a [2,4,6,7,1,8,4] 30 (by decide +kernel))
  node692
  (invalid_upper a [2,4,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,8,8] 30 (by decide +kernel)))

theorem node694 : UpperPrefix a [2,4,6,7,1] 30 :=
  branch_upper a [2,4,6,7,1] 30 (by decide) (fin9_cases _
  node688
  (invalid_upper a [2,4,6,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,2] 30 (by decide +kernel))
  node689
  (invalid_upper a [2,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,1,7] 30 (by decide +kernel))
  node693)

def cert695 : Leaf := ⟨⟨120,108,176,100,68,22,52,116,112⟩,[],[(7,3,2),(1,6,5)],⟨7,19,76,152,56,97,194,416,292⟩,⟨7,19,76,152,56,97,194,384,260⟩,[⟨8,1184203384225292091391,⟨55,55,127,255,127,127,255,255,55⟩⟩,⟨0,1437223914350366464672768,⟨78,478,76,408,444,508,206,384,260⟩⟩,⟨3,1215152803936758819456001,⟨487,499,68,144,176,481,226,384,260⟩⟩]⟩
theorem node695 : UpperPrefix a [2,4,6,7,3,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,0,1] 30 cert695 (by decide +kernel)

def cert696 : Leaf := ⟨⟨40,44,162,38,6,14,14,46,42⟩,[],[(7,3,2)],⟨7,19,76,152,56,97,224,386,262⟩,⟨7,19,76,152,56,97,224,384,260⟩,[⟨8,1184203384225292091391,⟨55,55,127,255,127,127,255,255,55⟩⟩,⟨0,1224302911315933741974528,⟨398,414,92,156,124,508,252,384,260⟩⟩,⟨4,1224302965456972626789379,⟨487,487,76,140,108,481,224,384,260⟩⟩,⟨6,1236439139534180371680517,⟨399,411,415,152,186,443,186,385,399⟩⟩]⟩
theorem node696 : UpperPrefix a [2,4,6,7,3,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,0,5] 30 cert696 (by decide +kernel)

def cert697 : Leaf := ⟨⟨72,76,131,103,71,6,0,103,99⟩,[(6,7)],[(7,3,2),(8,6,6)],⟨7,19,76,152,56,97,448,418,294⟩,⟨7,19,76,152,56,97,448,384,260⟩,[⟨4,1224305271299981842580483,⟨487,487,76,204,108,481,448,448,260⟩⟩,⟨3,1214860538335340983747585,⟨487,499,68,208,112,481,448,448,260⟩⟩,⟨5,1210109870000960995079197,⟨7,19,79,223,31,65,448,448,261⟩⟩]⟩
theorem node697 : UpperPrefix a [2,4,6,7,3,0,8] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,0,8] 30 cert697 (by decide +kernel)

theorem node698 : UpperPrefix a [2,4,6,7,3,0] 30 :=
  branch_upper a [2,4,6,7,3,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,7,3,0,0] 30 (by decide +kernel))
  node695
  (invalid_upper a [2,4,6,7,3,0,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,0,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,0,4] 30 (by decide +kernel))
  node696
  (invalid_upper a [2,4,6,7,3,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,0,7] 30 (by decide +kernel))
  node697)

def cert699 : Leaf := ⟨⟨104,108,160,100,68,13,44,108,104⟩,[],[(7,3,2),(0,6,5)],⟨7,19,76,152,56,98,193,416,292⟩,⟨7,19,76,152,56,98,193,384,260⟩,[⟨8,1184203384225292091391,⟨55,55,127,255,127,127,255,255,55⟩⟩,⟨1,1437223914350366447894529,⟨77,477,76,408,444,508,197,384,260⟩⟩,⟨4,1300893846851014685099011,⟨487,487,204,396,492,483,481,384,260⟩⟩]⟩
theorem node699 : UpperPrefix a [2,4,6,7,3,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,1,0] 30 cert699 (by decide +kernel)

def cert700 : Leaf := ⟨⟨72,76,129,69,69,13,13,77,73⟩,[],[(7,3,2)],⟨7,19,76,152,56,98,224,385,261⟩,⟨7,19,76,152,56,98,224,384,260⟩,[⟨8,1184203384225292091391,⟨55,55,127,255,127,127,255,255,55⟩⟩,⟨1,1224302911315933741973505,⟨397,413,92,156,124,508,252,384,260⟩⟩,⟨4,1224598401592528133424131,⟨487,487,76,204,236,483,224,384,260⟩⟩,⟨5,1766156994143818072732725,⟨399,411,463,411,415,463,453,384,389⟩⟩]⟩
theorem node700 : UpperPrefix a [2,4,6,7,3,1,5] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,1,5] 30 cert700 (by decide +kernel)

def cert701 : Leaf := ⟨⟨72,76,131,103,71,5,0,103,99⟩,[(6,7)],[(7,3,2),(8,6,6)],⟨7,19,76,152,56,98,448,417,293⟩,⟨7,19,76,152,56,98,448,384,260⟩,[⟨4,1224600419205161195406339,⟨487,487,76,204,236,483,448,448,260⟩⟩,⟨3,1214859961874588680324097,⟨487,499,68,208,48,226,448,448,260⟩⟩,⟨5,1210109870000960995079197,⟨7,19,79,223,31,66,448,448,261⟩⟩]⟩
theorem node701 : UpperPrefix a [2,4,6,7,3,1,8] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,1,8] 30 cert701 (by decide +kernel)

theorem node702 : UpperPrefix a [2,4,6,7,3,1] 30 :=
  branch_upper a [2,4,6,7,3,1] 30 (by decide) (fin9_cases _
  node699
  (invalid_upper a [2,4,6,7,3,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,1,4] 30 (by decide +kernel))
  node700
  (invalid_upper a [2,4,6,7,3,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,7,3,1,7] 30 (by decide +kernel))
  node701)

def cert703 : Leaf := ⟨⟨344,332,400,356,324,4,262,100,96⟩,[],[(7,3,2),(1,7,6)],⟨7,19,76,152,56,352,193,386,292⟩,⟨7,19,76,152,56,352,193,386,260⟩,[⟨0,1762652116295197727392768,⟨446,410,380,408,316,380,508,394,308⟩⟩,⟨3,1233747128859194976896001,⟨487,499,356,176,48,352,481,482,292⟩⟩,⟨4,1233747128858096539010049,⟨487,483,364,168,40,352,481,482,292⟩⟩,⟨5,1210110014116149075129375,⟨7,23,79,223,95,320,193,451,261⟩⟩]⟩
theorem node703 : UpperPrefix a [2,4,6,7,3,8,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,7,3,8,0,1] 30 cert703 (by decide +kernel)

#print axioms node703
end Delivery.FiniteExclusion.Sharp2x7
