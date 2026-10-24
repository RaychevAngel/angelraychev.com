import RegularNineSharp4x5Base
import RegularNineSharp4x5C009
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
theorem node640 : UpperPrefix a [3,4,6,5,2,8,1] 30 :=
  branch_upper a [3,4,6,5,2,8,1] 30 (by decide) (fin9_cases _
  node639
  (invalid_upper a [3,4,6,5,2,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,1,8] 30 (by decide +kernel)))

theorem node641 : UpperPrefix a [3,4,6,5,2,8] 30 :=
  branch_upper a [3,4,6,5,2,8] 30 (by decide) (fin9_cases _
  node638
  node640
  (invalid_upper a [3,4,6,5,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,8,8] 30 (by decide +kernel)))

theorem node642 : UpperPrefix a [3,4,6,5,2] 30 :=
  branch_upper a [3,4,6,5,2] 30 (by decide) (fin9_cases _
  node635
  node636
  (invalid_upper a [3,4,6,5,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,2,6] 30 (by decide +kernel))
  node637
  node641)

def cert643 : Leaf := ⟨⟨116,104,18,0,70,150,278,86,70⟩,[(3,5)],[(0,5,3)],⟨11,22,76,41,176,97,454,390,278⟩,⟨11,22,76,41,176,97,192,384,272⟩,[⟨3,1219570781057713722885121,⟨499,470,68,49,176,113,192,384,272⟩⟩,⟨8,1181748066173722881407,⟨11,63,127,47,191,127,255,129,27⟩⟩,⟨5,1219580021282997164835841,⟨463,470,76,205,144,197,192,384,272⟩⟩,⟨7,1293929570354794339509523,⟨267,287,76,45,319,109,64,257,283⟩⟩]⟩
theorem node643 : UpperPrefix a [3,4,6,5,7,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,0] 30 cert643 (by decide +kernel)

def cert644 : Leaf := ⟨⟨228,224,161,198,68,132,36,100,228⟩,[],[(1,5,3),(0,6,2)],⟨11,22,76,41,176,98,193,388,276⟩,⟨11,22,76,41,176,98,193,384,272⟩,[⟨8,1184356292524540423679,⟨47,127,127,47,255,127,255,255,127⟩⟩,⟨3,1238497122610688088345601,⟨499,438,502,113,176,498,241,384,272⟩⟩,⟨4,1212469036824938835084323,⟨47,111,76,45,237,111,205,388,460⟩⟩]⟩
theorem node644 : UpperPrefix a [3,4,6,5,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,1,0] 30 cert644 (by decide +kernel)

def cert645 : Leaf := ⟨⟨176,161,177,146,1,149,49,49,161⟩,[],[(1,5,3),(2,6,5)],⟨11,22,76,41,176,98,196,385,273⟩,⟨11,22,76,41,176,98,196,384,272⟩,[⟨8,1184356292524540423679,⟨47,127,127,47,255,127,255,255,127⟩⟩,⟨3,1252691948503800596171777,⟨435,118,502,433,176,114,246,384,272⟩⟩,⟨6,1508786869034570505784359,⟨411,415,415,441,441,443,391,384,408⟩⟩]⟩
theorem node645 : UpperPrefix a [3,4,6,5,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,1,2] 30 cert645 (by decide +kernel)

def cert646 : Leaf := ⟨⟨52,105,49,22,13,157,0,61,45⟩,[(6,7)],[(1,5,3),(8,6,6)],⟨11,22,76,41,176,98,448,389,277⟩,⟨11,22,76,41,176,98,448,384,272⟩,[⟨6,1219569592074365544956963,⟨395,415,12,57,185,443,384,384,280⟩⟩,⟨7,1293929570354794339509555,⟨267,287,76,45,319,367,321,257,283⟩⟩]⟩
theorem node646 : UpperPrefix a [3,4,6,5,7,1,8] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,1,8] 30 cert646 (by decide +kernel)

theorem node647 : UpperPrefix a [3,4,6,5,7,1] 30 :=
  branch_upper a [3,4,6,5,7,1] 30 (by decide) (fin9_cases _
  node644
  (invalid_upper a [3,4,6,5,7,1,1] 30 (by decide +kernel))
  node645
  (invalid_upper a [3,4,6,5,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,1,7] 30 (by decide +kernel))
  node646)

def cert648 : Leaf := ⟨⟨52,161,179,22,3,0,307,51,35⟩,[(5,2)],[(6,2,5)],⟨11,22,76,41,176,100,451,387,275⟩,⟨11,22,76,41,176,100,192,384,272⟩,[⟨3,1252692036249157819714561,⟨467,54,502,499,178,118,192,384,272⟩⟩,⟨8,1181748066173722881407,⟨11,63,127,47,191,127,255,129,27⟩⟩,⟨2,1214839173153706450355201,⟨475,18,88,505,176,96,192,384,272⟩⟩,⟨7,1218371706769611322033155,⟨267,319,108,41,48,100,64,256,272⟩⟩]⟩
theorem node648 : UpperPrefix a [3,4,6,5,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,2] 30 cert648 (by decide +kernel)

def cert649 : Leaf := ⟨⟨116,96,19,86,326,150,22,22,6⟩,[],[(8,5,4),(0,6,2)],⟨11,22,76,41,176,352,193,390,278⟩,⟨11,22,76,41,176,352,193,384,272⟩,[⟨3,1238497122608489065090049,⟨499,438,502,113,176,368,241,384,272⟩⟩,⟨7,1293929570354794339509523,⟨267,287,76,45,319,365,65,257,283⟩⟩,⟨5,1219580129369388221727745,⟨463,406,76,205,144,320,197,384,272⟩⟩,⟨6,1219569592072160079250433,⟨395,406,12,41,176,288,129,384,272⟩⟩]⟩
theorem node649 : UpperPrefix a [3,4,6,5,7,8,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,8,0] 30 cert649 (by decide +kernel)

def cert650 : Leaf := ⟨⟨52,32,51,86,262,22,53,54,38⟩,[],[(8,5,4)],⟨11,22,76,41,176,352,194,385,276⟩,⟨11,22,76,41,176,352,194,385,272⟩,[⟨3,1238451012512637764242433,⟨499,310,374,241,176,368,498,497,272⟩⟩,⟨7,1293929572606603296777555,⟨267,287,109,45,319,365,367,257,283⟩⟩,⟨6,1238505174864372689800197,⟨411,407,415,185,176,288,386,385,272⟩⟩,⟨0,1238441766578004905954304,⟨266,310,382,40,176,368,498,384,272⟩⟩]⟩
theorem node650 : UpperPrefix a [3,4,6,5,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,8,1,0] 30 cert650 (by decide +kernel)

def cert651 : Leaf := ⟨⟨112,96,51,82,322,18,52,123,106⟩,[],[(8,5,4),(2,7,6)],⟨11,22,76,41,176,352,194,388,273⟩,⟨11,22,76,41,176,352,194,388,273⟩,[⟨7,1293929572606603296777555,⟨267,287,109,45,319,365,367,269,283⟩⟩,⟨0,1210110172881230073236480,⟨10,86,94,40,242,368,242,502,368⟩⟩,⟨3,1210110172881228999494657,⟨3,86,86,33,242,368,242,502,369⟩⟩]⟩
theorem node651 : UpperPrefix a [3,4,6,5,7,8,1,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,8,1,2,0] 30 cert651 (by decide +kernel)

theorem node652 : UpperPrefix a [3,4,6,5,7,8,1,2] 30 :=
  branch_upper a [3,4,6,5,7,8,1,2] 30 (by decide) (fin9_cases _
  node651
  (invalid_upper a [3,4,6,5,7,8,1,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,2,8] 30 (by decide +kernel)))

theorem node653 : UpperPrefix a [3,4,6,5,7,8,1] 30 :=
  branch_upper a [3,4,6,5,7,8,1] 30 (by decide) (fin9_cases _
  node650
  (invalid_upper a [3,4,6,5,7,8,1,1] 30 (by decide +kernel))
  node652
  (invalid_upper a [3,4,6,5,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,1,8] 30 (by decide +kernel)))

def cert654 : Leaf := ⟨⟨52,33,49,84,261,149,49,54,39⟩,[],[(8,5,4)],⟨11,22,76,41,176,352,196,385,274⟩,⟨11,22,76,41,176,352,196,385,272⟩,[⟨3,1696594397893547246259201,⟨435,374,502,433,432,370,502,401,272⟩⟩,⟨1,1210110172881247307563009,⟨9,84,92,41,252,372,252,509,372⟩⟩,⟨6,1243891624136094902127621,⟨411,407,415,441,176,432,391,385,272⟩⟩,⟨7,1293929570354794339509523,⟨267,287,76,45,319,365,68,257,283⟩⟩]⟩
theorem node654 : UpperPrefix a [3,4,6,5,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,8,2,0] 30 cert654 (by decide +kernel)

def cert655 : Leaf := ⟨⟨160,161,163,194,259,131,35,49,163⟩,[],[(4,1,7),(8,5,4)],⟨11,22,76,41,176,352,196,386,273⟩,⟨11,22,76,41,176,352,196,386,272⟩,[⟨2,2244333497546048100369539,⟨411,443,376,441,441,376,505,411,280⟩⟩,⟨3,1252950241177377545686017,⟨499,246,502,433,176,498,246,498,272⟩⟩,⟨6,1281596769022757225630725,⟨411,407,415,441,176,432,391,386,272⟩⟩]⟩
theorem node655 : UpperPrefix a [3,4,6,5,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,5,7,8,2,1] 30 cert655 (by decide +kernel)

theorem node656 : UpperPrefix a [3,4,6,5,7,8,2] 30 :=
  branch_upper a [3,4,6,5,7,8,2] 30 (by decide) (fin9_cases _
  node654
  node655
  (invalid_upper a [3,4,6,5,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,2,8] 30 (by decide +kernel)))

theorem node657 : UpperPrefix a [3,4,6,5,7,8] 30 :=
  branch_upper a [3,4,6,5,7,8] 30 (by decide) (fin9_cases _
  node649
  node653
  node656
  (invalid_upper a [3,4,6,5,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,8,8] 30 (by decide +kernel)))

theorem node658 : UpperPrefix a [3,4,6,5,7] 30 :=
  branch_upper a [3,4,6,5,7] 30 (by decide) (fin9_cases _
  node643
  node647
  node648
  (invalid_upper a [3,4,6,5,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,7,7] 30 (by decide +kernel))
  node657)

def cert659 : Leaf := ⟨⟨116,104,18,0,198,406,278,86,198⟩,[(3,5)],[(0,5,3)],⟨11,22,76,41,304,97,198,390,406⟩,⟨11,22,76,41,304,97,192,384,272⟩,[⟨3,1219570781057713722885121,⟨499,470,68,49,304,113,192,384,272⟩⟩,⟨5,1219580021282997164835841,⟨463,470,76,205,272,197,192,384,272⟩⟩,⟨7,1208926973663140725662995,⟨11,31,76,45,319,109,64,257,283⟩⟩,⟨8,1181745669228962260243,⟨11,31,76,45,63,109,192,129,27⟩⟩]⟩
theorem node659 : UpperPrefix a [3,4,6,5,8,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,0] 30 cert659 (by decide +kernel)

def cert660 : Leaf := ⟨⟨420,480,417,390,132,388,292,36,164⟩,[],[(1,5,3),(0,6,2)],⟨11,22,76,41,304,98,193,388,404⟩,⟨11,22,76,41,304,98,193,384,272⟩,[⟨3,1238497122606290041834497,⟨499,438,502,113,304,498,241,384,272⟩⟩,⟨4,1212616646841518492746787,⟨111,239,76,45,493,111,237,388,460⟩⟩,⟨6,1219569592074365544956963,⟨395,415,12,57,313,443,129,384,280⟩⟩]⟩
theorem node660 : UpperPrefix a [3,4,6,5,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,1,0] 30 cert660 (by decide +kernel)

def cert661 : Leaf := ⟨⟨416,417,417,386,129,389,289,33,161⟩,[],[(1,5,3),(2,6,5)],⟨11,22,76,41,304,98,196,385,401⟩,⟨11,22,76,41,304,98,196,384,272⟩,[⟨3,1252691948499402549660673,⟨435,118,502,433,304,98,246,384,272⟩⟩,⟨4,1210262381129102704509987,⟨111,239,76,45,493,111,196,452,460⟩⟩,⟨6,1508786869034570505784359,⟨411,415,415,441,441,443,391,384,408⟩⟩]⟩
theorem node661 : UpperPrefix a [3,4,6,5,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,1,2] 30 cert661 (by decide +kernel)

theorem node662 : UpperPrefix a [3,4,6,5,8,1] 30 :=
  branch_upper a [3,4,6,5,8,1] 30 (by decide) (fin9_cases _
  node660
  (invalid_upper a [3,4,6,5,8,1,1] 30 (by decide +kernel))
  node661
  (invalid_upper a [3,4,6,5,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,1,8] 30 (by decide +kernel)))

def cert663 : Leaf := ⟨⟨36,417,435,6,131,0,307,51,163⟩,[(5,2)],[(6,2,5)],⟨11,22,76,41,304,100,195,387,403⟩,⟨11,22,76,41,304,100,192,384,272⟩,[⟨3,1252692036249157819714561,⟨467,54,502,499,306,118,192,384,272⟩⟩,⟨2,1214839173153706450355201,⟨475,18,88,505,304,96,192,384,272⟩⟩,⟨4,1210107565423489931281411,⟨11,47,108,41,288,100,192,384,256⟩⟩,⟨7,1208926973803872031605763,⟨11,63,108,41,304,100,64,256,272⟩⟩,⟨8,1181745809960268203011,⟨11,63,108,41,48,100,192,128,16⟩⟩]⟩
theorem node663 : UpperPrefix a [3,4,6,5,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,2] 30 cert663 (by decide +kernel)

def cert664 : Leaf := ⟨⟨116,96,51,86,70,0,54,118,102⟩,[(5,6)],[(7,5,5),(0,6,2)],⟨11,22,76,41,304,224,193,390,278⟩,⟨11,22,76,41,304,224,193,384,272⟩,[⟨3,1238497124855890832264193,⟨499,438,502,113,304,224,241,384,272⟩⟩,⟨8,1184634728415746991507,⟨15,31,108,109,127,237,237,239,31⟩⟩]⟩
theorem node664 : UpperPrefix a [3,4,6,5,8,7,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,7,0] 30 cert664 (by decide +kernel)

def cert665 : Leaf := ⟨⟨116,97,19,86,71,0,277,86,71⟩,[(5,6)],[(7,5,5)],⟨11,22,76,41,304,224,194,385,276⟩,⟨11,22,76,41,304,224,194,385,272⟩,[⟨3,1238451012653100374690817,⟨499,278,374,241,304,240,498,497,272⟩⟩,⟨5,1219561538510126436320257,⟨463,278,76,205,272,192,450,453,272⟩⟩,⟨8,1181747921037919528275,⟨11,31,109,45,63,237,239,129,27⟩⟩]⟩
theorem node665 : UpperPrefix a [3,4,6,5,8,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,7,1,0] 30 cert665 (by decide +kernel)

def cert666 : Leaf := ⟨⟨352,353,291,322,67,0,293,99,99⟩,[(5,6)],[(7,5,5),(2,7,6)],⟨11,22,76,41,304,224,194,388,273⟩,⟨11,22,76,41,304,224,194,388,272⟩,[⟨3,1252648754484172532288513,⟨371,246,502,369,368,242,242,502,272⟩⟩,⟨4,1210255177586321278108739,⟨111,239,109,45,428,237,239,396,384⟩⟩]⟩
theorem node666 : UpperPrefix a [3,4,6,5,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,7,1,2] 30 cert666 (by decide +kernel)

theorem node667 : UpperPrefix a [3,4,6,5,8,7,1] 30 :=
  branch_upper a [3,4,6,5,8,7,1] 30 (by decide) (fin9_cases _
  node665
  (invalid_upper a [3,4,6,5,8,7,1,1] 30 (by decide +kernel))
  node666
  (invalid_upper a [3,4,6,5,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,1,8] 30 (by decide +kernel)))

def cert668 : Leaf := ⟨⟨52,33,51,86,7,0,59,55,39⟩,[(5,6)],[(7,5,5)],⟨11,22,76,41,304,224,196,387,275⟩,⟨11,22,76,41,304,224,196,384,272⟩,[⟨6,1243817837157601040665605,⟨411,407,415,441,304,160,391,384,272⟩⟩,⟨8,1184634728415746991507,⟨15,31,108,109,127,237,237,239,31⟩⟩,⟨3,1214839157391106681867265,⟨403,22,118,433,304,224,230,384,272⟩⟩]⟩
theorem node668 : UpperPrefix a [3,4,6,5,8,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,5,8,7,2] 30 cert668 (by decide +kernel)

theorem node669 : UpperPrefix a [3,4,6,5,8,7] 30 :=
  branch_upper a [3,4,6,5,8,7] 30 (by decide) (fin9_cases _
  node664
  node667
  node668
  (invalid_upper a [3,4,6,5,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,7,8] 30 (by decide +kernel)))

theorem node670 : UpperPrefix a [3,4,6,5,8] 30 :=
  branch_upper a [3,4,6,5,8] 30 (by decide) (fin9_cases _
  node659
  node662
  node663
  (invalid_upper a [3,4,6,5,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,8,6] 30 (by decide +kernel))
  node669
  (invalid_upper a [3,4,6,5,8,8] 30 (by decide +kernel)))

theorem node671 : UpperPrefix a [3,4,6,5] 30 :=
  branch_upper a [3,4,6,5] 30 (by decide) (fin9_cases _
  node627
  node634
  node642
  (invalid_upper a [3,4,6,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,5,6] 30 (by decide +kernel))
  node658
  node670)

def cert672 : Leaf := ⟨⟨116,96,176,116,70,20,308,116,100⟩,[],[(7,3,2),(1,5,4)],⟨11,22,76,137,49,98,484,420,308⟩,⟨11,22,76,137,49,98,192,384,272⟩,[⟨0,1295285757993479547659264,⟨494,502,76,236,502,482,192,416,498⟩⟩,⟨3,1238497212746589749120001,⟨499,502,502,177,49,482,192,384,272⟩⟩,⟨8,1181748068777815239781,⟨27,55,127,137,55,127,255,128,18⟩⟩]⟩
theorem node672 : UpperPrefix a [3,4,6,7,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,1] 30 cert672 (by decide +kernel)

def cert673 : Leaf := ⟨⟨52,40,178,54,6,0,310,54,38⟩,[(5,2)],[(6,2,5),(7,3,2)],⟨11,22,76,137,49,100,482,418,306⟩,⟨11,22,76,137,49,100,192,384,272⟩,[⟨0,1297651544335946007979008,⟨494,502,108,236,502,100,192,448,498⟩⟩,⟨8,1181748068777815239781,⟨27,55,127,137,55,127,255,128,18⟩⟩,⟨3,1224302389102940592800769,⟨499,502,100,465,497,100,192,384,272⟩⟩]⟩
theorem node673 : UpperPrefix a [3,4,6,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,2] 30 cert673 (by decide +kernel)

def cert674 : Leaf := ⟨⟨100,96,162,102,70,22,308,102,102⟩,[],[(7,3,2)],⟨11,22,76,137,49,352,194,420,308⟩,⟨11,22,76,137,49,352,194,384,272⟩,[⟨0,1295290376434897416102912,⟨494,502,108,236,502,352,482,480,498⟩⟩,⟨3,1238497233012788072287233,⟨499,502,502,241,113,352,482,384,272⟩⟩,⟨8,1181745671430149792865,⟨11,22,77,137,55,127,207,128,18⟩⟩,⟨4,1210402713187946584867907,⟨11,15,77,137,173,493,207,384,264⟩⟩]⟩
theorem node674 : UpperPrefix a [3,4,6,7,0,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,1] 30 cert674 (by decide +kernel)

def cert675 : Leaf := ⟨⟨372,64,128,374,326,22,0,118,102⟩,[],[(7,3,2)],⟨11,22,76,137,49,352,196,418,306⟩,⟨11,22,76,137,49,352,196,384,272⟩,[⟨0,1297647085350102446121984,⟨494,502,76,236,502,480,196,416,498⟩⟩,⟨3,1243819100663654768446465,⟨499,502,502,433,433,480,486,384,272⟩⟩,⟨5,1210107708273139857499137,⟨79,22,76,205,23,320,196,384,274⟩⟩,⟨8,1181889784410589635585,⟨79,22,76,205,55,96,196,128,18⟩⟩,⟨1,1210107709399039764332545,⟨77,20,76,205,53,352,196,384,272⟩⟩,⟨4,1210107709397940252705793,⟨79,6,76,205,37,352,196,384,256⟩⟩]⟩
theorem node675 : UpperPrefix a [3,4,6,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,2] 30 cert675 (by decide +kernel)

def cert676 : Leaf := ⟨⟨84,64,146,86,70,22,278,86,70⟩,[],[(7,3,2),(8,5,6)],⟨11,22,76,137,49,352,224,390,278⟩,⟨11,22,76,137,49,352,224,384,272⟩,[⟨0,1295292824141294891967488,⟨494,502,76,236,502,352,224,480,498⟩⟩,⟨3,1238499685222785175522305,⟨499,502,502,241,113,352,224,480,272⟩⟩,⟨5,1295276181546322894005523,⟨395,415,76,137,415,333,204,393,411⟩⟩]⟩
theorem node676 : UpperPrefix a [3,4,6,7,0,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,0,8,5] 30 cert676 (by decide +kernel)

theorem node677 : UpperPrefix a [3,4,6,7,0,8] 30 :=
  branch_upper a [3,4,6,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,8,0] 30 (by decide +kernel))
  node674
  node675
  (invalid_upper a [3,4,6,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,4] 30 (by decide +kernel))
  node676
  (invalid_upper a [3,4,6,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,8,8] 30 (by decide +kernel)))

theorem node678 : UpperPrefix a [3,4,6,7,0] 30 :=
  branch_upper a [3,4,6,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,0,0] 30 (by decide +kernel))
  node672
  node673
  (invalid_upper a [3,4,6,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,0,7] 30 (by decide +kernel))
  node677)

def cert679 : Leaf := ⟨⟨116,104,176,118,68,20,48,116,100⟩,[],[(7,3,2)],⟨11,22,76,137,50,97,196,416,304⟩,⟨11,22,76,137,50,97,196,384,272⟩,[⟨8,1184202856665865125613,⟨127,55,127,255,55,127,255,255,18⟩⟩,⟨0,1437224634926300109489152,⟨78,470,76,204,498,502,196,384,400⟩⟩,⟨1,1285813183423000131928065,⟨109,468,108,237,496,101,196,384,400⟩⟩,⟨3,1479808295135165260235777,⟨499,470,452,433,498,497,196,384,400⟩⟩]⟩
theorem node679 : UpperPrefix a [3,4,6,7,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,0,2] 30 cert679 (by decide +kernel)

def cert680 : Leaf := ⟨⟨84,65,145,84,69,20,21,85,69⟩,[],[(7,3,2)],⟨11,22,76,137,50,97,224,388,276⟩,⟨11,22,76,137,50,97,224,384,272⟩,[⟨8,1184202856665865125613,⟨127,55,127,255,55,127,255,255,18⟩⟩,⟨1,1297647616423019213488129,⟨493,468,108,237,508,237,236,384,468⟩⟩,⟨3,1238497627147849333476353,⟨499,470,502,241,498,113,224,384,336⟩⟩,⟨5,1295276181546322894005523,⟨395,415,76,137,415,77,204,393,411⟩⟩]⟩
theorem node680 : UpperPrefix a [3,4,6,7,1,0,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,0,5] 30 cert680 (by decide +kernel)

def cert681 : Leaf := ⟨⟨100,97,163,102,69,6,0,103,103⟩,[(6,7)],[(7,3,2),(8,6,6)],⟨11,22,76,137,50,97,448,420,308⟩,⟨11,22,76,137,50,97,448,384,272⟩,[⟨3,1229036338949879829105665,⟨115,470,502,241,114,113,448,448,272⟩⟩,⟨4,1213065971152286357914641,⟨47,7,236,237,47,237,492,492,493⟩⟩]⟩
theorem node681 : UpperPrefix a [3,4,6,7,1,0,8] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,0,8] 30 cert681 (by decide +kernel)

theorem node682 : UpperPrefix a [3,4,6,7,1,0] 30 :=
  branch_upper a [3,4,6,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,0,1] 30 (by decide +kernel))
  node679
  (invalid_upper a [3,4,6,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,0,4] 30 (by decide +kernel))
  node680
  (invalid_upper a [3,4,6,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,0,7] 30 (by decide +kernel))
  node681)

def cert683 : Leaf := ⟨⟨48,40,179,50,12,0,315,59,43⟩,[(5,2)],[(6,2,5),(7,3,2),(2,5,4)],⟨11,22,76,137,50,100,481,417,305⟩,⟨11,22,76,137,50,100,192,384,272⟩,[⟨8,1181748068777815239781,⟨27,55,127,137,55,127,255,128,18⟩⟩,⟨0,1210107565427200514608128,⟨26,54,126,136,50,118,192,384,272⟩⟩]⟩
theorem node683 : UpperPrefix a [3,4,6,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,2] 30 cert683 (by decide +kernel)

def cert684 : Leaf := ⟨⟨372,352,435,0,324,22,0,118,102⟩,[(3,6),(6,3)],[(7,3,2),(0,6,2)],⟨11,22,76,137,50,352,193,420,308⟩,⟨11,22,76,137,50,352,193,384,272⟩,[⟨3,1238497266719279094434817,⟨499,438,502,241,434,352,241,384,272⟩⟩]⟩
theorem node684 : UpperPrefix a [3,4,6,7,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,0] 30 cert684 (by decide +kernel)

def cert685 : Leaf := ⟨⟨340,320,402,0,324,22,274,86,102⟩,[(3,7)],[(7,3,2),(0,7,3)],⟨11,22,76,137,50,352,196,385,304⟩,⟨11,22,76,137,50,352,196,385,272⟩,[⟨3,1772152261621248276073473,⟨435,374,502,401,306,370,502,401,272⟩⟩,⟨5,1212771821639976831821235,⟨79,95,76,205,223,463,205,463,479⟩⟩]⟩
theorem node685 : UpperPrefix a [3,4,6,7,1,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,2,0] 30 cert685 (by decide +kernel)

def cert686 : Leaf := ⟨⟨100,97,163,102,69,7,35,0,103⟩,[(7,5)],[(7,3,2),(8,5,7)],⟨11,22,76,137,50,352,196,416,273⟩,⟨11,22,76,137,50,352,196,416,272⟩,[⟨3,1253024023640726907685889,⟨499,246,502,433,242,498,246,432,272⟩⟩,⟨4,1212771836275546027459603,⟨79,79,76,237,239,492,228,492,493⟩⟩]⟩
theorem node686 : UpperPrefix a [3,4,6,7,1,8,2,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,2,5] 30 cert686 (by decide +kernel)

theorem node687 : UpperPrefix a [3,4,6,7,1,8,2] 30 :=
  branch_upper a [3,4,6,7,1,8,2] 30 (by decide) (fin9_cases _
  node685
  (invalid_upper a [3,4,6,7,1,8,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,2,4] 30 (by decide +kernel))
  node686
  (invalid_upper a [3,4,6,7,1,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,2,8] 30 (by decide +kernel)))

def cert688 : Leaf := ⟨⟨20,72,144,22,76,28,284,31,15⟩,[],[(7,3,2),(8,5,6)],⟨11,22,76,137,50,352,224,389,277⟩,⟨11,22,76,137,50,352,224,384,272⟩,[⟨5,1295571329451506541798675,⟨395,415,76,137,415,461,204,393,411⟩⟩,⟨0,1210110019746198361218560,⟨94,22,94,254,50,352,224,480,272⟩⟩,⟨6,1219569592072162629387283,⟨395,415,12,137,443,288,160,384,281⟩⟩,⟨1,1210110019745648605396993,⟨77,20,76,237,48,352,224,480,272⟩⟩]⟩
theorem node688 : UpperPrefix a [3,4,6,7,1,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,1,8,5] 30 cert688 (by decide +kernel)

theorem node689 : UpperPrefix a [3,4,6,7,1,8] 30 :=
  branch_upper a [3,4,6,7,1,8] 30 (by decide) (fin9_cases _
  node684
  (invalid_upper a [3,4,6,7,1,8,1] 30 (by decide +kernel))
  node687
  (invalid_upper a [3,4,6,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,4] 30 (by decide +kernel))
  node688
  (invalid_upper a [3,4,6,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,8,8] 30 (by decide +kernel)))

theorem node690 : UpperPrefix a [3,4,6,7,1] 30 :=
  branch_upper a [3,4,6,7,1] 30 (by decide) (fin9_cases _
  node682
  (invalid_upper a [3,4,6,7,1,1] 30 (by decide +kernel))
  node683
  (invalid_upper a [3,4,6,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,1,7] 30 (by decide +kernel))
  node689)

def cert691 : Leaf := ⟨⟨48,0,179,50,75,26,314,58,42⟩,[(1,4)],[(6,2,4),(7,3,2),(2,4,1)],⟨11,22,76,137,52,97,482,418,306⟩,⟨11,22,76,137,52,97,192,384,272⟩,[⟨8,1181748068777815239781,⟨27,55,127,137,55,127,255,128,18⟩⟩,⟨0,1285813291192731837670400,⟨10,470,76,136,502,96,192,384,466⟩⟩]⟩
theorem node691 : UpperPrefix a [3,4,6,7,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,0] 30 cert691 (by decide +kernel)

def cert692 : Leaf := ⟨⟨48,0,179,50,67,17,307,51,35⟩,[(1,4)],[(6,2,4),(7,3,2),(2,4,1)],⟨11,22,76,137,52,98,481,417,305⟩,⟨11,22,76,137,52,98,192,384,272⟩,[⟨3,1214913104420972713225217,⟨499,54,246,481,54,114,192,384,274⟩⟩,⟨8,1181748068777815239781,⟨27,55,127,137,55,127,255,128,18⟩⟩]⟩
theorem node692 : UpperPrefix a [3,4,6,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,1] 30 cert692 (by decide +kernel)

def cert693 : Local := ⟨⟨304,0,435,0,330,26,0,58,42⟩,[(1,4),(3,6),(6,3)],[(6,2,4),(7,3,2),(2,4,1),(0,6,2)]⟩
theorem node693 : UpperPrefix a [3,4,6,7,2,8,0] 30 :=
  local_sound a [3,4,6,7,2,8,0] 30 cert693 (by decide +kernel)

def cert694 : Leaf := ⟨⟨32,0,163,34,75,27,313,43,43⟩,[(1,4)],[(6,2,4),(7,3,2),(2,4,1)],⟨11,22,76,137,52,352,194,417,305⟩,⟨11,22,76,137,52,352,194,384,272⟩,[⟨4,1210402713187944437384257,⟨11,6,77,137,172,493,207,384,256⟩⟩,⟨8,1181745671430149792865,⟨11,22,77,137,55,127,207,128,18⟩⟩]⟩
theorem node694 : UpperPrefix a [3,4,6,7,2,8,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,8,1] 30 cert694 (by decide +kernel)

def cert695 : Leaf := ⟨⟨16,0,147,18,75,27,283,27,11⟩,[(1,4)],[(6,2,4),(7,3,2),(2,4,1),(8,5,6)],⟨11,22,76,137,52,352,224,387,275⟩,⟨11,22,76,137,52,352,224,384,272⟩,[⟨5,1297646588159798866355475,⟨395,415,76,137,415,461,204,393,411⟩⟩]⟩
theorem node695 : UpperPrefix a [3,4,6,7,2,8,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,2,8,5] 30 cert695 (by decide +kernel)

theorem node696 : UpperPrefix a [3,4,6,7,2,8] 30 :=
  branch_upper a [3,4,6,7,2,8] 30 (by decide) (fin9_cases _
  node693
  node694
  (invalid_upper a [3,4,6,7,2,8,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,4] 30 (by decide +kernel))
  node695
  (invalid_upper a [3,4,6,7,2,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,8,8] 30 (by decide +kernel)))

theorem node697 : UpperPrefix a [3,4,6,7,2] 30 :=
  branch_upper a [3,4,6,7,2] 30 (by decide) (fin9_cases _
  node691
  node692
  (invalid_upper a [3,4,6,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,2,7] 30 (by decide +kernel))
  node696)

def cert698 : Leaf := ⟨⟨64,73,129,64,77,10,301,109,109⟩,[],[(7,3,2),(1,6,5)],⟨11,22,76,137,304,97,194,420,308⟩,⟨11,22,76,137,304,97,194,384,272⟩,[⟨4,1210255177762238172496963,⟨111,239,109,173,420,109,239,384,384⟩⟩,⟨8,1181748061768428561473,⟨11,54,109,137,54,109,239,128,18⟩⟩,⟨5,1210107564157960394384449,⟨11,22,77,137,278,77,207,384,274⟩⟩,⟨2,1210107567676397577045057,⟨11,50,105,137,304,105,235,384,272⟩⟩]⟩
theorem node698 : UpperPrefix a [3,4,6,7,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,1] 30 cert698 (by decide +kernel)

def cert699 : Leaf := ⟨⟨352,360,416,354,72,264,296,120,104⟩,[],[(4,1,7),(7,3,2),(1,7,3)],⟨11,22,76,137,304,97,196,386,304⟩,⟨11,22,76,137,304,97,196,386,272⟩,[⟨0,1437243099684772328522752,⟨206,470,76,204,498,502,196,450,400⟩⟩,⟨2,1757920526299502173226115,⟨139,411,376,137,304,377,505,395,272⟩⟩]⟩
theorem node699 : UpperPrefix a [3,4,6,7,8,0,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,2,1] 30 cert699 (by decide +kernel)

def cert700 : Leaf := ⟨⟨356,360,418,358,0,270,298,0,110⟩,[(4,7),(7,4)],[(7,3,2)],⟨11,22,76,137,304,97,196,416,274⟩,⟨11,22,76,137,304,97,196,416,272⟩,[⟨4,1210255319766355310019587,⟨111,239,108,237,416,101,196,416,384⟩⟩,⟨0,2391142664474764535714816,⟨334,470,334,478,498,502,470,498,400⟩⟩]⟩
theorem node700 : UpperPrefix a [3,4,6,7,8,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,2,5] 30 cert700 (by decide +kernel)

theorem node701 : UpperPrefix a [3,4,6,7,8,0,2] 30 :=
  branch_upper a [3,4,6,7,8,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,8,0,2,0] 30 (by decide +kernel))
  node699
  (invalid_upper a [3,4,6,7,8,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,2,4] 30 (by decide +kernel))
  node700
  (invalid_upper a [3,4,6,7,8,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,2,8] 30 (by decide +kernel)))

def cert702 : Leaf := ⟨⟨276,321,385,278,71,260,261,23,7⟩,[],[(7,3,2)],⟨11,22,76,137,304,97,224,390,278⟩,⟨11,22,76,137,304,97,224,384,272⟩,[⟨3,1238497338917473181764609,⟨499,470,502,241,304,113,224,384,272⟩⟩,⟨5,1295276181546322894005523,⟨395,415,76,137,415,77,204,393,411⟩⟩,⟨6,1219569592072160481903619,⟨395,415,12,137,304,41,160,384,272⟩⟩,⟨1,1210107709715699113132033,⟨109,20,108,237,304,101,224,384,272⟩⟩,⟨4,1210107709714599601505281,⟨111,6,108,237,288,101,224,384,256⟩⟩]⟩
theorem node702 : UpperPrefix a [3,4,6,7,8,0,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,0,5] 30 cert702 (by decide +kernel)

theorem node703 : UpperPrefix a [3,4,6,7,8,0] 30 :=
  branch_upper a [3,4,6,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,7,8,0,0] 30 (by decide +kernel))
  node698
  node701
  (invalid_upper a [3,4,6,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,4] 30 (by decide +kernel))
  node702
  (invalid_upper a [3,4,6,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,0,8] 30 (by decide +kernel)))

#print axioms node703
end Delivery.FiniteExclusion.Sharp4x5
