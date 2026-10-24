import RegularNineSharp4x5Base
import RegularNineSharp4x5C000
import RegularNineSharp4x5C007
import RegularNineSharp4x5C010
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp4x5
open Bounds BoundTreeRows Extremal
def cert704 : Leaf := ⟨⟨372,352,435,0,70,276,0,118,102⟩,[(3,6),(6,3)],[(7,3,2),(0,6,2)],⟨11,22,76,137,304,98,193,420,308⟩,⟨11,22,76,137,304,98,193,384,272⟩,[⟨3,1238497266721478117690369,⟨499,438,502,241,304,498,241,384,272⟩⟩]⟩
theorem node704 : UpperPrefix a [3,4,6,7,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,0] 30 cert704 (by decide +kernel)

def cert705 : Leaf := ⟨⟨288,361,162,290,11,12,42,43,43⟩,[],[(7,3,2),(2,6,5)],⟨11,22,76,137,304,98,196,417,305⟩,⟨11,22,76,137,304,98,196,384,272⟩,[⟨4,1210262525244286353277987,⟨111,239,76,237,493,111,196,452,460⟩⟩,⟨6,1437222725400064812909603,⟨11,415,12,137,441,443,132,384,408⟩⟩,⟨0,1210107709434224136422400,⟨110,22,76,236,304,98,196,384,272⟩⟩,⟨8,1181889819594961716225,⟨111,22,76,237,48,98,196,128,16⟩⟩]⟩
theorem node705 : UpperPrefix a [3,4,6,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,2] 30 cert705 (by decide +kernel)

def cert706 : Leaf := ⟨⟨4,73,131,6,15,13,15,15,15⟩,[],[(7,3,2)],⟨11,22,76,137,304,98,224,389,277⟩,⟨11,22,76,137,304,98,224,384,272⟩,[⟨4,1210255607715267318907939,⟨111,239,76,237,493,111,237,388,460⟩⟩,⟨5,1295571329451515131733299,⟨395,415,76,137,415,463,205,393,411⟩⟩,⟨8,1181889819603576824865,⟨111,22,76,237,55,111,237,128,18⟩⟩,⟨6,1219569592074372390061091,⟨395,415,12,137,313,443,185,384,272⟩⟩]⟩
theorem node706 : UpperPrefix a [3,4,6,7,8,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,1,5] 30 cert706 (by decide +kernel)

theorem node707 : UpperPrefix a [3,4,6,7,8,1] 30 :=
  branch_upper a [3,4,6,7,8,1] 30 (by decide) (fin9_cases _
  node704
  (invalid_upper a [3,4,6,7,8,1,1] 30 (by decide +kernel))
  node705
  (invalid_upper a [3,4,6,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,4] 30 (by decide +kernel))
  node706
  (invalid_upper a [3,4,6,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,1,8] 30 (by decide +kernel)))

def cert708 : Local := ⟨⟨308,296,435,0,14,0,0,62,46⟩,[(3,6),(5,2),(6,3)],[(6,2,5),(7,3,2),(0,6,2)]⟩
theorem node708 : UpperPrefix a [3,4,6,7,8,2,0] 30 :=
  local_sound a [3,4,6,7,8,2,0] 30 cert708 (by decide +kernel)

def cert709 : Leaf := ⟨⟨16,9,147,18,11,0,317,59,43⟩,[(5,2)],[(6,2,5),(7,3,2)],⟨11,22,76,137,304,100,194,417,305⟩,⟨11,22,76,137,304,100,194,384,272⟩,[⟨2,1361518440643071592891457,⟨11,18,73,137,440,505,203,384,272⟩⟩,⟨5,1210107564157960394384449,⟨11,22,77,137,278,77,207,384,274⟩⟩,⟨8,1181748061768428561473,⟨11,54,109,137,54,109,239,128,18⟩⟩]⟩
theorem node709 : UpperPrefix a [3,4,6,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,1] 30 cert709 (by decide +kernel)

def cert710 : Leaf := ⟨⟨272,297,434,274,15,0,286,27,11⟩,[(5,2)],[(6,2,5),(7,3,2)],⟨11,22,76,137,304,100,224,387,275⟩,⟨11,22,76,137,304,100,224,384,272⟩,[⟨2,1219579968365701942477827,⟨395,411,72,137,304,96,224,384,272⟩⟩,⟨5,1219579967239802036683779,⟨395,415,76,137,272,68,192,384,272⟩⟩,⟨0,1210107709856436601488384,⟨110,54,108,236,304,100,224,384,272⟩⟩]⟩
theorem node710 : UpperPrefix a [3,4,6,7,8,2,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,5] 30 cert710 (by decide +kernel)

theorem node711 : UpperPrefix a [3,4,6,7,8,2] 30 :=
  branch_upper a [3,4,6,7,8,2] 30 (by decide) (fin9_cases _
  node708
  node709
  (invalid_upper a [3,4,6,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,4] 30 (by decide +kernel))
  node710
  (invalid_upper a [3,4,6,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,8] 30 (by decide +kernel)))

theorem node712 : UpperPrefix a [3,4,6,7,8] 30 :=
  branch_upper a [3,4,6,7,8] 30 (by decide) (fin9_cases _
  node703
  node707
  node711
  (invalid_upper a [3,4,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,8] 30 (by decide +kernel)))

theorem node713 : UpperPrefix a [3,4,6,7] 30 :=
  branch_upper a [3,4,6,7] 30 (by decide) (fin9_cases _
  node678
  node690
  node697
  (invalid_upper a [3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,7] 30 (by decide +kernel))
  node712)

def cert714 : Leaf := ⟨⟨116,96,416,244,70,4,292,100,228⟩,[],[(1,5,4)],⟨11,22,76,265,49,98,228,420,436⟩,⟨11,22,76,265,49,98,192,384,272⟩,[⟨0,1295359689084962461721600,⟨494,502,204,492,502,482,192,416,498⟩⟩,⟨3,1238497212746589749120001,⟨499,502,502,305,49,482,192,384,272⟩⟩,⟨4,1210181514423817972483073,⟨239,6,204,493,101,98,192,384,256⟩⟩,⟨7,1208926973804284080032773,⟨27,55,127,265,49,114,64,256,272⟩⟩,⟨8,1181745810372316630021,⟨27,55,127,9,49,114,192,128,16⟩⟩]⟩
theorem node714 : UpperPrefix a [3,4,6,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,1] 30 cert714 (by decide +kernel)

def cert715 : Leaf := ⟨⟨52,40,434,182,6,0,310,54,166⟩,[(5,2)],[(6,2,5)],⟨11,22,76,265,49,100,226,418,434⟩,⟨11,22,76,265,49,100,192,384,272⟩,[⟨0,1297651544335946007979008,⟨494,502,108,492,502,100,192,448,498⟩⟩,⟨3,1224302389102940592800769,⟨499,502,100,465,497,100,192,384,272⟩⟩,⟨7,1208926973806483103304709,⟨27,55,127,265,51,119,64,256,272⟩⟩,⟨8,1181745812571339901957,⟨27,55,127,9,51,119,192,128,16⟩⟩]⟩
theorem node715 : UpperPrefix a [3,4,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,2] 30 cert715 (by decide +kernel)

def cert716 : Leaf := ⟨⟨84,64,274,86,70,0,310,118,102⟩,[(5,6)],[(7,5,5)],⟨11,22,76,265,49,224,230,422,310⟩,⟨11,22,76,265,49,224,192,384,272⟩,[⟨0,1295285760526754338055168,⟨494,502,108,492,502,224,224,416,498⟩⟩,⟨3,1238497214998389562805249,⟨499,502,502,305,49,224,224,384,272⟩⟩,⟨5,1210107564158003344057601,⟨11,22,76,265,23,204,204,393,283⟩⟩,⟨8,1181747921297203006469,⟨11,23,127,9,49,224,224,128,16⟩⟩]⟩
theorem node716 : UpperPrefix a [3,4,6,8,0,7] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,7] 30 cert716 (by decide +kernel)

theorem node717 : UpperPrefix a [3,4,6,8,0] 30 :=
  branch_upper a [3,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,0,0] 30 (by decide +kernel))
  node714
  node715
  (invalid_upper a [3,4,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,6] 30 (by decide +kernel))
  node716
  (invalid_upper a [3,4,6,8,0,8] 30 (by decide +kernel)))

def cert718 : Leaf := ⟨⟨432,488,416,178,452,388,288,32,160⟩,[],[],⟨11,22,76,265,50,97,196,416,432⟩,⟨11,22,76,265,50,97,196,384,272⟩,[⟨0,1437224490811112031536128,⟨78,470,76,268,498,502,196,384,400⟩⟩,⟨1,1285887060471287517544449,⟨237,468,236,493,496,101,196,384,400⟩⟩,⟨3,1479808295135165260235777,⟨499,470,452,433,498,497,196,384,400⟩⟩,⟨2,1285813002962392460559379,⟨11,411,72,265,443,97,192,392,409⟩⟩,⟨4,1210181586762886987121665,⟨239,70,236,493,34,101,196,384,256⟩⟩,⟨6,1285811850040887854760979,⟨11,415,12,265,443,33,132,392,409⟩⟩]⟩
theorem node718 : UpperPrefix a [3,4,6,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,0,2] 30 cert718 (by decide +kernel)

def cert719 : Leaf := ⟨⟨404,449,385,148,453,388,261,5,133⟩,[],[],⟨11,22,76,265,50,97,224,388,404⟩,⟨11,22,76,265,50,97,224,384,272⟩,[⟨1,1295360292215468951076865,⟨493,468,236,493,500,237,228,384,464⟩⟩,⟨3,1238497483032661257620481,⟨499,470,502,369,498,113,224,384,336⟩⟩,⟨5,1295276181546322894005523,⟨395,415,76,265,415,77,204,393,411⟩⟩,⟨4,1210181586762886987121665,⟨239,70,236,493,34,101,224,384,256⟩⟩,⟨6,1219569592072196989125651,⟨395,415,12,265,443,41,160,392,281⟩⟩]⟩
theorem node719 : UpperPrefix a [3,4,6,8,1,0,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,0,5] 30 cert719 (by decide +kernel)

theorem node720 : UpperPrefix a [3,4,6,8,1,0] 30 :=
  branch_upper a [3,4,6,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,0,1] 30 (by decide +kernel))
  node718
  (invalid_upper a [3,4,6,8,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,0,4] 30 (by decide +kernel))
  node719
  (invalid_upper a [3,4,6,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,0,8] 30 (by decide +kernel)))

def cert721 : Leaf := ⟨⟨48,41,417,178,13,0,297,41,171⟩,[(5,2)],[(6,2,5),(2,5,4)],⟨11,22,76,265,50,100,225,417,433⟩,⟨11,22,76,265,50,100,192,384,272⟩,[⟨1,1210181514847129949175809,⟨237,52,236,493,48,100,192,384,272⟩⟩,⟨4,1210181514846030437549057,⟨239,38,236,493,34,100,192,384,256⟩⟩,⟨7,1208926973806483103304709,⟨27,55,127,265,50,119,64,256,272⟩⟩,⟨8,1181745812571339901957,⟨27,55,127,9,50,119,192,128,16⟩⟩]⟩
theorem node721 : UpperPrefix a [3,4,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,2] 30 cert721 (by decide +kernel)

def cert722 : Leaf := ⟨⟨84,72,257,86,76,0,301,109,111⟩,[(5,6)],[(7,5,5)],⟨11,22,76,265,50,224,229,421,309⟩,⟨11,22,76,265,50,224,192,384,272⟩,[⟨5,1210107564158003344057601,⟨11,22,76,265,22,204,204,393,283⟩⟩,⟨1,1210181517098929762861057,⟨237,52,236,493,48,224,224,384,272⟩⟩,⟨4,1210181517097830251234305,⟨239,38,236,493,34,224,224,384,256⟩⟩,⟨8,1181747921297203006469,⟨11,23,127,9,50,224,224,128,16⟩⟩,⟨0,1210107567535926377712640,⟨10,22,126,264,50,224,224,384,272⟩⟩]⟩
theorem node722 : UpperPrefix a [3,4,6,8,1,7] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,7] 30 cert722 (by decide +kernel)

theorem node723 : UpperPrefix a [3,4,6,8,1] 30 :=
  branch_upper a [3,4,6,8,1] 30 (by decide) (fin9_cases _
  node720
  (invalid_upper a [3,4,6,8,1,1] 30 (by decide +kernel))
  node721
  (invalid_upper a [3,4,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,6] 30 (by decide +kernel))
  node722
  (invalid_upper a [3,4,6,8,1,8] 30 (by decide +kernel)))

def cert724 : Leaf := ⟨⟨304,0,307,50,331,282,306,50,162⟩,[(1,4)],[(6,2,4),(2,4,1)],⟨11,22,76,265,52,97,226,418,434⟩,⟨11,22,76,265,52,97,192,384,272⟩,[⟨7,1208926976062732519927109,⟨27,55,127,265,55,119,127,265,283⟩⟩,⟨0,1285813291192731837670400,⟨10,470,76,264,502,96,192,384,466⟩⟩,⟨3,1285813291192730763928577,⟨3,470,68,257,502,97,192,384,466⟩⟩]⟩
theorem node724 : UpperPrefix a [3,4,6,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,2,0] 30 cert724 (by decide +kernel)

def cert725 : Leaf := ⟨⟨304,0,291,50,323,257,291,35,163⟩,[(1,4)],[(6,2,4),(2,4,1)],⟨11,22,76,265,52,98,225,417,433⟩,⟨11,22,76,265,52,98,192,384,272⟩,[⟨3,1214913104420972713225217,⟨499,54,246,481,54,114,192,384,274⟩⟩,⟨7,1208926976062732519927109,⟨27,55,127,265,55,119,127,265,283⟩⟩,⟨4,1210181514423817972483073,⟨239,6,204,493,36,98,192,384,256⟩⟩]⟩
theorem node725 : UpperPrefix a [3,4,6,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,2,1] 30 cert725 (by decide +kernel)

def cert726 : Leaf := ⟨⟨272,0,275,18,331,0,315,59,43⟩,[(1,4),(5,6)],[(6,2,4),(2,4,1),(7,5,5)],⟨11,22,76,265,52,224,227,419,307⟩,⟨11,22,76,265,52,224,192,384,272⟩,[⟨5,1210107564158003344057601,⟨11,22,76,265,22,204,204,393,283⟩⟩]⟩
theorem node726 : UpperPrefix a [3,4,6,8,2,7] 30 :=
  Boolean.leaf_sound a [3,4,6,8,2,7] 30 cert726 (by decide +kernel)

theorem node727 : UpperPrefix a [3,4,6,8,2] 30 :=
  branch_upper a [3,4,6,8,2] 30 (by decide) (fin9_cases _
  node724
  node725
  (invalid_upper a [3,4,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,6] 30 (by decide +kernel))
  node726
  (invalid_upper a [3,4,6,8,2,8] 30 (by decide +kernel)))

def cert728 : Leaf := ⟨⟨464,448,400,208,320,402,276,80,224⟩,[],[(1,6,5),(2,7,6)],⟨11,22,76,265,176,97,194,388,304⟩,⟨11,22,76,265,176,97,194,388,272⟩,[⟨0,1437169456823665566172160,⟨206,470,204,460,498,502,194,388,336⟩⟩,⟨3,1498229981462297977097217,⟨499,470,502,369,498,369,194,470,336⟩⟩,⟨5,1212549902264723481961945,⟨207,87,205,463,223,69,207,463,479⟩⟩]⟩
theorem node728 : UpperPrefix a [3,4,6,8,7,0,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,1,2] 30 cert728 (by decide +kernel)

def cert729 : Leaf := ⟨⟨340,328,272,84,0,286,284,92,76⟩,[(4,7)],[(1,6,5),(5,7,4)],⟨11,22,76,265,176,97,194,416,276⟩,⟨11,22,76,265,176,97,194,416,272⟩,[⟨7,1293929572747387895555411,⟨267,319,109,265,319,109,367,301,283⟩⟩,⟨0,1371113954133118456972288,⟨334,470,76,268,498,502,466,498,464⟩⟩]⟩
theorem node729 : UpperPrefix a [3,4,6,8,7,0,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,1,5] 30 cert729 (by decide +kernel)

theorem node730 : UpperPrefix a [3,4,6,8,7,0,1] 30 :=
  branch_upper a [3,4,6,8,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,1,1] 30 (by decide +kernel))
  node728
  (invalid_upper a [3,4,6,8,7,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,1,4] 30 (by decide +kernel))
  node729
  (invalid_upper a [3,4,6,8,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,1,8] 30 (by decide +kernel)))

def cert731 : Leaf := ⟨⟨448,448,386,194,322,386,258,80,226⟩,[],[(4,1,7)],⟨11,22,76,265,176,97,196,386,304⟩,⟨11,22,76,265,176,97,196,386,272⟩,[⟨0,1437242955569584252666880,⟨206,470,76,332,498,502,196,450,400⟩⟩,⟨2,1757920526297034580296835,⟨139,411,376,265,441,377,505,395,280⟩⟩,⟨3,1479347126536071300516865,⟨499,470,470,433,432,497,198,450,272⟩⟩,⟨5,1212549974322317519889817,⟨207,87,205,463,223,69,205,463,479⟩⟩]⟩
theorem node731 : UpperPrefix a [3,4,6,8,7,0,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,2,1] 30 cert731 (by decide +kernel)

def cert732 : Leaf := ⟨⟨404,384,402,150,0,406,274,22,134⟩,[(4,7)],[(5,7,4)],⟨11,22,76,265,176,97,196,416,274⟩,⟨11,22,76,265,176,97,196,416,272⟩,[⟨0,2353363588496619296048128,⟨334,470,334,268,498,502,470,498,400⟩⟩,⟨3,1697037153358713812192257,⟨499,470,470,433,432,499,470,432,400⟩⟩,⟨6,1673341049552369607541863,⟨267,415,271,265,441,443,415,441,408⟩⟩]⟩
theorem node732 : UpperPrefix a [3,4,6,8,7,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,2,5] 30 cert732 (by decide +kernel)

theorem node733 : UpperPrefix a [3,4,6,8,7,0,2] 30 :=
  branch_upper a [3,4,6,8,7,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,7,0,2,0] 30 (by decide +kernel))
  node731
  (invalid_upper a [3,4,6,8,7,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,2,4] 30 (by decide +kernel))
  node732
  (invalid_upper a [3,4,6,8,7,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,2,8] 30 (by decide +kernel)))

def cert734 : Leaf := ⟨⟨276,265,275,22,0,414,0,31,15⟩,[(4,6),(6,4)],[],⟨11,22,76,265,176,97,224,390,278⟩,⟨11,22,76,265,176,97,224,384,272⟩,[⟨5,1295276181546322894005523,⟨395,415,76,265,415,77,204,393,411⟩⟩,⟨6,1238495951496185065245703,⟨395,415,415,265,176,57,176,384,272⟩⟩,⟨7,1293929570354842003580179,⟨267,287,76,265,319,109,108,265,283⟩⟩]⟩
theorem node734 : UpperPrefix a [3,4,6,8,7,0,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0,5] 30 cert734 (by decide +kernel)

theorem node735 : UpperPrefix a [3,4,6,8,7,0] 30 :=
  branch_upper a [3,4,6,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,7,0,0] 30 (by decide +kernel))
  node730
  node733
  (invalid_upper a [3,4,6,8,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,4] 30 (by decide +kernel))
  node734
  (invalid_upper a [3,4,6,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,0,8] 30 (by decide +kernel)))

def cert736 : Leaf := ⟨⟨464,448,401,210,324,400,272,80,224⟩,[],[(0,6,2)],⟨11,22,76,265,176,98,193,388,304⟩,⟨11,22,76,265,176,98,193,388,272⟩,[⟨3,2414366379105825653328897,⟨499,438,502,369,434,498,499,438,272⟩⟩,⟨5,1212549974322317519889817,⟨207,87,205,463,223,70,205,463,479⟩⟩,⟨1,1436873552313748815085569,⟨205,404,204,461,432,496,197,388,272⟩⟩,⟨2,1295110450276257039909923,⟨299,379,72,265,505,363,201,384,344⟩⟩]⟩
theorem node736 : UpperPrefix a [3,4,6,8,7,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,0,2] 30 cert736 (by decide +kernel)

def cert737 : Leaf := ⟨⟨340,320,275,86,0,404,278,86,70⟩,[(4,7)],[(0,6,2),(5,7,4)],⟨11,22,76,265,176,98,193,416,276⟩,⟨11,22,76,265,176,98,193,416,272⟩,[⟨3,1238875424988733058845697,⟨499,438,502,497,176,498,241,432,272⟩⟩,⟨7,1293929570354846298547507,⟨267,287,76,265,319,367,77,301,283⟩⟩]⟩
theorem node737 : UpperPrefix a [3,4,6,8,7,1,0,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,0,5] 30 cert737 (by decide +kernel)

theorem node738 : UpperPrefix a [3,4,6,8,7,1,0] 30 :=
  branch_upper a [3,4,6,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,0,1] 30 (by decide +kernel))
  node736
  (invalid_upper a [3,4,6,8,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,0,4] 30 (by decide +kernel))
  node737
  (invalid_upper a [3,4,6,8,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,0,8] 30 (by decide +kernel)))

def cert739 : Leaf := ⟨⟨16,73,259,18,11,141,267,43,43⟩,[],[(2,6,5)],⟨11,22,76,265,176,98,196,417,305⟩,⟨11,22,76,265,176,98,196,384,272⟩,[⟨5,1210110158231388806063513,⟨11,87,77,271,223,70,205,463,351⟩⟩,⟨6,1437222725400064812909603,⟨11,415,12,265,441,443,132,384,408⟩⟩,⟨7,1284484837389102578935091,⟨11,287,76,265,319,111,76,265,283⟩⟩,⟨4,1210181586551780754588673,⟨239,102,204,493,160,98,196,384,256⟩⟩,⟨8,1181748066157859998725,⟨11,55,127,9,176,114,247,128,16⟩⟩]⟩
theorem node739 : UpperPrefix a [3,4,6,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,2] 30 cert739 (by decide +kernel)

def cert740 : Leaf := ⟨⟨276,265,275,22,0,413,0,31,15⟩,[(4,6),(6,4)],[],⟨11,22,76,265,176,98,224,389,277⟩,⟨11,22,76,265,176,98,224,384,272⟩,[⟨5,1295571329451506541798707,⟨395,415,76,265,415,463,205,393,411⟩⟩,⟨6,1238495951498388383468583,⟨395,415,415,265,185,443,185,384,272⟩⟩,⟨7,1293929570354846298547507,⟨267,287,76,265,319,367,109,265,283⟩⟩]⟩
theorem node740 : UpperPrefix a [3,4,6,8,7,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,5] 30 cert740 (by decide +kernel)

theorem node741 : UpperPrefix a [3,4,6,8,7,1] 30 :=
  branch_upper a [3,4,6,8,7,1] 30 (by decide) (fin9_cases _
  node738
  (invalid_upper a [3,4,6,8,7,1,1] 30 (by decide +kernel))
  node739
  (invalid_upper a [3,4,6,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,4] 30 (by decide +kernel))
  node740
  (invalid_upper a [3,4,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,8] 30 (by decide +kernel)))

def cert742 : Leaf := ⟨⟨404,384,403,150,262,0,278,54,166⟩,[(5,2)],[(6,2,5),(0,6,2)],⟨11,22,76,265,176,100,193,418,306⟩,⟨11,22,76,265,176,100,193,384,272⟩,[⟨3,1465613435606548949781505,⟨467,438,502,321,434,502,193,384,400⟩⟩,⟨5,1210110158231388806063513,⟨11,87,77,271,223,68,205,463,351⟩⟩]⟩
theorem node742 : UpperPrefix a [3,4,6,8,7,2,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,0] 30 cert742 (by decide +kernel)

def cert743 : Leaf := ⟨⟨276,257,275,22,263,0,277,55,39⟩,[(5,2)],[(6,2,5)],⟨11,22,76,265,176,100,194,417,305⟩,⟨11,22,76,265,176,100,194,384,272⟩,[⟨3,1214839461599104772099073,⟨499,118,118,465,242,118,242,384,336⟩⟩,⟨5,1210110158231388806063577,⟨11,87,77,271,223,69,207,463,351⟩⟩,⟨7,1293929572747387895555411,⟨267,319,109,265,319,109,367,265,283⟩⟩]⟩
theorem node743 : UpperPrefix a [3,4,6,8,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,1] 30 cert743 (by decide +kernel)

def cert744 : Leaf := ⟨⟨432,425,435,178,0,0,0,59,171⟩,[(4,6),(5,2),(6,4)],[(6,2,5)],⟨11,22,76,265,176,100,224,387,275⟩,⟨11,22,76,265,176,100,224,384,272⟩,[⟨2,1219580256600476140700675,⟨395,475,88,393,240,112,240,384,336⟩⟩]⟩
theorem node744 : UpperPrefix a [3,4,6,8,7,2,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,5] 30 cert744 (by decide +kernel)

theorem node745 : UpperPrefix a [3,4,6,8,7,2] 30 :=
  branch_upper a [3,4,6,8,7,2] 30 (by decide) (fin9_cases _
  node742
  node743
  (invalid_upper a [3,4,6,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,4] 30 (by decide +kernel))
  node744
  (invalid_upper a [3,4,6,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,8] 30 (by decide +kernel)))

theorem node746 : UpperPrefix a [3,4,6,8,7] 30 :=
  branch_upper a [3,4,6,8,7] 30 (by decide) (fin9_cases _
  node735
  node741
  node745
  (invalid_upper a [3,4,6,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,8] 30 (by decide +kernel)))

theorem node747 : UpperPrefix a [3,4,6,8] 30 :=
  branch_upper a [3,4,6,8] 30 (by decide) (fin9_cases _
  node717
  node723
  node727
  (invalid_upper a [3,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,6] 30 (by decide +kernel))
  node746
  (invalid_upper a [3,4,6,8,8] 30 (by decide +kernel)))

theorem node748 : UpperPrefix a [3,4,6] 30 :=
  branch_upper a [3,4,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut5 [3,4,6,1] [2,0,4,6] 30 (by decide +kernel) node25)
  (PrefixConjugacy.upper aut5 [3,4,6,2] [3,0,4,6] 30 (by decide +kernel) node472)
  (invalid_upper a [3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,4] 30 (by decide +kernel))
  node671
  (invalid_upper a [3,4,6,6] 30 (by decide +kernel))
  node713
  node747)

def cert749 : Leaf := ⟨⟨500,448,338,0,0,406,278,86,198⟩,[(3,4),(4,3)],[],⟨11,22,140,41,49,358,454,454,342⟩,⟨11,22,140,41,49,96,192,384,272⟩,[⟨0,1295285748986280292918272,⟨494,502,140,236,502,96,192,384,498⟩⟩,⟨3,1238497212711405377031169,⟨499,502,502,49,49,96,192,384,272⟩⟩,⟨5,1295285747191877316387841,⟨463,470,140,205,471,64,192,384,466⟩⟩]⟩
theorem node749 : UpperPrefix a [3,4,7,5,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,0] 30 cert749 (by decide +kernel)

def cert750 : Leaf := ⟨⟨484,488,352,0,452,388,292,100,228⟩,[(3,5)],[(0,5,3)],⟨11,22,140,41,50,97,452,452,340⟩,⟨11,22,140,41,50,97,192,384,272⟩,[⟨1,1297651543561894263783425,⟨493,468,172,237,508,237,192,448,468⟩⟩,⟨3,1219570781057713722885121,⟨499,470,132,49,498,113,192,384,272⟩⟩,⟨4,1212475675060454795772947,⟨11,15,204,41,43,105,196,492,493⟩⟩]⟩
theorem node750 : UpperPrefix a [3,4,7,5,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,0] 30 cert750 (by decide +kernel)

def cert751 : Leaf := ⟨⟨96,97,99,66,69,131,291,99,99⟩,[],[(7,2,5),(2,5,4)],⟨11,22,140,41,50,100,449,449,337⟩,⟨11,22,140,41,50,100,192,384,272⟩,[⟨3,1252692036251494281923585,⟨467,54,502,499,50,118,192,384,272⟩⟩,⟨4,1212473375972840728167443,⟨11,15,172,41,43,100,228,492,493⟩⟩,⟨8,1181747928184199892095,⟨27,31,159,59,59,127,255,128,25⟩⟩]⟩
theorem node751 : UpperPrefix a [3,4,7,5,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,2] 30 cert751 (by decide +kernel)

def cert752 : Leaf := ⟨⟨292,296,290,262,268,0,302,42,46⟩,[(5,8)],[(6,8,5)],⟨11,22,140,41,50,352,193,388,336⟩,⟨11,22,140,41,50,352,193,388,336⟩,[⟨0,1664118841718525346029056,⟨158,22,158,446,306,498,502,438,498⟩⟩,⟨4,1212768953971793116267539,⟨79,79,236,237,239,492,237,492,493⟩⟩,⟨7,1662274167290879995350231,⟨11,31,31,297,315,377,379,319,377⟩⟩]⟩
theorem node752 : UpperPrefix a [3,4,7,5,1,8,0,2,6] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,8,0,2,6] 30 cert752 (by decide +kernel)

theorem node753 : UpperPrefix a [3,4,7,5,1,8,0,2] 30 :=
  branch_upper a [3,4,7,5,1,8,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,1,8,0,2,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,2,5] 30 (by decide +kernel))
  node752
  (invalid_upper a [3,4,7,5,1,8,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,2,8] 30 (by decide +kernel)))

def cert754 : Leaf := ⟨⟨372,360,368,340,332,0,316,0,108⟩,[(5,7),(7,5)],[],⟨11,22,140,41,50,352,193,448,276⟩,⟨11,22,140,41,50,352,193,448,272⟩,[⟨7,1237261177064237925665815,⟨267,287,319,41,315,360,105,360,281⟩⟩,⟨0,1281828513003056546192896,⟨286,278,446,446,434,496,498,496,272⟩⟩,⟨1,1295414699921100877594625,⟨493,276,236,237,436,492,237,492,272⟩⟩]⟩
theorem node754 : UpperPrefix a [3,4,7,5,1,8,0,6] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,8,0,6] 30 cert754 (by decide +kernel)

theorem node755 : UpperPrefix a [3,4,7,5,1,8,0] 30 :=
  branch_upper a [3,4,7,5,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,1] 30 (by decide +kernel))
  node753
  (invalid_upper a [3,4,7,5,1,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,5] 30 (by decide +kernel))
  node754
  (invalid_upper a [3,4,7,5,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,0,8] 30 (by decide +kernel)))

def cert756 : Leaf := ⟨⟨308,296,305,276,268,28,0,60,108⟩,[(6,2)],[(7,2,6),(0,7,2)],⟨11,22,140,41,50,352,196,385,336⟩,⟨11,22,140,41,50,352,196,385,272⟩,[⟨6,1212762743511716558176063,⟨31,31,159,191,191,447,135,391,415⟩⟩,⟨1,1219564066260987778695169,⟨493,372,236,237,304,356,236,493,272⟩⟩]⟩
theorem node756 : UpperPrefix a [3,4,7,5,1,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,8,2,0] 30 cert756 (by decide +kernel)

def cert757 : Leaf := ⟨⟨372,360,370,342,332,0,0,0,111⟩,[(5,7),(6,2),(7,5)],[(7,2,6)],⟨11,22,140,41,50,352,196,448,273⟩,⟨11,22,140,41,50,352,196,448,272⟩,[⟨0,1210402933881630578744832,⟨94,86,254,254,178,498,246,498,272⟩⟩]⟩
theorem node757 : UpperPrefix a [3,4,7,5,1,8,2,6] 30 :=
  Boolean.leaf_sound a [3,4,7,5,1,8,2,6] 30 cert757 (by decide +kernel)

theorem node758 : UpperPrefix a [3,4,7,5,1,8,2] 30 :=
  branch_upper a [3,4,7,5,1,8,2] 30 (by decide) (fin9_cases _
  node756
  (invalid_upper a [3,4,7,5,1,8,2,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,2,5] 30 (by decide +kernel))
  node757
  (invalid_upper a [3,4,7,5,1,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,2,8] 30 (by decide +kernel)))

theorem node759 : UpperPrefix a [3,4,7,5,1,8] 30 :=
  branch_upper a [3,4,7,5,1,8] 30 (by decide) (fin9_cases _
  node755
  (invalid_upper a [3,4,7,5,1,8,1] 30 (by decide +kernel))
  node758
  (invalid_upper a [3,4,7,5,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,8,8] 30 (by decide +kernel)))

theorem node760 : UpperPrefix a [3,4,7,5,1] 30 :=
  branch_upper a [3,4,7,5,1] 30 (by decide) (fin9_cases _
  node750
  (invalid_upper a [3,4,7,5,1,1] 30 (by decide +kernel))
  node751
  (invalid_upper a [3,4,7,5,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,1,7] 30 (by decide +kernel))
  node759)

def cert761 : Leaf := ⟨⟨496,0,370,0,450,402,306,114,226⟩,[(1,4),(3,5)],[(2,4,1),(0,5,3)],⟨11,22,140,41,52,97,450,450,338⟩,⟨11,22,140,41,52,97,192,384,272⟩,[⟨3,1316577975039383661718529,⟨483,470,502,225,502,225,192,448,466⟩⟩]⟩
theorem node761 : UpperPrefix a [3,4,7,5,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,2,0] 30 cert761 (by decide +kernel)

def cert762 : Leaf := ⟨⟨240,0,113,210,193,145,305,113,225⟩,[(1,4)],[(2,4,1),(1,5,3)],⟨11,22,140,41,52,98,449,449,337⟩,⟨11,22,140,41,52,98,192,384,272⟩,[⟨3,1214913104420972713225217,⟨499,54,246,481,54,114,192,384,274⟩⟩,⟨8,1181747927634444084603,⟨11,31,141,59,63,127,255,129,27⟩⟩]⟩
theorem node762 : UpperPrefix a [3,4,7,5,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,2,1] 30 cert762 (by decide +kernel)

def cert763 : Leaf := ⟨⟨480,0,352,448,456,136,298,120,232⟩,[(1,4)],[(4,1,7),(2,4,1),(1,7,6)],⟨11,22,140,41,52,352,193,386,336⟩,⟨11,22,140,41,52,352,193,386,272⟩,[⟨0,1666922737781942640754176,⟨158,150,158,446,438,498,502,386,402⟩⟩]⟩
theorem node763 : UpperPrefix a [3,4,7,5,2,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,2,8,0,1] 30 cert763 (by decide +kernel)

def cert764 : Leaf := ⟨⟨496,0,369,464,457,0,312,0,235⟩,[(1,4),(5,7),(7,5)],[(2,4,1)],⟨11,22,140,41,52,352,193,448,274⟩,⟨11,22,140,41,52,352,193,448,272⟩,[⟨1,1210402861824045189431297,⟨93,20,252,253,180,508,253,508,272⟩⟩]⟩
theorem node764 : UpperPrefix a [3,4,7,5,2,8,0,6] 30 :=
  Boolean.leaf_sound a [3,4,7,5,2,8,0,6] 30 cert764 (by decide +kernel)

theorem node765 : UpperPrefix a [3,4,7,5,2,8,0] 30 :=
  branch_upper a [3,4,7,5,2,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,5,2,8,0,0] 30 (by decide +kernel))
  node763
  (invalid_upper a [3,4,7,5,2,8,0,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,0,5] 30 (by decide +kernel))
  node764
  (invalid_upper a [3,4,7,5,2,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,5,2,8,0,8] 30 (by decide +kernel)))

def cert766 : Leaf := ⟨⟨432,0,307,402,386,146,304,50,226⟩,[(1,4)],[(2,4,1),(0,7,2)],⟨11,22,140,41,52,352,194,385,336⟩,⟨11,22,140,41,52,352,194,385,272⟩,[⟨3,1621036557560361279040513,⟨499,374,502,481,374,352,498,481,306⟩⟩,⟨6,1212762743511716558176063,⟨31,31,159,191,191,447,131,391,415⟩⟩]⟩
theorem node766 : UpperPrefix a [3,4,7,5,2,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,7,5,2,8,1,0] 30 cert766 (by decide +kernel)

def cert767 : Leaf := ⟨⟨368,0,371,338,331,0,313,0,107⟩,[(1,4),(5,7),(7,5)],[(2,4,1)],⟨11,22,140,41,52,352,194,448,273⟩,⟨11,22,140,41,52,352,194,448,272⟩,[⟨7,1312819043041973537615191,⟨267,287,319,41,319,361,363,361,283⟩⟩]⟩
theorem node767 : UpperPrefix a [3,4,7,5,2,8,1,6] 30 :=
  Boolean.leaf_sound a [3,4,7,5,2,8,1,6] 30 cert767 (by decide +kernel)

#print axioms node767
end Delivery.FiniteExclusion.Sharp4x5
