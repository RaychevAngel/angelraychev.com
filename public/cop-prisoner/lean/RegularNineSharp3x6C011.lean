import RegularNineSharp3x6Base
import RegularNineSharp3x6C000
import RegularNineSharp3x6C007
import RegularNineSharp3x6C009
import RegularNineSharp3x6C010
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert704 : Leaf := ⟨⟨20,265,266,38,79,138,14,15,7⟩,[],[(4,1,0),(7,2,5),(5,6,3)],⟨11,22,133,88,304,100,224,387,267⟩,⟨11,22,133,88,304,100,224,384,264⟩,[⟨6,1255199478250530185426185,⟨399,150,389,415,439,36,164,389,399⟩⟩,⟨8,1181817937923050308611,⟨43,127,229,88,48,100,224,128,8⟩⟩,⟨0,1210107637552552225014784,⟨42,126,228,88,304,100,224,384,264⟩⟩]⟩
theorem node704 : UpperPrefix a [3,4,7,6,8,2,5] 30 :=
  Boolean.leaf_sound a [3,4,7,6,8,2,5] 30 cert704 (by decide +kernel)

theorem node705 : UpperPrefix a [3,4,7,6,8,2] 30 :=
  branch_upper a [3,4,7,6,8,2] 30 (by decide) (fin9_cases _
  node700
  node703
  (invalid_upper a [3,4,7,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,4] 30 (by decide +kernel))
  node704
  (invalid_upper a [3,4,7,6,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,2,8] 30 (by decide +kernel)))

theorem node706 : UpperPrefix a [3,4,7,6,8] 30 :=
  branch_upper a [3,4,7,6,8] 30 (by decide) (fin9_cases _
  node693
  node699
  node705
  (invalid_upper a [3,4,7,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,8,8] 30 (by decide +kernel)))

theorem node707 : UpperPrefix a [3,4,7,6] 30 :=
  branch_upper a [3,4,7,6] 30 (by decide) (fin9_cases _
  node668
  node678
  node687
  (invalid_upper a [3,4,7,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,6,7] 30 (by decide +kernel))
  node706)

def cert708 : Local := ⟨⟨368,361,360,96,330,268,0,104,96⟩,[(6,2)],[(4,1,0),(7,2,6),(0,4,1),(1,5,4),(2,6,5)]⟩
theorem node708 : UpperPrefix a [3,4,7,8,0,1,2] 30 :=
  local_sound a [3,4,7,8,0,1,2] 30 cert708 (by decide +kernel)

def cert709 : Leaf := ⟨⟨464,449,328,224,450,388,260,72,224⟩,[],[(4,1,0),(0,4,1),(1,5,4)],⟨11,22,133,280,49,98,224,388,328⟩,⟨11,22,133,280,49,98,224,388,264⟩,[⟨2,1663454747645949727736867,⟨11,27,129,280,313,379,505,384,264⟩⟩,⟨3,1210109950151303135038465,⟨51,118,247,272,49,98,226,502,256⟩⟩,⟨5,1212542534375681543124233,⟨143,22,133,415,23,66,196,389,399⟩⟩]⟩
theorem node709 : UpperPrefix a [3,4,7,8,0,1,5,2] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,1,5,2] 30 cert709 (by decide +kernel)

def cert710 : Leaf := ⟨⟨436,417,288,164,390,388,260,36,164⟩,[],[(4,1,0),(0,4,1),(1,5,4),(6,7,6)],⟨11,22,133,280,49,98,224,448,268⟩,⟨11,22,133,280,49,98,224,448,264⟩,[⟨3,1212547382465838456253953,⟨247,118,247,498,119,98,224,448,480⟩⟩]⟩
theorem node710 : UpperPrefix a [3,4,7,8,0,1,5,6] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,1,5,6] 30 cert710 (by decide +kernel)

theorem node711 : UpperPrefix a [3,4,7,8,0,1,5] 30 :=
  branch_upper a [3,4,7,8,0,1,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,1,5,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,5,1] 30 (by decide +kernel))
  node709
  (invalid_upper a [3,4,7,8,0,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,5,5] 30 (by decide +kernel))
  node710
  (invalid_upper a [3,4,7,8,0,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,5,8] 30 (by decide +kernel)))

theorem node712 : UpperPrefix a [3,4,7,8,0,1] 30 :=
  branch_upper a [3,4,7,8,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,1] 30 (by decide +kernel))
  node708
  (invalid_upper a [3,4,7,8,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,4] 30 (by decide +kernel))
  node711
  (invalid_upper a [3,4,7,8,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,1,8] 30 (by decide +kernel)))

def cert713 : Leaf := ⟨⟨368,353,354,98,322,386,288,66,98⟩,[],[(4,1,0),(7,2,5),(0,4,1)],⟨11,22,133,280,49,100,194,416,328⟩,⟨11,22,133,280,49,100,194,416,264⟩,[⟨2,1678064604976735523439683,⟨331,475,393,408,441,505,459,440,264⟩⟩,⟨3,1210183893099919443258881,⟨247,118,247,498,119,118,226,482,448⟩⟩]⟩
theorem node713 : UpperPrefix a [3,4,7,8,0,2,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,2,1,5] 30 cert713 (by decide +kernel)

def cert714 : Leaf := ⟨⟨368,353,354,98,322,386,288,34,98⟩,[],[(4,1,0),(7,2,5),(0,4,1)],⟨11,22,133,280,49,100,194,448,296⟩,⟨11,22,133,280,49,100,194,448,264⟩,[⟨2,1437242379108838656705603,⟨203,475,193,408,505,505,203,449,264⟩⟩,⟨3,1212542770498345052171777,⟨247,118,247,498,119,118,226,448,448⟩⟩]⟩
theorem node714 : UpperPrefix a [3,4,7,8,0,2,1,6] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,2,1,6] 30 cert714 (by decide +kernel)

theorem node715 : UpperPrefix a [3,4,7,8,0,2,1] 30 :=
  branch_upper a [3,4,7,8,0,2,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,2,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,1] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,4] 30 (by decide +kernel))
  node713
  node714
  (invalid_upper a [3,4,7,8,0,2,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,1,8] 30 (by decide +kernel)))

def cert716 : Leaf := ⟨⟨372,97,354,102,68,128,4,102,102⟩,[],[(4,1,0),(7,2,5),(0,4,1)],⟨11,22,133,280,49,100,224,450,330⟩,⟨11,22,133,280,49,100,224,384,264⟩,[⟨3,1210181587256910229564929,⟨247,118,247,498,119,118,226,384,448⟩⟩,⟨8,1181817938266379275265,⟨59,118,247,24,51,118,226,128,8⟩⟩,⟨1,1210107637552895553961985,⟨57,116,245,280,49,116,224,384,264⟩⟩]⟩
theorem node716 : UpperPrefix a [3,4,7,8,0,2,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,0,2,5] 30 cert716 (by decide +kernel)

theorem node717 : UpperPrefix a [3,4,7,8,0,2] 30 :=
  branch_upper a [3,4,7,8,0,2] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,2,0] 30 (by decide +kernel))
  node715
  (invalid_upper a [3,4,7,8,0,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,4] 30 (by decide +kernel))
  node716
  (invalid_upper a [3,4,7,8,0,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,2,8] 30 (by decide +kernel)))

theorem node718 : UpperPrefix a [3,4,7,8,0] 30 :=
  branch_upper a [3,4,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,0,0] 30 (by decide +kernel))
  node712
  node717
  (invalid_upper a [3,4,7,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,0,8] 30 (by decide +kernel)))

def cert719 : Leaf := ⟨⟨372,353,360,100,325,260,0,108,100⟩,[(6,2)],[(4,1,0),(7,2,6)],⟨11,22,133,280,50,97,196,480,360⟩,⟨11,22,133,280,50,97,196,384,264⟩,[⟨1,1300340804888244264370177,⟨493,508,485,472,508,485,228,384,264⟩⟩,⟨0,1285813111048749158761472,⟨74,478,196,408,506,96,196,384,264⟩⟩,⟨3,1210107637489191525321729,⟨19,118,247,272,50,115,246,384,256⟩⟩]⟩
theorem node719 : UpperPrefix a [3,4,7,8,1,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,8,1,0,2] 30 cert719 (by decide +kernel)

def cert720 : Leaf := ⟨⟨500,225,360,228,193,128,0,108,228⟩,[],[(4,1,0)],⟨11,22,133,280,50,97,224,452,332⟩,⟨11,22,133,280,50,97,224,384,264⟩,[⟨1,1300340804888244264370177,⟨493,508,485,472,508,485,228,384,264⟩⟩,⟨0,1219571033224043253728256,⟨394,478,132,344,506,96,224,384,264⟩⟩,⟨3,1210107637482594455522305,⟨19,118,247,272,50,97,224,384,256⟩⟩,⟨8,1181817867966354557953,⟨27,118,247,24,50,97,224,128,8⟩⟩,⟨2,1210107637482320650306561,⟨27,114,225,280,50,97,224,384,264⟩⟩]⟩
theorem node720 : UpperPrefix a [3,4,7,8,1,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,1,0,5] 30 cert720 (by decide +kernel)

theorem node721 : UpperPrefix a [3,4,7,8,1,0] 30 :=
  branch_upper a [3,4,7,8,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,1] 30 (by decide +kernel))
  node719
  (invalid_upper a [3,4,7,8,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,4] 30 (by decide +kernel))
  node720
  (invalid_upper a [3,4,7,8,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,0,8] 30 (by decide +kernel)))

def cert722 : Leaf := ⟨⟨368,97,360,99,69,129,33,105,97⟩,[],[(4,1,0),(7,2,5),(2,5,4)],⟨11,22,133,280,50,100,225,481,361⟩,⟨11,22,133,280,50,100,192,384,264⟩,[⟨1,1214876138945188757504001,⟨493,244,485,280,48,228,192,384,264⟩⟩,⟨3,1210107637555230942448641,⟨51,118,247,272,50,118,192,384,256⟩⟩,⟨8,1181817940602841484289,⟨59,118,247,24,50,118,192,128,8⟩⟩]⟩
theorem node722 : UpperPrefix a [3,4,7,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,8,1,2] 30 cert722 (by decide +kernel)

theorem node723 : UpperPrefix a [3,4,7,8,1] 30 :=
  branch_upper a [3,4,7,8,1] 30 (by decide) (fin9_cases _
  node721
  (invalid_upper a [3,4,7,8,1,1] 30 (by decide +kernel))
  node722
  (invalid_upper a [3,4,7,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,1,8] 30 (by decide +kernel)))

def cert724 : Leaf := ⟨⟨240,0,362,226,195,130,34,106,226⟩,[(1,4)],[(4,1,0),(2,4,1),(0,5,4)],⟨11,22,133,280,52,97,226,482,362⟩,⟨11,22,133,280,52,97,192,384,264⟩,[⟨8,1181817867966354566153,⟨27,118,247,27,118,97,192,128,9⟩⟩,⟨3,1210107637482594455530497,⟨19,118,247,274,118,97,192,384,256⟩⟩]⟩
theorem node724 : UpperPrefix a [3,4,7,8,2,0] 30 :=
  Boolean.leaf_sound a [3,4,7,8,2,0] 30 cert724 (by decide +kernel)

def cert725 : Leaf := ⟨⟨16,0,362,227,195,129,35,107,227⟩,[(1,4)],[(4,1,0),(2,4,1)],⟨11,22,133,280,52,98,225,481,361⟩,⟨11,22,133,280,52,98,192,384,264⟩,[⟨8,1181818501285052165129,⟨59,118,247,59,118,114,192,128,9⟩⟩,⟨3,1210107638115913153129473,⟨51,118,247,306,118,114,192,384,256⟩⟩,⟨5,1210107564157951779283977,⟨11,22,133,283,22,66,192,384,265⟩⟩,⟨6,1210106412362347079279625,⟨11,22,133,283,54,34,128,384,265⟩⟩,⟨7,1208926973663134274823177,⟨11,22,5,283,54,98,64,256,265⟩⟩]⟩
theorem node725 : UpperPrefix a [3,4,7,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,7,8,2,1] 30 cert725 (by decide +kernel)

theorem node726 : UpperPrefix a [3,4,7,8,2] 30 :=
  branch_upper a [3,4,7,8,2] 30 (by decide) (fin9_cases _
  node724
  node725
  (invalid_upper a [3,4,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,2,8] 30 (by decide +kernel)))

def cert727 : Leaf := ⟨⟨308,417,296,37,0,262,293,45,37⟩,[(4,5)],[(4,1,0),(6,4,4),(1,6,5)],⟨11,22,133,280,112,97,194,420,300⟩,⟨11,22,133,280,112,97,194,384,264⟩,[⟨7,1218371709450229260485699,⟨267,319,5,312,121,121,379,256,264⟩⟩,⟨3,1210107637484793478777857,⟨19,118,247,272,112,113,210,384,256⟩⟩]⟩
theorem node727 : UpperPrefix a [3,4,7,8,6,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,0,1] 30 cert727 (by decide +kernel)

def cert728 : Local := ⟨⟨308,297,298,39,0,270,0,47,39⟩,[(4,5),(6,2)],[(4,1,0),(7,2,6),(6,4,4)]⟩
theorem node728 : UpperPrefix a [3,4,7,8,6,0,2] 30 :=
  local_sound a [3,4,7,8,6,0,2] 30 cert728 (by decide +kernel)

def cert729 : Leaf := ⟨⟨404,393,266,134,0,398,271,14,134⟩,[(4,5)],[(4,1,0),(6,4,4),(5,6,4)],⟨11,22,133,280,112,97,224,390,270⟩,⟨11,22,133,280,112,97,224,384,264⟩,[⟨0,1219570745000262024299520,⟨394,414,132,280,112,112,240,384,264⟩⟩]⟩
theorem node729 : UpperPrefix a [3,4,7,8,6,0,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,0,5] 30 cert729 (by decide +kernel)

theorem node730 : UpperPrefix a [3,4,7,8,6,0] 30 :=
  branch_upper a [3,4,7,8,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,8,6,0,0] 30 (by decide +kernel))
  node727
  node728
  (invalid_upper a [3,4,7,8,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,0,4] 30 (by decide +kernel))
  node729
  (invalid_upper a [3,4,7,8,6,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,0,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,0,8] 30 (by decide +kernel)))

def cert731 : Local := ⟨⟨436,425,0,167,0,397,0,47,167⟩,[(2,6),(4,5),(6,2)],[(4,1,0),(6,4,4)]⟩
theorem node731 : UpperPrefix a [3,4,7,8,6,1,0] 30 :=
  local_sound a [3,4,7,8,6,1,0] 30 cert731 (by decide +kernel)

def cert732 : Local := ⟨⟨304,297,298,35,0,269,0,43,35⟩,[(4,5),(6,2)],[(4,1,0),(7,2,6),(6,4,4),(2,6,5)]⟩
theorem node732 : UpperPrefix a [3,4,7,8,6,1,2] 30 :=
  local_sound a [3,4,7,8,6,1,2] 30 cert732 (by decide +kernel)

def cert733 : Leaf := ⟨⟨404,392,266,135,0,396,270,15,135⟩,[(4,5)],[(4,1,0),(6,4,4),(5,6,4)],⟨11,22,133,280,112,98,224,389,269⟩,⟨11,22,133,280,112,98,224,384,264⟩,[⟨0,1210107637559561343208448,⟨58,118,246,280,112,114,240,384,264⟩⟩]⟩
theorem node733 : UpperPrefix a [3,4,7,8,6,1,5] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,1,5] 30 cert733 (by decide +kernel)

theorem node734 : UpperPrefix a [3,4,7,8,6,1] 30 :=
  branch_upper a [3,4,7,8,6,1] 30 (by decide) (fin9_cases _
  node731
  (invalid_upper a [3,4,7,8,6,1,1] 30 (by decide +kernel))
  node732
  (invalid_upper a [3,4,7,8,6,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,1,4] 30 (by decide +kernel))
  node733
  (invalid_upper a [3,4,7,8,6,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,1,8] 30 (by decide +kernel)))

def cert735 : Leaf := ⟨⟨308,33,298,39,0,131,39,47,39⟩,[(4,5)],[(4,1,0),(7,2,5),(6,4,4)],⟨11,22,133,280,112,100,227,419,299⟩,⟨11,22,133,280,112,100,192,384,264⟩,[⟨3,1210107637555162222971905,⟨51,118,247,272,114,118,192,384,256⟩⟩,⟨8,1181817940534122007553,⟨59,118,247,24,114,118,192,128,8⟩⟩]⟩
theorem node735 : UpperPrefix a [3,4,7,8,6,2] 30 :=
  Boolean.leaf_sound a [3,4,7,8,6,2] 30 cert735 (by decide +kernel)

theorem node736 : UpperPrefix a [3,4,7,8,6] 30 :=
  branch_upper a [3,4,7,8,6] 30 (by decide) (fin9_cases _
  node730
  node734
  node735
  (invalid_upper a [3,4,7,8,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,6,8] 30 (by decide +kernel)))

theorem node737 : UpperPrefix a [3,4,7,8] 30 :=
  branch_upper a [3,4,7,8] 30 (by decide) (fin9_cases _
  node718
  node723
  node726
  (invalid_upper a [3,4,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,5] 30 (by decide +kernel))
  node736
  (invalid_upper a [3,4,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,8,8] 30 (by decide +kernel)))

theorem node738 : UpperPrefix a [3,4,7] 30 :=
  branch_upper a [3,4,7] 30 (by decide) (fin9_cases _
  node627
  node636
  node637
  (invalid_upper a [3,4,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,4] 30 (by decide +kernel))
  node656
  node707
  (invalid_upper a [3,4,7,7] 30 (by decide +kernel))
  node737)

theorem node739 : UpperPrefix a [3,4] 30 :=
  branch_upper a [3,4] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,0] 30 (by decide +kernel))
  (PrefixConjugacy.upper aut6 [3,4,1] [2,3,4] 30 (by decide +kernel) node40)
  (invalid_upper a [3,4,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,4] 30 (by decide +kernel))
  node472
  node606
  node738
  (PrefixConjugacy.upper aut7 [3,4,8] [3,4,5] 30 (by decide +kernel) node472))

def cert740 : Leaf := ⟨⟨468,465,0,0,0,405,277,85,213⟩,[(2,3),(3,2),(4,1)],[(5,1,4),(1,4,2),(1,4,3)],⟨11,38,21,25,50,484,452,452,460⟩,⟨11,38,21,25,50,96,192,384,264⟩,[⟨3,1212473369245028837622785,⟨23,54,21,21,50,96,208,498,502⟩⟩]⟩
theorem node740 : UpperPrefix a [3,5,4,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,0,1] 30 cert740 (by decide +kernel)

def cert741 : Leaf := ⟨⟨496,0,0,0,0,411,315,123,243⟩,[(1,4),(2,3),(3,2),(4,1)],[],⟨11,38,21,25,52,482,450,450,458⟩,⟨11,38,21,25,52,96,192,384,264⟩,[⟨2,1224302388997320366621699,⟨491,491,505,505,56,96,192,384,264⟩⟩]⟩
theorem node741 : UpperPrefix a [3,5,4,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,0,2] 30 cert741 (by decide +kernel)

def cert742 : Leaf := ⟨⟨404,401,0,0,0,407,279,23,151⟩,[(2,3),(3,2),(4,5)],[(6,4,4)],⟨11,38,21,25,112,486,454,390,398⟩,⟨11,38,21,25,112,96,192,384,264⟩,[⟨3,1212473369247090421662721,⟨7,54,21,21,112,112,208,498,502⟩⟩,⟨5,1224302387765867346658307,⟨463,463,477,477,80,64,192,384,268⟩⟩]⟩
theorem node742 : UpperPrefix a [3,5,4,0,6] 30 :=
  Boolean.leaf_sound a [3,5,4,0,6] 30 cert742 (by decide +kernel)

def cert743 : Leaf := ⟨⟨16,17,0,0,327,407,279,87,215⟩,[(2,3),(3,2)],[],⟨11,38,21,25,176,358,454,454,334⟩,⟨11,38,21,25,176,96,192,384,264⟩,[⟨3,1212473369244891398407169,⟨7,38,21,21,176,96,208,498,502⟩⟩,⟨5,1224302387765867346658307,⟨463,463,477,477,144,64,192,384,268⟩⟩,⟨6,1210106412362349769925663,⟨15,47,31,31,191,32,128,384,269⟩⟩,⟨7,1208926973663136965469215,⟨15,47,31,31,63,96,64,256,269⟩⟩,⟨8,1181745669225202066463,⟨15,47,31,31,191,96,192,128,13⟩⟩,⟨2,1210107565283852221940739,⟨11,43,25,25,176,96,192,384,264⟩⟩]⟩
theorem node743 : UpperPrefix a [3,5,4,0,7] 30 :=
  Boolean.leaf_sound a [3,5,4,0,7] 30 cert743 (by decide +kernel)

def cert744 : Leaf := ⟨⟨16,17,0,0,199,407,279,87,215⟩,[(2,3),(3,2)],[],⟨11,38,21,25,304,230,198,454,462⟩,⟨11,38,21,25,304,96,192,384,264⟩,[⟨3,1212473369244891398407169,⟨7,38,21,21,498,96,208,498,502⟩⟩,⟨5,1224302387765867346658307,⟨463,463,477,477,272,64,192,384,268⟩⟩,⟨6,1210106412362349769925663,⟨15,47,31,31,319,32,128,384,269⟩⟩,⟨7,1208926973663136965469215,⟨15,47,31,31,319,96,64,256,269⟩⟩,⟨8,1181745669225202066463,⟨15,47,31,31,63,96,192,128,13⟩⟩,⟨2,1210107565283852221940739,⟨11,43,25,25,304,96,192,384,264⟩⟩]⟩
theorem node744 : UpperPrefix a [3,5,4,0,8] 30 :=
  Boolean.leaf_sound a [3,5,4,0,8] 30 cert744 (by decide +kernel)

theorem node745 : UpperPrefix a [3,5,4,0] 30 :=
  branch_upper a [3,5,4,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,0,0] 30 (by decide +kernel))
  node740
  node741
  (invalid_upper a [3,5,4,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,0,5] 30 (by decide +kernel))
  node742
  node743
  node744)

def cert746 : Leaf := ⟨⟨0,408,0,420,396,412,284,92,212⟩,[(0,3),(2,4)],[(5,1,3),(1,3,0),(0,4,2)],⟨11,38,21,26,49,484,452,452,460⟩,⟨11,38,21,26,49,96,192,384,264⟩,[⟨6,1210106412364690938946623,⟨31,63,31,31,63,63,128,384,269⟩⟩]⟩
theorem node746 : UpperPrefix a [3,5,4,1,0] 30 :=
  Boolean.leaf_sound a [3,5,4,1,0] 30 cert746 (by decide +kernel)

def cert747 : Local := ⟨⟨0,0,456,485,0,409,281,89,209⟩,[(0,3),(1,4),(4,1)],[(5,1,3),(1,3,0),(2,4,3)]⟩
theorem node747 : UpperPrefix a [3,5,4,1,2] 30 :=
  local_sound a [3,5,4,1,2] 30 cert747 (by decide +kernel)

def cert748 : Leaf := ⟨⟨0,281,264,293,0,413,285,29,149⟩,[(0,3),(4,5)],[(5,1,3),(1,3,0),(6,4,4)],⟨11,38,21,26,112,485,453,389,397⟩,⟨11,38,21,26,112,96,192,384,264⟩,[⟨7,1208926973665340561056831,⟨15,63,31,31,127,127,64,256,269⟩⟩]⟩
theorem node748 : UpperPrefix a [3,5,4,1,6] 30 :=
  Boolean.leaf_sound a [3,5,4,1,6] 30 cert748 (by decide +kernel)

def cert749 : Leaf := ⟨⟨0,153,136,164,76,156,284,92,212⟩,[(0,3)],[(5,1,3),(1,3,0),(0,5,1)],⟨11,38,21,26,176,97,452,452,332⟩,⟨11,38,21,26,176,97,192,384,264⟩,[⟨8,1181747925435972379775,⟨15,47,31,31,191,127,255,128,13⟩⟩,⟨6,1210106412362349769925663,⟨15,47,31,31,191,33,128,384,269⟩⟩]⟩
theorem node749 : UpperPrefix a [3,5,4,1,7,0] 30 :=
  Boolean.leaf_sound a [3,5,4,1,7,0] 30 cert749 (by decide +kernel)

def cert750 : Local := ⟨⟨0,0,456,481,329,409,281,89,209⟩,[(0,3),(1,5)],[(5,1,3),(1,3,0),(2,5,1)]⟩
theorem node750 : UpperPrefix a [3,5,4,1,7,2] 30 :=
  local_sound a [3,5,4,1,7,2] 30 cert750 (by decide +kernel)

def cert751 : Leaf := ⟨⟨0,25,8,37,333,157,28,93,213⟩,[(0,3)],[(5,1,3),(1,3,0),(8,5,4)],⟨11,38,21,26,176,352,193,452,332⟩,⟨11,38,21,26,176,352,193,384,264⟩,[⟨6,1210106412362349769925663,⟨15,47,31,31,191,288,129,384,269⟩⟩,⟨7,1208926973663136965469215,⟨15,47,31,31,63,352,65,256,269⟩⟩]⟩
theorem node751 : UpperPrefix a [3,5,4,1,7,8,0] 30 :=
  Boolean.leaf_sound a [3,5,4,1,7,8,0] 30 cert751 (by decide +kernel)

def cert752 : Leaf := ⟨⟨0,73,72,101,333,13,9,77,69⟩,[(0,3)],[(5,1,3),(1,3,0),(8,5,4)],⟨11,38,21,26,176,352,196,449,329⟩,⟨11,38,21,26,176,352,196,384,264⟩,[⟨4,1252728876008845987580937,⟨491,230,487,491,160,354,230,384,425⟩⟩,⟨7,1511158430818594072863839,⟨15,47,31,31,63,355,367,256,269⟩⟩]⟩
theorem node752 : UpperPrefix a [3,5,4,1,7,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,1,7,8,2] 30 cert752 (by decide +kernel)

theorem node753 : UpperPrefix a [3,5,4,1,7,8] 30 :=
  branch_upper a [3,5,4,1,7,8] 30 (by decide) (fin9_cases _
  node751
  (invalid_upper a [3,5,4,1,7,8,1] 30 (by decide +kernel))
  node752
  (invalid_upper a [3,5,4,1,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,8,8] 30 (by decide +kernel)))

theorem node754 : UpperPrefix a [3,5,4,1,7] 30 :=
  branch_upper a [3,5,4,1,7] 30 (by decide) (fin9_cases _
  node749
  (invalid_upper a [3,5,4,1,7,1] 30 (by decide +kernel))
  node750
  (invalid_upper a [3,5,4,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,7,7] 30 (by decide +kernel))
  node753)

def cert755 : Leaf := ⟨⟨0,281,264,292,204,412,284,92,212⟩,[(0,3)],[(5,1,3),(1,3,0),(0,5,1)],⟨11,38,21,26,304,97,196,452,460⟩,⟨11,38,21,26,304,97,192,384,264⟩,[⟨6,1210106412362349769925663,⟨15,47,31,31,319,33,128,384,269⟩⟩,⟨7,1208926973663136965469215,⟨15,47,31,31,319,97,64,256,269⟩⟩]⟩
theorem node755 : UpperPrefix a [3,5,4,1,8,0] 30 :=
  Boolean.leaf_sound a [3,5,4,1,8,0] 30 cert755 (by decide +kernel)

def cert756 : Local := ⟨⟨0,0,456,481,201,409,281,89,209⟩,[(0,3),(1,5)],[(5,1,3),(1,3,0),(2,5,1)]⟩
theorem node756 : UpperPrefix a [3,5,4,1,8,2] 30 :=
  local_sound a [3,5,4,1,8,2] 30 cert756 (by decide +kernel)

def cert757 : Leaf := ⟨⟨0,281,264,293,77,0,285,93,85⟩,[(0,3),(5,6)],[(5,1,3),(1,3,0),(7,5,5)],⟨11,38,21,26,304,224,197,453,333⟩,⟨11,38,21,26,304,224,192,384,264⟩,[⟨6,1210106412362349769925663,⟨15,47,31,31,319,160,128,384,269⟩⟩]⟩
theorem node757 : UpperPrefix a [3,5,4,1,8,7] 30 :=
  Boolean.leaf_sound a [3,5,4,1,8,7] 30 cert757 (by decide +kernel)

theorem node758 : UpperPrefix a [3,5,4,1,8] 30 :=
  branch_upper a [3,5,4,1,8] 30 (by decide) (fin9_cases _
  node755
  (invalid_upper a [3,5,4,1,8,1] 30 (by decide +kernel))
  node756
  (invalid_upper a [3,5,4,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,8,6] 30 (by decide +kernel))
  node757
  (invalid_upper a [3,5,4,1,8,8] 30 (by decide +kernel)))

theorem node759 : UpperPrefix a [3,5,4,1] 30 :=
  branch_upper a [3,5,4,1] 30 (by decide) (fin9_cases _
  node746
  (invalid_upper a [3,5,4,1,1] 30 (by decide +kernel))
  node747
  (invalid_upper a [3,5,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,1,5] 30 (by decide +kernel))
  node748
  node754
  node758)

def cert760 : Leaf := ⟨⟨4,9,42,0,459,395,267,75,195⟩,[(3,2)],[(4,2,3),(2,3,0)],⟨11,38,21,28,499,483,451,451,459⟩,⟨11,38,21,28,48,96,192,384,264⟩,[⟨5,1224302387765867344561155,⟨459,463,477,28,16,64,192,384,264⟩⟩,⟨6,1210106412362349769925663,⟨15,47,31,31,63,32,128,384,269⟩⟩,⟨7,1208926973663136965469215,⟨15,47,31,31,63,96,64,256,269⟩⟩,⟨8,1181745669225202066463,⟨15,47,31,31,63,96,192,128,13⟩⟩]⟩
theorem node760 : UpperPrefix a [3,5,4,2] 30 :=
  Boolean.leaf_sound a [3,5,4,2] 30 cert760 (by decide +kernel)

def cert761 : Leaf := ⟨⟨84,88,0,4,78,28,284,92,212⟩,[(2,4)],[(0,4,2),(1,5,4)],⟨11,38,21,88,49,98,452,388,396⟩,⟨11,38,21,88,49,98,192,384,264⟩,[⟨5,1352055800237104751969283,⟨459,463,477,476,477,451,192,384,456⟩⟩,⟨7,1208926976221367253268347,⟨63,63,23,127,63,127,127,279,319⟩⟩,⟨8,1181748227455489865595,⟨63,63,23,127,63,127,255,151,63⟩⟩]⟩
theorem node761 : UpperPrefix a [3,5,4,6,0,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,0,1] 30 cert761 (by decide +kernel)

def cert762 : Leaf := ⟨⟨464,0,0,386,458,410,282,90,210⟩,[(1,5),(2,4)],[(0,4,2),(2,5,1)],⟨11,38,21,88,49,100,450,386,394⟩,⟨11,38,21,88,49,100,192,384,264⟩,[⟨5,1224302387765869496239107,⟨459,463,477,92,477,76,192,384,264⟩⟩]⟩
theorem node762 : UpperPrefix a [3,5,4,6,0,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,0,2] 30 cert762 (by decide +kernel)

def cert763 : Leaf := ⟨⟨52,24,0,38,78,0,318,62,54⟩,[(2,4),(5,6)],[(0,4,2),(7,5,5)],⟨11,38,21,88,49,224,454,390,270⟩,⟨11,38,21,88,49,224,192,384,264⟩,[⟨6,1252875188497242680992777,⟨399,166,407,415,439,160,128,384,397⟩⟩,⟨8,1181747928319573947771,⟨31,63,23,127,63,255,255,133,31⟩⟩]⟩
theorem node763 : UpperPrefix a [3,5,4,6,0,7] 30 :=
  Boolean.leaf_sound a [3,5,4,6,0,7] 30 cert763 (by decide +kernel)

def cert764 : Leaf := ⟨⟨276,280,0,262,332,156,284,28,148⟩,[(2,4)],[(0,4,2)],⟨11,38,21,88,49,352,194,388,396⟩,⟨11,38,21,88,49,352,194,384,264⟩,[⟨5,1352055313848344995955715,⟨459,463,477,476,477,320,451,384,392⟩⟩,⟨1,1252876341700290982182913,⟨445,164,405,508,437,352,192,384,424⟩⟩,⟨6,1255236371738677503599625,⟨399,166,407,415,439,416,130,384,397⟩⟩,⟨7,1208926973665483654194299,⟨31,63,23,95,63,383,95,256,269⟩⟩]⟩
theorem node764 : UpperPrefix a [3,5,4,6,0,8,1] 30 :=
  Boolean.leaf_sound a [3,5,4,6,0,8,1] 30 cert764 (by decide +kernel)

def cert765 : Leaf := ⟨⟨388,392,0,390,462,142,266,14,134⟩,[(2,4)],[(0,4,2)],⟨11,38,21,88,49,352,196,386,394⟩,⟨11,38,21,88,49,352,196,384,264⟩,[⟨4,1253024023914025340406793,⟨491,230,487,491,417,482,230,384,425⟩⟩,⟨5,1224302730039441176396803,⟨459,463,477,92,477,320,204,384,264⟩⟩,⟨6,1252875188497242680992777,⟨399,166,407,415,439,288,132,384,397⟩⟩]⟩
theorem node765 : UpperPrefix a [3,5,4,6,0,8,2] 30 :=
  Boolean.leaf_sound a [3,5,4,6,0,8,2] 30 cert765 (by decide +kernel)

theorem node766 : UpperPrefix a [3,5,4,6,0,8] 30 :=
  branch_upper a [3,5,4,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,6,0,8,0] 30 (by decide +kernel))
  node764
  node765
  (invalid_upper a [3,5,4,6,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,8,8] 30 (by decide +kernel)))

theorem node767 : UpperPrefix a [3,5,4,6,0] 30 :=
  branch_upper a [3,5,4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,5,4,6,0,0] 30 (by decide +kernel))
  node761
  node762
  (invalid_upper a [3,5,4,6,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,5,4,6,0,6] 30 (by decide +kernel))
  node763
  node766)

#print axioms node767
end Delivery.FiniteExclusion.Sharp3x6
