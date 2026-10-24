import RegularNineSharp3x6Base
import RegularNineSharp3x6C007
import RegularNineSharp3x6C008
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def cert576 : Leaf := ⟨⟨144,169,170,259,143,0,15,11,131⟩,[(5,2)],[(4,1,0),(6,2,5),(8,4,3)],⟨11,22,69,152,304,100,224,387,267⟩,⟨11,22,69,152,304,100,224,384,264⟩,[⟨2,1224302334848571453473795,⟨395,411,449,152,304,96,224,384,264⟩⟩,⟨5,1224302333722671547679747,⟨395,415,453,152,272,68,192,384,264⟩⟩]⟩
theorem node576 : UpperPrefix a [3,4,6,7,8,2,5] 30 :=
  Boolean.leaf_sound a [3,4,6,7,8,2,5] 30 cert576 (by decide +kernel)

theorem node577 : UpperPrefix a [3,4,6,7,8,2] 30 :=
  branch_upper a [3,4,6,7,8,2] 30 (by decide) (fin9_cases _
  node574
  node575
  (invalid_upper a [3,4,6,7,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,4] 30 (by decide +kernel))
  node576
  (invalid_upper a [3,4,6,7,8,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,2,8] 30 (by decide +kernel)))

theorem node578 : UpperPrefix a [3,4,6,7,8] 30 :=
  branch_upper a [3,4,6,7,8] 30 (by decide) (fin9_cases _
  node565
  node573
  node577
  (invalid_upper a [3,4,6,7,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,8,8] 30 (by decide +kernel)))

theorem node579 : UpperPrefix a [3,4,6,7] 30 :=
  branch_upper a [3,4,6,7] 30 (by decide) (fin9_cases _
  node547
  node554
  node561
  (invalid_upper a [3,4,6,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,7,7] 30 (by decide +kernel))
  node578)

def cert580 : Leaf := ⟨⟨500,97,416,228,70,4,292,100,228⟩,[],[(4,1,0),(0,4,1),(1,5,4)],⟨11,22,69,280,49,98,228,420,428⟩,⟨11,22,69,280,49,98,192,384,264⟩,[⟨3,1210181524417621683092993,⟨247,54,119,502,119,98,192,416,482⟩⟩,⟨7,1208926973804146641079297,⟨11,54,119,280,49,98,64,256,264⟩⟩,⟨8,1181745810234877676545,⟨11,54,119,24,49,98,192,128,8⟩⟩]⟩
theorem node580 : UpperPrefix a [3,4,6,8,0,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,1] 30 cert580 (by decide +kernel)

def cert581 : Leaf := ⟨⟨436,289,418,166,262,0,294,38,166⟩,[(5,2)],[(4,1,0),(6,2,5),(0,4,1)],⟨11,22,69,280,49,100,226,418,426⟩,⟨11,22,69,280,49,100,192,384,264⟩,[⟨3,1212547310337875678363137,⟨247,54,119,502,119,118,192,448,482⟩⟩,⟨7,1208926973804146641095681,⟨11,54,119,280,51,118,64,256,264⟩⟩]⟩
theorem node581 : UpperPrefix a [3,4,6,8,0,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,2] 30 cert581 (by decide +kernel)

def cert582 : Leaf := ⟨⟨116,97,34,102,70,0,38,102,102⟩,[(5,6)],[(4,1,0),(0,4,1),(7,5,5)],⟨11,22,69,280,49,224,230,422,302⟩,⟨11,22,69,280,49,224,192,384,264⟩,[⟨3,1210181525965734055001601,⟨247,22,119,502,119,224,224,416,482⟩⟩,⟨8,1184634737454478392585,⟨11,22,119,31,119,246,246,247,11⟩⟩]⟩
theorem node582 : UpperPrefix a [3,4,6,8,0,7] 30 :=
  Boolean.leaf_sound a [3,4,6,8,0,7] 30 cert582 (by decide +kernel)

theorem node583 : UpperPrefix a [3,4,6,8,0] 30 :=
  branch_upper a [3,4,6,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,6,8,0,0] 30 (by decide +kernel))
  node580
  node581
  (invalid_upper a [3,4,6,8,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,0,6] 30 (by decide +kernel))
  node582
  (invalid_upper a [3,4,6,8,0,8] 30 (by decide +kernel)))

def cert584 : Leaf := ⟨⟨116,97,0,229,69,0,301,109,229⟩,[(2,5),(5,2)],[(4,1,0)],⟨11,22,69,280,50,97,228,420,428⟩,⟨11,22,69,280,50,97,192,384,264⟩,[⟨1,1300340804888244264370177,⟨493,508,485,472,508,485,192,384,264⟩⟩,⟨7,1208926973806483111701513,⟨27,54,119,283,54,119,64,256,265⟩⟩,⟨8,1181745812571348298761,⟨27,54,119,27,54,119,192,128,9⟩⟩,⟨3,1210107565427199449263105,⟨19,54,119,274,54,119,192,384,256⟩⟩]⟩
theorem node584 : UpperPrefix a [3,4,6,8,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,0] 30 cert584 (by decide +kernel)

def cert585 : Leaf := ⟨⟨432,424,424,163,396,0,297,41,161⟩,[(5,2)],[(4,1,0),(6,2,5),(2,5,4)],⟨11,22,69,280,50,100,225,417,425⟩,⟨11,22,69,280,50,100,192,384,264⟩,[⟨1,1214876138945188757504001,⟨493,244,485,280,48,228,192,384,264⟩⟩,⟨0,1210107565427200514608128,⟨26,54,118,280,50,118,192,384,264⟩⟩]⟩
theorem node585 : UpperPrefix a [3,4,6,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,2] 30 cert585 (by decide +kernel)

def cert586 : Leaf := ⟨⟨372,360,0,100,332,0,300,108,100⟩,[(2,6),(5,6)],[(4,1,0),(7,5,5),(0,6,2)],⟨11,22,69,280,50,224,193,420,300⟩,⟨11,22,69,280,50,224,193,384,264⟩,[⟨1,1224929616717162709516289,⟨493,508,485,280,440,228,485,384,264⟩⟩]⟩
theorem node586 : UpperPrefix a [3,4,6,8,1,7,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,7,0] 30 cert586 (by decide +kernel)

def cert587 : Leaf := ⟨⟨304,361,296,35,329,0,297,41,33⟩,[(5,6)],[(4,1,0),(7,5,5)],⟨11,22,69,280,50,224,196,417,297⟩,⟨11,22,69,280,50,224,196,384,264⟩,[⟨2,1314202544484471975969811,⟨411,443,489,409,443,224,480,384,264⟩⟩,⟨1,1214876177225785590153217,⟨493,244,485,280,112,224,228,384,264⟩⟩,⟨6,1285811850040853495022611,⟨11,415,5,409,443,160,132,384,264⟩⟩]⟩
theorem node587 : UpperPrefix a [3,4,6,8,1,7,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,7,2] 30 cert587 (by decide +kernel)

def cert588 : Leaf := ⟨⟨276,361,298,7,333,0,0,15,7⟩,[(5,6),(6,5)],[(4,1,0),(7,5,5),(7,5,6)],⟨11,22,69,280,50,224,224,389,269⟩,⟨11,22,69,280,50,224,224,384,264⟩,[⟨5,1219570743867767195173907,⟨395,415,69,281,411,192,192,384,264⟩⟩,⟨6,1219569592072162495169555,⟨395,415,5,281,443,160,160,384,264⟩⟩]⟩
theorem node588 : UpperPrefix a [3,4,6,8,1,7,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,1,7,5] 30 cert588 (by decide +kernel)

theorem node589 : UpperPrefix a [3,4,6,8,1,7] 30 :=
  branch_upper a [3,4,6,8,1,7] 30 (by decide) (fin9_cases _
  node586
  (invalid_upper a [3,4,6,8,1,7,1] 30 (by decide +kernel))
  node587
  (invalid_upper a [3,4,6,8,1,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,7,4] 30 (by decide +kernel))
  node588
  (invalid_upper a [3,4,6,8,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,7,8] 30 (by decide +kernel)))

theorem node590 : UpperPrefix a [3,4,6,8,1] 30 :=
  branch_upper a [3,4,6,8,1] 30 (by decide) (fin9_cases _
  node584
  (invalid_upper a [3,4,6,8,1,1] 30 (by decide +kernel))
  node585
  (invalid_upper a [3,4,6,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,1,6] 30 (by decide +kernel))
  node589
  (invalid_upper a [3,4,6,8,1,8] 30 (by decide +kernel)))

def cert591 : Local := ⟨⟨432,0,0,162,459,0,298,42,162⟩,[(1,4),(2,5),(5,2)],[(4,1,0),(6,2,4),(2,4,1),(0,5,4)]⟩
theorem node591 : UpperPrefix a [3,4,6,8,2,0] 30 :=
  local_sound a [3,4,6,8,2,0] 30 cert591 (by decide +kernel)

def cert592 : Leaf := ⟨⟨48,0,426,163,75,9,299,43,163⟩,[(1,4)],[(4,1,0),(6,2,4),(2,4,1)],⟨11,22,69,280,52,98,225,417,425⟩,⟨11,22,69,280,52,98,192,384,264⟩,[⟨7,1208926973804284080040969,⟨27,54,119,283,54,114,64,256,265⟩⟩,⟨8,1181745810372316638217,⟨27,54,119,27,54,114,192,128,9⟩⟩]⟩
theorem node592 : UpperPrefix a [3,4,6,8,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,2,1] 30 cert592 (by decide +kernel)

def cert593 : Local := ⟨⟨304,0,298,35,331,0,299,43,35⟩,[(1,4),(5,6)],[(4,1,0),(6,2,4),(2,4,1),(7,5,5)]⟩
theorem node593 : UpperPrefix a [3,4,6,8,2,7] 30 :=
  local_sound a [3,4,6,8,2,7] 30 cert593 (by decide +kernel)

theorem node594 : UpperPrefix a [3,4,6,8,2] 30 :=
  branch_upper a [3,4,6,8,2] 30 (by decide) (fin9_cases _
  node591
  node592
  (invalid_upper a [3,4,6,8,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,2,6] 30 (by decide +kernel))
  node593
  (invalid_upper a [3,4,6,8,2,8] 30 (by decide +kernel)))

def cert595 : Leaf := ⟨⟨84,65,0,103,79,0,39,111,103⟩,[(2,5),(5,2)],[(4,1,0)],⟨11,22,69,280,176,97,230,422,302⟩,⟨11,22,69,280,176,97,192,384,264⟩,[⟨7,1293929570495527801332763,⟨267,319,101,283,319,101,64,256,265⟩⟩,⟨8,1184344681614152957193,⟨47,118,119,127,246,119,246,247,47⟩⟩,⟨3,1210107853654964260840449,⟨3,118,101,338,246,101,192,384,256⟩⟩,⟨5,1210107564157951787672585,⟨11,22,69,283,150,69,192,384,265⟩⟩]⟩
theorem node595 : UpperPrefix a [3,4,6,8,7,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,0] 30 cert595 (by decide +kernel)

def cert596 : Leaf := ⟨⟨372,352,0,100,324,388,302,108,100⟩,[(2,6)],[(4,1,0),(0,6,2)],⟨11,22,69,280,176,98,193,420,300⟩,⟨11,22,69,280,176,98,193,384,264⟩,[⟨1,1361518440643065168265217,⟨9,28,69,280,440,508,197,384,264⟩⟩,⟨7,1435600564840879686165563,⟨11,287,69,283,319,367,69,256,265⟩⟩,⟨3,1210107567680785977756673,⟨3,54,119,272,178,118,247,384,256⟩⟩]⟩
theorem node596 : UpperPrefix a [3,4,6,8,7,1,0] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,0] 30 cert596 (by decide +kernel)

def cert597 : Leaf := ⟨⟨48,105,42,35,11,141,43,43,35⟩,[],[(4,1,0),(2,6,5)],⟨11,22,69,280,176,98,196,417,297⟩,⟨11,22,69,280,176,98,196,384,264⟩,[⟨8,1184347566732655836425,⟨47,118,119,127,246,114,246,247,47⟩⟩,⟨6,1437222725400064812909603,⟨11,415,5,408,441,443,132,384,264⟩⟩,⟨7,1435600564840879669388347,⟨11,287,69,283,319,367,68,256,265⟩⟩]⟩
theorem node597 : UpperPrefix a [3,4,6,8,7,1,2] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,2] 30 cert597 (by decide +kernel)

def cert598 : Leaf := ⟨⟨404,393,394,135,0,397,0,15,135⟩,[(4,6),(6,4)],[(4,1,0)],⟨11,22,69,280,176,98,224,389,269⟩,⟨11,22,69,280,176,98,224,384,264⟩,[⟨5,1447277352713637925495867,⟨395,415,197,411,415,463,453,384,265⟩⟩,⟨6,1238495951498388249250855,⟨395,415,415,280,185,443,185,384,264⟩⟩]⟩
theorem node598 : UpperPrefix a [3,4,6,8,7,1,5] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,1,5] 30 cert598 (by decide +kernel)

theorem node599 : UpperPrefix a [3,4,6,8,7,1] 30 :=
  branch_upper a [3,4,6,8,7,1] 30 (by decide) (fin9_cases _
  node596
  (invalid_upper a [3,4,6,8,7,1,1] 30 (by decide +kernel))
  node597
  (invalid_upper a [3,4,6,8,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,4] 30 (by decide +kernel))
  node598
  (invalid_upper a [3,4,6,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,1,8] 30 (by decide +kernel)))

def cert600 : Local := ⟨⟨436,424,0,166,270,0,302,46,166⟩,[(2,6),(5,2)],[(4,1,0),(6,2,5),(0,6,2),(0,6,5)]⟩
theorem node600 : UpperPrefix a [3,4,6,8,7,2,0] 30 :=
  local_sound a [3,4,6,8,7,2,0] 30 cert600 (by decide +kernel)

def cert601 : Leaf := ⟨⟨52,41,42,37,13,0,45,45,37⟩,[(5,2)],[(4,1,0),(6,2,5),(1,6,2)],⟨11,22,69,280,176,100,194,417,297⟩,⟨11,22,69,280,176,100,194,384,264⟩,[⟨7,1596161027650984925471835,⟨267,319,357,283,319,357,367,256,265⟩⟩,⟨8,1184347566732655852809,⟨47,118,119,127,246,118,246,247,47⟩⟩]⟩
theorem node601 : UpperPrefix a [3,4,6,8,7,2,1] 30 :=
  Boolean.leaf_sound a [3,4,6,8,7,2,1] 30 cert601 (by decide +kernel)

def cert602 : Local := ⟨⟨436,425,426,167,0,0,0,47,167⟩,[(4,6),(5,2),(6,4)],[(4,1,0),(6,2,5)]⟩
theorem node602 : UpperPrefix a [3,4,6,8,7,2,5] 30 :=
  local_sound a [3,4,6,8,7,2,5] 30 cert602 (by decide +kernel)

theorem node603 : UpperPrefix a [3,4,6,8,7,2] 30 :=
  branch_upper a [3,4,6,8,7,2] 30 (by decide) (fin9_cases _
  node600
  node601
  (invalid_upper a [3,4,6,8,7,2,2] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,4] 30 (by decide +kernel))
  node602
  (invalid_upper a [3,4,6,8,7,2,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,2,8] 30 (by decide +kernel)))

theorem node604 : UpperPrefix a [3,4,6,8,7] 30 :=
  branch_upper a [3,4,6,8,7] 30 (by decide) (fin9_cases _
  node595
  node599
  node603
  (invalid_upper a [3,4,6,8,7,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,7,8] 30 (by decide +kernel)))

theorem node605 : UpperPrefix a [3,4,6,8] 30 :=
  branch_upper a [3,4,6,8] 30 (by decide) (fin9_cases _
  node583
  node590
  node594
  (invalid_upper a [3,4,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,8,6] 30 (by decide +kernel))
  node604
  (invalid_upper a [3,4,6,8,8] 30 (by decide +kernel)))

theorem node606 : UpperPrefix a [3,4,6] 30 :=
  branch_upper a [3,4,6] 30 (by decide) (fin9_cases _
  node499
  node513
  node524
  (invalid_upper a [3,4,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,6,4] 30 (by decide +kernel))
  node538
  (invalid_upper a [3,4,6,6] 30 (by decide +kernel))
  node579
  node605)

def cert607 : Leaf := ⟨⟨112,104,104,98,76,136,296,104,96⟩,[],[(4,1,0),(7,2,5),(1,4,3),(2,5,4)],⟨11,22,133,25,50,100,480,480,360⟩,⟨11,22,133,25,50,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,50,246,192,384,264⟩⟩,⟨8,1181747927634712511603,⟨11,31,133,25,59,127,255,128,8⟩⟩]⟩
theorem node607 : UpperPrefix a [3,4,7,0,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,0,1,2] 30 cert607 (by decide +kernel)

def cert608 : Leaf := ⟨⟨368,360,360,354,332,12,0,104,100⟩,[(6,2)],[(4,1,0),(7,2,6),(1,4,3)],⟨11,22,133,25,50,352,196,480,360⟩,⟨11,22,133,25,50,352,196,384,264⟩,[⟨0,1215171304801475981511680,⟨506,246,502,440,242,498,246,384,264⟩⟩,⟨2,1210402713189033453814803,⟨11,27,129,25,187,480,192,384,264⟩⟩]⟩
theorem node608 : UpperPrefix a [3,4,7,0,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,0,1,8,2] 30 cert608 (by decide +kernel)

def cert609 : Leaf := ⟨⟨148,136,8,134,140,140,268,77,229⟩,[],[(4,1,0),(1,4,3),(8,5,6)],⟨11,22,133,25,50,352,224,452,332⟩,⟨11,22,133,25,50,352,224,384,264⟩,[⟨5,1210402712063133594170651,⟨11,31,133,31,159,453,196,389,267⟩⟩,⟨6,1210106412368959466685555,⟨11,31,133,25,59,319,191,384,264⟩⟩,⟨0,1210109947688329443019776,⟨10,86,246,24,50,352,224,480,264⟩⟩]⟩
theorem node609 : UpperPrefix a [3,4,7,0,1,8,5] 30 :=
  Boolean.leaf_sound a [3,4,7,0,1,8,5] 30 cert609 (by decide +kernel)

theorem node610 : UpperPrefix a [3,4,7,0,1,8] 30 :=
  branch_upper a [3,4,7,0,1,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,1,8,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,8,1] 30 (by decide +kernel))
  node608
  (invalid_upper a [3,4,7,0,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,8,4] 30 (by decide +kernel))
  node609
  (invalid_upper a [3,4,7,0,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,8,8] 30 (by decide +kernel)))

theorem node611 : UpperPrefix a [3,4,7,0,1] 30 :=
  branch_upper a [3,4,7,0,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,1] 30 (by decide +kernel))
  node607
  (invalid_upper a [3,4,7,0,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,1,7] 30 (by decide +kernel))
  node610)

def cert612 : Leaf := ⟨⟨272,0,362,258,458,394,298,106,226⟩,[(1,4)],[(4,1,0),(2,4,1)],⟨11,22,133,25,52,354,482,482,362⟩,⟨11,22,133,25,52,96,192,384,264⟩,[⟨0,1252729002111147382418432,⟨506,246,502,506,246,96,192,384,488⟩⟩,⟨5,1210107564157954195203099,⟨11,31,133,27,31,64,192,384,265⟩⟩,⟨6,1210106412362349495198747,⟨11,31,133,27,63,32,128,384,265⟩⟩,⟨7,1208926973663136690742299,⟨11,31,5,27,63,96,64,256,265⟩⟩]⟩
theorem node612 : UpperPrefix a [3,4,7,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,0,2] 30 cert612 (by decide +kernel)

def cert613 : Leaf := ⟨⟨16,169,42,2,0,141,303,47,167⟩,[(4,5)],[(4,1,0),(6,4,4)],⟨11,22,133,25,112,98,484,420,300⟩,⟨11,22,133,25,112,98,192,384,264⟩,[⟨8,1181748490584665941115,⟨11,63,133,59,127,127,255,128,9⟩⟩,⟨2,1210107565286057419211811,⟨11,27,129,25,121,123,192,384,264⟩⟩,⟨5,1210107564157954195194915,⟨11,31,133,25,89,75,192,384,264⟩⟩,⟨7,1208926973665340008956963,⟨11,31,5,25,121,123,64,256,264⟩⟩]⟩
theorem node613 : UpperPrefix a [3,4,7,0,6,1] 30 :=
  Boolean.leaf_sound a [3,4,7,0,6,1] 30 cert613 (by decide +kernel)

def cert614 : Leaf := ⟨⟨52,40,42,38,0,138,302,46,38⟩,[(4,5)],[(4,1,0),(7,2,5),(6,4,4)],⟨11,22,133,25,112,100,482,418,298⟩,⟨11,22,133,25,112,100,192,384,264⟩,[⟨0,1214876138912684444765184,⟨506,246,502,472,114,246,192,384,264⟩⟩,⟨8,1181748490584665941115,⟨11,63,133,59,127,127,255,128,9⟩⟩]⟩
theorem node614 : UpperPrefix a [3,4,7,0,6,2] 30 :=
  Boolean.leaf_sound a [3,4,7,0,6,2] 30 cert614 (by decide +kernel)

def cert615 : Leaf := ⟨⟨144,137,10,130,0,143,301,47,167⟩,[(4,5)],[(4,1,0),(6,4,4)],⟨11,22,133,25,112,352,194,420,300⟩,⟨11,22,133,25,112,352,194,384,264⟩,[⟨5,1210107564157954211980379,⟨11,31,133,27,95,325,207,384,265⟩⟩,⟨8,1181745671428262356091,⟨11,31,133,27,127,127,207,128,9⟩⟩,⟨2,1210107565286057419211843,⟨11,27,129,25,121,377,203,384,264⟩⟩]⟩
theorem node615 : UpperPrefix a [3,4,7,0,6,8,1] 30 :=
  Boolean.leaf_sound a [3,4,7,0,6,8,1] 30 cert615 (by decide +kernel)

def cert616 : Local := ⟨⟨308,297,298,294,0,15,0,47,39⟩,[(4,5),(6,2)],[(4,1,0),(7,2,6),(6,4,4)]⟩
theorem node616 : UpperPrefix a [3,4,7,0,6,8,2] 30 :=
  local_sound a [3,4,7,0,6,8,2] 30 cert616 (by decide +kernel)

def cert617 : Local := ⟨⟨148,137,10,134,0,143,271,15,135⟩,[(4,5)],[(4,1,0),(6,4,4),(8,5,6),(5,6,4)]⟩
theorem node617 : UpperPrefix a [3,4,7,0,6,8,5] 30 :=
  local_sound a [3,4,7,0,6,8,5] 30 cert617 (by decide +kernel)

theorem node618 : UpperPrefix a [3,4,7,0,6,8] 30 :=
  branch_upper a [3,4,7,0,6,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,6,8,0] 30 (by decide +kernel))
  node615
  node616
  (invalid_upper a [3,4,7,0,6,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,6,8,4] 30 (by decide +kernel))
  node617
  (invalid_upper a [3,4,7,0,6,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,6,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,6,8,8] 30 (by decide +kernel)))

theorem node619 : UpperPrefix a [3,4,7,0,6] 30 :=
  branch_upper a [3,4,7,0,6] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,6,0] 30 (by decide +kernel))
  node613
  node614
  (invalid_upper a [3,4,7,0,6,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,6,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,6,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,6,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,6,7] 30 (by decide +kernel))
  node618)

def cert620 : Leaf := ⟨⟨368,360,362,354,74,268,0,106,98⟩,[(6,2)],[(4,1,0),(7,2,6),(2,6,5)],⟨11,22,133,25,304,98,196,480,360⟩,⟨11,22,133,25,304,98,196,384,264⟩,[⟨0,1214876159212280433642496,⟨506,246,502,440,304,98,246,384,280⟩⟩]⟩
theorem node620 : UpperPrefix a [3,4,7,0,8,1,2] 30 :=
  Boolean.leaf_sound a [3,4,7,0,8,1,2] 30 cert620 (by decide +kernel)

def cert621 : Leaf := ⟨⟨404,392,264,390,206,396,268,8,196⟩,[],[(4,1,0)],⟨11,22,133,25,304,98,224,388,328⟩,⟨11,22,133,25,304,98,224,388,264⟩,[⟨0,1214869246195648512986112,⟨378,246,502,312,304,98,242,502,280⟩⟩,⟨5,1364617492519345532187963,⟨15,159,133,159,415,463,453,389,399⟩⟩,⟨6,1212615169556374118479163,⟨15,159,133,159,447,47,165,389,399⟩⟩,⟨1,1250330978966951517487105,⟨397,84,133,477,496,96,224,388,396⟩⟩]⟩
theorem node621 : UpperPrefix a [3,4,7,0,8,1,5,2] 30 :=
  Boolean.leaf_sound a [3,4,7,0,8,1,5,2] 30 cert621 (by decide +kernel)

def cert622 : Leaf := ⟨⟨400,385,258,386,135,385,259,3,135⟩,[],[(4,1,0),(6,7,6)],⟨11,22,133,25,304,98,224,448,268⟩,⟨11,22,133,25,304,98,224,448,264⟩,[⟨3,1212623795066760735104001,⟨103,246,247,247,498,98,240,498,502⟩⟩,⟨5,1484890263879931738993979,⟨267,287,133,287,415,463,453,453,267⟩⟩,⟨2,1212616863015387000734755,⟨107,251,225,249,505,107,225,448,456⟩⟩]⟩
theorem node622 : UpperPrefix a [3,4,7,0,8,1,5,6] 30 :=
  Boolean.leaf_sound a [3,4,7,0,8,1,5,6] 30 cert622 (by decide +kernel)

theorem node623 : UpperPrefix a [3,4,7,0,8,1,5] 30 :=
  branch_upper a [3,4,7,0,8,1,5] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,8,1,5,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,5,1] 30 (by decide +kernel))
  node621
  (invalid_upper a [3,4,7,0,8,1,5,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,5,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,5,5] 30 (by decide +kernel))
  node622
  (invalid_upper a [3,4,7,0,8,1,5,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,5,8] 30 (by decide +kernel)))

theorem node624 : UpperPrefix a [3,4,7,0,8,1] 30 :=
  branch_upper a [3,4,7,0,8,1] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,8,1,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,1] 30 (by decide +kernel))
  node620
  (invalid_upper a [3,4,7,0,8,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,4] 30 (by decide +kernel))
  node623
  (invalid_upper a [3,4,7,0,8,1,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,1,8] 30 (by decide +kernel)))

def cert625 : Leaf := ⟨⟨272,352,354,258,70,386,294,102,102⟩,[],[(4,1,0),(7,2,5)],⟨11,22,133,25,304,100,226,482,362⟩,⟨11,22,133,25,304,100,192,384,264⟩,[⟨0,1215024613582863133068288,⟨506,246,502,472,498,246,192,384,264⟩⟩,⟨3,1212623790000211154312193,⟨103,246,247,247,498,102,208,498,502⟩⟩,⟨2,1210107565283851953505283,⟨11,27,129,25,304,96,192,384,264⟩⟩,⟨5,1210107564157952047711235,⟨11,31,133,25,272,68,192,384,264⟩⟩,⟨6,1210106412362347347706883,⟨11,31,133,25,304,36,128,384,264⟩⟩]⟩
theorem node625 : UpperPrefix a [3,4,7,0,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,0,8,2] 30 cert625 (by decide +kernel)

theorem node626 : UpperPrefix a [3,4,7,0,8] 30 :=
  branch_upper a [3,4,7,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,8,0] 30 (by decide +kernel))
  node624
  node625
  (invalid_upper a [3,4,7,0,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,8,8] 30 (by decide +kernel)))

theorem node627 : UpperPrefix a [3,4,7,0] 30 :=
  branch_upper a [3,4,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,0,0] 30 (by decide +kernel))
  node611
  node612
  (invalid_upper a [3,4,7,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,0,5] 30 (by decide +kernel))
  node619
  (invalid_upper a [3,4,7,0,7] 30 (by decide +kernel))
  node626)

def cert628 : Local := ⟨⟨0,361,360,0,332,392,300,108,100⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(7,2,5),(1,3,0),(0,4,1)]⟩
theorem node628 : UpperPrefix a [3,4,7,1,0,2] 30 :=
  local_sound a [3,4,7,1,0,2] 30 cert628 (by decide +kernel)

def cert629 : Local := ⟨⟨0,489,360,0,460,140,300,108,228⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(0,4,1)]⟩
theorem node629 : UpperPrefix a [3,4,7,1,0,8] 30 :=
  local_sound a [3,4,7,1,0,8] 30 cert629 (by decide +kernel)

theorem node630 : UpperPrefix a [3,4,7,1,0] 30 :=
  branch_upper a [3,4,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [3,4,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,0,1] 30 (by decide +kernel))
  node628
  (invalid_upper a [3,4,7,1,0,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,0,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,0,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,0,7] 30 (by decide +kernel))
  node629)

def cert631 : Local := ⟨⟨0,0,360,0,457,393,297,105,225⟩,[(0,3),(1,4),(3,1)],[(4,1,0),(4,1,3),(1,3,0),(2,4,1),(2,4,3)]⟩
theorem node631 : UpperPrefix a [3,4,7,1,2] 30 :=
  local_sound a [3,4,7,1,2] 30 cert631 (by decide +kernel)

def cert632 : Local := ⟨⟨0,425,296,0,0,397,301,45,165⟩,[(0,3),(3,1),(4,5)],[(4,1,0),(4,1,3),(1,3,0),(6,4,4)]⟩
theorem node632 : UpperPrefix a [3,4,7,1,6] 30 :=
  local_sound a [3,4,7,1,6] 30 cert632 (by decide +kernel)

def cert633 : Leaf := ⟨⟨0,489,360,0,205,132,37,109,229⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(1,3,0)],⟨11,22,133,26,304,97,228,484,364⟩,⟨11,22,133,26,304,97,192,384,264⟩,[⟨3,1210107637482182138659841,⟨3,118,229,18,304,97,192,384,256⟩⟩,⟨8,1181817937923050308619,⟨43,127,229,59,48,97,192,128,9⟩⟩]⟩
theorem node633 : UpperPrefix a [3,4,7,1,8,0] 30 :=
  Boolean.leaf_sound a [3,4,7,1,8,0] 30 cert633 (by decide +kernel)

def cert634 : Leaf := ⟨⟨0,361,360,0,77,385,293,109,101⟩,[(0,3),(3,1)],[(4,1,0),(4,1,3),(7,2,5),(1,3,0)],⟨11,22,133,26,304,100,225,481,361⟩,⟨11,22,133,26,304,100,192,384,264⟩,[⟨3,1210107637552550882837505,⟨35,118,229,50,304,100,192,384,256⟩⟩]⟩
theorem node634 : UpperPrefix a [3,4,7,1,8,2] 30 :=
  Boolean.leaf_sound a [3,4,7,1,8,2] 30 cert634 (by decide +kernel)

theorem node635 : UpperPrefix a [3,4,7,1,8] 30 :=
  branch_upper a [3,4,7,1,8] 30 (by decide) (fin9_cases _
  node633
  (invalid_upper a [3,4,7,1,8,1] 30 (by decide +kernel))
  node634
  (invalid_upper a [3,4,7,1,8,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,8,6] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,8,7] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,8,8] 30 (by decide +kernel)))

theorem node636 : UpperPrefix a [3,4,7,1] 30 :=
  branch_upper a [3,4,7,1] 30 (by decide) (fin9_cases _
  node630
  (invalid_upper a [3,4,7,1,1] 30 (by decide +kernel))
  node631
  (invalid_upper a [3,4,7,1,3] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [3,4,7,1,5] 30 (by decide +kernel))
  node632
  (invalid_upper a [3,4,7,1,7] 30 (by decide +kernel))
  node635)

def cert637 : Leaf := ⟨⟨20,0,10,0,459,395,299,107,227⟩,[(1,3),(3,1)],[(4,1,0),(2,3,0)],⟨11,22,133,28,371,355,483,483,363⟩,⟨11,22,133,28,48,96,192,384,264⟩,[⟨5,1210107564157952081270027,⟨11,31,133,31,16,64,196,389,267⟩⟩,⟨6,1210106412362347381265675,⟨11,31,133,31,48,32,132,389,267⟩⟩,⟨8,1181745669222813406475,⟨11,31,133,31,48,96,196,133,11⟩⟩,⟨7,1208926973663134543254795,⟨11,31,5,31,48,96,64,257,267⟩⟩]⟩
theorem node637 : UpperPrefix a [3,4,7,2] 30 :=
  Boolean.leaf_sound a [3,4,7,2] 30 cert637 (by decide +kernel)

def cert638 : Leaf := ⟨⟨212,201,72,0,206,140,268,76,196⟩,[(3,4)],[(4,1,0),(5,3,3),(0,4,1),(1,5,4)],⟨11,22,133,56,49,98,452,452,332⟩,⟨11,22,133,56,49,98,192,384,264⟩,[⟨8,1181747928184199890043,⟨27,31,133,59,59,127,255,128,25⟩⟩]⟩
theorem node638 : UpperPrefix a [3,4,7,5,0,1] 30 :=
  Boolean.leaf_sound a [3,4,7,5,0,1] 30 cert638 (by decide +kernel)

def cert639 : Leaf := ⟨⟨84,73,74,0,78,138,270,78,70⟩,[(3,4)],[(4,1,0),(7,2,5),(5,3,3),(0,4,1)],⟨11,22,133,56,49,100,450,450,330⟩,⟨11,22,133,56,49,100,192,384,264⟩,[⟨8,1181747928184199890043,⟨27,31,133,59,59,127,255,128,25⟩⟩]⟩
theorem node639 : UpperPrefix a [3,4,7,5,0,2] 30 :=
  Boolean.leaf_sound a [3,4,7,5,0,2] 30 cert639 (by decide +kernel)

#print axioms node639
end Delivery.FiniteExclusion.Sharp3x6
