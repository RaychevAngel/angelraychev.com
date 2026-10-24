import RegularNineSharp2x7Base
import RegularNineSharp2x7C007
import RegularNineSharp2x7C008
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert576 : Leaf := ⟨⟨112,100,0,327,71,151,7,71,67⟩,[(2,5)],[(7,3,5),(8,4,3),(3,5,2)],⟨7,19,44,152,304,104,195,451,327⟩,⟨7,19,44,152,304,104,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,152,272,72,192,384,260⟩⟩,⟨4,1214857655924927920866305,⟨455,451,44,136,292,108,192,384,260⟩⟩]⟩
theorem node576 : UpperPrefix a [2,4,5,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,7,8,3] 30 cert576 (by decide +kernel)

theorem node577 : UpperPrefix a [2,4,5,7,8] 30 :=
  branch_upper a [2,4,5,7,8] 30 (by decide) (fin9_cases _
  node568
  node575
  (invalid_upper a [2,4,5,7,8,2] 30 (by decide +kernel))
  node576
  (invalid_upper a [2,4,5,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,8,8] 30 (by decide +kernel)))

theorem node578 : UpperPrefix a [2,4,5,7] 30 :=
  branch_upper a [2,4,5,7] 30 (by decide) (fin9_cases _
  node544
  node552
  (invalid_upper a [2,4,5,7,2] 30 (by decide +kernel))
  node553
  (invalid_upper a [2,4,5,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,7,5] 30 (by decide +kernel))
  node561
  (invalid_upper a [2,4,5,7,7] 30 (by decide +kernel))
  node577)

def cert579 : Leaf := ⟨⟨48,0,466,6,6,410,282,90,218⟩,[(1,4)],[(0,4,1)],⟨7,19,44,280,49,234,202,458,462⟩,⟨7,19,44,280,49,96,192,384,260⟩,[⟨5,1215079448074578675377153,⟨463,475,204,474,475,64,192,384,260⟩⟩,⟨2,1210181496656809575851009,⟨3,19,232,506,51,96,192,384,256⟩⟩,⟨6,1210106412362656317062917,⟨23,19,63,283,51,32,128,395,287⟩⟩,⟨7,1208926973663443512606469,⟨23,19,63,283,51,96,64,267,287⟩⟩,⟨3,1210107565284125490429701,⟨23,19,55,275,51,96,192,387,279⟩⟩,⟨8,1181745669497389465349,⟨23,19,63,27,51,96,192,131,23⟩⟩]⟩
theorem node579 : UpperPrefix a [2,4,5,8,0] 30 :=
  Boolean.leaf_sound a [2,4,5,8,0] 30 cert579 (by decide +kernel)

def cert580 : Leaf := ⟨⟨440,424,464,128,393,392,264,72,200⟩,[],[(1,4,1),(0,5,4)],⟨7,19,44,280,50,97,200,456,460⟩,⟨7,19,44,280,50,97,192,384,260⟩,[⟨2,1212549669241289892185601,⟨115,51,250,472,50,115,192,456,472⟩⟩,⟨4,1229107927886639498527745,⟨487,35,492,456,34,97,192,384,452⟩⟩,⟨5,1233858305599206889358337,⟨463,475,460,472,218,449,192,384,452⟩⟩,⟨6,1210106412364855340326661,⟨23,19,63,283,50,51,128,395,287⟩⟩]⟩
theorem node580 : UpperPrefix a [2,4,5,8,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,8,1,0] 30 cert580 (by decide +kernel)

def cert581 : Leaf := ⟨⟨416,420,0,133,389,389,261,69,193⟩,[(2,5)],[(1,4,1),(3,5,2)],⟨7,19,44,280,50,104,193,449,453⟩,⟨7,19,44,280,50,104,192,384,260⟩,[⟨4,1328416245210460615345169,⟨487,451,492,493,487,492,192,384,292⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,280,218,72,192,384,260⟩⟩,⟨6,1210106412364855348723509,⟨23,19,63,283,55,63,128,395,287⟩⟩]⟩
theorem node581 : UpperPrefix a [2,4,5,8,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,8,1,3] 30 cert581 (by decide +kernel)

def cert582 : Leaf := ⟨⟨304,292,337,5,261,0,285,93,89⟩,[(5,6)],[(1,4,1),(7,5,5)],⟨7,19,44,280,50,224,201,457,333⟩,⟨7,19,44,280,50,224,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,280,218,192,192,384,260⟩⟩,⟨6,1210106412362656317054725,⟨23,19,63,283,50,160,128,395,287⟩⟩,⟨3,1210107567535925304106757,⟨23,19,55,275,50,224,224,387,279⟩⟩]⟩
theorem node582 : UpperPrefix a [2,4,5,8,1,7] 30 :=
  Boolean.leaf_sound a [2,4,5,8,1,7] 30 cert582 (by decide +kernel)

theorem node583 : UpperPrefix a [2,4,5,8,1] 30 :=
  branch_upper a [2,4,5,8,1] 30 (by decide) (fin9_cases _
  node580
  (invalid_upper a [2,4,5,8,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,1,2] 30 (by decide +kernel))
  node581
  (invalid_upper a [2,4,5,8,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,1,6] 30 (by decide +kernel))
  node582
  (invalid_upper a [2,4,5,8,1,8] 30 (by decide +kernel)))

def cert584 : Leaf := ⟨⟨232,236,0,199,0,135,7,71,195⟩,[(2,4),(4,2)],[],⟨7,19,44,280,56,227,195,451,455⟩,⟨7,19,44,280,56,96,192,384,260⟩,[⟨4,1224302388996220323365891,⟨487,487,44,268,44,96,192,384,260⟩⟩,⟨3,1214857656031579466630145,⟨487,499,36,272,48,96,192,384,260⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,280,24,64,192,384,260⟩⟩,⟨8,1184056016106234724127,⟨23,23,63,31,63,96,224,227,23⟩⟩]⟩
theorem node584 : UpperPrefix a [2,4,5,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,8,3] 30 cert584 (by decide +kernel)

def cert585 : Leaf := ⟨⟨48,36,402,134,0,414,286,30,154⟩,[(4,5)],[(6,4,4)],⟨7,19,44,280,112,97,202,394,398⟩,⟨7,19,44,280,112,97,192,384,260⟩,[⟨0,1224302388893970313774080,⟨462,478,60,284,124,508,192,384,260⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,280,80,449,192,384,260⟩⟩,⟨3,1210107565286049635654917,⟨7,19,55,275,114,115,192,385,263⟩⟩,⟨7,1208926973665333298093317,⟨7,19,63,283,114,115,64,257,263⟩⟩,⟨8,1181745671421534690565,⟨7,19,63,27,114,115,192,129,7⟩⟩]⟩
theorem node585 : UpperPrefix a [2,4,5,8,6,0] 30 :=
  Boolean.leaf_sound a [2,4,5,8,6,0] 30 cert585 (by decide +kernel)

def cert586 : Leaf := ⟨⟨48,36,401,133,0,413,285,29,153⟩,[(4,5)],[(6,4,4)],⟨7,19,44,280,112,98,201,393,397⟩,⟨7,19,44,280,112,98,192,384,260⟩,[⟨1,1224302388893970313773057,⟨461,477,60,284,124,508,192,384,260⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,280,80,202,192,384,260⟩⟩,⟨3,1210107565286049635638533,⟨7,19,55,275,112,114,192,385,263⟩⟩,⟨7,1208926973665333298076933,⟨7,19,63,283,112,114,64,257,263⟩⟩,⟨8,1181745671421534674181,⟨7,19,63,27,112,114,192,129,7⟩⟩]⟩
theorem node586 : UpperPrefix a [2,4,5,8,6,1] 30 :=
  Boolean.leaf_sound a [2,4,5,8,6,1] 30 cert586 (by decide +kernel)

def cert587 : Leaf := ⟨⟨432,420,0,135,0,407,263,7,131⟩,[(2,5),(4,5)],[(6,4,4),(3,5,2)],⟨7,19,44,280,112,104,195,387,391⟩,⟨7,19,44,280,112,104,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,280,80,72,192,384,260⟩⟩,⟨4,1214857655924927920866305,⟨455,451,44,264,100,108,192,384,260⟩⟩]⟩
theorem node587 : UpperPrefix a [2,4,5,8,6,3] 30 :=
  Boolean.leaf_sound a [2,4,5,8,6,3] 30 cert587 (by decide +kernel)

def cert588 : Leaf := ⟨⟨312,300,275,7,0,0,287,31,27⟩,[(4,5),(5,6)],[(6,4,4),(7,5,4),(7,5,5)],⟨7,19,44,280,112,224,203,395,271⟩,⟨7,19,44,280,112,224,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,280,80,192,192,384,260⟩⟩]⟩
theorem node588 : UpperPrefix a [2,4,5,8,6,7] 30 :=
  Boolean.leaf_sound a [2,4,5,8,6,7] 30 cert588 (by decide +kernel)

theorem node589 : UpperPrefix a [2,4,5,8,6] 30 :=
  branch_upper a [2,4,5,8,6] 30 (by decide) (fin9_cases _
  node585
  node586
  (invalid_upper a [2,4,5,8,6,2] 30 (by decide +kernel))
  node587
  (invalid_upper a [2,4,5,8,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,6,6] 30 (by decide +kernel))
  node588
  (invalid_upper a [2,4,5,8,6,8] 30 (by decide +kernel)))

def cert590 : Leaf := ⟨⟨240,224,208,224,64,146,48,120,248⟩,[],[(1,6,5)],⟨7,19,44,280,176,97,194,456,332⟩,⟨7,19,44,280,176,97,194,384,260⟩,[⟨0,1376303560061649075307520,⟨478,478,444,284,444,508,458,392,284⟩⟩,⟨2,1212542895899811935962625,⟨115,115,250,472,242,115,242,392,472⟩⟩,⟨8,1182034255840432641037,⟨39,115,47,127,242,115,242,128,5⟩⟩,⟨3,1210107853588993554793477,⟨39,115,39,336,242,115,242,384,261⟩⟩]⟩
theorem node590 : UpperPrefix a [2,4,5,8,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,0,1] 30 cert590 (by decide +kernel)

def cert591 : Leaf := ⟨⟨56,44,80,36,12,28,308,60,120⟩,[],[(8,3,6)],⟨7,19,44,280,176,97,200,386,324⟩,⟨7,19,44,280,176,97,200,386,260⟩,[⟨0,1507647548400289379779584,⟨462,478,380,348,508,508,456,458,268⟩⟩,⟨1,2390701780153841424793601,⟨301,381,300,348,508,365,476,508,260⟩⟩,⟨7,1662274158270422197482591,⟨7,31,303,287,319,357,367,259,261⟩⟩,⟨6,1212541382580385977868037,⟨23,19,191,411,176,35,138,395,415⟩⟩]⟩
theorem node591 : UpperPrefix a [2,4,5,8,7,0,3,1] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,0,3,1] 30 cert591 (by decide +kernel)

def cert592 : Leaf := ⟨⟨176,160,146,162,66,146,306,50,178⟩,[],[(8,3,6),(6,7,4)],⟨7,19,44,280,176,97,200,448,262⟩,⟨7,19,44,280,176,97,200,448,260⟩,[⟨0,1227040505410126909277184,⟨478,478,252,476,252,508,200,456,476⟩⟩,⟨2,1212549669238884710483457,⟨115,51,248,472,240,99,200,456,472⟩⟩,⟨3,1234014550122645859557125,⟨279,275,439,275,178,499,242,499,279⟩⟩]⟩
theorem node592 : UpperPrefix a [2,4,5,8,7,0,3,6] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,0,3,6] 30 cert592 (by decide +kernel)

theorem node593 : UpperPrefix a [2,4,5,8,7,0,3] 30 :=
  branch_upper a [2,4,5,8,7,0,3] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,8,7,0,3,0] 30 (by decide +kernel))
  node591
  (invalid_upper a [2,4,5,8,7,0,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,3,5] 30 (by decide +kernel))
  node592
  (invalid_upper a [2,4,5,8,7,0,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,3,8] 30 (by decide +kernel)))

theorem node594 : UpperPrefix a [2,4,5,8,7,0] 30 :=
  branch_upper a [2,4,5,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,8,7,0,0] 30 (by decide +kernel))
  node590
  (invalid_upper a [2,4,5,8,7,0,2] 30 (by decide +kernel))
  node593
  (invalid_upper a [2,4,5,8,7,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,0,8] 30 (by decide +kernel)))

def cert595 : Leaf := ⟨⟨248,232,208,224,72,153,60,0,248⟩,[(7,3)],[(8,3,7),(0,6,5)],⟨7,19,44,280,176,98,193,392,324⟩,⟨7,19,44,280,176,98,193,392,260⟩,[⟨1,1378922997720115831635969,⟨477,477,444,412,444,508,457,392,412⟩⟩,⟨2,1212542537758088443758081,⟨19,19,184,408,176,114,243,392,408⟩⟩]⟩
theorem node595 : UpperPrefix a [2,4,5,8,7,1,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,1,0,3] 30 cert595 (by decide +kernel)

def cert596 : Leaf := ⟨⟨304,292,272,36,324,405,308,52,56⟩,[],[(0,6,5),(6,7,4)],⟨7,19,44,280,176,98,193,448,268⟩,⟨7,19,44,280,176,98,193,448,260⟩,[⟨1,1508529821581999141289985,⟨477,477,444,284,444,508,457,456,284⟩⟩,⟨3,1212549686017946473963269,⟨119,51,247,499,242,114,243,499,503⟩⟩,⟨7,1506436062083924351792191,⟨271,287,303,287,319,367,321,320,261⟩⟩]⟩
theorem node596 : UpperPrefix a [2,4,5,8,7,1,0,6] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,1,0,6] 30 cert596 (by decide +kernel)

theorem node597 : UpperPrefix a [2,4,5,8,7,1,0] 30 :=
  branch_upper a [2,4,5,8,7,1,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,8,7,1,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,0,2] 30 (by decide +kernel))
  node595
  (invalid_upper a [2,4,5,8,7,1,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,0,5] 30 (by decide +kernel))
  node596
  (invalid_upper a [2,4,5,8,7,1,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,0,8] 30 (by decide +kernel)))

def cert598 : Leaf := ⟨⟨120,104,80,96,73,24,304,124,120⟩,[],[(2,0,7),(8,3,6)],⟨7,19,44,280,176,98,200,385,324⟩,⟨7,19,44,280,176,98,200,385,260⟩,[⟨1,1507645242557280166084609,⟨461,477,380,348,508,508,456,449,268⟩⟩,⟨7,1662274158270422197482623,⟨7,31,303,287,319,359,367,257,261⟩⟩,⟨0,1484005109591038433690624,⟨302,382,300,348,508,366,456,388,260⟩⟩]⟩
theorem node598 : UpperPrefix a [2,4,5,8,7,1,3,0] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,1,3,0] 30 cert598 (by decide +kernel)

def cert599 : Leaf := ⟨⟨56,40,17,33,73,25,305,57,57⟩,[],[(8,3,6),(6,7,4)],⟨7,19,44,280,176,98,200,448,261⟩,⟨7,19,44,280,176,98,200,448,260⟩,[⟨1,1227040505410126909276161,⟨477,477,252,476,252,508,200,456,476⟩⟩,⟨2,1212549669238884710483457,⟨115,51,248,472,240,98,200,456,472⟩⟩,⟨7,2413130429046696063284351,⟨271,287,303,287,319,367,367,357,261⟩⟩]⟩
theorem node599 : UpperPrefix a [2,4,5,8,7,1,3,6] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,1,3,6] 30 cert599 (by decide +kernel)

theorem node600 : UpperPrefix a [2,4,5,8,7,1,3] 30 :=
  branch_upper a [2,4,5,8,7,1,3] 30 (by decide) (fin9_cases _
  node598
  (invalid_upper a [2,4,5,8,7,1,3,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,3,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,3,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,3,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,3,5] 30 (by decide +kernel))
  node599
  (invalid_upper a [2,4,5,8,7,1,3,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,3,8] 30 (by decide +kernel)))

theorem node601 : UpperPrefix a [2,4,5,8,7,1] 30 :=
  branch_upper a [2,4,5,8,7,1] 30 (by decide) (fin9_cases _
  node597
  (invalid_upper a [2,4,5,8,7,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,2] 30 (by decide +kernel))
  node600
  (invalid_upper a [2,4,5,8,7,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,1,8] 30 (by decide +kernel)))

def cert602 : Leaf := ⟨⟨112,100,0,71,327,151,7,71,67⟩,[(2,5)],[(3,5,2)],⟨7,19,44,280,176,104,195,451,327⟩,⟨7,19,44,280,176,104,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,280,144,72,192,384,260⟩⟩,⟨7,1360042701114965081732159,⟨7,31,303,287,319,367,64,256,261⟩⟩,⟨8,1182034181073650332733,⟨7,83,47,127,247,111,192,128,5⟩⟩,⟨4,1214857655924927920866305,⟨455,451,44,264,164,108,192,384,260⟩⟩]⟩
theorem node602 : UpperPrefix a [2,4,5,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,5,8,7,3] 30 cert602 (by decide +kernel)

theorem node603 : UpperPrefix a [2,4,5,8,7] 30 :=
  branch_upper a [2,4,5,8,7] 30 (by decide) (fin9_cases _
  node594
  node601
  (invalid_upper a [2,4,5,8,7,2] 30 (by decide +kernel))
  node602
  (invalid_upper a [2,4,5,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,7,8] 30 (by decide +kernel)))

theorem node604 : UpperPrefix a [2,4,5,8] 30 :=
  branch_upper a [2,4,5,8] 30 (by decide) (fin9_cases _
  node579
  node583
  (invalid_upper a [2,4,5,8,2] 30 (by decide +kernel))
  node584
  (invalid_upper a [2,4,5,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,8,5] 30 (by decide +kernel))
  node589
  node603
  (invalid_upper a [2,4,5,8,8] 30 (by decide +kernel)))

theorem node605 : UpperPrefix a [2,4,5] 30 :=
  branch_upper a [2,4,5] 30 (by decide) (fin9_cases _
  node491
  node507
  (invalid_upper a [2,4,5,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,5] 30 (by decide +kernel))
  node538
  node578
  node604)

def cert606 : Leaf := ⟨⟨504,0,416,0,460,396,300,108,232⟩,[(1,3),(3,1)],[(1,4,1),(1,4,3)],⟨7,19,76,25,50,488,488,424,428⟩,⟨7,19,76,25,50,96,192,384,260⟩,[⟨0,1266886860137792986416128,⟨502,18,492,508,50,96,192,384,484⟩⟩,⟨4,1266886860136624755311617,⟨487,3,492,493,34,96,192,384,484⟩⟩]⟩
theorem node606 : UpperPrefix a [2,4,6,0,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,1] 30 cert606 (by decide +kernel)

def cert607 : Leaf := ⟨⟨496,0,418,0,454,390,294,102,226⟩,[(1,3),(3,1)],[],⟨7,19,76,25,56,482,482,418,422⟩,⟨7,19,76,25,56,96,192,384,260⟩,[⟨0,1214857656032130298283008,⟨486,498,92,508,60,96,192,384,260⟩⟩,⟨3,1233858019022494883648517,⟨487,499,487,499,242,96,192,384,485⟩⟩,⟨4,1214857656030481030841345,⟨487,483,76,493,44,96,192,384,260⟩⟩]⟩
theorem node607 : UpperPrefix a [2,4,6,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,0,3] 30 cert607 (by decide +kernel)

def cert608 : Leaf := ⟨⟨112,0,49,0,77,21,317,125,121⟩,[(1,3),(3,1)],[],⟨7,19,76,25,176,98,488,424,300⟩,⟨7,19,76,25,176,98,192,384,260⟩,[⟨1,1361519017103811289284609,⟨13,25,76,25,500,508,192,384,260⟩⟩,⟨7,1459212397395965383816245,⟨303,283,367,283,319,367,64,256,293⟩⟩,⟨8,1181748066173722885493,⟨47,27,127,27,191,127,255,129,47⟩⟩,⟨3,1210107565424588100736005,⟨39,19,103,19,176,98,192,384,293⟩⟩]⟩
theorem node608 : UpperPrefix a [2,4,6,0,7,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,1] 30 cert608 (by decide +kernel)

def cert609 : Leaf := ⟨⟨504,0,0,0,334,0,318,126,250⟩,[(1,3),(2,5),(3,1),(5,2)],[],⟨7,19,76,25,176,104,482,418,294⟩,⟨7,19,76,25,176,104,192,384,260⟩,[⟨0,1214839173575987646432256,⟨502,466,124,508,180,124,192,384,292⟩⟩]⟩
theorem node609 : UpperPrefix a [2,4,6,0,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,3] 30 cert609 (by decide +kernel)

def cert610 : Leaf := ⟨⟨248,0,176,0,332,156,60,124,248⟩,[(1,3),(3,1)],[(8,5,4)],⟨7,19,76,25,176,352,194,424,300⟩,⟨7,19,76,25,176,352,194,384,260⟩,[⟨0,1266886662033010573968384,⟨502,114,508,508,176,368,194,400,436⟩⟩,⟨1,1536587267689470760058881,⟨445,409,508,409,176,500,508,400,436⟩⟩]⟩
theorem node610 : UpperPrefix a [2,4,6,0,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,8,1] 30 cert610 (by decide +kernel)

def cert611 : Leaf := ⟨⟨112,0,0,0,327,23,55,119,115⟩,[(1,3),(2,6),(3,1)],[(8,5,4),(3,6,2)],⟨7,19,76,25,176,352,200,418,294⟩,⟨7,19,76,25,176,352,200,384,260⟩,[⟨7,1534770263373677381817413,⟨303,283,367,283,48,357,367,256,293⟩⟩]⟩
theorem node611 : UpperPrefix a [2,4,6,0,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,0,7,8,3] 30 cert611 (by decide +kernel)

def cert612 : Local := ⟨⟨248,0,179,0,0,159,0,127,251⟩,[(1,3),(3,1),(4,6),(6,4)],[(8,5,4),(8,5,6)]⟩
theorem node612 : UpperPrefix a [2,4,6,0,7,8,5] 30 :=
  local_sound a [2,4,6,0,7,8,5] 30 cert612 (by decide +kernel)

theorem node613 : UpperPrefix a [2,4,6,0,7,8] 30 :=
  branch_upper a [2,4,6,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,7,8,0] 30 (by decide +kernel))
  node610
  (invalid_upper a [2,4,6,0,7,8,2] 30 (by decide +kernel))
  node611
  (invalid_upper a [2,4,6,0,7,8,4] 30 (by decide +kernel))
  node612
  (invalid_upper a [2,4,6,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,8,8] 30 (by decide +kernel)))

theorem node614 : UpperPrefix a [2,4,6,0,7] 30 :=
  branch_upper a [2,4,6,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,7,0] 30 (by decide +kernel))
  node608
  (invalid_upper a [2,4,6,0,7,2] 30 (by decide +kernel))
  node609
  (invalid_upper a [2,4,6,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,7,7] 30 (by decide +kernel))
  node613)

def cert615 : Leaf := ⟨⟨112,0,49,0,69,21,317,125,249⟩,[(1,3),(3,1)],[],⟨7,19,76,25,304,98,232,424,428⟩,⟨7,19,76,25,304,98,192,384,260⟩,[⟨1,1361519017103811289284609,⟨13,25,76,25,500,508,192,384,260⟩⟩,⟨7,1208926976073317743801717,⟨47,27,111,27,319,111,111,283,319⟩⟩,⟨3,1210107567693980100670725,⟨39,19,103,19,307,98,226,403,311⟩⟩,⟨8,1181745809962424087605,⟨47,27,111,27,63,111,192,128,37⟩⟩]⟩
theorem node615 : UpperPrefix a [2,4,6,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,8,1] 30 cert615 (by decide +kernel)

def cert616 : Leaf := ⟨⟨504,0,0,0,206,0,318,126,250⟩,[(1,3),(2,5),(3,1),(5,2)],[],⟨7,19,76,25,304,104,226,418,422⟩,⟨7,19,76,25,304,104,192,384,260⟩,[⟨0,1214839173593579832476672,⟨502,466,124,508,308,124,192,400,308⟩⟩]⟩
theorem node616 : UpperPrefix a [2,4,6,0,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,0,8,3] 30 cert616 (by decide +kernel)

def cert617 : Leaf := ⟨⟨376,0,306,0,78,0,316,126,122⟩,[(1,3),(3,1),(5,6)],[(7,5,5)],⟨7,19,76,25,304,224,194,424,300⟩,⟨7,19,76,25,304,224,194,384,260⟩,[⟨0,1266886664284810387653632,⟨502,114,508,508,304,224,226,400,436⟩⟩]⟩
theorem node617 : UpperPrefix a [2,4,6,0,8,7,1] 30 :=
  Boolean.leaf_sound a [2,4,6,0,8,7,1] 30 cert617 (by decide +kernel)

def cert618 : Local := ⟨⟨368,0,0,0,71,0,311,119,115⟩,[(1,3),(2,6),(3,1),(5,6)],[(7,5,5),(3,6,2)]⟩
theorem node618 : UpperPrefix a [2,4,6,0,8,7,3] 30 :=
  local_sound a [2,4,6,0,8,7,3] 30 cert618 (by decide +kernel)

def cert619 : Local := ⟨⟨376,0,307,0,79,0,0,127,123⟩,[(1,3),(3,1),(5,6),(6,5)],[(7,5,5),(7,5,6)]⟩
theorem node619 : UpperPrefix a [2,4,6,0,8,7,5] 30 :=
  local_sound a [2,4,6,0,8,7,5] 30 cert619 (by decide +kernel)

theorem node620 : UpperPrefix a [2,4,6,0,8,7] 30 :=
  branch_upper a [2,4,6,0,8,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,8,7,0] 30 (by decide +kernel))
  node617
  (invalid_upper a [2,4,6,0,8,7,2] 30 (by decide +kernel))
  node618
  (invalid_upper a [2,4,6,0,8,7,4] 30 (by decide +kernel))
  node619
  (invalid_upper a [2,4,6,0,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,7,8] 30 (by decide +kernel)))

theorem node621 : UpperPrefix a [2,4,6,0,8] 30 :=
  branch_upper a [2,4,6,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,8,0] 30 (by decide +kernel))
  node615
  (invalid_upper a [2,4,6,0,8,2] 30 (by decide +kernel))
  node616
  (invalid_upper a [2,4,6,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,8,6] 30 (by decide +kernel))
  node620
  (invalid_upper a [2,4,6,0,8,8] 30 (by decide +kernel)))

theorem node622 : UpperPrefix a [2,4,6,0] 30 :=
  branch_upper a [2,4,6,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,0,0] 30 (by decide +kernel))
  node606
  (invalid_upper a [2,4,6,0,2] 30 (by decide +kernel))
  node607
  (invalid_upper a [2,4,6,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,0,6] 30 (by decide +kernel))
  node614
  node621)

def cert623 : Leaf := ⟨⟨488,0,416,0,460,396,300,108,232⟩,[(1,4),(3,1)],[(4,1,3),(0,4,1),(0,4,3)],⟨7,19,76,26,49,488,488,424,428⟩,⟨7,19,76,26,49,96,192,384,260⟩,[⟨1,1266886860137792986415105,⟨501,17,492,508,49,96,192,384,484⟩⟩]⟩
theorem node623 : UpperPrefix a [2,4,6,1,0] 30 :=
  Boolean.leaf_sound a [2,4,6,1,0] 30 cert623 (by decide +kernel)

def cert624 : Leaf := ⟨⟨104,108,33,0,69,389,293,101,225⟩,[(3,1)],[(4,1,3)],⟨7,19,76,26,56,481,481,417,421⟩,⟨7,19,76,26,56,96,192,384,260⟩,[⟨1,1214857656032130298281985,⟨485,497,92,252,60,96,192,384,260⟩⟩,⟨3,1214857656031579466630145,⟨487,499,68,242,48,96,192,384,260⟩⟩,⟨7,1208926973665340017374261,⟨15,27,79,27,63,127,64,256,261⟩⟩,⟨8,1181745671428253971509,⟨15,27,79,27,63,127,192,128,5⟩⟩]⟩
theorem node624 : UpperPrefix a [2,4,6,1,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,3] 30 cert624 (by decide +kernel)

def cert625 : Leaf := ⟨⟨224,228,0,0,71,134,39,103,227⟩,[(2,6),(3,1)],[(4,1,3),(3,6,2)],⟨7,19,76,26,176,97,200,416,292⟩,⟨7,19,76,26,176,97,200,384,260⟩,[⟨8,1184347566765703298559,⟨47,127,127,127,255,127,255,255,47⟩⟩]⟩
theorem node625 : UpperPrefix a [2,4,6,1,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,0,3] 30 cert625 (by decide +kernel)

def cert626 : Leaf := ⟨⟨488,492,417,0,0,396,0,109,233⟩,[(3,1),(4,6),(6,4)],[(4,1,3)],⟨7,19,76,26,176,97,224,392,268⟩,⟨7,19,76,26,176,97,224,384,260⟩,[⟨1,1266887094013262063206401,⟨501,113,476,508,240,113,240,384,388⟩⟩]⟩
theorem node626 : UpperPrefix a [2,4,6,1,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,0,5] 30 cert626 (by decide +kernel)

def cert627 : Leaf := ⟨⟨224,228,163,0,71,134,0,111,235⟩,[(3,1),(6,7)],[(4,1,3),(8,6,6)],⟨7,19,76,26,176,97,448,424,300⟩,⟨7,19,76,26,176,97,448,384,260⟩,[⟨3,1210109878036190895131909,⟨39,19,119,18,242,115,499,499,295⟩⟩]⟩
theorem node627 : UpperPrefix a [2,4,6,1,7,0,8] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,0,8] 30 cert627 (by decide +kernel)

theorem node628 : UpperPrefix a [2,4,6,1,7,0] 30 :=
  branch_upper a [2,4,6,1,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,1,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,0,2] 30 (by decide +kernel))
  node625
  (invalid_upper a [2,4,6,1,7,0,4] 30 (by decide +kernel))
  node626
  (invalid_upper a [2,4,6,1,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,0,7] 30 (by decide +kernel))
  node627)

def cert629 : Leaf := ⟨⟨360,364,0,0,333,0,301,109,105⟩,[(2,5),(3,1),(5,2)],[(4,1,3)],⟨7,19,76,26,176,104,481,417,293⟩,⟨7,19,76,26,176,104,192,384,260⟩,[⟨1,1214839173293962911809537,⟨501,465,108,24,180,108,192,384,292⟩⟩,⟨7,1459212397395965383816245,⟨303,283,367,283,319,367,64,256,293⟩⟩]⟩
theorem node629 : UpperPrefix a [2,4,6,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,3] 30 cert629 (by decide +kernel)

def cert630 : Leaf := ⟨⟨232,236,162,0,332,140,44,108,232⟩,[(3,1)],[(4,1,3),(8,5,4)],⟨7,19,76,26,176,352,193,424,300⟩,⟨7,19,76,26,176,352,193,384,260⟩,[⟨0,1536587267689470760059904,⟨446,410,508,26,176,500,508,400,436⟩⟩,⟨1,1229033942916131885940737,⟨501,113,508,24,176,368,241,400,436⟩⟩]⟩
theorem node630 : UpperPrefix a [2,4,6,1,7,8,0] 30 :=
  Boolean.leaf_sound a [2,4,6,1,7,8,0] 30 cert630 (by decide +kernel)

def cert631 : Local := ⟨⟨224,228,0,0,327,135,39,103,227⟩,[(2,6),(3,1)],[(4,1,3),(8,5,4),(3,6,2)]⟩
theorem node631 : UpperPrefix a [2,4,6,1,7,8,3] 30 :=
  local_sound a [2,4,6,1,7,8,3] 30 cert631 (by decide +kernel)

def cert632 : Local := ⟨⟨232,236,163,0,0,143,0,111,235⟩,[(3,1),(4,6),(6,4)],[(4,1,3),(8,5,4),(8,5,6)]⟩
theorem node632 : UpperPrefix a [2,4,6,1,7,8,5] 30 :=
  local_sound a [2,4,6,1,7,8,5] 30 cert632 (by decide +kernel)

theorem node633 : UpperPrefix a [2,4,6,1,7,8] 30 :=
  branch_upper a [2,4,6,1,7,8] 30 (by decide) (fin9_cases _
  node630
  (invalid_upper a [2,4,6,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,8,2] 30 (by decide +kernel))
  node631
  (invalid_upper a [2,4,6,1,7,8,4] 30 (by decide +kernel))
  node632
  (invalid_upper a [2,4,6,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,8,8] 30 (by decide +kernel)))

theorem node634 : UpperPrefix a [2,4,6,1,7] 30 :=
  branch_upper a [2,4,6,1,7] 30 (by decide) (fin9_cases _
  node628
  (invalid_upper a [2,4,6,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,2] 30 (by decide +kernel))
  node629
  (invalid_upper a [2,4,6,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,7,7] 30 (by decide +kernel))
  node633)

def cert635 : Leaf := ⟨⟨480,484,0,0,198,390,294,102,226⟩,[(2,6),(3,1)],[(4,1,3),(3,6,2)],⟨7,19,76,26,304,97,200,416,420⟩,⟨7,19,76,26,304,97,200,384,260⟩,[⟨0,1361666194739633768367104,⟨78,222,76,222,432,500,204,384,260⟩⟩]⟩
theorem node635 : UpperPrefix a [2,4,6,1,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,0,3] 30 cert635 (by decide +kernel)

def cert636 : Leaf := ⟨⟨360,364,289,0,76,268,268,108,232⟩,[(3,1)],[(4,1,3)],⟨7,19,76,26,304,97,224,392,396⟩,⟨7,19,76,26,304,97,224,384,260⟩,[⟨1,1266886805778487864983553,⟨501,113,476,508,304,113,224,384,388⟩⟩,⟨7,1208926976073317735408961,⟨47,27,109,26,315,101,111,283,319⟩⟩,⟨0,1233784537765409490732032,⟨398,410,460,154,368,496,240,384,388⟩⟩]⟩
theorem node636 : UpperPrefix a [2,4,6,1,8,0,5] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,0,5] 30 cert636 (by decide +kernel)

theorem node637 : UpperPrefix a [2,4,6,1,8,0] 30 :=
  branch_upper a [2,4,6,1,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,6,1,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,0,2] 30 (by decide +kernel))
  node635
  (invalid_upper a [2,4,6,1,8,0,4] 30 (by decide +kernel))
  node636
  (invalid_upper a [2,4,6,1,8,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,6,1,8,0,8] 30 (by decide +kernel)))

def cert638 : Leaf := ⟨⟨360,364,0,0,77,0,301,109,233⟩,[(2,5),(3,1),(5,2)],[(4,1,3)],⟨7,19,76,26,304,104,225,417,421⟩,⟨7,19,76,26,304,104,192,384,260⟩,[⟨1,1214839173311555097853953,⟨501,465,108,24,308,108,192,400,308⟩⟩,⟨7,1208926976073317743801717,⟨47,27,111,27,319,111,111,283,319⟩⟩]⟩
theorem node638 : UpperPrefix a [2,4,6,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,3] 30 cert638 (by decide +kernel)

def cert639 : Leaf := ⟨⟨360,364,290,0,78,0,302,110,106⟩,[(3,1),(5,6)],[(4,1,3),(7,5,5)],⟨7,19,76,26,304,224,193,424,300⟩,⟨7,19,76,26,304,224,193,384,260⟩,[⟨0,1536587267689470760059904,⟨446,410,508,26,304,500,508,400,436⟩⟩]⟩
theorem node639 : UpperPrefix a [2,4,6,1,8,7,0] 30 :=
  Boolean.leaf_sound a [2,4,6,1,8,7,0] 30 cert639 (by decide +kernel)

#print axioms node639
end Delivery.FiniteExclusion.Sharp2x7
