import RegularNineSharp2x7Base
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def cert448 : Local := ⟨⟨0,0,497,0,460,396,300,108,232⟩,[(0,2),(1,3),(3,1)],[(4,1,2),(1,2,0),(0,3,2)]⟩
theorem node448 : UpperPrefix a [2,4,1,0] 30 :=
  local_sound a [2,4,1,0] 30 cert448 (by decide +kernel)

def cert449 : Leaf := ⟨⟨0,268,273,0,461,397,269,77,201⟩,[(0,2),(3,4)],[(4,1,2),(1,2,0),(5,3,3)],⟨7,19,14,56,505,489,457,457,461⟩,⟨7,19,14,56,48,96,192,384,260⟩,[⟨6,1210106412362349233583135,⟨7,31,15,63,63,32,128,384,261⟩⟩,⟨7,1208926973663136429126687,⟨7,31,15,63,63,96,64,256,261⟩⟩]⟩
theorem node449 : UpperPrefix a [2,4,1,5] 30 :=
  Boolean.leaf_sound a [2,4,1,5] 30 cert449 (by decide +kernel)

def cert450 : Local := ⟨⟨0,0,496,420,460,396,300,108,232⟩,[(0,2),(1,4)],[(4,1,2),(1,2,0),(0,4,1)]⟩
theorem node450 : UpperPrefix a [2,4,1,6,0] 30 :=
  local_sound a [2,4,1,6,0] 30 cert450 (by decide +kernel)

def cert451 : Leaf := ⟨⟨0,300,305,293,325,389,293,37,161⟩,[(0,2)],[(4,1,2),(1,2,0),(6,3,4)],⟨7,19,14,88,56,481,481,417,421⟩,⟨7,19,14,88,56,96,192,384,260⟩,[⟨3,1236149891584189497607173,⟨487,499,487,80,48,96,192,480,485⟩⟩,⟨7,1208926973665337607746623,⟨7,23,15,95,63,127,64,256,261⟩⟩]⟩
theorem node451 : UpperPrefix a [2,4,1,6,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,3] 30 cert451 (by decide +kernel)

def cert452 : Leaf := ⟨⟨0,108,112,164,76,12,300,108,104⟩,[(0,2)],[(4,1,2),(1,2,0),(7,4,3)],⟨7,19,14,88,176,97,488,424,300⟩,⟨7,19,14,88,176,97,192,384,260⟩,[⟨0,1361666879286783552259072,⟨14,222,14,216,504,508,192,384,260⟩⟩,⟨8,1181748206908264739967,⟨7,23,47,127,191,127,255,128,5⟩⟩]⟩
theorem node452 : UpperPrefix a [2,4,1,6,7,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,0] 30 cert452 (by decide +kernel)

def cert453 : Local := ⟨⟨0,300,305,421,269,0,301,45,41⟩,[(0,2),(5,3)],[(4,1,2),(1,2,0),(6,3,5),(7,4,3)]⟩
theorem node453 : UpperPrefix a [2,4,1,6,7,3] 30 :=
  local_sound a [2,4,1,6,7,3] 30 cert453 (by decide +kernel)

def cert454 : Leaf := ⟨⟨0,12,17,165,333,13,45,109,105⟩,[(0,2)],[(4,1,2),(1,2,0),(7,4,3),(8,5,4)],⟨7,19,14,88,176,352,233,425,301⟩,⟨7,19,14,88,176,352,192,384,260⟩,[⟨5,1210107564157951781377037,⟨7,19,15,95,144,320,192,384,261⟩⟩,⟨6,1210106412362347081372685,⟨7,19,15,31,176,288,128,384,261⟩⟩]⟩
theorem node454 : UpperPrefix a [2,4,1,6,7,8] 30 :=
  Boolean.leaf_sound a [2,4,1,6,7,8] 30 cert454 (by decide +kernel)

theorem node455 : UpperPrefix a [2,4,1,6,7] 30 :=
  branch_upper a [2,4,1,6,7] 30 (by decide) (fin9_cases _
  node452
  (invalid_upper a [2,4,1,6,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,2] 30 (by decide +kernel))
  node453
  (invalid_upper a [2,4,1,6,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,7,7] 30 (by decide +kernel))
  node454)

def cert456 : Leaf := ⟨⟨0,364,368,416,204,264,296,104,232⟩,[(0,2)],[(4,1,2),(1,2,0)],⟨7,19,14,88,304,97,232,424,428⟩,⟨7,19,14,88,304,97,192,384,260⟩,[⟨0,1361666879286783552259072,⟨14,222,14,216,504,508,192,384,260⟩⟩,⟨2,1210255463601170064344065,⟨107,251,106,216,504,97,192,384,256⟩⟩,⟨7,1208926973944609253626893,⟨7,19,47,127,304,97,64,256,261⟩⟩]⟩
theorem node456 : UpperPrefix a [2,4,1,6,8,0] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,0] 30 cert456 (by decide +kernel)

def cert457 : Leaf := ⟨⟨0,396,401,421,141,0,301,45,169⟩,[(0,2),(5,3)],[(4,1,2),(1,2,0),(6,3,5)],⟨7,19,14,88,304,104,225,417,421⟩,⟨7,19,14,88,304,104,192,384,260⟩,[⟨5,1210107564157951789773885,⟨7,19,15,95,279,79,192,384,261⟩⟩]⟩
theorem node457 : UpperPrefix a [2,4,1,6,8,3] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,3] 30 cert457 (by decide +kernel)

def cert458 : Leaf := ⟨⟨0,332,337,293,77,0,301,109,105⟩,[(0,2),(5,6)],[(4,1,2),(1,2,0),(7,5,5)],⟨7,19,14,88,304,224,233,425,301⟩,⟨7,19,14,88,304,224,192,384,260⟩,[⟨5,1210107564157951781377037,⟨7,19,15,95,272,192,192,384,261⟩⟩]⟩
theorem node458 : UpperPrefix a [2,4,1,6,8,7] 30 :=
  Boolean.leaf_sound a [2,4,1,6,8,7] 30 cert458 (by decide +kernel)

theorem node459 : UpperPrefix a [2,4,1,6,8] 30 :=
  branch_upper a [2,4,1,6,8] 30 (by decide) (fin9_cases _
  node456
  (invalid_upper a [2,4,1,6,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,2] 30 (by decide +kernel))
  node457
  (invalid_upper a [2,4,1,6,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,8,6] 30 (by decide +kernel))
  node458
  (invalid_upper a [2,4,1,6,8,8] 30 (by decide +kernel)))

theorem node460 : UpperPrefix a [2,4,1,6] 30 :=
  branch_upper a [2,4,1,6] 30 (by decide) (fin9_cases _
  node450
  (invalid_upper a [2,4,1,6,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,2] 30 (by decide +kernel))
  node451
  (invalid_upper a [2,4,1,6,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,6,6] 30 (by decide +kernel))
  node455
  node459)

def cert461 : Local := ⟨⟨0,0,496,356,460,396,300,108,232⟩,[(0,2),(1,4)],[(4,1,2),(1,2,0),(0,4,1)]⟩
theorem node461 : UpperPrefix a [2,4,1,7,0] 30 :=
  local_sound a [2,4,1,7,0] 30 cert461 (by decide +kernel)

def cert462 : Leaf := ⟨⟨0,12,17,357,453,389,293,101,225⟩,[(0,2)],[(4,1,2),(1,2,0)],⟨7,19,14,152,56,353,481,481,357⟩,⟨7,19,14,152,56,96,192,384,260⟩,[⟨3,1236149891584189497607173,⟨487,499,487,144,48,96,192,480,485⟩⟩,⟨5,1210107564157951785579551,⟨7,23,15,159,31,64,192,384,261⟩⟩,⟨6,1210106412362347085575199,⟨7,23,15,159,63,32,128,384,261⟩⟩,⟨7,1208926973663134281118751,⟨7,23,15,31,63,96,64,256,261⟩⟩,⟨8,1181745669222517715999,⟨7,23,15,159,63,96,192,128,5⟩⟩]⟩
theorem node462 : UpperPrefix a [2,4,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,1,7,3] 30 cert462 (by decide +kernel)

def cert463 : Leaf := ⟨⟨0,396,401,293,0,397,301,45,169⟩,[(0,2),(4,5)],[(4,1,2),(1,2,0),(6,4,4)],⟨7,19,14,152,112,361,489,425,301⟩,⟨7,19,14,152,112,96,192,384,260⟩,[⟨5,1210107564157951781377037,⟨7,19,15,159,80,64,192,384,261⟩⟩]⟩
theorem node463 : UpperPrefix a [2,4,1,7,6] 30 :=
  Boolean.leaf_sound a [2,4,1,7,6] 30 cert463 (by decide +kernel)

def cert464 : Leaf := ⟨⟨0,236,240,352,204,136,40,104,232⟩,[(0,2)],[(4,1,2),(1,2,0),(8,4,3)],⟨7,19,14,152,304,97,232,488,364⟩,⟨7,19,14,152,304,97,192,384,260⟩,[⟨0,1361666879286783552259072,⟨14,222,14,216,504,508,192,384,260⟩⟩,⟨2,1210255463601170064344065,⟨107,251,106,216,504,97,192,384,256⟩⟩]⟩
theorem node464 : UpperPrefix a [2,4,1,7,8,0] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,0] 30 cert464 (by decide +kernel)

def cert465 : Leaf := ⟨⟨0,12,17,357,77,133,45,109,105⟩,[(0,2)],[(4,1,2),(1,2,0),(7,3,5),(8,4,3)],⟨7,19,14,152,304,104,225,481,357⟩,⟨7,19,14,152,304,104,192,384,260⟩,[⟨5,1210107564157951789773885,⟨7,19,15,159,279,79,192,384,261⟩⟩,⟨6,1210106412362347089769533,⟨7,19,15,159,311,47,128,384,261⟩⟩]⟩
theorem node465 : UpperPrefix a [2,4,1,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,1,7,8,3] 30 cert465 (by decide +kernel)

theorem node466 : UpperPrefix a [2,4,1,7,8] 30 :=
  branch_upper a [2,4,1,7,8] 30 (by decide) (fin9_cases _
  node464
  (invalid_upper a [2,4,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,2] 30 (by decide +kernel))
  node465
  (invalid_upper a [2,4,1,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,8,8] 30 (by decide +kernel)))

theorem node467 : UpperPrefix a [2,4,1,7] 30 :=
  branch_upper a [2,4,1,7] 30 (by decide) (fin9_cases _
  node461
  (invalid_upper a [2,4,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,2] 30 (by decide +kernel))
  node462
  (invalid_upper a [2,4,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,7,5] 30 (by decide +kernel))
  node463
  (invalid_upper a [2,4,1,7,7] 30 (by decide +kernel))
  node466)

def cert468 : Local := ⟨⟨0,0,496,228,460,396,300,108,232⟩,[(0,2),(1,4)],[(4,1,2),(1,2,0),(0,4,1)]⟩
theorem node468 : UpperPrefix a [2,4,1,8,0] 30 :=
  local_sound a [2,4,1,8,0] 30 cert468 (by decide +kernel)

def cert469 : Leaf := ⟨⟨0,12,17,229,453,389,293,101,225⟩,[(0,2)],[(4,1,2),(1,2,0)],⟨7,19,14,280,56,225,225,481,485⟩,⟨7,19,14,280,56,96,192,384,260⟩,[⟨3,1236149891584189497607173,⟨487,499,487,496,48,96,192,480,485⟩⟩,⟨5,1210107564157951785579551,⟨7,23,15,287,31,64,192,384,261⟩⟩,⟨6,1210106412362347085575199,⟨7,23,15,287,63,32,128,384,261⟩⟩,⟨7,1208926973663134281118751,⟨7,23,15,287,63,96,64,256,261⟩⟩,⟨8,1181745669222517715999,⟨7,23,15,31,63,96,192,128,5⟩⟩]⟩
theorem node469 : UpperPrefix a [2,4,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,1,8,3] 30 cert469 (by decide +kernel)

def cert470 : Leaf := ⟨⟨0,396,401,165,0,397,301,45,169⟩,[(0,2),(4,5)],[(4,1,2),(1,2,0),(6,4,4)],⟨7,19,14,280,112,233,233,425,429⟩,⟨7,19,14,280,112,96,192,384,260⟩,[⟨5,1210107564157951781377037,⟨7,19,15,287,80,64,192,384,261⟩⟩]⟩
theorem node470 : UpperPrefix a [2,4,1,8,6] 30 :=
  Boolean.leaf_sound a [2,4,1,8,6] 30 cert470 (by decide +kernel)

def cert471 : Leaf := ⟨⟨0,76,81,101,77,12,293,109,105⟩,[(0,2)],[(4,1,2),(1,2,0),(8,3,6)],⟨7,19,14,280,176,97,200,480,356⟩,⟨7,19,14,280,176,97,200,384,260⟩,[⟨7,1662274158270422200104031,⟨7,31,15,287,319,357,367,256,261⟩⟩,⟨5,1210107564157951798154317,⟨7,19,15,287,144,69,207,384,261⟩⟩]⟩
theorem node471 : UpperPrefix a [2,4,1,8,7,0,3] 30 :=
  Boolean.leaf_sound a [2,4,1,8,7,0,3] 30 cert471 (by decide +kernel)

def cert472 : Leaf := ⟨⟨0,492,496,228,0,396,0,108,232⟩,[(0,2),(4,6),(6,4)],[(4,1,2),(1,2,0)],⟨7,19,14,280,176,97,224,456,332⟩,⟨7,19,14,280,176,97,224,384,260⟩,[⟨0,1371794141787656732541952,⟨398,478,398,472,504,508,504,384,260⟩⟩]⟩
theorem node472 : UpperPrefix a [2,4,1,8,7,0,5] 30 :=
  Boolean.leaf_sound a [2,4,1,8,7,0,5] 30 cert472 (by decide +kernel)

theorem node473 : UpperPrefix a [2,4,1,8,7,0] 30 :=
  branch_upper a [2,4,1,8,7,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,1,8,7,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,0,2] 30 (by decide +kernel))
  node471
  (invalid_upper a [2,4,1,8,7,0,4] 30 (by decide +kernel))
  node472
  (invalid_upper a [2,4,1,8,7,0,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,0,8] 30 (by decide +kernel)))

def cert474 : Leaf := ⟨⟨0,12,17,101,333,133,45,109,105⟩,[(0,2)],[(4,1,2),(1,2,0)],⟨7,19,14,280,176,104,225,481,357⟩,⟨7,19,14,280,176,104,192,384,260⟩,[⟨7,1360042701114965084353599,⟨7,31,15,287,319,367,64,256,261⟩⟩,⟨8,1182034181073650332733,⟨7,83,47,127,247,111,192,128,5⟩⟩,⟨5,1210107564157951789773885,⟨7,19,15,287,151,79,192,384,261⟩⟩,⟨6,1210106412362347089769533,⟨7,19,15,287,183,47,128,384,261⟩⟩]⟩
theorem node474 : UpperPrefix a [2,4,1,8,7,3] 30 :=
  Boolean.leaf_sound a [2,4,1,8,7,3] 30 cert474 (by decide +kernel)

theorem node475 : UpperPrefix a [2,4,1,8,7] 30 :=
  branch_upper a [2,4,1,8,7] 30 (by decide) (fin9_cases _
  node473
  (invalid_upper a [2,4,1,8,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,2] 30 (by decide +kernel))
  node474
  (invalid_upper a [2,4,1,8,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,7,8] 30 (by decide +kernel)))

theorem node476 : UpperPrefix a [2,4,1,8] 30 :=
  branch_upper a [2,4,1,8] 30 (by decide) (fin9_cases _
  node468
  (invalid_upper a [2,4,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,2] 30 (by decide +kernel))
  node469
  (invalid_upper a [2,4,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,8,5] 30 (by decide +kernel))
  node470
  node475
  (invalid_upper a [2,4,1,8,8] 30 (by decide +kernel)))

theorem node477 : UpperPrefix a [2,4,1] 30 :=
  branch_upper a [2,4,1] 30 (by decide) (fin9_cases _
  node448
  (invalid_upper a [2,4,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,2] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,3] 30 (by decide +kernel))
  (invalid_upper a [2,4,1,4] 30 (by decide +kernel))
  node449
  node460
  node467
  node476)

def cert478 : Leaf := ⟨⟨504,0,448,0,460,396,300,108,232⟩,[(1,3),(3,1)],[(1,4,1),(1,4,3)],⟨7,19,44,25,50,488,456,456,460⟩,⟨7,19,44,25,50,96,192,384,260⟩,[⟨0,1266886860137792986416128,⟨502,18,492,508,50,96,192,384,484⟩⟩,⟨4,1266886860136624755311617,⟨487,3,492,493,34,96,192,384,484⟩⟩]⟩
theorem node478 : UpperPrefix a [2,4,5,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,0,1] 30 cert478 (by decide +kernel)

def cert479 : Leaf := ⟨⟨496,0,0,0,0,407,311,119,243⟩,[(1,3),(2,4),(3,1),(4,2)],[],⟨7,19,44,25,56,482,450,450,454⟩,⟨7,19,44,25,56,96,192,384,260⟩,[⟨3,1233858019022494883648517,⟨487,499,487,499,242,96,192,384,485⟩⟩]⟩
theorem node479 : UpperPrefix a [2,4,5,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,0,3] 30 cert479 (by decide +kernel)

def cert480 : Leaf := ⟨⟨280,0,275,0,0,415,287,31,155⟩,[(1,3),(3,1),(4,5)],[(6,4,4)],⟨7,19,44,25,112,490,458,394,398⟩,⟨7,19,44,25,112,96,192,384,260⟩,[⟨5,1233858017368830737650693,⟨463,475,463,475,80,64,192,384,453⟩⟩,⟨7,1208926973665340558441791,⟨15,31,63,31,127,127,64,257,271⟩⟩]⟩
theorem node480 : UpperPrefix a [2,4,5,0,6] 30 :=
  Boolean.leaf_sound a [2,4,5,0,6] 30 cert480 (by decide +kernel)

def cert481 : Leaf := ⟨⟨504,0,448,0,332,396,300,108,232⟩,[(1,3),(3,1)],[],⟨7,19,44,25,176,98,456,456,332⟩,⟨7,19,44,25,176,98,192,384,260⟩,[⟨0,1266886859751589527159808,⟨502,50,508,508,176,98,192,384,468⟩⟩,⟨1,1385269470314964991344641,⟨477,473,508,473,500,508,192,384,468⟩⟩,⟨4,1266886859749596662334465,⟨487,35,492,493,160,98,192,384,452⟩⟩]⟩
theorem node481 : UpperPrefix a [2,4,5,0,7,1] 30 :=
  Boolean.leaf_sound a [2,4,5,0,7,1] 30 cert481 (by decide +kernel)

def cert482 : Leaf := ⟨⟨496,0,0,0,326,406,310,118,242⟩,[(1,3),(2,5),(3,1)],[(3,5,2)],⟨7,19,44,25,176,104,450,450,326⟩,⟨7,19,44,25,176,104,192,384,260⟩,[⟨0,1214857656208052167115776,⟨454,466,60,508,180,124,192,384,260⟩⟩]⟩
theorem node482 : UpperPrefix a [2,4,5,0,7,3] 30 :=
  Boolean.leaf_sound a [2,4,5,0,7,3] 30 cert482 (by decide +kernel)

def cert483 : Leaf := ⟨⟨88,0,81,0,333,29,29,93,89⟩,[(1,3),(3,1)],[(8,5,4)],⟨7,19,44,25,176,352,194,456,332⟩,⟨7,19,44,25,176,352,194,384,260⟩,[⟨1,1512929318256264854110209,⟨13,25,60,25,176,500,508,384,260⟩⟩,⟨5,1233858017368830737650693,⟨463,475,463,475,144,320,202,384,453⟩⟩,⟨7,1511158430818593819079775,⟨15,31,47,31,63,357,367,256,261⟩⟩]⟩
theorem node483 : UpperPrefix a [2,4,5,0,7,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,0,7,8,1] 30 cert483 (by decide +kernel)

def cert484 : Leaf := ⟨⟨80,0,83,0,327,31,23,87,91⟩,[(1,3),(3,1)],[(8,5,4)],⟨7,19,44,25,176,352,200,450,326⟩,⟨7,19,44,25,176,352,200,384,260⟩,[⟨5,1233858017368830737650693,⟨463,475,463,475,144,320,202,384,453⟩⟩,⟨7,1511158430818593819079775,⟨15,31,47,31,63,357,367,256,261⟩⟩,⟨3,1210402713191503866519301,⟨23,19,183,19,178,499,194,387,279⟩⟩]⟩
theorem node484 : UpperPrefix a [2,4,5,0,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,0,7,8,3] 30 cert484 (by decide +kernel)

theorem node485 : UpperPrefix a [2,4,5,0,7,8] 30 :=
  branch_upper a [2,4,5,0,7,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,0,7,8,0] 30 (by decide +kernel))
  node483
  (invalid_upper a [2,4,5,0,7,8,2] 30 (by decide +kernel))
  node484
  (invalid_upper a [2,4,5,0,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,7,8,8] 30 (by decide +kernel)))

theorem node486 : UpperPrefix a [2,4,5,0,7] 30 :=
  branch_upper a [2,4,5,0,7] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,0,7,0] 30 (by decide +kernel))
  node481
  (invalid_upper a [2,4,5,0,7,2] 30 (by decide +kernel))
  node482
  (invalid_upper a [2,4,5,0,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,7,7] 30 (by decide +kernel))
  node485)

def cert487 : Leaf := ⟨⟨504,0,448,0,204,396,300,108,232⟩,[(1,3),(3,1)],[],⟨7,19,44,25,304,98,200,456,460⟩,⟨7,19,44,25,304,98,192,384,260⟩,[⟨0,1266886859751589527159808,⟨502,50,508,508,304,98,192,384,468⟩⟩,⟨1,1385269470314964991344641,⟨477,473,508,473,500,508,192,384,468⟩⟩,⟨4,1266886859749596662334465,⟨487,35,492,493,288,98,192,384,452⟩⟩]⟩
theorem node487 : UpperPrefix a [2,4,5,0,8,1] 30 :=
  Boolean.leaf_sound a [2,4,5,0,8,1] 30 cert487 (by decide +kernel)

def cert488 : Leaf := ⟨⟨496,0,0,0,198,406,310,118,242⟩,[(1,3),(2,5),(3,1)],[(3,5,2)],⟨7,19,44,25,304,104,194,450,454⟩,⟨7,19,44,25,304,104,192,384,260⟩,[⟨0,1214857656208052167115776,⟨454,466,60,508,308,124,192,384,260⟩⟩]⟩
theorem node488 : UpperPrefix a [2,4,5,0,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,0,8,3] 30 cert488 (by decide +kernel)

def cert489 : Leaf := ⟨⟨280,0,275,0,79,0,287,95,91⟩,[(1,3),(3,1),(5,6)],[(7,5,5)],⟨7,19,44,25,304,224,202,458,334⟩,⟨7,19,44,25,304,224,192,384,260⟩,[⟨5,1233858017368830737650693,⟨463,475,463,475,272,192,192,384,453⟩⟩,⟨6,1210106412362349499397151,⟨15,31,47,31,319,160,128,384,261⟩⟩]⟩
theorem node489 : UpperPrefix a [2,4,5,0,8,7] 30 :=
  Boolean.leaf_sound a [2,4,5,0,8,7] 30 cert489 (by decide +kernel)

theorem node490 : UpperPrefix a [2,4,5,0,8] 30 :=
  branch_upper a [2,4,5,0,8] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,0,8,0] 30 (by decide +kernel))
  node487
  (invalid_upper a [2,4,5,0,8,2] 30 (by decide +kernel))
  node488
  (invalid_upper a [2,4,5,0,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,8,6] 30 (by decide +kernel))
  node489
  (invalid_upper a [2,4,5,0,8,8] 30 (by decide +kernel)))

theorem node491 : UpperPrefix a [2,4,5,0] 30 :=
  branch_upper a [2,4,5,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,0,0] 30 (by decide +kernel))
  node478
  (invalid_upper a [2,4,5,0,2] 30 (by decide +kernel))
  node479
  (invalid_upper a [2,4,5,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,0,5] 30 (by decide +kernel))
  node480
  node486
  node490)

def cert492 : Leaf := ⟨⟨488,0,448,0,460,396,300,108,232⟩,[(1,4),(3,1)],[(4,1,3),(0,4,1),(0,4,3)],⟨7,19,44,26,49,488,456,456,460⟩,⟨7,19,44,26,49,96,192,384,260⟩,[⟨1,1266886860137792986415105,⟨501,17,492,508,49,96,192,384,484⟩⟩]⟩
theorem node492 : UpperPrefix a [2,4,5,1,0] 30 :=
  Boolean.leaf_sound a [2,4,5,1,0] 30 cert492 (by decide +kernel)

def cert493 : Leaf := ⟨⟨488,492,0,0,0,389,293,101,225⟩,[(2,4),(3,1),(4,2)],[(4,1,3)],⟨7,19,44,26,56,481,449,449,453⟩,⟨7,19,44,26,56,96,192,384,260⟩,[⟨1,1224302388998144470810625,⟨501,501,60,508,60,96,192,384,276⟩⟩,⟨3,1214857656031579466630145,⟨487,499,36,242,48,96,192,384,260⟩⟩]⟩
theorem node493 : UpperPrefix a [2,4,5,1,3] 30 :=
  Boolean.leaf_sound a [2,4,5,1,3] 30 cert493 (by decide +kernel)

def cert494 : Leaf := ⟨⟨296,300,259,0,0,399,271,15,139⟩,[(3,1),(4,5)],[(4,1,3),(6,4,4)],⟨7,19,44,26,112,489,457,393,397⟩,⟨7,19,44,26,112,96,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,218,80,64,192,384,260⟩⟩,⟨7,1208926973665340558441791,⟨15,31,63,31,127,127,64,257,271⟩⟩]⟩
theorem node494 : UpperPrefix a [2,4,5,1,6] 30 :=
  Boolean.leaf_sound a [2,4,5,1,6] 30 cert494 (by decide +kernel)

def cert495 : Leaf := ⟨⟨232,236,194,0,76,140,300,108,232⟩,[(3,1)],[(4,1,3)],⟨7,19,44,26,176,97,456,456,332⟩,⟨7,19,44,26,176,97,192,384,260⟩,[⟨0,1385195539223482077283328,⟨478,474,508,218,500,508,192,384,468⟩⟩,⟨1,1229033996796599693475841,⟨501,49,508,24,176,113,192,384,468⟩⟩,⟨8,1181747925435701851263,⟨15,31,47,31,191,127,255,128,5⟩⟩]⟩
theorem node495 : UpperPrefix a [2,4,5,1,7,0] 30 :=
  Boolean.leaf_sound a [2,4,5,1,7,0] 30 cert495 (by decide +kernel)

def cert496 : Leaf := ⟨⟨480,484,0,0,325,389,293,101,225⟩,[(2,5),(3,1)],[(4,1,3),(3,5,2)],⟨7,19,44,26,176,104,449,449,325⟩,⟨7,19,44,26,176,104,192,384,260⟩,[⟨1,1214857656208052167114753,⟨453,465,60,252,180,124,192,384,260⟩⟩]⟩
theorem node496 : UpperPrefix a [2,4,5,1,7,3] 30 :=
  Boolean.leaf_sound a [2,4,5,1,7,3] 30 cert496 (by decide +kernel)

def cert497 : Leaf := ⟨⟨168,172,130,0,270,142,46,38,234⟩,[(3,1)],[(4,1,3),(8,5,4)],⟨7,19,44,26,176,352,193,392,324⟩,⟨7,19,44,26,176,352,193,392,260⟩,[⟨0,1664081939196515932177408,⟨158,26,444,26,432,500,508,392,404⟩⟩,⟨6,1212762743511476910325567,⟨31,31,191,31,191,447,139,395,415⟩⟩]⟩
theorem node497 : UpperPrefix a [2,4,5,1,7,8,0,3] 30 :=
  Boolean.leaf_sound a [2,4,5,1,7,8,0,3] 30 cert497 (by decide +kernel)

def cert498 : Local := ⟨⟨168,172,131,0,335,0,46,0,171⟩,[(3,1),(5,7),(7,5)],[(4,1,3),(8,5,4),(6,7,4)]⟩
theorem node498 : UpperPrefix a [2,4,5,1,7,8,0,6] 30 :=
  local_sound a [2,4,5,1,7,8,0,6] 30 cert498 (by decide +kernel)

theorem node499 : UpperPrefix a [2,4,5,1,7,8,0] 30 :=
  branch_upper a [2,4,5,1,7,8,0] 30 (by decide) (fin9_cases _
  (invalid_upper a [2,4,5,1,7,8,0,0] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,0,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,0,2] 30 (by decide +kernel))
  node497
  (invalid_upper a [2,4,5,1,7,8,0,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,0,5] 30 (by decide +kernel))
  node498
  (invalid_upper a [2,4,5,1,7,8,0,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,0,8] 30 (by decide +kernel)))

def cert500 : Leaf := ⟨⟨96,100,67,0,327,15,7,71,75⟩,[(3,1)],[(4,1,3),(8,5,4)],⟨7,19,44,26,176,352,200,449,325⟩,⟨7,19,44,26,176,352,200,384,260⟩,[⟨7,1662274158270422465918047,⟨15,31,303,31,319,357,367,256,261⟩⟩,⟨3,1210402713191503866515205,⟨23,19,183,18,178,499,192,387,279⟩⟩,⟨5,1214857798915315861554177,⟨463,475,76,218,144,320,200,384,260⟩⟩]⟩
theorem node500 : UpperPrefix a [2,4,5,1,7,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,1,7,8,3] 30 cert500 (by decide +kernel)

theorem node501 : UpperPrefix a [2,4,5,1,7,8] 30 :=
  branch_upper a [2,4,5,1,7,8] 30 (by decide) (fin9_cases _
  node499
  (invalid_upper a [2,4,5,1,7,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,2] 30 (by decide +kernel))
  node500
  (invalid_upper a [2,4,5,1,7,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,7] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,8,8] 30 (by decide +kernel)))

theorem node502 : UpperPrefix a [2,4,5,1,7] 30 :=
  branch_upper a [2,4,5,1,7] 30 (by decide) (fin9_cases _
  node495
  (invalid_upper a [2,4,5,1,7,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,2] 30 (by decide +kernel))
  node496
  (invalid_upper a [2,4,5,1,7,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,6] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,7,7] 30 (by decide +kernel))
  node501)

def cert503 : Leaf := ⟨⟨424,428,386,0,204,396,268,76,200⟩,[(3,1)],[(4,1,3)],⟨7,19,44,26,304,97,200,456,460⟩,⟨7,19,44,26,304,97,192,384,260⟩,[⟨0,1385195683338670153139200,⟨478,474,508,218,500,508,192,384,468⟩⟩,⟨1,1229033996796599693475841,⟨501,49,508,24,304,113,192,384,468⟩⟩,⟨5,1233784230392535899440129,⟨463,475,460,218,272,449,192,384,452⟩⟩,⟨6,1210106412362349499397151,⟨15,31,47,31,319,33,128,384,261⟩⟩]⟩
theorem node503 : UpperPrefix a [2,4,5,1,8,0] 30 :=
  Boolean.leaf_sound a [2,4,5,1,8,0] 30 cert503 (by decide +kernel)

def cert504 : Leaf := ⟨⟨480,484,0,0,199,389,293,101,225⟩,[(2,5),(3,1)],[(4,1,3),(3,5,2)],⟨7,19,44,26,304,104,193,449,453⟩,⟨7,19,44,26,304,104,192,384,260⟩,[⟨1,1214857656207502411300865,⟨453,465,44,252,308,108,192,384,260⟩⟩]⟩
theorem node504 : UpperPrefix a [2,4,5,1,8,3] 30 :=
  Boolean.leaf_sound a [2,4,5,1,8,3] 30 cert504 (by decide +kernel)

def cert505 : Leaf := ⟨⟨296,300,259,0,79,0,271,79,75⟩,[(3,1),(5,6)],[(4,1,3),(7,5,5)],⟨7,19,44,26,304,224,201,457,333⟩,⟨7,19,44,26,304,224,192,384,260⟩,[⟨5,1214857654800127785698305,⟨463,475,12,218,272,192,192,384,260⟩⟩,⟨6,1210106412362349499397151,⟨15,31,47,31,319,160,128,384,261⟩⟩]⟩
theorem node505 : UpperPrefix a [2,4,5,1,8,7] 30 :=
  Boolean.leaf_sound a [2,4,5,1,8,7] 30 cert505 (by decide +kernel)

theorem node506 : UpperPrefix a [2,4,5,1,8] 30 :=
  branch_upper a [2,4,5,1,8] 30 (by decide) (fin9_cases _
  node503
  (invalid_upper a [2,4,5,1,8,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,8,2] 30 (by decide +kernel))
  node504
  (invalid_upper a [2,4,5,1,8,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,8,5] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,8,6] 30 (by decide +kernel))
  node505
  (invalid_upper a [2,4,5,1,8,8] 30 (by decide +kernel)))

theorem node507 : UpperPrefix a [2,4,5,1] 30 :=
  branch_upper a [2,4,5,1] 30 (by decide) (fin9_cases _
  node492
  (invalid_upper a [2,4,5,1,1] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,2] 30 (by decide +kernel))
  node493
  (invalid_upper a [2,4,5,1,4] 30 (by decide +kernel))
  (invalid_upper a [2,4,5,1,5] 30 (by decide +kernel))
  node494
  node502
  node506)

def cert508 : Leaf := ⟨⟨56,0,82,6,14,414,286,30,154⟩,[(1,4)],[(6,3,2),(0,4,1)],⟨7,19,44,88,49,490,458,394,398⟩,⟨7,19,44,88,49,96,192,384,260⟩,[⟨5,1215005516983095761314817,⟨463,475,12,218,475,64,192,384,260⟩⟩,⟨7,1208926973665612483690303,⟨23,23,63,95,63,127,64,259,279⟩⟩,⟨8,1181745671700720287551,⟨23,23,63,95,63,127,192,131,23⟩⟩]⟩
theorem node508 : UpperPrefix a [2,4,5,6,0] 30 :=
  Boolean.leaf_sound a [2,4,5,6,0] 30 cert508 (by decide +kernel)

def cert509 : Leaf := ⟨⟨48,36,81,5,5,413,285,29,153⟩,[],[(6,3,2),(1,4,1)],⟨7,19,44,88,50,489,457,393,397⟩,⟨7,19,44,88,50,96,192,384,260⟩,[⟨7,1208926973665612483690303,⟨23,23,63,95,63,127,64,259,279⟩⟩,⟨8,1181745671700720287551,⟨23,23,63,95,63,127,192,131,23⟩⟩,⟨5,1214857654800129933181953,⟨463,475,12,88,218,64,192,384,260⟩⟩,⟨3,1210107565284125490417413,⟨23,19,55,80,50,96,192,387,279⟩⟩]⟩
theorem node509 : UpperPrefix a [2,4,5,6,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,1] 30 cert509 (by decide +kernel)

def cert510 : Leaf := ⟨⟨424,428,0,391,0,391,263,7,131⟩,[(2,4),(4,2)],[(6,3,2),(6,3,4)],⟨7,19,44,88,56,483,451,387,391⟩,⟨7,19,44,88,56,96,192,384,260⟩,[⟨4,1224302388996220323365891,⟨487,487,44,76,44,96,192,384,260⟩⟩,⟨3,1214857656031579466630145,⟨487,499,36,80,48,96,192,384,260⟩⟩,⟨5,1214857654800127785698305,⟨463,475,12,88,24,64,192,384,260⟩⟩]⟩
theorem node510 : UpperPrefix a [2,4,5,6,3] 30 :=
  Boolean.leaf_sound a [2,4,5,6,3] 30 cert510 (by decide +kernel)

def cert511 : Leaf := ⟨⟨56,44,80,164,12,30,60,60,56⟩,[],[(6,3,2),(7,4,3),(1,6,5)],⟨7,19,44,88,176,97,194,392,268⟩,⟨7,19,44,88,176,97,194,384,260⟩,[⟨8,1184347426027678332159,⟨47,127,47,127,255,127,255,255,5⟩⟩,⟨0,1508788075998994030920704,⟨478,478,444,476,444,508,458,384,404⟩⟩]⟩
theorem node511 : UpperPrefix a [2,4,5,6,7,0,1] 30 :=
  Boolean.leaf_sound a [2,4,5,6,7,0,1] 30 cert511 (by decide +kernel)

#print axioms node511
end Delivery.FiniteExclusion.Sharp2x7
